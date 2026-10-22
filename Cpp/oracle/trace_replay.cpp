// SPDX-License-Identifier: MIT OR Apache-2.0

// trace_replay.cpp — the C++ leg of the three-way trace gate: replays a trace
// (`../../examples/traces/GRAMMAR.md` §1) on the 2007 HPHA allocator and prints its
// transition record (§2) on stdout, byte for byte what `orisnik`'s
// `cargo run --example replay --features trace` and `orisnitsa`'s `zig build replay` print.
//
// It links against a *scratch copy* of `../hpha.h`/`../hpha.cpp` patched with
// `letopis.patch` (the reference files are never modified); `build_trace_oracle.ps1` makes
// the copy and builds this file. The parser, the semantic constraints, the normalization and
// the output format are ports of `Rust/src/letopis/` and `Zig/src/letopis_*.zig`; the error
// messages are the same, word for word. Windows/MSVC only, as HPHA itself is.

#include "hpha.h"

#include <fcntl.h>
#include <io.h>

#include <cstdarg>
#include <cstdio>
#include <cstdlib>
#include <cstring>
#include <map>
#include <string>
#include <vector>

// ---- the hooks' storage (declared in letopis_hooks.h) ----

int letopis_branch = LETOPIS_BRANCH_NODE;
unsigned letopis_rotations = 0;

namespace {

struct Event {
	letopis_event_type type;
	size_t a;
	size_t b;
	int branch;
	unsigned rotations;
};

std::vector<Event> g_events;
bool g_recording = false;

} // namespace

void letopis_event(letopis_event_type type, const void* a, size_t b) {
	if (!g_recording)
		return;
	Event e = {type, (size_t)a, b, letopis_branch, letopis_rotations};
	g_events.push_back(e);
}

namespace {

// ---- reading a trace (GRAMMAR.md §1.1 and §1.3) ----

const unsigned long long MAX_TRACE_SIZE = 1ull << 30;
const unsigned long long MAX_TRACE_ALIGNMENT = 1ull << 16;

enum OpKind {
	OP_ALLOC, OP_ALLOC_ALIGNED, OP_CALLOC, OP_REALLOC, OP_REALLOC_ALIGNED, OP_RESIZE,
	OP_SIZE, OP_FREE, OP_FREE_SIZED, OP_FREE_SIZED_ALIGNED, OP_PURGE
};

struct Keyword {
	const char* name;
	OpKind kind;
	size_t arity;
};

const Keyword KEYWORDS[] = {
	{"purge", OP_PURGE, 0},
	{"size", OP_SIZE, 1},
	{"free", OP_FREE, 1},
	{"alloc", OP_ALLOC, 2},
	{"realloc", OP_REALLOC, 2},
	{"resize", OP_RESIZE, 2},
	{"free_sized", OP_FREE_SIZED, 2},
	{"alloc_aligned", OP_ALLOC_ALIGNED, 3},
	{"calloc", OP_CALLOC, 3},
	{"realloc_aligned", OP_REALLOC_ALIGNED, 3},
	{"free_sized_aligned", OP_FREE_SIZED_ALIGNED, 3},
};

// One operation: `h` the handle number, `x`/`y` its numeric arguments in order.
struct Op {
	OpKind kind;
	unsigned long long h, x, y;
	size_t line;
};

struct Failure {
	const char* category; // "syntax error" or "trace rejected"
	size_t line;
	std::string message;
};

std::string format(const char* fmt, ...) {
	char buf[512];
	va_list args;
	va_start(args, fmt);
	vsnprintf(buf, sizeof buf, fmt, args);
	va_end(args);
	return buf;
}

std::vector<std::string> tokens(const std::string& line) {
	std::vector<std::string> out;
	size_t i = 0;
	while (i < line.size()) {
		while (i < line.size() && (line[i] == ' ' || line[i] == '\t'))
			++i;
		size_t start = i;
		while (i < line.size() && line[i] != ' ' && line[i] != '\t')
			++i;
		if (i > start)
			out.push_back(line.substr(start, i - start));
	}
	return out;
}

bool well_formed(const std::string& t) {
	if (t.empty())
		return false;
	for (size_t i = 0; i < t.size(); ++i)
		if (t[i] < '0' || t[i] > '9')
			return false;
	return t == "0" || t[0] != '0';
}

// Parses a well-formed decimal; false on overflow.
bool to_u64(const std::string& t, unsigned long long* out) {
	unsigned long long v = 0;
	for (size_t i = 0; i < t.size(); ++i) {
		unsigned d = (unsigned)(t[i] - '0');
		if (v > (~0ull - d) / 10)
			return false;
		v = v * 10 + d;
	}
	*out = v;
	return true;
}

bool parse_number(const std::string& t, size_t line, unsigned long long* out, Failure* f) {
	if (!well_formed(t)) {
		*f = Failure{"syntax error", line, format("expected a number, found `%s`", t.c_str())};
		return false;
	}
	if (!to_u64(t, out)) {
		*f = Failure{"syntax error", line, format("number `%s` does not fit in 64 bits", t.c_str())};
		return false;
	}
	return true;
}

bool parse_handle(const std::string& t, size_t line, unsigned long long* out, Failure* f) {
	if (t.size() < 2 || t[0] != 'h' || !well_formed(t.substr(1)) || !to_u64(t.substr(1), out)) {
		*f = Failure{"syntax error", line, format("expected a handle `hN`, found `%s`", t.c_str())};
		return false;
	}
	return true;
}

bool parse_op(const std::string& text, size_t line, Op* op, Failure* f) {
	std::vector<std::string> t = tokens(text);
	std::string keyword = t.empty() ? "" : t[0];
	const Keyword* k = NULL;
	for (size_t i = 0; i < sizeof KEYWORDS / sizeof KEYWORDS[0]; ++i)
		if (keyword == KEYWORDS[i].name)
			k = &KEYWORDS[i];
	if (!k) {
		*f = Failure{"syntax error", line, format("unknown operation `%s`", keyword.c_str())};
		return false;
	}
	size_t count = t.size() - 1;
	if (count != k->arity) {
		*f = Failure{"syntax error", line,
		             format("`%s` takes %zu argument(s), found %zu", keyword.c_str(), k->arity, count)};
		return false;
	}
	op->kind = k->kind;
	op->h = op->x = op->y = 0;
	op->line = line;
	if (k->kind == OP_PURGE)
		return true;
	if (!parse_handle(t[1], line, &op->h, f))
		return false;
	if (k->arity >= 2 && !parse_number(t[2], line, &op->x, f))
		return false;
	if (k->arity >= 3 && !parse_number(t[3], line, &op->y, f))
		return false;
	return true;
}

bool size_ok(unsigned long long s) { return s <= MAX_TRACE_SIZE; }

bool align_ok(unsigned long long a) {
	return a == 0 || ((a & (a - 1)) == 0 && a <= MAX_TRACE_ALIGNMENT);
}

// A bound handle's binding for the sized-free rules C6/C7: the size and alignment of the
// allocation that bound it, or `fresh == false` once a realloc or resize touched it.
struct Binding {
	bool fresh;
	unsigned long long size, alignment;
};

bool reject(Failure* f, size_t line, const std::string& message) {
	*f = Failure{"trace rejected", line, message};
	return false;
}

bool validate(const std::vector<Op>& ops, Failure* f) {
	std::map<unsigned long long, Binding> bound;
	for (size_t i = 0; i < ops.size(); ++i) {
		const Op& o = ops[i];
		const size_t n = o.line;
		switch (o.kind) {
		case OP_ALLOC:
		case OP_ALLOC_ALIGNED: {
			if (bound.count(o.h))
				return reject(f, n, format("C1: h%llu is already bound", o.h));
			if (!size_ok(o.x))
				return reject(f, n, format("C4: size %llu exceeds 2^30", o.x));
			unsigned long long a = o.kind == OP_ALLOC_ALIGNED ? o.y : 0;
			if (!align_ok(a))
				return reject(f, n, format("C3: alignment %llu is not 0 or a power of two at most 65536", a));
			bound[o.h] = Binding{true, o.x, a};
			break;
		}
		case OP_CALLOC: {
			if (bound.count(o.h))
				return reject(f, n, format("C1: h%llu is already bound", o.h));
			bool overflow = o.y != 0 && o.x > ~0ull / o.y;
			if (overflow || !size_ok(o.x * o.y))
				return reject(f, n, format("C4: %llu x %llu exceeds 2^30", o.x, o.y));
			bound[o.h] = Binding{true, o.x * o.y, 0};
			break;
		}
		case OP_REALLOC:
		case OP_REALLOC_ALIGNED:
			if (!size_ok(o.x))
				return reject(f, n, format("C4: size %llu exceeds 2^30", o.x));
			if (o.kind == OP_REALLOC_ALIGNED) {
				if (!align_ok(o.y))
					return reject(f, n, format("C3: alignment %llu is not 0 or a power of two at most 65536", o.y));
				if (o.y > 256 && o.x <= 256)
					return reject(f, n, format("C8: alignment %llu above 256 needs a size above 256, found %llu", o.y, o.x));
			}
			bound[o.h] = Binding{false, 0, 0};
			break;
		case OP_RESIZE:
			if (!bound.count(o.h))
				return reject(f, n, format("C2: h%llu is not bound", o.h));
			if (o.x == 0)
				return reject(f, n, "C5: resize to 0");
			if (!size_ok(o.x))
				return reject(f, n, format("C4: size %llu exceeds 2^30", o.x));
			bound[o.h] = Binding{false, 0, 0};
			break;
		case OP_SIZE:
			if (!bound.count(o.h))
				return reject(f, n, format("C2: h%llu is not bound", o.h));
			break;
		case OP_FREE:
			if (!bound.erase(o.h))
				return reject(f, n, format("C2: h%llu is not bound", o.h));
			break;
		case OP_FREE_SIZED: {
			std::map<unsigned long long, Binding>::iterator it = bound.find(o.h);
			if (it == bound.end())
				return reject(f, n, format("C2: h%llu is not bound", o.h));
			Binding b = it->second;
			bound.erase(it);
			if (!(o.x >= 1 && b.fresh && b.size == o.x && b.alignment <= 8))
				return reject(f, n, format("C6: free_sized h%llu %llu does not directly follow an allocation of exactly %llu bytes at alignment 8 or less", o.h, o.x, o.x));
			break;
		}
		case OP_FREE_SIZED_ALIGNED: {
			std::map<unsigned long long, Binding>::iterator it = bound.find(o.h);
			if (it == bound.end())
				return reject(f, n, format("C2: h%llu is not bound", o.h));
			Binding b = it->second;
			bound.erase(it);
			if (!(o.x >= 1 && o.y >= 1 && b.fresh && b.size == o.x && b.alignment == o.y))
				return reject(f, n, format("C7: free_sized_aligned h%llu %llu %llu does not directly follow alloc_aligned h%llu %llu %llu", o.h, o.x, o.y, o.h, o.x, o.y));
			break;
		}
		case OP_PURGE:
			break;
		}
	}
	return true;
}

bool parse(const std::string& text, std::vector<Op>* ops, Failure* f) {
	std::vector<std::string> lines;
	size_t start = 0;
	for (;;) {
		size_t end = text.find('\n', start);
		std::string line = text.substr(start, end == std::string::npos ? std::string::npos : end - start);
		if (!line.empty() && line[line.size() - 1] == '\r')
			line.erase(line.size() - 1);
		lines.push_back(line);
		if (end == std::string::npos)
			break;
		start = end + 1;
	}
	std::vector<std::string> header = tokens(lines[0]);
	if (!(header.size() == 2 && header[0] == "oris-trace" && header[1] == "1")) {
		*f = Failure{"syntax error", 1, "missing header `oris-trace 1`"};
		return false;
	}
	for (size_t i = 1; i < lines.size(); ++i) {
		const std::string& line = lines[i];
		size_t first = line.find_first_not_of(" \t");
		if (first == std::string::npos || line[first] == '#')
			continue;
		Op op;
		if (!parse_op(line, i + 1, &op, f))
			return false;
		ops->push_back(op);
	}
	return validate(*ops, f);
}

std::string render(const Op& o) {
	switch (o.kind) {
	case OP_ALLOC: return format("alloc h%llu %llu", o.h, o.x);
	case OP_ALLOC_ALIGNED: return format("alloc_aligned h%llu %llu %llu", o.h, o.x, o.y);
	case OP_CALLOC: return format("calloc h%llu %llu %llu", o.h, o.x, o.y);
	case OP_REALLOC: return format("realloc h%llu %llu", o.h, o.x);
	case OP_REALLOC_ALIGNED: return format("realloc_aligned h%llu %llu %llu", o.h, o.x, o.y);
	case OP_RESIZE: return format("resize h%llu %llu", o.h, o.x);
	case OP_SIZE: return format("size h%llu", o.h);
	case OP_FREE: return format("free h%llu", o.h);
	case OP_FREE_SIZED: return format("free_sized h%llu %llu", o.h, o.x);
	case OP_FREE_SIZED_ALIGNED: return format("free_sized_aligned h%llu %llu %llu", o.h, o.x, o.y);
	case OP_PURGE: return "purge";
	}
	return "";
}

// ---- normalization (GRAMMAR.md §2.2) ----

struct Mapping {
	size_t bytes;
	unsigned long long id;
};

struct Normalizer {
	std::map<size_t, Mapping> live;
	unsigned long long next_id, maps, unmaps, rotations;

	Normalizer() : next_id(0), maps(0), unmaps(0), rotations(0) {}

	const std::pair<const size_t, Mapping>* find(size_t addr) const {
		std::map<size_t, Mapping>::const_iterator it = live.upper_bound(addr);
		if (it == live.begin())
			return NULL;
		--it;
		if (addr - it->first >= it->second.bytes)
			return NULL;
		return &*it;
	}

	// `m<id>+0x<offset>`; false if no live mapping holds `addr`.
	bool location(size_t addr, std::string* out) const {
		const std::pair<const size_t, Mapping>* m = find(addr);
		if (!m)
			return false;
		*out = format("m%llu+0x%zx", m->second.id, addr - m->first);
		return true;
	}

	bool mapping(size_t addr, unsigned long long* id) const {
		const std::pair<const size_t, Mapping>* m = find(addr);
		if (!m)
			return false;
		*id = m->second.id;
		return true;
	}

	bool event_line(const Event& e, std::string* out) {
		static const char* const insert_kind[] = {"chain", "node", "?", "?"};
		static const char* const erase_kind[] = {"?", "node", "link", "promote"};
		std::string loc;
		unsigned long long id;
		switch (e.type) {
		case LETOPIS_MAP_BUCKET:
		case LETOPIS_MAP_TREE:
			id = next_id++;
			++maps;
			live[e.a] = Mapping{e.b, id};
			*out = format("map %c m%llu %zu", e.type == LETOPIS_MAP_BUCKET ? 'b' : 't', id, e.b);
			return true;
		case LETOPIS_UNMAP:
			if (!mapping(e.a, &id))
				return false;
			live.erase(e.a);
			++unmaps;
			*out = format("unmap m%llu %zu", id, e.b);
			return true;
		case LETOPIS_PAGE_SPAWN:
		case LETOPIS_PAGE_RELEASE:
		case LETOPIS_PAGE_FULL:
		case LETOPIS_PAGE_REFILL: {
			static const char* const names[] = {"page+", "page-", "page-full", "page-refill"};
			if (!mapping(e.a, &id))
				return false;
			*out = format("%s b%zu m%llu", names[e.type - LETOPIS_PAGE_SPAWN], e.b, id);
			return true;
		}
		case LETOPIS_SPLIT:
		case LETOPIS_SHIFT:
		case LETOPIS_LIST_PUSH:
		case LETOPIS_LIST_ERASE: {
			if (!location(e.a, &loc))
				return false;
			const char* name = e.type == LETOPIS_SPLIT ? "split" : e.type == LETOPIS_SHIFT ? "shift"
			                 : e.type == LETOPIS_LIST_PUSH ? "list+" : "list-";
			*out = format("%s %s %zu", name, loc.c_str(), e.b);
			return true;
		}
		case LETOPIS_MERGE:
			if (!location(e.a, &loc))
				return false;
			*out = "merge " + loc;
			return true;
		case LETOPIS_TREE_INSERT:
		case LETOPIS_TREE_ERASE:
			if (!location(e.a, &loc))
				return false;
			rotations += e.rotations;
			*out = format("%s %s %zu %s rot=%u", e.type == LETOPIS_TREE_INSERT ? "tree+" : "tree-", loc.c_str(),
			              e.b, (e.type == LETOPIS_TREE_INSERT ? insert_kind : erase_kind)[e.branch], e.rotations);
			return true;
		case LETOPIS_MR:
			if (e.a == 0) {
				*out = "mr -";
				return true;
			}
			if (!location(e.a, &loc))
				return false;
			*out = "mr " + loc;
			return true;
		}
		return false;
	}
};

// ---- replay ----

std::string g_out;

void out(const std::string& s) { g_out += s; }

int fail_unmapped(size_t line) {
	fprintf(stderr, "replay: line %zu: an event named an address outside every live mapping (a hook bug, not a trace error)\n", line);
	return 1;
}

int replay(const std::vector<Op>& ops) {
	// Never deleted: teardown is outside the record, and HPHA's destructor asserts the heap
	// empty, which a trace that ends with live blocks is not.
	allocator* a = new allocator();
	std::map<unsigned long long, void*> handles; // bound handles; NULL is "bound to null"
	Normalizer norm;
	out("oris-record 1\n");
	g_recording = true;
	for (size_t i = 0; i < ops.size(); ++i) {
		const Op& o = ops[i];
		enum { POINTER, SIZE, NOTHING } kind = NOTHING;
		void* result = NULL;
		size_t size_result = 0;
		std::map<unsigned long long, void*>::iterator it = handles.find(o.h);
		void* p = it == handles.end() ? NULL : it->second;
		switch (o.kind) {
		case OP_ALLOC: result = a->alloc((size_t)o.x); handles[o.h] = result; kind = POINTER; break;
		case OP_ALLOC_ALIGNED: result = a->alloc((size_t)o.x, (size_t)o.y); handles[o.h] = result; kind = POINTER; break;
		case OP_CALLOC: result = a->calloc((size_t)o.x, (size_t)o.y); handles[o.h] = result; kind = POINTER; break;
		case OP_REALLOC:
		case OP_REALLOC_ALIGNED:
			result = o.kind == OP_REALLOC ? a->realloc(p, (size_t)o.x) : a->realloc(p, (size_t)o.x, (size_t)o.y);
			// A failed realloc (null for a nonzero size) keeps the original binding.
			if (result || o.x == 0 || it == handles.end())
				handles[o.h] = result;
			kind = POINTER;
			break;
		case OP_RESIZE: size_result = a->resize(p, (size_t)o.x); kind = SIZE; break;
		case OP_SIZE: size_result = a->size(p); kind = SIZE; break;
		case OP_FREE: handles.erase(o.h); a->free(p); break;
		case OP_FREE_SIZED: handles.erase(o.h); a->free(p, (size_t)o.x); break;
		case OP_FREE_SIZED_ALIGNED: handles.erase(o.h); a->free(p, (size_t)o.x, (size_t)o.y); break;
		case OP_PURGE: a->purge(); break;
		}
		std::string events;
		for (size_t e = 0; e < g_events.size(); ++e) {
			std::string line;
			if (!norm.event_line(g_events[e], &line))
				return fail_unmapped(o.line);
			events += "  " + line + "\n";
		}
		g_events.clear();
		std::string res;
		if (kind == POINTER) {
			if (!result)
				res = "null";
			else if (!norm.location((size_t)result, &res))
				return fail_unmapped(o.line);
		} else if (kind == SIZE) {
			res = format("%zu", size_result);
		} else {
			res = "-";
		}
		out(format("#%zu ", i) + render(o) + " -> " + res + format(" a=%zu\n", a->allocated()));
		out(events);
	}
	g_recording = false;
	out(format("end ops=%zu maps=%llu unmaps=%llu rotations=%llu allocated=%zu\n", ops.size(), norm.maps,
	           norm.unmaps, norm.rotations, a->allocated()));
	return 0;
}

} // namespace

int main(int argc, char** argv) {
	if (argc != 2) {
		fprintf(stderr, "usage: trace_replay <trace-file>\n");
		return 2;
	}
	FILE* in = fopen(argv[1], "rb");
	if (!in) {
		fprintf(stderr, "replay: failed to read %s\n", argv[1]);
		return 2;
	}
	std::string text;
	char buf[65536];
	size_t n;
	while ((n = fread(buf, 1, sizeof buf, in)) > 0)
		text.append(buf, n);
	fclose(in);

	std::vector<Op> ops;
	Failure failure;
	if (!parse(text, &ops, &failure)) {
		fprintf(stderr, "replay: %s: %s (line %zu): %s\n", argv[1], failure.category, failure.line,
		        failure.message.c_str());
		return 1;
	}
	int status = replay(ops);
	if (status != 0)
		return status;
	// Raw bytes, LF line endings: MSVC's text-mode stdout would turn every "\n" into "\r\n".
	_setmode(_fileno(stdout), _O_BINARY);
	fwrite(g_out.data(), 1, g_out.size(), stdout);
	fflush(stdout);
	return 0;
}
