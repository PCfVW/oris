# SPDX-License-Identifier: MIT OR Apache-2.0
"""Turns mimalloc-bench's benchres.csv into a Markdown summary (summary.md, next to it).

    python3 summarize.py <results-dir>

benchres.csv has one line per (test, allocator, run): elapsed time (m:ss.cc or seconds), peak
RSS in KiB, user and system seconds. Repeated runs are reduced to their median. The summary
has one table for time and one for peak RSS, each with the allocator's value relative to
glibc (`sys`) in parentheses. benchmarks/scripts/aggregate appends it to SUMMARY.md.
"""
import json
import statistics
import sys
from collections import defaultdict
from pathlib import Path

ORDER = ["sys", "mi", "je", "sn", "onik", "onit"]
NAMES = {"sys": "glibc", "mi": "mimalloc", "je": "jemalloc", "sn": "snmalloc", "onik": "**orisnik**", "onit": "**orisnitsa**"}
# Tests that run for a fixed time and report throughput: bench.sh replaces their elapsed time
# by a relative time (inverse throughput), and their peak RSS grows with the work done.
FIXED_TIME = ("larson", "rptest", "xmalloc", "glibc-thread")
# Tests that allocate from several threads: Oris serializes them behind its shim's lock.
THREADED = ("larson", "mstress", "rptest", "alloc-testN", "sh6bench", "sh8bench", "xmalloc", "cache-scratchN", "cache-thrashN", "glibc-thread")


def seconds(text):
    if ":" in text:
        minutes, secs = text.split(":", 1)
        return int(minutes) * 60 + float(secs)
    return float(text)


def main(results):
    results = Path(results)
    time = defaultdict(list)
    rss = defaultdict(list)
    tests = []
    for line in (results / "benchres.csv").read_text().splitlines():
        if not line.strip() or line.startswith("#"):
            continue
        fields = line.split()
        test, alloc = fields[0], fields[1]
        if test not in tests:
            tests.append(test)
        time[test, alloc].append(seconds(fields[2]))
        rss[test, alloc].append(int(fields[3]) / 1024.0)
    allocs = [a for a in ORDER if any((t, a) in time for t in tests)]
    env = json.loads((results / "env.json").read_text())
    out = []
    out.append("## mimalloc-bench\n")
    out.append(
        f"[mimalloc-bench](https://github.com/daanx/mimalloc-bench) at commit `391382606681` with "
        "Oris added as two `LD_PRELOAD` shims (`benchmarks/mimalloc-bench/`): `orisnik` and "
        f"`orisnitsa`. {env['os']}, {env['cpu']}, {env['logical_cores']} logical cores, "
        f"{env['ram_gb']} GB RAM; commit `{env['commit']}`, {env['date']}. Median of the runs.\n"
    )
    out.append(
        "**Read the threaded rows with care.** Oris is a single-threaded allocator; its shims put "
        "one global lock around every call, so a multithreaded test (marked †) measures Oris "
        "*serialized*, not a multithreaded Oris (that is v2.x on the roadmap). The shims also "
        "round every request up to 16 bytes, the alignment `malloc` owes its callers.\n"
    )
    out.append(
        "**Rows marked ‡ run for a fixed time.** mimalloc-bench reports their *time* as a relative "
        "time derived from throughput (lower is better, as for elapsed time), and their *peak RSS* "
        "grows with the work done in that time — so a slower allocator can look leaner.\n"
    )
    for title, data, fmt in (("Elapsed time, seconds (‡ relative time)", time, "{:.2f}"), ("Peak RSS, MiB", rss, "{:.1f}")):
        out.append(f"### {title} (relative to glibc)\n")
        out.append("| test | " + " | ".join(NAMES[a] for a in allocs) + " |")
        out.append("|---|" + "---:|" * len(allocs))
        for test in tests:
            base = statistics.median(data[test, "sys"]) if (test, "sys") in data else None
            cells = []
            for a in allocs:
                if (test, a) not in data:
                    cells.append("—")
                    continue
                v = statistics.median(data[test, a])
                rel = f" ({v / base:.2f}×)" if base and a != "sys" else ""
                cells.append(fmt.format(v) + rel)
            mark = (" †" if test.startswith(THREADED) else "") + (" ‡" if test.startswith(FIXED_TIME) else "")
            out.append(f"| {test}{mark} | " + " | ".join(cells) + " |")
        out.append("")
    (results / "summary.md").write_text("\n".join(out) + "\n", encoding="utf-8")
    print(f"wrote {results / 'summary.md'}")


if __name__ == "__main__":
    main(sys.argv[1])
