# Oris

*A high-performance heap allocator, after the folk-allotters of fate.*

A Rust and Zig port of Dimitar Lazarov's **HPHA** (2007).

**Working draft — v0.4. No code shipped yet.**

## Status

This is a project repository at the design-document stage. The two foundational documents are:

- **[BRIEF.md](BRIEF.md)** — design rationale, etymological grounding, target workloads, prior-art positioning
- **[ROADMAP.md](ROADMAP.md)** — milestones, versioning policy, the cross-language invariant

## Structure

- **[Cpp/](Cpp/)** — the canonical HPHA reference source from 2007, included for diff and reference purposes. See [Cpp/NOTICE.md](Cpp/NOTICE.md) for the license trail.
- **`Rust/`** — the `orisnik` crate *(forthcoming, v0.1.0)*
- **`Zig/`** — the `orisnitsa` module *(forthcoming, v0.1.0)*

## License

Dual-licensed under [MIT](LICENSE-MIT) OR [Apache-2.0](LICENSE-APACHE), at your option — see [LICENSE](LICENSE).

The HPHA reference source under `Cpp/` retains its original 2007 copyright header verbatim and is included under the same dual license, consistent with the public license trail established by the [Open 3D Engine](https://github.com/o3de/o3de) project. See [Cpp/NOTICE.md](Cpp/NOTICE.md) for full provenance.
