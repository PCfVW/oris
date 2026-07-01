# Changelog

All notable changes to Oris are documented here. The format is based on
[Keep a Changelog](https://keepachangelog.com/en/1.1.0/), and the project adheres to
[Semantic Versioning](https://semver.org/spec/v2.0.0.html).

Both ports ship in lockstep: one version number covers `orisnik` (crates.io) and
`orisnitsa` (GitHub Release), carrying the same feature set and the same internal
state transitions (see [`ROADMAP.md`](ROADMAP.md)).

## [Unreleased]

### Added

- Project scaffolding ahead of the v0.1.0 allocator implementation:
  - Rust (`orisnik`, edition 2024 / MSRV 1.85) and Zig (`orisnitsa`, 0.16.0) stub
    packages that build and test green.
  - `Grit-ORIS` coding conventions and AI-assist wiring (`CLAUDE.md`) for both ports.
  - CI for both ports (3-OS matrix; Rust adds a Miri soundness lane) with aggregator
    gate checks, crates.io **Trusted Publishing**, and a re-rooted Zig release asset
    with a recorded `zig fetch` hash.
  - `INSTALL.md`, `SECURITY.md`, README badges, Dependabot, and the Rust lint floor.

<!-- On cutting v0.1.0, add a dated section and move the shipped items here:
## [0.1.0] - YYYY-MM-DD
-->
