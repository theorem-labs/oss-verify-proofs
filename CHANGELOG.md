# Changelog

## 2026.10.2 (2026-10-27), a patch release

- 20,164 statements: 336 proved (202 in 2026.10.1), 5 known false, 229 blocked by the model, 19,594 open.
- 134 new proofs on 42 fuzz targets in 20 projects: 46 decidability, 46 bound, 40 agreement and 2 halts statements.
- No published statement changes its meaning. No binary or source tree is new.
- The proofs had 456 lines with a wall-clock time limit. 59 remain, each with a comment that gives the reason, and `oft lint` refuses a limit without one. On a slow machine, a remaining limit can make a proof fail.

### Known issue

- Each proved agreement statement, and each proved halts statement except one, assumes that the run stays in its memory budget. The premise is `~ run_scfg_budget_refused` or its equivalent, in [theories/Shapes.v](theories/Shapes.v). No theorem shows yet that this is true for a released build. This also applies to 2026.10.0 and 2026.10.1.

## 2026.10.1 (2026-10-27), a patch release

The second release. 1,381 OSS-Fuzz projects, 427 of them available, with 2,148 harnesses; 8,578 binaries, all attached to v2026.10.0, and 0 withheld. 20,164 statements: 202 proved, 5 known false (witnessed), 229 blocked by the model, 0 withheld; the other 19,728 are open. 2026.10.0 had no statement known false.

The 202 proved statements cover 61 fuzz targets in 26 projects. This release adds 64 of them, all halts statements, the first proofs of that kind here: 63 on 24 fuzz targets that had proofs in 2026.10.0, and the proof of zlib's `checksum_fuzzer` `plain_halts`, described below. More statements of these fuzz targets are proved but are not in this release; they come in a later one.

Five statements of libarchive_xar_fuzzer that let a memory request fail are now false (witnessed); analyses/known-issues.md gives the run that shows each. A statement may now allow exit 78 where a fuzz target lists its rejects; no fuzz target lists any yet. Statement fingerprints are now version 2: each hashes the code of `Shapes.v` and `Images.v`, not their comments or layout. So every fingerprint changes, and `oft revisions` with `--write-pins` wrote each of the 138 published pins again in version 2. No statement published in 2026.10.0 changes its meaning.

A known limit of the agreement statements. 129 of this release's 202 proved statements are agreement statements with the reading `alloc-forced-only`, and 2026.10.0 published the same 129. Each compares a fuzz target's plain and sanitizer builds and says: on every input where the plain build stays within its memory budget, neither build crashes and both write the same output. This is exact except when our Linux model lays out memory in a way real Linux would not, and refuses a large request Linux would grant. A program that reacts to that refusal can push an input out of the statement, or hide an output difference. Test programs show this; we have not shown it in a released fuzz target. Every proof still passes its check. We plan to close the gap in the next release.

Rares Buhai contributed the proof of `zlib/checksum_fuzzer/plain_halts` on the public repository ([theorem-labs/oss-verify-proofs#3](https://github.com/theorem-labs/oss-verify-proofs/pull/3)), the first proof from outside Theorem Labs. Its library reuses files of the cgif and Varnish proofs, which stay under Apache-2.0 OR MIT; each file he changed says so in a line under its licence header, and the build record says where each part came from.

The release machinery is new: CI reads draft releases, a release can be uploaded in parts, `oft release-tree` cuts a release to the proofs an approvals file lists, and `oft approvals` writes that file. The adding-a-proof skill is new, and docs/licensing.md and NOTICE are revised.

This release attaches no binaries and no source trees of its own. Every binary and source tree it pins stays attached to v2026.10.0, v2026.10.0-src or sources-v1. It publishes proofs and documents only, with no v2026.10.1-src release beside it.

### Known issue: the model's stack window is larger than Linux gives

The process model maps 8 MiB of stack below the entry stack pointer. It puts the entry image (the arguments, the environment and the auxiliary vector) above that stack pointer. Linux counts the entry image inside its 8 MiB stack limit. Thus, on a real launch, the model can give a program more stack than Linux gives.

The proofs of these statements depend on a model fact about stack near that limit:

- msgpack-c/unpack_pack_fuzzer/asan_halts and msgpack-c/unpack_pack_fuzzer/asan_ubsan_halts. This release proves them for the first time.
- msgpack-c/unpack_pack_fuzzer/asan_agrees, msgpack-c/unpack_pack_fuzzer/ubsan_agrees and msgpack-c/unpack_pack_fuzzer/asan_ubsan_agrees.
- glaze/binary_reflection/asan_agrees, glaze/binary_reflection/ubsan_agrees and glaze/binary_reflection/asan_ubsan_agrees.

The msgpack-c proofs depend on files that treat stack down to 8,384,512 bytes below the entry stack pointer as available. The glaze proofs depend on files that treat stack down to 8,388,560 bytes below the entry stack pointer as available. We made five launches of a test program on real Linux, with an empty environment, the program name and one argument. In those launches, the available stack was between 8,382,288 and 8,387,440 bytes below the entry stack pointer. A launch with a larger environment or larger arguments has less stack.

We know no input that makes either program use that much stack. We ran both programs with a 128 KiB stack under the emulator that our checks use. They ran correctly on every input that we tried. For msgpack-c, these inputs included data nested 1,000 levels deep. But the proofs do not show that the programs stay inside the real limit.

The model correction and new proofs of these statements will come in a later release. Thank you to the reporter of rocq-linux-process-semantics#6, who found the difference.

### Known issue: the memory-budget premise

- Each proved statement of this release assumes that the run stays in its memory budget (`~ run_scfg_budget_refused` or its equivalent, in [theories/Shapes.v](theories/Shapes.v)). No theorem shows yet that this is true for a released build.

## 2026.10.0 (2026-10-22)

The first release. 1,381 OSS-Fuzz projects, 427 of them available, with 2,148 harnesses; 8,578 binaries attached and 0 withheld. 20,164 statements: 138 proved, 229 blocked by the model, 0 withheld; the other 19,797 are open.

The 138 proved statements cover 60 fuzz targets in 25 projects. Their proofs were made from proofs that Anthropic licensed under the Apache License 2.0 or the MIT licence, ported to this release's binaries; each such file says so in a line under its licence header. Two projects, mariadb and wazuh, are held from this release because their only binary combines an Apache-2.0 harness with GPL-2.0-only code.
