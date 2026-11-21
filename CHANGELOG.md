# Changelog

## 2026.11.3 (2026-11-21)

- 20,659 statements: 695 proved, 58 known false (56 shown by a counterexample, 2 witnessed false), 3 suspected false, 478 blocked by the model, 19,425 open. 524 of the 526 statements that 2026.11.2 proved are still proved, and their statements do not change. Their proofs, on 89 fuzz targets, are repaired for this release's model and checked at it. The other 2 change (below).
- 171 new proofs on 28 fuzz targets in 13 projects: 54 halts, 15 agreement, 15 bound, 15 decidability, 26 classifier-total, 20 classifier-sound and 26 classifier-bound statements. 109 of them are on zlib. Two of those, `zlib/checksum_fuzzer/plain_halts` and `zlib/checksum_fuzzer/plain_halts_may_fail`, replace the proofs that 2026.11.2 had of the same names, because their statements changed (below).
- zlib is now built from zlib 1.4 (madler/zlib at `99623ef7`). 2026.11.2 used zlib 1.3.1. The builds carry 8 patches, each from a public pull request: madler/zlib #1390 and #1361, and google/oss-fuzz #16582, #16316, #16411, #16428 and #16429. [projects/zlib/project.yaml](projects/zlib/project.yaml) lists them.
  - zlib has 384 statements on 10 fuzz targets. 2026.11.2 had 146 of them, for zlib 1.3.1. Each of these 146 statements changes its meaning, and its revision goes from 1 to 2. The other 238 statements are new.
  - zlib publishes 60 classifiers and 36 originals beside its 40 builds, in `zlib-bin.tar.zst`, which also holds the files of two fuzz targets that this release does not describe. Its statements use the new statement kinds (below): 168 of them are classifier statements, and 70 are twins.
  - 109 of zlib's statements are proved, on 8 fuzz targets. Each `_bound_good` and `_bound_diff` proof is at a bound of 0.
    - `zlib/checksum_fuzzer/plain_halts@r2`, `zlib/checksum_fuzzer/plain_halts_may_fail@r2`, `zlib/checksum_fuzzer/{plain,ubsan,asan,asan_ubsan}_halts_any_exit`, `zlib/checksum_fuzzer/{ubsan,asan,asan_ubsan}_agrees_alloc_forced_only`, `zlib/checksum_fuzzer/{ubsan,asan,asan_ubsan}_{ca,cb}_{total,sound}` and `zlib/checksum_fuzzer/{ubsan,asan,asan_ubsan}_bound_{good,diff}`: 27 statements.
    - `zlib/compress_fuzzer/plain_halts_any_exit`: 1 statement.
    - `zlib/example_flush_fuzzer/{plain,ubsan}_halts_any_exit` and `zlib/example_flush_fuzzer/ubsan_agrees_alloc_forced_only`: 3 statements.
    - `zlib/example_large_fuzzer/ubsan_halts_any_exit`, `zlib/example_large_fuzzer/ubsan_agrees_alloc_forced_only`, `zlib/example_large_fuzzer/ubsan_{ca,cb}_{total,sound}` and `zlib/example_large_fuzzer/ubsan_bound_{good,diff}`: 8 statements.
    - `zlib/example_small_fuzzer/{plain,ubsan}_halts_any_exit`: 2 statements.
    - `zlib/zlib_uncompress_fuzzer/{plain,ubsan,asan,asan_ubsan}_halts_any_exit`, `zlib/zlib_uncompress_fuzzer/{ubsan,asan,asan_ubsan}_agrees_alloc_forced_only`, `zlib/zlib_uncompress_fuzzer/{ubsan,asan,asan_ubsan}_{ca,cb}_{total,sound}` and `zlib/zlib_uncompress_fuzzer/{ubsan,asan,asan_ubsan}_bound_{good,diff}`: 25 statements.
    - `zlib/zlib_uncompress2_fuzzer/{plain,ubsan,asan,asan_ubsan}_halts_any_exit`, `zlib/zlib_uncompress2_fuzzer/{ubsan,asan,asan_ubsan}_agrees_alloc_forced_only`, `zlib/zlib_uncompress2_fuzzer/{ubsan,asan,asan_ubsan}_{ca,cb}_total`, `zlib/zlib_uncompress2_fuzzer/ubsan_{ca,cb}_sound` and `zlib/zlib_uncompress2_fuzzer/{ubsan,asan,asan_ubsan}_bound_{good,diff}`: 21 statements.
    - `zlib/zlib_uncompress3_fuzzer/{plain,asan,asan_ubsan}_halts_any_exit`, `zlib/zlib_uncompress3_fuzzer/{ubsan,asan,asan_ubsan}_agrees_alloc_forced_only`, `zlib/zlib_uncompress3_fuzzer/{ubsan,asan,asan_ubsan}_{ca,cb}_total`, `zlib/zlib_uncompress3_fuzzer/{ubsan,asan}_{ca,cb}_sound` and `zlib/zlib_uncompress3_fuzzer/{ubsan,asan,asan_ubsan}_bound_{good,diff}`: 22 statements.
- New statement kinds: classifier statements and twins ([docs/statements.md](docs/statements.md)).
  - A harness can now publish classifiers and originals (`classifiers` and `originals` in `harness.yaml`). A classifier is a static riscv64 program that reads the same input file as the builds. It answers yes (exit 0), no (exit 1) or maybe (exit 2). An original is built by the same recipe as its published build, but with none of the patches. Classifier A is about where the two originals of a sanitizer pair agree. Classifier B is about where each build agrees with its original.
  - `classifier-total` (`<build>_ca_total`, `<build>_cb_total`): the classifier answers on every valid finite input.
  - `classifier-sound` (`<build>_ca_sound`, `<build>_cb_sound`): when the classifier answers yes, its property holds. Where its property holds, it never answers no.
  - `classifier-maybe` (`<build>_maybe_good`, `<build>_maybe_diff`): for an input drawn from `Distribution.v`, the classifier gives no firm answer with probability at most `b`.
  - `classifier-bound` (`<build>_bound_good`, `<build>_bound_diff`): for an input drawn from `Distribution.v`, the classifier does not answer yes with probability at most `b`.
  - The shapes of these statements are in [theories/ClassifierShapes.v](theories/ClassifierShapes.v). The model that this release pins does not have these definitions yet. So the file carries a verbatim copy of their text, and proves each shape equal to its copy. `oft lint` checks that the copy does not change. The fingerprint of a classifier statement also hashes the code of `theories/ClassifierShapes.v`, and the SHA-256 of its classifier and of each original that it names.
  - A twin is a second statement beside a first one. It differs from the first statement in one way, and it has its own name, status and proof. `<build>_halts_any_exit` allows any exit status, beside `<build>_halts`. In `<build>_agrees_alloc_forced_only`, the environment refuses a memory request only when the budget is spent or no address range is free. It sits beside `<build>_agrees`, in which the environment may refuse every kind of call that the model lets fail, at any time.
- The model is now rocq-linux-process-semantics at commit [`c0dd863a`](https://github.com/theorem-labs/rocq-linux-process-semantics/commit/c0dd863a0f8f307beca7f2ee5cb4d7686a875779). 2026.11.2 used commit `f1006fe8`. The pinned checker image is rebuilt from it, at `ghcr.io/theorem-labs/oss-fuzz-theorems-checker@sha256:dbe610615b7e22cf20e45ac04c0740b05ce9d1ad4211006abf546f845fc3f12f`. Every proof of this release, 695 in all, is checked again in that image.
  - The model now describes one system: stable Linux v6.18.46 on riscv64. `f1006fe8` described Linux and QEMU user mode together. Where the two give different answers, the model gives the Linux answer. So a proof does not cover a QEMU run that depends on such a difference. The model's SCOPE.md lists each known difference, and the known soundness gaps of the model ([docs/semantics.md](docs/semantics.md)).
  - The model update moves no fingerprint and no revision, because a fingerprint hashes the model's version string, not its commit. [theories/Premises.v](theories/Premises.v), which shows that the entry and input premises of each shape can hold, changes for the new model.
  - The checker image now holds the model's proof library `LinuxProcessSemantics.Common` and its tactics ([docs/checking.md](docs/checking.md)).
- Trevor Hansen and gabelogan195 proved these statements on the public repository:
  - `libtasn1/asn1_get_length_der_fuzzer/ubsan_{agrees,disagrees_at_most,agreement_decidable}`, by Trevor Hansen ([theorem-labs/oss-verify-proofs#19](https://github.com/theorem-labs/oss-verify-proofs/pull/19)).
  - `cgif/cgif_rgb_fuzzer/ubsan_{disagrees_at_most,agreement_decidable}`, by Trevor Hansen ([theorem-labs/oss-verify-proofs#20](https://github.com/theorem-labs/oss-verify-proofs/pull/20)).
  - `mbedtls/fuzz_pkcs7/{ubsan,asan_ubsan}_{disagrees_at_most,agreement_decidable}`, by Trevor Hansen ([theorem-labs/oss-verify-proofs#21](https://github.com/theorem-labs/oss-verify-proofs/pull/21)).
  - 14 statements of five openssl fuzz targets, by Trevor Hansen ([theorem-labs/oss-verify-proofs#22](https://github.com/theorem-labs/oss-verify-proofs/pull/22)): `openssl/bignum/ubsan_{disagrees_at_most,agreement_decidable}`, `openssl/bndiv/asan_ubsan_{disagrees_at_most,agreement_decidable}`, `openssl/ct/{asan,ubsan}_{disagrees_at_most,agreement_decidable}`, `openssl/echconfiglist_parser/asan_ubsan_{disagrees_at_most,agreement_decidable}` and `openssl/pem/{asan,ubsan}_{disagrees_at_most,agreement_decidable}`.
  - `openssl/hashtable/{ubsan,asan_ubsan}_{disagrees_at_most,agreement_decidable}`, by Trevor Hansen ([theorem-labs/oss-verify-proofs#23](https://github.com/theorem-labs/oss-verify-proofs/pull/23)).
  - `ffmpeg/ffmpeg_AV_CODEC_ID_ADPCM_IMA_WAV_fuzzer/plain_halts`, by Trevor Hansen ([theorem-labs/oss-verify-proofs#24](https://github.com/theorem-labs/oss-verify-proofs/pull/24)).
  - `skcms/iccprofile_info/{asan,asan_ubsan}_halts`, by gabelogan195 ([theorem-labs/oss-verify-proofs#33](https://github.com/theorem-labs/oss-verify-proofs/pull/33)).
  - `glaze/binary_reflection/{plain,ubsan,asan,asan_ubsan}_halts`, by gabelogan195 ([theorem-labs/oss-verify-proofs#35](https://github.com/theorem-labs/oss-verify-proofs/pull/35)).
  - `jsoncons/fuzz_msgpack_encoder/{plain,asan}_halts`, by gabelogan195 ([theorem-labs/oss-verify-proofs#36](https://github.com/theorem-labs/oss-verify-proofs/pull/36)).
  - `zstd/fse_read_ncount/ubsan_halts`, by gabelogan195 ([theorem-labs/oss-verify-proofs#38](https://github.com/theorem-labs/oss-verify-proofs/pull/38)).
  - `zstd/zstd_frame_info/{plain,ubsan}_halts`, by gabelogan195 ([theorem-labs/oss-verify-proofs#40](https://github.com/theorem-labs/oss-verify-proofs/pull/40)).
- 23 more new proofs, by Theorem Labs, on 10 fuzz targets: `cgif/cgif_rgb_fuzzer/ubsan_halts{,_may_fail}`, `coturn/FuzzStunClient/{plain,ubsan,asan,asan_ubsan}_halts`, `jsoncons/fuzz_bigint/{plain,ubsan,asan,asan_ubsan}_halts`, `jsoncons/fuzz_json_cursor/ubsan_{halts,disagrees_at_most,agreement_decidable}`, `libpcap/fuzz_pcap/{asan,asan_ubsan}_halts`, `openssl/bignum/ubsan_halts`, `openssl/bndiv/asan_ubsan_halts`, `openssl/echconfiglist_parser/asan_ubsan_halts`, `skcms/iccprofile_info/{plain,ubsan}_halts` and `spirv-tools/spvtools_binary_parser_fuzzer/asan_ubsan_{halts,disagrees_at_most,agreement_decidable}`.
- The 298 statements of 28 fuzz targets change their meaning: their binaries are built again from fuzz harnesses that Theorem Labs patched. Each statement's revision goes from 1 to 2. No statement is weakened: each one says what it said before about a harness that no longer has the fault.
  - libarchive, 18 fuzz targets. 17 of them, all but `libarchive_fuzzer`, catch `std::bad_alloc` from their own allocations, where they aborted before: 16 free what they opened and return 0, and in `libarchive_write_fuzzer` the write callback returns -1, so that libarchive's write fails. 17 of them, all but `libarchive_write_fuzzer`, also ignore SIGPIPE at the start of each call, as libarchive's own `bsdtar` and `bsdcpio` do. When one of them starts an outside decompression program that stops reading, libarchive's write fails with "broken pipe" and it goes on, where the harness was killed by SIGPIPE. `libarchive_fuzzer` gets only that change.
  - mapserver (2), trafficserver (4) and wt (4), 10 fuzz targets: the harness returns -1 to reject an input, where it returned 1, a value that libFuzzer reserves. mapserver `configfuzzer` and `mapfuzzer` also return 0 where they cannot open their temporary file.
- 249 of these statements are now blocked by the model: their fuzz targets make calls that the model does not cover yet. They were open, all but the 5 of `libarchive_xar_fuzzer` below.
  - `libarchive/libarchive_7zip_fuzzer`, `libarchive/libarchive_ar_fuzzer`, `libarchive/libarchive_cab_fuzzer`, `libarchive/libarchive_cpio_fuzzer`, `libarchive/libarchive_filter_fuzzer`, `libarchive/libarchive_fuzzer`, `libarchive/libarchive_iso9660_fuzzer`, `libarchive/libarchive_lha_fuzzer`, `libarchive/libarchive_mtree_fuzzer`, `libarchive/libarchive_rar5_fuzzer`, `libarchive/libarchive_rar_fuzzer`, `libarchive/libarchive_seek_fuzzer`, `libarchive/libarchive_tar_fuzzer`, `libarchive/libarchive_warc_fuzzer`, `libarchive/libarchive_xar_fuzzer`, `libarchive/libarchive_zip_fuzzer`: threads (`clone` with `CLONE_VM|CLONE_VFORK`: the `vfork` that starts an outside decompression program, on an input that starts with the first bytes of an lrzip, grzip, lz4 or lzop file); resource-limits (`prlimit64` of `RLIMIT_NOFILE`, in the child process of that program); nonblocking-io (`fcntl` with `F_SETFL` and `O_NONBLOCK`, on the pipes to that program); signal-handlers (`rt_sigaction`, which sets SIGPIPE to be ignored, on every input).
  - `libarchive/libarchive_roundtrip_fuzzer`: signal-handlers (`rt_sigaction`, which sets SIGPIPE to be ignored, on every input).
  - `libarchive/libarchive_write_fuzzer`: open-flags (`openat` in `/tmp` with `O_TMPFILE`); other-files (`openat` of a path that the model does not name).
  - `mapserver/configfuzzer`: file-removal (`unlinkat` of a path that the model does not name); other-files (`openat` of a path that the model does not name).
  - `mapserver/mapfuzzer`: file-removal (`unlinkat` of a path that the model does not name); other-files (`openat` of a path that the model does not name); working-directory (`getcwd` with a size of 1024).
  - `trafficserver/fuzz_rec_http`: process-control (`prctl` with `PR_GET_NAME`).
- The statements of 7 fuzz targets stay open: `trafficserver/fuzz_json`, `trafficserver/fuzz_proxy_protocol`, `trafficserver/fuzz_yamlcpp`, `wt/fuzz-css`, `wt/fuzz-eval`, `wt/fuzz-http`, `wt/fuzz-uri`.
- The 5 statements of `libarchive_xar_fuzzer` that 2026.10.1 published as false (witnessed) are no longer published as false: the fault that a witness showed was in the fuzz harness, which no longer aborts. They are blocked by the model, as the other statements of that fuzz target are.
- The changed statements, one line for each fuzz target:
  - `libarchive/libarchive_7zip_fuzzer/*@r2`
  - `libarchive/libarchive_ar_fuzzer/*@r2`
  - `libarchive/libarchive_cab_fuzzer/*@r2`
  - `libarchive/libarchive_cpio_fuzzer/*@r2`
  - `libarchive/libarchive_filter_fuzzer/*@r2`
  - `libarchive/libarchive_fuzzer/*@r2`
  - `libarchive/libarchive_iso9660_fuzzer/*@r2`
  - `libarchive/libarchive_lha_fuzzer/*@r2`
  - `libarchive/libarchive_mtree_fuzzer/*@r2`
  - `libarchive/libarchive_rar5_fuzzer/*@r2`
  - `libarchive/libarchive_rar_fuzzer/*@r2`
  - `libarchive/libarchive_roundtrip_fuzzer/*@r2`
  - `libarchive/libarchive_seek_fuzzer/*@r2`
  - `libarchive/libarchive_tar_fuzzer/*@r2`
  - `libarchive/libarchive_warc_fuzzer/*@r2`
  - `libarchive/libarchive_write_fuzzer/*@r2`
  - `libarchive/libarchive_xar_fuzzer/*@r2`
  - `libarchive/libarchive_zip_fuzzer/*@r2`
  - `mapserver/configfuzzer/*@r2`
  - `mapserver/mapfuzzer/*@r2`
  - `trafficserver/fuzz_json/*@r2`
  - `trafficserver/fuzz_proxy_protocol/*@r2`
  - `trafficserver/fuzz_rec_http/*@r2`
  - `trafficserver/fuzz_yamlcpp/*@r2`
  - `wt/fuzz-css/*@r2`
  - `wt/fuzz-eval/*@r2`
  - `wt/fuzz-http/*@r2`
  - `wt/fuzz-uri/*@r2`
- No other statement's fingerprint or revision changes, so every other published pin still holds.
- `./oft check` now has dune build each proof directory once, with an empty dune cache of its own, and checks the `.vo` files that dune built. It no longer compiles each proof file itself. Its log says how many library targets it compiled and how many rules it ran. It builds the whole `OSSVerify.Core` theory.
- `./oft check` compares each binary that it reads with its pin in `harness.yaml`, whatever `--parts` names. Before, only a run whose `--parts` named statements compared them.
- `oft lint` refuses a bound proof whose `proof.yaml` names a bound of 1 or more: a `_disagrees_at_most` proof, or a classifier-bound or classifier-maybe proof. At such a bound the statement holds trivially. Every bound proof of this release is at a bound of 0.
- The pages and the `Statements.v` comments that `oft generate` writes say only what each statement says. `oft lint` refuses a counterexample witness that cannot refute the statement that it is attached to.
- `harness.yaml` can now say how a fuzz target's binaries differ from OSS-Fuzz's build, which scenarios they leave out and what a debug build adds. `oft generate` writes the left-out scenarios and the debug builds into the generated pages. Each statement can carry one input on which its premises hold, and `oft lint` and `./oft check` check it.
- `oft lint` checks each `Read from:` comment in a proof file of a fuzz target. The comment must name a build that the fuzz target's own `harness.yaml` publishes. Each SHA-256 in it, other than that of the build's unstripped copy, must be the pin of that build.
- `harness.yaml` accepts `rust-allocator-shim`, rustc's allocator shim, as uninstrumented code in the `asan` and `asan-ubsan` builds of a Rust fuzz target.
- `./oft lint --release` accepts a build record of a port-built project whose builder image is one that its project lists. A build record of a recipe-built project must still name the first image of `images.builder`, and lint now says why when it does not.
- A proof that writes its own `(see <path>)` or `File "<path>"` text can no longer make `./oft lps-impact` read a file outside its run.
- `./oft prove --json` names its schema, `oss-verify/prove/1`.
- `tools/budgetwit/` is new. It reads a released Rocq library as text and writes the files of a budget-premise witness for a fuzz target (Known issue, below). It runs no Rocq.
- In the pull request checks, the job `lps_pin` runs for each change to `release.yaml`, `toolchain/` or `theories/`. It checks that the model files of `release.yaml`'s `semantics.commit` hash to the pin in `toolchain/checker.Dockerfile`, verifies the attestation of the pinned checker image, and compiles `theories/` in that image. For a new checker pin, it also holds the image to the change's own build definition.
- Three new pull request checks. `held-content` refuses a pull request that adds a line that matches one of its detectors. `statement-freeze` prints one line for each change to a `Statements.v` or to a row of `index/statements.tsv`, and fails until a code owner approves that head of the pull request. `pin-coherence` requires that a change to a build's `sha256` gives each statement about that build a new fingerprint, and leaves the statement `open` unless a proof of that fuzz target changes in the same pull request.
- Two changes from the public repository: `oft lint` names the files of the public repository's review by their exact paths ([theorem-labs/oss-verify-proofs#47](https://github.com/theorem-labs/oss-verify-proofs/pull/47)), and the tests of the plan step for a push set `GITHUB_REPOSITORY` ([theorem-labs/oss-verify-proofs#46](https://github.com/theorem-labs/oss-verify-proofs/pull/46)).

### Known issue

- Each proved agreement statement, and each proved halts statement except the nine `*_halts_may_fail` statements, assumes that the run stays in its memory budget. The premise is `~ run_scfg_budget_refused` or its equivalent, in [theories/Shapes.v](theories/Shapes.v). This release proves 492 such statements. For 281 of them, on 82 fuzz targets in 31 projects, a file `BudgetWitness.v` in the fuzz target's `proofs/lib/` shows that this premise holds on one input, together with the statement's other premises. In each case that input does not give the program the arguments it expects, so the program prints its usage line and exits before it reaches the fuzz target. For the other 211 statements it is not shown. No classifier statement has a budget premise.

## 2026.11.2 (2026-11-08)

- 20,421 statements: 526 proved, 63 known false (56 shown by a counterexample, 7 witnessed false), 3 suspected false, 229 blocked by the model, 19,600 open.
- 56 statements on eight FFmpeg decoder fuzz targets are false: seven statements each on `ADPCM_VIMA`, `BMV_AUDIO`, `IMC`, `RA_144_DEC`, `RA_288`, `SBC_DEC`, `SIPR` and `SIREN`. For each statement, the repository holds a counterexample: an input that `./oft check` runs to show the statement false. The 56 statements share 32 inputs. They came in [theorem-labs/oss-verify-proofs#18](https://github.com/theorem-labs/oss-verify-proofs/pull/18). 2026.11.1 had no counterexample.
- No statement is newly proved. No statement's fingerprint or revision changes, so every published pin still holds.
- `./oft check` now ends a run with `VOID` and exit status 7 in two cases: the run was asked to check statements or proofs but compiled no file, or, with `--facts-from`, a fuzz target's saved facts file is missing, unreadable or does not match the checkout. `VOID` is neither a pass nor a fail.
- When a build fails, `./oft check` quotes the first `Error:` blocks of the build log, up to five, in its error message. If the log has no `Error:` line, it quotes the log's last lines.
- `./oft check` now gives each run of a binary on a counterexample or finding input 1,620 seconds, up from 600. Two of FFmpeg `SIPR`'s counterexample runs take about 535 seconds each on one runner, and they ran past 600 seconds on another runner of the same type. 1,620 is three times 535, rounded up.
- `./oft check` runs dune with as many jobs as its container's CPU quota allows, or `OFT_JOBS` if that is set, and never more than the CPUs it may use. Before, it used one job for each CPU it could run on.
- In a sparse checkout, `./oft check` refuses to run when a fuzz target's proof library (`proofs/lib/`) is left out. It names each missing library and the command that adds it.
- `./oft fetch` no longer refuses an archive that also holds binaries of fuzz targets this checkout has no build record for. It skips those files and says how many it skipped.
- `docs/adding-a-proof.md`, requirement 8, now exempts a file that shows a released statement's premises can all hold, and each file it needs, because no released `Proof.v` requires them.
- In the pull request checks, a failed check's log is printed only when it is a regular file inside that run's log folder. The checks delete symbolic links before they upload logs, so a link that a build leaves cannot upload another file.

### Known issue

- Each proved agreement statement, and each proved halts statement except the eight `*_halts_may_fail` statements, assumes that the run stays in its memory budget. The premise is `~ run_scfg_budget_refused` or its equivalent, in [theories/Shapes.v](theories/Shapes.v). A new theorem, in `projects/libreac/fuzz_knock/proofs/lib/BudgetWit/BudgetWitness.v`, shows that this premise holds for libreac `fuzz_knock` `plain_halts` on one input. That input does not give the program the arguments it expects, so the program prints its usage line and exits before it reaches the fuzz target. For every other proved statement it is not shown.

## 2026.11.1 (2026-11-05)

- 20,421 statements: 526 proved (336 in 2026.11.0), 7 known false, 3 suspected false (an argument from reading the source, not yet a run or a proof; [docs/status.md](docs/status.md)), 229 blocked by the model, 19,656 open.
- 190 new proofs on 30 fuzz targets in 7 projects: 113 halts and 77 agreement statements.
- Seven projects are new, with 257 statements on 35 fuzz targets. libreac (9 fuzz targets), omx-clap-core (3) and plugin-hostd (2) are proved in full, 100 statements. reac-pw has 47 of its 51 statements proved, libdiginet 22 of 30 and reac-repacer 20 of 28. omx-dsp's 48 statements have no proof yet.
- The halts statements of five fuzz targets allow exit status 78 as well as 0 and 2: brpc `fuzz_http_parser`, lldpd `fuzz_lldp`, pupnp `FuzzIxml`, spice-usbredir `usbredirfilterfuzz` and wavpack `fuzzer`. Each of these fuzz targets returns a value other than 0 or -1 to turn away an input it does not take: 1, or for pupnp also an IXML error code. libFuzzer treats such a return as a rejected input, and the driver then exits with status 78. A harness names these places as `rejects` in `harness.yaml`. In pupnp `FuzzIxml`, a failure of its return-only check at `FuzzIxml.c:23-27` also exits 78, and this release allows that too. No other statement's fingerprint changed ([docs/statements.md](docs/statements.md#halting-build_halts-build_halts_may_fail)). The 20 statements, each at its new revision:
  - `brpc/fuzz_http_parser/{plain,ubsan,asan,asan_ubsan}_halts@r2`
  - `lldpd/fuzz_lldp/{plain,ubsan,asan,asan_ubsan}_halts@r2`
  - `pupnp/FuzzIxml/{plain,ubsan,asan,asan_ubsan}_halts@r2`
  - `spice-usbredir/usbredirfilterfuzz/{plain,ubsan,asan,asan_ubsan}_halts@r2`
  - `wavpack/fuzzer/{plain,ubsan,asan,asan_ubsan}_halts@r2`
- Rares Buhai contributed the proof of `zlib/checksum_fuzzer/plain_halts_may_fail` on the public repository ([theorem-labs/oss-verify-proofs#7](https://github.com/theorem-labs/oss-verify-proofs/pull/7)).
- The static AddressSanitizer now lives in [asan-static](https://github.com/theorem-labs/asan-static). Its former name, static-asan, redirects there. The build records of this release still name static-asan. The toolchain is the same commit `b05061352064`, which that repository tags `static-asan-2026.10.0`.
- The Rocq namespace is now `OSSVerify`. It was `OssFuzzTheorems`. The opam packages are now `rocq-oss-verify-*`. They were `rocq-oss-fuzz-theorems-*`. A proof written for an earlier release needs one change: each module path that starts `OssFuzzTheorems.` must start `OSSVerify.`, in its `From ... Require` lines. `./oft generate` writes the new names into the dune files. No statement changes its meaning, its fingerprint or its revision, so every published pin still holds.
- The pinned checker image is rebuilt, at `ghcr.io/theorem-labs/oss-fuzz-theorems-checker@sha256:063f93261f11ba449f1c3825884fadc65cf1fc836d4a3ee534633211abbdc3eb`. It holds the step in `toolchain/checker.Dockerfile` that no longer trusts five root certificates.
- `./oft fetch` can now read a binary from a release that has no public download URL, such as a draft release or a release of another repository. Set `OFT_RELEASES_REPO=<owner>/<repo>`, and put a token in `GH_TOKEN` or `GITHUB_TOKEN`. `fetch` then reads each asset from that repository's release of the same tag through the GitHub API, with the same size and SHA-256 checks. `fetch` does not send the token to the storage host that the API redirects to. Without the variable, `fetch` uses the public release URL as before, and an HTTP 404 there now says what to set.
- `./oft check` now asks for a 2 GiB stack for the `rocq`, `rocqchk` and `dune` processes it starts, instead of the largest stack the hard limit allows. Under a lower hard limit it takes that limit and runs; it no longer refuses to start. A container runtime can give a process less stack than the limit says, so the check measures the stack that a process it starts really gets. A step that runs out of stack now fails as `stack exhausted at <N> MiB` and names its log.
- Proof files made from Anthropic's proofs carry Anthropic's licence lines (`Apache-2.0 OR MIT`), and `oft lint` checks them.
- `docs/versioning.md` no longer says that tags are never deleted. A release can be withdrawn, which deletes its GitHub release and its tag, as 2026.10.2 was.
- The proofs have 83 lines with a wall-clock time limit, each with a comment that gives the reason, and `oft lint` refuses a limit without one. 2026.11.0 had 59, and the new projects bring 24. On a slow machine, a remaining limit can make a proof fail.

### Known issue

- Each proved agreement statement, and each proved halts statement except the eight `*_halts_may_fail` statements, assumes that the run stays in its memory budget. The premise is `~ run_scfg_budget_refused` or its equivalent, in [theories/Shapes.v](theories/Shapes.v). No theorem shows yet that this is true for a released build. This also applies to 2026.10.0, 2026.10.1 and 2026.11.0.

## 2026.11.0 (2026-11-01), a patch release

- 277 proof-library files in 37 units are rewritten. In 1 of them the rewritten text came out byte-identical to the released text; the rest change. Where a released file carries a copyright or attribution notice, the rewritten file keeps it unchanged.
- Release v2026.10.2 is withdrawn. v2026.10.1 and v2026.10.0 are unchanged.
- No statement changes. Library definitions that now say something different include these five groups:
  - `XENV_CORE_FPA` in `proofs/simdjson/fuzz_dump_raw_tape/lib/B/X_xdefs.v`: four lemmas keep byte-identical statements that cover 64 bytes fewer and 248 bytes more. The unit's top theorem `main_rta` and its assumptions are unchanged. A definition of the same name stands in eight other units; the three whose `X_xdefs.v` is also rewritten were checked and are unaffected.
  - `hs_xenv_ok` in `proofs/simdjson/fuzz_dump_raw_tape/lib/B/HandoffCLX.v`: for eleven one-byte slots from 0x6aa3e0 to 0x6aa3ea it requires only that the bytes can be read and written, where the released text also required the state's knowledge table to give a literal byte for each. Lemmas that assume it now assume less. The checks on the unit's four certified states now check less, and those four states satisfy the released definition too. `Print Assumptions` for the unit's top theorems gives the same output as before.
  - `XENV_FPA` in `proofs/openssl/pem/lib/A/X_xdefs.v`: it covers 32 bytes fewer, the range [0x669460, 0x669480), which lies in no section. Each of the seven statements that name it is proved equivalent to its published form, using three proved facts about those 32 bytes.
  - `common_facts` and `common_facts3` in `proofs/cgif/cgif_rgb_fuzzer/lib/UI2s.v`: two of their bounds are narrower, `4096 .. CEIL_MAX - 1` and `CEIL_MIN + 8560 .. 2^63 - 184`. Four published lemmas name them, and each is proved to claim at least what the released version did; every other use is inside a proof.
  - `lib0_statics` in `proofs/openssl/pem/lib/A/Fz_lib0.v`: it requires 192 more bytes to be zero and writable, 12 objects of `crypto/init.c` and three runs inside `default_context_int`. The two theorems that take it as a premise, `fuzz_init_A` and `fuzz_init_closed`, now assume more. The kept `lib0_at_main_A` proves the stronger form holds at `main` in the pinned `pem.asan`.
- Each proved agreement statement, and each proved halts statement except one, assumes that the run stays in its memory budget. The premise is `~ run_scfg_budget_refused` or its equivalent, in [theories/Shapes.v](theories/Shapes.v). No theorem shows yet that this is true for a released build. This also applies to 2026.10.0 and 2026.10.1.
- The proofs had 456 lines with a wall-clock time limit. 59 remain, each with a comment that gives the reason, and `oft lint` refuses a limit without one. On a slow machine, a remaining limit can make a proof fail.
- The pinned checker image predates the step in `toolchain/checker.Dockerfile` that no longer trusts five root certificates (four of emSign and Comodo's AAA Certificate Services). No result depends on it, because every check runs with no network. A later release rebuilds the image and pins it.

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
