# Patch style and report preferences

omx-clap-core is FreeMixer's in-process CLAP hosting library, with a JACK worker, a plugin scanner and an LV2-to-CLAP
adapter. Three readers parse bytes that people and other programs write: the preset file (`pj_parse` and the writer
`pj_write` in `src/preset_file.c`), the base64 state body a preset carries (`preset_base64_decode` and
`preset_base64_encode`), and the `manifest.ttl` of every bundle on the LV2 path (`lv2_locate_manifest_names` in
`src/lv2_locate.c`). They are the code that matters most here, and the three fuzz targets drive them.

## How findings and patches land

Nothing from the pipeline enters omx-clap-core as it is. A maintainer reads each finding, reproduces it against the
omx-clap-core harness and build, and writes the fix in FreeMixer/omx-clap-core as an ordinary change. A patch you send
is a description of a fix, and we re-author it before it lands.

Every commit in omx-clap-core is signed. No attribution line, trailer, or generated-by marker enters the history. When
a finding leads to a fix, we quote its id in the omx-clap-core issue that tracks the fix, not in a commit.

## Which findings to report

Report all of them. A memory-safety bug in a reader is the most severe: a write out of bounds first, then a read out of
bounds, then undefined behaviour that a sanitizer traps. A property check that fails is a bug of the same rank as the
code it guards. A finding without a patch is welcome. Put findings that share one cause in one report.

Bugs that no fuzz target can hit are welcome too, with the input or the reasoning that reaches them. The host also
loads plugins and talks to JACK; those parts have no harness (see `fuzz/README.md` for what is left out and why), and a
finding there is welcome with the reasoning that reaches it.

## Which patches to write

- A fix is minimal: the smallest change that removes the bug, with a test under `tests/` that fails before the fix and
  passes after it. An input that finds the bug goes into `fuzz/corpus/<harness>/` as well.
- The readers survive a refused allocation, and the harnesses refuse allocations on purpose (`fuzz/alloc.c`). A stop
  after the harness's own allocation failed is not a property.
- Patches that change only the documentation are welcome.
- A refactoring that makes the code easier to verify is welcome only if it keeps the behaviour, and only with a test
  that shows it.

## Patch format

- Plain C11, in the style of the file you change: four spaces, braces on their own lines, `/* */` comments.
- One change per commit. The subject line says what the change does, in the present tense. The body is plain prose
  that says why.
- Comments and commit messages describe the code as it is, not how it came to be.

## What the proofs mean for us

A proof is about the static riscv64 binary that this directory builds, under Theorem's RISC-V and Linux process
semantics. It does not transfer by itself to the x86-64 glibc packages that we ship. A proof removes classes of bugs
from the code that the fuzz targets drive. It does not certify a shipped binary, and we do not describe it as if it
did.
