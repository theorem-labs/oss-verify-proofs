# Patch style and report preferences

reac-repacer is FreeREAC's de-jitter relay: it sits between a Wi-Fi link and the REAC stageboxes of a Roland mixer,
buffers the bursty stream and re-emits it at a steady cadence. It relays REAC frames without decoding them, but it
reads a few bytes of each frame off the wire to decide what to do with it (`src/repace_wire.c`: the forward reader,
the return relay, the downstream listener, the clock meter and the inject-copy reader), writes a few bytes into each
frame it emits (the counter restamp, the rate-change mute and the test injectors), and reads two texts besides its
command line (`src/repace_conf.c`: the warm-start lock it wrote on an earlier run, and the `uci get` reply on SIGHUP).
Those readers are the code that matters most here, and the four fuzz targets drive them. The frame readers face the
network; they matter most of all.

## How findings and patches land

Nothing from the pipeline enters reac-repacer as it is. A maintainer reads each finding, reproduces it against the
reac-repacer harness and build, and writes the fix in FreeREAC/reac-repacer as an ordinary change. A patch you send
is a description of a fix, and we re-author it before it lands.

Every commit in reac-repacer is signed. No attribution line, trailer, or generated-by marker enters the history. When
a finding leads to a fix, we quote its id in the reac-repacer issue that tracks the fix, not in a commit.

## Which findings to report

Report all of them. A memory-safety bug in a frame reader is the most severe: a write out of bounds first, then a read
out of bounds, then undefined behaviour that a sanitizer traps. A property check that fails is a bug of the same rank
as the code it guards: a frame the relay takes or drops against its rule reaches, or fails to reach, a stagebox. A
finding without a patch is welcome. Put findings that share one cause in one report.

Bugs that no fuzz target can hit are welcome too, with the input or the reasoning that reaches them. The daemon's
sockets, threads, pacing clock and command line have no harness (`fuzz/README.md` says what is left out and why); a
finding there is welcome with the reasoning that reaches it.

## Which patches to write

- A fix is minimal: the smallest change that removes the bug, with a test under `tests/` that fails before the fix and
  passes after it. An input that finds the bug goes into `fuzz/gen-corpus.c` as well, under a name that says what it
  is, so the committed corpus replays it.
- The readers allocate nothing. A stop after the harness's own allocation failed is not a property.
- The frame geometry and the braid byte map are libreac's (`reac_frame_clean_len`, `reac_braid_pos`). A fix does not
  make a second copy of them in reac-repacer; a fix to them goes to FreeREAC/libreac.
- Patches that change only the documentation are welcome.
- A refactoring that makes the code easier to verify is welcome only if it keeps the behaviour, and only with a test
  that shows it. The bytes the inject paths write are pinned by `tests/test_inject.c`'s goldens.

## Patch format

- Plain C11, in the style of the file you change: tabs, braces as the file has them, `/* */` comments.
- One change per commit. The subject line says what the change does, in the present tense. The body is plain prose
  that says why, with the numbers it measured.
- Comments and commit messages describe the code as it is, not how it came to be.

## What the proofs mean for us

A proof is about the static riscv64 binary that this directory builds, under Theorem's RISC-V and Linux process
semantics. It does not transfer by itself to the OpenWrt and Fedora packages that we ship, which are built by other
compilers for other targets. A proof removes classes of bugs from the code that the fuzz targets drive. It does not
certify a shipped binary, and we do not describe it as if it did.
