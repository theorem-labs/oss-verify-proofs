# Patch style and report preferences

libdiginet is FreeMixer's library for the DigiNet protocol, the raw Ethernet protocol that the
Digidesign Control|24 and ProControl control surfaces speak (EtherType 0x885F). It reads every
byte a desk sends: the frame and its header (`diginet_frame_parse` and `diginet_announce_parse`
in `src/diginet_frame.c`), the command stream of a data frame (`diginet_msg_next` in
`src/diginet_msg.c`), the controls in it (`diginet_decoder_next` in `src/diginet_decode.c`), and
the session those frames drive (`diginet_session_rx` and the rest of
`transport/src/diginet_session.c`). These readers are the code that matters most here, and the
four fuzz targets drive them, with the encoders of `src/diginet_codec.c`.

## How findings and patches land

Nothing from the pipeline enters libdiginet as it is. A maintainer reads each finding,
reproduces it against the libdiginet harness and build, and writes the fix in
FreeMixer/libdiginet as an ordinary change. A patch you send is a description of a fix, and we
re-author it before it lands.

Every commit in libdiginet is signed. No attribution line, trailer, or generated-by marker
enters the history. When a finding leads to a fix, we quote its id in the libdiginet issue that
tracks the fix, not in a commit.

## Which findings to report

Report all of them. A memory-safety bug in a reader of desk bytes is the most severe: a write
out of bounds first, then a read out of bounds, then undefined behaviour that a sanitizer
traps. A property check that fails is a bug of the same rank as the code it guards. A frame the
session sends that holds the system family `F0 13 xx 70` is as severe as a memory-safety bug,
because that family writes the desk's memory. A finding without a patch is welcome. Put findings
that share one cause in one report.

Bugs that no fuzz target can hit are welcome too, with the input or the reasoning that reaches
them. The packet socket and the descriptor io (`transport/src/diginet_io.c`) and the
`diginet-probe` tool have no harness (`fuzz/README.md` says why); a finding there is welcome
with the reasoning that reaches it.

## Which patches to write

- A fix is minimal: the smallest change that removes the bug, with a test under `tests/` that
  fails before the fix and passes after it. An input that finds the bug goes into
  `fuzz/corpus/<harness>/`, written by `fuzz/gen-corpus.c`, as well.
- The library allocates nothing; a stop after the harness's own allocation failed is not a
  property.
- A change to the protocol's reading cites its source in `docs/protocol.md`, as every field of
  `protocol/diginet.ksy` does.
- Patches that change only the documentation are welcome.
- A refactoring that makes the code easier to verify is welcome only if it keeps the behaviour,
  and only with a test that shows it.

## Patch format

- Plain C11, in the style of the file you change: tabs, braces on the line of the statement,
  `/* */` comments.
- One change per commit. The subject line says what the change does, in the present tense. The
  body is plain prose that says why.
- Comments and commit messages describe the code as it is, not how it came to be.

## What the proofs mean for us

A proof is about the static riscv64 binary that this directory builds, under Theorem's RISC-V
and Linux process semantics. It does not transfer by itself to the x86-64 glibc packages that
we ship. A proof removes classes of bugs from the code that the fuzz targets drive. It does not
certify a shipped binary, and we do not describe it as if it did.
