# Patch style and report preferences

libreac is the C library under FreeREAC's REAC tools. It decodes and builds the Ethernet frames that Roland REAC stageboxes and desks exchange (EtherType 0x8819), and it reads pcap captures of them. Every byte that reaches these parsers comes from the wire or from a capture file, so the parsers are the code that matters most here. The state machines and registries that the frames drive come next.

## How findings and patches land

Nothing from the pipeline enters libreac as it is. A maintainer reads each finding, reproduces it against the libreac harness and build, and writes the fix in FreeREAC/libreac as an ordinary libreac change. A patch you send is a description of a fix, and we re-author it before it lands.

Every commit in libreac is signed. No attribution line, trailer, or generated-by marker enters the history, including the "Found by Theorem's OSS Verify" line. When a finding leads to a fix, we quote its id in the libreac issue that tracks the fix, not in a commit.

## Which findings to report

Report all of them. A memory-safety bug in a parser is the most severe: a write out of bounds first, then a read out of bounds, then undefined behaviour that a sanitizer traps. A property check that fails is a bug of the same rank as the code it guards. A finding without a patch is welcome. Put findings that share one cause in one report.

Bugs that no fuzz target can hit are welcome too, with the input or the reasoning that reaches them.

## Which patches to write

- A fix is minimal: the smallest change that removes the bug, with a test under `tests/` that fails before the fix and passes after it. An input that finds the bug goes into `fuzz/corpus/<harness>/` as well.
- libreac allocates no memory in the code that the fuzz targets drive. A refused allocation in a harness is a limit of the harness, so make the harness narrower, not the library.
- Patches that change only the documentation are welcome.
- A refactoring that makes the code easier to verify is welcome only if it keeps the behaviour, and only with a test that shows it.

## Patch format

- Plain C11, in the style of the file you change: tabs, the kernel brace style, `/* */` comments.
- One change per commit. The subject line is under 72 characters and says what the change does, in the present tense. The body is plain prose that says why.
- Comments and commit messages describe the code as it is, not how it came to be.

## What the proofs mean for us

A proof is about the static riscv64 binary that this directory builds, under Theorem's RISC-V and Linux process semantics. It does not transfer by itself to the x86-64 glibc packages that we ship. A proof removes classes of bugs from the code that the fuzz targets drive. It does not certify a shipped binary, and we do not describe it as if it did.
