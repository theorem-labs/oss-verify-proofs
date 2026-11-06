# Patch style and report preferences

plugin-hostd is FreeMixer's plugin supervisor. It speaks mod-host's command protocol to its controller, runs each CLAP
or LV2 plugin in a worker process of its own, and relays what the workers write back. Two byte streams reach it from
outside: the commands of any local client on its command socket, and each worker's feedback socket. The command
parser and dispatcher (`src/verbs.c`) and the feedback relay (`src/relay.c`) read them, so they are the code that
matters most here, and the two fuzz targets drive them.

## How findings and patches land

Nothing from the pipeline enters plugin-hostd as it is. A maintainer reads each finding, reproduces it against the
plugin-hostd harness and build, and writes the fix in FreeMixer/plugin-hostd as an ordinary change. A patch you send
is a description of a fix, and we re-author it before it lands.

Every commit in plugin-hostd is signed. No attribution line, trailer, or generated-by marker enters the history. When
a finding leads to a fix, we quote its id in the plugin-hostd issue that tracks the fix, not in a commit.

## Which findings to report

Report all of them. A memory-safety bug in the parser or the relay is the most severe: a write out of bounds first,
then a read out of bounds, then undefined behaviour that a sanitizer traps. A property check that fails is a bug of
the same rank as the code it guards. A finding without a patch is welcome. Put findings that share one cause in one
report.

Bugs that no fuzz target can hit are welcome too, with the input or the reasoning that reaches them.

## Which patches to write

- A fix is minimal: the smallest change that removes the bug, with a test under `tests/` that fails before the fix and
  passes after it. An input that finds the bug goes into `fuzz/corpus/<harness>/` and `fuzz/gen_corpus.py` as well.
- The relay survives a refused allocation, and `tests/relay_test.c` and `tests/gesture_alloc_test.c` drive those paths.
  The fuzz targets do not refuse allocations; a stop after the harness's own allocation failed is not a property.
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
