# Patch style and report preferences

reac-pw is FreeREAC's daemon that bridges Roland REAC, the audio network of Roland's digital mixers and stageboxes,
and PipeWire. libreac, enrolled on its own, parses the REAC frames. reac-pw parses input of its own beside them, and the
seven fuzz targets drive those readers:

- the operator's override file, `reac-pw.conf` and its drop-ins (`reac_segconf_parse_file` in `src/reac_segconf.c`),
  and the VLAN segments it declares (`src/reac_declared_vlan.c`);
- the `--box MODEL[:LABEL]` pin (`src/reac_box_pin.c`);
- the control writes a PipeWire client sets on a node's Props: the head-amp cells (`src/reac_headamp_prop.c`), the
  rate (`src/reac_rate_cfg.c`) and the role (`src/reac_role_cfg.c`);
- the rtnetlink replies of the kernel: the etf qdisc counters (`reac_qdisc_stats_read` in `src/reac_qdisc.c`) and an
  interface's alias and link kind, with the marking policy over them (`src/reac_link_alias.c`,
  `src/reac_served_mark.c`).

The control writes come from any client of the PipeWire graph, and they matter most here.

## How findings and patches land

Nothing from the pipeline enters reac-pw as it is. A maintainer reads each finding, reproduces it against the reac-pw
harness and build, and writes the fix in FreeREAC/reac-pw as an ordinary change. A patch you send is a description of
a fix, and we re-author it before it lands.

Every commit in reac-pw is signed. No attribution line, trailer, or generated-by marker enters the history. When a
finding leads to a fix, we quote its id in the reac-pw issue that tracks the fix, not in a commit.

## Which findings to report

Report all of them. A memory-safety bug in a reader is the most severe: a write out of bounds first, then a read out
of bounds, then undefined behaviour that a sanitizer traps. A property check that fails is a bug of the same rank as
the code it guards. A finding without a patch is welcome. Put findings that share one cause in one report.

Bugs that no fuzz target can hit are welcome too, with the input or the reasoning that reaches them. `fuzz/README.md`
in reac-pw says which parts have no fuzz target and why: the config file loader, the knobs, the qdisc policy, the
topology tap and the PipeWire nodes. A finding there is welcome with the reasoning that reaches it.

## Which patches to write

- A fix is minimal: the smallest change that removes the bug, with a test under `tests/` that fails before the fix
  and passes after it. An input that finds the bug goes into `fuzz/corpus/<harness>/` too, through
  `fuzz/gen-corpus.c`.
- The readers never allocate on their input; a stop after the harness's own allocation failed is not a property.
- Patches that change only the documentation are welcome.
- A refactoring that makes the code easier to verify is welcome only if it keeps the behaviour, and only with a test
  that shows it.

## Patch format

- Plain C11, in the style of the file you change: tabs, braces on the line of their statement, `/* */` comments.
- One change per commit. The subject line says what the change does, in the present tense. The body is plain prose
  that says why.
- Comments and commit messages describe the code as it is, not how it came to be.

## What the proofs mean for us

A proof is about the static riscv64 binary that this directory builds, under Theorem's RISC-V and Linux process
semantics. It does not transfer by itself to the x86-64 glibc packages that we ship. A proof removes classes of bugs
from the code that the fuzz targets drive. It does not certify a shipped binary, and we do not describe it as if it
did.
