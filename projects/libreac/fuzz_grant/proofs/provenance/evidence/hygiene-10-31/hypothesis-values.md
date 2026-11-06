# Numeric values in hypothesis positions, audited against the images

A proof can be weakened by a number that is assumed rather than proved: an atom range, a bound in a `Hypothesis`, a
field of a record of propositions, or the region of a state a section assumes whole. If such a number excluded a value
the program can really take, the statement above it would be about a program this one is not. Every one of them in
this unit was read against the image the file is about.

## What was audited

| kind | items |
|---|---|
| `mkAF lo hi al` atom ranges | 1741 |
| `Hypothesis` / `Hypotheses` sentences carrying a numeric bound or equality | 1721 |
| fields carrying a numeric bound or equality in a `Record`/`Class`/`Structure ... : Prop` | 344 |
| all items | 3806 |
| all sites (an item may appear in several files) | 8151 |

Identical text in a pair of twin files (image A's and image B's copy, or `lib/Reusable` and `lib/U/Reusable`) counts
as one item listing all of its sites. In addition, the regions and conditions of every symbolic state that a section
assumes whole were written out as 404 further rows and judged the same way.

Not judged: 1966 hypothesis sentences whose only literal is an address or an offset (for example
`val_mem ... (T + 2880) 8 jm2`). They bind a variable to a cell and bound nothing.

## Verdicts

| | TRUE-tight | TRUE-slack | FALSE | CANNOT-DERIVE | NOT-A-VALUE |
|---|---|---|---|---|---|
| items (3806) | 1840 | 1896 | **0** | 33 | 37 |
| sites (8151) | 4228 | 3744 | **0** | 63 | 116 |
| the 404 state rows | 288 | 116 | **0** | 0 | 0 |

TRUE-tight means the bound equals the reachable extreme or the type's width; TRUE-slack means it covers the reachable
range with room to spare. **No value excludes a reachable one.** No twin pair disagrees in verdict.

The 33 CANNOT-DERIVE items have one cause between them: dead text copied from the donor that describes no program
point of this unit. No proof uses any of them, and neither image contains the code they describe. They are left as
they are rather than guessed at.

## Whether the build checks each atom range

An atom range that only a premise carries is assumed: a too-narrow value there would not fail any build. Each of the
3715 `mkAF` rows was placed by what reads it:

| kind | meaning | rows |
|---|---|---|
| P | on the dependency path of a shipped theorem; its `afact_ok` is proved, so a too-narrow value fails the build | 3391 |
| P-local | off that path, but a closed lemma of `lib/` proves it, so a too-narrow value still fails the build | 267 |
| H | only a hypothesis, premise or unconstructed record field carries it; no build checks it | **0** |
| C | only a `vm_compute` check reads it | 2 |
| U | nothing reads it | 54 |
| NA | the `Record afact := mkAF {...}` declaration itself, not a value | 1 |

So **3658 of 3715 atom ranges are discharged by proof**, and none is merely assumed. 196 of the groups reach their
lemma through a section hypothesis such as `Hypothesis FH : free_hyps ...` or `Hypothesis SEED : st_ok ...`, which by
the declaration alone would read as assumed; each of those lemmas is on the shipped path, so a closed theorem
discharges the hypothesis, and the record cites the builder (`FACTS_ok`, `FACTS1_ok`, `FACTSR_ok`, ...) that does it.

## One verdict was corrected

`lib/Reusable/YN3d.v:196` and `lib/U/Reusable/YN3d.v:196`, `exit_demo_F ... 10 (mkAF 1 6 0)`, were reported FALSE
while the audit was running. That was wrong and is retracted: both are TRUE-slack. An independent reader found the
error and a re-derivation confirmed it.

The cause is worth recording, because it is the trap this kind of audit falls into. Atom 10 is `wpos - wbase` at the
entry of `exit`, the count of pending bytes the stream writes. The first derivation read `lbf = -1` from the stream's
state and concluded that output is never line-buffered, which would make the pending count larger than 6. But
`lbf = -1` holds only *after* the first write: the initial `FILE` bytes, read from each image, have `lbf = 10` ('\n'),
`fd = 1`, and both positions 0. So the first print flushes at the newline, every later print stays in the buffer, and
the printed value is always `0\n`, two bytes. The range 1..6 covers it.

Two rules came out of it, and both were applied to every item afterwards:

- **A range bounds what the atom denotes, not what the cell holds.** Each atom-range row names the tie between the
  two (a region chunk, a register mapping, or a store) before judging the number.
- **A value read from a symbolic state must be checked for whether it holds from the start of the run**, or only
  after some event.

## Method

Each item was derived from this unit's own definitions and from the image the file is about: image A's pin for
`lib/A`, image B's pin for `lib/B`, each named by the sha256 the build's `harness.yaml` pins. The enumeration is
reproducible: the script beside this record reads the tree and recreates the same 3806 items, with none differing
from the list that was judged.
