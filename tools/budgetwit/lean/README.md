# Lean budget-premise witness generator

The Lean back end reuses the range-copying approach of the libreac and curl
budget-premise witnesses.

This back end copies reviewed, 1-based inclusive source ranges, replaces whole identifier
tokens using tab-separated rename tables, and assembles explicit fragments and a carrier
soundness template. It does not discover a proof dependency closure or invent a grant proof.
The checked-in libreac recipe reproduces all seven witness files except for their issue-free header comments.

## What is shared

`lean/units.py` reads Lean's `Images.lean`, `Statements.lean` and `proofs/lib/Theorems.lean`
into the existing `budgetwit.units.Unit` and `Statement` records. It finds
`lean-proofs/<project>/<harness>/<Root>/<project>/<harness>/Images.lean`, reads the namespace
from that file, and checks it against the path. It does not read Rocq's `release.yaml` or dune
package. `Unit.package` remains the logical prefix of `proofs/lib`; `Unit.directory` is the
unit's namespace directory. This second reader is necessary because Lean has different
layout and metadata syntax, not because it needs a second unit-record type.

`budgetwit.carriers.CarrierProfile` supplies the family, relation, cut and node constructors,
index arguments and twin-name rules for both languages. Its optional Lean template, index and
source-location fields leave Rocq callers unchanged. The supplied `YK15.lean.in` uses the same
`{{package}}` placeholder as Rocq, plus `{{unit_prefix}}` for Lean's witness namespace. The current
Lean carrier has the `AllocMode` index; curl's separately documented `amx` carrier variant is
not silently treated as this one.

## Commands

Run from the repository root. `--repo` names a checkout containing the Lean source tree;
`--out` names the output **namespace directory**, not the Lake package directory.

```sh
python3 -m tools.budgetwit.lean tools/budgetwit/lean/control/libreac/manifest.json \
  --repo /path/to/lean-libreac-checkout --unit libreac/fuzz_knock \
  --out /scratch/regenerated \
  --about /scratch/BudgetwitTypes.lean
```

This writes `BudgetWit/{Rzb,RunB,StartB,UsageB,WritevF,WritevG}.lean` and
`BudgetWitness.lean`. `--about` additionally writes an elaborator probe; generating the probe
does not execute it. Source SHA-256 values pin the line ranges: a changed source is refused
rather than silently copying a different declaration. Review the ranges and refresh their
hashes when porting a recipe to another harness.

A manifest selects a carrier family and lists output files. Each file's ordered `pieces` is
one of:

- `{"carrier": true}`: render the shared profile's Lean soundness template;
- `{"fragment": "RunB.lean.in", "ranges": [[50, 53]]}`: substitute placeholders in an
  explicit fragment; omitting `ranges` includes the whole fragment;
- `{"source": "proofs/lib/Reusable/YP03.lean", "ranges": [[217, 229]],
  "sha256": "<source SHA-256>", "renames": "RunB.tsv"}`: copy and rename source ranges.

`drop_private: true` drops `private` before a copied theorem, definition, abbreviation or
opaque declaration. The libreac recipe preserves private helpers instead. Rename tables are
`old<TAB>new`, one pair per line; dotted identifiers are one token, so renaming `X.foo` does
not rename `X.fooBar` or an unlisted `Other.X.foo`.
Ranges are assembled in the requested order, but overlapping ranges within one piece are
rejected. A deliberate reuse can be represented by separate pieces.

## Discharged-type check

The generated probe reads elaborated `ConstantInfo.type` values, replaces only the original
`YK15.realizes` constant with `BudgetWit.Rzb.rzb`, and asks Lean's metaprogramming `isDefEq`
check to compare the results at Lean's default transparency. Binder names and definitionally
equal presentations are immaterial; this is not syntactic alpha-equivalence. The probe checks
carrier universe arities before substituting and prints a line for each checked pair.
A twin stated through a different but definitionally equal abbreviation, wrapper or `let`
passes this check; the check does not require identical statement spelling.

The libreac manifest lists 48 public theorem pairs, including the unchanged pure helper
`skipn_all_nil`. Six are explicitly `extra_grant`: four carrier node helpers and
`RunB.rzb_chk1_silent`/`rzb_ret_only_copyins_silent`. For these, the probe traverses only the
outer forall telescope and permits exactly one additional `grant_ok` binder whose proof is
unused by later binders and the conclusion. It does not remove grants inside a hypothesis or
the conclusion. Negative controls cover an extra grant in `equal` mode, a hidden grant inside
a hypothesis, two additional grants, and a used grant proof.

Before emitting the probe, the CLI resolves original declaration names against source files
and accounts for every public theorem in the generated files: 48 paired theorems plus 12
explicitly fresh theorems, each with a reason in the manifest. Missing pairs, stale original
names, unknown exemptions and duplicate pairs fail locally. A lexical check of indented
`macro` bodies rejects calls to original theorem names that have twins, including qualified
calls; it is not a general Lean syntax parser. This control copies only `bwst_omega`, whose
body uses arithmetic facts and `omega`, not carrier lemmas. Imported `yn3f_omega`/`yn3f_gr`
operate on numerals and register reads; `YL0v`'s carrier-typed walk macros are not copied.

Private helpers have compiler-generated names and are not paired by this probe. Carrier
soundness and the composed witness are fresh claims, not theorem twins. The probe prints
the three top-level axiom sets; the farm's axiom gate verdict and kernel replay, not the
presence of those prints alone, check the proofs. Review the explicit strengthening and fresh
claim lists too. Declaration discovery supports the ASCII line-oriented forms in this tree;
the Lean elaborator, rather than this reader, resolves the actual discharged types.

## Checks and farm control

```sh
python3 -m unittest tools.budgetwit.lean.test_lean -v
python3 -m py_compile tools/budgetwit/lean/__main__.py \
  tools/budgetwit/lean/about_check.py tools/budgetwit/lean/emitter.py \
  tools/budgetwit/lean/units.py tools/budgetwit/lean/test_lean.py
```

Do not run Lean or Lake on the dev box. In a scratch copy of the source Lake package, replace
only the seven witness files with the regenerated output. Preserve `tools/LayoutSmoke.lean`'s
existing assertions; add the probe's imports to its import header and append the probe's
remaining commands. This makes the normal smoke phase execute the discharged-type check.

Read the farm's `README.md`, `libreac-farmbuild.sh` and `libreac-farm-pod.sh` before using it.
After applying the stream's pending-pod rule and server-side Job dry run, call the existing
farm driver with `OSSV_KIND=lean-precheck`, `OSSV_UNIT=libreac__fuzz_knock`, `PKG` set to the
scratch Lake package and all seven module names as targets. Leave sizing to that driver.
`control/libreac/RESULTS.md` records the source ref, byte comparison, line accounting and farm
evidence for the checked-in recipe.

## Limits and parser decision

The emitter deliberately retains the range-copy design. On this seven-file control, 3,364
of 4,272 output lines come from released source ranges; 438 are explicit fragments (headers,
namespace setup, changed proof applications and grant obligations), 329 are the carrier
template and 141 are the composed top-level witness. A parser is needed for **zero** of these
4,272 lines. This is not a claim that the 908 supplied lines were inferred automatically.

The curl measurement is 99 Lean files / 42,409 lines / 9.8 agent-hours, versus 100 Rocq files /
32,763 lines / 17.7 agent-hours. It is not a copier-versus-parser experiment: curl's
`CurlHarnessWit/RESUME.md` wave 2 records `tools/gen_file.py` and `leanparse.py` alongside the
57-line copier. That larger measurement therefore cannot be attributed to this copier alone.
Neither parser is needed to reproduce this control; their dependency-discovery features may
be useful for a larger new tree, but have not been ported speculatively here.

The current metadata reader supports the released `Image.mkImage <Build>.M.loaded_segments`
image definitions, `def <statement> : Prop :=` statements and direct released theorem aliases.
It is not a general Lean elaborator. The identifier copier uses ASCII identifiers and applies
its substitution in comments and strings too, like the scratch tool. It does not reformat or
understand Lean syntax. Fragments may be incomplete syntax on their own: their manifest
ranges say exactly where each piece is inserted. Choose ranges and rename tables by reading
the released proof, then run the elaborated-type probe and farm build.
