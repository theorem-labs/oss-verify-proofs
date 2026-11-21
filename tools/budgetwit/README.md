# budgetwit — budget-premise witness twins

Standard-library-only Python 3 tools for reading a released Rocq library as text,
selecting the startup and wrong-argument-count usage path for an image, and
emitting proof twins over a carrier that records that the budget grants each step.
These tools run no Rocq. The farm, not this parser, judges the generated proofs.

The Rocq back end reuses the text-copying approach of the curl `fuzz_fnmatch`
budget-premise witness.

A released statement can assume `~ run_scfg_budget_refused cfg image lim en inp`
without establishing that this premise is satisfiable. The witness uses an input
with argc different from 2: the CLI driver writes its usage diagnostic to fd 2
and exits 2, without allocation. This tool copies the relevant released proof;
it does **not** synthesize grant proofs, a top-level witness, or a replacement
statement. Those remain proof work. No released files are changed by discovery.

## Running

Run from the repository root, or pass `--repo /path/to/repository` to any
subcommand. The executable and `python3 -m tools.budgetwit` expose the same CLI.
Python 3.10 or newer is required; no dependencies beyond the standard library.

```bash
./tools/budgetwit/budgetwit detect --unit libreac/fuzz_knock
./tools/budgetwit/budgetwit detect --unit libreac/fuzz_knock --image ubsan
./tools/budgetwit/budgetwit census --unit libreac/fuzz_knock --out /tmp/twins.tsv
./tools/budgetwit/budgetwit genall --unit libreac/fuzz_knock --out-dir /tmp/bw
./tools/budgetwit/budgetwit gen --unit libreac/fuzz_knock \
  --module Reusable.YN3e --names src0_start --out /tmp/StartB.v
./tools/budgetwit/budgetwit gen --unit libreac/fuzz_knock \
  --module Reusable.YN3e --names src0_start --admit --out /tmp/StartProbeInput.v
./tools/budgetwit/budgetwit image --unit libreac/fuzz_knock \
  --from plain --to ubsan --out-dir /tmp/bw-ubsan
./tools/budgetwit/budgetwit probe --unit libreac/fuzz_knock \
  --twin /tmp/bw/YN3eB.v --r1-module Reusable.YN3e \
  --out /tmp/Probe.v --map /tmp/probe.json
# Build the twin and probe on the farm, then:
./tools/budgetwit/budgetwit about --map /tmp/probe.json --log outputs/dune.out
```

`--root DIR` selects an external proof-library tree instead of locating it from
`--unit PROJECT/HARNESS`. It still reads the library's `dune`; the surrounding
harness metadata is used when present. There is no hard-coded default tree or
logical package. The package comes from the named `rocq.theory` in `proofs/lib/dune`,
which must use `(include_subdirs qualified)`. Images and their Rocq modules come
from `Images.v`, checked against `harness.yaml`'s build keys and `images/dune`'s
generated targets. The image `.v` files themselves are build outputs, not inputs.
Statement names come
from `Statements.v` and `harness.yaml`; exported theorem aliases are read from
`proofs/lib/Theorems.v`. Missing released proofs are not invented.

Discovery is per **(unit, image)**, defaulting to `plain`. It records declaration
names, paths and source line numbers, including relevant section hypotheses and
statement aliases. Multiple candidates are a refusal, not a ranking by an opaque
score. Use repeated/comma-separated `--start MODULE.NAME` and `--usage MODULE.NAME`
to resolve an ambiguity. Certificate paths may need more than one usage root:
the top certificate node and the lemma supplying its argc premise. `--roots A.x,B.y`
replaces discovery for a census/generation run. An explicit override is a human
choice, not evidence that the named declaration proves the intended property.

`census --out twins.tsv` also writes `twins-ltacs.tsv`. `genall` writes the twins,
`Rzb.v` rendered from the carrier's template, both census tables, and a
`budgetwit.json` manifest mapping original names to twins. `gen` accepts `--tsv`,
`--ltacs`, `--names`, `--identity`, `--twin-module`, `--overrides`, and `--note`.
Without `--twin-module`, a single-file generation uses the output filename stem.
Use the manifest or `--tsv` when writing probes. Probes refuse an unpairable twin
name rather than asking About for a nonexistent original. A fully-qualified
`--r1-module` lets `probe` find its unit without `--unit`.

`--admit` is only for statement-check farm builds. Generated admissions must not
be committed. `genall` is not a finished witness: discharge every HAND obligation,
write the usage-to-budget soundness application and concrete input witness, and
check the discharged statements and assumptions on the farm.

## Carrier families

The initial harness census suggested these families. Reading a particular
**image path** wins over that classification: imported algebras are not proof
that the usage walk is expressed in their relation. `carriers.py` records the
constructors and indices actually present, with declaration evidence.

| Family | Carrier | Cut-like constructors | Index/configuration |
|---|---|---|---|
| YK15 | `Reusable/YK15.v`, `realizes` | `rz_cut` | Some variants bind `AllocMode`; others fix ACFG |
| ShapeAlg | `ShapeAlg.v`, `realizes` | Inspect the actual constructors; some variants have none | Configuration can be fixed by the module, not an inductive index |
| SpinAlg | `SpinAlg.v`, `srealizes0` / `srealizes` | Inspect the actual constructors | Some variants mention scfg; not universal |
| RealizesCfg | `RealizesCfg.v` or `ShapeAlgCfg.v`, `realizes_cfg` and `node_ok_cfg` | None in the inspected base carriers | Section configuration over `sstep_cfg` |
| FwSafety | `Fw/Safety`, `star_cfg` through `star_a`, `syscall_spec_ns` | None | Configuration fixed by Refusable |
| ITree | `impl` / `implM` / `tree_ok` | Not applicable | Bridge route, **not** a twin |

Corrections to the initial table, from this repository tree:

- `libreac/fuzz_knock/proofs/lib/Reusable/YK15.v:209` has `rz_cut` at :222
  and the AllocMode-parametric consequence rule. `libreac/fuzz_identity`'s
  counterpart at :208 has the fixed-ACFG rule and `rz_cut` at :221; these are
  not identical carrier signatures.
- `msgpack-c/unpack_pack_fuzzer/proofs/lib/Common/ShapeAlg.v:349` has only
  `rz_node`, `rz_halt`, `rz_conseq`; `node_ok` at :344 uses a module-fixed fcfg.
  `openssl/bndiv/proofs/lib/VCommon/ShapeAlg.v:255` likewise has no cut.
- `openssl/pem/proofs/lib/Common/SpinAlg.v:24` has only `srz_node`,
  `srz_halt`, `srz_conseq`, no scfg index. Its soundness lemmas at :89 and
  :109 refer to `kit_cfg`; that is not an index on `srealizes`.
- pem's **plain** usage statement is `P/Drv_main_defs.v:129`, over `implM`;
  its startup theorem is `P/Startup.v:184`, over `impl`. The plain tree is
  ITree, even though it also imports ShapeAlg and SpinAlg. Detecting it must
  report the bridge route and fail rather than generate a misleading twin.
- bndiv's **plain** startup is likewise `P/Startup.v:182` over `impl`,
  and `P/Drv_main_defs.v:114` states the usage walk over `implM`. Its
  imported `VCommon/ShapeAlg.v` is not the plain usage carrier.
- `yajl-ruby/json_fuzzer/proofs/lib/Common/ShapeAlgCfg.v:172` has
  `rz_node_cfg`, `rz_halt_cfg`, `rz_conseq_cfg`;
  `fast_float/from_chars/proofs/lib/Common/RealizesCfg.v:34` calls them
  `rzc_node`, `rzc_halt`, `rzc_conseq` instead.
- `tinyobjloader/fuzz_tobj_c/proofs/lib/Fw/Safety.v:50` defines `wsteps`;
  `Fw/Refusable.v:223` defines `star_a := star_cfg ... ACFG`, and :235
  defines `syscall_spec_ns`.
- The inspected boost-json ShapeAlg (`boost-json/fuzz_parse`, :141) has no
  cut. The inspected leptonica ShapeAlg (`paintcmap_fuzzer`, :366) also has
  only the three node/halt/consequence constructors; the initially reported
  `rz_refused`/`rz_side` at :418/:423 are not constructors in this revision.

Each detected YK15 profile records its `node_step`: the actual `sstep_cfg`
configuration, the soundness mode, and file:line evidence from `node_ok`.
`carriers/YK15.v.in` is the AllocMode-parametric reference from the shipped
`libreac/fuzz_knock` BudgetWit library. Its non-refusal theorem is specialized
at `MayFail`, not every AllocMode. `carriers/YK15Fixed.v.in` is the fixed-ACFG
instance generalized from the farm-checked zlib witness. Its node obligation
is `budget_ok`: the grant check **and** `cfg_transparent segs c`. It supplies
`budget_ok_instr`, `budget_ok_no`, and `budget_ok_exit`; rendering checks that
the target's `cfg_transparent` covers the configuration used by `node_ok`.
Both templates have package/module substitution points.
The farm-checked identity witness also demonstrates a grant-only fixed-ACFG
proof that derives filtered-step completeness from `Cfg.acfg_nonspurious`.
The generator currently retains the zlib joint-predicate template and its
shared segment-indexed introduction-lemma API; it does not silently normalize
the identity witness's different `grant_ok c` API.

The other five files remain explicit one-line **carrier-prover owner stubs**,
not proofs. Both `gen` and `genall` validate the carrier template before writing
any output and refuse a stub. ITree always refuses the twin route. Unknown
parameterized node configurations are refused rather than treated as fixed or
silently specialized to `MayFail`.

Templates use `{{package}}`, `{{carrier_directory}}`, `{{carrier_module}}`,
`{{cfg_module}}`, `{{prelude_module}}`, and `{{support_modules}}`. Rendering
requires every placeholder and every referenced support module. Templates are
handwritten proof assets; a text substitution is not a soundness check.

## The census rule

A declaration needs a twin when it is **R-typed** and the selected usage route
**reaches** it.

- R-typedness is the least set containing the carrier profile's seeds, closed
  under a Definition/Fixpoint/Inductive/Record/Class/Let whose type **or body**
  names an R-typed declaration, and a Lemma/Theorem/etc. whose **statement**
  names one. A theorem whose statement does not change is reused from release.
  YK15 also seeds `knode`, `SR`, `mreal`, whose bodies need not name `realizes`.
  Local notation aliases are followed back to their seeds.
- Reachability follows statement **and proof** references from the discovered
  startup and usage roots, but only into R-typed declarations. It stops at a
  reused non-R lemma. These are usage roots, not the scratch tool's argc=2
  MayFail application/allocator/contract roots.
- Tactic bodies count: an Ltac binds names where it is defined. The census
  follows called tactics transitively. It also follows every sibling tactic
  that generation replays because it mentions a twin, including siblings not
  called by the entry proofs. Declaration and copied-tactic dependencies close
  together until neither adds another twin.
- The must-exit `TraceHalting*` / `ZTraceSpec*` side is excluded by unit policy.
  A skipped declaration is neither R-typed nor walked into. Carrier cuts are
  skipped: removing their escape hatch is the point of the strengthened carrier.
- The census records released tactics and node-builder sites. The family profile
  supplies builder names and rename rules; generated sites owe a grant argument
  a person must prove. They are marked `(* HAND: grant *)`.

YK15 names follow the scratch rule: `realizes -> rzb`, `rz_x` / `realizes_x ->
rzb_x`, `SR -> SRb`, `mreal -> mreal_b`, `knode -> knode_b`, preserving suffixes;
other names gain `_b`. YK15 file `X.v` becomes `XB.v`. Other profiles flatten
the relative module path into a twin module, preventing same-basename lane
collisions; `genall` refuses any remaining collision. A TSV override can name a
specific twin module and declaration or skip one:

```text
Reusable.YK15.realizes\tRzb.rzb\t1
Reusable.SomeModule.*\tskip
```

The third column `1` marks a handwritten/existing twin. Module-wide `M.* -> XB`
mappings are supported. Overrides are caller-supplied per unit: the old curl
allocator-pinned skip decisions are not silently applied to another harness.

## What gen_v.py writes

1. The source header comments and a provenance line naming the released file.
2. Its Require/Import commands verbatim, then the released module itself, then
   the required twin modules. Rocq short names resolve to the **last** import.
3. Every enclosing Section needed by copied declarations, replaying Variables,
   Contexts, Hypotheses, Lets, notation, tactics, Open Scope, Set/Unset and
   Existing Instance commands in order. Unused sections and binders are dropped.
4. Declarations in source order, preserving **Proof using**: it controls section
   discharge and must not be guessed from a theorem's visible statement.
5. Copied released tactics under their released names, with references renamed.
6. Local notation aliases repointed to their twins.

Only code is rewritten. A resolved twin reference becomes `XB.twin_name`, or a
bare twin name in its own file. Retyped section hypotheses gain twin names.
Replayed section variables, hypotheses, Lets and intro-pattern names stay bound.
A non-copied declaration from the same released file needs special handling:

- A Definition/Fixpoint/Record is qualified and supplied the explicit section
  arguments its type/body transitively uses. Implicit Context binders are
  omitted, because the twin binds them too; section Lets discharge as let-ins.
  The statement names the **released** constant, making About meaningful.
- A section Lemma/Theorem is copied transitively instead. Without Proof using,
  its discharged argument list depends on the elaborated proof, not just text.
- A section Let has no discharged constant, so it stays bare and is replayed.
- In unfold and constant-name lists such as cbn/cbv/simpl/delta `[names]`, the
  reference stays a constant name, not an application. `fold` accepts terms.
- A section with only implicit Contexts needs no extra argument application.

## Image substitution

Image and sibling modes use the same `retarget.py` identifier/import rewriter,
released-source line checker, address-consistency checks, and output renderer.
The image mode adds no reviewed renames or carrier changes.

`image` reads already-written source BudgetWit files; `--source-dir` overrides
`proofs/lib/BudgetWit`. It derives corresponding released modules from their
imports and provenance, follows their dependencies, and pairs files only when
the target image and relative path suffix identify one counterpart. It checks
**every line** of every pair before writing anything: line counts must agree,
and differences may only be mapped module/image references or hex literals.
A non-address difference reports the two paths and the offending line and
refuses the entire run. Conflicting address mappings, a literal that both relocates
and stays unchanged, and mixed shared/relocated imports are likewise refused.

The derived released-module imports must move to the corresponding target
namespace as well as the image module and `Images.plain` references. These
renames are checked against the paired released sources, not inferred from
letters such as U/A/B. The run reports replaced literal occurrences and module
rename occurrences. Numeric constants without a changed, corresponding-source
literal are left alone. This is deliberately not a general sanitizer port:
non-address-only twins require a fresh proof walk.

## Sibling-harness ports

`sibling` ports selected already-written walk twins between two harness trees.
`--unit` / `--root` selects the source; `--to-unit` / `--to-root` selects the
target. Both images default to `plain`; `--from` / `--to` can select them.
Pass a reviewed rename file even when its `renames` list is empty:

```json
{
  "renames": [
    {
      "from": "mcfg_nonspurious_no",
      "to": "acfg_nonspurious_no",
      "reason": "the fixed target configuration uses the corresponding acfg helper",
      "reviewed_by": "the person or agent who checked this rename"
    }
  ],
  "manual_patches": []
}
```

Every explicit identifier/decimal-token rename needs a reason and reviewer.
The named tokens must occur in corresponding source/target code. A declaration
that contradicts profile-derived budget renames or context handling is refused.
The profiles derive only the mechanical MayFail-to-fixed changes: remove the
AllocMode context and rename `grant_ok` and its three introduction lemmas to
`budget_ok`. Other helper renames are explicit, not guessed from spelling.

Example of a **checked attempt**, not a claim that this pair is address-only:

```bash
./tools/budgetwit/budgetwit sibling --unit libreac/fuzz_knock \
  --to-unit zlib/checksum_fuzzer --renames reviewed.json \
  --files StartB,UsageB,RunB,WritevF,WritevG --out-dir /tmp/bw-sibling
```

The released owners of each copied file come from its `made from ...v:`
provenance. A combined list such as `Reusable/YP0n.v, YP03.v and YN35.v`
inherits its explicitly written directory and checks **all** named owners.
Corresponding target modules prefer the same relative path, then the longest
shared suffix; ties are errors. Every difference in those complete
released walk files must be a checked hex-literal pair, a namespace/profile
change, or a declared reviewed rename. Decimal changes are not silently
classified as addresses. A source literal cannot both relocate and remain
unchanged elsewhere in the checked files.
Hexadecimal text in comments or strings is not an address literal and is never
relocated. Profile-requested context removal likewise applies only to code.

Unaccounted changes refuse the whole run before any witness `.v` is written.
The JSON report lists all unaccounted files and complete diagnostic hunks under
`manual/*.patch`; those patches are **not applied**. In particular, the measured
knock-to-zlib port has shape-changing proof hunks and requires manual work.
`manual_patches` records the names of patches applied outside this mechanism;
it is not a whitelist and bypasses no check. Successful reports record address
pairs and evidence, module/identifier renames, profile consequences, removed
contexts, and each file's counts. `--report` overrides the report path.

### Three-way candidates

Add `--three-way` to `sibling` to run `git merge-file --diff3 -p` for each
selected twin. This needs the Git executable, but changes no repository index,
branch, input proof, or working copy. The existing twin is ours; its released
source is the base; the corresponding target release is theirs. Namespace,
profile, and declared renames are applied to ours and the base first. Combined
twins concatenate their explicitly named released owners in provenance order.

Candidates are retained under `merge/*.merge`, including Git's three-sided
conflict markers. The JSON report records their paths and Git exit codes.
Git's positive exit code indicates conflicts and is not treated as success.
A clean Git merge does not override the declared-change gate: unaccounted
released-source differences still require named manual patches, and a clean
candidate must equal the result allowed by the shared relocation checker.
No candidate becomes a witness `.v` when either check refuses it. Resolve and
review manual proof work outside this mechanism, then run the farm and About
checks; the tool never silently applies it.

```bash
./tools/budgetwit/budgetwit sibling --unit libreac/fuzz_knock \
  --to-unit zlib/checksum_fuzzer --renames reviewed.json --three-way \
  --files StartB,UsageB,RunB,WritevF,WritevG --out-dir /tmp/bw-merge
```

Select walk twins with `--files`; write the target top and render its carrier
from the target profile, rather than blindly copying these proof assets.
After a text port, run the target farm build and About check. No sibling-mode
text result by itself claims a completed witness.

## The About check

A twin is the released theorem over the strengthened carrier only when its
**discharged** statement is the released statement with the appropriate names
replaced. Wrong section discharge can still build. A probe Requires both
modules, prints About original and About twin for each pair, and surrounds each
answer with uniquely module-tagged marker definitions and Print commands.
Repeated answers to a marker in one log are refused.

`about` compares the printed type and Arguments after renaming relevant original
names, preserving qualifiers for names not renamed. Verdicts are `SAME`, `DIFF`
(first differing word and context), `ALLOWED` (`--allow REGEX` signs off a
particular difference), or `NOREAD`. A renamed section binder is allowed in the
Arguments line. An empty map is refused. NOREAD/DIFF exit nonzero.

Build a generated `--admit` statement-check twin on the farm before spending
proof work on it. That is a probe input, never a proof to ship. The port itself
runs no `coqc`, `lean`, `lake`, or `dune` and starts no farm job.

## Shipped-witness source control

Compare a generated walk with a shipped witness before sending it to the farm:

```bash
./tools/budgetwit/budgetwit genall --unit libreac/fuzz_knock \
  --roots Reusable.YN3e.src0_start,Reusable.YL0y.src0_usage \
  --out-dir /tmp/bw-pinned
python3 -m tools.budgetwit.control --unit libreac/fuzz_knock \
  --reference origin/main --reference-entry BudgetWitness.usage_rzb \
  --pin StartB.src0_start_b=Reusable.YN3e.src0_start \
  --pin UsageB.src0_usage_b=Reusable.YL0y.src0_usage \
  --generated /tmp/bw-pinned --out /tmp/bw-control.json
```

The reference entry and pins use names relative to `BudgetWit`; released pins
are relative to the unit's package. Each reference pin must be reachable from
the entry. Compared reference and released source files must match the named
Git ref byte for byte. The JSON records both declaration sets, required versus
unused reference-only declarations, generated-only declarations, and original
R-typed references retained in generated declarations or tactics. Missing
required declarations, unpairable declarations, or retained R-typed references
fail the check; unused reference helpers and extra generated helpers do not.

The reference is the set of twin files the named entry reaches, not every file
under `BudgetWit`. One twin directory can hold several witnesses: other images
of the same harness, and walks this entry never reaches. The run prints each
such file as `NOT_REACHED_BY_ENTRY` and records them under
`reference_modules_not_reached`. Within a file the entry does reach, every
declaration must still pair with a released one.

This is a source dependency comparison, not Rocq elaboration, a grant proof,
or a semantic reachability check. It cannot establish that either witness is
complete. Keep the farm build and About check.

## Known limits

All the scratch tool's limitations still apply; parameterising paths does not
make this a Rocq parser or an elaborator.

### rocqparse.py

1. Text, not Rocq: the farm is the judge.
2. Resolution uses module/import/export order and the require graph, but local
   binders are not tracked by the index. A shadowing identifier can add a
   spurious reference or make a Definition R-typed through a let in its body;
   it cannot make a theorem R-typed through its proof alone.
3. Local notation/tactics, and section-local ones, are not exported. A Global
   Ltac inside a section is retained.
4. A sentence ends at dot followed by whitespace; `..`, qualified names and `.(`
   do not end it. Module Type, functors and Include are treated as plain modules;
   mutual/with blocks are one declaration.
5. Declaration extents are textual through Qed/Defined/Admitted/Abort or the end
   of a `:=` sentence. A preceding doc comment is not part of a declaration.

### census.py

1. Line counts describe released source, not generated twins.
2. R-typedness is a least fixed point. A seedless mutual cycle can be missed;
   the scratch documentation knew no such case in its source tree.
3. Section hypotheses contribute when Proof using or the statement names them.
   Without Proof using, every name in the proof script is conservatively counted,
   because discharge depends on a proof term text cannot predict. This may twin
   more than necessary (the scratch YL0q/YN1* examples).
4. Reachability is only as good as the roots. Re-run with --roots when the route
   changes, rather than editing a generated table by hand. Discovery cannot
   elaborate opaque Ltac2-compressed statements or prove semantic reachability;
   ambiguous/unsupported patterns need explicit evidence-backed overrides.

### gen_v.py

1. Only code is rewritten; comments and strings retain released names.
2. Bound-name inference is conservative: an over-approximated binder is not
   renamed. That normally produces a loud build error, not a corrected proof.
   Statement inference handles binder groups/forall/fun; proof inference also
   includes intros, as, set, eqn and related patterns.
3. Proof text is copied. HAND grant markers do not supply arguments; extra grant
   hypotheses in a twin statement also require handwritten work. Generated
   twins are not expected to compile before that work.
4. Definition discharge is only as good as the text parser. Variables reached
   through unexpanded notation can be missed; transitively reached section
   constants may or may not discharge in the elaborated term. An `@name` is
   left with a HAND diagnostic because implicit arguments must also be supplied.
   Destructed section variables are replaced by unification holes in proofs.
5. A discharged Definition inlines section Lets while a copied proof names the
   replayed Lets. `lia` can then see different atoms; unfolding those Lets in
   the proof fixes that mismatch (scratch YN0i WDm over nx/sp).
6. Copying section lemmas/tactics can create cross-twin import cycles. Split
   them by hand if this occurs.
7. One released file / one twin module at a time. No automatic semantic file
   splitting or allocation among several twin modules; use overrides.
8. Output goes only to paths the caller supplies. A caller can explicitly point
   it at a worktree; the tool does not choose an integration path by itself.
9. A copied non-R section lemma can discharge extra variables because its
   renamed proof uses them. About then reports DIFF (scratch YN1e rsvT/YN1s
   rsv2 had three extra binders). This is not a weakened R-typed theorem, but
   it must be reported rather than hidden.

### about_check.py

1. It compares printed terms. Different terms that print identically, for example
   through a notation hiding an argument, can compare SAME.
2. A probe build must reach About. An earlier error gives NOREAD, not DIFF.
3. Renamed constants lose their qualifiers on both sides: the wrong module's
   strengthened carrier can still compare SAME. Unrenamed qualifiers stay.
4. Renames are per file, not per declaration. Restating a name in one statement
   but reusing it in another can hide a difference. Split the file or check
   with a manual --rename mapping.
5. About prints only a Definition/Inductive's **type**, not its body. SAME does
   not validate bodies; inspect them or use Print on the farm. The scratch
   census had 76 such twins among 410 at its recorded revision.
6. ALLOWED examines only the **first** difference. A later difference can be
   hidden. Manually diff the complete types of every ALLOWED row.
