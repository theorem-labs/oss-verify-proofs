# Image-B (asan-ubsan) core relocation for a reac-repacer target: the route

Written for fuzz_uci; the other reac-repacer targets (fuzz_wire, fuzz_egress, fuzz_lock) take the same route and change
only the unit pins, the module prefix and the `Grant* -> <Unit>*` renames.

## Donor

fuzz_grant's RELEASED image-B library: `proofs/libreac/fuzz_grant/lib` at recipes commit 4f87de75d67 ("Merge pull request
#401: Pau proofs (libreac/fuzz_grant)"; the index rows libreac/fuzz_grant/asan_ubsan_halts and asan_ubsan_agrees are
`proved`). No cgif image-B text and no other donor is used. In that release the image-B text is `lib/B/` (per-image
files) over `lib/Reusable/` (files shared with image A). `mkdon.sh` lays both at the lib root, `B/` winning where a name is
in both (33 names), and rewrites the module text `...fuzz_grant.lib.Reusable` / `...fuzz_grant.lib.B` to
`...fuzz_grant.lib`: the shape port_core's `core-files-Y.txt` names (root `Y<x>.v`).

Why this donor (measured, same tool, same target lib): fuzz_grant B refused 67 values and staged 369 per-image files;
fuzz_identity's released `lib/ReusableB` (recipes 70952e1c8c9) refused 60 but left 3 partner-left FAIL rows and staged 395,
the 26 more being kernel files that the grant donor keeps shared with image A (whose donor is also fuzz_grant), and its
record names differ from image A's.

## Tool and inputs

- port_core 0e4e065eab9f (`git archive 7f0e4b05267 tools/pg-reloc/0e4e065eab9f`), image-B mode: `--remap-images
  --reusable-dir B --kernel-dir Reusable --kernel-image <donor asan image>`, file list = the release's
  `core-files-Y.txt` minus the files the target does not need (files-B-core.txt says which and why), the unit's 19
  start-up files `--no-stage`d (no-stage-B.txt; they come from the start-up generator, not from the donor).
- Old ELF: the pinned `fuzz_grant.asan-ubsan` (sha256 fde52226dc48...).
- `--old-syms`: `mksyms.py` over the donor's unstripped twin (sha256 5a5ee7c02b4e...), FUNC/OBJECT symbols with a size.
  CONTROL: the same script over fuzz_grant's asan twin reproduces, byte for byte (after its header line), the
  `fuzz_grant.asan.syms.txt` that libreac/fuzz_decode's image-A core run used.
- `--old-prog`: from `LLVMFuzzerTestOneInput` to the end of the last program function before `__wrap_getenv`:
  `80a3c:86640` for fuzz_grant.asan-ubsan. CONTROL: the same rule gives fuzz_grant.asan's `806b0:857dc`, the value
  libreac/fuzz_decode's and fuzz_uci's image-A runs use.
- Renames: `GrantB=UciB GrantSyms=UciSyms GrantB_syms=UciB_syms GrantB_ok=UciB_ok` (the image-A run's set). No shape
  rename: `YD1q.v` takes the unit's plain-side instance `checksum_shape` (lib/ZTraceSpec.v) by `B-ad1q-shape.patch`, as
  image A's `A/AD1q.v` does.
- Target lib: the unit's lib with the image-A core and the image-B start-up layer already merged, so every shared
  kernel file is KEPT (never staged twice) and the zero-shadow / CZONE / region-count rules read the unit's own
  `lib/B/YF0m.v` / `YD2j.v`.

## Target pins (control)

`fuzz_uci.asan-ubsan` sha256 a1b86e424add... equals the `asan-ubsan` pin of the unit's harness.yaml; its unstripped twin
(8d07ffcf5948...) has PT_LOAD contents equal to the pin; symbols are read from the twin, bytes from the pin.

## Values no rule decides

`overrides-B.tsv`: each row's value is measured on the pinned image by its ROLE (`measure-B.py`, output
`measure-B.out`), and the same rule run on fuzz_grant.asan-ubsan prints the donor's own value (the control):
FILE.buf pointers (stdout / stderr / stdin, FILE+88), BUFEND, the driver format shadow windows
`[floor8(shadow(FMT)), floor8(shadow(FMT + len)) + 8)`, absent entries (`__asan_memset`, bcmp trampoline) = 0, the
image start, the zero-shadow range `(__stop_asan_globals, page-up end of the last PT_LOAD)` and its quotients.

## Structure

Image A's patches re-cut for B: zero-shadow-forallb (the unit has 3 zero-shadow ranges, the donor 15) and cell-lookup
(index lookups into the const-cell list) by `mkpatch-B.py` (A file and module names mapped to B, each hunk's old lines
found exactly once in the B stage-out, a fresh zero-fuzz diff); ad1q-shape (the plain-side lib_shape instance) written
against B's own `YD1q.v`. A patch is applied before port_core adds its own header line, so a hunk near the header is
cut against the text without that line.

## Apply and headers

`run.sh` exits 3 for one known row, `rename-new-undeclared UciSyms`: the Record is declared in the start-up file
`lib/B/YF0m.v`, which the run does not stage. So the staged files are copied by `--apply`'s own rule (`apply-B.sh`:
nothing is overwritten; `applied.txt` lists them). The files keep the notices port_core writes: the donor's inherited
licence and `Modified by` lines unchanged, and one added `Modified by Theorem Labs, YYYY-MM: <what changed>` line
(docs/adding-a-proof.md, requirement 7). Then `imgtop-require.py` makes every B file that
Requires YImgTop take image B's `lib/B/YImgTop.v`: port_core 0e4e065eab9f names the shared `lib/Reusable/YImgTop.v`
(image A's bounds) in B/YB1w.v, YCeg.v, YD2k.v and YF0x.v. On fuzz_uci the two images' bounds are equal, so this
changes no number; on a unit whose images differ (fuzz_wire: A 0x5f5000, B 0x5f6000) the build fails without it. It is a
post-step, not a `--patch`, because port_core's generated header would then claim that a file whose only change is this
Require had its addresses moved.

## Gates (records/, scripts in gates/)

The flag gate (port_addr_check efa19b81e92b `--fail-on-flags`, every FLAGGED and GENERATOR-FILL row triaged by
`triage-B.py`), the by-value check (`decval-B.py`, with a planted donor value as control), codeptr 12348302dfd2 (with
`--not-address` declarations and a planted control), and the settings count (global_settings 439f8e3bd463, equal to the
donor's counterpart files). GATES.md gives the numbers and the controls.
