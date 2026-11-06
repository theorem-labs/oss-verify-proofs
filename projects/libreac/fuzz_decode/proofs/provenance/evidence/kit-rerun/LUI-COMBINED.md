# kit-rerun: two lui values combined into one address (the KNOWN FAIL-OPEN of cmpkit 86da41d3ef68)

strictcmp3 65688e94214a's rule 8 carries ONE lui value forward to the word that uses it. Two lui values combined by
add / sub / sh*add into one load / store / jalr / AMO base are therefore not compared as an address: `lui ; lui ; add ;
ld` reading different objects in the two images gives EQUAL-mod-pcrel with luiscan `exposure` 0. Until strictcmp3d /
luiscan3b are registered, an EQUAL verdict on a function of that shape is not evidence without a hand trace that names
the combined target on both sides.

This file is that check for the three records here. Measured with `cmpkit-86da41d3ef68/luicomb.py` (sha256
`69fe2b13fadd`), run by `cmpkit-86da41d3ef68/luicomb-run.sh` (`2826820888ff`), with the control planted by
`cmpkit-86da41d3ef68/plantlui.py` (`1352999653f1`), all on cmpkit 86da41d3ef68; outputs
`cmpkit-86da41d3ef68/luicomb-86da41d3ef68.out` and `cmpkit-86da41d3ef68/luicomb-control-86da41d3ef68.out`.

## One line per record

Every function of every record was scanned, not only those with two or more lui (luiscan `luis`: Allocator::Allocate
12, CombinedAllocator::Allocate 5, memset 1, TryMemCpy 1, the other four 0).

| record | line |
|---|---|
| A record, `A/kit-rerun-4bbd3a74be89/` (7 pairs, donor twin : decode A twin) | lui+lui->base: **27 sites, no target on either side** (22 in Allocator::Allocate, 5 in CombinedAllocator::Allocate; every base is a runtime pointer, so no site forms a static address in either image) |
| the copy, `A/kit-rerun-4bbd3a74be89/` as it ships here | lui+lui->base: the same 27 sites (the copy changes no byte of any image and compares the same 7 pairs) |
| B record, `B/fncmp.cmpkit-4bbd3a74be89.log` (8 functions, symtwin and donor twin : decode B twin) | lui+lui->base: **27 sites, no target on either side** (the same two functions; TryMemCpy, the eighth, has none) |
| settled rows, `cmpkit-4bbd3a74be89/settled.tsv` (Allocate +0xdc, PoisonShadow +0x48c) | lui+lui->base: **22 sites, no target on either side** (all in Allocator::Allocate; PoisonShadow holds no lui at all) |

No target differs between the images, because no site has a target: `ea` is `-` in all 108 rows (27 sites x 4 images).

## What was measured

luicomb.py runs a MAY forward dataflow over each function's whole control-flow graph and carries, per register, the SET
of lui words whose value reached it (so two lui values meeting in one register are seen) and its abstract value where
every step is constant. At every load / store / jalr / AMO it reports the base register's set.

- **The shape is present**: 27 sites per image where a base carries two or three lui values at once. `bases with 1 lui`
  is 0 everywhere, so every base that any lui reaches carries at least two. These are the same 27 distinct base sites
  the A hand trace measured (`A/kit-rerun-4bbd3a74be89/LUI-HANDTRACE.md` section 4, point 2: "166 MEMBASE/JUMPBASE use
  lines at 27 distinct sites; in every one the base register's abstract value is unknown").
- **No site forms an address**: the base's abstract value is unknown at all 108 rows. The lui values enter these bases
  as a mask, a bound or an index added to a runtime pointer (the allocator object pointer, the cache pointer, a chunk
  pointer, a loaded shadow base), which is what the two hand traces already argue per lui. So there is no combined
  target to name, and nothing for the fail-open to hide.
- **The four images agree**: the SITE rows of the donor twin, the symtwin, the decode A twin and the decode B twin are
  byte-identical, line for line: the same offsets, the same instruction text, the same base registers and the same lui
  word sets.

## Do the existing hand traces cover it?

Per function, for the shape "two or more lui in one base":

| function | sites | covered by |
|---|---|---|
| `__asan::Allocator::Allocate` | 22 | both traces, as the base sites of their class (b) rows: every base value unknown, a runtime pointer. Neither names a combined target, and this measurement shows there is none to name. |
| `__sanitizer::CombinedAllocator<…>::Allocate` | 5 | the same |
| `SizeClassAllocator64LocalCache::Refill`, `PoisonShadow`, `internal_mmap`, `StackDepotPut`, `memset`, `TryMemCpy` | 0 | nothing to cover |

So the traces cover the sites, but they report them per lui; what they did not state, and this file adds, is that at
every one of those bases two or three lui values meet, and that no such base is a statically known address in either
image.

## The control

A planted copy (plantlui.py) puts the fail-open shape itself into one function: `lui a0,0x11 ; lui a1,0x2 ;
add a0,a0,a1 ; ld a0,0(a0)`. luicomb.py reports it with its address:
`SITE memset +0xc ld a0, 0(a0) base a0 luis 2 value 0x13000 ea 0x13000 (.rodata)`, while the same function of the image
of record gives `bases with >=2 lui 0`. The tool does report a combined address when one exists.

## Verdict

cmpkit 86da41d3ef68, luicomb.py `69fe2b13fadd`: the fail-open class has no instance in the A record, the B record, the
settled rows or the shipped copy. No verdict of any record changes.
