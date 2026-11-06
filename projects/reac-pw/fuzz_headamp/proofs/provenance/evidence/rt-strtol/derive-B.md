# Image B (fuzz_headamp.asan-ubsan) twin of the strtol wrapper chain: lib/AU

Route: derive_y.py b7b132fb12a7 (sha256 b7b132fb12a73966...) over this branch's committed lib/A files at edf6010b0aae,
one run per directory (the tool writes base names into one directory), with --rename-mod lib.A=lib.AU,
--rename-tok Asan=AsanUbsan, --rename-tok Img0=Img0U (lib/AU/Img0U.v is image B's one source of segments),
--keep-name, --keep-head-literals; driver run-dy.sh and post-processor post_dy.py (copies in the evidence directory).
68 files derived (every lib/A file of the chain except RtDefs.v and RtNumber.v, which are image-independent and stay
lib/A: astrtol_realizes keeps ONE text, the one HPgCSpec.v names for both images). lib/A/HPgHole.v and lib/A/Rt/FMupoison.v
are image-independent too and stay lib/A.

Independent checks:
- alreloc a5c53bb2bed4 (A image -> B image, --from-build asan --build asan-ubsan --assume-source --dry, at 8017a2d315a5):
  129 distinct image-range numerals compared per file: 127 agree with derive_y, 2 disagree, both decided by hand
  against image B: R_prim_defs.v 0x40000 (6 rows; the 2^18 rounding constant of round_fa; derive_y moved it to
  0x40080 as a code address: WRONG; alreloc keeps it) and the comment number 0x84a0c in RtLStrtolH.v (the parse's
  strtol call: B's is 0x84ddc, lib/AU/HPgHole.v B_CALL_STRTOL; derive_y 0x84e04 and alreloc 0x84a0c both wrong).
- every image-range numeral derive_y wrote (200 rows: code 82, bss 53, image-bound 27, .got 23, data 15) checked by
  symbol + offset in both unstripped twins (a .got cell by the symbol its word points to): 200 same, 0 different.
- .got cells: 23 rows over 4 cells (0x9c360 -> 0x9c7e0 common_flags, 0x9c368 -> 0x9c7e8 asan_flags,
  0x9c370 -> 0x9c7f0 __asan_shadow_memory_dynamic_address, 0x9cff8 -> 0x9d478 __stack_chk_guard): each B cell holds
  the pointer to the same symbol: checked 23, wrong 0.
- model constants: every numeral token of every derived file body (7317 tokens) compared with its A twin: every
  changed token is one of the 200 checked address rows (0 unchecked changes); 0x40000 restored (above). derive_y also
  rewrote the comment number "5,012" as "5,12" in two header comments: the A comments now give this image's count.
- image-derived values: image B's bounds recomputed from its pin: PT_LOAD [0x10000 ...) and the last PT_LOAD end
  0x5f9ab0 -> page top 0x5fa000 (the same as A's), errno 0x5d812c in segment 3 (B0's YF0m TFIB_ERRNO); the owned
  read-only count of RtBzPins.v's header recomputed on B (52 intersections of B0's 77 owned ranges, 1272 bytes).
Hand edits (post_dy.py, one line each in derive-B-edits.tsv): H1 note names the A path; H2 note after the leading
comments; H3 RtDefs / RtNumber Requires kept at lib.A.Rt; H4 HPgHole / FMupoison kept at lib.A; H5 0x40000; H6
image B's facts in comments (RtLStrtolH.v, RtBzPins.v, RtBzHBase.v).
