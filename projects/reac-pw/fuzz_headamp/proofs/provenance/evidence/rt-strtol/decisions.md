# Port of the strtol wrapper chain and musl strtol to fuzz_headamp.asan (image A)

Donor: origin/ossv/recipes 2d2ff01bb6f, proofs/plugin-hostd/fuzz_command/lib/A (69 files of the 230-file closure of
RtLStrtol.v, I_strtolw.v, I_strtolfix.v, R_isPoisoned.v and strtol_wrap_sb.v that are not in this unit already).
Not copied: lib/Reusable (this unit's kit), lib/Lib, lib/MemNorm.v, lib/BWorld.v, lib/Img0.v, lib/Prog/__intscan_c.v,
lib/Spec/CType.v (this unit's own files; equal text apart from module paths, and __intscan_c.v apart from INTSCAN),
lib/A/Img0.v (this unit's, from the a4spec merge: the same rsegs over images.Asan), and the A core AB1q AB1v AE20 AE2y
AE34 AF0l AF0m AF0x (this unit's A2 / A3 layers).

## Same code (elfdis 6edf458084a6, --diff, level 3 = identical except pc-relative fields)
headamp vs fuzz_command.asan, every function the walks step through: __interceptor_trampoline_strtol (1 insn),
___interceptor_strtol (49), StrtolFixAndCheck (304), __asan_region_is_poisoned (209), TryAsanInitFromRtl (40),
AsanInitFromRtl (36), mem_is_zero (45), __strtol_internal (46), __intscan (374), __shlim (14), __errno_location (3):
L1 = L2 = L3 = True for each. The pc-relative fields differ; every one the proofs name is a relocated numeral below,
and the walks decode this image's bytes, so a wrong pc or target fails the build.

## Relocation (reloc.tsv, 254 rows over the 68 alreloc-written files)
- .got cells: 21 rows over 5 cells, each read in this image and compared with the donor word's target:
  0x9cff8 -> __stack_chk_guard 0x5f7d90, 0x9c360 -> common_flags 0x1368e8, 0x9c368 -> asan_flags 0xa25b8,
  0x9c370 -> __asan_shadow_memory_dynamic_address 0xa4db8, 0x9c3b0 = 1 (GetEnv's word: headamp's auipc a1,0x38 at
  0x64b80 + ld -0x7d0 at 0x64b84 = 0x9c3b0; the donor's 0xa6430 holds 1 too). Checked 21, wrong 0.
- class-5 model constants: 75 rows kept byte-identical by the tool (sizes, shadow offsets 0x7fff8000 /
  0x10007fff8000, 0x40000 / 0x3ffff / 262144 / 65536). Checked 75, wrong 0.
- image bounds: the stack-floor bound 0x5f7000 of I_ikit.v:23 and I_init.v:21 is fuzz_manifest's image end (knock's
  derive_y forbid list names it so), carried unrelocated through fuzz_boxreg and fuzz_command; alreloc's symbol rule
  moved it to 0x5ea7b8 = builtin_tls+0x12b30 (WRONG, 2 rows); set by hand to this image's end 0x5fa000 (page_up of the
  last PT_LOAD end 0x5f9630; reac-pw/fuzz_pin's port of I_ikit.v states it as IMG_TOP). The image top 0x606000 ->
  0x5fa000 (RtLStrtol.v img_lo_hi) by the tool's derived-bound rule, the same value.
- address bounds: the image top 0x606000 -> 0x5fa000 (RtLStrtol.v img_lo_hi; this image's page-rounded top,
  A3's TFIB_IMG_END) and 0x10000 (segment bound, identity).
- hand rows: __intscan.v:100/105/112/117 148089 (donor table + 1) -> 141769 (this image's table 0x229c8 + 1; the 257
  bytes are equal); RtNumber.v: the atoi entry's addresses (0x451e4, 0x4d10c; this image has no atoi interceptor) were
  kept by the resolve and then removed with the atoi contract; the comment range end 0x142cde -> 0x1369de.
- RtDefs.v: written by hand (module paths only); RT_ROM_RANGES left out (see reloc.tsv footer).

## Donor choice
Candidates for the shared Bz layer (lib/A/Bz): plugin-hostd/fuzz_command (2d2ff01bb6f) and reac-pw/fuzz_pin
(at 90722657971, itself from libreac/fuzz_boxreg f26f9fbd8777). Comments stripped, numerals
masked: 37 files equal, 5 differ in numerals only (I_consts, R_isPoisoned, R_m2s, R_memiszero, R_small), 2 differ in
structure: I_ikit.v (pin states the stack floor as YImgTop's IMG_TOP, the donor as the literal 0x5f7000) and
Bz/Lib/ImageA.v (pin drops the unused bsegs). The fuzz_command files are kept (the rule-24 donor; I_init.v,
I_strtolw.v, I_strtolfix.v exist only there). The RtBz* adapters: pin's Rt/FMbz_bridge, FMbz_clean, FMbz_str,
FMrt_lift, FMrt_pre are the same lineage (ratio 0.87-0.97) with extra ARU / unpoison lemmas the strtol walk does not
use; the fuzz_command files are kept.

## Shadow bytes the wrapper reads (review item F1)
From the walk's premises (I_strtolw.v istrtol_spec, I_strtolfix.v sfixE_spec, I_qck.v chk_ok = acc /\ qc_words /\
rng_ok): for the end-pointer cell e (8 bytes, e mod 8 = 0) the shadow byte shad(e) = e / 8 + 0x7fff8000, which must
be 0 (acc), and the 8-byte aligned shadow word al8(shad(e)) (qc_words: read, value free; it describes the 64 bytes
[e - e mod 64, e - e mod 64 + 64)); for the string x the shadow byte of each byte of [x, x + nn) for every
1 <= nn <= len + 1 (acc: addressable) and the shadow words al8(shad(x)) and al8(shad(x + nn - 1)) (qc_words).
No other shadow byte of the caller's frame is read by the wrapper.
