(* The numerals of fuzz_manifest.asan's printf_common call (RT_pf_bz.v), one name each, in the form of port-reply's
   lib/A/RT_pf_Tbl.v (origin/cold/port-reply-pf-chain 970f7d733a4) restricted to printf_common.
   MEASURED from fm.asan's unstripped twin (port-fm's fuzz_manifest.asan,
   symbol table and disassembly), keyed on the symbol, never on a bare address of another image:

     printf_common = _ZL13printf_commonPvPKcS_ at 0x44d24 (size 2760). It is the same code as fuzz_reply.asan's
     printf_common at 0x45964 instruction for instruction: 690 instructions each, 0 differences in mnemonic, registers
     or size, 30 differing only in the immediate of an auipc consumer (pc-relative addressing); its callees map by
     symbol (analyses/pcommon-wip/cmpfn.py on cold/port-fm-pcom).

     Its own frame: `addi sp,sp,-0x7f0` at +0x0 and `addi sp,sp,-0xd0` at +0x3c, 2032 + 208 = 2240 bytes.
     The deepest window its success path charges below that frame, per callee (first instruction `addi sp,sp,-N`):
       __asan_region_is_poisoned 64, and its callee __sanitizer::mem_is_zero 16 below it: 80;
       format_get_value_size 32 (its callee internal_strchr 0);
       internal_atoll 0, and its callee internal_simple_strtoll 16: 16;
       internal_strlen, internal_strnlen, internal_strchr, __sanitizer_internal_memset: 0 (leaf, no frame).
     (CheckFailed, 64, is reached only on a failed CHECK, which never returns.)
     So printf_common's window is 2240 + 80 = 2320 bytes below its entry sp. *)
(* Modified by Theorem Labs, 2026-10: c-libc-stdio's copy for fuzz_preset image A (route (a) P2) of proofs/omx-clap-core/fuzz_manifest/lib/A/RT_pf_Tbl.v at origin/cold/port-fm-rtprintf-param 7e395de08f5: PF_PRINTF_COMMON relocated by symbol, _ZL13printf_commonPvPKcS_ fm 0x44d24 -> preset A 0x4560c (size 2760 in both); the frame numbers re-measured on preset A's unstripped twin f0d2e8d4: `addi sp,sp,-0x7f0` at +0x0 and `addi sp,sp,-0xd0` at +0x3c, __asan_region_is_poisoned 0x40, __sanitizer::mem_is_zero 0x10, format_get_value_size 0x20, as at fm. The sentences above describe fm.asan. *)
(* Modified by Theorem Labs, 2026-10: image B twin (fuzz_preset.asan-ubsan f8f98a95) of lib/A/PSnpPcTbl.v, by the unit's image-B convention (lib/AU/FCxA.v's rule): module paths lib/A/PSnpBz -> lib/AU/PSnpBz (alreloc's image-B relocation), the image-A core A<x> -> image B's Y<x> (lib/Reusable), lib/A/Img0 -> lib/B/Img0, the PSnp glue lib/A -> lib/AU. PF_PRINTF_COMMON: _ZL13printf_commonPvPKcS_ -> preset B 0x45690 (size 2760); frame numbers re-measured on B's unstripped twin 3b5e1a09: `addi sp,sp,-0x7f0` at +0x0, `addi sp,sp,-0xd0` at +0x3c, __asan_region_is_poisoned 0x40, __sanitizer::mem_is_zero 0x10, format_get_value_size 0x20, internal_simple_strtoll 0x10, CheckFailed 0x40, and no frame in internal_atoll, internal_strlen, internal_strnlen, internal_strchr, __sanitizer_internal_memset (first instruction not an sp adjustment), as at A and fm. Sentences above that name image A describe the A twin. *)
(* Modified by Theorem Labs, 2026-10: moved to the #102 pins, image B' (fuzz_preset.asan-ubsan d663f82d, unstripped c90d4fa5), from the old-pin donor origin/cold/c-libc-stdio-presetsnp-vfp ac1750cac8be: every code numeral by symbol + offset, checked equal to the B -> B' map of record (preset-F reloc102-maps bmap_b2bp.py 27b4c628bef6 over this file); B''s derived bounds from that map: the read-only top / writable start 0xa1000 -> 0xa2000, the image top 0x600000 -> 0x601000; kept as written: the IImg record keys, the instruction words and the segment sizes; audited by port_addr_check 0767e70e074a (only the record keys flag). Per-numeral table: c-libc-stdio scratch/p102/reloc/AU/PSnpPcTbl.v.reloc.tsv. Comment numerals are as written. *)
From Stdlib Require Import ZArith.
Open Scope Z_scope.

Definition PF_PRINTF_COMMON : Z := 0x4578c.        (* printf_common(void*, const char*, va_list) *)
Definition PF_PCOM_FRAME : Z := 2240.              (* 0x7f0 + 0xd0 *)
Definition PF_PCOM_DEPTH : Z := 2320.             (* PF_PCOM_FRAME + 80, = I_vprintfw.v PCOM_DEPTH *)
