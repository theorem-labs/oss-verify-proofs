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
(* Modified by Theorem Labs, 2026-10: c-libc-stdio's copy for fuzz_preset image A (route (a) P2) of proofs/omx-clap-core/fuzz_manifest/lib/A/RT_pf_Tbl.v at origin/cold/port-fm-rtprintf-param 7e395de08f5: PF_PRINTF_COMMON relocated by symbol, _ZL13printf_commonPvPKcS_ fm 0x44d24 -> preset A 0x4560c (size 2760 in both); the frame numbers re-measured on preset A's unstripped twin f0d2e8d4: `addi sp,sp,-0x7f0` at +0x0 and `addi sp,sp,-0xd0` at +0x3c, __asan_region_is_poisoned 0x40, __sanitizer::mem_is_zero 0x10, format_get_value_size 0x20, internal_simple_strtoll 0x10, CheckFailed 0x40, and no frame in internal_atoll, internal_strlen, internal_strnlen, internal_strchr, __sanitizer_internal_memset (first instruction not an sp adjustment), as at fm. The sentences above describe fm.asan. *)
(* Modified by Theorem Labs, 2026-10: moved to the #102 pins, image A' (fuzz_preset.asan 1be0f53d, unstripped bff8519b), from the old-pin donor origin/cold/c-libc-stdio-presetsnp-vfp ac1750cac8be: every code numeral by symbol + offset by c-asan's alreloc of record (frame/alreloc.py.frozen-c4338d099cfb8025, --src omx-clap-core/fuzz_preset --src-pin d83eb25d --assume-source; the chain's code is equal old -> #102); kept as written: the IImg record keys (fm addresses), the instruction words and the segment sizes; audited by port_addr_check 0767e70e074a (only the record keys flag). Per-numeral table: c-libc-stdio scratch/p102/reloc/A/PSnpPcTbl.v.reloc.tsv. Comment numerals are as written (sentences above that name preset A's addresses describe the old pin). *)
From Stdlib Require Import ZArith.
Open Scope Z_scope.

Definition PF_PRINTF_COMMON : Z := 0x456a0.        (* printf_common(void*, const char*, va_list) *)
Definition PF_PCOM_FRAME : Z := 2240.              (* 0x7f0 + 0xd0 *)
Definition PF_PCOM_DEPTH : Z := 2320.             (* PF_PCOM_FRAME + 80, = I_vprintfw.v PCOM_DEPTH *)
