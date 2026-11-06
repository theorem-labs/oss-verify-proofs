(* Copied from proofs/omx-clap-core/fuzz_manifest/lib/A/RT_pf_Tbl.v (a working branch 3e35620c52e); relocated to libreac/fuzz_disco.asan by g9/tool (reloc.py target disco-A): module paths changed; 2 address numerals moved (port_addr_check 0767e70e074a predict, fm.asan -> fuzz_disco.asan, symbol + offset; table g9/tool/tables/disco-A/RT_pf_Tbl.table). *)
(* The numerals of fuzz_manifest.asan's printf_common call (RT_pf_bz.v), one name each, in the form of a Theorem Labs lane's
   lib/A/RT_pf_Tbl.v (a working branch 970f7d733a4) restricted to printf_common.
   MEASURED from fm.asan's unstripped twin (a lane record (fuzz_manifest.asan),
   symbol table and disassembly), keyed on the symbol, never on a bare address of another image:

     printf_common = _ZL13printf_commonPvPKcS_ at 0x45fb4 (size 2760). It is the same code as fuzz_reply.asan's
     printf_common at 0x45fb4 instruction for instruction: 690 instructions each, 0 differences in mnemonic, registers
     or size, 30 differing only in the immediate of an auipc consumer (pc-relative addressing); its callees map by
     symbol (internal path on a working branch).

     Its own frame: `addi sp,sp,-0x7f0` at +0x0 and `addi sp,sp,-0xd0` at +0x3c, 2032 + 208 = 2240 bytes.
     The deepest window its success path charges below that frame, per callee (first instruction `addi sp,sp,-N`):
       __asan_region_is_poisoned 64, and its callee __sanitizer::mem_is_zero 16 below it: 80;
       format_get_value_size 32 (its callee internal_strchr 0);
       internal_atoll 0, and its callee internal_simple_strtoll 16: 16;
       internal_strlen, internal_strnlen, internal_strchr, __sanitizer_internal_memset: 0 (leaf, no frame).
     (CheckFailed, 64, is reached only on a failed CHECK, which never returns.)
     So printf_common's window is 2240 + 80 = 2320 bytes below its entry sp. *)
From Stdlib Require Import ZArith.
Open Scope Z_scope.

Definition PF_PRINTF_COMMON : Z := 0x45fb4.        (* printf_common(void*, const char*, va_list) *)
Definition PF_PCOM_FRAME : Z := 2240.              (* 0x7f0 + 0xd0 *)
Definition PF_PCOM_DEPTH : Z := 2320.             (* PF_PCOM_FRAME + 80, = I_vprintfw.v PCOM_DEPTH *)
