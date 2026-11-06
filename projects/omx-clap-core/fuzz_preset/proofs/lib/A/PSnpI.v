(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_preset/lib/A/ACf0.v, with its module paths changed; 167 of its 202 lines of code are new or changed and 44 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_manifest/lib/B/FMsnprintfI.v, with its module paths, module names and addresses changed; 37 of its 52 lines of code are new or changed and 187 lines of the source are left out. *)
(* fm program part, statement base: fm.asan addresses, the per-function stack/event/live constants, the user-poison
   wrappers over the donor's afn_pre / apost_base, C-string premises, fm's static allocation counters (fuzz/alloc.c).
   Definitions only. Design: a Theorem Labs lane's internal file HARNESS.md. *)
(* fm's snprintf walks (lib/A/FMsnprintf*.v), interface: the snprintf sink and the contracts the walks hand to each
   other. The chain (fm.asan, MEASURED from the unstripped twin):
     __wrap_snprintf 0x41314 -> __interceptor_snprintf 0x45c90 -> __interceptor_vsnprintf 0x458a0
       [printf_common 0x44d24; REAL = musl vsnprintf 0x91f0c -> __wrap_vfprintf 0x41308 -> __interceptor_vfprintf 0x457ec
         [printf_common; REAL = musl vfprintf 0x8ede0 -> printf_core 0x8ef90 (f = 0, then f = FILE)
           -> __fwritex 0x8ea20 -> sn_write 0x91fd8; flush sn_write (f, 0, 0)]; WRITE_RANGE (str, min (size, res + 1))]
   Frame base sp0 = musl vfprintf's entry sp. musl vsnprintf's FILE lies at sp0 + FO, its cookie {s, n} at sp0 + CKO,
   vfprintf's 80-byte internal buffer at sp0 + IBO, vfprintf's ap2 at sp0 + OSP_PC, nl_arg / nl_type after it. Every
   call below vfprintf writes only the band [sp0 - SNK_STK, sp0 + 0x200), the sink cells and the destination. *)
(* fm's snprintf glue, interface: the contracts of the walks above printf_core at fm.asan addresses, in FMsnprintfI's
   frame (sp0 = musl vfprintf's entry sp). MEASURED from the unstripped twin of fm.asan:
     __wrap_snprintf 0x41314: j 0x45c90
     __interceptor_snprintf 0x45c90: frame 0x60; a3..a7 spilled at sp + 0x38 (the va area P); TryAsanInitFromRtl 0x59a78;
       jal __interceptor_vsnprintf 0x458a0 (ra 0x45ce8)
     __interceptor_vsnprintf 0x458a0: frame 0x7f0 + 0x80; TryAsanInitFromRtl; common_flags ()->check_printf (slot 0x999a0
       -> 0x1338a8, byte + 0x54); printf_common 0x44d24 (ra 0x45918); REAL (vsnprintf) from slot 0x9b748 (ra 0x45934);
       res >= 0 and size >= res + 1: WRITE_RANGE (str, res + 1) from 0x45a18 to 0x4599c; epilogue
     musl vsnprintf 0x91f0c: frame 0x130; canary; memset (sp, 0, 0xe8) through __wrap_memset 0x51a60 (ra 0x91f70); FILE
       fields; *c.s = 0; jal __wrap_vfprintf 0x41308 = j 0x457ec (ra 0x91fac); canary check
     __interceptor_vfprintf 0x457ec: frame 0x30; TryAsanInitFromRtl; check_printf; printf_common (ra 0x45844);
       REAL (vfprintf) from slot 0x9b740 (ra 0x4585c)
     musl vfprintf 0x8ede0: frame 0x170 (the walks below it are FMsnprintfI's)
   Entry sps from sp0: vfprintf sp0, its interceptor sp0 + 0x30, vsnprintf sp0 + 0x160, its interceptor sp0 + 0x9d0, the
   snprintf interceptor sp0 + 0xa30; the va area P = sp0 + 0xa08. *)
(* Modified by Theorem Labs, 2026-10: c-libc-stdio's image-A layer for fuzz_preset (route (a), c-omx-hpreset 10:51Z; parent decision (A): restate and re-pin in one step) of the snprintf chain's image constants from origin/cold/port-fm-rtprintf-param 7e395de08f5 lib/A/FMH_Base.v, FMsnprintfI.v and FMsnprintfGI.v (the three headers above): each fm.asan numeral relocated BY SYMBOL + OFFSET to preset image A (fuzz_preset.asan d83eb25d, unstripped twin f0d2e8d4) by c-libc-stdio's pyelftools + capstone script scratch/snpx/reloc/reloc_defs.py, fm.asan read at its unstripped twin fc92e86b (loadable bytes of 0ba7e169); the table below gives fm symbol + offset, fm address and preset A address per constant, and every code row decodes to the same mnemonic in both images. Frame offsets (FO, CKO, IBO, OSP_*, OP_VA, SNK_STK, STK_PCOM) are fm's: the chain's code is equal modulo relocation (lookups/snpr-CONFIRM.md A.1; the frame sizes -0x60 / -0x7f0 / -0x130 / -0x170 / -0x220 decode equal). The stack-protector cells are NOT restated: fm's FM_GOT_canary 0x9a638 (GOT cell of vsnprintf+0x20) and FM_canary 0x5f4db0 (__stack_chk_guard) relocate to 0xa2758 / 0x5fd910, which are preset's own AE2p.A_GOT_canary / AE2p.A_canary (checked below). Left out, unreached by the four roots: FMH_Base's fm-harness addresses, STK_* and predicates, FMH_Rt (fm's seven formats, frender, the runtime contracts; preset's formats are not fm's), and the FMsnprintfI / GI predicates and contracts (SNK, snk_*, fw_*, gl_*, vsn_*, a*_realizesU; the memset contract is Reusable/YGcallMx.v aintrin_realizes_x). *)
(* relocation table: fm symbol + offset | fm.asan | preset A (from the internal file reloc_defs.py)
   PC_snprintf     __interceptor_trampoline_snprintf+0x0                        0x41314   -> 0x42cc4
   A_SNI           ___interceptor_snprintf+0x0                                  0x45c90   -> 0x46578
   A_VSNI          ___interceptor_vsnprintf+0x0                                 0x458a0   -> 0x46188
   A_PCOM          _ZL13printf_commonPvPKcS_+0x0                                0x44d24   -> 0x4560c
   A_VFPI          ___interceptor_vfprintf+0x0                                  0x457ec   -> 0x460d4
   A_VSN           vsnprintf+0x0                                                0x91f0c   -> 0x9a63c
   A_VFP           vfprintf+0x0                                                 0x8ede0   -> 0x950a0
   A_PCORE         printf_core+0x0                                              0x8ef90   -> 0x95250
   A_FWX           __fwritex+0x0                                                0x8ea20   -> 0x94ce0
   A_SNW           sn_write+0x0                                                 0x91fd8   -> 0x9a708
   W_MEMCPY        __interceptor_trampoline_memcpy+0x0                          0x51a64   -> 0x5234c
   W_MEMSET        __interceptor_trampoline_memset+0x0                          0x51a60   -> 0x52348
   W_STRNLEN       __interceptor_trampoline_strnlen+0x0                         0x412cc   -> 0x42c88
   W_VFPRINTF      __interceptor_trampoline_vfprintf+0x0                        0x41308   -> 0x42cb8
   RA_PCORE0       vfprintf+0x68                                                0x8ee48   -> 0x95108
   RA_PCORE        vfprintf+0x108                                               0x8eee8   -> 0x951a8
   RA_FLUSH        vfprintf+0x128                                               0x8ef08   -> 0x951c8
   A_TRY           _ZN6__asan18TryAsanInitFromRtlEv+0x0                         0x59a78   -> 0x5a6a8
   RA_VSNI         ___interceptor_snprintf+0x58                                 0x45ce8   -> 0x465d0
   RA_PCOM_VSNI    ___interceptor_vsnprintf+0x78                                0x45918   -> 0x46200
   RA_VSN          ___interceptor_vsnprintf+0x94                                0x45934   -> 0x4621c
   WRC_ENTRY       ___interceptor_vsnprintf+0x178                               0x45a18   -> 0x46300
   WRC_END         ___interceptor_vsnprintf+0xfc                                0x4599c   -> 0x46284
   RA_MSET         vsnprintf+0x64                                               0x91f70   -> 0x9a6a0
   RA_VFPI         vsnprintf+0xa0                                               0x91fac   -> 0x9a6dc
   RA_PCOM_VFPI    ___interceptor_vfprintf+0x58                                 0x45844   -> 0x4612c
   RA_VFP          ___interceptor_vfprintf+0x70                                 0x4585c   -> 0x46144
   SLOT_VSN        _ZN14__interception14real_vsnprintfE+0x0                     0x9b748   -> 0xa3850
   SLOT_VFP        _ZN14__interception13real_vfprintfE+0x0                      0x9b740   -> 0xa3848
   SLOT_CFLAGS     GOT cell of the auipc/ld pair at ___interceptor_vsnprintf+0x 0x999a0   -> 0xa1ac0
   A_CHECK_PRINTF  _ZN11__sanitizer21common_flags_dont_useE+0x54                0x1338fc  -> 0x13c43c
   A_ASAN_INITED   _ZN6__asanL11asan_initedE+0x0                                0xa2a58   -> 0xab598
   FM_GOT_canary   GOT cell of the auipc/ld pair at vsnprintf+0x20 (and vfprintf+0x28) 0x9a638 -> 0xa2758
   FM_canary       __stack_chk_guard+0x0                                        0x5f4db0 -> 0x5fd910 *)
(* Modified by Theorem Labs, 2026-10: moved to the #102 pins, image A' (fuzz_preset.asan 1be0f53d, unstripped bff8519b), from the old-pin donor origin/cold/c-libc-stdio-presetsnp-vfp ac1750cac8be: every code numeral by symbol + offset by c-asan's alreloc of record (frame/alreloc.py.frozen-c4338d099cfb8025, --src omx-clap-core/fuzz_preset --src-pin d83eb25d --assume-source; the chain's code is equal old -> #102); kept as written: the IImg record keys (fm addresses), the instruction words and the segment sizes; audited by port_addr_check 0767e70e074a (only the record keys flag). Per-numeral table: c-libc-stdio scratch/p102/reloc/A/PSnpI.v.reloc.tsv. Comment numerals are as written (sentences above that name preset A's addresses describe the old pin). *)
From Stdlib Require Import ZArith.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YG0d.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require AE2p AE3h.
Local Open Scope Z_scope.

(* ---- FMH_Base.v's runtime entry ---- *)
Definition PC_snprintf : Z := 0x42d58.
(* ---- FMsnprintfI.v ---- *)
Definition A_SNI : Z := 0x4660c.    (* __interceptor_snprintf *)
Definition A_VSNI : Z := 0x4621c.    (* __interceptor_vsnprintf *)
Definition A_PCOM : Z := 0x456a0.    (* printf_common (ctx, format, aq) *)
Definition A_VFPI : Z := 0x46168.    (* __interceptor_vfprintf *)
Definition A_VSN : Z := 0x9ab78.    (* musl vsnprintf *)
Definition A_VFP : Z := 0x955dc.    (* musl vfprintf *)
Definition A_PCORE : Z := 0x9578c.    (* musl printf_core *)
Definition A_FWX : Z := 0x9521c.    (* musl __fwritex *)
Definition A_SNW : Z := 0x9ac44.    (* musl sn_write *)
Definition W_MEMCPY : Z := 0x523e0.    (* __wrap_memcpy *)
Definition W_MEMSET : Z := 0x523dc.    (* __wrap_memset *)
Definition W_STRNLEN : Z := 0x42d1c.    (* __wrap_strnlen *)
Definition W_VFPRINTF : Z := 0x42d4c.
Definition RA_PCORE0 : Z := 0x95644.    (* vfprintf's return points: printf_core (0, ..) *)
Definition RA_PCORE : Z := 0x956e4.    (* printf_core (f, ..) *)
Definition RA_FLUSH : Z := 0x95704.    (* f->write (f, 0, 0) *)
(* ---- FMsnprintfGI.v ---- *)
Definition A_TRY : Z := 0x5a73c.    (* __asan::TryAsanInitFromRtl *)
Definition RA_VSNI : Z := 0x46664.    (* __interceptor_snprintf: return from the vsnprintf interceptor *)
Definition RA_PCOM_VSNI : Z := 0x46294.    (* __interceptor_vsnprintf: return from printf_common *)
Definition RA_VSN : Z := 0x462b0.    (* __interceptor_vsnprintf: return from REAL (vsnprintf) *)
Definition WRC_ENTRY : Z := 0x46394.    (* __interceptor_vsnprintf: WRITE_RANGE (str, res + 1), size >= res + 1 *)
Definition WRC_END : Z := 0x46318.
Definition RA_MSET : Z := 0x9abdc.    (* musl vsnprintf: return from memset *)
Definition RA_VFPI : Z := 0x9ac18.    (* musl vsnprintf: return from __wrap_vfprintf *)
Definition RA_PCOM_VFPI : Z := 0x461c0.    (* __interceptor_vfprintf: return from printf_common *)
Definition RA_VFP : Z := 0x461d8.    (* __interceptor_vfprintf: return from REAL (vfprintf) *)
Definition SLOT_VSN : Z := 0xa3d90.    (* REAL (vsnprintf) = A_VSN *)
Definition SLOT_VFP : Z := 0xa3d88.    (* REAL (vfprintf) = A_VFP *)
Definition SLOT_CFLAGS : Z := 0xa2000.    (* -> common_flags 0x13c3e8; check_printf at + 0x54 *)
Definition A_CHECK_PRINTF : Z := 0x13ca3c.
Definition A_ASAN_INITED : Z := 0xabb98.

(* ---- frame offsets from sp0 = musl vfprintf's entry sp (FMsnprintfI.v, FMsnprintfGI.v; unchanged) ---- *)
Definition FO : Z := 0x30.          (* musl vsnprintf's FILE *)
Definition CKO : Z := FO + 0xe8.    (* its cookie {s, n} *)
Definition IBO : Z := -352.         (* vfprintf's internal_buf[80] *)
Definition OSP_PC : Z := -368.      (* sp at printf_core's entry = &ap2; nl_arg at +0x60, nl_type at +0x108 *)
Definition OSP_FW : Z := -912.      (* sp at __fwritex / sn_write entry from printf_core's out() *)
Definition SNK_STK : Z := 9104.     (* the band below sp0 the chain below vfprintf uses (donor VF_STK) *)
Definition snk_band (sp0 a : Z) : Prop := sp0 - SNK_STK <= a < sp0 + 0x200.
Definition STK_PCOM : Z := 2 * YG0d.ESTACK.
Definition OSP_VFPI : Z := 0x30.
Definition OSP_VSN : Z := 0x160.
Definition OSP_VSNI : Z := 0x9d0.
Definition OSP_SNI : Z := 0xa30.
Definition OP_VA : Z := 0xa08.

(* ---- cross-checks against preset's own image-A names ---- *)
Lemma psnp_got_canary : AE2p.A_GOT_canary = 0xa2c98. Proof. vm_compute. reflexivity. Qed.
Lemma psnp_canary : AE2p.A_canary = 0x5fdf30. Proof. vm_compute. reflexivity. Qed.
Lemma psnp_vfp : A_VFP = AE3h.A_vfprintf. Proof. reflexivity. Qed.
