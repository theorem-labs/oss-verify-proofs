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
(* Modified by Theorem Labs, 2026-10: image B twin (fuzz_preset.asan-ubsan f8f98a95, unstripped twin 3b5e1a09) of lib/A/PSnpI.v: every image-A constant relocated A -> B BY SYMBOL + OFFSET by the same script (fm -> B directly gives the same values; each code row decodes to the same mnemonic), the frame offsets unchanged (the internal file snpr-CONFIRM.md A.2: preset B equals fm modulo relocation), the cross-checks against image B's YE2p / YE3h. Sentences above that name image A describe the A twin. *)
(* relocation table: fm symbol + offset | fm.asan | preset A | preset B (A -> B by symbol + offset, the same script; fm -> B gives the same values)
   PC_snprintf     __interceptor_trampoline_snprintf+0x0                        0x41314   -> A 0x42cc4 -> B 0x42d48
   A_SNI           ___interceptor_snprintf+0x0                                  0x45c90   -> A 0x46578 -> B 0x465fc
   A_VSNI          ___interceptor_vsnprintf+0x0                                 0x458a0   -> A 0x46188 -> B 0x4620c
   A_PCOM          _ZL13printf_commonPvPKcS_+0x0                                0x44d24   -> A 0x4560c -> B 0x45690
   A_VFPI          ___interceptor_vfprintf+0x0                                  0x457ec   -> A 0x460d4 -> B 0x46158
   A_VSN           vsnprintf+0x0                                                0x91f0c   -> A 0x9a63c -> B 0x9aed8
   A_VFP           vfprintf+0x0                                                 0x8ede0   -> A 0x950a0 -> B 0x9593c
   A_PCORE         printf_core+0x0                                              0x8ef90   -> A 0x95250 -> B 0x95aec
   A_FWX           __fwritex+0x0                                                0x8ea20   -> A 0x94ce0 -> B 0x9557c
   A_SNW           sn_write+0x0                                                 0x91fd8   -> A 0x9a708 -> B 0x9afa4
   W_MEMCPY        __interceptor_trampoline_memcpy+0x0                          0x51a64   -> A 0x5234c -> B 0x523d0
   W_MEMSET        __interceptor_trampoline_memset+0x0                          0x51a60   -> A 0x52348 -> B 0x523cc
   W_STRNLEN       __interceptor_trampoline_strnlen+0x0                         0x412cc   -> A 0x42c88 -> B 0x42d0c
   W_VFPRINTF      __interceptor_trampoline_vfprintf+0x0                        0x41308   -> A 0x42cb8 -> B 0x42d3c
   RA_PCORE0       vfprintf+0x68                                                0x8ee48   -> A 0x95108 -> B 0x959a4
   RA_PCORE        vfprintf+0x108                                               0x8eee8   -> A 0x951a8 -> B 0x95a44
   RA_FLUSH        vfprintf+0x128                                               0x8ef08   -> A 0x951c8 -> B 0x95a64
   A_TRY           _ZN6__asan18TryAsanInitFromRtlEv+0x0                         0x59a78   -> A 0x5a6a8 -> B 0x5a72c
   RA_VSNI         ___interceptor_snprintf+0x58                                 0x45ce8   -> A 0x465d0 -> B 0x46654
   RA_PCOM_VSNI    ___interceptor_vsnprintf+0x78                                0x45918   -> A 0x46200 -> B 0x46284
   RA_VSN          ___interceptor_vsnprintf+0x94                                0x45934   -> A 0x4621c -> B 0x462a0
   WRC_ENTRY       ___interceptor_vsnprintf+0x178                               0x45a18   -> A 0x46300 -> B 0x46384
   WRC_END         ___interceptor_vsnprintf+0xfc                                0x4599c   -> A 0x46284 -> B 0x46308
   RA_MSET         vsnprintf+0x64                                               0x91f70   -> A 0x9a6a0 -> B 0x9af3c
   RA_VFPI         vsnprintf+0xa0                                               0x91fac   -> A 0x9a6dc -> B 0x9af78
   RA_PCOM_VFPI    ___interceptor_vfprintf+0x58                                 0x45844   -> A 0x4612c -> B 0x461b0
   RA_VFP          ___interceptor_vfprintf+0x70                                 0x4585c   -> A 0x46144 -> B 0x461c8
   SLOT_VSN        _ZN14__interception14real_vsnprintfE+0x0                     0x9b748   -> A 0xa3850 -> B 0xa40f0
   SLOT_VFP        _ZN14__interception13real_vfprintfE+0x0                      0x9b740   -> A 0xa3848 -> B 0xa40e8
   SLOT_CFLAGS     GOT cell of the auipc/ld pair at ___interceptor_vsnprintf+0x 0x999a0   -> A 0xa1ac0 -> B 0xa2360
   A_CHECK_PRINTF  _ZN11__sanitizer21common_flags_dont_useE+0x54                0x1338fc  -> A 0x13c43c -> B 0x13ccfc
   A_ASAN_INITED   _ZN6__asanL11asan_initedE+0x0                                0xa2a58   -> A 0xab598 -> B 0xabe58
   FM_GOT_canary   GOT cell of the auipc/ld pair at vsnprintf+0x20 (and vfprintf+0x28) 0x9a638 -> A 0xa2758 -> B 0xa2ff8
   FM_canary       __stack_chk_guard+0x0                                        0x5f4db0 -> A 0x5fd910 -> B 0x5fe1d0 *)
(* Modified by Theorem Labs, 2026-10: moved to the #102 pins, image B' (fuzz_preset.asan-ubsan d663f82d, unstripped c90d4fa5), from the old-pin donor origin/cold/c-libc-stdio-presetsnp-vfp ac1750cac8be: every code numeral by symbol + offset, checked equal to the B -> B' map of record (preset-F reloc102-maps bmap_b2bp.py 27b4c628bef6 over this file); B''s derived bounds from that map: the read-only top / writable start 0xa1000 -> 0xa2000, the image top 0x600000 -> 0x601000; kept as written: the IImg record keys, the instruction words and the segment sizes; audited by port_addr_check 0767e70e074a (only the record keys flag). Per-numeral table: c-libc-stdio scratch/p102/reloc/AU/PSnpI.v.reloc.tsv. Comment numerals are as written. *)
From Stdlib Require Import ZArith.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YG0d.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YE2p YE3h.
Local Open Scope Z_scope.

(* ---- FMH_Base.v's runtime entry ---- *)
Definition PC_snprintf : Z := 0x42e44.
(* ---- FMsnprintfI.v ---- *)
Definition A_SNI : Z := 0x466f8.    (* __interceptor_snprintf *)
Definition A_VSNI : Z := 0x46308.    (* __interceptor_vsnprintf *)
Definition A_PCOM : Z := 0x4578c.    (* printf_common (ctx, format, aq) *)
Definition A_VFPI : Z := 0x46254.    (* __interceptor_vfprintf *)
Definition A_VSN : Z := 0x9b3c8.    (* musl vsnprintf *)
Definition A_VFP : Z := 0x95e2c.    (* musl vfprintf *)
Definition A_PCORE : Z := 0x95fdc.    (* musl printf_core *)
Definition A_FWX : Z := 0x95a6c.    (* musl __fwritex *)
Definition A_SNW : Z := 0x9b494.    (* musl sn_write *)
Definition W_MEMCPY : Z := 0x524cc.    (* __wrap_memcpy *)
Definition W_MEMSET : Z := 0x524c8.    (* __wrap_memset *)
Definition W_STRNLEN : Z := 0x42e08.    (* __wrap_strnlen *)
Definition W_VFPRINTF : Z := 0x42e38.
Definition RA_PCORE0 : Z := 0x95e94.    (* vfprintf's return points: printf_core (0, ..) *)
Definition RA_PCORE : Z := 0x95f34.    (* printf_core (f, ..) *)
Definition RA_FLUSH : Z := 0x95f54.    (* f->write (f, 0, 0) *)
(* ---- FMsnprintfGI.v ---- *)
Definition A_TRY : Z := 0x5a828.    (* __asan::TryAsanInitFromRtl *)
Definition RA_VSNI : Z := 0x46750.    (* __interceptor_snprintf: return from the vsnprintf interceptor *)
Definition RA_PCOM_VSNI : Z := 0x46380.    (* __interceptor_vsnprintf: return from printf_common *)
Definition RA_VSN : Z := 0x4639c.    (* __interceptor_vsnprintf: return from REAL (vsnprintf) *)
Definition WRC_ENTRY : Z := 0x46480.    (* __interceptor_vsnprintf: WRITE_RANGE (str, res + 1), size >= res + 1 *)
Definition WRC_END : Z := 0x46404.
Definition RA_MSET : Z := 0x9b42c.    (* musl vsnprintf: return from memset *)
Definition RA_VFPI : Z := 0x9b468.    (* musl vsnprintf: return from __wrap_vfprintf *)
Definition RA_PCOM_VFPI : Z := 0x462ac.    (* __interceptor_vfprintf: return from printf_common *)
Definition RA_VFP : Z := 0x462c4.    (* __interceptor_vfprintf: return from REAL (vfprintf) *)
Definition SLOT_VSN : Z := 0xa45d0.    (* REAL (vsnprintf) = A_VSN *)
Definition SLOT_VFP : Z := 0xa45c8.    (* REAL (vfprintf) = A_VFP *)
Definition SLOT_CFLAGS : Z := 0xa2840.    (* -> common_flags 0x13cca8; check_printf at + 0x54 *)
Definition A_CHECK_PRINTF : Z := 0x13d27c.
Definition A_ASAN_INITED : Z := 0xac3d8.

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
Lemma psnp_got_canary : YE2p.A_GOT_canary = 0xa34d8. Proof. vm_compute. reflexivity. Qed.
Lemma psnp_canary : YE2p.A_canary = 0x5fe770. Proof. vm_compute. reflexivity. Qed.
Lemma psnp_vfp : A_VFP = YE3h.A_vfprintf. Proof. reflexivity. Qed.
