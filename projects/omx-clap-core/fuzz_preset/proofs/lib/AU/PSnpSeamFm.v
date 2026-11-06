(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/cgif/cgif_file_fuzzer/lib/A/AE2y.v, with its module paths and module names changed; 503 of its 563 lines of code are new or changed and 644 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_preset/lib/A/PSnpSeam.v, with its module paths and module names changed; 36 of its 79 lines of code are new or changed and 520 lines of the source are left out. *)
(* THE GXA SEAM AT fm.asan's MUSL VFPRINTF, CLOSED: FMgxaSeam.fm_vfprintf_seam with every Section
   hypothesis discharged but the ambient ones (the FP state fx, the run ceiling rc, the symbol
   assignment B with its laws and fm's symbols).

   The three interceptor call contracts and their readiness predicates are fm's own
   (FMgxa_mem.memcpy_stack_contract_A / memset_stack_contract_A at FMgxa_mem.copy_ready /
   set_ready, RT_gxa_strnlen.strnlen_stack_contract_A at RT_gxa_strnlen.strn_ready), all three at
   the image instance RT_IImgA.A_img, the instance fm_vfprintf_seam runs at.  READY, the readiness
   of those three predicates at musl vfprintf's call site, is FMgxaSeamReady.seam_ready_holds.

   No function is proved here and no machine step is walked: this file only instantiates.  New
   file. *)
(* Modified by Theorem Labs, 2026-10: c-libc-stdio's restatement for fuzz_preset image A (L3-V2) of proofs/omx-clap-core/fuzz_manifest/lib/A/FMgxaSeamFm.v at origin/cold/port-fm-rtprintf-param 3e35620c52e: fm_vfprintf_seam_closed -> vfprintf_seam_closed_x, over ARx with Hp fixed and generic in the covered pieces PK; READY is discharged by PSnpSeamReady.seam_ready_holds at c-libc-str's lib/AU/PSnpL3/FMgxa_mem.v copy_ready / set_ready and RT_gxa_strnlen.v strn_ready (each _def by iff_refl), the three interceptor contracts are their memcpy_stack_contract_A / memset_stack_contract_A / strnlen_stack_contract_A and GXA's closed theorem their RT_gxa_inst.fm_vfprintf_snf_a_closed (3244f5c71f6), all at N_img_asan, the ASan-wrapped record fm's A_img is; the Section keeps the laws, alx_band_pres (c-omx-alloc field 20) and TfibSyms (the world's w_H8 field is the world record's own, YA0n.w_H8, which PSnpSeamReady.v reads). The sentences above name fm's files. *)
(* Modified by Theorem Labs, 2026-10: image B twin (fuzz_preset.asan-ubsan f8f98a95) of lib/A/PSnpSeamFm.v, by the unit's image-B convention (lib/AU/FCxA.v's rule): the image record CJ.RL.I.IImgA.N_img_asan -> CJ.RL.I.IImgB.N_img_asan (rebuilt pin, by path from h-hpreset-7-pvN-B 16345363f93d via c-libc-str f697dea427f), lib/A/PSnpBz -> lib/AU/PSnpBz, the image-A core A<x> -> image B's Y<x> (lib/Reusable), the PSnp seam files lib/A -> lib/AU. Sentences above that name image A or fm describe the A twin. *)
(* Modified by Theorem Labs, 2026-10: moved to the #102 pins, image B' (fuzz_preset.asan-ubsan d663f82d, unstripped c90d4fa5), from the old-pin donor origin/cold/c-libc-stdio-presetsnp-vfp ac1750cac8be: every code numeral by symbol + offset, checked equal to the B -> B' map of record (preset-F reloc102-maps bmap_b2bp.py 27b4c628bef6 over this file); B''s derived bounds from that map: the read-only top / writable start 0xa1000 -> 0xa2000, the image top 0x600000 -> 0x601000; kept as written: the IImg record keys, the instruction words and the segment sizes; audited by port_addr_check 0767e70e074a (only the record keys flag). Per-numeral table: c-libc-stdio scratch/p102/reloc/AU/PSnpSeamFm.v.reloc.tsv. Comment numerals are as written. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YK11 YK04 YK0i YK0s YK14 YK1b YK1a YK18 YP09 YG0n YG00 YG0a YG01 YG0f YG0v YG0d YA0n YM05.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YB1v.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import FMsnprintfPf PSnpShared PSnpSx PSnpPfFam.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YCbqG FCiface.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YF0m.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.CJ.RL.Reloc Require Import RStep.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.CJ.RL.GX Require G_printf_core_common.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.CJ.RL.GXA Require
AsanFacts CopyCall SetCall StrnlenCall G_printf_core_common G_printf_snfsink G_vfprintf_snf.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.CJ.RL.I Require Import IImgB.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.AU Require Import PSnpSeamDef.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.AU Require PSnpSeamNorm PSnpSeamReady PSnpSeam.
Require OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.AU.PSnpBz.A.R_m2s.
Require OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.AU.PSnpBz.A.I_qck.
Require OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.AU.PSnpBz.A.I_memcpyw.
Require OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.AU.PSnpBz.A.I_memsetw.
Require OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.AU.PSnpBz.A.I_memchrw.
Require OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.AU.PSnpBz.A.I_strnlenw.
Require OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.AU.PSnpBz.Spec.StrFun.
Require OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.AU.PSnpL3.FMgxa_mem.
Require OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.AU.PSnpL3.RT_gxa_strnlen.
Import ListNotations.
Local Open Scope Z_scope.

Module GXC := OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.CJ.RL.GX.G_printf_core_common.G_printf_iface.
Module GVA := OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.CJ.RL.GXA.G_vfprintf_snf.
Module GSA := OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.CJ.RL.GXA.G_printf_snfsink.
Module GCC := OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.CJ.RL.GXA.CopyCall.
Module GSC := OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.CJ.RL.GXA.SetCall.
Module GNC := OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.CJ.RL.GXA.StrnlenCall.
Module NM := OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.AU.PSnpSeamNorm.
Module SR := OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.AU.PSnpSeamReady.
Module SM := OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.AU.PSnpSeam.
Module BR := OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.AU.PSnpBz.A.R_m2s.
Module BQ := OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.AU.PSnpBz.A.I_qck.
Module BMW := OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.AU.PSnpBz.A.I_memcpyw.
Module BSW := OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.AU.PSnpBz.A.I_memsetw.
Module BCW := OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.AU.PSnpBz.A.I_memchrw.
Module BNW := OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.AU.PSnpBz.A.I_strnlenw.
Module BSF := OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.AU.PSnpBz.Spec.StrFun.

Module FMM := OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.AU.PSnpL3.FMgxa_mem.
Module RSN := OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.AU.PSnpL3.RT_gxa_strnlen.

#[local] Existing Instance N_img_asan.

Section F. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : asyms.
Variable ARx : alayout -> astate -> list Z -> world tfibsegs -> (word -> option byte) -> Model -> Prop.
(* the AR_laws_x fields the seam and its readiness use (YCbqG.v), each under its field's name, and the engine lemma
   stk_bounds_x's statement (7792959a2abb YCbqG.v:308) *)
Hypothesis alx_frame : ARx_frame_law tfibsegs B ARx.
Hypothesis alx_stack : ARx_stack_law tfibsegs B ARx.
Hypothesis alx_zshadow : ARx_zshadow_law tfibsegs B ARx.
Hypothesis alx_zshadow_byte : ARx_zshadow_byte_law tfibsegs ARx.
Hypothesis alx_const_cells : ARx_const_cells_law tfibsegs B ARx.
Hypothesis alx_layout_ok : ARx_layout_ok_law tfibsegs ARx.
Hypothesis stk_bounds_x : forall ly S Hp W mem md,
  ARx ly S Hp W mem md -> kHighMemBeg <= ly_stk_lo ly /\ ly_stk_hi ly <= kHighMemEnd.
(* AR_laws_x field 20 alx_band_pres (c-omx-alloc 14:56Z), inline until its Definition lands *)
Hypothesis alx_band_pres : forall ly S Hp W mem md a, ARx ly S Hp W mem md -> in_band_rw a ->
  w_H W (w64 a) = false -> ~ in_vis0 ly a -> aview tfibsegs (w_H W) mem a <> None.
Hypothesis TB : YF0m.TfibSyms B.
Variable PK : pf_piece -> Prop.
Hypothesis PK_cov : forall p, PK p -> match p with PLit _ | Pc | Px04 | Ps | Pps => True | _ => False end.

Theorem vfprintf_seam_closed_x :
  forall (K gc gv img_lo img_hi snw fam_lo fam_hi : Z) (cr : list (Z * Z)),
    GVA.VFA_DEPTH <= K -> gc = @sym N_img_asan 0x22e18 -> gv = @sym N_img_asan 0x34288 ->
    snw = @sym N_img_asan GXC.K_SN_WRITE -> img_lo <= 65536 -> @GXC.GLOBALS_TOP N_img_asan <= img_hi ->
    65536 <= fam_lo -> fam_hi <= @sym N_img_asan 0x22e18 -> NM.ro_covered cr ->
    sh_avfprintf_icpt_realizes_xx tfibsegs B ARx
      (pf_family_ro PK fam_lo fam_hi) K gc gv img_lo img_hi cr snw (@sym N_img_asan 0x7f000400).
Proof.
exact (SM.vfprintf_seam_x B ARx alx_frame alx_stack alx_zshadow alx_zshadow_byte alx_layout_ok stk_bounds_x TB PK PK_cov
         FMM.copy_ready FMM.set_ready RSN.strn_ready
         FMM.memcpy_stack_contract_A FMM.memset_stack_contract_A RSN.strnlen_stack_contract_A
         (SR.seam_ready_holds FMM.copy_ready (fun m sp d s n => iff_refl _) FMM.set_ready (fun m sp d n => iff_refl _)
            RSN.strn_ready (fun m sp s n buf => iff_refl _)
            B ARx alx_zshadow_byte alx_const_cells alx_layout_ok stk_bounds_x alx_band_pres TB)).
Qed.

End F.
