(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/cgif/cgif_file_fuzzer/lib/A/AE2y.v, with its module paths and module names changed; 449 of its 511 lines of code are new or changed and 642 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_disco/lib/A/FMgxaSeam.v, with its module paths and module names changed; 233 of its 353 lines of code are new or changed and 391 lines of the source are left out. *)
(* reac-pw/fuzz_link, image A (fuzz_link.asan, pin 059dae63e07c): THE GXA SEAM OF MUSL VFPRINTF ON LINK'S MEMORY FILE.
   musl vfprintf 0x973e0 (= sym 0x7f000400 of RecAsanVfA.N_img_asan_vf) realizes the A-engine contract
   LinkVfDefs.avfprintf_mf_realizes at the window LVF_MUSL_STK = 5552 (GXA's VFA_DEPTH), the stack-protector cells
   LA_GOT_GUARD 0xa2658 -> LA_GUARD 0x651c50, link's FILE record AMemFile.link_amf and link's format family
   FMsnprintfFmI.FF_fmP pf_link_piece, for every relro bound pair rlo rhi (link_vfprintf_mf_musl).

   Nothing here walks a machine step. The walk is the GXA theorem of musl vfprintf on the memory FILE
   (lib/CJ/RL/GXA/LinkVfMfA.v vfprintf_mf_a_proof), closed at link's image record (LinkVfSeamCall.v
   seam_vfprintf_mf_a); this file feeds it the contract's premises and reads its post back, following the donors'
   seam for musl vsnprintf's FILE (lib/A/FMgxaSeam.v fm_vfprintf_seamP), with the memory FILE's pieces from
   LinkVfSeam{Block,Cells,Guard,Ready,Norm}.v:
   - the arguments: GXA's (f k fl jp jc we wp j48 wb j64 j104 mode lbf jx pb bjunk A VA OM fmt slots args lo canary
     r o) are the contract's f, k, its words (w64 fl, w64 wend, w64 wpos, w64 wbase, w64 om, the lbf word AU32M1),
     the FILE's own bytes between them (LinkVfSeamCells.mf_file_in), the k pending bytes, the rest of the buffer,
     fmt, ap, |T|, the format with its NUL, map w64 ws, the model's argument list, sp - K, w64 cval, |T| and T;
   - the read agreement the normalization needs (MemNorm.ro_agree) from consts_view over FMsnprintfCr.fm_cr, which
     comes from the contract's arodata_okP (its image arm is FMH_Base.rom_viewN) and AR (RtBzAdapt.rom_viewO_of_ARm:
     the owned read-only bytes are pinned by AR's constant table), as FMsnprintfCr.fm_cr_consts_view states it;
   - the store: GXA runs on cjnormv ly R (FMgxaSeamNorm.v) at R = NM.seam_R (f + 280) 1024 fmt fmtb (sp - K) K ws
     args: the buffer, the format, the window, musl's prefix and each %s string carved out; the FILE header and the
     buffer are application memory above GLOBALS_TOP, which cjnormv keeps (LinkVfSeamNorm.cells_cjnormv_high);
   - the FILE block: it lies in high application memory and below the stack's floor (LinkVfSeamBlock.v), so it is
     off the image, apart from the window, and every byte of it present and not the runtime's;
   - the guard: LinkVfSeamNorm.vf_mf_guard_cjnormv, with READY discharged at link's three interceptor predicates
     by LinkVfSeamReady.seam_ready_holds_mf;
   - the run: as the donor's (FMgxaSeamNorm.evt_from_norm_MS_v, FMgxaSeam.sa_evt_eqv, FMgxa_bridge.srr_of_gxa_evt);
   - the post: GXA's post at the harness's final store (LinkVfSeamNorm.post_from_norm_mf_v), the window and the FILE
     block as the footprint of the frame and of AR (FMgxaSeamPost.v), and the FILE's words back as apf_file_post
     (LinkVfSeamCells.mf_file_post, mf_buf_post).
   The contract is the AR form (ecall_pre); the donor lemmas stated with a user-poisoned list U are used at U = [].
   Section hypotheses: B, its laws (AR_laws tfibsegs B) and link's symbols (PcapSyms B), as the donor seam's;
   link_vfprintf_mf_musl_PcapB closes them at AD2l.PcapB. *)
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import
YK11 YK04 YK0i YK0s YK14 YK1b YK1a YK18 YP09 YG0n YG00 YG0a YG01 YG0f YG0v YG0d YA0n YM05 YI04 YC20.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require YG0q.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A Require Import AB1v AF0m AMemFile.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Rt Require Import SnUpoison PfFacts SnShared SnFF.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A Require Import FMpfStep FMgxa_bridge FMgxaSeamBase FMgxaSeamPf.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A Require AD2l AF0x FMH_Base FMsnprintfCr FMsnprintfFmI FMgxaSeam
  FMgxaSeamCall FMgxaSeamNormG FMgxaSeamNorm FMgxaSeamReady FMgxaSeamShadow FMgxaSeamPost FMgxaSeamCells
  FMgxaSeamFam RT_gxa_calls_mem RT_gxa_calls_mem_vf RT_gxa_strnlen.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Rt Require RtBzAdapt.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.CJ.Lib Require Mem Frame MState FP Cells Step Exec.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Lib Require Regs6ss.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.CJ.RL.Reloc Require Import RStep.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.CJ.Spec Require Prelim.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.CJ.RL.GX Require Import Printf_model.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.CJ.RL.GX Require G_printf_core_common.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.CJ.RL.G Require G_fmt_fp_lib.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.CJ.RL.GXA Require
AsanFacts G_printf_core_common G_vfprintf_snf LinkVfMfA.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.CJ.RL.I Require Import RecAsanVfA.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Rt Require Import LinkMfDefs LinkVfDefs LinkPfPiece.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Prog Require mf_sink_c.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Rt Require LinkSnpPort LinkVfSeamCall LinkVfSeamBlock
  LinkVfSeamCells LinkVfSeamGuard LinkVfSeamReady LinkVfSeamNorm.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Open Scope Z_scope.

Module RE := OSSVerify.Proofs.reac_pw.fuzz_link.lib.Lib.Regs6ss.
Module CJE := OSSVerify.Proofs.reac_pw.fuzz_link.lib.CJ.Lib.Exec.
Module CJM := OSSVerify.Proofs.reac_pw.fuzz_link.lib.CJ.Lib.Mem.
Module CJF := OSSVerify.Proofs.reac_pw.fuzz_link.lib.CJ.Lib.Frame.
Module CJMS := OSSVerify.Proofs.reac_pw.fuzz_link.lib.CJ.Lib.MState.
Module CJC := OSSVerify.Proofs.reac_pw.fuzz_link.lib.CJ.Lib.Cells.
Module CJS := OSSVerify.Proofs.reac_pw.fuzz_link.lib.CJ.Lib.Step.
Module MFS := OSSVerify.Proofs.reac_pw.fuzz_link.lib.Prog.mf_sink_c.
Module PRL := OSSVerify.Proofs.reac_pw.fuzz_link.lib.CJ.Spec.Prelim.
Module GXC := OSSVerify.Proofs.reac_pw.fuzz_link.lib.CJ.RL.GX.G_printf_core_common.G_printf_iface.
Module GAF := OSSVerify.Proofs.reac_pw.fuzz_link.lib.CJ.RL.GXA.AsanFacts.
Module GVA := OSSVerify.Proofs.reac_pw.fuzz_link.lib.CJ.RL.GXA.G_vfprintf_snf.
Module GCA := OSSVerify.Proofs.reac_pw.fuzz_link.lib.CJ.RL.GXA.G_printf_core_common.G_printf_iface.
Module GMF := OSSVerify.Proofs.reac_pw.fuzz_link.lib.CJ.RL.GXA.LinkVfMfA.
Module NM := OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.FMgxaSeamNorm.
Module SR := OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.FMgxaSeamReady.
Module SA := OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.FMgxaSeam.
Module FAM := OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.FMgxaSeamFam.
Module PST := OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.FMgxaSeamPost.
Module SHW := OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.FMgxaSeamShadow.
Module FMM := OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.RT_gxa_calls_mem.
Module FMMV := OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.RT_gxa_calls_mem_vf.
Module RSN := OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.RT_gxa_strnlen.
Module FmI := OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.FMsnprintfFmI.
Module LSC := OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Rt.LinkVfSeamCall.
Module LSB := OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Rt.LinkVfSeamBlock.
Module LCL := OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Rt.LinkVfSeamCells.
Module LSR := OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Rt.LinkVfSeamReady.
Module LSN := OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Rt.LinkVfSeamNorm.

#[local] Existing Instance N_img_asan_vf.

(* ---- link's cells and code address are the symbols GXA names ---- *)
Lemma lvs_vfp : LA_VFPRINTF = @sym N_img_asan_vf 0x7f000400.
Proof. vm_compute. reflexivity. Qed.
Lemma lvs_got : LA_GOT_GUARD = @sym N_img_asan_vf 0x22e18.
Proof. vm_compute. reflexivity. Qed.
Lemma lvs_guard : LA_GUARD = @sym N_img_asan_vf 0x34288.
Proof. vm_compute. reflexivity. Qed.
Lemma lvs_depth : LVF_MUSL_STK = GVA.VFA_DEPTH.
Proof. reflexivity. Qed.

(* the harness's store outside a footprint the walk munched: the restricted stores agree *)
Lemma mrestrict_munch : forall (H : word -> bool) mem (m' : word -> option byte) (Wn : list (Z * Z)) (x : word),
  CJF.munch Wn (cjstore H mem) m' -> CJF.outside Wn (bv_unsigned x) -> mrestrict H m' x = mrestrict H mem x.
Proof.
intros H mem m' Wn x MU Ho. unfold mrestrict. destruct (H x) eqn:E; [reflexivity|].
rewrite (MU x Ho). unfold cjstore, mrestrict. rewrite E. reflexivity.
Qed.

Section S. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : asyms.
Hypothesis LAWS : AR_laws tfibsegs B.
Hypothesis TB : PcapSyms B.

(* consts_view over fm_cr from the contract's read-only premise and AR *)
Lemma lvs_consts : forall ly S (W : world tfibsegs) mem md rlo rhi,
  AR tfibsegs B ly S W mem md -> arodata_okP tfibsegs rlo rhi B (aview tfibsegs (w_H W) mem) ->
  consts_view tfibsegs W mem FMsnprintfCr.fm_cr.
Proof.
intros ly S W mem md rlo rhi HAR HRO.
apply (FMsnprintfCr.fm_cr_consts_view B W mem TB).
- intros a Ha Ho He. exact (HRO a (or_introl Ha) Ho He).
- exact (RtBzAdapt.rom_viewO_of_ARm B TB ly S W mem (proj1 HAR)).
Qed.

Theorem link_vfprintf_mf_muslB : forall rlo rhi,
  avfprintf_mf_realizes tfibsegs B link_amf rlo rhi (FmI.FF_fmP pf_link_piece) LVF_MUSL_STK
    LA_GOT_GUARD LA_GUARD LA_VFPRINTF.
Proof.
intros rlo rhi. unfold avfprintf_mf_realizes.
intros ly S W regs mem md f fmt ap k fl om wend wpos wbase pos len pb ws T cval
  HPRE HK HWIN Ha0 Ha1 Ha2 HBLK HDJ HAMF HDYN HPEND HLPB HFIT HROD Hgc Hgv Hgc0 Hgc1 Hgv0 Hgv1 Dgc Dgv
  HAP Hap0 Hap1 Dap HFAM HT FRM0.
set (K := LVF_MUSL_STK) in *.
assert (EK : K = 5552) by reflexivity.
apply FmI.FF_fmP_ro in HFAM.
destruct HFAM as (fmtb & ps & args0 & HFA & HPS & HPK & HPA & HPT & HPP & HFLO & HFHI & HSL).
(* ---- the harness state ---- *)
pose proof HPRE as (HAR & HRET & _ & _ & HSPhi & _ & _ & _).
pose proof (proj2 (ecall_preU_nil tfibsegs B ly S W regs mem md) HPRE) as HPREU.
assert (HARU : ARU tfibsegs B ly S [] W mem md) by (apply (proj2 (ARU_nil tfibsegs B ly S W mem md)); exact HAR).
assert (HSTK : kHighMemBeg <= ly_stk_lo ly /\ ly_stk_hi ly <= kHighMemEnd)
  by (eapply stk_kHighMemBeg; exact (proj1 HAR)).
unfold kHighMemBeg, kHighMemEnd in HSTK.
pose proof SA.sa_globals_top as GT. pose proof SA.sa_globals_top_a as GTA.
pose proof SA.sa_sym_got_ssp as S22. pose proof SA.sa_sym_guard as S34.
assert (Esp : bv_unsigned (getr regs 2) = spZ regs) by reflexivity.
(* ---- the FILE block ---- *)
destruct (LSB.amf_block_seam tfibsegs B LAWS ly S W mem md f HAR HBLK)
  as (Hfhi & Hfceil & Hf16 & HBY & HBHULL & HBRA & HAM & HAM8 & HSC).
pose proof ASAN_CEIL_range as [CR _].
unfold kHighMemBeg, ASAN_CEIL, AMF_BLOCK, AMF_BUF, AMF_BUFSIZ in *.
assert (HFlo : f + 1304 <= spZ regs - K) by lia.
assert (HPF : forall a, f <= a < f + 1304 -> apresent (w_H W) mem a) by (intros a Ha; exact (proj1 (HBY a Ha))).
assert (HVF : forall a, f <= a < f + 1304 -> w_H W (Z_to_bv 64 a) = false) by (intros a Ha; exact (proj1 (HPF a Ha))).
(* ---- the FILE's words and GXA's side conditions on them ---- *)
destruct (LCL.mf_side_in link_amf (mrestrict (w_H W) mem) f k fl om wend wpos wbase pos len ltac:(lia) ltac:(lia)
            HAMF HDYN) as (HWST & HFL8 & HMODE & Hk).
pose proof HDYN as (Rfl & Rom & Rwe & Rwp & Rwb & _).
destruct (LCL.mf_file_in link_amf (w_H W) mem f k fl om wend wpos wbase pos len ltac:(lia) ltac:(lia)
            ltac:(intros a Ha; apply HPF; lia) HAMF HDYN) as (jp & jc & j48 & j64 & j104 & jx & FH0).
pose proof (LCL.pend_range _ f pb HPEND) as Rpb.
destruct (LCL.mf_buf_in (w_H W) mem f pb ltac:(lia) ltac:(lia) ltac:(intros a Ha; apply HPF; lia) HPEND
            ltac:(lia)) as (bj & Lbj & BUF0).
(* ---- the family: format, pieces, arguments, text ---- *)
pose proof HFA as (Hf0 & _ & _ & _ & HFRA & _).
assert (HWR : Forall (fun w => 0 <= w < 2 ^ 64) ws).
{ apply Forall_forall. intros w Hin. apply (In_nth ws w 0) in Hin as (i & Hi & <-).
  exact (SA.sa_rdword_range _ _ _ _ (HAP i Hi)). }
pose proof (SA.sa_args_fit _ _ ws args0 HPA HWR) as HFIT'.
assert (HU : forall u, In (AU64 u) args0 -> 0 <= u < 2 ^ 64).
{ intros u Hin. rewrite Forall_forall in HFIT'. exact (HFIT' _ Hin). }
assert (HTl : PRL.zlength T <= 2147483647) by (unfold PRL.zlength; lia).
destruct (pf_model_agreeP pf_link_piece LinkSnpPort.link_text_arms fmtb ps args0 T HPS HPK HPT HFIT' HTl)
  as (AM & AP1 & _).
set (PA := PT.pf_pargs (map pt_piece ps) (map pt_arg args0)) in AM.
pose proof (pt_pargs_shapeP pf_link_piece LinkSnpPort.link_pargs_arms ps args0 T HPK HPT) as HPAS. fold PA in HPAS.
assert (TBy : Forall (fun c => 0 <= c < 256) T)
  by exact (pf_text_bytesP pf_link_piece LinkSnpPort.link_bytes_arms ps args0 T (pf_parse_codes fmtb ps HPS) HPK
              HFIT' HPT).
assert (ZL : PRL.zlength (fmtb ++ [0]) = Z.of_nat (length fmtb) + 1).
{ unfold PRL.zlength. rewrite length_app. cbn [length]. lia. }
assert (ERS : vmf_out K (spZ regs) f = [(spZ regs - K, spZ regs - (spZ regs - K)); (f, 1304)]).
{ unfold vmf_out, AMF_BLOCK. replace (spZ regs - (spZ regs - K)) with K by lia. reflexivity. }
(* ---- the read agreement the normalized store needs ---- *)
pose proof (NM.ro_agree_of_consts W mem FMsnprintfCr.fm_cr (lvs_consts ly S W mem md rlo rhi HAR HROD)
              FMsnprintfCr.fm_cr_ro_covered) as HRO.
assert (Egc : LA_GOT_GUARD = @sym N_img_asan_vf 0x22e18) by exact lvs_got.
assert (Egv : LA_GUARD = @sym N_img_asan_vf 0x34288) by exact lvs_guard.
assert (WGC : forall a, LA_GOT_GUARD <= a < LA_GOT_GUARD + 8 -> writable_at tfibsegs (cjstore (w_H W) mem) a).
{ intros a Ha. apply SA.sa_ssp_writable. left. unfold LA_GOT_GUARD in Ha. lia. }
assert (WGV : forall a, LA_GUARD <= a < LA_GUARD + 8 -> writable_at tfibsegs (cjstore (w_H W) mem) a).
{ intros a Ha. apply SA.sa_ssp_writable. right. unfold LA_GUARD in Ha. lia. }
(* ---- the carve-out list: the buffer, the format, the window, musl's prefix, each %s string ---- *)
pose proof HFA as (_ & _ & _ & AMF & _ & _).
destruct (NM.seam_drop_keeps ly (spZ regs - K) K (f + 280) 1024 fmt fmtb ws args0
            (aview tfibsegs (w_H W) mem) (vmf_out K (spZ regs) f)
            ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) HAM Hf0 AMF HPA) as (KD & KF & KW & KP & KA & KAPP).
assert (HVR : Forall (fun r => shadow_hull_vis (aview tfibsegs (w_H W) mem) (fst r) (snd r))
                (NM.seam_R (f + 280) 1024 fmt fmtb (spZ regs - K) K ws args0)).
{ apply (NM.seam_R_hulls (aview tfibsegs (w_H W) mem) (vmf_out K (spZ regs) f)).
  - exact HBHULL.
  - exact HFA.
  - eapply SR.stack_hull; try exact LAWS; try exact HARU; lia.
  - eapply SR.prefix_hull; try exact TB; try exact HARU.
  - exact HPA. }
assert (InD : In (f + 280, 1024) (NM.seam_R (f + 280) 1024 fmt fmtb (spZ regs - K) K ws args0))
  by (unfold NM.seam_R; apply in_eq).
assert (InW : In (spZ regs - K, spZ regs - (spZ regs - K)) (NM.seam_R (f + 280) 1024 fmt fmtb (spZ regs - K) K ws args0)).
{ replace (spZ regs - (spZ regs - K)) with K by lia. unfold NM.seam_R. apply in_cons, in_cons, in_eq. }
set (RN := NM.seam_R (f + 280) 1024 fmt fmtb (spZ regs - K) K ws args0) in *.
(* ---- GXA's walk, at the harness's arguments ---- *)
assert (APF : GVA.args_pf (cjstore (w_H W) mem) (map w64 ws) PA)
  by exact (SA.sa_args_pf_pt _ _ _ _ HPAS (FAM.args_pf_of_pf_args_asan (w_H W) mem _ ws args0 HPA HSL)).
pose proof (LSC.seam_vfprintf_mf_a FMM.copy_ready FMM.set_ready RSN.strn_ready FMMV.memcpy_stack_contract_Avf
              FMMV.memset_stack_contract_Avf RSN.strnlen_stack_contract_A) as G.
unfold GMF.vfprintf_mf_a_stmt in G.
specialize (G (getr regs 1) (getr regs 2) (getr regs 3) (getr regs 4) (getr regs 5) (getr regs 6) (getr regs 7)
  (getr regs 8) (getr regs 9) (getr regs 10) (getr regs 11) (getr regs 12) (getr regs 13) (getr regs 14)
  (getr regs 15) (getr regs 16) (getr regs 17) (getr regs 18) (getr regs 19) (getr regs 20) (getr regs 21)
  (getr regs 22) (getr regs 23) (getr regs 24) (getr regs 25) (getr regs 26) (getr regs 27) (getr regs 28)
  (getr regs 29) (getr regs 30) (getr regs 31) (@fp_regs fx) (@fp_csr fx) (NM.cjnormv ly RN (w_H W) mem)
  f k (w64 fl) jp jc (w64 wend) (w64 wpos) j48 (w64 wbase) j64 j104 (w64 om) (w64 AU32M1) jx (zb8 pb) bj
  fmt ap (PRL.zlength T) (fmtb ++ [0]) (map w64 ws) PA (spZ regs - K) (w64 cval) (PRL.zlength T) T).
cbv zeta in G. rewrite Esp in G.
rewrite lvs_vfp.
eapply srr_of_gxa_evt.
{ exact AF0x.Hwx_tfa. }
{ eapply SA.sa_evt_eqv.
  - eapply NM.evt_from_norm_MS_v; [exact HRO|]. apply G; clear G.
    + exact Ha0.
    + exact Ha1.
    + exact Ha2.
    + apply LSN.cells_cjnormv_high; [first [rewrite GT | rewrite GTA]; lia
                                    | cbn [CJC.cells_size MFS.mf_file CJC.csize]; unfold TASK_SIZE; lia
                                    | cbn [CJC.cells_size MFS.mf_file CJC.csize];
                                      apply GAF.high_stack_app; unfold GAF.HIGHMEM_BEG, GAF.APPMEM_END; lia
                                    | exact FH0].
    + apply LSN.cells_cjnormv_high; [first [rewrite GT | rewrite GTA]; lia
                                    | cbn [CJC.cells_size CJC.csize]; unfold TASK_SIZE; lia
                                    | cbn [CJC.cells_size CJC.csize];
                                      apply GAF.high_stack_app; unfold GAF.HIGHMEM_BEG, GAF.APPMEM_END; lia
                                    | exact BUF0].
    + rewrite zb8_length. exact HLPB.
    + exact Lbj.
    + rewrite (FAM.uw64 wend Rwe), (FAM.uw64 wpos Rwp), (FAM.uw64 wbase Rwb). exact HWST.
    + rewrite (FAM.uw64 fl ltac:(lia)). exact HFL8.
    + rewrite (FAM.uw64 om ltac:(lia)). exact HMODE.
    + vm_compute. discriminate.
    + apply NM.fmt_cjnormv; [exact HRO | rewrite ZL, GT; lia |].
      exact (FAM.fmt_bytes_of_fmt_at (w_H W) mem _ fmt fmtb HFA ltac:(lia)).
    + exact (FAM.fmt_bytes_small _ _ fmt fmtb ps HFA HPS).
    + exact AP1.
    + apply NM.va_area_cjnormv;
        [exact HRO | unfold TASK_SIZE, PRL.zlength; rewrite length_map; lia
        | apply GAF.high_stack_app;
          [unfold GAF.HIGHMEM_BEG; lia | unfold GAF.APPMEM_END, PRL.zlength; rewrite length_map; lia] |].
      exact (FAM.va_area_of_words_at (w_H W) mem ap ws ltac:(lia) ltac:(lia) HAP).
    + apply NM.args_ok_cjnormv;
        [exact HRO | exact (NM.args_task_of_pf _ _ _ APF) | exact (NM.args_app_of_pf _ _ _ APF) |].
      apply (SA.sa_args_ok_pt _ _ _ _ _ _ _ _ _ _ _ _ _ _ HPAS).
      exact (LSN.args_ok_of_pf_args_asan_mf (w_H W) mem _ ws args0 f (spZ regs - K) (spZ regs) HPA HSL HU ERS
               ltac:(lia)).
    + exact AM.
    + unfold PRL.zlength. lia.
    + unfold PRL.zlength. lia.
    + apply NM.stk_window_cjnormv;
        [first [rewrite GT | rewrite GTA]; lia | unfold TASK_SIZE; lia
        | apply GAF.high_stack_app; unfold GAF.HIGHMEM_BEG, GAF.APPMEM_END; lia |].
      exact (stk_of_apresent (w_H W) mem (spZ regs - K) (spZ regs) ltac:(lia) ltac:(lia) HWIN).
    + rewrite <- lvs_depth. lia.
    + first [rewrite GT | rewrite GTA]; lia.
    + lia.
    + apply NM.ssp_cells_cjnormv.
      exact (FMgxaSeamCells.ssp_cells_of_view (w_H W) mem LA_GOT_GUARD LA_GUARD cval (w64 cval) Egc Egv Hgc Hgv
               eq_refl WGC WGV).
    + exact (NM.mem_inv_cjnormv ly RN (w_H W) mem).
    + exact FRM0.
    + rewrite ZL, S22. lia.
    + lia.
    + exact Hap0.
    + unfold PRL.zlength. rewrite length_map. lia.
    + lia.
    + lia.
    + first [rewrite GT | rewrite GTA]; lia.
    + apply (LSN.vf_mf_guard_cjnormv FMM.copy_ready FMM.set_ready RSN.strn_ready ly RN (w_H W) mem
               (spZ regs) (spZ regs - K) f fmt (fmtb ++ [0]) (map w64 ws) PA).
      * rewrite ZL. apply SHW.pf_rng_of_view; [lia | lia | lia | | exact HFRA].
        unfold amem_range, kLowMemEnd. left. lia.
      * rewrite ZL. exact (NM.sh_kept_of_hull ly RN fmt (Z.of_nat (length fmtb) + 1) KF).
      * exact (SHW.musl_prefix_of_ARU B ly S [] W mem md (SHW.zsh_rodata_of_tfib B TB) HARU).
      * exact (NM.sh_kept_of_hull ly RN (@sym N_img_asan_vf 0x1029e) 9 KP).
      * exact APF.
      * exact (SA.sa_args_kept_pt _ _ _ _ _ HPAS KA).
      * apply GAF.high_stack_app; unfold GAF.HIGHMEM_BEG, GAF.APPMEM_END; lia.
      * apply GAF.high_stack_app; unfold GAF.HIGHMEM_BEG, GAF.APPMEM_END; lia.
      * apply GAF.high_stack_app; unfold GAF.HIGHMEM_BEG, GAF.APPMEM_END; lia.
      * unfold GCA.OUT_DEPTH. lia.
      * exact (LSR.seam_ready_holds_mf B LAWS TB ly RN S [] W regs mem md (spZ regs - K) f HPREU InD
                 ltac:(replace (spZ regs - (spZ regs - K)) with K in InW |- * by lia; exact InW)
                 HVR ltac:(lia) ltac:(unfold GCA.OUT_DEPTH; lia) ltac:(unfold kHighMemBeg; lia) ltac:(lia)
                 HAM HAM8 HBRA).
  - split; [apply RE.xregs_eqv_sym, RE.mkR_eqv_of; reflexivity|]. repeat split. }
(* ---- GXA's post, read as the harness's ---- *)
intros ms' model' (y & (st0 & HQ & HREL & HSAME) & HEQ) HSBM _.
pose proof (LSN.post_from_norm_mf_v FMgxaSeamCall.SEAM_INV ly RN (w_H W) mem _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
              _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HRO HREL HSAME HQ) as HP.
clear HQ.
destruct HP as (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & Ft & fc' & bj' & m'
                & Ey & MU & WM & FRM' & FREG & STK' & SSP' & FC' & BUF' & Hr').
subst y. rewrite Esp in MU.
destruct ms' as [R' F' pc' svc' rv' fc'' mm ro'].
destruct HEQ as (HR & HF & HPC & HSVC & HRV & HFC & HM & HROM).
cbn [ms_regs ms_fregs ms_pc_val ms_svc_pending ms_resv ms_fcsr ms_mem ms_rom CJMS.MS] in HR, HF, HPC, HSVC, HRV, HFC, HM, HROM.
subst F' pc' svc' rv' fc'' mm ro'.
assert (EPC : CJMS.ret_pc (getr regs 1) = w64 (raZ regs)) by exact (ret_pc_raZ _ HRET).
set (Wn := [(spZ regs - K, spZ regs); (f, f + 232); (f + 280, f + 1304)]) in MU.
assert (OWN : forall a, 0 <= a < 2 ^ 64 -> aowned B ly S a -> CJF.outside Wn a).
{ apply (PST.win_owned B LAWS ly S [] W regs mem md Wn HPREU). intros a Ha HE.
  apply Exists_cons in HE; destruct HE as [HE|HE]; [cbn [fst snd] in HE; left; lia|].
  apply Exists_cons in HE; destruct HE as [HE|HE]; [cbn [fst snd] in HE; right; exact (proj2 (HBY a ltac:(lia)))|].
  apply Exists_cons in HE; destruct HE as [HE|HE]; [cbn [fst snd] in HE; right; exact (proj2 (HBY a ltac:(lia)))|].
  inversion HE. }
cbv beta. split; [reflexivity|].
exists (YK11.mkFP Ft fc'), R', (munrestrict (w_H W) mem m'), model'.
split.
{ rewrite PST.cfg_of_ms. unfold unrestrict.
  cbn [ms_regs ms_fregs ms_pc_val ms_svc_pending ms_resv ms_fcsr ms_mem ms_rom].
  rewrite EPC. reflexivity. }
split.
{ intros k0 Hk0. exact (FREG k0 Hk0). }
split; [exact FRM'|].
split.
{ destruct (PST.aru_of_window B LAWS ly S [] W regs mem md m' Wn HPREU MU WM OWN) as (md2 & SB2 & ARU2).
  pose proof (same_but_materialized_frame md md2 SB2) as (_ & Hv2 & Hl2 & _).
  pose proof (same_but_materialized_frame md model' HSBM) as (_ & Hv' & Hl' & _).
  apply (proj1 (ARU_nil tfibsegs B ly S W _ model')).
  exact (SA.sa_ARU_model_same B ly S [] W _ md2 model' ARU2 ltac:(congruence) ltac:(congruence)). }
split.
{ intros r Hr. unfold acallee_saved in Hr.
  assert (RR : r = 2 \/ r = 3 \/ r = 4 \/ r = 8 \/ r = 9 \/ r = 18 \/ r = 19 \/ r = 20 \/ r = 21 \/
               r = 22 \/ r = 23 \/ r = 24 \/ r = 25 \/ r = 26 \/ r = 27) by lia.
  repeat (destruct RR as [RR|RR];
    [subst r; rewrite !SA.sa_getr_nz by reflexivity; rewrite <- (HR _) by reflexivity; reflexivity|]).
  subst r; rewrite !SA.sa_getr_nz by reflexivity; rewrite <- (HR _) by reflexivity; reflexivity. }
split; [exact HSBM|].
split.
{ rewrite SA.sa_getr_nz by reflexivity. rewrite <- (HR _) by reflexivity. reflexivity. }
split.
{ (* the FILE's words at the new window *)
  unfold apf_file_post. rewrite mrestrict_munrestrict.
  set (om' := if wend =? 0 then AU32M1 else om).
  assert (FC2 : CJS.rw_cells tfibsegs m' f
                  (MFS.mf_file (w64 fl) jp jc (w64 (f + 1304)) (w64 (f + 280 + (k + PRL.zlength T))) j48
                     (w64 (f + 280)) j64 (f + 280) j104 (w64 om') (w64 AU32M1) jx)).
  { replace (f + 280 + (k + PRL.zlength T)) with (f + 280 + k + PRL.zlength T) by lia.
    rewrite (FAM.uw64 wend Rwe) in FC'. unfold om', AU32M1. destruct (wend =? 0); exact FC'. }
  assert (HC : forall x, f + 232 <= x < f + AMF_ZEROED ->
                 mbyte tfibsegs (mrestrict (w_H W) m') x = mbyte tfibsegs (mrestrict (w_H W) mem) x).
  { intros x Hx. unfold mbyte. unfold AMF_ZEROED in Hx.
    rewrite (mrestrict_munch (w_H W) mem m' Wn (Z_to_bv 64 x) MU); [reflexivity|].
    rewrite CJMS.unsigned_lit by lia. unfold Wn. cbn [CJF.outside]. lia. }
  destruct (LCL.mf_file_post link_amf (w_H W) mem m' f k (k + PRL.zlength T) fl om om' wend wpos wbase pos len
              jp jc j48 j64 j104 jx ltac:(lia) ltac:(lia) ltac:(intros a Ha; apply HVF; lia) HAMF HDYN FH0 FC2 HC
              ltac:(unfold AMF_BUFSIZ, PRL.zlength; lia)
              ltac:(unfold om', AU32M1; destruct (wend =? 0); [right; reflexivity | exact HMODE]))
    as (HK' & HD').
  unfold PRL.zlength in HK', HD'.
  split; [exact HK'|]. split.
  - replace (f + AMF_BUF + k + Z.of_nat (length T)) with (f + AMF_BUF + (k + Z.of_nat (length T))) by lia.
    exact HD'.
  - apply (LCL.mf_buf_post (w_H W) m' f pb T bj' ltac:(intros a Ha; apply HVF; lia) Rpb TBy).
    + rewrite Nat2Z.inj_add. lia.
    + exact BUF'. }
split.
{ intros a Ha Hd HN.
  apply (PST.win_view_out (w_H W) mem m' Wn MU a Ha). unfold Wn. cbn [CJF.outside].
  unfold AMF_BLOCK in Hd. repeat split; lia. }
apply (PST.win_present_off (w_H W) mem m' Wn MU WM).
unfold Wn. repeat (apply Forall_cons; [cbn [fst snd]; lia|]). apply Forall_nil.
Qed.

End S.

(* ---- the target, at the runtime's record PcapB: Section hypotheses AR_laws tfibsegs PcapB and PcapSyms PcapB ---- *)
Section P. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Hypothesis LAWS : AR_laws tfibsegs AD2l.PcapB.
Hypothesis TB : PcapSyms AD2l.PcapB.

Theorem link_vfprintf_mf_musl : forall rlo rhi,
  @avfprintf_mf_realizes fx rc tfibsegs AD2l.PcapB link_amf rlo rhi (FmI.FF_fmP pf_link_piece) LVF_MUSL_STK
    LA_GOT_GUARD LA_GUARD LA_VFPRINTF.
Proof. exact (link_vfprintf_mf_muslB AD2l.PcapB LAWS TB). Qed.

End P.

(* ---- closed: the laws by YG0q.AR_laws_ok, link's symbols by AD2l.PcapB_syms ---- *)
Corollary link_vfprintf_mf_musl_PcapB : forall (fx : YK11.FPState) (rc : YM05.RunCeil) rlo rhi,
  @avfprintf_mf_realizes fx rc tfibsegs AD2l.PcapB link_amf rlo rhi (FmI.FF_fmP pf_link_piece) LVF_MUSL_STK
    LA_GOT_GUARD LA_GUARD LA_VFPRINTF.
Proof.
intros fx rc. exact (link_vfprintf_mf_musl (YG0q.AR_laws_ok tfibsegs AD2l.PcapB) AD2l.PcapB_syms).
Qed.
