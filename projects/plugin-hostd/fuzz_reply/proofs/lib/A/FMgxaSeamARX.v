(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Theorem Labs, 2026-10: the two side laws of the ARx seam files (FMgxaSeamNormX.v / FMgxaSeamReadyX.v), PROVED at
   the cf instance and at reply's top_x instance ARX:
     LAY   : forall ly S Hp W mem md, ARx ly S Hp W mem md -> layout_ok ly
             (preset's AR_laws_x field 18 alx_layout_ok, ARx_layout_ok_law; reply's Reusable/YCbqG.v has no such field);
     BANDP : forall ly S Hp W mem md a, ARx ly S Hp W mem md -> in_band_rw a ->
               w_H W (w64 a) = false -> ~ in_vis0 ly a -> aview tfibsegs (w_H W) mem a <> None
             (preset's alx_band_pres, PSnpSnpRoot.v:96-98 / PSnpSeamReady.v:542-543 at
             a working branch dad42dbecbc4).
   Generic part (any segs, B, CfImg, CfParams): layout_ok_cf from ARmcf's amc_layout (YG0ncf.v:217); band_pres_cf from
   ARcf's last conjunct `ahs B ly S (w_H W) mem` (YG0ncf.v:612), split on the byte: a client byte (a live chunk's user
   bytes or a fake frame's shadow) is visible by YG0qcf.client_band_vis_cf (amc_client); any other band byte that is
   not hidden and not in_vis0 is present by ahs_pres (YG0n.v:442-444), and a present visible band byte is readable
   (YG0q.aview_band, with the image env from ALedger_cf, YG0qcf.al_img_env_cf). The client / non-client split is
   decided under a double negation (the goal is a negation), so no axiom is used.
   Instance part: ARX_seam is top_x's ARX (W_LLVMFuzzerTestOneInput_top_x.v:131-132) VERBATIM, so a plug at ARX is
   `exact` up to unfolding; its AR_laws_x is top_x's ARX_laws proof (:133-138) restated over the seam files' segment
   name tfibsegs (AB1v.v, the same Asan.M.loaded_segments as W_tbl.v's frsegs = pa_segs PB_fr); ARX_LAY / ARX_BANDP
   are the two laws at ARX_seam. Then each ARx lemma of FMgxaSeamShadowX / NormX / PostX at ARX_seam (the plug
   check: the three Section hypotheses LAWS, LAY, BANDP hold at reply's instance with no premise left). *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn YP0b YP0a.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YN3v YI04 YI00.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import
W_syms W_listing W_place W_tbl W_kit W_pl W_img W_journal.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YCbqG.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import W_kit_x W_journal_x.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import AD2l CfImgA CfParamsReply.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YGcfNames YG0ncf YGcallcf YG0lawscf.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YG0q YG0qcf.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require AB1v AF0m RT_IImgA FMgxaSeamBase FMgxaSeamShadow.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.CJ.RL.GXA Require AsanFacts.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.CJ.Lib Require Frame.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require FCiface.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require FMgxaSeamShadowX FMgxaSeamNormX FMgxaSeamPostX.
Import ListNotations.
Open Scope Z_scope.

Module SHX := OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A.FMgxaSeamShadowX.
Module NMX := OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A.FMgxaSeamNormX.
Module POX := OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A.FMgxaSeamPostX.
Module CJF := OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.CJ.Lib.Frame.

(* ---- the two laws at the cf allocator relation, for any image and parameters ---- *)
Section G. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {ci : CfImg} {cp : CfParams}.
Variable segs : list Segment.
Variable B : asyms.

Lemma layout_ok_cf : forall ly S Hp (W : world segs) mem md, ARcf segs B ly S Hp W mem md -> layout_ok ly.
Proof. intros ly S Hp W mem md (M & _). exact (amc_layout _ _ _ _ _ M). Qed.

Lemma band_pres_cf : forall ly S Hp (W : world segs) mem md a,
  ARcf segs B ly S Hp W mem md -> in_band_rw a -> w_H W (w64 a) = false -> ~ in_vis0 ly a ->
  aview segs (w_H W) mem a <> None.
Proof.
intros ly S Hp W mem md a (M & L & _ & _ & HP & _) Ha Hh NV.
pose proof (al_img_env_cf segs ly S md (amc_layout _ _ _ _ _ M) L) as IMG.
assert (NNEM : forall P : Prop, ~ ~ (P \/ ~ P))
  by (intros P k; apply k; right; intros p; apply k; left; exact p).
intros Hn. apply (NNEM (aclient_byte B ly S a)). intros [C|NC].
- (* a client byte: ARmcf's amc_client *)
  exact (client_band_vis_cf B ly S Hp _ a M Ha C Hn).
- (* any other byte, not hidden and not in_vis0: ahs_pres *)
  apply (proj2 (aview_band segs (w_H W) mem a IMG Ha Hh)); [|exact Hn].
  exact (HP a Ha NC (or_intror NV)).
Qed.

End G.

(* ---- reply's top_x instance ---- *)
Section I. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
#[local] Abbreviation segs := (@pa_segs _ fr_prog_listing PB_fr).

(* top_x.v:131-132, verbatim *)
Definition ARX_seam : alayout -> astate -> list Z -> world segs -> (word -> option byte) -> Model -> Prop :=
  fun ly S Hp W mem md => ARcf (ci := CfImg_A) (cp := CfParams_reply) segs TfibB ly S Hp W mem md /\ Hp = [].

(* top_x.v:133-138 (ARX_laws), over the seam files' segment name *)
Lemma ARX_seam_laws : AR_laws_x AB1v.tfibsegs TfibB ARX_seam (@cf_head CfParams_reply).
Proof.
  unfold ARX_seam. apply AR_laws_x_and_hp.
  exact (AR_laws_x_cf (cp := CfParams_reply) segs TfibB
           (AR_laws_ok_cf (cp := CfParams_reply) segs TfibB)).
Qed.

(* LAY at ARX *)
Lemma ARX_LAY : forall ly S Hp (W : world AB1v.tfibsegs) mem md, ARX_seam ly S Hp W mem md -> layout_ok ly.
Proof. intros ly S Hp W mem md (HAR & _). exact (layout_ok_cf segs TfibB ly S Hp W mem md HAR). Qed.

(* BANDP at ARX *)
Lemma ARX_BANDP : forall ly S Hp (W : world AB1v.tfibsegs) mem md a, ARX_seam ly S Hp W mem md -> in_band_rw a ->
  w_H W (w64 a) = false -> ~ in_vis0 ly a -> aview AB1v.tfibsegs (w_H W) mem a <> None.
Proof. intros ly S Hp W mem md a (HAR & _). exact (band_pres_cf segs TfibB ly S Hp W mem md a HAR). Qed.

(* ---- the plug check: the ARx lemmas of ShadowX / NormX / PostX at ARX_seam, no premise left ---- *)
Lemma ARX_musl_prefix : forall ly S Hp (W : world AB1v.tfibsegs) mem md, ARX_seam ly S Hp W mem md ->
  @AsanFacts.musl_prefix_addressable RT_IImgA.A_img (FMgxaSeamBase.cjstore (w_H W) mem).
Proof.
intros ly S Hp W mem md HAR.
exact (SHX.musl_prefix_of_ARx TfibB ARX_seam _ ARX_seam_laws ly S Hp W mem md
         (FMgxaSeamShadow.zsh_rodata_of_tfib TfibB TfibB_syms) HAR).
Qed.

Lemma ARX_layout_of_pre : forall ly S Hp (W : world AB1v.tfibsegs) regs mem md,
  FCiface.ecall_pre_x AB1v.tfibsegs TfibB ARX_seam ly S Hp W regs mem md -> layout_ok ly.
Proof. exact (NMX.layout_of_pre_x TfibB ARX_seam ARX_LAY). Qed.

Lemma ARX_stk_bounds : forall ly S Hp (W : world AB1v.tfibsegs) mem md,
  ARX_seam ly S Hp W mem md -> kHighMemBeg <= ly_stk_lo ly /\ ly_stk_hi ly <= kHighMemEnd.
Proof. exact (NMX.stk_bounds_x ARX_seam ARX_LAY). Qed.

Lemma ARX_win_owned : forall ly S Hp (W : world AB1v.tfibsegs) regs mem md (Wn : list (Z * Z)),
  FCiface.ecall_pre_x AB1v.tfibsegs TfibB ARX_seam ly S Hp W regs mem md ->
  (forall a, 0 <= a < 2 ^ 64 -> Exists (fun r => fst r <= a < snd r) Wn ->
     (ly_stk_lo ly <= a < ly_stk_hi ly) \/ ~ aowned TfibB ly S a) ->
  (forall a, 0 <= a < 2 ^ 64 -> aowned TfibB ly S a -> CJF.outside Wn a).
Proof. exact (POX.win_owned_x TfibB ARX_seam _ ARX_seam_laws). Qed.

Lemma ARX_of_window : forall ly S Hp (W : world AB1v.tfibsegs) regs mem md m' (Wn : list (Z * Z)),
  FCiface.ecall_pre_x AB1v.tfibsegs TfibB ARX_seam ly S Hp W regs mem md ->
  CJF.munch Wn (FMgxaSeamBase.cjstore (w_H W) mem) m' ->
  CJF.wmono AB1v.tfibsegs (FMgxaSeamBase.cjstore (w_H W) mem) m' ->
  (forall a, 0 <= a < 2 ^ 64 -> aowned TfibB ly S a -> CJF.outside Wn a) ->
  (forall a, 0 <= a < 2 ^ 64 -> YCbqG.kept_x AB1v.tfibsegs TfibB a -> CJF.outside Wn a) ->
  exists md', same_but_materialized md md' /\ ARX_seam ly S Hp W (munrestrict (w_H W) mem m') md'.
Proof. exact (POX.arx_of_window TfibB ARX_seam _ ARX_seam_laws). Qed.

End I.
