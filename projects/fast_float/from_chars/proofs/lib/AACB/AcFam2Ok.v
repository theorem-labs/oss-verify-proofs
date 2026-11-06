(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.fast_float.from_chars.images Require Import AsanUbsan.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec ShapeSet RealizesCfg AsanAcct PlacementCount AllocNodesCfg.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import FxLin FxCore FxSound FxMem FxSubst FxEnt FxCall.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXC Require Import FxBacking FxChDen FxWvC FxChMain.
From OSSVerify.Proofs.fast_float.from_chars.lib.AACB Require AcPri.
From OSSVerify.Proofs.fast_float.from_chars.lib.AACB Require AcAst AcHA AcFam AcPri AcConvA AcNPop AcNEnq AcNPopG.
From OSSVerify.Proofs.fast_float.from_chars.lib.AACB Require AcFam2.
From OSSVerify.Proofs.fast_float.from_chars.lib.AACB Require AcFam2.
From OSSVerify.Proofs.fast_float.from_chars.lib.AACB Require AcNPopN.

Module AcNPopAll.
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.fast_float.from_chars.images Require Import AsanUbsan.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec ShapeSet RealizesCfg AsanAcct PlacementCount AllocNodesCfg.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxLin FxCore FxSound FxMem FxFacts FxStep.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxLoop.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxSubst FxEnt FxPlan FxFrame FxDrv FxCall.
Import OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxLin OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxCore OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxSound OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxMem OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxFacts OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxStep OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxLoop.FxExplore OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxSubst OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxEnt OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxPlan OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxFrame OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxDrv OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxCall.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require Import AxMng.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXC Require Import FxBacking FxChDen FxChLib FxChSep FxChFix FxChMain.
From OSSVerify.Proofs.fast_float.from_chars.lib.AAXB Require Import AXG_put AXG_np AXG_nf1 AXG_npf.
From OSSVerify.Proofs.fast_float.from_chars.lib.AACB Require AcPri.
From OSSVerify.Proofs.fast_float.from_chars.lib.AACB Require AcAst AcHA AcFacts AcMALlib AcPri AcPriStep AcNPop AcNPopN AcNPopF.
Import OSSVerify.Proofs.fast_float.from_chars.lib.AACB.AcPri.AcDepSep OSSVerify.Proofs.fast_float.from_chars.lib.AACB.AcAst OSSVerify.Proofs.fast_float.from_chars.lib.AACB.AcHA OSSVerify.Proofs.fast_float.from_chars.lib.AACB.AcFacts OSSVerify.Proofs.fast_float.from_chars.lib.AACB.AcMALlib OSSVerify.Proofs.fast_float.from_chars.lib.AACB.AcPri OSSVerify.Proofs.fast_float.from_chars.lib.AACB.AcPriStep OSSVerify.Proofs.fast_float.from_chars.lib.AACB.AcNPop OSSVerify.Proofs.fast_float.from_chars.lib.AACB.AcNPopN OSSVerify.Proofs.fast_float.from_chars.lib.AACB.AcNPopF.
Import ListNotations.
Local Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Section NPopAll.
Variable cfg : SpuriousCfg.
Variable LIMIT : Z.
Variable model0 : Model.
Hypothesis Hwx : wx_segs_nowrap ASEGS.
Hypothesis Hsegb : segs_below_b ASEGS 0x800000000000 = true.
Hypothesis Hoff : sc_alloc cfg = false.
Hypothesis Hrespos : Forall (fun p => 0 < bv_unsigned (snd p)) (segments_reserved ASEGS).
Hypothesis Hreswf : ivs_wf (segments_reserved ASEGS).

#[using="Hwx Hsegb Hoff Hrespos Hreswf"] Theorem npop_node0 : forall c S M a S' M' a', apost_npop0 LIMIT c S M a = Some (S', M', a') ->
  forall mem0 E ms model T, DEN ASEGS LIMIT model0 mem0 E S M ms model -> awf (s_next S) a = true -> HA E M a mem0 ->
  (forall E' mem0' ms' model', agree (s_next S) E E' -> frz_same E M mem0 mem0' -> DEN ASEGS LIMIT model0 mem0' E' S' M' ms' model' ->
     HA E' M' a' mem0' -> realizes_cfg ASEGS cfg (mkCfg ms' model') T) ->
  realizes_cfg ASEGS cfg (mkCfg ms model) T.
Proof. LiaFast.lf_pins (fun (Hwx Hsegb Hoff Hrespos Hreswf : LiaFast.U) => LiaFast.u0).
  intros c S M a S' M' a' H mem0 E ms model T Hd Haw HHA Hk.
  pose proof H as H0. unfold apost_npop0 in H0. cbv zeta in H0. apply obool_some in H0 as (Hon & _).
  apply andb_prop in Hon as [Hon _]. apply andb_prop in Hon as [Hon _]. apply andb_prop in Hon as [Hon _].
  apply andb_prop in Hon as [Hon Hcin]. apply andb_prop in Hon as [Hon Hlen].
  apply existsb_eqb_in in Hcin. apply Nat.eqb_eq in Hlen.
  assert (Hne : a_pri a <> []) by (intros Hn; rewrite Hn in Hlen; discriminate).
  pose proof (po_inv _ _ _ _ (ha_pri _ _ _ _ (HHA Hon) Hne)) as HI. unfold INV_A in HI.
  destruct (cls_jb (pden E a) mem0 HI c Hcin) as (K0 & _).
  destruct (Z.eq_dec (z_j (pden E a) c) 0) as [Hz|Hnz].
  - exact (npop_node_first cfg LIMIT model0 Hwx Hsegb Hoff Hrespos Hreswf c S M a S' M' a' H mem0 E ms model T Hd Haw HHA Hz Hk).
  - exact (npop_node_pop cfg LIMIT model0 Hwx c S M a S' M' a' H mem0 E ms model T Hd Haw HHA ltac:(clear - K0 Hnz; lia) Hk).
Qed.

#[using="Hwx Hsegb Hoff Hrespos Hreswf"] Theorem npop_node : forall c S M a S' M' a', apost_npop LIMIT c S M a = Some (S', M', a') ->
  forall mem0 E ms model T, DEN ASEGS LIMIT model0 mem0 E S M ms model -> awf (s_next S) a = true -> HA E M a mem0 ->
  (forall E' mem0' ms' model', agree (s_next S) E E' -> frz_same E M mem0 mem0' -> DEN ASEGS LIMIT model0 mem0' E' S' M' ms' model' ->
     HA E' M' a' mem0' -> realizes_cfg ASEGS cfg (mkCfg ms' model') T) ->
  realizes_cfg ASEGS cfg (mkCfg ms model) T.
Proof. LiaFast.lf_pins (fun (Hwx Hsegb Hoff Hrespos Hreswf : LiaFast.U) => LiaFast.u0).
  intros c S M a S' M' a' H mem0 E ms model T Hd Haw HHA Hk. unfold apost_npop in H.
  exact (npop_node0 c _ M a S' M' a' H mem0 E ms model T (den_sp_fact ASEGS LIMIT model0 mem0 E S M ms model Hd) Haw HHA Hk).
Qed.
End NPopAll.
(* [comment removed for export] *)
End AcNPopAll.


Module AcNPopGAll.
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.fast_float.from_chars.images Require Import AsanUbsan.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec ShapeSet RealizesCfg AsanAcct PlacementCount AllocNodesCfg.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxLin FxCore FxSound FxMem FxFacts FxStep.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxLoop.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxSubst FxEnt FxPlan FxFrame FxDrv FxCall.
Import OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxLin OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxCore OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxSound OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxMem OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxFacts OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxStep OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxLoop.FxExplore OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxSubst OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxEnt OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxPlan OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxFrame OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxDrv OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxCall.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require Import AxMng.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXC Require Import FxBacking FxChDen FxChLib FxChSep FxChFix FxChMain.
From OSSVerify.Proofs.fast_float.from_chars.lib.AAXB Require Import AXG_put AXG_np AXG_nf1 AXG_npf AXG_gp AXG_gf1.
From OSSVerify.Proofs.fast_float.from_chars.lib.AACB Require AcUnwApp.
From OSSVerify.Proofs.fast_float.from_chars.lib.AACB Require AcPri.
From OSSVerify.Proofs.fast_float.from_chars.lib.AACB Require AcAst AcHA AcFacts AcMALlib AcPri AcPriStep AcNPop AcNPopG.
Import OSSVerify.Proofs.fast_float.from_chars.lib.AACB.AcUnwApp.AcPutApp OSSVerify.Proofs.fast_float.from_chars.lib.AACB.AcPri.AcDepSep OSSVerify.Proofs.fast_float.from_chars.lib.AACB.AcAst OSSVerify.Proofs.fast_float.from_chars.lib.AACB.AcHA OSSVerify.Proofs.fast_float.from_chars.lib.AACB.AcFacts OSSVerify.Proofs.fast_float.from_chars.lib.AACB.AcMALlib OSSVerify.Proofs.fast_float.from_chars.lib.AACB.AcPri OSSVerify.Proofs.fast_float.from_chars.lib.AACB.AcPriStep OSSVerify.Proofs.fast_float.from_chars.lib.AACB.AcNPop OSSVerify.Proofs.fast_float.from_chars.lib.AACB.AcNPopG.
From OSSVerify.Proofs.fast_float.from_chars.lib.AACB Require AcNPopGLib.
From OSSVerify.Proofs.fast_float.from_chars.lib.AACB Require AcNPopGF.
From OSSVerify.Proofs.fast_float.from_chars.lib.AACB Require AcNPopGF.
Import OSSVerify.Proofs.fast_float.from_chars.lib.AACB.AcNPopGLib OSSVerify.Proofs.fast_float.from_chars.lib.AACB.AcNPopGF.AcNPopGN OSSVerify.Proofs.fast_float.from_chars.lib.AACB.AcNPopGF.
Import ListNotations.
Local Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Section NPopGAll.
Variable cfg : SpuriousCfg.
Variable LIMIT : Z.
Variable model0 : Model.
Hypothesis Hwx : wx_segs_nowrap ASEGS.
Hypothesis Hsegb : segs_below_b ASEGS 0x800000000000 = true.
Hypothesis Hoff : sc_alloc cfg = false.
Hypothesis Hrespos : Forall (fun p => 0 < bv_unsigned (snd p)) (segments_reserved ASEGS).
Hypothesis Hreswf : ivs_wf (segments_reserved ASEGS).

#[using="Hwx Hsegb Hoff Hrespos Hreswf"] Theorem npopg_node0 : forall S M a S' M' a', apost_npopg0 LIMIT S M a = Some (S', M', a') ->
  forall mem0 E ms model T, DEN ASEGS LIMIT model0 mem0 E S M ms model -> awf (s_next S) a = true -> HA E M a mem0 ->
  (forall E' mem0' ms' model', agree (s_next S) E E' -> frz_same E M mem0 mem0' -> DEN ASEGS LIMIT model0 mem0' E' S' M' ms' model' ->
     HA E' M' a' mem0' -> realizes_cfg ASEGS cfg (mkCfg ms' model') T) ->
  realizes_cfg ASEGS cfg (mkCfg ms model) T.
Proof. LiaFast.lf_pins (fun (Hwx Hsegb Hoff Hrespos Hreswf : LiaFast.U) => LiaFast.u0).
  intros S M a S' M' a' H mem0 E ms model T Hd Haw HHA Hk.
  pose proof H as H0. unfold apost_npopg0 in H0. cbv zeta in H0.
  apply obool_some in H0 as (Hon & H0).
  apply obind_some in H0 as (ND8 & _ & H0). cbv beta in H0.
  apply obind_some in H0 as (stk & _ & H0). cbv beta in H0.
  apply obind_some in H0 as (ro & _ & H0). cbv beta in H0.
  apply obind_some in H0 as (ist & _ & H0). cbv beta in H0.
  apply obind_some in H0 as (R & _ & H0). cbv beta in H0.
  apply obind_some in H0 as (o & _ & H0). cbv beta in H0.
  apply obind_some in H0 as (cv & _ & H0). cbv beta in H0.
  apply obind_some in H0 as (jP & _ & H0). cbv beta in H0.
  apply obind_some in H0 as (jT & _ & H0). cbv beta in H0.
  apply obind_some in H0 as (gP & _ & H0). cbv beta in H0.
  apply obool_some in H0 as (Hchk & _).
  apply andb_prop in Hon as [Hon _]. apply andb_prop in Hon as [Hon _]. apply andb_prop in Hon as [Hon _]. apply andb_prop in Hon as [Hon Hlen].
  apply Nat.eqb_eq in Hlen.
  do 20 (apply andb_prop in Hchk as [Hchk _]).
  apply andb_prop in Hchk as [Hchk Cndhi]. apply andb_prop in Hchk as [_ Cndlo]. apply Z.leb_le in Cndlo, Cndhi.
  assert (Hne : a_pri a <> []) by (intros Hn; rewrite Hn in Hlen; discriminate).
  pose proof (po_inv _ _ _ _ (ha_pri _ _ _ _ (HHA Hon) Hne)) as HI. unfold INV_A in HI.
  pose proof (sden_0 _ _ _ _ (dn_sden _ _ _ _ _ _ _ _ _ Hd)) as (_ & _ & _ & _ & _ & _ & HF0 & _).
  pose proof (irange_sound E (s_facts S) (rget (s_regs S) (rk 12)) HF0) as Rnd. fold (uE E (rget (s_regs S) (rk 12))) in Rnd.
  set (c := cls_of (uE E (rget (s_regs S) (rk 12)))) in *.
  assert (Hcr : 1 <= c <= 30) by (apply cls_of_rng; clear - Rnd Cndlo Cndhi; lia).
  destruct (cls_jb (pden E a) mem0 HI c (rng_in_cls c Hcr)) as (K0 & _).
  destruct (Z.eq_dec (z_j (pden E a) c) 0) as [Hz|Hnz].
  - exact (npopg_node_first cfg LIMIT model0 Hwx Hsegb Hoff Hrespos Hreswf S M a S' M' a' H mem0 E ms model T Hd Haw HHA Hz Hk).
  - exact (npopg_node_pop cfg LIMIT model0 Hwx S M a S' M' a' H mem0 E ms model T Hd Haw HHA ltac:(change (1 <= z_j (pden E a) c); clear - K0 Hnz; lia) Hk).
Qed.

#[using="Hwx Hsegb Hoff Hrespos Hreswf"] Theorem npopg_node : forall S M a S' M' a', apost_npopg LIMIT S M a = Some (S', M', a') ->
  forall mem0 E ms model T, DEN ASEGS LIMIT model0 mem0 E S M ms model -> awf (s_next S) a = true -> HA E M a mem0 ->
  (forall E' mem0' ms' model', agree (s_next S) E E' -> frz_same E M mem0 mem0' -> DEN ASEGS LIMIT model0 mem0' E' S' M' ms' model' ->
     HA E' M' a' mem0' -> realizes_cfg ASEGS cfg (mkCfg ms' model') T) ->
  realizes_cfg ASEGS cfg (mkCfg ms model) T.
Proof. LiaFast.lf_pins (fun (Hwx Hsegb Hoff Hrespos Hreswf : LiaFast.U) => LiaFast.u0).
  intros S M a S' M' a' H mem0 E ms model T Hd Haw HHA Hk. unfold apost_npopg in H.
  exact (npopg_node0 _ M a S' M' a' H mem0 E ms model T (den_sp_fact ASEGS LIMIT model0 mem0 E S M ms model Hd) Haw HHA Hk).
Qed.
End NPopGAll.
(* [comment removed for export] *)
End AcNPopGAll.


Module AcBatchOut.
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.fast_float.from_chars.images Require Import AsanUbsan.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec AsanAcct FxLin FxCore FxSound FxMem FxFacts FxStep FxSubst FxEnt.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require Import AxMng.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXC Require Import FxBacking FxChDen FxChLib FxChSep FxChFix.
From OSSVerify.Proofs.fast_float.from_chars.lib.AAXB Require Import AXG_put AXG_np AXG_nf1 AXG_npf.
From OSSVerify.Proofs.fast_float.from_chars.lib.AACB Require AcAst AcDenW AcPri AcHA.
From OSSVerify.Proofs.fast_float.from_chars.lib.AACB Require AcPri.
From OSSVerify.Proofs.fast_float.from_chars.lib.AACB Require AcMALlib AcDepDen.
From OSSVerify.Proofs.fast_float.from_chars.lib.AACB Require AcPriSepOk.
From OSSVerify.Proofs.fast_float.from_chars.lib.AACB Require AcPriSepOk.
From OSSVerify.Proofs.fast_float.from_chars.lib.AACB Require AcConvA.
From OSSVerify.Proofs.fast_float.from_chars.lib.AACB Require AcNEnq.
Import OSSVerify.Proofs.fast_float.from_chars.lib.AACB.AcAst OSSVerify.Proofs.fast_float.from_chars.lib.AACB.AcDenW OSSVerify.Proofs.fast_float.from_chars.lib.AACB.AcPri OSSVerify.Proofs.fast_float.from_chars.lib.AACB.AcHA OSSVerify.Proofs.fast_float.from_chars.lib.AACB.AcPri.AcDepSep OSSVerify.Proofs.fast_float.from_chars.lib.AACB.AcMALlib OSSVerify.Proofs.fast_float.from_chars.lib.AACB.AcDepDen OSSVerify.Proofs.fast_float.from_chars.lib.AACB.AcPriSepOk.AcPriSep OSSVerify.Proofs.fast_float.from_chars.lib.AACB.AcPriSepOk OSSVerify.Proofs.fast_float.from_chars.lib.AACB.AcConvA.AcPriDen OSSVerify.Proofs.fast_float.from_chars.lib.AACB.AcNEnq.
Import ListNotations.
Local Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
Lemma lin_off_diff : forall E x b d, lin_off x b = Some d -> uE E b <= uE E x -> d = uE E x - uE E b.
Proof.
  intros E x b d H Hle. destruct (lin_off_sound E x b d H) as [Hv Hd]. rewrite lden_lsub in Hv.
  apply (f_equal bv_unsigned) in Hv. rewrite bv_sub_unsigned, u_Z_to_bv in Hv. unfold bv_wrap, bv_modulus in Hv.
  change (2 ^ Z.of_N 64) with two64 in Hv. fold (uE E x) in Hv. fold (uE E b) in Hv.
  pose proof (uE_range E x) as Bx. pose proof (uE_range E b) as Bb.
  rewrite (Z.mod_small (uE E x - uE E b)) in Hv by lia. rewrite (Z.mod_small d) in Hv by exact Hd. lia.
Qed.

Section BatchSem.
Variable E : valu.
Variable fs : list fact.
Hypothesis HF : Forall (fact_ok E) fs.
Variable a : ast.
Variable m0 : word -> option byte.
Hypothesis HI : INV_A E a m0.
Hypothesis Hsepc : forall p, In p (a_live a) -> uE E (fst p) + uE E (snd p) <= two64 /\
  (forall x, uE E (fst p) <= x < uE E (fst p) + uE E (snd p) -> ~ FPmax (pden E a) x).
Hypothesis Hext : forall p, In p (a_ext a) -> ext_sem (pden E a) (uE E (fst p)) (uE E (snd p)).
Local Abbreviation pz := (pden E a).

(* [comment removed for export] *)
Definition BAT (q : Z) : Z := z_sb pz + 103079215104 + 8192 * q.

#[using="m0 HI"] Lemma shadow_below_bat : forall R c q w, In c CLS -> live_shadow E a R c -> 0 <= q ->
  uE E (rg_base R) <= w < uE E (rg_base R) + rsz E R -> ~ (BAT q <= w < BAT q + 8192).
Proof. LiaFast.lf_pins (fun (m0 HI : LiaFast.U) => LiaFast.u0).
  intros R c q w Hc (L1 & L2 & L3) Hq Hw. pose proof (ps_geo E a m0 HI) as G. pose proof (in_cls_rng c Hc) as Hcr. unfold BAT. lia.
Qed.

#[using="HF m0 HI Hsepc Hext"] Lemma batch_sep_at_sound : forall ql R, 0 <= rsz E R -> uE E (rg_base R) + rsz E R <= two64 ->
  sep_route E fs a R -> batch_sep_at fs a ql R = true -> 0 <= uE E ql < 32 ->
  (forall b z, ext_sem pz b z -> b + z <= BAT (uE E ql) \/ BAT (uE E ql) + 8192 <= b) ->
  forall w, uE E (rg_base R) <= w < uE E (rg_base R) + rsz E R -> ~ (BAT (uE E ql) <= w < BAT (uE E ql) + 8192).
Proof. LiaFast.lf_pins (fun (HF m0 HI Hsepc Hext : LiaFast.U) => LiaFast.u0).
  intros ql R Hz Hr Hrt Hbs Hq Hx w Hw. pose proof (ps_geo E a m0 HI) as G.
  assert (HinP : BAT (uE E ql) <= w < BAT (uE E ql) + 8192 -> FPmax pz w).
  { intros Hb. left. unfold BAT in Hb. unfold PG_SIZE. lia. }
  destruct Hrt as [Hap|[(c & Hc & Hl)|Hxi]].
  - intros Hb. exact (Hap w Hw (HinP Hb)).
  - pose proof (in_cls_rng c Hc) as Hcr.
    destruct (live_in_sound_c E fs HF a m0 HI R c Hc Hz Hl) as [Hu|Hs]; [|exact (shadow_below_bat R c _ w Hc Hs (proj1 Hq) Hw)].
    destruct (Z.eq_dec c 24) as [->|Hne].
    2:{ destruct Hu as (U1 & U2 & U3). unfold BAT. lia. }
    unfold batch_sep_at in Hbs. unfold QCLS in Hbs. rewrite Hl in Hbs.
    destruct (sep_cached a R) eqn:Hsc.
    { intros Hb. exact (sep_cached_sound E a Hsepc R Hz Hr Hsc w Hw (HinP Hb)). }
    cbv zeta in Hbs.
    pose proof (irange_sound E fs ql HF) as Rq. fold (uE E ql) in Rq.
    pose proof (irange_sound E fs (rg_size R) HF) as Rs. fold (rsz E R) in Rs.
    pose proof (u_lrb E a m0 HI 24 ltac:(lia)) as Erb. destruct Hu as (U1 & U2 & U3).
    destruct (lin_off (rg_base R) (l_rb a 24)) as [d|] eqn:Hd.
    + pose proof (lin_off_diff E _ _ d Hd ltac:(rewrite Erb; lia)) as Ed. rewrite Erb in Ed.
      assert (Hc2 : d + snd (irange fs (rg_size R)) <= 8192 * fst (irange fs ql) \/ 8192 * (snd (irange fs ql) + 1) <= d).
      { destruct (Z.leb (d + snd (irange fs (rg_size R))) (8192 * fst (irange fs ql))) eqn:Q1; [left; apply Z.leb_le; exact Q1 | right; apply Z.leb_le; exact Hbs]. }
      unfold BAT. lia.
    + destruct (lin_off (ladd (rg_base R) (rg_size R)) (l_rb a 24)) as [e|] eqn:He.
      * assert (Eend : uE E (ladd (rg_base R) (rg_size R)) = uE E (rg_base R) + rsz E R).
        { unfold uE, rsz. rewrite lden_ladd, bv_add_unsigned. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 64) with two64.
          apply Z.mod_small. pose proof (uE_range E (rg_base R)) as B1. unfold uE, rsz in *. unfold two64 in *. lia. }
        pose proof (lin_off_diff E _ _ e He ltac:(rewrite Erb, Eend; lia)) as Ee. rewrite Erb, Eend in Ee.
        assert (Hc2 : e <= 8192 * fst (irange fs ql) \/ 8192 * (snd (irange fs ql) + 1) <= e - snd (irange fs (rg_size R))).
        { destruct (Z.leb e (8192 * fst (irange fs ql))) eqn:Q1; [left; apply Z.leb_le; exact Q1 | right; apply Z.leb_le; exact Hbs]. }
        unfold BAT. lia.
      * exact (shadow_below_bat R 24 _ w Hc (live_in_shadow_c E fs HF a m0 HI R 24 Hc Hz Hd He Hl) (proj1 Hq) Hw).
  - destruct (ext_in_route E fs HF a m0 HI Hext R Hz Hxi) as (p & Hp & Hsem & [[L1 L2]|(c & Hc & Hs)]);
      [|exact (shadow_below_bat R c _ w Hc Hs (proj1 Hq) Hw)].
    destruct (Hx _ _ Hsem) as [X|X]; lia.
Qed.
End BatchSem.

Section BatchOut.
Variable LIMIT : Z.
Variable model0 : Model.
Variable mem0 : word -> option byte.

(* [comment removed for export] *)
#[using="Type"] Lemma batch_outside_at : forall E S M ms model a m0 jP jT ql, DEN ASEGS LIMIT model0 mem0 E S M ms model -> PRI_on E M a m0 ->
  find_grant (sm_maps M) (p_pg a) PG_SIZE = Some jP -> find_grant (sm_maps M) (p_tg a) TG_SIZE = Some jT ->
  forallb_l (fun R => pri_sep_c (s_facts S) (sm_maps M) ASEGSR jP jT (sm_sp M) a R &&& batch_sep_at (s_facts S) a ql R) (s_rgs S) = true ->
  0 <= uE E ql < 32 ->
  (forall b z, ext_sem (pden E a) b z ->
     b + z <= z_sb (pden E a) + 103079215104 + 8192 * uE E ql \/ z_sb (pden E a) + 103079215104 + 8192 * uE E ql + 8192 <= b) ->
  forall x, 0 <= x < two64 -> z_sb (pden E a) + 103079215104 + 8192 * uE E ql <= x < z_sb (pden E a) + 103079215104 + 8192 * uE E ql + 8192 ->
  outside E (s_rgs S) (Z_to_bv 64 x).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros E S M ms model a m0 jP jT ql Hd [Hi _ _ _ _ Hsep Hxt _] HjP HjT Hck Hq Hx x Hx64 Hb.
  destruct (find_grant_sound _ _ _ _ HjP) as (kp & Hp). destruct (find_grant_sound _ _ _ _ HjT) as (kt & Ht).
  pose proof (sden_0 _ _ _ _ (dn_sden _ _ _ _ _ _ _ _ _ Hd)) as (_ & _ & _ & _ & _ & _ & HF0 & _).
  rewrite forallb_l_eq in Hck. rewrite forallb_forall in Hck.
  pose proof (rgs_sz_ok LIMIT model0 mem0 E S M ms model Hd) as Hsz. rewrite Forall_forall in Hsz.
  unfold outside. rewrite Forall_forall. intros R HR. destruct (Hsz R HR) as [Hz Hr]. rewrite u_small64 by exact Hx64. fold (uE E (rg_base R)).
  destruct (Z_lt_le_dec x (uE E (rg_base R))) as [H1|H1]; [left; exact H1|].
  destruct (Z_lt_le_dec x (uE E (rg_base R) + rsz E R)) as [H2|H2]; [|right; exact H2]. exfalso.
  specialize (Hck R HR). destruct (pri_sep_c (s_facts S) (sm_maps M) ASEGSR jP jT (sm_sp M) a R) eqn:Hps; [|discriminate].
  assert (Hrt : sep_route E (s_facts S) a R).
  { exact (pri_sep_c_route E (s_facts S) (sm_maps M) model (sm_sp M) _ HF0 (dn_maps _ _ _ _ _ _ _ _ _ Hd) (dn_pd _ _ _ _ _ _ _ _ _ Hd)
           (dn_gsh _ _ _ _ _ _ _ _ _ Hd) (dn_gtop _ _ _ _ _ _ _ _ _ Hd) (dn_sp _ _ _ _ _ _ _ _ _ Hd) (proj2 (dn_spok _ _ _ _ _ _ _ _ _ Hd))
           (proj1 (dn_spok _ _ _ _ _ _ _ _ _ Hd)) (dn_mres _ _ _ _ _ _ _ _ _ Hd) ASEGSR (dn_res _ _ _ _ _ _ _ _ _ Hd) gq_res a m0 Hi jP jT _ _ Hp eq_refl eq_refl Ht eq_refl eq_refl Hsep
           R Hz Hr Hps). }
  exact (batch_sep_at_sound E (s_facts S) HF0 a m0 Hi Hsep Hxt ql R Hz Hr Hrt Hck Hq Hx x ltac:(lia) Hb).
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma batch_outside : forall E S M ms model a m0 jP jT, DEN ASEGS LIMIT model0 mem0 E S M ms model -> PRI_on E M a m0 ->
  find_grant (sm_maps M) (p_pg a) PG_SIZE = Some jP -> find_grant (sm_maps M) (p_tg a) TG_SIZE = Some jT ->
  forallb_l (fun R => pri_sep_c (s_facts S) (sm_maps M) ASEGSR jP jT (sm_sp M) a R &&& batch_sep (s_facts S) a R) (s_rgs S) = true ->
  1 <= z_qn (pden E a) ->
  forall x, 0 <= x < two64 -> z_sb (pden E a) + 103079215104 + 8192 * z_qj (pden E a) <= x < z_sb (pden E a) + 103079215104 + 8192 * z_qj (pden E a) + 8192 ->
  outside E (s_rgs S) (Z_to_bv 64 x).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros E S M ms model a m0 jP jT Hd HP HjP HjT Hck Hqn x Hx Hb.
  assert (Eq : uE E (p_qj a) = z_qj (pden E a)) by (symmetry; apply zn_pden).
  pose proof HP as [Hi _ _ _ _ _ _].
  assert (Hqj : 0 <= z_qj (pden E a) < 32).
  { destruct Hi as [_ _ _ _ _ _ _ _ _ [(_ & _ & [(Q0 & _)|(_ & Q1 & _)]) _] _ _]; [lia | exact Q1]. }
  refine (batch_outside_at E S M ms model a m0 jP jT (p_qj a) Hd HP HjP HjT Hck ltac:(rewrite Eq; exact Hqj) _ x Hx ltac:(rewrite Eq; exact Hb)).
  intros b z (_ & Hs & _). rewrite Eq. exact (Hs Hqn).
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma batch_outside_gl : forall E S M ms model a m0 jP jT, DEN ASEGS LIMIT model0 mem0 E S M ms model -> PRI_on E M a m0 ->
  find_grant (sm_maps M) (p_pg a) PG_SIZE = Some jP -> find_grant (sm_maps M) (p_tg a) TG_SIZE = Some jT ->
  forallb_l (fun R => pri_sep_c (s_facts S) (sm_maps M) ASEGSR jP jT (sm_sp M) a R &&& batch_sep_at (s_facts S) a (p_gl a) R) (s_rgs S) = true ->
  1 <= z_gn (pden E a) ->
  forall x, 0 <= x < two64 -> z_sb (pden E a) + 103079215104 + 8192 * z_gl (pden E a) <= x < z_sb (pden E a) + 103079215104 + 8192 * z_gl (pden E a) + 8192 ->
  outside E (s_rgs S) (Z_to_bv 64 x).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros E S M ms model a m0 jP jT Hd HP HjP HjT Hck Hgn x Hx Hb.
  assert (Eq : uE E (p_gl a) = z_gl (pden E a)) by (symmetry; apply zn_pden).
  pose proof HP as [Hi _ _ _ _ _ _].
  assert (Hgl : 0 <= z_gl (pden E a) < 32).
  { destruct Hi as [_ _ _ _ _ _ _ _ _ _ [(_ & _ & _ & _ & _ & _ & _ & _ & [(G0 & _)|(_ & G1 & _)]) _] _]; [lia | exact G1]. }
  refine (batch_outside_at E S M ms model a m0 jP jT (p_gl a) Hd HP HjP HjT Hck ltac:(rewrite Eq; exact Hgl) _ x Hx ltac:(rewrite Eq; exact Hb)).
  intros b z (_ & _ & Hs). rewrite Eq. exact (Hs Hgn).
Qed.
End BatchOut.
(* [comment removed for export] *)
End AcBatchOut.

Module AcNEnqAll.
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.fast_float.from_chars.images Require Import AsanUbsan.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec ShapeSet RealizesCfg AsanAcct PlacementCount AllocNodesCfg.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxLin FxCore FxSound FxMem FxFacts FxStep.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxLoop.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxSubst FxEnt FxPlan FxFrame FxDrv FxCall.
Import OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxLin OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxCore OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxSound OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxMem OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxFacts OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxStep OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxLoop.FxExplore OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxSubst OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxEnt OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxPlan OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxFrame OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxDrv OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxCall.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require Import AxMng.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXC Require Import FxBacking FxChDen FxChLib FxChSep FxChFix FxChMain.
From OSSVerify.Proofs.fast_float.from_chars.lib.AAXB Require Import AXG_put AXG_np AXG_nf1 AXG_npf.
From OSSVerify.Proofs.fast_float.from_chars.lib.AACB Require AcPri.
From OSSVerify.Proofs.fast_float.from_chars.lib.AACB Require AcAst AcHA AcFacts AcMALlib AcPri AcPriStep AcNPop AcNEnq.
From OSSVerify.Proofs.fast_float.from_chars.lib.AACB Require NqStepZ AcNEnqLib.
From OSSVerify.Proofs.fast_float.from_chars.lib.AACB Require AcNEnqF.
From OSSVerify.Proofs.fast_float.from_chars.lib.AACB Require AcNEnqF.
From OSSVerify.Proofs.fast_float.from_chars.lib.AACB Require AcNEnqF.
From OSSVerify.Proofs.fast_float.from_chars.lib.AACB Require AcNEnqF.
Import OSSVerify.Proofs.fast_float.from_chars.lib.AACB.AcPri.AcDepSep OSSVerify.Proofs.fast_float.from_chars.lib.AACB.AcAst OSSVerify.Proofs.fast_float.from_chars.lib.AACB.AcHA OSSVerify.Proofs.fast_float.from_chars.lib.AACB.AcFacts OSSVerify.Proofs.fast_float.from_chars.lib.AACB.AcMALlib OSSVerify.Proofs.fast_float.from_chars.lib.AACB.AcPri OSSVerify.Proofs.fast_float.from_chars.lib.AACB.AcPriStep OSSVerify.Proofs.fast_float.from_chars.lib.AACB.AcNPop OSSVerify.Proofs.fast_float.from_chars.lib.AACB.AcNEnq OSSVerify.Proofs.fast_float.from_chars.lib.AACB.AcFam2Ok.AcBatchOut OSSVerify.Proofs.fast_float.from_chars.lib.AACB.NqStepZ OSSVerify.Proofs.fast_float.from_chars.lib.AACB.AcNEnqLib OSSVerify.Proofs.fast_float.from_chars.lib.AACB.AcNEnqF.AcNEnqN OSSVerify.Proofs.fast_float.from_chars.lib.AACB.AcNEnqF.AcNEnqD OSSVerify.Proofs.fast_float.from_chars.lib.AACB.AcNEnqF.AcNEnqD2 OSSVerify.Proofs.fast_float.from_chars.lib.AACB.AcNEnqF.
Import ListNotations.
Local Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Section NEnqAll.
Variable cfg : SpuriousCfg.
Variable LIMIT : Z.
Variable model0 : Model.
Hypothesis Hwx : wx_segs_nowrap ASEGS.
Hypothesis Hsegb : segs_below_b ASEGS 0x800000000000 = true.
Hypothesis Hoff : sc_alloc cfg = false.
Hypothesis Hrespos : Forall (fun p => 0 < bv_unsigned (snd p)) (segments_reserved ASEGS).
Hypothesis Hreswf : ivs_wf (segments_reserved ASEGS).

#[using="Hwx Hsegb Hoff Hrespos Hreswf"] Theorem nenq_node0 : forall S M a S' M' a', apost_nenq0 LIMIT S M a = Some (S', M', a') ->
  forall mem0 E ms model T, DEN ASEGS LIMIT model0 mem0 E S M ms model -> awf (s_next S) a = true -> HA E M a mem0 ->
  (forall E' mem0' ms' model', agree (s_next S) E E' -> frz_same E M mem0 mem0' -> DEN ASEGS LIMIT model0 mem0' E' S' M' ms' model' ->
     HA E' M' a' mem0' -> realizes_cfg ASEGS cfg (mkCfg ms' model') T) ->
  realizes_cfg ASEGS cfg (mkCfg ms model) T.
Proof. LiaFast.lf_pins (fun (Hwx Hsegb Hoff Hrespos Hreswf : LiaFast.U) => LiaFast.u0).
  intros S M a S' M' a' H mem0 E ms model T Hd Haw HHA Hk.
  assert (BO := fun mem0 E S M ms model a m0 jP jT => batch_outside LIMIT model0 mem0 E S M ms model a m0 jP jT).
  assert (GBO := fun mem0 E S M ms model a m0 jP jT => batch_outside_gl LIMIT model0 mem0 E S M ms model a m0 jP jT).
  destruct (nq_room S a) eqn:Hroom; destruct (nq_nodrain S a) eqn:Hnd.
  - exact (nenq_node_room cfg LIMIT model0 Hwx BO S M a S' M' a' H Hroom Hnd mem0 E ms model T Hd Haw HHA Hk).
  - exact (nenq_node_room_drain cfg LIMIT model0 Hwx BO GBO S M a S' M' a' H Hroom Hnd mem0 E ms model T Hd Haw HHA Hk).
  - pose proof H as H0. unfold apost_nenq0 in H0. cbv zeta in H0. apply obool_some in H0 as (Hon & _).
    apply andb_prop in Hon as [Hon _]. apply andb_prop in Hon as [Hon _]. apply andb_prop in Hon as [Hon _]. apply andb_prop in Hon as [Hon Hlen].
    apply Nat.eqb_eq in Hlen.
    assert (Hne : a_pri a <> []) by (intros Hn; rewrite Hn in Hlen; discriminate).
    pose proof (po_inv _ _ _ _ (ha_pri _ _ _ _ (HHA Hon) Hne)) as HI. unfold INV_A in HI.
    destruct (cls_jb (pden E a) mem0 HI 24 in_cls_24) as (K0 & _).
    destruct (Z.eq_dec (z_j (pden E a) 24) 0) as [Hz|Hnz].
    + exact (nenq_node_first cfg LIMIT model0 Hwx Hsegb Hoff Hrespos Hreswf S M a S' M' a' H Hroom Hnd mem0 E ms model T Hd Haw HHA Hz Hk).
    + exact (nenq_node_new cfg LIMIT model0 Hwx S M a S' M' a' H Hroom Hnd mem0 E ms model T Hd Haw HHA ltac:(clear - K0 Hnz; lia) Hk).
  - exact (nenq_node_new_drain cfg LIMIT model0 Hwx GBO S M a S' M' a' H Hroom Hnd mem0 E ms model T Hd Haw HHA Hk).
Qed.

#[using="Hwx Hsegb Hoff Hrespos Hreswf"] Theorem nenq_node : forall S M a S' M' a', apost_nenq LIMIT S M a = Some (S', M', a') ->
  forall mem0 E ms model T, DEN ASEGS LIMIT model0 mem0 E S M ms model -> awf (s_next S) a = true -> HA E M a mem0 ->
  (forall E' mem0' ms' model', agree (s_next S) E E' -> frz_same E M mem0 mem0' -> DEN ASEGS LIMIT model0 mem0' E' S' M' ms' model' ->
     HA E' M' a' mem0' -> realizes_cfg ASEGS cfg (mkCfg ms' model') T) ->
  realizes_cfg ASEGS cfg (mkCfg ms model) T.
Proof. LiaFast.lf_pins (fun (Hwx Hsegb Hoff Hrespos Hreswf : LiaFast.U) => LiaFast.u0).
  intros S M a S' M' a' H mem0 E ms model T Hd Haw HHA Hk. unfold apost_nenq in H.
  exact (nenq_node0 _ M a S' M' a' H mem0 E ms model T (den_sp_fact ASEGS LIMIT model0 mem0 E S M ms model Hd) Haw HHA Hk).
Qed.
End NEnqAll.
(* [comment removed for export] *)
End AcNEnqAll.


Module AcExtN.
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.fast_float.from_chars.images Require Import AsanUbsan.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec ShapeSet RealizesCfg FxLin FxCore FxSound FxMem FxFacts FxSubst FxEnt FxDrv.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXC Require Import FxBacking FxChDen FxChLib FxChMain.
From OSSVerify.Proofs.fast_float.from_chars.lib.AACB Require AcPri.
From OSSVerify.Proofs.fast_float.from_chars.lib.AACB Require AcAst.
From OSSVerify.Proofs.fast_float.from_chars.lib.AACB Require AcHA.
From OSSVerify.Proofs.fast_float.from_chars.lib.AACB Require AcHA AcPri.
From OSSVerify.Proofs.fast_float.from_chars.lib.AACB Require AcPriSepOk.
From OSSVerify.Proofs.fast_float.from_chars.lib.AACB Require AcPriSepOk AcPriStep AcMALp AcMALlib AcNPop.
From OSSVerify.Proofs.fast_float.from_chars.lib.AACB Require AcFam2.
Import OSSVerify.Proofs.fast_float.from_chars.lib.AACB.AcPri.AcDepSep OSSVerify.Proofs.fast_float.from_chars.lib.AACB.AcAst OSSVerify.Proofs.fast_float.from_chars.lib.AACB.AcHA.AcLv OSSVerify.Proofs.fast_float.from_chars.lib.AACB.AcHA OSSVerify.Proofs.fast_float.from_chars.lib.AACB.AcPri OSSVerify.Proofs.fast_float.from_chars.lib.AACB.AcPriSepOk.AcPriSep OSSVerify.Proofs.fast_float.from_chars.lib.AACB.AcPriSepOk OSSVerify.Proofs.fast_float.from_chars.lib.AACB.AcPriStep OSSVerify.Proofs.fast_float.from_chars.lib.AACB.AcMALp OSSVerify.Proofs.fast_float.from_chars.lib.AACB.AcMALlib OSSVerify.Proofs.fast_float.from_chars.lib.AACB.AcNPop OSSVerify.Proofs.fast_float.from_chars.lib.AACB.AcFam2.AcExt.
Import ListNotations.
Local Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
Lemma HA_on_ext : forall E M a a' m0, HA_on E M a m0 ->
  a_on a' = a_on a -> a_fcts a' = a_fcts a -> a_own a' = a_own a -> a_dep a' = a_dep a -> a_nl a' = a_nl a -> a_live a' = a_live a -> a_pri a' = a_pri a ->
  (a_pri a <> [] -> forall p, In p (a_ext a') -> ext_sem (pden E a) (uE E (fst p)) (uE E (snd p))) ->
  (a_pri a <> [] -> lv_inv E a m0 -> lv_inv E a' m0) ->      (* [comment removed for export] *)
  HA_on E M a' m0.
Proof.
  intros E M a a' m0 [Hdep Hown Hownx Hhi HgD HgB Hpri] Eon Efc Eow Edp Enl Elv Epr Hx Hlvx.
  assert (Epd : pden E a' = pden E a) by (unfold pden; rewrite Epr; reflexivity).
  constructor.
  - unfold dD1, dB1. rewrite Edp, Enl. exact Hdep.
  - unfold dD1, dB1. rewrite Edp. exact Hown.
  - rewrite Eow, Hownx. unfold aown_of. rewrite Edp, Epr. unfold pri_own, cls_own, l_cb, l_rip, l_rb, l_fa, l_shu, l_shf, p_ca, p_sb, p_sh, p_z, p_nth. rewrite Epr. reflexivity.
  - unfold dD1, dB1. rewrite Edp. exact Hhi.
  - rewrite Edp. exact HgD.
  - rewrite Edp. exact HgB.
  - intros Hne. rewrite Epr in Hne. destruct (Hpri Hne) as [Hi Ho Hp Ht Hz Hs Hxt Hlv Hsd]. constructor; [| | | | | | |exact (Hlvx Hne Hlv)|].
    + unfold INV_A. rewrite Epd. exact Hi.
    + intros x Hx0 Hf. unfold pri_foot in Hf. rewrite Epd in Hf. exact (Ho x Hx0 Hf).
    + unfold p_pg, p_nth. rewrite Epr. exact Hp.
    + unfold p_tg, p_nth. rewrite Epr. exact Ht.
    + intros x Hx0. apply Hz. unfold pri_shadow in *. rewrite Epd in Hx0. exact Hx0.
    + intros p Hp'. rewrite Elv in Hp'. rewrite Epd. exact (Hs p Hp').
    + intros p Hp'. rewrite Epd. exact (Hx Hne p Hp').
    + intros p Hp' x Hx0. rewrite Elv in Hp'. unfold dD1, dB1. rewrite Edp. exact (Hsd p Hp' x Hx0).
Qed.

Section ExtNodes.
Variable cfg : SpuriousCfg.
Variable LIMIT : Z.
Variable model0 : Model.

#[using="Type"] Theorem extdrop_node : forall i S M a S' M' a', apost_extdrop i S M a = Some (S', M', a') ->
  forall mem0 E ms model T, DEN ASEGS LIMIT model0 mem0 E S M ms model -> awf (s_next S) a = true -> HA E M a mem0 ->
  (forall E' mem0' ms' model', agree (s_next S) E E' -> frz_same E M mem0 mem0' -> DEN ASEGS LIMIT model0 mem0' E' S' M' ms' model' ->
     HA E' M' a' mem0' -> realizes_cfg ASEGS cfg (mkCfg ms' model') T) ->
  realizes_cfg ASEGS cfg (mkCfg ms model) T.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros i S M a S' M' a' H mem0 E ms model T Hd Haw HHA Hk. unfold apost_extdrop in H.
  destruct (a_on a && Nat.ltb i (List.length (a_rgs a)))%bool eqn:Hc; [|discriminate]. injection H as <- <- <-.
  apply (Hk E mem0 ms model); [apply agree_refl | intros p Hp w Hw; reflexivity | exact Hd |].
  intros Hon. change (a_on (ext_drop a i)) with (a_on a) in Hon.
  apply (HA_on_ext E M a (ext_drop a i) mem0 (HHA Hon)); try reflexivity.
  - intros Hne p Hp. exact (po_ext _ _ _ _ (ha_pri _ _ _ _ (HHA Hon) Hne) p (In_ext_drop a i p Hp)).
  - intros _ Hlv. exact (lv_inv_ext_drop E a mem0 i Hlv).
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma ext_sem_sub : forall pz b z b' z', ext_sem pz b z -> b <= b' -> b' + z' <= b + z -> b' mod 8 = 0 -> ext_sem pz b' z'.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros pz b z b' z' ((c & Hc & H1 & H2 & H3) & HB & HG) L1 L2 L3. split; [|split].
  - exists c. split; [exact Hc|]. split; [lia|]. split; [lia | exact L3].
  - intros Hq. destruct (HB Hq) as [X|X]; [left | right]; lia.
  - intros Hg. destruct (HG Hg) as [X|X]; [left | right]; lia.
Qed.
#[using="Type"] Lemma In_set_nth_rg : forall i R l x, In x (set_nth_rg i R l) -> x = R \/ In x l.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros i R l. revert i. induction l as [|y l IH]; intros i x H; [destruct i; destruct H|].
  destruct i as [|i]; cbn [set_nth_rg] in H.
  - destruct H as [<-|H]; [left; reflexivity | right; right; exact H].
  - destruct H as [<-|H]; [right; left; reflexivity|]. destruct (IH i x H) as [->|H']; [left; reflexivity | right; right; exact H'].
Qed.

#[using="Type"] Theorem extsub_node : forall i b z S M a S' M' a', apost_extsub i b z S M a = Some (S', M', a') ->
  forall mem0 E ms model T, DEN ASEGS LIMIT model0 mem0 E S M ms model -> awf (s_next S) a = true -> HA E M a mem0 ->
  (forall E' mem0' ms' model', agree (s_next S) E E' -> frz_same E M mem0 mem0' -> DEN ASEGS LIMIT model0 mem0' E' S' M' ms' model' ->
     HA E' M' a' mem0' -> realizes_cfg ASEGS cfg (mkCfg ms' model') T) ->
  realizes_cfg ASEGS cfg (mkCfg ms model) T.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros i b z S M a S' M' a' H mem0 E ms model T Hd Haw HHA Hk. unfold apost_extsub in H.
  apply obind_some in H as (Re & HRe & H). cbv beta in H. apply obool_some in H as (Hc & H). injection H as <- <- <-.
  apply andb_prop in Hc as [Hc Cmod]. apply andb_prop in Hc as [Hc Cin]. apply andb_prop in Hc as [Hc _]. apply andb_prop in Hc as [Hon _].
  pose proof (sden_0 _ _ _ _ (dn_sden _ _ _ _ _ _ _ _ _ Hd)) as (_ & _ & _ & _ & _ & _ & HF0 & _).
  apply (Hk E mem0 ms model); [apply agree_refl | intros p Hp w Hw; reflexivity | exact Hd |].
  intros _. set (a1 := AST (a_on a) (set_nth_rg i (ext_rg b z) (a_rgs a)) (a_fcts a) (a_own a) (a_dep a) (a_nl a) (a_live a) (a_pri a)).
  (* [comment removed for export] *)
  assert (Hin : a_pri a <> [] -> ext_sem (pden E a) (uE E (rg_base Re)) (uE E (rg_size Re)) /\
                 uE E (rg_base Re) <= uE E b /\ uE E b + uE E z <= uE E (rg_base Re) + uE E (rg_size Re)).
  { intros Hne. pose proof (ha_pri _ _ _ _ (HHA Hon) Hne) as HP0.
    pose proof (po_ext _ _ _ _ HP0 (rg_base Re, rg_size Re) ltac:(unfold a_ext; exact (in_map (fun R => (rg_base R, rg_size R)) _ Re (nth_error_In _ _ HRe)))) as Hx.
    cbn [fst snd] in Hx. pose proof (po_inv _ _ _ _ HP0) as HI. unfold INV_A in HI.
    assert (Hb48 : uE E (rg_base Re) + uE E (rg_size Re) < 2^48).
    { destruct Hx as ((c & Hcin & X1 & X2 & _) & _). pose proof (in_cls_rng c Hcin) as Hcr.
      destruct (cls_jb (pden E a) mem0 HI c Hcin) as (_ & K1 & _). pose proof (iz_pg _ _ HI) as G. unfold PG_SIZE in G. clear - X2 K1 G Hcr. lia. }
    destruct (inside_lin_sound E (s_facts S) HF0 b z (rg_base Re) (rg_size Re) Cin Hb48) as [I1 I2]. split; [exact Hx | split; [exact I1 | exact I2]]. }
  apply (HA_on_ext E M a a1 mem0 (HHA Hon)); try reflexivity.
  - intros Hne p Hp. pose proof (ha_pri _ _ _ _ (HHA Hon) Hne) as HP0.
    unfold a_ext, a1 in Hp. cbn [a_rgs] in Hp. apply in_map_iff in Hp as (R0 & <- & HR0). cbn [fst snd].
    destruct (In_set_nth_rg _ _ _ _ HR0) as [->|HR1].
    + (* [comment removed for export] *)
      destruct (Hin Hne) as (Hx & I1 & I2). cbn [ext_rg rg_base rg_size].
      pose proof (fact_implied_ok E _ _ HF0 Cmod) as Hm. cbn [fact_ok] in Hm. change (2^3) with 8 in Hm.
      exact (ext_sem_sub _ _ _ _ _ Hx I1 I2 Hm).
    + exact (po_ext _ _ _ _ HP0 (rg_base R0, rg_size R0) ltac:(unfold a_ext; exact (in_map (fun R => (rg_base R, rg_size R)) _ R0 HR1))).
  - (* [comment removed for export] *)
    intros Hne Hlv. destruct (Hin Hne) as (_ & I1 & I2). apply (lv_inv_ext_sub E a a1 mem0); try reflexivity; [|exact Hlv].
    unfold e_rngs, a_ext, a1. cbn [a_rgs]. clear - HRe I1 I2. revert i HRe. induction (a_rgs a) as [|R0 l IH]; intros i HRe; [destruct i; discriminate|].
    destruct i as [|i]; cbn [nth_error set_nth_rg List.map] in *.
    + injection HRe as ->. constructor; [|apply Forall2_same; intros p x X; exact X].
      intros x Hx. unfold in_rg in *. cbn [fst snd ext_rg rg_base rg_size] in *. lia.
    + constructor; [intros x X; exact X | exact (IH i HRe)].
Qed.

#[using="Type"] Theorem exthull_node : forall i j1 j2 S M a S' M' a', apost_exthull i j1 j2 S M a = Some (S', M', a') ->
  forall mem0 E ms model T, DEN ASEGS LIMIT model0 mem0 E S M ms model -> awf (s_next S) a = true -> HA E M a mem0 ->
  (forall E' mem0' ms' model', agree (s_next S) E E' -> frz_same E M mem0 mem0' -> DEN ASEGS LIMIT model0 mem0' E' S' M' ms' model' ->
     HA E' M' a' mem0' -> realizes_cfg ASEGS cfg (mkCfg ms' model') T) ->
  realizes_cfg ASEGS cfg (mkCfg ms model) T.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros i j1 j2 S M a S' M' a' H. unfold apost_exthull in H.
  apply obind_some in H as (R1 & _ & H). cbv beta in H. apply obind_some in H as (R2 & _ & H). cbv beta in H.
  exact (extsub_node i _ _ S M a S' M' a' H).
Qed.
End ExtNodes.
(* [comment removed for export] *)
End AcExtN.


Module AcFrameLive.
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.fast_float.from_chars.images Require Import AsanUbsan.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec ShapeSet RealizesCfg FxLin FxCore FxSound FxMem FxFacts FxStep FxSubst FxEnt FxDrv.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require Import AxMng.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXC Require Import FxBacking FxChDen FxChLib FxChMain.
From OSSVerify.Proofs.fast_float.from_chars.lib.AAXB Require Import AXG_put AXG_put3 AXG_np AXG_nf1 AXG_npf.
From OSSVerify.Proofs.fast_float.from_chars.lib.AACB Require AcPri.
From OSSVerify.Proofs.fast_float.from_chars.lib.AACB Require AcDepDen.
From OSSVerify.Proofs.fast_float.from_chars.lib.AACB Require AcPriHA.
From OSSVerify.Proofs.fast_float.from_chars.lib.AACB Require AcAst.
From OSSVerify.Proofs.fast_float.from_chars.lib.AACB Require AcHA.
From OSSVerify.Proofs.fast_float.from_chars.lib.AACB Require AcHA AcPri.
From OSSVerify.Proofs.fast_float.from_chars.lib.AACB Require AcPriSepOk.
From OSSVerify.Proofs.fast_float.from_chars.lib.AACB Require AcPriSepOk.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXC Require FxChMprot.
From OSSVerify.Proofs.fast_float.from_chars.lib.AACB Require AcMALp AcMALlib AcNPop.
From OSSVerify.Proofs.fast_float.from_chars.lib.AACB Require AcFam2.
From OSSVerify.Proofs.fast_float.from_chars.lib.AACB Require AcConvA.
From OSSVerify.Proofs.fast_float.from_chars.lib.AACB Require AcDenW AcPriStep AcUnwApp.
Import OSSVerify.Proofs.fast_float.from_chars.lib.AACB.AcPri.AcDepSep OSSVerify.Proofs.fast_float.from_chars.lib.AACB.AcDepDen OSSVerify.Proofs.fast_float.from_chars.lib.AACB.AcPriHA.AcPriGrant OSSVerify.Proofs.fast_float.from_chars.lib.AACB.AcAst OSSVerify.Proofs.fast_float.from_chars.lib.AACB.AcHA.AcLv OSSVerify.Proofs.fast_float.from_chars.lib.AACB.AcHA OSSVerify.Proofs.fast_float.from_chars.lib.AACB.AcPri OSSVerify.Proofs.fast_float.from_chars.lib.AACB.AcPriSepOk.AcPriSep OSSVerify.Proofs.fast_float.from_chars.lib.AACB.AcPriSepOk OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChMprot.AcAddOwn OSSVerify.Proofs.fast_float.from_chars.lib.AACB.AcMALp OSSVerify.Proofs.fast_float.from_chars.lib.AACB.AcMALlib OSSVerify.Proofs.fast_float.from_chars.lib.AACB.AcNPop OSSVerify.Proofs.fast_float.from_chars.lib.AACB.AcFam2.AcExt OSSVerify.Proofs.fast_float.from_chars.lib.AACB.AcConvA.AcPriDen OSSVerify.Proofs.fast_float.from_chars.lib.AACB.AcDenW OSSVerify.Proofs.fast_float.from_chars.lib.AACB.AcPriStep OSSVerify.Proofs.fast_float.from_chars.lib.AACB.AcUnwApp.
Import ListNotations.
Local Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
Definition live_u (pz : list Z) (x : Z) : Prop :=
  exists c, In c CLS /\ z_sb pz + 4294967296 * c <= x < z_sb pz + 4294967296 * c + sz_tbl c * z_j pz c /\
    (1 <= z_qn pz -> ~ (z_sb pz + 103079215104 + 8192 * z_qj pz <= x < z_sb pz + 103079215104 + 8192 * z_qj pz + 8192)) /\
    (1 <= z_gn pz -> ~ (z_sb pz + 103079215104 + 8192 * z_gl pz <= x < z_sb pz + 103079215104 + 8192 * z_gl pz + 8192)).
Definition live_s (pz : list Z) (x : Z) : Prop :=
  exists c, In c CLS /\ z_sh pz + 536870912 * c <= x < z_sh pz + 536870912 * c + sz_tbl c / 8 * z_j pz c.

Section FrameLive.
Variables (pz : list Z) (m0 m0' : word -> option byte).
Hypothesis HI : INV_Az pz m0.
Hypothesis Hdisj : z_tg pz + 4096 <= z_pg pz \/ z_pg pz + PG_SIZE <= z_tg pz.
Hypothesis HF : forall x, pri_foot_z pz x -> ~ live_u pz x -> ~ live_s pz x -> m0' (wa x) = m0 (wa x).
Hypothesis HN : forall x, live_s pz x -> m0' (wa x) <> None.

Local Ltac nolive G :=
  first [intros (lc & Hlc & L1 & L2 & L3) | intros (lc & Hlc & L1)];
  match goal with Hlc' : In ?c' CLS |- _ => pose proof (in_cls_rng c' Hlc') as Hlr; destruct (cls_jb pz m0 HI c' Hlc') as (K0 & K1 & K2 & _) end.

#[using="m0 HI Hdisj HF HN"] Lemma INV_Az_frame_live : INV_Az pz m0'.
Proof. LiaFast.lf_pins (fun (m0 HI Hdisj HF HN : LiaFast.U) => LiaFast.u0).
  pose proof (az_geo pz m0 HI) as G. unfold PG_SIZE in Hdisj.
  pose proof HI as [Hlen Hsb Hsh Hca Hpg Htg Hnsh Hst Hwc Hq Hgq Hcls].
  assert (B : 0 <= z_ca pz /\ z_ca pz + 4096 <= 2^63 /\ 0 <= z_sb pz /\ z_sb pz + 137438953472 + 4096 <= 2^63) by (unfold PG_SIZE in Hpg; lia).
  (* [comment removed for export] *)
  assert (Fca : forall x, z_ca pz - 128 <= x < z_ca pz + 2592 -> m0' (wa x) = m0 (wa x)).
  { intros x Hx. apply HF; [left; exact Hx | nolive G; clear - Hx L1 G Hdisj Hlr K0 K1; lia | nolive G; clear - Hx L1 G Hlr K0 K2; lia]. }
  assert (Fri : forall x, z_sb pz + 137438953472 <= x < z_sb pz + 137438953472 + 4096 -> m0' (wa x) = m0 (wa x)).
  { intros x Hx. apply HF; [right; left; exact Hx | nolive G; clear - Hx L1 Hlr K0 K1; lia | nolive G; clear - Hx L1 G Hlr K0 K2; lia]. }
  assert (Fgq : forall x, 930696 <= x < 930736 -> m0' (wa x) = m0 (wa x)).
  { intros x Hx. apply HF; [right; right; left; exact Hx | nolive G; clear - Hx L1 G Hlr K0; lia | nolive G; clear - Hx L1 G Hlr K0; lia]. }
  constructor; try assumption.
  - apply (STATS_frame m0); [lia | lia | | exact Hst]. intros x Hx. apply Fca. lia.
  - apply (wr_frame m0); [lia | lia | | exact Hwc]. intros x Hx. apply Fca. lia.
  - destruct Hq as [(Hqb & Rqb & Hq') Hqj]. split; [|exact Hqj]. split; [exact Hqb|]. split.
    { apply (rd_frame m0); [lia | cbn; lia | intros x Hx; cbn in Hx; apply Fca; lia | exact Rqb]. }
    destruct Hq' as [(Q0 & Qb0 & R0)|(Q1 & Q2 & R1 & R1b & R2 & R3 & R4 & W1)]; [left | right].
    + split; [exact Q0|]. split; [exact Qb0|]. apply (rd_frame m0); [lia | cbn; lia | intros x Hx; cbn in Hx; apply Fca; lia | exact R0].
    + assert (Z24 : z_z pz 24 = 262144).
      { destruct (Hcls 24 in_cls_24) as [(J0 & _)|(_ & Z1 & _)]; [specialize (Hqj ltac:(lia)); lia | exact Z1]. }
      assert (HB : forall x, z_sb pz + 103079215104 + 8192 * z_qj pz <= x < z_sb pz + 103079215104 + 8192 * z_qj pz + 8192 -> m0' (wa x) = m0 (wa x)).
      { intros x Hx. apply HF.
        - right. right. right. exists 24. split; [exact in_cls_24|]. left. rewrite Z24. lia.
        - nolive G. apply (L2 ltac:(lia)). exact Hx.
        - nolive G. clear - Hx L1 G Hlr K0 K2 Q2. lia. }
      split; [exact Q1|]. split; [exact Q2|]. split; [|split; [|split; [|split; [|split]]]].
      * apply (rd_frame m0); [lia | cbn; lia | intros x Hx; cbn in Hx; apply Fca; lia | exact R1].
      * apply (rd_frame m0); [lia | cbn; lia | intros x Hx; cbn in Hx; apply Fca; lia | exact R1b].
      * apply (rd_frame m0); [lia | cbn; lia | intros x Hx; cbn in Hx; apply Fca; lia | exact R2].
      * apply (rd_frame m0); [lia | cbn; lia | intros x Hx; cbn in Hx; apply HB; lia | exact R3].
      * apply (rd_frame m0); [lia | cbn; lia | intros x Hx; cbn in Hx; apply HB; lia | exact R4].
      * apply (wr_frame m0); [lia | lia | intros x Hx; apply HB; lia | exact W1].
  - destruct Hgq as [Hg Hgl]. split; [|exact Hgl]. apply (gq_inv_o_frame m0 m0' (z_sb pz) (z_gn pz) (z_gl pz) (z_gb pz) ltac:(lia) ltac:(lia)); [|exact Hg].
    intros x [Hx|(Hg1 & Hx)]; [exact (Fgq x Hx)|].
    assert (Z24 : z_z pz 24 = 262144).
    { destruct (Hcls 24 in_cls_24) as [(J0 & _)|(_ & Z1 & _)]; [specialize (Hgl Hg1); destruct Hg as (_ & _ & _ & _ & _ & _ & _ & _ & [(G0 & _)|(_ & G1 & _)]); lia | exact Z1]. }
    destruct Hg as (_ & _ & _ & _ & _ & _ & _ & _ & [(G0 & _)|(_ & G1 & _)]); [lia|].
    apply HF.
    + right. right. right. exists 24. split; [exact in_cls_24|]. left. rewrite Z24. lia.
    + nolive G. apply (L3 Hg1). lia.
    + nolive G. clear - Hx L1 G Hlr K0 K2 G1. lia.
  - intros c Hc. pose proof (in_cls_rng c Hc) as Hcr. destruct (cls_tbl c Hc) as (Hsz & Hs8 & Hs8r & Hnw & Hnm & Hmc).
    destruct (Hcls c Hc) as [(J0 & Z0 & HV & HSW)|(J1 & Z1 & Jb & HIo & HP)]; [left | right].
    + split; [exact J0|]. split; [exact Z0|]. split.
      * apply (VIRG_C_frame m0); [lia | lia | lia | lia | lia | | exact HV].
        intros x Hx. unfold foot_V in Hx. destruct Hx as [Hx|Hx]; [apply Fca; lia | apply Fri; lia].
      * destruct HSW as [W1 W2]. split.
        -- apply (wr_frame m0); [lia | lia | | exact W1]. intros x Hx. apply HF.
           ++ right. right. right. exists c. split; [exact Hc|]. right. right. left. lia.
           ++ nolive G. clear - Hx L1 G Hlr K0 K1 Hcr. lia.
           ++ nolive G. clear - Hx L1 Hlr K0 K2 Hcr J0. destruct (Z.eq_dec lc c) as [->|Hn]; [rewrite J0 in L1; lia | lia].
        -- apply (wr_frame m0); [lia | lia | | exact W2]. intros x Hx. apply HF.
           ++ right. right. right. exists c. split; [exact Hc|]. right. right. right. lia.
           ++ nolive G. clear - Hx L1 G Hlr K0 K1 Hcr. lia.
           ++ nolive G. clear - Hx L1 Hlr K0 K2 Hcr. lia.
    + split; [exact J1|]. split; [exact Z1|]. split; [exact Jb|]. split.
      * apply (INV_Co_frame m0); [lia | lia | lia | lia | | exact HIo].
        intros x Hx. unfold foot_Co in Hx. destruct Hx as [Hx|[Hx|Hx]]; [apply Fca; lia | apply Fri; lia |].
        apply HF.
        -- right. right. right. exists c. split; [exact Hc|]. right. left. rewrite Z1. lia.
        -- nolive G. clear - Hx L1 Hlr K0 K1 Hcr Hsz Hnw Hnm. lia.
        -- nolive G. clear - Hx L1 G Hlr K0 K2 Hcr Hsz Hnw Hnm. lia.
      * destruct (cls_jb pz m0 HI c Hc) as (Kc0 & Kc1 & Kc2 & _).
        assert (Kp : 0 <= sz_tbl c * z_j pz c) by (clear - Kc0 Hsz; nia). assert (Kp8 : 0 <= sz_tbl c / 8 * z_j pz c) by (clear - Kc0 Hs8r; nia).
        destruct HP as [PA PB PC]. constructor.
        -- intros x Hx. unfold RBX in Hx. rewrite HF; [exact (PA x Hx) | | |].
           ++ right. right. right. exists c. split; [exact Hc|]. left. rewrite Z1. unfold RBX. lia.
           ++ nolive G. clear - Hx L1 Hlr K0 K1 Hcr Kc0 Kc1 Kc2 Kp Kp8. destruct (Z.eq_dec lc c) as [->|Hn]; lia.
           ++ nolive G. clear - Hx L1 G Hlr K0 K2 Hcr Kc0 Kc1 Kc2 Kp Kp8. lia.
        -- intros x Hx. unfold SHX in Hx. rewrite HF; [exact (PB x Hx) | | |].
           ++ right. right. right. exists c. split; [exact Hc|]. right. right. left. unfold SHX. lia.
           ++ nolive G. clear - Hx L1 G Hlr K0 K1 Hcr Kc0 Kc1 Kc2 Kp Kp8. lia.
           ++ nolive G. clear - Hx L1 Hlr K0 K2 Hcr Kc0 Kc1 Kc2 Kp Kp8. destruct (Z.eq_dec lc c) as [->|Hn]; lia.
        -- intros x Hx. unfold SHX in Hx. destruct (Z_lt_le_dec x (z_sh pz + 536870912 * c + sz_tbl c / 8 * z_j pz c)) as [Hl|Hl].
           ++ apply HN. exists c. split; [exact Hc | clear - Hx Hl; lia].
           ++ rewrite HF; [exact (PC x Hx) | | |].
              ** right. right. right. exists c. split; [exact Hc|]. right. right. left. unfold SHX. lia.
              ** nolive G. clear - Hx L1 G Hlr K0 K1 Hcr Kc0 Kc1 Kc2 Kp Kp8. lia.
              ** nolive G. clear - Hx Hl L1 Hlr K0 K2 Hcr Kc0 Kc1 Kc2 Kp Kp8. destruct (Z.eq_dec lc c) as [->|Hn]; lia.
Qed.
End FrameLive.

(* [comment removed for export] *)
Lemma HA_on_snap : forall E M a m0 m0', HA_on E M a m0 ->
  (forall x, 0 <= x < 2^64 -> downed (dD1 E a) (dB1 E a) x -> m0' (wa x) = m0 (wa x)) ->
  (a_pri a <> [] -> INV_A E a m0') ->
  (* [comment removed for export] *)
  (a_pri a <> [] -> forall k x, (k < LV_N)%nat -> uE E (lv_B a k) = 1 -> lv_lo E a k <= x < lv_lo E a k + lv_sz E a k -> m0' (wa x) = m0 (wa x)) ->
  HA_on E M a m0'.
Proof.
  intros E M a m0 m0' [Hdep Hown Hownx Hhi HgD HgB Hpri] Hd HI' Hlvfr. constructor; try assumption.
  - destruct Hdep as (nd & F & st & I & R). exists nd, F, st. split; [exact (INV_D_frame _ _ _ _ _ _ _ I Hd) | exact R].
  - intros Hne. destruct (Hpri Hne) as [Hi Ho Hp Ht Hz Hs Hxt Hlv]. constructor; try assumption; [exact (HI' Hne) | exact (lv_inv_snap E a m0 m0' (Hlvfr Hne) Hlv)].
Qed.
(* [comment removed for export] *)
End AcFrameLive.

Module AcGiveX.
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.fast_float.from_chars.images Require Import AsanUbsan.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec ShapeSet RealizesCfg AsanAcct FxLin FxCore FxSound FxMem FxFacts FxStep FxSubst FxEnt FxDrv.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require Import AxMng.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXC Require Import FxBacking FxChDen FxChLib FxChMain.
From OSSVerify.Proofs.fast_float.from_chars.lib.AAXB Require Import AXG_put AXG_put3 AXG_np AXG_nf1 AXG_npf.
From OSSVerify.Proofs.fast_float.from_chars.lib.AACB Require AcPri.
From OSSVerify.Proofs.fast_float.from_chars.lib.AACB Require AcDepDen.
From OSSVerify.Proofs.fast_float.from_chars.lib.AACB Require AcPriHA.
From OSSVerify.Proofs.fast_float.from_chars.lib.AACB Require AcAst.
From OSSVerify.Proofs.fast_float.from_chars.lib.AACB Require AcHA.
From OSSVerify.Proofs.fast_float.from_chars.lib.AACB Require AcHA AcPri.
From OSSVerify.Proofs.fast_float.from_chars.lib.AACB Require AcPriSepOk.
From OSSVerify.Proofs.fast_float.from_chars.lib.AACB Require AcPriSepOk.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXC Require FxChMprot.
From OSSVerify.Proofs.fast_float.from_chars.lib.AACB Require AcMALp AcMALlib AcNPop.
From OSSVerify.Proofs.fast_float.from_chars.lib.AACB Require AcFam2.
From OSSVerify.Proofs.fast_float.from_chars.lib.AACB Require AcConvA.
From OSSVerify.Proofs.fast_float.from_chars.lib.AACB Require AcDenW AcPriStep AcUnwApp.
Import OSSVerify.Proofs.fast_float.from_chars.lib.AACB.AcPri.AcDepSep OSSVerify.Proofs.fast_float.from_chars.lib.AACB.AcDepDen OSSVerify.Proofs.fast_float.from_chars.lib.AACB.AcPriHA.AcPriGrant OSSVerify.Proofs.fast_float.from_chars.lib.AACB.AcAst OSSVerify.Proofs.fast_float.from_chars.lib.AACB.AcHA.AcLv OSSVerify.Proofs.fast_float.from_chars.lib.AACB.AcHA OSSVerify.Proofs.fast_float.from_chars.lib.AACB.AcPri OSSVerify.Proofs.fast_float.from_chars.lib.AACB.AcPriSepOk.AcPriSep OSSVerify.Proofs.fast_float.from_chars.lib.AACB.AcPriSepOk OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChMprot.AcAddOwn OSSVerify.Proofs.fast_float.from_chars.lib.AACB.AcMALp OSSVerify.Proofs.fast_float.from_chars.lib.AACB.AcMALlib OSSVerify.Proofs.fast_float.from_chars.lib.AACB.AcNPop OSSVerify.Proofs.fast_float.from_chars.lib.AACB.AcFam2.AcExt OSSVerify.Proofs.fast_float.from_chars.lib.AACB.AcConvA.AcPriDen OSSVerify.Proofs.fast_float.from_chars.lib.AACB.AcDenW OSSVerify.Proofs.fast_float.from_chars.lib.AACB.AcPriStep OSSVerify.Proofs.fast_float.from_chars.lib.AACB.AcUnwApp.
Import OSSVerify.Proofs.fast_float.from_chars.lib.AACB.AcFam2Ok.AcFrameLive.
Import ListNotations.
Local Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
Lemma nth_remove_nth_lt : forall {A} (l : list A) i j, (j < i)%nat -> nth_error (remove_nth i l) j = nth_error l j.
Proof.
  intros A l. induction l as [|x l IH]; intros i j H; [destruct i; reflexivity|].
  destruct i as [|i]; [lia|]. cbn [remove_nth]. destruct j as [|j]; [reflexivity|]. cbn [nth_error]. apply IH. lia.
Qed.
Lemma incr_b_tail : forall i r, incr_b (i :: r) = true -> incr_b r = true /\ forall k, In k r -> (i < k)%nat.
Proof.
  intros i r. revert i. induction r as [|y r IH]; intros i H; [split; [reflexivity | intros k []]|].
  cbn [incr_b] in H. apply andb_prop in H as [H1 H2]. apply Nat.ltb_lt in H1. split; [exact H2|].
  intros k [<-|Hk]; [exact H1|]. destruct (IH y H2) as [_ X]. specialize (X k Hk). lia.
Qed.
Lemma nth_remove_ixs_lt : forall {A} r (l : list A) j, (forall k, In k r -> (j < k)%nat) -> nth_error (remove_ixs r l) j = nth_error l j.
Proof.
  intros A r. induction r as [|i r IH]; intros l j H; [reflexivity|]. cbn [remove_ixs].
  rewrite nth_remove_nth_lt by (apply H; left; reflexivity). apply IH. intros k Hk. apply H. right. exact Hk.
Qed.

Section GiveX.
Variable cfg : SpuriousCfg.
Variable LIMIT : Z.
Variable model0 : Model.

#[using="Type"] Lemma den_drop_ixs : forall mem0 E M ms model ix S, incr_b ix = true -> DEN ASEGS LIMIT model0 mem0 E S M ms model ->
  (forall i, In i ix -> exists R, nth_error (s_rgs S) i = Some R /\
     forall w, uE E (rg_base R) <= w < uE E (rg_base R) + rsz E R -> own_pt E M w /\ ms_mem ms (Z_to_bv 64 w) = mem0 (Z_to_bv 64 w)) ->
  DEN ASEGS LIMIT model0 mem0 E (with_rgs S (remove_ixs ix (s_rgs S))) M ms model.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros mem0 E M ms model ix. induction ix as [|i r IH]; intros S Hinc Hd Hall.
  - cbn [remove_ixs]. destruct S; exact Hd.
  - destruct (incr_b_tail i r Hinc) as [Hr Hlt]. cbn [remove_ixs].
    pose proof (IH S Hr Hd (fun k Hk => Hall k (or_intror Hk))) as Hd1.
    destruct (Hall i (or_introl eq_refl)) as (R & HR & Hpt).
    assert (HR1 : nth_error (s_rgs (with_rgs S (remove_ixs r (s_rgs S)))) i = Some R).
    { cbn [with_rgs s_rgs]. rewrite (nth_remove_ixs_lt r (s_rgs S) i Hlt). exact HR. }
    exact (den_drop_own ASEGS LIMIT model0 mem0 E _ M ms model i R Hd1 HR1 Hpt).
Qed.

(* [comment removed for export] *)
Definition in_ix (E : valu) (rgs : list region) (ix : list nat) (x : Z) : bool :=
  existsb (fun i => match nth_error rgs i with
                    | Some R => (Z.leb (uE E (rg_base R)) x && Z.ltb x (uE E (rg_base R) + rsz E R))%bool
                    | None => false end) ix.
#[using="Type"] Lemma in_ix_spec : forall E rgs ix x, in_ix E rgs ix x = true <->
  exists i R, In i ix /\ nth_error rgs i = Some R /\ uE E (rg_base R) <= x < uE E (rg_base R) + rsz E R.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros E rgs ix x. unfold in_ix. rewrite existsb_exists. split.
  - intros (i & Hi & H). destruct (nth_error rgs i) as [R|] eqn:ER; [|discriminate]. apply andb_prop in H as [H1 H2].
    apply Z.leb_le in H1. apply Z.ltb_lt in H2. exists i, R. split; [exact Hi|]. split; [exact ER | lia].
  - intros (i & R & Hi & HR & Hx). exists i. split; [exact Hi|]. rewrite HR. apply andb_true_intro. split; [apply Z.leb_le | apply Z.ltb_lt]; lia.
Qed.

#[using="Type"] Theorem givex_node : forall ix S M a S' M' a', apost_givex ix S M a = Some (S', M', a') ->
  forall mem0 E ms model T, DEN ASEGS LIMIT model0 mem0 E S M ms model -> awf (s_next S) a = true -> HA E M a mem0 ->
  (forall E' mem0' ms' model', agree (s_next S) E E' -> frz_same E M mem0 mem0' -> DEN ASEGS LIMIT model0 mem0' E' S' M' ms' model' ->
     HA E' M' a' mem0' -> realizes_cfg ASEGS cfg (mkCfg ms' model') T) ->
  realizes_cfg ASEGS cfg (mkCfg ms model) T.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros ix S M a S' M' a' H mem0 E ms model T Hd Haw HHA Hk. unfold apost_givex in H.
  apply obool_some in H as (Hc & H). injection H as <- <- <-.
  apply andb_prop in Hc as [Hc Call]. apply andb_prop in Hc as [Hhdr Cinc]. unfold givex_hdr_ok in Hhdr.
  apply andb_prop in Hhdr as [Hhdr Hown_eq]. apply andb_prop in Hhdr as [Hon Hlen]. apply Nat.eqb_eq in Hlen.
  apply (list_eqb_eq pair_eqb pair_eqb_eq) in Hown_eq. rewrite forallb_forall in Call.
  pose proof (HHA Hon) as HA0.
  assert (Hne : a_pri a <> []) by (intros Hn; rewrite Hn in Hlen; discriminate).
  pose proof (ha_pri _ _ _ _ HA0 Hne) as HP0. pose proof (po_inv _ _ _ _ HP0) as HI. unfold INV_A in HI. set (pz := pden E a) in *.
  pose proof (tg_pg_disj LIMIT model0 mem0 E S M ms model a mem0 Hd HP0) as Hdisj. fold pz in Hdisj.
  pose proof (az_geo pz mem0 HI) as G.
  set (Hh := Hof E M model) in *. set (mr := ms_mem (restrict Hh ms)) in *.
  pose proof (sden_0 _ _ _ _ (dn_sden _ _ _ _ _ _ _ _ _ Hd)) as (_ & _ & _ & _ & HRG & _ & HF0 & _). fold Hh in HRG. fold mr in HRG.
  rewrite Forall_forall in HRG.
  (* [comment removed for export] *)
  assert (Hlive : forall i R, In i ix -> nth_error (s_rgs S) i = Some R -> forall x, uE E (rg_base R) <= x < uE E (rg_base R) + rsz E R ->
            (live_u pz x \/ live_s pz x) /\ pri_foot_z pz x /\ 0 <= x < 2^47).
  { intros i R Hi HR x Hx. pose proof (Call i Hi) as Ci. rewrite HR in Ci.
    pose proof (HRG R (nth_error_In _ _ HR)) as (Hz0 & _).
    destruct (ext_in_route E (s_facts S) HF0 a mem0 HI (po_ext _ _ _ _ HP0) R Hz0 Ci) as (p & Hp & Hsem & Hside). fold pz in Hsem.
    destruct Hside as [[U1 U2]|(c & Hcin & (V1 & V2 & V3))].
    - destruct Hsem as ((c & Hcin & X1 & X2 & X3) & XB & XG). pose proof (in_cls_rng c Hcin) as Hcr.
      destruct (cls_jb pz mem0 HI c Hcin) as (K0 & K1 & K2 & _).
      assert (Hj1 : 1 <= z_j pz c).
      { destruct (Z_le_gt_dec 1 (z_j pz c)) as [Y|Y]; [exact Y|]. exfalso. assert (z_j pz c = 0) by (clear - K0 Y; lia).
        rewrite H in X2. clear - X1 X2 U1 U2 Hx. lia. }
      assert (Zc : z_z pz c = 262144).
      { destruct (iz_cls _ _ HI c Hcin) as [(J0 & _)|(_ & Z1 & _)]; [clear - J0 Hj1; lia | exact Z1]. }
      split; [left; exists c; split; [exact Hcin|]; split; [clear - X1 X2 U1 U2 Hx; lia|]; split|split].
      + intros Hq Hb. destruct (XB Hq) as [Y|Y]; clear - Y Hb U1 U2 Hx; lia.
      + intros Hg Hb. destruct (XG Hg) as [Y|Y]; clear - Y Hb U1 U2 Hx; lia.
      + right. right. right. exists c. split; [exact Hcin|]. left. rewrite Zc. clear - X1 X2 U1 U2 Hx K1. lia.
      + clear - X1 X2 U1 U2 Hx K1 G Hcr. lia.
    - pose proof (in_cls_rng c Hcin) as Hcr. fold pz in V1, V2, V3.
      split; [right; exists c; split; [exact Hcin | clear - V1 V2 Hx; lia]|]. split.
      + right. right. right. exists c. split; [exact Hcin|]. right. right. left. clear - V1 V2 V3 Hx. lia.
      + clear - V1 V2 V3 Hx G Hcr. lia. }
  (* [comment removed for export] *)
  set (Db := in_ix E (s_rgs S) ix). set (hyb := hyb_p Db (ms_mem ms) mem0).
  assert (Hhyb_in : forall x, 0 <= x < 2^64 -> Db x = true -> hyb (wa x) = ms_mem ms (wa x)).
  { intros x Hx Hb. unfold hyb, hyb_p. rewrite u_wa_small by exact Hx. rewrite Hb. reflexivity. }
  assert (Hhyb_out : forall x, 0 <= x < 2^64 -> Db x = false -> hyb (wa x) = mem0 (wa x)).
  { intros x Hx Hb. unfold hyb, hyb_p. rewrite u_wa_small by exact Hx. rewrite Hb. reflexivity. }
  assert (Hout_nd : forall w : word, outside E (s_rgs S) w -> Db (bv_unsigned w) = false).
  { intros w Hout. destruct (Db (bv_unsigned w)) eqn:Eb; [|reflexivity]. exfalso. apply in_ix_spec in Eb as (i & R & Hi & HR & Hx).
    unfold outside in Hout. rewrite Forall_forall in Hout. specialize (Hout R (nth_error_In _ _ HR)). unfold uE in Hx. clear - Hout Hx. lia. }
  assert (HD1 : DEN ASEGS LIMIT model0 hyb E S M ms model).
  { apply (den_snap ASEGS LIMIT model0 mem0 hyb E S M ms model Hd).
    - intros w (q & Hq & Hqw). destruct (dn_frz _ _ _ _ _ _ _ _ _ Hd q Hq w Hqw) as (_ & Hout & _).
      unfold hyb, hyb_p. rewrite (Hout_nd _ Hout). reflexivity.
    - intros w _ Hout. unfold hyb, hyb_p. rewrite (Hout_nd _ Hout). reflexivity. }
  (* [comment removed for export] *)
  assert (HD2 : DEN ASEGS LIMIT model0 hyb E (with_rgs S (remove_ixs ix (s_rgs S))) M ms model).
  { apply (den_drop_ixs hyb E M ms model ix S Cinc HD1). intros i Hi.
    pose proof (Call i Hi) as Ci. destruct (nth_error (s_rgs S) i) as [R|] eqn:HR; [|discriminate]. exists R. split; [reflexivity|].
    intros w Hw. destruct (Hlive i R Hi HR w Hw) as (_ & Hf & Hr). split.
    - exact (po_own _ _ _ _ HP0 w ltac:(clear - Hr; lia) Hf).
    - change (Z_to_bv 64 w) with (wa w). symmetry. apply Hhyb_in; [clear - Hr; lia|]. apply in_ix_spec. exists i, R. split; [exact Hi|]. split; [exact HR | exact Hw]. }
  apply (Hk E hyb ms model); [apply agree_refl | | exact HD2 |].
  - intros q Hq w Hqw. destruct (dn_frz _ _ _ _ _ _ _ _ _ Hd q Hq w Hqw) as (_ & Hout & _).
    unfold hyb, hyb_p. rewrite (Hout_nd _ Hout). reflexivity.
  - intros _. apply (HA_on_snap E M a mem0 hyb HA0).
    + intros x Hx Hdw. apply (Hhyb_out x Hx). destruct (Db x) eqn:Eb; [|reflexivity]. exfalso.
      apply in_ix_spec in Eb as (i & R & Hi & HR & Hxr). destruct (Hlive i R Hi HR x Hxr) as (_ & Hf & _).
      exact (pri_not_downed LIMIT model0 mem0 E S M ms model a mem0 Hd HA0 Hne x Hf Hdw).
    + intros _. unfold INV_A. fold pz. apply (INV_Az_frame_live pz mem0 hyb HI Hdisj).
      * intros x Hf Hnu Hns. pose proof (pri_foot_rng E a mem0 HI x Hf) as Rx. apply (Hhyb_out x ltac:(clear - Rx; lia)).
        destruct (Db x) eqn:Eb; [|reflexivity]. exfalso. apply in_ix_spec in Eb as (i & R & Hi & HR & Hxr).
        destruct (Hlive i R Hi HR x Hxr) as ([L|L] & _); [exact (Hnu L) | exact (Hns L)].
      * intros x Hs. assert (Hx47 : 2199291686912 <= x < 2^47).
        { destruct Hs as (c & Hcin & L1). pose proof (in_cls_rng c Hcin) as Hcr. destruct (cls_jb pz mem0 HI c Hcin) as (K0 & _ & K2 & _). clear - L1 G Hcr K0 K2. lia. }
        destruct (Db x) eqn:Eb.
        -- rewrite (Hhyb_in x ltac:(clear - Hx47; lia) Eb). apply in_ix_spec in Eb as (i & R & Hi & HR & Hxr).
           pose proof (HRG R (nth_error_In _ _ HR)) as (Hz0 & Hz1 & Hpt & _).
           specialize (Hpt (x - uE E (rg_base R)) ltac:(clear - Hxr; lia)). unfold uE in Hpt.
           replace (bv_unsigned (lden E (rg_base R)) + (x - bv_unsigned (lden E (rg_base R)))) with x in Hpt by ring.
           assert (Hrom : seg_rom ASEGS (Z_to_bv 64 x) = None).
           { apply (seg_rom_above ASEGS (2^33)); [vm_compute; reflexivity|]. rewrite u_small64 by (unfold two64; clear - Hx47; lia). clear - Hx47. lia. }
           assert (Hrd : rd1 ASEGS mr (Z_to_bv 64 x) <> None).
           { destruct (rg_kind R); first [exact (proj1 Hpt) | exact (proj1 (proj1 Hpt)) | exact Hpt | exfalso; destruct Hpt as [_ X]; exact (X Hrom)]. }
           pose proof (vis_of_rd1 Hh (ms_mem ms) (Z_to_bv 64 x) Hrd Hrom) as Hv.
           unfold rd1 in Hrd. unfold mr in Hrd. cbn [restrict ms_mem] in Hrd. unfold mrestrict in Hrd. rewrite Hv, Hrom in Hrd.
           unfold wa. destruct (ms_mem ms (Z_to_bv 64 x)); [discriminate | exfalso; apply Hrd; reflexivity].
        -- rewrite (Hhyb_out x ltac:(clear - Hx47; lia) Eb). destruct Hs as (c & Hcin & L1).
           destruct (iz_cls _ _ HI c Hcin) as [(J0 & _)|(_ & _ & _ & _ & HPo)]; [rewrite J0 in L1; clear - L1; lia|].
           destruct (cls_jb pz mem0 HI c Hcin) as (_ & _ & K2 & _).
           apply (pc_shm _ _ _ _ _ _ HPo x). unfold SHX. clear - L1 K2. lia.
    + (* [comment removed for export] *)
      intros _ k x Hkk HB Hxr. pose proof (po_lv _ _ _ _ HP0) as Hlv. destruct (proj1 Hlv k Hkk) as [_ L]. destruct (L HB) as (L3 & _).
      pose proof (ext_sem_foot _ mem0 _ _ HI L3 x Hxr) as Hf. pose proof (pri_foot_rng E a mem0 HI x Hf) as Rx.
      apply (Hhyb_out x ltac:(clear - Rx; lia)). destruct (Db x) eqn:Eb; [|reflexivity]. exfalso.
      apply in_ix_spec in Eb as (i & R & Hi & HR & Hxi). pose proof (Call i Hi) as Ci. rewrite HR in Ci.
      pose proof (HRG R (nth_error_In _ _ HR)) as (Hz0 & _).
      destruct (ext_in_route E (s_facts S) HF0 a mem0 HI (po_ext _ _ _ _ HP0) R Hz0 Ci) as (p & Hp & Hsem & Hside).
      destruct Hside as [[U1 U2]|(c & Hcin & (V1 & V2 & V3))].
      * apply (lv_apart_entry E a mem0 p k Hlv Hp Hkk HB x). split; [clear - U1 U2 Hxi; lia | exact Hxr].
      * destruct L3 as ((c' & Hcin' & X1 & X2 & _) & _). fold pz in X1, X2, V1, V2, V3.
        pose proof (in_cls_rng c Hcin) as Hcr. pose proof (in_cls_rng c' Hcin') as Hcr'.
        destruct (cls_jb pz mem0 HI c' Hcin') as (_ & K1 & _). clear - V1 V2 V3 X1 X2 K1 Hxi Hxr G Hcr Hcr'. lia.
Qed.
End GiveX.
(* [comment removed for export] *)
End AcGiveX.

Import OSSVerify.Proofs.fast_float.from_chars.lib.AACB.AcPri.AcDepSep OSSVerify.Proofs.fast_float.from_chars.lib.AACB.AcAst OSSVerify.Proofs.fast_float.from_chars.lib.AACB.AcHA OSSVerify.Proofs.fast_float.from_chars.lib.AACB.AcFam OSSVerify.Proofs.fast_float.from_chars.lib.AACB.AcPri OSSVerify.Proofs.fast_float.from_chars.lib.AACB.AcConvA OSSVerify.Proofs.fast_float.from_chars.lib.AACB.AcNPop OSSVerify.Proofs.fast_float.from_chars.lib.AACB.AcNEnq OSSVerify.Proofs.fast_float.from_chars.lib.AACB.AcNPopG OSSVerify.Proofs.fast_float.from_chars.lib.AACB.AcFam2.AcExt OSSVerify.Proofs.fast_float.from_chars.lib.AACB.AcFam2 OSSVerify.Proofs.fast_float.from_chars.lib.AACB.AcNPopN.AcConvAN OSSVerify.Proofs.fast_float.from_chars.lib.AACB.AcFam2Ok.AcNPopAll OSSVerify.Proofs.fast_float.from_chars.lib.AACB.AcFam2Ok.AcNPopGAll OSSVerify.Proofs.fast_float.from_chars.lib.AACB.AcFam2Ok.AcNEnqAll OSSVerify.Proofs.fast_float.from_chars.lib.AACB.AcFam2Ok.AcExtN OSSVerify.Proofs.fast_float.from_chars.lib.AACB.AcFam2Ok.AcGiveX.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Section Fam2.
Variable cfg : SpuriousCfg.
Variable LIMIT : Z.
Hypothesis Hwx : wx_segs_nowrap ASEGS.
Hypothesis Hsegb : segs_below_b ASEGS 0x800000000000 = true.
Hypothesis Hoff : sc_alloc cfg = false.
Hypothesis Hrespos : Forall (fun p => 0 < bv_unsigned (snd p)) (segments_reserved ASEGS).
Hypothesis Hreswf : ivs_wf (segments_reserved ASEGS).

#[using="Hwx Hsegb Hoff Hrespos Hreswf"] Theorem alloc2_anode_ok : forall nk, anode_ok ASEGS cfg LIMIT (apost_alloc2 LIMIT) awf HA nk.
Proof. LiaFast.lf_pins (fun (Hwx Hsegb Hoff Hrespos Hreswf : LiaFast.U) => LiaFast.u0).
  intros [k| |c|c|c|c ix|c i s| |ix|i s|i|i b z|i j1 j2| ] S M a S' M' a' H model0 mem0 E ms model T Hd Haw HHA Hk; cbn [apost_alloc2] in H; try discriminate H.
  - exact (alloc_anode_ok cfg LIMIT Hwx Hsegb Hoff Hrespos Hreswf k S M a S' M' a' H model0 mem0 E ms model T Hd Haw HHA Hk).
  - exact (conva_node cfg LIMIT model0 S M a S' M' a' H mem0 E ms model T Hd Haw HHA Hk).
  - exact (npop_node cfg LIMIT model0 Hwx Hsegb Hoff Hrespos Hreswf c S M a S' M' a' H mem0 E ms model T Hd Haw HHA Hk).
  - exact (npopg_node cfg LIMIT model0 Hwx Hsegb Hoff Hrespos Hreswf S M a S' M' a' H mem0 E ms model T Hd Haw HHA Hk).
  - exact (givex_node cfg LIMIT model0 ix S M a S' M' a' H mem0 E ms model T Hd Haw HHA Hk).
  - exact (extdrop_node cfg LIMIT model0 i S M a S' M' a' H mem0 E ms model T Hd Haw HHA Hk).
  - exact (extsub_node cfg LIMIT model0 i b z S M a S' M' a' H mem0 E ms model T Hd Haw HHA Hk).
  - exact (exthull_node cfg LIMIT model0 i j1 j2 S M a S' M' a' H mem0 E ms model T Hd Haw HHA Hk).
  - exact (nenq_node cfg LIMIT model0 Hwx Hsegb Hoff Hrespos Hreswf S M a S' M' a' H mem0 E ms model T Hd Haw HHA Hk).
Qed.
End Fam2.
(* [comment removed for export] *)
