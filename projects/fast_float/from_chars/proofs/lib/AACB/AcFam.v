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
From OSSVerify.Proofs.fast_float.from_chars.lib.AACB Require AcAst AcHA.
From OSSVerify.Proofs.fast_float.from_chars.lib.AACB Require AcPri.
From OSSVerify.Proofs.fast_float.from_chars.lib.AACB Require AcMALlib AcConvG AcPutN AcUnwN.
From OSSVerify.Proofs.fast_float.from_chars.lib.AACB Require AcSysK.
From OSSVerify.Proofs.fast_float.from_chars.lib.AACB Require AcSysK.

Module AcSysS.
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.fast_float.from_chars.images Require Import AsanUbsan.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec ShapeSet RealizesCfg AsanAcct PlacementCount AllocNodesCfg.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxLin FxCore FxSound FxMem FxFacts FxStep.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxLoop.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxSubst FxEnt FxPlan FxFrame FxDrv FxCall FxEcall.
Import OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxLin OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxCore OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxSound OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxMem OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxFacts OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxStep OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxLoop.FxExplore OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxSubst OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxEnt OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxPlan OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxFrame OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxDrv OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxCall OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxEcall.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXC Require FxBacking FxChDen FxChLib FxChSep FxChNull.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXC Require FxChAdd.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXC Require FxChFix FxChAdd FxChFixNew FxChain.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXC Require FxChNull.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXC Require FxChMain.
Import OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxBacking OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChDen OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChLib OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChSep OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChNull OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChAdd.FxChNullS OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChFix OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChAdd OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChFixNew OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChain OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChNull.FxChNode OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChMain.
From OSSVerify.Proofs.fast_float.from_chars.lib.AACB Require AcAst AcHA.
From OSSVerify.Proofs.fast_float.from_chars.lib.AACB Require AcSteps.
From OSSVerify.Proofs.fast_float.from_chars.lib.AACB Require AcPri.
From OSSVerify.Proofs.fast_float.from_chars.lib.AACB Require AcDepDen AcTbl.
From OSSVerify.Proofs.fast_float.from_chars.lib.AACB Require AcUnwApp.
From OSSVerify.Proofs.fast_float.from_chars.lib.AACB Require AcPriSepOk.
From OSSVerify.Proofs.fast_float.from_chars.lib.AACB Require AcMALlib.
From OSSVerify.Proofs.fast_float.from_chars.lib.AACB Require AcSysK.
Import OSSVerify.Proofs.fast_float.from_chars.lib.AACB.AcAst OSSVerify.Proofs.fast_float.from_chars.lib.AACB.AcHA OSSVerify.Proofs.fast_float.from_chars.lib.AACB.AcSteps.AcP0gen OSSVerify.Proofs.fast_float.from_chars.lib.AACB.AcPri.AcDepSep OSSVerify.Proofs.fast_float.from_chars.lib.AACB.AcDepDen OSSVerify.Proofs.fast_float.from_chars.lib.AACB.AcTbl OSSVerify.Proofs.fast_float.from_chars.lib.AACB.AcUnwApp.AcTblOk OSSVerify.Proofs.fast_float.from_chars.lib.AACB.AcPriSepOk.AcFast OSSVerify.Proofs.fast_float.from_chars.lib.AACB.AcMALlib OSSVerify.Proofs.fast_float.from_chars.lib.AACB.AcSysK.AcSysN.
Import ListNotations.
Local Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Definition apost_nullS (LIMIT : Z) (k : gkind) (vis piece na : bool) (S : sst) (M : smodel) (a : ast) : option (sst * smodel * ast) :=
  obool (Z.eqb (s_pc S) 0x73c38 && null_okS ASEGSR LIMIT S M k vis piece na && own_ok_b M a)%bool
    (Some (null_postS S (rget (s_regs S) (rkey a1r)) (null_loS S) (null_hiS S) vis piece,
           null_MS M (s_next S) (rget (s_regs S) (rkey a1r)) (null_hiS S) k vis piece, a)).

Section NullSNode.
Variable cfg : SpuriousCfg.
Variable LIMIT : Z.
Variable model0 : Model.
Hypothesis Hwx : wx_segs_nowrap ASEGS.
Hypothesis Hsegb : segs_below_b ASEGS 0x800000000000 = true.
Hypothesis Hoff : sc_alloc cfg = false.

#[using="Hwx Hsegb Hoff"] Theorem nullS_node : forall k vis piece na S M a S' M' a', apost_nullS LIMIT k vis piece na S M a = Some (S', M', a') ->
  forall mem0 E ms model T, DEN ASEGS LIMIT model0 mem0 E S M ms model -> awf (s_next S) a = true -> HA E M a mem0 ->
  (forall E' mem0' ms' model', agree (s_next S) E E' -> frz_same E M mem0 mem0' -> DEN ASEGS LIMIT model0 mem0' E' S' M' ms' model' ->
     HA E' M' a' mem0' -> realizes_cfg ASEGS cfg (mkCfg ms' model') T) ->
  realizes_cfg ASEGS cfg (mkCfg ms model) T.
Proof. LiaFast.lf_pins (fun (Hwx Hsegb Hoff : LiaFast.U) => LiaFast.u0).
  intros k vis piece na S M a S' M' a' H mem0 E ms model T Hd Haw HHA Hk.
  unfold apost_nullS in H. apply obool_some in H as (Hb & H). injection H as <- <- <-.
  apply andb_prop in Hb as [Hb Hoo]. apply andb_prop in Hb as [Hpc Hnull].
  apply Z.eqb_eq in Hpc. unfold ASEGSR in Hnull.
  apply (den_ecall ASEGS cfg LIMIT model0 mem0 Hwx ATBLd E S M ms model T ATBLd_ecall ltac:(rewrite Hpc; exact ecall_73aa8) Hd).
  intros model' Hd'.
  apply (den_nullS ASEGS cfg LIMIT model0 mem0 Hsegb Hoff E S M ms model' T k vis piece na Hd' Hnull).
  - intros ad Hpl. unfold own_ok_b in Hoo.
    pose proof (uE_range E (rget (s_regs S) (rkey a1r))) as Rln.
    destruct (sm_own M) as [|p0 ps] eqn:Hown.
    + split; [exact (own_avoid_nil E M _ _ Hown) | intros _; exact (own_avoid_nil E M _ _ Hown)].
    + apply andb_prop in Hoo as [Hoo Hoe]. apply (list_eqb_eq pair_eqb pair_eqb_eq) in Hoe.
      assert (Hoa : sm_own M = a_own a) by (rewrite Hown; exact Hoe).
      pose proof (HHA Hoo) as HA0. split.
      * apply (dep_avoid_place LIMIT model0 mem0 E S M ms model' a mem0 _ ad Hd' HA0 Hoa Hpl). exact Rln.
      * intros _. exact (dep_avoid_shadow_place LIMIT model0 mem0 E S M ms model' a mem0 _ ad Hd' HA0 Hoa Hpl Rln).
  - intros E' ms' model'' Hd2 Ha2. apply (Hk E' mem0 ms' model'' Ha2).
    + intros q Hq w Hw. reflexivity.
    + exact Hd2.
    + apply (HA_keep_own E E' M _ a mem0 (s_next S) HHA (dn_wf _ _ _ _ _ _ _ _ _ Hd) Haw Ha2); [reflexivity | reflexivity |].
      intros b z kd Hin. exists kd. unfold null_MS. cbn [sm_maps]. right. exact Hin.
Qed.
End NullSNode.
(* [comment removed for export] *)
End AcSysS.


Module AcMset.
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.fast_float.from_chars.images Require Import AsanUbsan.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec StoreOk ShapeSet RealizesCfg AsanAcct PlacementCount AllocNodesCfg.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxLin FxCore FxSound FxMem FxFacts FxStep.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxLoop.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxSubst FxEnt FxPlan FxFrame FxDrv FxCall.
Import OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxLin OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxCore OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxSound OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxMem OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxFacts OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxStep OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxLoop.FxExplore OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxSubst OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxEnt OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxPlan OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxFrame OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxDrv OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxCall.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require Import AxMng.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXC Require Import FxBacking FxChDen FxChLib FxChMain FxChSplit.
From OSSVerify.Proofs.fast_float.from_chars.lib.AAXB Require AXG_put AXG_put2.
From OSSVerify.Proofs.fast_float.from_chars.lib.AAXB Require AXG_np2.
From OSSVerify.Proofs.fast_float.from_chars.lib.AAXB Require AXG_np2.
From OSSVerify.Proofs.fast_float.from_chars.lib.AAXB Require AXG_np2.
From OSSVerify.Proofs.fast_float.from_chars.lib.AAXB Require AXG_np2.
Import OSSVerify.Proofs.fast_float.from_chars.lib.AAXB.AXG_put OSSVerify.Proofs.fast_float.from_chars.lib.AAXB.AXG_put2 OSSVerify.Proofs.fast_float.from_chars.lib.AAXB.AXG_np2.AXG_ms2 OSSVerify.Proofs.fast_float.from_chars.lib.AAXB.AXG_np2.AXG_msc OSSVerify.Proofs.fast_float.from_chars.lib.AAXB.AXG_np2.AXG_msc2 OSSVerify.Proofs.fast_float.from_chars.lib.AAXB.AXG_np2.AXG_msc3.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXC Require FxChDen.
From OSSVerify.Proofs.fast_float.from_chars.lib.AACB Require AcHand AcHand0 AcDenW.
From OSSVerify.Proofs.fast_float.from_chars.lib.AACB Require AcUnwApp.
From OSSVerify.Proofs.fast_float.from_chars.lib.AACB Require AcUnwApp AcUnwApp0.
From OSSVerify.Proofs.fast_float.from_chars.lib.AACB Require AcShapes0.
From OSSVerify.Proofs.fast_float.from_chars.lib.AACB Require AcAst AcHA.
From OSSVerify.Proofs.fast_float.from_chars.lib.AACB Require AcPri.
From OSSVerify.Proofs.fast_float.from_chars.lib.AACB Require AcMALlib AcSplitX AcCarve.
Import OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChDen.AcMrg OSSVerify.Proofs.fast_float.from_chars.lib.AACB.AcHand OSSVerify.Proofs.fast_float.from_chars.lib.AACB.AcHand0 OSSVerify.Proofs.fast_float.from_chars.lib.AACB.AcDenW OSSVerify.Proofs.fast_float.from_chars.lib.AACB.AcUnwApp.AcPutApp OSSVerify.Proofs.fast_float.from_chars.lib.AACB.AcUnwApp OSSVerify.Proofs.fast_float.from_chars.lib.AACB.AcUnwApp0 OSSVerify.Proofs.fast_float.from_chars.lib.AACB.AcShapes0.AcShapes OSSVerify.Proofs.fast_float.from_chars.lib.AACB.AcAst OSSVerify.Proofs.fast_float.from_chars.lib.AACB.AcHA OSSVerify.Proofs.fast_float.from_chars.lib.AACB.AcPri.AcDepSep OSSVerify.Proofs.fast_float.from_chars.lib.AACB.AcMALlib OSSVerify.Proofs.fast_float.from_chars.lib.AACB.AcSplitX OSSVerify.Proofs.fast_float.from_chars.lib.AACB.AcCarve.
Import ListNotations.
Local Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
Definition Snil : sst := SST 0 TEmpty [] [] 1%positive RNone.
Lemma mrg_nil : forall L, mrg L Snil = L.
Proof. intros [pc r g f n v]. unfold mrg, Snil. cbn [s_pc s_regs s_rgs s_facts s_next s_resv]. rewrite !app_nil_r. reflexivity. Qed.

(* [comment removed for export] *)
Section IstepsQ.
Variable segs : list Segment.
Variable cfg : SpuriousCfg.
Variable LIMIT : Z.
Variable model0 : Model.
Variable mem0 : word -> option byte.
Hypothesis Hwx : wx_segs_nowrap segs.

#[using="Hwx"] Theorem den_isteps_q : forall E S M ms model T L msr' E',
  DEN segs LIMIT model0 mem0 E S M ms model ->
  isteps segs (restrict (Hof E M model) ms) msr' ->
  sden segs E' L msr' -> agree (s_next S) E E' -> (s_next S <= s_next L)%positive ->
  (forall x, outside E (s_rgs S) x -> ms_mem msr' x = ms_mem (restrict (Hof E M model) ms) x) ->
  shape (s_rgs L) = shape (s_rgs S) ->
  (forall E' ms' model', DEN segs LIMIT model0 mem0 E' L M ms' model' -> agree (s_next S) E E' ->
      (forall x, Hof E M model x = false -> ms_mem ms' x = ms_mem msr' x) ->
      realizes_cfg segs cfg (mkCfg ms' model') T) ->
  realizes_cfg segs cfg (mkCfg ms model) T.
Proof. LiaFast.lf_pins (fun (Hwx : LiaFast.U) => LiaFast.u0).
  intros E S M ms model T L msr' E' Hd Hst Hd' Ha Hn Hfr Hsh Hk.
  pose proof (dn_own _ _ _ _ _ _ _ _ _ Hd) as Hown.
  pose proof (dn_frz _ _ _ _ _ _ _ _ _ Hd) as Hfrz.
  pose proof (dn_wf _ _ _ _ _ _ _ _ _ Hd) as Hwf.
  pose proof (dn_bases _ _ _ _ _ _ _ _ _ Hd) as Hbw.
  apply (den_isteps_w segs cfg LIMIT model0 Hwx mem0 E S M ms model T L msr' E' Hd Hst Hd' Ha Hn).
  - intros w _ Hout _. exact (Hfr _ Hout).
  - intros w (q & Hq & Hw). destruct (Hfrz q Hq w Hw) as (_ & Hout & _). exact (Hfr _ Hout).
  - exact Hsh.
  - intros E2 ms2 model2 HD2 Ha2 Hfz2 Hvis2. apply (Hk E2 ms2 model2); [|exact Ha2|exact Hvis2].
    apply (den_snap segs LIMIT model0 (ms_mem ms2) mem0 E2 L M ms2 model2 HD2).
    + intros w Hw. symmetry. apply Hfz2. exact (proj1 (frz_pt_agree (s_next S) E E2 M w Hwf Ha2) Hw).
    + intros w Hw Hout. apply (proj1 (own_pt_agree (s_next S) E E2 M w Hwf Ha2)) in Hw. destruct Hw as (q & Hq & Hw).
      destruct (Hown q Hq w Hw) as [Hv Hm].
      assert (Hout0 : outside E (s_rgs S) (Z_to_bv 64 w)) by exact (outside_agree_shape _ E E2 _ _ _ Hbw Ha2 Hsh Hout).
      rewrite (Hvis2 _ Hv), (Hfr _ Hout0). cbn [restrict ms_mem]. unfold mrestrict. rewrite Hv. symmetry. exact (Hm Hout0).
Qed.

(* [comment removed for export] *)
#[using="Hwx"] Theorem den_hand_q0 : forall L S E M ms model T q K W msr',
  DEN segs LIMIT model0 mem0 E (mrg L S) M ms model ->
  state_wf L = true ->
  (forall i R, In i W -> nth_error (s_rgs L) i = Some R -> rg_kind R <> RO) ->
  isteps segs (restrict (Hof E M model) ms) msr' -> ms_pc_val msr' = Z_to_bv 64 q -> ms_svc_pending msr' = None ->
  ms_resv msr' = None -> ms_fcsr msr' = ms_fcsr ms ->
  (forall r : reg, existsb (Pos.eqb (rkey r)) K = true -> getr (ms_regs msr') r = getr (ms_regs ms) r) ->
  (forall x, ~ (exists i R, In i W /\ nth_error (s_rgs L) i = Some R /\ in_rg E R x) -> ms_mem msr' x = ms_mem (restrict (Hof E M model) ms) x) ->
  (forall i R j, In i W -> nth_error (s_rgs L) i = Some R -> 0 <= j < rsz E R ->
     rd1 segs (ms_mem msr') (Z_to_bv 64 (bv_unsigned (lden E (rg_base R)) + j)) <> None /\
     (rg_kind R <> RT -> wview segs (ms_mem msr') (Z_to_bv 64 (bv_unsigned (lden E (rg_base R)) + j)) <> None)) ->
  (forall E' ms' model', DEN segs LIMIT model0 mem0 E' (mrg (hand_post L q K W) S) M ms' model' ->
     agree (s_next L) E E' -> (forall x, Hof E M model x = false -> ms_mem ms' x = ms_mem msr' x) ->
     realizes_cfg segs cfg (mkCfg ms' model') T) ->
  realizes_cfg segs cfg (mkCfg ms model) T.
Proof. LiaFast.lf_pins (fun (Hwx : LiaFast.U) => LiaFast.u0).
  intros L S E M ms model T q K W msr' Hd HwL HnRO Hst Hpc Hsvc Hrsv Hfcsr Hkeep Hmem Hrw Hk.
  pose proof (dn_sden _ _ _ _ _ _ _ _ _ Hd) as Hsd.
  assert (Ha : agree (s_next L) E (hval0 (s_next L) E (ms_regs msr'))) by (intros x Hx; unfold hval0; rewrite (proj2 (Pos.ltb_lt _ _) Hx); reflexivity).
  apply (den_isteps_q E (mrg L S) M ms model T (mrg (hand_post L q K W) S) msr' (hval0 (s_next L) E (ms_regs msr')) Hd Hst).
  - assert (HbS : bases_wf (s_next L) (s_rgs S) = true).
    { pose proof (dn_bases _ _ _ _ _ _ _ _ _ Hd) as Hb. cbn [mrg s_next s_rgs] in Hb. unfold bases_wf in *.
      rewrite forallb_app in Hb. apply andb_prop in Hb as [_ Hb]. exact Hb. }
    apply (hand_sden0 segs L S E _ msr' q K W Hsd HwL HbS HnRO Hpc Hsvc Hrsv Hfcsr Hkeep); [|exact Hrw].
    intros x Hx _. exact (Hmem x Hx).
  - exact Ha.
  - cbn [mrg hand_post s_next]. lia.
  - intros x Hx. apply Hmem. intros (i0 & R2 & Hi0 & HR2 & Hin). unfold outside in Hx. cbn [mrg s_rgs] in Hx.
    apply Forall_app in Hx as [Hx _]. rewrite Forall_forall in Hx. specialize (Hx R2 (nth_error_In _ _ HR2)).
    unfold in_rg in Hin. unfold rsz in Hx, Hin. lia.
  - cbn [mrg s_rgs hand_post]. unfold shape. rewrite !map_app. f_equal. exact (empty_at_shape W (s_rgs L) 0).
  - intros E2 ms2 model2 HD2 Ha2 Hvis. exact (Hk E2 ms2 model2 HD2 Ha2 Hvis).
Qed.
End IstepsQ.

(* [comment removed for export] *)
Lemma nth_error_empty_at : forall W rgs i j, nth_error (empty_at W i rgs) j =
  match nth_error rgs j with Some R => Some (if existsb (Nat.eqb (i + j)) W then empty_rg R else R) | None => None end.
Proof.
  intros W rgs. induction rgs as [|R rs IH]; intros i j; [destruct j; reflexivity|]. cbn [empty_at].
  destruct j as [|j]; cbn [nth_error].
  - rewrite Nat.add_0_r. reflexivity.
  - rewrite IH. replace (Datatypes.S i + j)%nat with (i + Datatypes.S j)%nat by lia. reflexivity.
Qed.

(* [comment removed for export] *)
Definition KMSk : list positive := List.map rk [1;2;3;4;5;6;7;8;9;10;17;18;19;20;21;22;23;24;25;26;27;28;29;30;31].
Lemma kms_cases : forall r, existsb (Pos.eqb (rkey r)) KMSk = true -> exists k : nat, In k KMS /\ r = Z_to_bv 5 (Z.of_nat k).
Proof.
  intros r Hr. apply existsb_exists in Hr as (key & Hkey & Hke). apply Pos.eqb_eq in Hke.
  unfold KMSk in Hkey. apply in_map_iff in Hkey as (z & Hz & Hin).
  assert (Hr : r = Z_to_bv 5 z) by (rewrite <- (rkey_reg r), Hke, <- Hz; exact (rkey_reg (Z_to_bv 5 z))).
  exists (Z.to_nat z). cbn [In] in Hin.
  repeat destruct Hin as [<-|Hin]; try destruct Hin; (split; [cbn [KMS In]; repeat (first [left; reflexivity | right]) | exact Hr]).
Qed.

(* [comment removed for export] *)
Definition mset_rng_ok (fs : list fact) (p m : lin) : bool :=
  (Z.leb 1 (fst (irange fs p)) && Z.leb (snd (irange fs p) + snd (irange fs m)) (2^47) && Z.leb (snd (irange fs m)) (2^32))%bool.

Definition apost_mset (S : sst) (M : smodel) (a : ast) : option (sst * smodel * ast) :=
  let p := rget (s_regs S) (rk 10) in let mm := rget (s_regs S) (rk 12) in
  obool (Z.eqb (s_pc S) 0xd4904 && rsv_none_b (s_resv S) && lin_eqb (rget (s_regs S) (rk 11)) (lconst 0) && mset_rng_ok (s_facts S) p mm)%bool (
  obind (msplit S p mm) (fun sj =>
  obool (state_wf (fst sj)) (
  obind (rz_zero_post (hand_post (fst sj) 0xd49f8 KMSk [snd sj]) (snd sj)) (fun S3 =>
  Some (S3, M, a))))).
Lemma apost_mset_unf : forall S M a,
  (let p := rget (s_regs S) (rk 10) in let mm := rget (s_regs S) (rk 12) in
  obool (Z.eqb (s_pc S) 0xd4904 && rsv_none_b (s_resv S) && lin_eqb (rget (s_regs S) (rk 11)) (lconst 0) && mset_rng_ok (s_facts S) p mm)%bool (
  obind (msplit S p mm) (fun sj =>
  obool (state_wf (fst sj)) (
  obind (rz_zero_post (hand_post (fst sj) 0xd49f8 KMSk [snd sj]) (snd sj)) (fun S3 =>
  Some (S3, M, a)))))) = apost_mset S M a.
Proof. intros. exact eq_refl. Qed.

Section MsetNode.
Variable cfg : SpuriousCfg.
Variable LIMIT : Z.
Variable model0 : Model.
Hypothesis Hwx : wx_segs_nowrap ASEGS.

#[using="Hwx"] Theorem mset_node : forall S M a S' M' a', apost_mset S M a = Some (S', M', a') ->
  forall mem0 E ms model T, DEN ASEGS LIMIT model0 mem0 E S M ms model -> awf (s_next S) a = true -> HA E M a mem0 ->
  (forall E' mem0' ms' model', agree (s_next S) E E' -> frz_same E M mem0 mem0' -> DEN ASEGS LIMIT model0 mem0' E' S' M' ms' model' ->
     HA E' M' a' mem0' -> realizes_cfg ASEGS cfg (mkCfg ms' model') T) ->
  realizes_cfg ASEGS cfg (mkCfg ms model) T.
Proof. LiaFast.lf_pins (fun (Hwx : LiaFast.U) => LiaFast.u0).
  intros S M a S' M' a' H mem0 E ms model T Hd Haw HHA Hk.
  rewrite <- apost_mset_unf in H. cbv zeta in H.
  apply obool_some in H as (Hchk & H).
  apply obind_some in H as ([S1 jm] & HS1 & H). cbv beta in H. cbn [fst snd] in H.
  apply obool_some in H as (Hwf1 & H).
  apply obind_some in H as (S3 & HS3 & H). injection H as <- <- <-.
  apply andb_prop in Hchk as [Hchk Hrng]. apply andb_prop in Hchk as [Hchk Ha1]. apply andb_prop in Hchk as [Hpc Hrsv].
  apply Z.eqb_eq in Hpc. apply rsv_none_b_sound in Hrsv. apply lin_eqb_eq in Ha1.
  set (p := rget (s_regs S) (rk 10)) in *. set (mm := rget (s_regs S) (rk 12)) in *.
  (* [comment removed for export] *)
  destruct (msplit_sound ASEGS LIMIT mem0 model0 E S M ms model p mm S1 jm HS1 Hd) as (Hd1 & E1pc & E1r & E1f & E1n & E1v & Hmid & Hlp & Hlm).
  pose proof (dn_wf _ _ _ _ _ _ _ _ _ Hd) as HwfM.
  pose proof (dn_sden _ _ _ _ _ _ _ _ _ Hd1) as Hsd1.
  set (H := Hof E M model) in *. set (msr := restrict H ms) in *.
  pose proof (sden_0 _ _ _ _ Hsd1) as Hd0.
  destruct Hd0 as (Hpc0 & Hsvc & Hrv0 & HR & HG & _ & HF & _).
  assert (Hrv : ms_resv ms = None) by (rewrite E1v, Hrsv in Hrv0; cbn [rsv_ok] in Hrv0; exact Hrv0).
  assert (Hpc1 : ms_pc_val ms = wa 0xd4904) by (rewrite E1pc, Hpc in Hpc0; exact Hpc0).
  rewrite E1f in HF.
  (* [comment removed for export] *)
  set (s := bv_unsigned (lden E p)). set (n := bv_unsigned (lden E mm)).
  assert (Rs : getr (ms_regs ms) (Z_to_bv 5 10) = wa s).
  { change (ms_regs ms) with (ms_regs msr). rewrite (HR (Z_to_bv 5 10)), E1r. unfold s, wa. rewrite Z_to_bv_bv_unsigned. reflexivity. }
  assert (R11 : getr (ms_regs ms) (Z_to_bv 5 11) = wa 0).
  { change (ms_regs ms) with (ms_regs msr). rewrite (HR (Z_to_bv 5 11)), E1r. change (rkey (Z_to_bv 5 11)) with (rk 11). rewrite Ha1, lden_lconst. reflexivity. }
  assert (Rn : getr (ms_regs ms) (Z_to_bv 5 12) = wa n).
  { change (ms_regs ms) with (ms_regs msr). rewrite (HR (Z_to_bv 5 12)), E1r. unfold n, wa. rewrite Z_to_bv_bv_unsigned. reflexivity. }
  pose proof (irange_sound E (s_facts S) p HF) as Bp. pose proof (irange_sound E (s_facts S) mm HF) as Bm.
  unfold mset_rng_ok in Hrng. repeat match goal with H0 : (_ && _)%bool = true |- _ => apply andb_prop in H0 as [? ?] end.
  repeat match goal with H0 : Z.leb _ _ = true |- _ => apply Z.leb_le in H0 end.
  fold s in Bp. fold n in Bm. pose proof (bv_unsigned_in_range _ (lden E mm)) as Rm. fold n in Rm.
  assert (Hs1 : 1 <= s) by lia. assert (Hn : 0 <= n <= 2^32) by lia. assert (Hsn : s + n <= 2^47) by lia.
  (* [comment removed for export] *)
  assert (Rmid : rg_ok ASEGS E (ms_mem msr) (RG p mm RW TEmpty)).
  { rewrite Forall_forall in HG. exact (HG _ (nth_error_In _ _ Hmid)). }
  assert (Hszm : rsz E (RG p mm RW TEmpty) = n) by reflexivity.
  assert (Bmid : forall x, s <= x < s + n -> rd1 ASEGS (ms_mem msr) (Z_to_bv 64 x) <> None /\ wview ASEGS (ms_mem msr) (Z_to_bv 64 x) <> None).
  { intros x Hx. apply (rg_rw_pt _ _ _ x Rmid eq_refl). cbn [rg_base]. rewrite Hszm. exact Hx. }
  assert (HW : forall d k, 0 <= d -> d + Z.of_nat k <= n -> store_ok ASEGS (ms_mem msr) (wa (s + d)) k = true).
  { intros d k Hd' Hk'. apply store_ok_of_all; [rewrite u_wa_small by lia; lia|].
    intros x Hx. rewrite u_wa_small in Hx by lia. pose proof (bv_unsigned_in_range _ x) as Rx.
    destruct (Bmid (bv_unsigned x) ltac:(lia)) as [_ W]. rewrite Z_to_bv_bv_unsigned in W. exact W. }
  (* [comment removed for export] *)
  destruct (@memset0_contract (mkFP (ms_fregs ms) (ms_fcsr ms)) (ms_rom ms) (ms_regs ms) (ms_mem msr) s n) as (R' & m' & Hms & HK & HZ & HFr & Hgr).
  all: try (replace (10%bv : reg) with (Z_to_bv 5 10) by (apply bv_eq; reflexivity); exact Rs).
  all: try (replace (11%bv : reg) with (Z_to_bv 5 11) by (apply bv_eq; reflexivity); exact R11).
  all: try (replace (12%bv : reg) with (Z_to_bv 5 12) by (apply bv_eq; reflexivity); exact Rn).
  all: try exact HW.
  all: try lia.
  all: match goal with |- realizes_cfg _ _ _ _ => idtac | |- ?G => idtac "REMAIN" G; fail end.
  set (fx1 := mkFP (ms_fregs ms) (ms_fcsr ms)).
  set (msr' := @mkst fx1 R' (wa 0xd49f8) m' (ms_rom ms)).
  assert (Hst : isteps ASEGS msr msr').
  { unfold msr. rewrite (restrict_mkst H ms Hsvc Hrv), Hpc1. apply isteps_of_msteps. exact Hms. }
  (* [comment removed for export] *)
  assert (Hin_mid : forall x, (exists i0 R0, In i0 [jm] /\ nth_error (s_rgs S1) i0 = Some R0 /\ in_rg E R0 x) -> s <= bv_unsigned x < s + n).
  { intros x (i0 & R0 & Hi0 & HR0 & Hin). destruct Hi0 as [<-|[]]. rewrite Hmid in HR0. injection HR0 as <-.
    unfold in_rg in Hin. rewrite Hszm in Hin. exact Hin. }
  rewrite <- (mrg_nil S1) in Hd1.
  apply (den_hand_q0 ASEGS cfg LIMIT model0 mem0 Hwx S1 Snil E M ms model T 0xd49f8 KMSk [jm] msr' Hd1 Hwf1).
  - intros i0 R0 Hi0 HR0. destruct Hi0 as [<-|[]]. rewrite Hmid in HR0. injection HR0 as <-. discriminate.
  - exact Hst.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - intros r Hr. destruct (kms_cases r Hr) as (k & Hk' & ->). change (ms_regs msr') with R'. exact (HK k Hk').
  - intros x Hx. cbn [msr' mkst ms_mem]. rewrite <- (wa_u x). apply HFr; [apply bv_unsigned_in_range|].
    intros Hc. apply Hx. exists jm, (RG p mm RW TEmpty). split; [left; reflexivity|]. split; [exact Hmid|].
    unfold in_rg. cbn [rg_base]. rewrite Hszm. exact Hc.
  - intros i0 R0 j Hi0 HR0 Hj. destruct Hi0 as [<-|[]]. rewrite Hmid in HR0. injection HR0 as <-.
    rewrite Hszm in Hj. cbn [rg_base]. fold s. destruct (Bmid (s + j) ltac:(lia)) as [B1' B2'].
    destruct (grows_rw ASEGS (ms_mem msr) m' (Z_to_bv 64 (s + j)) Hgr B1' B2') as [C1 C2].
    split; [exact C1 | intros _; exact C2].
  - (* [comment removed for export] *)
    intros E' ms' model' HD' Ha' Hvis. rewrite mrg_nil in HD'.
    assert (Ha0 : agree (s_next S) E E') by (rewrite <- E1n; exact Ha').
    assert (Hmid2 : nth_error (s_rgs (hand_post S1 0xd49f8 KMSk [jm])) jm = Some (RG p mm RW TEmpty)).
    { cbn [hand_post s_rgs]. rewrite nth_error_empty_at, Hmid. cbn [Nat.add existsb orb]. rewrite Nat.eqb_refl. reflexivity. }
    pose proof (dn_hoff _ _ _ _ _ _ _ _ _ Hd1) as Hoff.
    apply (Hk E' mem0 ms' model' Ha0).
    + intros q0 Hq0 w Hw. reflexivity.
    + apply (den_rz_zero ASEGS LIMIT mem0 model0 E' _ M ms' model' jm (RG p mm RW TEmpty) S3 HD' Hmid2 HS3).
      intros j Hj. unfold rsz in Hj. cbn [rg_size rg_base] in Hj |- *.
      assert (Es : uE E' p = s) by exact (uE_agree (s_next S) E E' p Hlp Ha0).
      assert (En : bv_unsigned (lden E' mm) = n) by exact (uE_agree (s_next S) E E' mm Hlm Ha0).
      rewrite Es. rewrite En in Hj.
      assert (Hv : H (Z_to_bv 64 (s + j)) = false).
      { pose proof (rg_ok_visible ASEGS H (ms_mem ms) E (RG p mm RW TEmpty) Hoff Rmid j ltac:(rewrite Hszm; lia)) as X.
        cbn [rg_base] in X. exact X. }
      rewrite (Hvis _ Hv). cbn [msr' mkst ms_mem]. change (Z_to_bv 64 (s + j)) with (wa (s + j)). apply HZ. lia.
    + exact (HA_agree (s_next S) E E' M a mem0 HwfM Haw Ha0 HHA).
Qed.
End MsetNode.

(* [comment removed for export] *)
Definition apost_msetc (S : sst) (M : smodel) (a : ast) : option (sst * smodel * ast) :=
  let p := rget (s_regs S) (rk 10) in let mm := rget (s_regs S) (rk 12) in
  obool (Z.eqb (s_pc S) 0xd4904 && rsv_none_b (s_resv S) && mset_rng_ok (s_facts S) p mm)%bool (
  obind (msplit S p mm) (fun sj =>
  obool (state_wf (fst sj)) (
  Some (hand_post (fst sj) 0xd49f8 KMSk [snd sj], M, a)))).
Lemma apost_msetc_unf : forall S M a,
  (let p := rget (s_regs S) (rk 10) in let mm := rget (s_regs S) (rk 12) in
  obool (Z.eqb (s_pc S) 0xd4904 && rsv_none_b (s_resv S) && mset_rng_ok (s_facts S) p mm)%bool (
  obind (msplit S p mm) (fun sj =>
  obool (state_wf (fst sj)) (
  Some (hand_post (fst sj) 0xd49f8 KMSk [snd sj], M, a))))) = apost_msetc S M a.
Proof. intros. exact eq_refl. Qed.

Section MsetcNode.
Variable cfg : SpuriousCfg.
Variable LIMIT : Z.
Variable model0 : Model.
Hypothesis Hwx : wx_segs_nowrap ASEGS.

#[using="Hwx"] Theorem msetc_node : forall S M a S' M' a', apost_msetc S M a = Some (S', M', a') ->
  forall mem0 E ms model T, DEN ASEGS LIMIT model0 mem0 E S M ms model -> awf (s_next S) a = true -> HA E M a mem0 ->
  (forall E' mem0' ms' model', agree (s_next S) E E' -> frz_same E M mem0 mem0' -> DEN ASEGS LIMIT model0 mem0' E' S' M' ms' model' ->
     HA E' M' a' mem0' -> realizes_cfg ASEGS cfg (mkCfg ms' model') T) ->
  realizes_cfg ASEGS cfg (mkCfg ms model) T.
Proof. LiaFast.lf_pins (fun (Hwx : LiaFast.U) => LiaFast.u0).
  intros S M a S' M' a' H mem0 E ms model T Hd Haw HHA Hk.
  rewrite <- apost_msetc_unf in H. cbv zeta in H.
  apply obool_some in H as (Hchk & H).
  apply obind_some in H as ([S1 jm] & HS1 & H). cbv beta in H. cbn [fst snd] in H.
  apply obool_some in H as (Hwf1 & H). injection H as <- <- <-.
  apply andb_prop in Hchk as [Hchk Hrng]. apply andb_prop in Hchk as [Hpc Hrsv].
  apply Z.eqb_eq in Hpc. apply rsv_none_b_sound in Hrsv.
  set (p := rget (s_regs S) (rk 10)) in *. set (mm := rget (s_regs S) (rk 12)) in *.
  (* [comment removed for export] *)
  destruct (msplit_sound ASEGS LIMIT mem0 model0 E S M ms model p mm S1 jm HS1 Hd) as (Hd1 & E1pc & E1r & E1f & E1n & E1v & Hmid & Hlp & Hlm).
  pose proof (dn_wf _ _ _ _ _ _ _ _ _ Hd) as HwfM.
  pose proof (dn_sden _ _ _ _ _ _ _ _ _ Hd1) as Hsd1.
  set (H := Hof E M model) in *. set (msr := restrict H ms) in *.
  pose proof (sden_0 _ _ _ _ Hsd1) as Hd0.
  destruct Hd0 as (Hpc0 & Hsvc & Hrv0 & HR & HG & _ & HF & _).
  assert (Hrv : ms_resv ms = None) by (rewrite E1v, Hrsv in Hrv0; cbn [rsv_ok] in Hrv0; exact Hrv0).
  assert (Hpc1 : ms_pc_val ms = wa 0xd4904) by (rewrite E1pc, Hpc in Hpc0; exact Hpc0).
  rewrite E1f in HF.
  set (s := bv_unsigned (lden E p)). set (n := bv_unsigned (lden E mm)).
  assert (Rs : getr (ms_regs ms) (Z_to_bv 5 10) = wa s).
  { change (ms_regs ms) with (ms_regs msr). rewrite (HR (Z_to_bv 5 10)), E1r. unfold s, wa. rewrite Z_to_bv_bv_unsigned. reflexivity. }
  assert (Rn : getr (ms_regs ms) (Z_to_bv 5 12) = wa n).
  { change (ms_regs ms) with (ms_regs msr). rewrite (HR (Z_to_bv 5 12)), E1r. unfold n, wa. rewrite Z_to_bv_bv_unsigned. reflexivity. }
  pose proof (irange_sound E (s_facts S) p HF) as Bp. pose proof (irange_sound E (s_facts S) mm HF) as Bm.
  unfold mset_rng_ok in Hrng. repeat match goal with H0 : (_ && _)%bool = true |- _ => apply andb_prop in H0 as [? ?] end.
  repeat match goal with H0 : Z.leb _ _ = true |- _ => apply Z.leb_le in H0 end.
  fold s in Bp. fold n in Bm. pose proof (bv_unsigned_in_range _ (lden E mm)) as Rm. fold n in Rm.
  assert (Hs1 : 1 <= s) by lia. assert (Hn : 0 <= n <= 2^32) by lia. assert (Hsn : s + n <= 2^47) by lia.
  assert (Rmid : rg_ok ASEGS E (ms_mem msr) (RG p mm RW TEmpty)).
  { rewrite Forall_forall in HG. exact (HG _ (nth_error_In _ _ Hmid)). }
  assert (Hszm : rsz E (RG p mm RW TEmpty) = n) by reflexivity.
  assert (Bmid : forall x, s <= x < s + n -> rd1 ASEGS (ms_mem msr) (Z_to_bv 64 x) <> None /\ wview ASEGS (ms_mem msr) (Z_to_bv 64 x) <> None).
  { intros x Hx. apply (rg_rw_pt _ _ _ x Rmid eq_refl). cbn [rg_base]. rewrite Hszm. exact Hx. }
  assert (HW : forall d k, 0 <= d -> d + Z.of_nat k <= n -> store_ok ASEGS (ms_mem msr) (wa (s + d)) k = true).
  { intros d k Hd' Hk'. apply store_ok_of_all; [rewrite u_wa_small by lia; lia|].
    intros x Hx. rewrite u_wa_small in Hx by lia. pose proof (bv_unsigned_in_range _ x) as Rx.
    destruct (Bmid (bv_unsigned x) ltac:(lia)) as [_ W]. rewrite Z_to_bv_bv_unsigned in W. exact W. }
  destruct (@memsetck_contract (mkFP (ms_fregs ms) (ms_fcsr ms)) (ms_rom ms) (ms_regs ms) (ms_mem msr) s n) as (R' & m' & Hms & HK & _ & HFr & Hgr).
  all: try (replace (10%bv : reg) with (Z_to_bv 5 10) by (apply bv_eq; reflexivity); exact Rs).
  all: try (replace (12%bv : reg) with (Z_to_bv 5 12) by (apply bv_eq; reflexivity); exact Rn).
  all: try exact HW.
  all: try lia.
  all: match goal with |- realizes_cfg _ _ _ _ => idtac | |- ?G => idtac "REMAIN" G; fail end.
  set (fx1 := mkFP (ms_fregs ms) (ms_fcsr ms)).
  set (msr' := @mkst fx1 R' (wa 0xd49f8) m' (ms_rom ms)).
  assert (Hst : isteps ASEGS msr msr').
  { unfold msr. rewrite (restrict_mkst H ms Hsvc Hrv), Hpc1. apply isteps_of_msteps. exact Hms. }
  rewrite <- (mrg_nil S1) in Hd1.
  apply (den_hand_q0 ASEGS cfg LIMIT model0 mem0 Hwx S1 Snil E M ms model T 0xd49f8 KMSk [jm] msr' Hd1 Hwf1).
  - intros i0 R0 Hi0 HR0. destruct Hi0 as [<-|[]]. rewrite Hmid in HR0. injection HR0 as <-. discriminate.
  - exact Hst.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - intros r Hr. destruct (kms_cases r Hr) as (k & Hk' & ->). change (ms_regs msr') with R'. exact (HK k Hk').
  - intros x Hx. cbn [msr' mkst ms_mem]. rewrite <- (wa_u x). apply HFr; [apply bv_unsigned_in_range|].
    intros Hc. apply Hx. exists jm, (RG p mm RW TEmpty). split; [left; reflexivity|]. split; [exact Hmid|].
    unfold in_rg. cbn [rg_base]. rewrite Hszm. exact Hc.
  - intros i0 R0 j Hi0 HR0 Hj. destruct Hi0 as [<-|[]]. rewrite Hmid in HR0. injection HR0 as <-.
    rewrite Hszm in Hj. cbn [rg_base]. fold s. destruct (Bmid (s + j) ltac:(lia)) as [B1' B2'].
    destruct (grows_rw ASEGS (ms_mem msr) m' (Z_to_bv 64 (s + j)) Hgr B1' B2') as [C1 C2].
    split; [exact C1 | intros _; exact C2].
  - intros E' ms' model' HD' Ha' _. rewrite mrg_nil in HD'.
    assert (Ha0 : agree (s_next S) E E') by (rewrite <- E1n; exact Ha').
    apply (Hk E' mem0 ms' model' Ha0).
    + intros q0 Hq0 w Hw. reflexivity.
    + exact HD'.
    + exact (HA_agree (s_next S) E E' M a mem0 HwfM Haw Ha0 HHA).
Qed.
End MsetcNode.

(* [comment removed for export] *)
Fixpoint put_bks (t : tree bval) (ks : list Z) (b : Z) : tree bval :=
  match ks with [] => t | k :: ks' => put_bks (tset (okey k) (BK b) t) ks' b end.
Lemma tget_put_bks : forall ks t b p, tget p (put_bks t ks b) = if existsb (fun k => Pos.eqb p (okey k)) ks then Some (BK b) else tget p t.
Proof.
  induction ks as [|k ks IH]; intros t b p; [reflexivity|]. cbn [put_bks existsb]. rewrite IH.
  destruct (existsb (fun k0 => Pos.eqb p (okey k0)) ks) eqn:E1; [rewrite orb_true_r; reflexivity|]. rewrite orb_false_r.
  destruct (Pos.eqb p (okey k)) eqn:E2.
  - apply Pos.eqb_eq in E2. subst p. rewrite tget_tset_same. reflexivity.
  - apply Pos.eqb_neq in E2. rewrite tget_tset_other by (intros X; apply E2; symmetry; exact X). reflexivity.
Qed.
Definition keep_ok (ks : list Z) (lo : Z) : bool := forallb (fun k => Z.leb 0 k && Z.ltb k lo)%bool ks.
Definition track_post (S : sst) (j : nat) (ks : list Z) (b : Z) : option sst :=
  match nth_error (s_rgs S) j with
  | Some R => if rkind_eqb (rg_kind R) RW
              then Some (with_rgs S (firstn j (s_rgs S) ++ RG (rg_base R) (rg_size R) RW (put_bks (rg_cont R) ks b) :: skipn (Datatypes.S j) (s_rgs S)))
              else None
  | None => None
  end.
Lemma nth_split : forall {A} (l : list A) j x, nth_error l j = Some x -> l = firstn j l ++ x :: skipn (Datatypes.S j) l.
Proof.
  intros A l. induction l as [|y l IH]; intros [|j] x H; cbn [nth_error] in H; try discriminate.
  - injection H as <-. reflexivity.
  - cbn [firstn skipn app]. f_equal. exact (IH j x H).
Qed.

Section Track.
Variable segs : list Segment.
Variable LIMIT : Z.
Variable model0 : Model.
Variable mem0 : word -> option byte.
(* [comment removed for export] *)
#[using="Type"] Theorem den_track : forall E S M ms model j R ks b S', DEN segs LIMIT model0 mem0 E S M ms model ->
  nth_error (s_rgs S) j = Some R -> track_post S j ks b = Some S' ->
  (forall E', agree (s_next S) E E' -> forall k, In k ks -> 0 <= k < rsz E' R /\ uE E' (rg_base R) = uE E (rg_base R)) ->
  (forall k, In k ks -> rd1 segs (ms_mem (restrict (Hof E M model) ms)) (Z_to_bv 64 (uE E (rg_base R) + k)) = Some (Z_to_bv 8 b)) ->
  DEN segs LIMIT model0 mem0 E S' M ms model.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros E S M ms model j R ks b S' Hd Hj Hp Hks Hm. unfold track_post in Hp. rewrite Hj in Hp.
  destruct (rkind_eqb (rg_kind R) RW) eqn:Hk; [|discriminate]. injection Hp as <-.
  assert (HkR : rg_kind R = RW) by (destruct (rg_kind R); try discriminate; reflexivity).
  apply (den_track_rg segs LIMIT model0 mem0 E S M ms model (firstn j (s_rgs S)) R (skipn (Datatypes.S j) (s_rgs S)) (RG (rg_base R) (rg_size R) RW (put_bks (rg_cont R) ks b)) Hd (nth_split _ j R Hj) eq_refl eq_refl).
  intros E' Ha Hok. unfold rg_ok in *. cbv zeta in *. cbn [rg_base rg_size rg_kind rg_cont] in *. rewrite HkR in Hok.
  destruct Hok as (P1 & P2 & P3 & P4). fold (rsz E' R) in *.
  split; [exact P1|]. split; [exact P2|]. split; [exact P3|].
  intros p v Hpv. rewrite tget_put_bks in Hpv. destruct (existsb (fun k => Pos.eqb p (okey k)) ks) eqn:Hex; [|exact (P4 p v Hpv)].
  injection Hpv as <-. apply existsb_exists in Hex as (k & Hkin & Hkp). apply Pos.eqb_eq in Hkp. subst p.
  destruct (Hks E' Ha k Hkin) as [Hkr Hb]. unfold okey. rewrite Z2Pos.id by lia. replace (k + 1 - 1) with k by lia.
  split; [unfold rsz in *; cbn [rg_size] in *; lia|]. fold (uE E' (rg_base R)). rewrite Hb. cbn [bden]. exact (Hm k Hkin).
Qed.
End Track.

Definition apost_msetk (keep : list Z) (S : sst) (M : smodel) (a : ast) : option (sst * smodel * ast) :=
  let p := rget (s_regs S) (rk 10) in let mm := rget (s_regs S) (rk 12) in
  obool (Z.eqb (s_pc S) 0xd4904 && rsv_none_b (s_resv S) && mset_rng_ok (s_facts S) p mm && keep_ok keep (fst (irange (s_facts S) mm)))%bool (
  obind (is_const (rget (s_regs S) (rk 11))) (fun c =>
  obool (Z.ltb c 256) (
  obind (msplit S p mm) (fun sj =>
  obool (state_wf (fst sj)) (
  obind (track_post (hand_post (fst sj) 0xd49f8 KMSk [snd sj]) (snd sj) keep c) (fun S3 =>
  Some (S3, M, a))))))).
Lemma apost_msetk_unf : forall keep S M a,
  (let p := rget (s_regs S) (rk 10) in let mm := rget (s_regs S) (rk 12) in
  obool (Z.eqb (s_pc S) 0xd4904 && rsv_none_b (s_resv S) && mset_rng_ok (s_facts S) p mm && keep_ok keep (fst (irange (s_facts S) mm)))%bool (
  obind (is_const (rget (s_regs S) (rk 11))) (fun c =>
  obool (Z.ltb c 256) (
  obind (msplit S p mm) (fun sj =>
  obool (state_wf (fst sj)) (
  obind (track_post (hand_post (fst sj) 0xd49f8 KMSk [snd sj]) (snd sj) keep c) (fun S3 =>
  Some (S3, M, a)))))))) = apost_msetk keep S M a.
Proof. intros. exact eq_refl. Qed.

Section MsetkNode.
Variable cfg : SpuriousCfg.
Variable LIMIT : Z.
Variable model0 : Model.
Hypothesis Hwx : wx_segs_nowrap ASEGS.

#[using="Hwx"] Theorem msetk_node : forall keep S M a S' M' a', apost_msetk keep S M a = Some (S', M', a') ->
  forall mem0 E ms model T, DEN ASEGS LIMIT model0 mem0 E S M ms model -> awf (s_next S) a = true -> HA E M a mem0 ->
  (forall E' mem0' ms' model', agree (s_next S) E E' -> frz_same E M mem0 mem0' -> DEN ASEGS LIMIT model0 mem0' E' S' M' ms' model' ->
     HA E' M' a' mem0' -> realizes_cfg ASEGS cfg (mkCfg ms' model') T) ->
  realizes_cfg ASEGS cfg (mkCfg ms model) T.
Proof. LiaFast.lf_pins (fun (Hwx : LiaFast.U) => LiaFast.u0).
  intros keep S M a S' M' a' H mem0 E ms model T Hd Haw HHA Hk.
  rewrite <- apost_msetk_unf in H. cbv zeta in H.
  apply obool_some in H as (Hchk & H).
  apply obind_some in H as (c & Hc & H). cbv beta in H.
  apply obool_some in H as (Hc256 & H). apply Z.ltb_lt in Hc256.
  apply obind_some in H as ([S1 jm] & HS1 & H). cbv beta in H. cbn [fst snd] in H.
  apply obool_some in H as (Hwf1 & H).
  apply obind_some in H as (S3 & HS3 & H). injection H as <- <- <-.
  apply andb_prop in Hchk as [Hchk Hkeep]. apply andb_prop in Hchk as [Hchk Hrng]. apply andb_prop in Hchk as [Hpc Hrsv].
  apply Z.eqb_eq in Hpc. apply rsv_none_b_sound in Hrsv.
  set (p := rget (s_regs S) (rk 10)) in *. set (mm := rget (s_regs S) (rk 12)) in *.
  destruct (msplit_sound ASEGS LIMIT mem0 model0 E S M ms model p mm S1 jm HS1 Hd) as (Hd1 & E1pc & E1r & E1f & E1n & E1v & Hmid & Hlp & Hlm).
  pose proof (dn_wf _ _ _ _ _ _ _ _ _ Hd) as HwfM.
  pose proof (dn_sden _ _ _ _ _ _ _ _ _ Hd1) as Hsd1.
  set (H := Hof E M model) in *. set (msr := restrict H ms) in *.
  pose proof (sden_0 _ _ _ _ Hsd1) as Hd0.
  destruct Hd0 as (Hpc0 & Hsvc & Hrv0 & HR & HG & _ & HF & _).
  assert (Hrv : ms_resv ms = None) by (rewrite E1v, Hrsv in Hrv0; cbn [rsv_ok] in Hrv0; exact Hrv0).
  assert (Hpc1 : ms_pc_val ms = wa 0xd4904) by (rewrite E1pc, Hpc in Hpc0; exact Hpc0).
  rewrite E1f in HF.
  set (s := bv_unsigned (lden E p)). set (n := bv_unsigned (lden E mm)).
  assert (Rs : getr (ms_regs ms) (Z_to_bv 5 10) = wa s).
  { change (ms_regs ms) with (ms_regs msr). rewrite (HR (Z_to_bv 5 10)), E1r. unfold s, wa. rewrite Z_to_bv_bv_unsigned. reflexivity. }
  assert (Rn : getr (ms_regs ms) (Z_to_bv 5 12) = wa n).
  { change (ms_regs ms) with (ms_regs msr). rewrite (HR (Z_to_bv 5 12)), E1r. unfold n, wa. rewrite Z_to_bv_bv_unsigned. reflexivity. }
  assert (Rc : bv_unsigned (getr (ms_regs ms) 11) mod 256 = c).
  { change (ms_regs ms) with (ms_regs msr). replace (11%bv : reg) with (Z_to_bv 5 11) by (apply bv_eq; reflexivity).
    rewrite (HR (Z_to_bv 5 11)), E1r. change (rkey (Z_to_bv 5 11)) with (rk 11).
    rewrite (is_const_u E _ c Hc). pose proof (proj2 (is_const_sound E _ c Hc)) as X. rewrite Z.mod_small; [reflexivity | lia]. }
  pose proof (irange_sound E (s_facts S) p HF) as Bp. pose proof (irange_sound E (s_facts S) mm HF) as Bm.
  unfold mset_rng_ok in Hrng. repeat match goal with H0 : (_ && _)%bool = true |- _ => apply andb_prop in H0 as [? ?] end.
  repeat match goal with H0 : Z.leb _ _ = true |- _ => apply Z.leb_le in H0 end.
  fold s in Bp. fold n in Bm. pose proof (bv_unsigned_in_range _ (lden E mm)) as Rm. fold n in Rm.
  assert (Hs1 : 1 <= s) by lia. assert (Hn : 0 <= n <= 2^32) by lia. assert (Hsn : s + n <= 2^47) by lia.
  assert (Hkn : forall k, In k keep -> 0 <= k < n).
  { intros k Hkin. unfold keep_ok in Hkeep. rewrite forallb_forall in Hkeep. specialize (Hkeep k Hkin).
    apply andb_prop in Hkeep as [K1 K2]. apply Z.leb_le in K1. apply Z.ltb_lt in K2. lia. }
  assert (Rmid : rg_ok ASEGS E (ms_mem msr) (RG p mm RW TEmpty)).
  { rewrite Forall_forall in HG. exact (HG _ (nth_error_In _ _ Hmid)). }
  assert (Hszm : rsz E (RG p mm RW TEmpty) = n) by reflexivity.
  assert (Bmid : forall x, s <= x < s + n -> rd1 ASEGS (ms_mem msr) (Z_to_bv 64 x) <> None /\ wview ASEGS (ms_mem msr) (Z_to_bv 64 x) <> None).
  { intros x Hx. apply (rg_rw_pt _ _ _ x Rmid eq_refl). cbn [rg_base]. rewrite Hszm. exact Hx. }
  assert (HW : forall d k, 0 <= d -> d + Z.of_nat k <= n -> store_ok ASEGS (ms_mem msr) (wa (s + d)) k = true).
  { intros d k Hd' Hk'. apply store_ok_of_all; [rewrite u_wa_small by lia; lia|].
    intros x Hx. rewrite u_wa_small in Hx by lia. pose proof (bv_unsigned_in_range _ x) as Rx.
    destruct (Bmid (bv_unsigned x) ltac:(lia)) as [_ W]. rewrite Z_to_bv_bv_unsigned in W. exact W. }
  destruct (@memsetck_contract (mkFP (ms_fregs ms) (ms_fcsr ms)) (ms_rom ms) (ms_regs ms) (ms_mem msr) s n) as (R' & m' & Hms & HK & HV & HFr & Hgr).
  all: try (replace (10%bv : reg) with (Z_to_bv 5 10) by (apply bv_eq; reflexivity); exact Rs).
  all: try (replace (12%bv : reg) with (Z_to_bv 5 12) by (apply bv_eq; reflexivity); exact Rn).
  all: try exact HW.
  all: try lia.
  all: match goal with |- realizes_cfg _ _ _ _ => idtac | |- ?G => idtac "REMAIN" G; fail end.
  rewrite Rc in HV.
  set (fx1 := mkFP (ms_fregs ms) (ms_fcsr ms)).
  set (msr' := @mkst fx1 R' (wa 0xd49f8) m' (ms_rom ms)).
  assert (Hst : isteps ASEGS msr msr').
  { unfold msr. rewrite (restrict_mkst H ms Hsvc Hrv), Hpc1. apply isteps_of_msteps. exact Hms. }
  rewrite <- (mrg_nil S1) in Hd1.
  apply (den_hand_q0 ASEGS cfg LIMIT model0 mem0 Hwx S1 Snil E M ms model T 0xd49f8 KMSk [jm] msr' Hd1 Hwf1).
  - intros i0 R0 Hi0 HR0. destruct Hi0 as [<-|[]]. rewrite Hmid in HR0. injection HR0 as <-. discriminate.
  - exact Hst.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - intros r Hr. destruct (kms_cases r Hr) as (k & Hk' & ->). change (ms_regs msr') with R'. exact (HK k Hk').
  - intros x Hx. cbn [msr' mkst ms_mem]. rewrite <- (wa_u x). apply HFr; [apply bv_unsigned_in_range|].
    intros Hc'. apply Hx. exists jm, (RG p mm RW TEmpty). split; [left; reflexivity|]. split; [exact Hmid|].
    unfold in_rg. cbn [rg_base]. rewrite Hszm. exact Hc'.
  - intros i0 R0 j Hi0 HR0 Hj. destruct Hi0 as [<-|[]]. rewrite Hmid in HR0. injection HR0 as <-.
    rewrite Hszm in Hj. cbn [rg_base]. fold s. destruct (Bmid (s + j) ltac:(lia)) as [B1' B2'].
    destruct (grows_rw ASEGS (ms_mem msr) m' (Z_to_bv 64 (s + j)) Hgr B1' B2') as [C1 C2].
    split; [exact C1 | intros _; exact C2].
  - (* [comment removed for export] *)
    intros E' ms' model' HD' Ha' Hvis. rewrite mrg_nil in HD'.
    assert (Ha0 : agree (s_next S) E E') by (rewrite <- E1n; exact Ha').
    assert (Hmid2 : nth_error (s_rgs (hand_post S1 0xd49f8 KMSk [jm])) jm = Some (RG p mm RW TEmpty)).
    { cbn [hand_post s_rgs]. rewrite nth_error_empty_at, Hmid. cbn [Nat.add existsb orb]. rewrite Nat.eqb_refl. reflexivity. }
    pose proof (dn_hoff _ _ _ _ _ _ _ _ _ Hd1) as Hoff.
    pose proof (dn_hoff _ _ _ _ _ _ _ _ _ HD') as Hoff'.
    assert (Es : uE E' p = s) by exact (uE_agree (s_next S) E E' p Hlp Ha0).
    assert (Rmid' : rg_ok ASEGS E' (ms_mem (restrict (Hof E' M model') ms')) (RG p mm RW TEmpty)).
    { pose proof (sden_0 _ _ _ _ (dn_sden _ _ _ _ _ _ _ _ _ HD')) as (_ & _ & _ & _ & HG' & _).
      rewrite Forall_forall in HG'. exact (HG' _ (nth_error_In _ _ Hmid2)). }
    apply (Hk E' mem0 ms' model' Ha0).
    + intros q0 Hq0 w Hw. reflexivity.
    + apply (den_track ASEGS LIMIT model0 mem0 E' _ M ms' model' jm (RG p mm RW TEmpty) keep c S3 HD' Hmid2 HS3).
      * intros E'' Ha'' k Hkin. cbn [hand_post s_next] in Ha''.
        assert (Ha3 : agree (s_next S) E E'') by (apply (agree_trans _ E E' E''); [exact Ha0 | intros x Hx; apply Ha''; rewrite E1n in *; lia]).
        split.
        -- unfold rsz. cbn [rg_size]. rewrite (lden_agree_wf (s_next S) E E'' mm Hlm Ha3). fold n. exact (Hkn k Hkin).
        -- cbn [rg_base]. rewrite (uE_agree (s_next S) E E'' p Hlp Ha3), Es. reflexivity.
      * intros k Hkin. cbn [rg_base]. rewrite Es. pose proof (Hkn k Hkin) as Hk'.
        assert (Hv' : Hof E' M model' (Z_to_bv 64 (s + k)) = false).
        { pose proof (rg_ok_visible ASEGS (Hof E' M model') (ms_mem ms') E' (RG p mm RW TEmpty) Hoff' Rmid' k) as X.
          cbn [rg_base] in X. rewrite Es in X. apply X. unfold rsz. cbn [rg_size]. rewrite (lden_agree_wf (s_next S) E E' mm Hlm Ha0). fold n. lia. }
        assert (Hv : H (Z_to_bv 64 (s + k)) = false).
        { pose proof (rg_ok_visible ASEGS H (ms_mem ms) E (RG p mm RW TEmpty) Hoff Rmid k ltac:(rewrite Hszm; lia)) as X.
          cbn [rg_base] in X. exact X. }
        cbn [restrict ms_mem]. unfold rd1, mrestrict. cbv beta. rewrite Hv'.
        rewrite (Hvis _ Hv). cbn [msr' mkst ms_mem]. change (Z_to_bv 64 (s + k)) with (wa (s + k)). rewrite (HV (s + k) ltac:(lia)). reflexivity.
    + exact (HA_agree (s_next S) E E' M a mem0 HwfM Haw Ha0 HHA).
Qed.
End MsetkNode.
(* [comment removed for export] *)
End AcMset.

Import OSSVerify.Proofs.fast_float.from_chars.lib.AACB.AcAst OSSVerify.Proofs.fast_float.from_chars.lib.AACB.AcHA OSSVerify.Proofs.fast_float.from_chars.lib.AACB.AcPri.AcDepSep OSSVerify.Proofs.fast_float.from_chars.lib.AACB.AcMALlib OSSVerify.Proofs.fast_float.from_chars.lib.AACB.AcConvG OSSVerify.Proofs.fast_float.from_chars.lib.AACB.AcPutN OSSVerify.Proofs.fast_float.from_chars.lib.AACB.AcUnwN OSSVerify.Proofs.fast_float.from_chars.lib.AACB.AcSysK.AcSysN OSSVerify.Proofs.fast_float.from_chars.lib.AACB.AcSysK OSSVerify.Proofs.fast_float.from_chars.lib.AACB.AcFam.AcSysS OSSVerify.Proofs.fast_float.from_chars.lib.AACB.AcFam.AcMset.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
Inductive anode : Type :=
| NConvG                   (* [comment removed for export] *)
| NUnw                     (* [comment removed for export] *)
| NPut                     (* [comment removed for export] *)
| NNullA (nZ : Z) (k : gkind) (vis piece na : bool)   (* [comment removed for export] *)
| NSepWA (i j : nat)                                  (* [comment removed for export] *)
| NFixA (n : Z) (j : nat)                             (* [comment removed for export] *)
| NFixKA (n : Z) (na : bool) (j : nat) (kd' : gkind)   (* [comment removed for export] *)
| NNullS (k : gkind) (vis piece na : bool)             (* [comment removed for export] *)
| NMset                                                (* [comment removed for export] *)
| NMsetC                                               (* [comment removed for export] *)
| NMsetK (keep : list Z).                              (* [comment removed for export] *)

Definition apost_alloc (LIMIT : Z) (nk : anode) (S : sst) (M : smodel) (a : ast) : option (sst * smodel * ast) :=
  match nk with
  | NConvG => apost_convG S M a
  | NUnw => apost_unw S M a
  | NPut => apost_put S M a
  | NNullA nZ k vis piece na => apost_nullA LIMIT nZ k vis piece na S M a
  | NSepWA i j => apost_sepwA i j S M a
  | NFixA n j => apost_fixA LIMIT n j S M a
  | NFixKA n na j kd' => apost_fixkA LIMIT n na j kd' S M a
  | NNullS k vis piece na => apost_nullS LIMIT k vis piece na S M a
  | NMset => apost_mset S M a
  | NMsetC => apost_msetc S M a
  | NMsetK keep => apost_msetk keep S M a
  end.
Definition acopy_alloc (a : ast) : list srec := [].

Section Fam.
Variable cfg : SpuriousCfg.
Variable LIMIT : Z.
Hypothesis Hwx : wx_segs_nowrap ASEGS.
Hypothesis Hsegb : segs_below_b ASEGS 0x800000000000 = true.
Hypothesis Hoff : sc_alloc cfg = false.
Hypothesis Hrespos : Forall (fun p => 0 < bv_unsigned (snd p)) (segments_reserved ASEGS).
Hypothesis Hreswf : ivs_wf (segments_reserved ASEGS).

#[using="Hwx Hsegb Hoff Hrespos Hreswf"] Theorem alloc_anode_ok : forall nk, anode_ok ASEGS cfg LIMIT (apost_alloc LIMIT) awf HA nk.
Proof. LiaFast.lf_pins (fun (Hwx Hsegb Hoff Hrespos Hreswf : LiaFast.U) => LiaFast.u0).
  intros [| | |nZ k vis piece na|i j|n j|n na j kd'|k vis piece na| | |keep] S M a S' M' a' H model0 mem0 E ms model T Hd Haw HHA Hk; cbn [apost_alloc] in H.
  - exact (convG_node cfg LIMIT model0 S M a S' M' a' H mem0 E ms model T Hd Haw HHA Hk).
  - exact (unw_node cfg LIMIT model0 Hwx S M a S' M' a' H mem0 E ms model T Hd Haw HHA Hk).
  - exact (put_node cfg LIMIT model0 Hwx S M a S' M' a' H mem0 E ms model T Hd Haw HHA Hk).
  - exact (nullA_node cfg LIMIT model0 Hwx Hsegb Hoff nZ k vis piece na S M a S' M' a' H mem0 E ms model T Hd Haw HHA Hk).
  - exact (sepwA_node cfg LIMIT model0 i j S M a S' M' a' H mem0 E ms model T Hd Haw HHA Hk).
  - exact (fixA_node cfg LIMIT model0 Hwx Hsegb Hoff Hrespos Hreswf n j S M a S' M' a' H mem0 E ms model T Hd Haw HHA Hk).
  - exact (fixkA_node cfg LIMIT model0 Hwx Hsegb Hoff Hrespos Hreswf n na j kd' S M a S' M' a' H mem0 E ms model T Hd Haw HHA Hk).
  - exact (nullS_node cfg LIMIT model0 Hwx Hsegb Hoff k vis piece na S M a S' M' a' H mem0 E ms model T Hd Haw HHA Hk).
  - exact (mset_node cfg LIMIT model0 Hwx S M a S' M' a' H mem0 E ms model T Hd Haw HHA Hk).
  - exact (msetc_node cfg LIMIT model0 Hwx S M a S' M' a' H mem0 E ms model T Hd Haw HHA Hk).
  - exact (msetk_node cfg LIMIT model0 Hwx keep S M a S' M' a' H mem0 E ms model T Hd Haw HHA Hk).
Qed.
End Fam.

(* [comment removed for export] *)
Lemma alloc_awf_mono : forall n n' a, (n <= n')%positive -> awf n a = true -> awf n' a = true.
Proof. exact awf_mono. Qed.
Lemma alloc_aeqb_eq : forall x y, aeqb x y = true -> x = y.
Proof. exact aeqb_eq. Qed.
Lemma alloc_HA_nil : forall E M a m0, anil a = true -> HA E M a m0.
Proof. exact HA_nil. Qed.
Lemma alloc_HA_agree : forall n E E' M a m0, sm_wf n M = true -> awf n a = true -> agree n E E' -> HA E M a m0 -> HA E' M a m0.
Proof. exact HA_agree. Qed.

Lemma alloc_HA_copy : forall (P : srec -> Prop) E M a m0, HA E M a m0 -> Forall P (acopy_alloc a).
Proof. intros P E M a m0 _. constructor. Qed.
(* [comment removed for export] *)
