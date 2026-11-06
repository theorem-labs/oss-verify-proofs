(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.fast_float.from_chars.images Require Import AsanUbsan.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec ShapeSet RealizesCfg AsanAcct PlacementCount AllocNodesCfg.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxLin FxCore FxSound FxMem FxFacts FxStep.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxLoop.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxSubst FxEnt FxPlan FxFrame FxDrv FxCall.
Import OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxLin OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxCore OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxSound OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxMem OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxFacts OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxStep OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxLoop.FxExplore OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxSubst OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxEnt OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxPlan OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxFrame OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxDrv OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxCall.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require Import AxMng.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXC Require Import FxBacking FxChDen FxChLib FxChSep FxChFix FxChEnt FxWvC FxChMain.
From OSSVerify.Proofs.fast_float.from_chars.lib.AAXB Require AXG_put AXG_put3 AXG_np AXG_nf1 AXG_npf AXG_gp AXG_gf1.
From OSSVerify.Proofs.fast_float.from_chars.lib.AACB Require AcPriStep.
Import OSSVerify.Proofs.fast_float.from_chars.lib.AAXB.AXG_put OSSVerify.Proofs.fast_float.from_chars.lib.AAXB.AXG_put3 OSSVerify.Proofs.fast_float.from_chars.lib.AAXB.AXG_np OSSVerify.Proofs.fast_float.from_chars.lib.AAXB.AXG_nf1 OSSVerify.Proofs.fast_float.from_chars.lib.AAXB.AXG_npf OSSVerify.Proofs.fast_float.from_chars.lib.AAXB.AXG_gp OSSVerify.Proofs.fast_float.from_chars.lib.AAXB.AXG_gf1 OSSVerify.Proofs.fast_float.from_chars.lib.AACB.AcPriStep.AXG_gpf.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXC Require FxChDen.
From OSSVerify.Proofs.fast_float.from_chars.lib.AACB Require AcHand.
From OSSVerify.Proofs.fast_float.from_chars.lib.AACB Require AcCarve AcSteps AcEntry AcMALp AcHand AcUnwApp0.
From OSSVerify.Proofs.fast_float.from_chars.lib.AACB Require AcUnwApp.
From OSSVerify.Proofs.fast_float.from_chars.lib.AACB Require AcShapes0.
From OSSVerify.Proofs.fast_float.from_chars.lib.AACB Require AcShapes0.
From OSSVerify.Proofs.fast_float.from_chars.lib.AACB Require AcShapes0.
From OSSVerify.Proofs.fast_float.from_chars.lib.AACB Require AcPri.
From OSSVerify.Proofs.fast_float.from_chars.lib.AACB Require AcDepDen AcAst AcHA AcFacts AcCarveP AcMALlib AcPutN AcUnwApp AcTbl.
From OSSVerify.Proofs.fast_float.from_chars.lib.AACB Require AcUnwApp.
From OSSVerify.Proofs.fast_float.from_chars.lib.AACB Require AcConv AcConvG.
From OSSVerify.Proofs.fast_float.from_chars.lib.AACB Require AcConvA.
From OSSVerify.Proofs.fast_float.from_chars.lib.AACB Require AcPri.
From OSSVerify.Proofs.fast_float.from_chars.lib.AACB Require AcPriSepOk.
From OSSVerify.Proofs.fast_float.from_chars.lib.AACB Require AcPriSepOk.
From OSSVerify.Proofs.fast_float.from_chars.lib.AACB Require AcConvA.
From OSSVerify.Proofs.fast_float.from_chars.lib.AACB Require AcPriStep AcPriHA.
From OSSVerify.Proofs.fast_float.from_chars.lib.AACB Require AcCarveP.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXC Require FxChMprot.
From OSSVerify.Proofs.fast_float.from_chars.lib.AACB Require AcOwnSet AcDenW AcConvA AcNPop.
From OSSVerify.Proofs.fast_float.from_chars.lib.AACB Require AcPriStep.
Import OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChDen.AcMrg OSSVerify.Proofs.fast_float.from_chars.lib.AACB.AcHand.AcMrg0 OSSVerify.Proofs.fast_float.from_chars.lib.AACB.AcCarve OSSVerify.Proofs.fast_float.from_chars.lib.AACB.AcSteps OSSVerify.Proofs.fast_float.from_chars.lib.AACB.AcEntry OSSVerify.Proofs.fast_float.from_chars.lib.AACB.AcMALp OSSVerify.Proofs.fast_float.from_chars.lib.AACB.AcHand OSSVerify.Proofs.fast_float.from_chars.lib.AACB.AcUnwApp0 OSSVerify.Proofs.fast_float.from_chars.lib.AACB.AcUnwApp.AcPutApp OSSVerify.Proofs.fast_float.from_chars.lib.AACB.AcShapes0.AcPutAppG OSSVerify.Proofs.fast_float.from_chars.lib.AACB.AcShapes0.AcShapes OSSVerify.Proofs.fast_float.from_chars.lib.AACB.AcShapes0 OSSVerify.Proofs.fast_float.from_chars.lib.AACB.AcPri.AcDepSep OSSVerify.Proofs.fast_float.from_chars.lib.AACB.AcDepDen OSSVerify.Proofs.fast_float.from_chars.lib.AACB.AcAst OSSVerify.Proofs.fast_float.from_chars.lib.AACB.AcHA OSSVerify.Proofs.fast_float.from_chars.lib.AACB.AcFacts OSSVerify.Proofs.fast_float.from_chars.lib.AACB.AcCarveP OSSVerify.Proofs.fast_float.from_chars.lib.AACB.AcMALlib OSSVerify.Proofs.fast_float.from_chars.lib.AACB.AcPutN OSSVerify.Proofs.fast_float.from_chars.lib.AACB.AcUnwApp OSSVerify.Proofs.fast_float.from_chars.lib.AACB.AcTbl OSSVerify.Proofs.fast_float.from_chars.lib.AACB.AcUnwApp.AcTblOk OSSVerify.Proofs.fast_float.from_chars.lib.AACB.AcConv OSSVerify.Proofs.fast_float.from_chars.lib.AACB.AcConvG OSSVerify.Proofs.fast_float.from_chars.lib.AACB.AcConvA.AcRdw OSSVerify.Proofs.fast_float.from_chars.lib.AACB.AcPri OSSVerify.Proofs.fast_float.from_chars.lib.AACB.AcPriSepOk.AcPriSep OSSVerify.Proofs.fast_float.from_chars.lib.AACB.AcPriSepOk OSSVerify.Proofs.fast_float.from_chars.lib.AACB.AcConvA.AcPriDen OSSVerify.Proofs.fast_float.from_chars.lib.AACB.AcPriStep OSSVerify.Proofs.fast_float.from_chars.lib.AACB.AcPriHA OSSVerify.Proofs.fast_float.from_chars.lib.AACB.AcCarveP.AcStepsOut OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChMprot.AcAddOwn OSSVerify.Proofs.fast_float.from_chars.lib.AACB.AcOwnSet OSSVerify.Proofs.fast_float.from_chars.lib.AACB.AcDenW OSSVerify.Proofs.fast_float.from_chars.lib.AACB.AcConvA OSSVerify.Proofs.fast_float.from_chars.lib.AACB.AcNPop OSSVerify.Proofs.fast_float.from_chars.lib.AACB.AcPriStep.AcNPopApp.
Import ListNotations.

Module AcConvAN.
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.fast_float.from_chars.images Require Import AsanUbsan.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec CatSim StoreOk ShapeSet RealizesCfg AsanAcct PlacementCount AllocNodesCfg AxSymRun3.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxLin FxCore.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxSound.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxSound FxMem FxRgs FxFacts FxStep.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxLoop.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxSubst FxEnt FxPlan FxFrame FxDrv FxCall.
Import OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxLin OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxCore OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxSound.FxGlue OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxSound OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxMem OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxRgs OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxFacts OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxStep OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxLoop.FxExplore OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxSubst OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxEnt OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxPlan OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxFrame OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxDrv OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxCall.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require Import AxMng.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXC Require FxBacking FxChDen FxChLib FxChSep FxChNull FxChFix FxChEnt FxWvC.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXC Require FxChStart.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXC Require FxChMain.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXC Require FxChMprot.
Import OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxBacking OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChDen OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChLib OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChSep OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChNull OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChFix OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChEnt OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxWvC OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChStart.FxChLoop OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChMain OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChMprot.FxChAllow.
From OSSVerify.Proofs.fast_float.from_chars.lib.AAXB Require Import AXG_put AXG_put3 AXG_np AXG_nf1 AXG_npf.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXC Require FxChDen.
From OSSVerify.Proofs.fast_float.from_chars.lib.AACB Require AcHand.
From OSSVerify.Proofs.fast_float.from_chars.lib.AACB Require AcCarve AcSteps AcEntry AcMALp AcHand.
From OSSVerify.Proofs.fast_float.from_chars.lib.AACB Require AcUnwApp.
From OSSVerify.Proofs.fast_float.from_chars.lib.AACB Require AcShapes0.
From OSSVerify.Proofs.fast_float.from_chars.lib.AACB Require AcPri.
From OSSVerify.Proofs.fast_float.from_chars.lib.AACB Require AcDepDen AcAst.
From OSSVerify.Proofs.fast_float.from_chars.lib.AACB Require AcHA.
From OSSVerify.Proofs.fast_float.from_chars.lib.AACB Require AcHA AcFacts AcCarveP AcMALlib AcTbl AcConv AcConvLib AcConvInvLib AcConvG.
From OSSVerify.Proofs.fast_float.from_chars.lib.AACB Require AcConvA.
From OSSVerify.Proofs.fast_float.from_chars.lib.AACB Require AcPri.
From OSSVerify.Proofs.fast_float.from_chars.lib.AACB Require AcPriSepOk.
From OSSVerify.Proofs.fast_float.from_chars.lib.AACB Require AcPriSepOk.
From OSSVerify.Proofs.fast_float.from_chars.lib.AACB Require AcConvA.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXC Require FxChMprot.
From OSSVerify.Proofs.fast_float.from_chars.lib.AACB Require AcOwnSet AcDenW AcConvA AcNPop AcPriStep.
Import OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChDen.AcMrg OSSVerify.Proofs.fast_float.from_chars.lib.AACB.AcHand.AcMrg0 OSSVerify.Proofs.fast_float.from_chars.lib.AACB.AcCarve OSSVerify.Proofs.fast_float.from_chars.lib.AACB.AcSteps OSSVerify.Proofs.fast_float.from_chars.lib.AACB.AcEntry OSSVerify.Proofs.fast_float.from_chars.lib.AACB.AcMALp OSSVerify.Proofs.fast_float.from_chars.lib.AACB.AcHand OSSVerify.Proofs.fast_float.from_chars.lib.AACB.AcUnwApp.AcPutApp OSSVerify.Proofs.fast_float.from_chars.lib.AACB.AcShapes0.AcShapes OSSVerify.Proofs.fast_float.from_chars.lib.AACB.AcPri.AcDepSep OSSVerify.Proofs.fast_float.from_chars.lib.AACB.AcDepDen OSSVerify.Proofs.fast_float.from_chars.lib.AACB.AcAst OSSVerify.Proofs.fast_float.from_chars.lib.AACB.AcHA.AcLv OSSVerify.Proofs.fast_float.from_chars.lib.AACB.AcHA OSSVerify.Proofs.fast_float.from_chars.lib.AACB.AcFacts OSSVerify.Proofs.fast_float.from_chars.lib.AACB.AcCarveP OSSVerify.Proofs.fast_float.from_chars.lib.AACB.AcMALlib OSSVerify.Proofs.fast_float.from_chars.lib.AACB.AcTbl OSSVerify.Proofs.fast_float.from_chars.lib.AACB.AcConv OSSVerify.Proofs.fast_float.from_chars.lib.AACB.AcConvLib OSSVerify.Proofs.fast_float.from_chars.lib.AACB.AcConvInvLib OSSVerify.Proofs.fast_float.from_chars.lib.AACB.AcConvG OSSVerify.Proofs.fast_float.from_chars.lib.AACB.AcConvA.AcRdw OSSVerify.Proofs.fast_float.from_chars.lib.AACB.AcPri OSSVerify.Proofs.fast_float.from_chars.lib.AACB.AcPriSepOk.AcPriSep OSSVerify.Proofs.fast_float.from_chars.lib.AACB.AcPriSepOk OSSVerify.Proofs.fast_float.from_chars.lib.AACB.AcConvA.AcPriDen OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChMprot.AcAddOwn OSSVerify.Proofs.fast_float.from_chars.lib.AACB.AcOwnSet OSSVerify.Proofs.fast_float.from_chars.lib.AACB.AcDenW OSSVerify.Proofs.fast_float.from_chars.lib.AACB.AcConvA OSSVerify.Proofs.fast_float.from_chars.lib.AACB.AcNPop OSSVerify.Proofs.fast_float.from_chars.lib.AACB.AcPriStep.
Import ListNotations.
Local Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
Lemma find_rg_acc'_sound : forall f l i0 i, find_rg_acc' f l i0 = Some i -> (i0 <= i)%nat /\ exists R, nth_error l (i - i0) = Some R /\ f R = true.
Proof.
  intros f l. induction l as [|R r IH]; intros i0 i H; cbn [find_rg_acc'] in H; [discriminate|].
  destruct (f R) eqn:Hf.
  - injection H as <-. split; [lia|]. exists R. rewrite Nat.sub_diag. split; [reflexivity | exact Hf].
  - destruct (IH _ _ H) as (Hle & R' & Hn & Hf'). split; [lia|]. exists R'. split; [|exact Hf'].
    replace (i - i0)%nat with (Datatypes.S (i - Datatypes.S i0)) by lia. exact Hn.
Qed.
Lemma find_gsz_acc_sound : forall gs z i0 j b, find_gsz_acc gs z i0 = Some (j, b) -> (i0 <= j)%nat /\ exists k, nth_error gs (j - i0) = Some (b, lconst z, k).
Proof.
  induction gs as [|g r IH]; intros z i0 j b H; cbn [find_gsz_acc] in H; [discriminate|].
  destruct (lin_eqb (snd (fst g)) (lconst z)) eqn:Hg.
  - injection H as <- <-. apply lin_eqb_eq in Hg. split; [lia|]. exists (snd g). rewrite Nat.sub_diag. cbn. destruct g as [[b' z'] k']. cbn in *. subst. reflexivity.
  - destruct (IH _ _ _ _ H) as (Hle & k & Hk). split; [lia|]. exists k. replace (j - i0)%nat with (Datatypes.S (j - Datatypes.S i0)) by lia. exact Hk.
Qed.
Lemma rg_is_sound : forall b z k R, rg_is b z k R = true -> R = RG b (lconst z) k (rg_cont R).
Proof.
  intros b z k [b0 z0 k0 c0] H. unfold rg_is in H. cbn [rg_base rg_size rg_kind] in H. apply andb_prop in H as [H H3]. apply andb_prop in H as [H1 H2].
  apply lin_eqb_eq in H1, H2. apply rkind_eqb_eq in H3. subst. reflexivity.
Qed.
Lemma remove_nth_split : forall {A} i (l : list A), remove_nth i l = firstn i l ++ skipn (Datatypes.S i) l.
Proof. intros A i. induction i as [|i IH]; intros [|x l]; cbn; try reflexivity. rewrite IH. reflexivity. Qed.
Lemma remove_nth_app_len : forall {A} (l r : list A) x, remove_nth (length l) (l ++ x :: r) = l ++ r.
Proof. intros A l r x. induction l as [|y l IH]; cbn; [reflexivity|]. rewrite IH. reflexivity. Qed.
Lemma nth_error_app_len : forall {A} (l r : list A) x, nth_error (l ++ x :: r) (length l) = Some x.
Proof. intros A l r x. induction l as [|y l IH]; cbn; [reflexivity | exact IH]. Qed.
Lemma nth_split4 : forall {A} (l : list A) i a b c d, nth_error l i = Some a -> nth_error l (Datatypes.S i) = Some b ->
  nth_error l (2 + i) = Some c -> nth_error l (3 + i) = Some d -> l = firstn i l ++ a :: b :: c :: d :: skipn (4 + i) l.
Proof.
  intros A l. induction l as [|y l IH]; intros i a b c d H0 H1 H2 H3; [destruct i; discriminate|]. destruct i as [|i].
  - cbn in H0, H1, H2, H3. injection H0 as <-. destruct l as [|y1 [|y2 [|y3 l]]]; cbn in H1, H2, H3; try discriminate.
    injection H1 as <-. injection H2 as <-. injection H3 as <-. reflexivity.
  - cbn [firstn]. change (4 + Datatypes.S i)%nat with (Datatypes.S (4 + i)). cbn [skipn]. rewrite <- app_comm_cons. f_equal. apply IH; assumption.
Qed.
Lemma perm_to_end : forall {A} (l1 l2 : list A) x, Permutation (l1 ++ x :: l2) ((l1 ++ l2) ++ [x]).
Proof. intros A l1 l2 x. apply (Permutation_trans (Permutation_sym (Permutation_middle l1 l2 x))). apply Permutation_cons_append. Qed.

(* [comment removed for export] *)
Lemma nth_app1 : forall {A} (l r : list A) i x, nth_error l i = Some x -> nth_error (l ++ r) i = Some x.
Proof. intros A l r i x H. rewrite nth_error_app1; [exact H | apply nth_error_Some; rewrite H; discriminate]. Qed.
Lemma csplit_app : forall l r i ins x, nth_error l i = Some x -> csplit (l ++ r) i ins = csplit l i ins ++ r.
Proof.
  intros l r i ins x H. assert (Hi : (i < length l)%nat) by (apply nth_error_Some; rewrite H; discriminate).
  unfold csplit. rewrite firstn_app, skipn_app. replace (i - length l)%nat with O by lia. replace (Datatypes.S i - length l)%nat with O by lia.
  cbn [firstn skipn]. rewrite app_nil_r, <- !app_assoc. reflexivity.
Qed.
Lemma merge_app : forall (l r : list region) i X x y, nth_error l i = Some x -> nth_error l (Datatypes.S i) = Some y ->
  firstn i (l ++ r) ++ X :: skipn (Datatypes.S (Datatypes.S i)) (l ++ r) = (firstn i l ++ X :: skipn (Datatypes.S (Datatypes.S i)) l) ++ r.
Proof.
  intros l r i X x y H0 H1. assert (Hi : (Datatypes.S i < length l)%nat) by (apply nth_error_Some; rewrite H1; discriminate).
  rewrite firstn_app, skipn_app. replace (i - length l)%nat with O by lia. replace (Datatypes.S (Datatypes.S i) - length l)%nat with O by lia.
  cbn [firstn skipn]. rewrite app_nil_r, <- app_assoc. reflexivity.
Qed.
Lemma step_rgs_app : forall n fs l r st l', step_rgs n fs l st = Some l' -> step_rgs n fs (l ++ r) st = Some (l' ++ r).
Proof.
  intros n fs l r st l' H. destruct st as [i R1 R2 o|i|i x b'|i|i|i]; cbn [step_rgs] in H |- *.
  - destruct (nth_error l i) as [R|] eqn:HR; [|discriminate]. rewrite (nth_app1 l r i R HR).
    destruct (is_const (rg_size R)) as [z|]; [|discriminate].
    match type of H with (if ?c then _ else _) = _ => destruct c; [|discriminate] end.
    injection H as <-. rewrite (csplit_app l r i _ R HR). reflexivity.
  - destruct (nth_error l i) as [R|] eqn:HR; [|discriminate]. rewrite (nth_app1 l r i R HR).
    injection H as <-. rewrite (csplit_app l r i _ R HR). reflexivity.
  - destruct (nth_error l i) as [R|] eqn:HR; [|discriminate]. rewrite (nth_app1 l r i R HR).
    destruct (lin_off (rg_base R) x) as [c|]; [|discriminate].
    match type of H with (if ?c then _ else _) = _ => destruct c; [|discriminate] end.
    injection H as <-. rewrite (csplit_app l r i _ R HR). reflexivity.
  - destruct (nth_error l i) as [Ra|] eqn:HRa; [|discriminate]. destruct (nth_error l (Datatypes.S i)) as [Rb|] eqn:HRb; [|discriminate].
    rewrite (nth_app1 l r i Ra HRa), (nth_app1 l r _ Rb HRb).
    destruct (is_const (rg_size Ra)) as [z1|]; [|discriminate]. destruct (is_const (rg_size Rb)) as [z2|]; [|discriminate].
    destruct (lin_off (rg_base Rb) (rg_base Ra)) as [d|]; [|discriminate].
    match type of H with (if ?c then _ else _) = _ => destruct c; [|discriminate] end.
    injection H as <-. rewrite (merge_app l r i _ Ra Rb HRa HRb). reflexivity.
  - destruct (nth_error l i) as [Ra|] eqn:HRa; [|discriminate]. destruct (nth_error l (Datatypes.S i)) as [Rb|] eqn:HRb; [|discriminate].
    rewrite (nth_app1 l r i Ra HRa), (nth_app1 l r _ Rb HRb).
    destruct (is_const (rg_size Ra)) as [z1|]; [|discriminate]. destruct (is_const (rg_size Rb)) as [z2|]; [|discriminate].
    destruct (lin_off (rg_base Rb) (rg_base Ra)) as [d|]; [|discriminate].
    match type of H with (if ?c then _ else _) = _ => destruct c; [|discriminate] end.
    injection H as <-. rewrite (merge_app l r i _ Ra Rb HRa HRb). reflexivity.
  - destruct (nth_error l i) as [Ra|] eqn:HRa; [|discriminate]. destruct (nth_error l (Datatypes.S i)) as [Rb|] eqn:HRb; [|discriminate].
    rewrite (nth_app1 l r i Ra HRa), (nth_app1 l r _ Rb HRb).
    destruct (is_const (rg_size Ra)) as [z1|]; [|discriminate]. destruct (is_const (rg_size Rb)) as [z2|]; [|discriminate].
    destruct (lin_off (rg_base Rb) (rg_base Ra)) as [d|]; [|discriminate].
    match type of H with (if ?c then _ else _) = _ => destruct c; [|discriminate] end.
    injection H as <-. rewrite (merge_app l r i _ Ra Rb HRa HRb). reflexivity.
Qed.
Lemma steps_rgs_app : forall n fs sts l r l', steps_rgs n fs l sts = Some l' -> steps_rgs n fs (l ++ r) sts = Some (l' ++ r).
Proof.
  intros n fs sts. induction sts as [|st sts IH]; intros l r l' H; [rewrite steps_rgs_nil in H |- * | rewrite steps_rgs_cons in H |- *]; [injection H as <-; reflexivity|].
  destruct (step_rgs n fs l st) as [l1|] eqn:H1; [|discriminate]. rewrite (step_rgs_app n fs l r st l1 H1). exact (IH l1 r l' H).
Qed.

(* [comment removed for export] *)
Lemma rd_zero : forall m a w, 0 <= a -> a + Z.of_nat w <= two64 ->
  (forall x, a <= x < a + Z.of_nat w -> rd1 SEGS m (wa x) = Some (Z_to_bv 8 0)) -> rd m a w 0.
Proof.
  intros m a w Ha Hw H. apply rd_of_rd1; [exact Ha | exact Hw |]. intros j Hj.
  change (Z_to_bv 64 (a + Z.of_nat j)) with (wa (a + Z.of_nat j)). rewrite (H (a + Z.of_nat j) ltac:(lia)).
  unfold word_to_le_bytes, wa. rewrite u_small64 by (unfold two64; lia). rewrite nth_Z_to_le_bytes by exact Hj.
  rewrite Z.shiftr_0_l. reflexivity.
Qed.
Lemma weaken_rw_ok : forall E m R, rg_kind R = RZ -> rg_ok SEGS E m R -> rg_ok SEGS E m (weaken_rw R).
Proof.
  intros E m [b z k c] Hk (H1 & H2 & H3 & H4). cbn [rg_kind] in Hk. subst k. unfold rg_ok, weaken_rw in *. cbn [rg_base rg_size rg_kind rg_cont] in *.
  unfold rsz in *. cbn [rg_size] in *. split; [exact H1|]. split; [exact H2|]. split; [|exact H4]. intros i Hi. exact (proj1 (H3 i Hi)).
Qed.

(* [comment removed for export] *)
Lemma nth_virgin : forall (a b c d e : Z) k, (5 <= k)%nat -> nth k (a :: b :: c :: d :: e :: repeat 0 66) 0 = 0.
Proof.
  intros a b c d e k Hk. do 5 (destruct k as [|k]; [lia|]). cbn [nth]. clear Hk. revert k. generalize 66%nat. intros n. induction n as [|n IH]; intros [|k]; cbn; try reflexivity. apply IH.
Qed.
Lemma INV_Az_virgin : forall SB SH CA PG T m,
  17594333495296 <= SB -> SB mod 4096 = 0 -> SH = SB / 8 + 2147450880 ->
  ((4304 <= CA /\ CA + 3888 <= 65536) \/ 6537424 <= CA) -> CA mod 16 = 0 -> CA + 3888 <= 2^47 ->
  PG <= SB -> SB + 137438953472 + 4096 <= PG + PG_SIZE -> PG + PG_SIZE <= 2^47 -> CA = T + 208 ->
  17594333495296 <= PG -> (T + 4096 <= 2147446784 \/ 17594333495296 <= T) ->
  (forall x, CA - 128 <= x < CA + 2592 \/ SB + 137438953472 <= x < SB + 137438953472 + 4096 \/ 930696 <= x < 930736 ->
     rd1 SEGS m (wa x) = Some (Z_to_bv 8 0) /\ wview SEGS m (wa x) <> None) ->
  (forall x, SH <= x < SH + 17179869184 -> wview SEGS m (wa x) <> None) ->
  INV_Az (SB :: SH :: CA :: PG :: T :: repeat 0 66) m.
Proof.
  intros SB SH CA PG T m Hsb1 Hsb2 Hsh Hca1 Hca2 Hca3 Hpg1 Hpg2 Hpg3 Htg Hn1 Hn2 HZ HW.
  set (pz := SB :: SH :: CA :: PG :: T :: repeat 0 66).
  assert (B : 4096 <= CA - 128 /\ 0 <= SB /\ SB + 137438953472 + 4096 <= 2^47) by (unfold PG_SIZE in *; lia).
  assert (Hshb : 0 <= SB / 8 <= 2^44) by (split; [apply Z.div_pos; lia | apply Z.div_le_upper_bound; lia]).
  assert (RD : forall a w, (1 <= w <= 8)%nat -> (forall x, a <= x < a + Z.of_nat w -> CA - 128 <= x < CA + 2592 \/ SB + 137438953472 <= x < SB + 137438953472 + 4096 \/ 930696 <= x < 930736) ->
            0 <= a -> rd m a w 0).
  { intros a w Hw Hin Ha. apply rd_zero; [exact Ha | | intros x Hx; exact (proj1 (HZ x (Hin x Hx)))].
    pose proof (Hin (a + Z.of_nat w - 1) ltac:(lia)) as Y. unfold two64. lia. }
  assert (WR : forall a n, (forall x, a <= x < a + n -> CA - 128 <= x < CA + 2592 \/ SB + 137438953472 <= x < SB + 137438953472 + 4096 \/ 930696 <= x < 930736) ->
            0 <= a -> a + n <= 2^64 -> wr m a n).
  { intros a n Hin Ha Hn. apply wr_bytes; [exact Ha | exact Hn | intros x Hx; exact (proj2 (HZ x (Hin x Hx)))]. }
  assert (Zj : forall c, In c CLS -> z_j pz c = 0 /\ z_z pz c = 0).
  { intros c Hc. unfold z_j, z_z, zn, pz. split; apply nth_virgin; lia. }
  constructor.
  - reflexivity.
  - split; assumption.
  - exact Hsh.
  - split; [exact Hca1|]. split; assumption.
  - change (z_pg pz) with PG. change (z_sb pz) with SB. split; [exact Hpg1|]. split; assumption.
  - exact Htg.
  - split; assumption.
  - change (z_ca pz) with CA. split; [|split].
    + exists 0. split; [lia|]. apply RD; [lia | intros x Hx; cbn in Hx; left; lia | lia].
    + exists 0. split; [lia|]. apply RD; [lia | intros x Hx; cbn in Hx; left; lia | lia].
    + apply WR; [intros x Hx; left; lia | lia | lia].
  - change (z_ca pz) with CA. apply WR; [intros x Hx; left; lia | lia | lia].
  - change (z_ca pz) with CA. change (z_sb pz) with SB. change (z_qj pz) with 0. change (z_qn pz) with 0. change (z_qb pz) with 0. split; [|intros X; lia].
    split; [lia|]. split; [apply RD; [lia | intros x Hx; cbn in Hx; left; lia | lia]|].
    left. split; [reflexivity|]. split; [reflexivity|]. apply RD; [lia | intros x Hx; cbn in Hx; left; lia | lia].
  - change (z_sb pz) with SB. change (z_gn pz) with 0. change (z_gl pz) with 0. change (z_gb pz) with 0. split; [|intros X; lia].
    split; [lia|]. split; [lia|].
    split; [apply RD; [lia | intros x Hx; cbn in Hx; right; right; lia | lia]|].
    split; [apply WR; [intros x Hx; right; right; lia | lia | lia]|].
    split; [apply RD; [lia | intros x Hx; cbn in Hx; right; right; lia | lia]|].
    split; [apply RD; [lia | intros x Hx; cbn in Hx; right; right; lia | lia]|].
    split; [apply WR; [intros x Hx; right; right; lia | lia | lia]|].
    split; [exists 0; split; [lia|]; apply RD; [lia | intros x Hx; cbn in Hx; right; right; lia | lia]|].
    left. split; [reflexivity|]. exists 0. split; [lia|]. apply RD; [lia | intros x Hx; cbn in Hx; right; right; lia | lia].
  - intros c Hc. pose proof (in_cls_rng c Hc) as Hcr. destruct (Zj c Hc) as [-> ->]. change (z_ca pz) with CA. change (z_sb pz) with SB. change (z_sh pz) with SH.
    left. split; [reflexivity|]. split; [reflexivity|]. split.
    + constructor.
      * apply RD; [lia | intros x Hx; cbn in Hx; left; lia | lia].
      * left. split; [apply RD; [lia | intros x Hx; cbn in Hx; left; lia | lia]|]. exists 0. split; [lia|]. apply RD; [lia | intros x Hx; cbn in Hx; left; lia | lia].
      * intros i Hi. apply RD; [lia | intros x Hx; cbn in Hx; right; left; lia | lia].
      * apply WR; [intros x Hx; left; lia | lia | lia].
      * apply WR; [intros x Hx; right; left; lia | lia | lia].
    + split; (apply wr_bytes; [lia | lia | intros x Hx; apply HW; lia]).
Qed.
(* [comment removed for export] *)
Definition mzero : word -> option byte := fun _ => Some (Z_to_bv 8 0).
Lemma mzero_ok : forall x, rd1 SEGS mzero (wa x) = Some (Z_to_bv 8 0) /\ wview SEGS mzero (wa x) <> None.
Proof. intros x. split; [reflexivity | unfold wview, mzero; discriminate]. Qed.

(* [comment removed for export] *)
Lemma den_rg_vis' : forall LIMIT model0 m0 E S M ms model R x, DEN ASEGS LIMIT model0 m0 E S M ms model -> In R (s_rgs S) ->
  uE E (rg_base R) <= x < uE E (rg_base R) + rsz E R -> Hof E M model (wa x) = false.
Proof.
  intros LIMIT model0 m0 E S M ms model R x Hd HR Hx.
  pose proof (sden_0 _ _ _ _ (dn_sden _ _ _ _ _ _ _ _ _ Hd)) as (_ & _ & _ & _ & HG & _). rewrite Forall_forall in HG.
  pose proof (rg_ok_visible ASEGS (Hof E M model) (ms_mem ms) E R (dn_hoff _ _ _ _ _ _ _ _ _ Hd) (HG R HR) (x - uE E (rg_base R)) ltac:(lia)) as V.
  replace (uE E (rg_base R) + (x - uE E (rg_base R))) with x in V by ring. exact V.
Qed.
(* [comment removed for export] *)
Lemma rz_zero_pt : forall E m b z c x, rg_ok SEGS E m (RG b z RZ c) -> tzero_b c = true -> uE E b <= x < uE E b + rsz E (RG b z RZ c) ->
  rd1 SEGS m (wa x) = Some (Z_to_bv 8 0) /\ wview SEGS m (wa x) <> None.
Proof.
  intros E m b z c x HR Hc Hx. split.
  - replace x with (uE E b + (x - uE E b)) by ring. destruct (tget (okey (x - uE E b)) c) as [v|] eqn:Ht.
    + pose proof (tforall_spec _ c Hc _ v Ht) as Hv. cbv beta in Hv. destruct v as [k|l j]; [|discriminate]. destruct k; try discriminate.
      exact (byte_tracked E m b z RZ c (x - uE E b) _ HR ltac:(lia) Ht).
    + exact (byte_rz E m b z c (x - uE E b) HR ltac:(lia) Ht).
  - exact (proj2 (rg_rw_pt E m _ x HR eq_refl Hx)).
Qed.
Lemma tzero_empty : tzero_b TEmpty = true.
Proof. reflexivity. Qed.
(* [comment removed for export] *)
Lemma grant_off_image : forall LIMIT model0 mem0 E S M ms model g, DEN ASEGS LIMIT model0 mem0 E S M ms model -> In g (sm_maps M) -> is_mark g = false ->
  uE E (fst (fst g)) + gsz E g <= 65536 \/ 6537216 <= uE E (fst (fst g)).
Proof.
  intros LIMIT model0 mem0 E S M ms model g Hd Hg Hgm.
  pose proof (dn_gsh _ _ _ _ _ _ _ _ _ Hd) as Hgs. rewrite Forall_forall in Hgs. destruct (Hgs g Hg) as (G1 & G2 & G3 & G4 & G5).
  destruct (Z_le_gt_dec (uE E (fst (fst g)) + gsz E g) 65536) as [Hle|Hgt]; [left; exact Hle|].
  destruct (Z_lt_ge_dec (uE E (fst (fst g))) 6537216) as [Hlt|]; [|right; lia]. exfalso.
  set (x := Z.max (uE E (fst (fst g))) 65536).
  assert (Hc1 : covered (vm_maps (m_vmmaps model)) x = true).
  { apply (grant_covered E _ M model g (dn_maps _ _ _ _ _ _ _ _ _ Hd) (dn_gsh _ _ _ _ _ _ _ _ _ Hd) Hg Hgm). unfold x. lia. }
  pose proof (dn_mres _ _ _ _ _ _ _ _ _ Hd x Hc1) as Hc2. rewrite (dn_res _ _ _ _ _ _ _ _ _ Hd) in Hc2.
  rewrite (res_cov x ltac:(unfold x; lia)) in Hc2. discriminate.
Qed.

(* [comment removed for export] *)
Lemma grants_apart_in : forall LIMIT model0 mem0 E S M ms model b1 z1 k1 b2 z2 k2, DEN ASEGS LIMIT model0 mem0 E S M ms model ->
  In (b1, lconst z1, k1) (sm_maps M) -> In (b2, lconst z2, k2) (sm_maps M) -> lconst z1 <> lconst z2 -> 0 <= z1 < 2^64 -> 0 <= z2 < 2^64 ->
  uE E b1 + z1 <= uE E b2 \/ uE E b2 + z2 <= uE E b1.
Proof.
  intros LIMIT model0 mem0 E S M ms model b1 z1 k1 b2 z2 k2 Hd H1 H2 Hne Hz1 Hz2.
  pose proof (dn_maps _ _ _ _ _ _ _ _ _ Hd) as Hmaps. pose proof (dn_pd _ _ _ _ _ _ _ _ _ Hd) as Hpd.
  destruct (In_nth_error _ _ H1) as (j & Hj). destruct (In_nth_error _ _ H2) as (j' & Hj').
  assert (Hnj : j <> j') by (intros ->; rewrite Hj in Hj'; apply Hne; congruence).
  assert (Hd' : iv_disj (gden E (b1, lconst z1, k1)) (gden E (b2, lconst z2, k2))).
  { rewrite Hmaps in Hpd. exact (pdisj_lden_nth E _ _ j j' _ _ Hpd Hj Hj' Hnj (is_mark_csize _ _ _) (is_mark_csize _ _ _)). }
  unfold iv_disj, FxBacking.B, FxBacking.S, gden in Hd'. cbn [fst snd] in Hd'.
  assert (G1 : uE E (lconst z1) = z1) by (apply uE_lc; exact Hz1). assert (G2 : uE E (lconst z2) = z2) by (apply uE_lc; exact Hz2).
  unfold gsz, uE in *. cbn [fst snd] in *. lia.
Qed.

Section ConvAN.
Variable cfg : SpuriousCfg.
Variable LIMIT : Z.
Variable model0 : Model.

#[using="Type"] Theorem conva_node : forall S M a S' M' a', apost_conva LIMIT S M a = Some (S', M', a') ->
  forall mem0 E ms model T, DEN ASEGS LIMIT model0 mem0 E S M ms model -> awf (s_next S) a = true -> HA E M a mem0 ->
  (forall E' mem0' ms' model', agree (s_next S) E E' -> frz_same E M mem0 mem0' -> DEN ASEGS LIMIT model0 mem0' E' S' M' ms' model' ->
     HA E' M' a' mem0' -> realizes_cfg ASEGS cfg (mkCfg ms' model') T) ->
  realizes_cfg ASEGS cfg (mkCfg ms model) T.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros S M a S' M' a' H mem0 E ms model T Hd Haw HHA Hk.
  unfold apost_conva in H. cbv zeta in H.
  apply obool_some in H as (Hon & H).
  apply obind_some in H as (SBl & WSB & H). cbv beta in H.
  apply obind_some in H as (RIBl & WRIB & H). cbv beta in H.
  apply obind_some in H as (SB8 & HSB8 & H). cbv beta in H.
  apply obind_some in H as (Kl & WK & H). cbv beta in H.
  apply obind_some in H as (K & EK & H). cbv beta in H.
  apply obind_some in H as (TSDAl & WT1 & H). cbv beta in H.
  apply obind_some in H as (PTl & WT2 & H). cbv beta in H.
  apply obind_some in H as (Tl & WT3 & H). cbv beta in H.
  apply obind_some in H as ([jP PGl] & HjPG & H). cbv beta in H. cbn [fst snd] in H.
  apply obind_some in H as (jT & HjT & H). cbv beta in H.
  apply obind_some in H as (jD1 & HjD1 & H). cbv beta in H.
  apply obind_some in H as (jB1 & HjB1 & H). cbv beta in H.
  apply obind_some in H as (iRI & HiRI & H). cbv beta in H.
  apply obind_some in H as (RRI & HRRI & H). cbv beta in H.
  set (G1 := remove_nth iRI (s_rgs S)) in *.
  apply obind_some in H as (iT & HiT & H). cbv beta in H.
  apply obind_some in H as (RT & HRT & H). cbv beta in H.
  apply obind_some in H as (G2 & HG2 & H). cbv beta in H.
  apply obind_some in H as (RP0 & HRP0 & H). cbv beta in H.
  apply obind_some in H as (RCA & HRCA & H). cbv beta in H.
  apply obind_some in H as (RP2 & HRP2 & H). cbv beta in H.
  apply obind_some in H as (RST & HRST & H). cbv beta in H.
  set (G4 := firstn iT G2 ++ weaken_rw RP0 :: RP2 :: weaken_rw RST :: skipn (4 + iT) G2) in *.
  apply obind_some in H as ([[iQ bq] zq] & Hfq & H). cbv beta in H. cbn [fst snd] in H.
  apply obind_some in H as (RQ & HRQ & H). cbv beta in H.
  apply obind_some in H as (G5 & HG5 & H). cbv beta in H.
  apply obind_some in H as (RGQ & HRGQ & H). cbv beta in H.
  set (G6 := remove_nth (Datatypes.S iQ) G5) in *.
  set (SHl := laddc SB8 2147450880) in *. set (CAl := laddc Tl 208) in *.
  set (pri := pri_lins0 SBl SHl CAl PGl Tl) in *.
  set (a0 := with_pri a (a_own a) pri) in *.
  set (own' := a_own a ++ pri_own a0) in *.
  set (a1 := with_pri a own' pri) in *.
  apply obool_some in H as (Hchk & H). injection H as <- <- <-.
  (* [comment removed for export] *)
  apply andb_prop in Hchk as [Hchk Cx]. apply andb_prop in Hchk as [Hchk Cwp]. apply andb_prop in Hchk as [Hchk Cwo].
  apply andb_prop in Hchk as [Hchk Cal]. apply andb_prop in Hchk as [Hchk _]. apply andb_prop in Hchk as [Hchk _]. apply andb_prop in Hchk as [Hchk _].
  apply andb_prop in Hchk as [Hchk Cal4]. apply andb_prop in Hchk as [Hchk Csblo]. apply andb_prop in Hchk as [Hchk Cdhi]. apply andb_prop in Hchk as [Hchk Cdlo].
  apply andb_prop in Hchk as [Hchk Cgq0]. apply andb_prop in Hchk as [Hchk CRQ]. apply andb_prop in Hchk as [Hchk CeCA]. apply andb_prop in Hchk as [_ CeRI].
  unfold conva_extra in Cx. cbv zeta in Cx.
  apply andb_prop in Cx as [Cx Cn8]. apply andb_prop in Cx as [Cx Cn7]. apply andb_prop in Cx as [Cx Cn6]. apply andb_prop in Cx as [Cx Cn10]. apply andb_prop in Cx as [Cx Cn5].
  apply andb_prop in Cx as [Cx Cn4]. apply andb_prop in Cx as [Cx Cn3b]. apply andb_prop in Cx as [Cx Cn3a]. apply andb_prop in Cx as [Cn1 Cn2].
  apply andb_prop in Hon as [Hon Hown_eq]. apply andb_prop in Hon as [Hon Hpri0].
  apply (list_eqb_eq pair_eqb pair_eqb_eq) in Hown_eq. apply Nat.eqb_eq in Hpri0.
  apply Z.leb_le in Csblo, Cdhi, Cdlo, Cn6. apply Z.ltb_lt in Cn10. apply tempty_b_eq in CeCA, CeRI. apply rkind_eqb_eq in Cn3a, Cn3b.
  assert (Hpnil : a_pri a = []) by (destruct (a_pri a); [reflexivity | discriminate]).
  assert (Hfnil : a_fcts a = []) by (destruct (a_rgs a); [destruct (a_fcts a); [reflexivity | discriminate] | discriminate]).
  assert (Hxnil : a_rgs a = []) by (destruct (a_rgs a); [reflexivity | discriminate]).
  pose proof (HHA Hon) as HA0.
  pose proof (sden_0 _ _ _ _ (dn_sden _ _ _ _ _ _ _ _ _ Hd)) as (_ & _ & _ & _ & _ & _ & HF0 & _).
  (* [comment removed for export] *)
  destruct (find_gsz_acc_sound _ _ _ _ _ HjPG) as (_ & kp & HgP). rewrite Nat.sub_0_r in HgP.
  destruct (find_grant_sound _ _ _ _ HjT) as (kt & HgT).
  pose proof (dn_gsh _ _ _ _ _ _ _ _ _ Hd) as Hgs. rewrite Forall_forall in Hgs.
  destruct (Hgs _ (nth_error_In _ _ HgP)) as (GP1 & GP2 & GP3 & GP4 & GP5). destruct (Hgs _ (nth_error_In _ _ HgT)) as (GT1 & GT2 & GT3 & GT4 & GT5).
  assert (ZP : gsz E (PGl, lconst PG_SIZE, kp) = PG_SIZE) by (unfold gsz; cbn [fst snd]; apply uE_lc; unfold PG_SIZE; lia).
  assert (ZT : gsz E (Tl, lconst TG_SIZE, kt) = 4096) by (unfold gsz; cbn [fst snd]; apply uE_lc; unfold TG_SIZE; lia).
  cbn [fst snd] in GP3, GP4, GP5, GT3, GT4, GT5. rewrite ZP in GP4. rewrite ZT in GT4. clear GP1 GP2 GT1 GT2.
  set (SB := uE E SBl) in *. set (PG := uE E PGl) in *. set (TT := uE E Tl) in *.
  (* [comment removed for export] *)
  pose proof (irange_sound E (s_facts S) SBl HF0) as RSB. fold (uE E SBl) in RSB. fold SB in RSB.
  pose proof (irange_sound E (s_facts S) SB8 HF0) as RS8. fold (uE E SB8) in RS8.
  pose proof (lal4096_sound E SBl Cal4) as Hsb4. fold SB in Hsb4.
  assert (E8 : SB = 8 * uE E SB8).
  { unfold SB. pose proof (ldiv8_eqm E SBl SB8 HSB8) as Hq. unfold eqm in Hq. unfold uE, lden. rewrite !u_Z_to_bv. rewrite Hq.
    pose proof (Z.mod_pos_bound (lz E SB8) two64 ltac:(unfold two64; lia)) as B8.
    assert (X : uE E SB8 = lz E SB8 mod two64) by (unfold uE, lden; rewrite u_Z_to_bv; reflexivity). rewrite X in RS8.
    rewrite <- (Z.mod_small (8 * (lz E SB8 mod two64)) two64) by (unfold two64 in *; lia).
    rewrite <- Zmult_mod_idemp_r. reflexivity. }
  assert (Hsh : uE E SHl = SB / 8 + 2147450880).
  { unfold SHl. rewrite uE_laddc_z by (unfold two64; lia). rewrite E8. rewrite Z.mul_comm, Z.div_mul by lia. reflexivity. }
  assert (HD : 0 <= SB - PG <= 65536).
  { pose proof (irange_sound E (s_facts S) (lsub SBl PGl) HF0) as RD. rewrite lden_lsub, bv_sub_unsigned in RD. unfold bv_wrap, bv_modulus in RD.
    change (2 ^ Z.of_N 64) with two64 in RD. fold (uE E SBl) in RD. fold (uE E PGl) in RD. fold SB PG in RD.
    pose proof (uE_range E SBl) as U1. pose proof (uE_range E PGl) as U2. fold SB in U1. fold PG in U2.
    destruct (Z_le_gt_dec PG SB) as [X|X].
    - rewrite Z.mod_small in RD by (unfold two64 in *; lia). lia.
    - exfalso. replace (SB - PG) with ((SB - PG + two64) + (-1) * two64) in RD by ring. rewrite Z.mod_add in RD by (unfold two64; lia).
      rewrite Z.mod_small in RD by (unfold two64 in *; lia). unfold two64 in *. lia. }
  assert (Eca : uE E CAl = TT + 208) by (unfold CAl; apply uE_laddc2; [lia | fold TT; unfold two64; lia]).
  (* [comment removed for export] *)
  assert (HTpl : 4096 <= TT /\ (TT + 4096 <= 65536 \/ 6537216 <= TT)).
  { pose proof (grant_off_image LIMIT model0 mem0 E S M ms model _ Hd (nth_error_In _ _ HgT) (is_mark_csize _ _ _)) as X. rewrite ZT in X. cbn [fst] in X. fold TT in X.
    split; [|exact X]. pose proof (Z.div_mod TT 4096 ltac:(lia)) as Ed. rewrite GT3, Z.add_0_r in Ed. lia. }
  (* [comment removed for export] *)
  destruct (find_rg_acc'_sound _ _ _ _ HiRI) as (_ & RRI' & HRRI' & FRI). rewrite Nat.sub_0_r in HRRI'. rewrite HRRI in HRRI'. injection HRRI' as <-.
  destruct (find_rg_acc'_sound _ _ _ _ HiT) as (_ & RT' & HRT' & FRT). rewrite Nat.sub_0_r in HRT'. rewrite HRT in HRT'. injection HRT' as <-.
  pose proof (rg_is_sound _ _ _ _ FRI) as ERI. rewrite CeRI in ERI.
  pose proof (rg_is_sound _ _ _ _ FRT) as ERT.
  pose proof (rg_is_sound _ _ _ _ Cn2) as ECA. rewrite CeCA in ECA.
  pose proof (rg_is_sound _ _ _ _ Cn4) as EGQ. change (GQ_HI - GQ_LO) with 40 in EGQ. unfold GQ_LO in EGQ.
  (* [comment removed for export] *)
  assert (HTns : SH_HI <= TT \/ TT + 4096 <= SH_LO).
  { apply (noshadow_range TT 4096 ltac:(lia)). intros w Hw. apply (noshadow_sound E (s_facts S) RT HF0 Cn7).
    rewrite ERT. cbn [rg_base]. unfold rsz. cbn [rg_size]. fold (uE E (lconst 4096)). rewrite uE_lc by lia. fold TT. exact Hw. }
  (* [comment removed for export] *)
  set (M1 := allow_ins M 0 (SHl, 17179869184)).
  pose proof (den_allow_ins ASEGS LIMIT model0 mem0 E S M ms model 0 (SHl, 17179869184) Hd Cal) as D1. fold M1 in D1.
  (* [comment removed for export] *)
  pose proof (nth_split _ _ _ HRRI) as EG. 
  assert (P1 : Permutation (s_rgs S) (G1 ++ [RRI])).
  { rewrite EG at 1. unfold G1. rewrite remove_nth_split. apply perm_to_end. }
  pose proof (den_perm ASEGS LIMIT model0 mem0 E S M1 ms model _ D1 P1) as D2.
  pose proof (den_steps ASEGS LIMIT model0 mem0 _ E _ M1 ms model _ D2 (steps_rgs_app _ _ _ _ [RRI] _ HG2)) as D3.
  change (with_rgs (with_rgs S (G1 ++ [RRI])) (G2 ++ [RRI])) with (with_rgs S (G2 ++ [RRI])) in D3.
  pose proof (nth_split4 G2 iT _ _ _ _ HRP0 HRCA HRP2 HRST) as EG2.
  set (l1 := firstn iT G2) in *. set (l2 := skipn (4 + iT) G2) in *.
  assert (D4 : DEN ASEGS LIMIT model0 mem0 E (with_rgs S (l1 ++ weaken_rw RP0 :: (RCA :: RP2 :: RST :: l2) ++ [RRI])) M1 ms model).
  { apply (den_weaken_rg ASEGS LIMIT model0 mem0 E (with_rgs S (G2 ++ [RRI])) M1 ms model l1 RP0 ((RCA :: RP2 :: RST :: l2) ++ [RRI]) (weaken_rw RP0) D3).
    - cbn [with_rgs s_rgs]. rewrite EG2 at 1. rewrite <- app_assoc. reflexivity.
    - reflexivity.
    - reflexivity.
    - intros E' m _ HR. exact (weaken_rw_ok E' m RP0 Cn3a HR). }
  assert (D5 : DEN ASEGS LIMIT model0 mem0 E (with_rgs S ((l1 ++ [weaken_rw RP0; RCA; RP2]) ++ weaken_rw RST :: l2 ++ [RRI])) M1 ms model).
  { apply (den_weaken_rg ASEGS LIMIT model0 mem0 E _ M1 ms model (l1 ++ [weaken_rw RP0; RCA; RP2]) RST (l2 ++ [RRI]) (weaken_rw RST) D4).
    - cbn [with_rgs s_rgs]. rewrite <- !app_assoc. reflexivity.
    - reflexivity.
    - reflexivity.
    - intros E' m _ HR. exact (weaken_rw_ok E' m RST Cn3b HR). }
  assert (P5 : Permutation ((l1 ++ [weaken_rw RP0; RCA; RP2]) ++ weaken_rw RST :: l2 ++ [RRI]) (G4 ++ [RRI; RCA])).
  { unfold G4. fold l1 l2.
    replace ((l1 ++ [weaken_rw RP0; RCA; RP2]) ++ weaken_rw RST :: l2 ++ [RRI]) with ((l1 ++ [weaken_rw RP0]) ++ RCA :: (RP2 :: weaken_rw RST :: l2 ++ [RRI]))
      by (rewrite <- !app_assoc; reflexivity).
    replace ((l1 ++ weaken_rw RP0 :: RP2 :: weaken_rw RST :: l2) ++ [RRI; RCA]) with (((l1 ++ [weaken_rw RP0]) ++ (RP2 :: weaken_rw RST :: l2 ++ [RRI])) ++ [RCA])
      by (rewrite <- !app_assoc; cbn [app]; rewrite <- !app_assoc; reflexivity).
    apply perm_to_end. }
  pose proof (den_perm ASEGS LIMIT model0 mem0 E _ M1 ms model _ D5 P5) as D6.
  change (with_rgs (with_rgs S ((l1 ++ [weaken_rw RP0; RCA; RP2]) ++ weaken_rw RST :: l2 ++ [RRI])) (G4 ++ [RRI; RCA])) with (with_rgs S (G4 ++ [RRI; RCA])) in D6.
  pose proof (den_steps ASEGS LIMIT model0 mem0 _ E _ M1 ms model _ D6 (steps_rgs_app _ _ _ _ [RRI; RCA] _ HG5)) as D7.
  change (with_rgs (with_rgs S (G4 ++ [RRI; RCA])) (G5 ++ [RRI; RCA])) with (with_rgs S (G5 ++ [RRI; RCA])) in D7.
  pose proof (nth_split _ _ _ HRGQ) as EG5.
  assert (P7 : Permutation (G5 ++ [RRI; RCA]) (G6 ++ [RRI; RCA; RGQ])).
  { rewrite EG5 at 1. unfold G6. rewrite remove_nth_split. rewrite <- app_assoc. cbn [app].
    replace ((firstn (Datatypes.S iQ) G5 ++ skipn (Datatypes.S (Datatypes.S iQ)) G5) ++ [RRI; RCA; RGQ])
      with ((firstn (Datatypes.S iQ) G5 ++ (skipn (Datatypes.S (Datatypes.S iQ)) G5 ++ [RRI; RCA])) ++ [RGQ]) by (rewrite <- !app_assoc; reflexivity).
    apply perm_to_end. }
  pose proof (den_perm ASEGS LIMIT model0 mem0 E _ M1 ms model _ D7 P7) as D8.
  change (with_rgs (with_rgs S (G5 ++ [RRI; RCA])) (G6 ++ [RRI; RCA; RGQ])) with (with_rgs S (G6 ++ [RRI; RCA; RGQ])) in D8.
  set (Sf := with_rgs S (G6 ++ [RRI; RCA; RGQ])) in *.
  (* [comment removed for export] *)
  set (CA := TT + 208) in *. set (SH := SB / 8 + 2147450880) in *.
  assert (Epz : pden E a1 = SB :: SH :: CA :: PG :: TT :: repeat 0 66).
  { assert (X : pden E a1 = SB :: uE E SHl :: uE E CAl :: PG :: TT :: repeat 0 66) by reflexivity. rewrite X, Hsh, Eca. reflexivity. }
  pose proof (irange_sound E (s_facts S) PGl HF0) as RPG. fold (uE E PGl) in RPG. fold PG in RPG.
  assert (Hsb47 : SB + 137438953472 + 4096 <= 2^47) by (clear - HD GP4; unfold PG_SIZE in GP4; lia).
  assert (Hshb : 0 <= SB / 8 <= 2^44) by (split; [apply Z.div_pos; lia | apply Z.div_le_upper_bound; lia]).
  assert (GEO : 17594333495296 <= SB /\ ((4304 <= CA /\ CA + 3888 <= 65536) \/ 6537424 <= CA) /\ CA mod 16 = 0 /\ CA + 3888 <= 2^47 /\
                PG <= SB /\ SB + 137438953472 + 4096 <= PG + PG_SIZE /\ PG + PG_SIZE <= 2^47 /\ 17594333495296 <= PG /\
                (TT + 4096 <= 2147446784 \/ 17594333495296 <= TT)).
  { split; [lia|]. split; [unfold CA; lia|]. split.
    - unfold CA. pose proof (Z.div_mod TT 4096 ltac:(lia)) as Ed. rewrite GT3, Z.add_0_r in Ed.
      replace (TT + 208) with ((256 * (TT / 4096) + 13) * 16) by lia. apply Z.mod_mul. lia.
    - unfold CA, PG_SIZE in *. unfold SH_HI, SH_LO in HTns. lia. }
  destruct GEO as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7 & Q8 & Q9).
  (* [comment removed for export] *)
  assert (HIf : INV_A E a1 mzero).
  { unfold INV_A. rewrite Epz. apply INV_Az_virgin; try assumption; [reflexivity | reflexivity | intros x _; exact (mzero_ok x) | intros x _; exact (proj2 (mzero_ok x))]. }
  (* [comment removed for export] *)
  pose proof (rgs_sz_ok LIMIT model0 mem0 E Sf M1 ms model D8) as HSZ. rewrite Forall_forall in HSZ.
  pose proof (dn_rl _ _ _ _ _ _ _ _ _ D8) as HRL. rewrite Forall_forall in HRL.
  pose proof (sden_0 _ _ _ _ (dn_sden _ _ _ _ _ _ _ _ _ D8)) as (_ & _ & _ & _ & HRG8 & _). rewrite Forall_forall in HRG8.
  set (mr := ms_mem (restrict (Hof E M1 model) ms)) in *.
  assert (In6 : forall R, In R G6 -> In R (s_rgs Sf)) by (intros R HR; cbn [Sf with_rgs s_rgs]; apply in_or_app; left; exact HR).
  assert (InRI : In RRI (s_rgs Sf)) by (cbn [Sf with_rgs s_rgs]; apply in_or_app; right; left; reflexivity).
  assert (InCA : In RCA (s_rgs Sf)) by (cbn [Sf with_rgs s_rgs]; apply in_or_app; right; right; left; reflexivity).
  assert (InGQ : In RGQ (s_rgs Sf)) by (cbn [Sf with_rgs s_rgs]; apply in_or_app; right; right; right; left; reflexivity).
  assert (BRI : uE E (rg_base RRI) = SB + 137438953472 /\ rsz E RRI = 4096).
  { rewrite ERI. cbn [rg_base]. unfold rsz. cbn [rg_size]. fold (uE E (lconst 4096)). rewrite uE_lc by lia. split; [|reflexivity].
    apply uE_laddc2; [lia | fold SB; unfold two64; lia]. }
  assert (BCA : uE E (rg_base RCA) = CA - 128 /\ rsz E RCA = 2720).
  { rewrite ECA. cbn [rg_base]. unfold rsz. cbn [rg_size]. fold (uE E (lconst 2720)). rewrite uE_lc by lia. split; [|reflexivity].
    rewrite uE_laddc2 by (first [lia | fold TT; unfold two64; lia]). fold TT. unfold CA. lia. }
  assert (BGQ : uE E (rg_base RGQ) = 930696 /\ rsz E RGQ = 40).
  { rewrite EGQ. cbn [rg_base]. unfold rsz. cbn [rg_size]. fold (uE E (lconst 40)). rewrite !uE_lc by lia. split; reflexivity. }
  (* [comment removed for export] *)
  assert (Hcell : forall x, CA - 128 <= x < CA + 2592 \/ SB + 137438953472 <= x < SB + 137438953472 + 4096 \/ 930696 <= x < 930736 ->
            (rd1 SEGS mr (wa x) = Some (Z_to_bv 8 0) /\ wview SEGS mr (wa x) <> None) /\ Hof E M1 model (wa x) = false /\
            exists R, In R (s_rgs Sf) /\ (R = RRI \/ R = RCA \/ R = RGQ) /\ uE E (rg_base R) <= x < uE E (rg_base R) + rsz E R).
  { intros x [Hx|[Hx|Hx]].
    - assert (Hin : uE E (rg_base RCA) <= x < uE E (rg_base RCA) + rsz E RCA) by (destruct BCA as [-> ->]; lia).
      split; [|split; [exact (den_rg_vis' LIMIT model0 mem0 E Sf M1 ms model RCA x D8 InCA Hin) | exists RCA; split; [exact InCA|]; split; [right; left; reflexivity | exact Hin]]].
      pose proof (HRG8 RCA InCA) as HR. rewrite ECA in HR, Hin. exact (rz_zero_pt E mr _ _ _ x HR tzero_empty Hin).
    - assert (Hin : uE E (rg_base RRI) <= x < uE E (rg_base RRI) + rsz E RRI) by (destruct BRI as [-> ->]; lia).
      split; [|split; [exact (den_rg_vis' LIMIT model0 mem0 E Sf M1 ms model RRI x D8 InRI Hin) | exists RRI; split; [exact InRI|]; split; [left; reflexivity | exact Hin]]].
      pose proof (HRG8 RRI InRI) as HR. rewrite ERI in HR, Hin. exact (rz_zero_pt E mr _ _ _ x HR tzero_empty Hin).
    - assert (Hin : uE E (rg_base RGQ) <= x < uE E (rg_base RGQ) + rsz E RGQ) by (destruct BGQ as [-> ->]; lia).
      split; [|split; [exact (den_rg_vis' LIMIT model0 mem0 E Sf M1 ms model RGQ x D8 InGQ Hin) | exists RGQ; split; [exact InGQ|]; split; [right; right; reflexivity | exact Hin]]].
      pose proof (HRG8 RGQ InGQ) as HR. rewrite EGQ in HR, Hin. exact (rz_zero_pt E mr _ _ _ x HR Cgq0 Hin). }
  (* [comment removed for export] *)
  set (a' := AST (a_on a1) (a_rgs a1) (a_fcts a1) (a_own a1) (a_dep a1) (a_nl a1)
               (sep_cache_d (s_facts S) (sm_maps M) ASEGSR jP jT (sm_sp M) a1
                  (dep_cacheable (s_facts S) M a jD1 jB1 (sep_noshadow_b (s_facts S) (RGz (fst (a_dep a)) 1048576 RZ TEmpty))
                     (sep_noshadow_b (s_facts S) (RGz (snd (a_dep a)) 8388608 RZ TEmpty))) G6) (a_pri a1)) in *.
  assert (Epz' : pden E a' = pden E a1) by reflexivity.
  assert (Hx1 : a_ext a1 = []) by (unfold a_ext; cbn [a1 with_pri a_rgs]; rewrite Hxnil; reflexivity).
  assert (Hsepf : forall R, In R G6 -> pri_sep_f (s_facts S) (sm_maps M) ASEGSR jP jT (sm_sp M) a1 R = true ->
            forall w, uE E (rg_base R) <= w < uE E (rg_base R) + rsz E R -> ~ FPmax (pden E a1) w).
  { intros R HR Hck. destruct (HSZ R (In6 R HR)) as [Hz Hr].
    destruct (pri_sep_f_sound E (s_facts S) (sm_maps M) model (sm_sp M) _ HF0 (dn_maps _ _ _ _ _ _ _ _ _ Hd) (dn_pd _ _ _ _ _ _ _ _ _ Hd)
                (dn_gsh _ _ _ _ _ _ _ _ _ Hd) (dn_gtop _ _ _ _ _ _ _ _ _ Hd) (dn_sp _ _ _ _ _ _ _ _ _ Hd) (proj2 (dn_spok _ _ _ _ _ _ _ _ _ Hd))
                (proj1 (dn_spok _ _ _ _ _ _ _ _ _ Hd)) (dn_mres _ _ _ _ _ _ _ _ _ Hd) ASEGSR (dn_res _ _ _ _ _ _ _ _ _ Hd) gq_res a1 mzero HIf jP jT _ _
                HgP eq_refl eq_refl HgT eq_refl eq_refl ltac:(intros p Hp; rewrite Hx1 in Hp; destruct Hp) R Hz Hr Hck) as [Hs|(c & Hc & Hl)]; [exact Hs|].
    exfalso. destruct (HRL R (In6 R HR)) as [Hpos _].
    assert (Zj : z_j (pden E a1) c = 0) by (rewrite Epz; unfold z_j, zn; apply nth_virgin; lia).
    rewrite Zj in Hl. destruct Hl as [(L1 & L2 & _)|(L1 & L2 & _)]; lia. }
  assert (Hsepc' : forall p, In p (a_live a') -> uE E (fst p) + uE E (snd p) <= two64 /\
            (forall x, uE E (fst p) <= x < uE E (fst p) + uE E (snd p) -> ~ FPmax (pden E a') x)).
  { intros p Hp. cbn [a' a_live] in Hp. unfold sep_cache_d in Hp. apply in_map_iff in Hp as (R & <- & HRf). apply filter_In in HRf as [HR Hck].
    destruct (pri_sep_ff (s_facts S) (sm_maps M) ASEGSR jP jT (sm_sp M) a1 R) eqn:Hck0; [|discriminate]. clear Hck. rename Hck0 into Hck.
    rewrite pri_sep_ff_eq in Hck. cbn [fst snd].
    destruct (HSZ R (In6 R HR)) as [Hz Hr]. split; [exact Hr|]. rewrite Epz'. exact (Hsepf R HR Hck). }
  (* [comment removed for export] *)
  assert (Hsepd' : forall p, In p (a_live a') -> forall x, uE E (fst p) <= x < uE E (fst p) + uE E (snd p) -> ~ downed (dD1 E a) (dB1 E a) x).
  { intros p Hp. cbn [a' a_live] in Hp. unfold sep_cache_d in Hp. apply in_map_iff in Hp as (R & <- & HRf). apply filter_In in HRf as [HR Hck].
    destruct (pri_sep_ff (s_facts S) (sm_maps M) ASEGSR jP jT (sm_sp M) a1 R); [|discriminate]. cbv iota in Hck. cbn [fst snd].
    destruct (HSZ R (In6 R HR)) as [Hz Hr].
    exact (dep_cacheable_pts LIMIT model0 mem0 E S M ms model a mem0 jD1 jB1 R Hd HA0 HjD1 HjB1 Hz Hr Hck). }
  (* [comment removed for export] *)
  assert (HshR : SH_LO <= SH /\ SH + 17179869184 <= SH_HI) by (unfold SH, SH_LO, SH_HI; lia).
  assert (Hshout : forall x, SH <= x < SH + 17179869184 -> outside E (s_rgs Sf) (wa x)).
  { intros x Hx. unfold outside. apply Forall_forall. intros R HR. rewrite u_wa_small by (unfold SH_LO, SH_HI in HshR; lia). fold (uE E (rg_base R)).
    destruct (Z_lt_le_dec x (uE E (rg_base R))) as [H1|H1]; [left; exact H1|].
    destruct (Z_lt_le_dec x (uE E (rg_base R) + rsz E R)) as [H2|H2]; [|right; exact H2]. exfalso.
    cbn [Sf with_rgs s_rgs] in HR. apply in_app_or in HR as [HR|[<-|[<-|[<-|[]]]]].
    - rewrite forallb_l_eq, forallb_forall in Cn8. specialize (Cn8 R HR). destruct (HSZ R (In6 R HR)) as [Hz Hr].
      destruct (sep_cached a' R) eqn:Hc.
      + apply (sep_cached_sound E a' Hsepc' R Hz Hr Hc x ltac:(lia)). rewrite Epz', Epz. unfold FPmax. right. right. left. exact Hx.
      + pose proof (noshadow_sound E (s_facts S) R HF0 Cn8 x ltac:(lia)) as Hn. unfold in_shadow in Hn. apply andb_false_iff in Hn as [Hn|Hn]; [apply Z.leb_gt in Hn | apply Z.ltb_ge in Hn]; lia.
    - destruct BRI as [B1 B2]. rewrite B1 in H1. unfold SH_HI in HshR. lia.
    - destruct BCA as [B1 B2]. rewrite B1, B2 in *. unfold CA, SH_HI, SH_LO in *. lia.
    - destruct BGQ as [B1 B2]. rewrite B1, B2 in *. unfold SH_LO in HshR. lia. }
  assert (Hshz : forall x, SH <= x < SH + 17179869184 -> ms_mem ms (wa x) = Some (Z_to_bv 8 0)).
  { intros x Hx. apply (dn_zr _ _ _ _ _ _ _ _ _ D8 x).
    - (* [comment removed for export] *)
      unfold zr_cover in Cn5. apply existsb_exists in Cn5 as (p & Hp & Hc). apply andb_prop in Hc as [C1 C2]. apply Z.leb_le in C1, C2.
      unfold in_zr. apply existsb_exists. exists p. split; [exact Hp|]. apply andb_true_intro.
      assert (D1' : fst (irange (s_facts S) SBl) / 8 <= SB / 8) by (apply Z.div_le_mono; lia).
      assert (D2' : SB / 8 <= snd (irange (s_facts S) SBl) / 8) by (apply Z.div_le_mono; lia).
      split; [apply Z.leb_le | apply Z.ltb_lt]; unfold SH in Hx; lia.
    - exact (Hshout x Hx).
    - (* [comment removed for export] *)
      intros Ho. assert (Ho' : own_pt_a E a x) by (apply (own_pt_a_M E M a x Hown_eq); exact Ho).
      destruct (ha_ownx _ _ _ _ HA0 x Ho') as [Dc|[Hne _]]; [|exact (Hne Hpnil)].
      destruct (ha_hi _ _ _ _ HA0) as [Hh1 Hh2]. unfold dcov in Dc. unfold SH_LO, SH_HI in *. lia.
    - (* [comment removed for export] *)
      apply (blob_sh_grant E M1 model _ jP _ SB 137438953472 x (dn_maps _ _ _ _ _ _ _ _ _ D8) (dn_pd _ _ _ _ _ _ _ _ _ D8) (dn_blob _ _ _ _ _ _ _ _ _ D8) HgP (is_mark_csize _ _ _)).
      + cbn [fst]. fold PG. lia.
      + cbn [fst]. fold PG. rewrite ZP. lia.
      + replace (SB + 137438953472) with (SB + 17179869184 * 8) by lia. rewrite Z.div_add by lia. unfold SH, SH_OFF in *. lia. }
  (* [comment removed for export] *)
  set (dec := fun x : Z => ((CA - 128 <=? x) && (x <? CA + 2592) || (SB + 137438953472 <=? x) && (x <? SB + 137438953472 + 4096) ||
                           (930696 <=? x) && (x <? 930736) || (SH <=? x) && (x <? SH + 17179869184))%bool).
  assert (Hdec : forall x, dec x = true <-> (CA - 128 <= x < CA + 2592 \/ SB + 137438953472 <= x < SB + 137438953472 + 4096 \/ 930696 <= x < 930736 \/ SH <= x < SH + 17179869184)).
  { intros x. unfold dec. rewrite !orb_true_iff, !andb_true_iff, !Z.leb_le, !Z.ltb_lt. clear. tauto. }
  set (hyb := hyb_p dec (ms_mem ms) mem0).
  assert (Hdec47 : forall x, dec x = true -> 0 <= x < 2^47).
  { intros x Hx. apply Hdec in Hx. unfold SH_LO, SH_HI, CA in *. lia. }
  assert (Hdectop : forall x, dec x = true -> x < alloc_top (m_vmmaps model)).
  { intros x Hx. apply Hdec in Hx. pose proof (alloc_top_lo _ (proj1 (dn_spok _ _ _ _ _ _ _ _ _ Hd))) as Hlo.
    pose proof (dn_gtop _ _ _ _ _ _ _ _ _ Hd) as Hgt. rewrite Forall_forall in Hgt.
    pose proof (Hgt _ (nth_error_In _ _ HgP)) as TP. pose proof (Hgt _ (nth_error_In _ _ HgT)) as TT'. rewrite ZP in TP. rewrite ZT in TT'. cbn [fst] in TP, TT'. fold PG in TP. fold TT in TT'.
    unfold SH_LO, SH_HI, CA, PG_SIZE in *. lia. }
  assert (Hhyb_in : forall x, dec x = true -> hyb (wa x) = ms_mem ms (wa x)).
  { intros x Hx. unfold hyb, hyb_p. rewrite u_wa_small by (pose proof (Hdec47 x Hx); lia). rewrite Hx. reflexivity. }
  assert (Hhyb_out : forall x, 0 <= x < 2^64 -> dec x = false -> hyb (wa x) = mem0 (wa x)).
  { intros x Hx Hn. unfold hyb, hyb_p. rewrite u_wa_small by exact Hx. rewrite Hn. reflexivity. }
  assert (HIz : INV_Az (pden E a1) hyb).
  { rewrite Epz. apply INV_Az_virgin; try assumption; [reflexivity | reflexivity | |].
    - intros x Hx. destruct (Hcell x Hx) as ((Z1 & Z2) & Hv & _).
      assert (Em : hyb (wa x) = mr (wa x)).
      { rewrite (Hhyb_in x ltac:(apply Hdec; clear - Hx; tauto)). unfold mr. cbn [restrict ms_mem]. unfold mrestrict. rewrite Hv. reflexivity. }
      split; [unfold rd1 in *; rewrite Em; exact Z1 | rewrite (wview_same mr hyb (wa x) Em); exact Z2].
    - intros x Hx. unfold wview. rewrite (Hhyb_in x ltac:(apply Hdec; right; right; right; exact Hx)), (Hshz x Hx). discriminate. }
  (* [comment removed for export] *)
  assert (HwM1 : sm_wf (s_next Sf) M1 = true) by exact (dn_wf _ _ _ _ _ _ _ _ _ D8).
  assert (Hfoot : forall x, pri_foot E a1 x -> dec x = true /\ (SH <= x < SH + 17179869184 \/ exists R, In R (s_rgs Sf) /\ uE E (rg_base R) <= x < uE E (rg_base R) + rsz E R)).
  { intros x Hf. unfold pri_foot in Hf. rewrite Epz in Hf. unfold pri_foot_z in Hf.
    change (z_ca (SB :: SH :: CA :: PG :: TT :: repeat 0 66)) with CA in Hf. change (z_sb (SB :: SH :: CA :: PG :: TT :: repeat 0 66)) with SB in Hf.
    change (z_sh (SB :: SH :: CA :: PG :: TT :: repeat 0 66)) with SH in Hf.
    destruct Hf as [Hf|[Hf|[Hf|(c & Hc & Hf)]]].
    - split; [apply Hdec; left; exact Hf|]. right. destruct (Hcell x (or_introl Hf)) as (_ & _ & R & HR & _ & Hin). exists R. split; assumption.
    - split; [apply Hdec; right; left; exact Hf|]. right. destruct (Hcell x (or_intror (or_introl Hf))) as (_ & _ & R & HR & _ & Hin). exists R. split; assumption.
    - split; [apply Hdec; right; right; left; exact Hf|]. right. destruct (Hcell x (or_intror (or_intror Hf))) as (_ & _ & R & HR & _ & Hin). exists R. split; assumption.
    - pose proof (in_cls_rng c Hc) as Hcr.
      assert (Zz : z_z (SB :: SH :: CA :: PG :: TT :: repeat 0 66) c = 0) by (unfold z_z, zn; apply nth_virgin; lia). rewrite Zz in Hf.
      assert (Hs : SH <= x < SH + 17179869184) by (clear - Hf Hcr; lia). split; [apply Hdec; right; right; right; exact Hs | left; exact Hs]. }
  assert (Hvis_sh : forall x, SH <= x < SH + 17179869184 -> Hof E M1 model (wa x) = false).
  { intros x Hx. unfold Hof. apply mkH_allowed.
    assert (EA : allowA E M1 = [allow1 E (SHl, 17179869184)] ++ allowA E M) by (unfold M1; rewrite allowA_ins; reflexivity).
    rewrite EA. apply page_allowedb_app_l. apply allow1_covers; [unfold SH_LO, SH_HI, two64 in *; lia|]. cbn [fst snd]. rewrite Hsh. exact Hx. }
  assert (Hpo : forall p, In p (pri_own a0) -> forall w, uE E (fst p) <= w < uE E (fst p) + uE E (snd p) -> pri_foot E a1 w).
  { intros p Hp w Hw. exact (pri_own_foot E a1 hyb HIz p Hp w Hw). }
  assert (D9 : DEN ASEGS LIMIT model0 hyb E Sf (with_own M1 own') ms model).
  { apply (den_own_set ASEGS LIMIT model0 mem0 hyb E Sf M1 ms model own' D8).
    - apply forallb_forall. intros p Hp. rewrite forallb_forall in Cwo. exact (Cwo p Hp).
    - intros w (q & Hq & Hqw). destruct (dn_frz _ _ _ _ _ _ _ _ _ D8 q Hq w Hqw) as (Ht & _ & _).
      pose proof (alloc_top_lo _ (proj1 (dn_spok _ _ _ _ _ _ _ _ _ D8))) as Hlo. change (Z_to_bv 64 w) with (wa w). apply Hhyb_out; [lia|].
      destruct (dec w) eqn:Ed; [|reflexivity]. pose proof (Hdectop w Ed). lia.
    - intros w (p & Hp & Hpw). exists p. split; [|exact Hpw]. cbn [with_own sm_own]. unfold own'. apply in_or_app. left.
      cbn [M1 allow_ins sm_own] in Hp. rewrite Hown_eq in Hp. exact Hp.
    - intros w (p & Hp & Hpw). cbn [with_own sm_own] in Hp. unfold own' in Hp. apply in_app_or in Hp as [Hp|Hp].
      + assert (Hp1 : In p (sm_own M1)) by (cbn [M1 allow_ins sm_own]; rewrite Hown_eq; exact Hp).
        destruct (dn_own _ _ _ _ _ _ _ _ _ D8 p Hp1 w Hpw) as [Hv Hm]. split; [exact Hv|]. intros Hout.
        change (Z_to_bv 64 w) with (wa w). destruct (dec w) eqn:Ed; [symmetry; exact (Hhyb_in w Ed)|].
        assert (Hw64 : 0 <= w < 2^64) by (pose proof (uE_range E (fst p)) as U1; pose proof (uE_range E (snd p)) as U2;
          destruct (ha_ownx _ _ _ _ HA0 w (ex_intro _ p (conj Hp Hpw))) as [Dc|[Hne _]]; [|exfalso; exact (Hne Hpnil)];
          destruct HA0 as [(n0 & F0 & st0 & I0 & _) _ _ _ _ _ _]; destruct I0 as [_ _ _ D1r _ _ _ _ _ B1r _ _ _]; unfold dcov in Dc; lia).
        rewrite (Hhyb_out w Hw64 Ed). exact (Hm Hout).
      + destruct (Hfoot w (Hpo p Hp w Hpw)) as [Ed Hw]. split.
        * destruct Hw as [Hs|(R & HR & Hin)]; [exact (Hvis_sh w Hs) | exact (den_rg_vis' LIMIT model0 mem0 E Sf M1 ms model R w D8 HR Hin)].
        * intros _. change (Z_to_bv 64 w) with (wa w). symmetry. exact (Hhyb_in w Ed). }
  (* [comment removed for export] *)
  assert (Hown_in : forall p, In p (pri_own a0) -> In p (sm_own (with_own M1 own'))) by (intros p Hp; cbn [with_own sm_own]; unfold own'; apply in_or_app; right; exact Hp).
  assert (D10 : DEN ASEGS LIMIT model0 hyb E (with_rgs S (G6 ++ [RCA; RGQ])) (with_own M1 own') ms model).
  { pose proof (OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChMprot.AcAddOwn.den_drop_own ASEGS LIMIT model0 hyb E Sf (with_own M1 own') ms model (length G6) RRI D9 (nth_error_app_len G6 [RCA; RGQ] RRI)) as X.
    unfold dropo_post in X. cbn [Sf with_rgs s_pc s_regs s_rgs s_facts s_next s_resv] in X. rewrite remove_nth_app_len in X. apply X.
    intros w Hw. destruct BRI as [B1 B2]. rewrite B1, B2 in Hw. split.
    - exists (l_rip a0, lconst 4096). split; [apply Hown_in; right; left; reflexivity|]. cbn [fst snd]. rewrite uE_lc by lia.
      change (l_rip a0) with (laddc SBl 137438953472). rewrite uE_laddc2 by (first [lia | fold SB; unfold two64; lia]). fold SB. exact Hw.
    - change (Z_to_bv 64 w) with (wa w). symmetry. apply Hhyb_in. apply Hdec. right. left. exact Hw. }
  assert (D11 : DEN ASEGS LIMIT model0 hyb E (with_rgs S (G6 ++ [RGQ])) (with_own M1 own') ms model).
  { pose proof (OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChMprot.AcAddOwn.den_drop_own ASEGS LIMIT model0 hyb E _ (with_own M1 own') ms model (length G6) RCA D10 (nth_error_app_len G6 [RGQ] RCA)) as X.
    unfold dropo_post in X. cbn [with_rgs s_pc s_regs s_rgs s_facts s_next s_resv] in X. rewrite remove_nth_app_len in X. apply X.
    intros w Hw. destruct BCA as [B1 B2]. rewrite B1, B2 in Hw. split.
    - exists (l_cb a0, lconst CB_SIZE). split; [apply Hown_in; left; reflexivity|]. cbn [fst snd]. unfold CB_SIZE. rewrite uE_lc by lia.
      change (l_cb a0) with (laddc CAl (-128)). rewrite uE_laddc_z by (rewrite Eca; unfold two64, CA in *; lia). rewrite Eca. unfold CA in *. lia.
    - change (Z_to_bv 64 w) with (wa w). symmetry. apply Hhyb_in. apply Hdec. left. lia. }
  assert (D12 : DEN ASEGS LIMIT model0 hyb E (with_rgs S G6) (with_own M1 own') ms model).
  { pose proof (OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChMprot.AcAddOwn.den_drop_own ASEGS LIMIT model0 hyb E _ (with_own M1 own') ms model (length G6) RGQ D11 (nth_error_app_len G6 [] RGQ)) as X.
    unfold dropo_post in X. cbn [with_rgs s_pc s_regs s_rgs s_facts s_next s_resv] in X. rewrite remove_nth_app_len, app_nil_r in X. apply X.
    intros w Hw. destruct BGQ as [B1 B2]. rewrite B1, B2 in Hw. split.
    - exists (lconst 930696, lconst 40). split; [apply Hown_in; right; right; left; reflexivity|]. cbn [fst snd]. rewrite !uE_lc by lia. exact Hw.
    - change (Z_to_bv 64 w) with (wa w). symmetry. apply Hhyb_in. apply Hdec. right. right. left. lia. }
  (* [comment removed for export] *)
  assert (Hdown : forall x, 0 <= x < 2^64 -> downed (dD1 E a) (dB1 E a) x -> hyb (wa x) = mem0 (wa x)).
  { intros x Hx Hdw. apply (Hhyb_out x Hx). destruct (dec x) eqn:Ed; [|reflexivity]. exfalso. apply Hdec in Ed.
    destruct (ha_hi _ _ _ _ HA0) as [Hh1 Hh2]. destruct (ha_gD1 _ _ _ _ HA0) as (k1 & Hg1). destruct (ha_gB1 _ _ _ _ HA0) as (k2 & Hg2).
    pose proof (grant_above_image LIMIT model0 mem0 E S M ms model _ Hd Hg1 (is_mark_csize _ _ _) ltac:(unfold gsz; cbn [fst snd]; rewrite uE_lc by lia; lia)) as Ha1.
    pose proof (grant_above_image LIMIT model0 mem0 E S M ms model _ Hd Hg2 (is_mark_csize _ _ _) ltac:(unfold gsz; cbn [fst snd]; rewrite uE_lc by lia; lia)) as Ha2.
    cbn [fst] in Ha1, Ha2. fold (dD1 E a) in Ha1. fold (dB1 E a) in Ha2.
    pose proof (grants_apart_in LIMIT model0 mem0 E S M ms model _ _ _ _ _ _ Hd Hg1 (nth_error_In _ _ HgT) ltac:(unfold TG_SIZE; intros Q; vm_compute in Q; discriminate Q) ltac:(lia) ltac:(unfold TG_SIZE; lia)) as A1.
    pose proof (grants_apart_in LIMIT model0 mem0 E S M ms model _ _ _ _ _ _ Hd Hg1 (nth_error_In _ _ HgP) ltac:(unfold PG_SIZE; intros Q; vm_compute in Q; discriminate Q) ltac:(lia) ltac:(unfold PG_SIZE; lia)) as A2.
    pose proof (grants_apart_in LIMIT model0 mem0 E S M ms model _ _ _ _ _ _ Hd Hg2 (nth_error_In _ _ HgT) ltac:(unfold TG_SIZE; intros Q; vm_compute in Q; discriminate Q) ltac:(lia) ltac:(unfold TG_SIZE; lia)) as A3.
    pose proof (grants_apart_in LIMIT model0 mem0 E S M ms model _ _ _ _ _ _ Hd Hg2 (nth_error_In _ _ HgP) ltac:(unfold PG_SIZE; intros Q; vm_compute in Q; discriminate Q) ltac:(lia) ltac:(unfold PG_SIZE; lia)) as A4.
    fold (dD1 E a) in A1, A2. fold (dB1 E a) in A3, A4. fold TT in A1, A3. fold PG in A2, A4.
    destruct (downed_cases _ _ x Hdw) as [D|[D|[D|D]]]; clear - D Ed Hh1 Hh2 Ha1 Ha2 A1 A2 A3 A4 HTpl Q1 Q5 Q6 Q7 Hsb47 HshR;
      unfold DT_LO, DT_HI, DF_LO, DF_HI, SH_LO, SH_HI, CA, PG_SIZE, TG_SIZE in *; lia. }
  (* [comment removed for export] *)
  assert (Hzr : forall x, SH <= x < SH + 17179869184 -> in_zr (sm_zr M) x = true).
  { intros x Hx. unfold zr_cover in Cn5. apply existsb_exists in Cn5 as (p & Hp & Hc). apply andb_prop in Hc as [C1 C2]. apply Z.leb_le in C1, C2.
    unfold in_zr. apply existsb_exists. exists p. split; [exact Hp|]. apply andb_true_intro.
    assert (D1' : fst (irange (s_facts S) SBl) / 8 <= SB / 8) by (apply Z.div_le_mono; lia).
    assert (D2' : SB / 8 <= snd (irange (s_facts S) SBl) / 8) by (apply Z.div_le_mono; lia).
    split; [apply Z.leb_le | apply Z.ltb_lt]; unfold SH in Hx; lia. }
  assert (HA' : HA E (with_own M1 own') a' hyb).
  { intros _. destruct HA0 as [Hdep Hown0 Haown Hhi HgD HgB _]. constructor.
    - destruct Hdep as (n & F & st & I & Rn). exists n, F, st. split; [exact (INV_D_frame _ _ _ _ _ _ _ I Hdown) | exact Rn].
    - intros x Hx Hdw. destruct (Hown0 x Hx Hdw) as (p & Hp & Hpw). exists p. split; [|exact Hpw].
      cbn [with_own sm_own]. unfold own'. apply in_or_app. left. rewrite <- Hown_eq. exact Hp.
    - cbn [a' a_own a1 with_pri]. unfold own'. rewrite Haown at 1. unfold aown_of. rewrite Hpnil, app_nil_r. reflexivity.
    - exact Hhi.
    - exact HgD.
    - exact HgB.
    - intros _. constructor.
      + unfold INV_A. rewrite Epz'. exact HIz.
      + intros x Hx Hf. unfold pri_foot in Hf. rewrite Epz' in Hf. destruct (pri_foot_own E a1 hyb HIz x Hf) as (p & Hp & Hpw).
        exists p. split; [exact (Hown_in p Hp) | exact Hpw].
      + exists kp. exact (nth_error_In _ _ HgP).
      + exists kt. exact (nth_error_In _ _ HgT).
      + intros x (c & Hc & Hx). rewrite Epz', Epz in Hx. change (z_sh (SB :: SH :: CA :: PG :: TT :: repeat 0 66)) with SH in Hx.
        pose proof (in_cls_rng c Hc) as Hcr. apply (Hzr x). lia.
      + exact Hsepc'.
      + intros p Hp. exfalso. change (a_ext a') with (a_ext a1) in Hp. rewrite Hx1 in Hp. destruct Hp.
      + (* [comment removed for export] *)
        apply lv_inv_none; [unfold lv_cnt; change (a_fcts a') with (a_fcts a); rewrite Hfnil; reflexivity|].
        unfold e_rngs. change (a_ext a') with (a_ext a1). rewrite Hx1. intros i j p q _ Hi. destruct i; discriminate Hi.
      + exact Hsepd'. }
  apply (Hk E hyb ms model (agree_refl _ _)).
  - intros q Hq w Hw. destruct (dn_frz _ _ _ _ _ _ _ _ _ Hd q Hq w Hw) as (Ht & _ & _).
    pose proof (alloc_top_lo _ (proj1 (dn_spok _ _ _ _ _ _ _ _ _ Hd))) as Hlo. change (Z_to_bv 64 w) with (wa w). apply Hhyb_out; [lia|].
    destruct (dec w) eqn:Ed; [|reflexivity]. pose proof (Hdectop w Ed). lia.
  - exact D12.
  - exact HA'.
Qed.
End ConvAN.
(* [comment removed for export] *)
End AcConvAN.

Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Lemma IMGP_ok : img_ok ASEGS IMGP.
Proof. unfold IMGP. apply mk_img_runs_ok; [repeat constructor; cbn; lia | intros p w H; rewrite tget_empty in H; discriminate]. Qed.

Lemma existsb_eqb_in : forall c l, existsb (Z.eqb c) l = true -> In c l.
Proof. intros c l H. apply existsb_exists in H as (x & Hx & He). apply Z.eqb_eq in He. subst x. exact Hx. Qed.

Lemma regs_wf_n_mono : forall n n' R k, (n <= n')%positive -> regs_wf_n n R k = true -> regs_wf_n n' R k = true.
Proof.
  intros n n' R k Hn. induction k as [|k IH]; intros H; [reflexivity|]. cbn [regs_wf_n] in *. apply andb_prop in H as [H1 H2].
  rewrite (lwf_mono' n n' _ Hn H1), (IH H2). reflexivity.
Qed.
Lemma np_front_wf_mono : forall S n n' rgs, (n <= n')%positive -> state_wf (np_front S n rgs) = true -> state_wf (np_front S n' rgs) = true.
Proof.
  intros S n n' rgs Hn H. unfold state_wf, np_front in *. cbn [s_next s_regs s_rgs s_facts s_resv] in *.
  apply andb_prop in H as [H _]. apply andb_prop in H as [H _]. apply andb_prop in H as [H1 H2].
  rewrite (regs_wf_n_mono n n' _ _ Hn H1). cbn [forallb rsv_wf]. rewrite !andb_true_r.
  apply forallb_forall. intros R HR. rewrite forallb_forall in H2. exact (rwf_mono n n' R Hn (H2 R HR)).
Qed.

Section NPopNode.
Variable cfg : SpuriousCfg.
Variable LIMIT : Z.
Variable model0 : Model.
Hypothesis Hwx : wx_segs_nowrap ASEGS.

#[using="Hwx"] Theorem npop_node_pop : forall c S M a S' M' a', apost_npop0 LIMIT c S M a = Some (S', M', a') ->
  forall mem0 E ms model T, DEN ASEGS LIMIT model0 mem0 E S M ms model -> awf (s_next S) a = true -> HA E M a mem0 ->
  1 <= z_j (pden E a) c ->
  (forall E' mem0' ms' model', agree (s_next S) E E' -> frz_same E M mem0 mem0' -> DEN ASEGS LIMIT model0 mem0' E' S' M' ms' model' ->
     HA E' M' a' mem0' -> realizes_cfg ASEGS cfg (mkCfg ms' model') T) ->
  realizes_cfg ASEGS cfg (mkCfg ms model) T.
Proof. LiaFast.lf_pins (fun (Hwx : LiaFast.U) => LiaFast.u0).
  intros c S M a S' M' a' H mem0 E ms model T Hd Haw HHA Hj1 Hk.
  unfold apost_npop0 in H. cbv zeta in H.
  apply obool_some in H as (Hon & H).
  apply obind_some in H as (stk & Hstk & H). cbv beta in H.
  apply obind_some in H as (ro & Hro & H). cbv beta in H.
  apply obind_some in H as (ist & Hist & H). cbv beta in H.
  apply obind_some in H as (R & HR & H). cbv beta in H.
  apply obind_some in H as (o & Ho & H). cbv beta in H.
  apply obind_some in H as (cv & Hcv & H). cbv beta in H.
  apply obind_some in H as (jP & HjP & H). cbv beta in H.
  apply obind_some in H as (jT & HjT & H). cbv beta in H.
  apply obind_some in H as (gP & HgP & H). cbv beta in H.
  apply obool_some in H as (Hchk & H).
  apply obind_some in H as (l'' & Hsteps & H). cbv beta in H. injection H as <- <- <-.
  apply andb_prop in Hon as [Hon Hown_eq]. apply andb_prop in Hon as [Hon Hrs]. apply andb_prop in Hon as [Hon Hpc].
  apply andb_prop in Hon as [Hon Hcin]. apply andb_prop in Hon as [Hon Hlen].
  apply Z.eqb_eq in Hpc. apply rsv_none_b_sound in Hrs. apply Nat.eqb_eq in Hlen. apply existsb_eqb_in in Hcin.
  apply (list_eqb_eq pair_eqb pair_eqb_eq) in Hown_eq.
  apply andb_prop in Hchk as [Hchk Cfu]. apply andb_prop in Hchk as [Hchk Csep]. apply andb_prop in Hchk as [Hchk Cwo].
  apply andb_prop in Hchk as [Hchk Cwp]. apply andb_prop in Hchk as [Hchk CpX]. apply andb_prop in Hchk as [Hchk CwL].
  apply andb_prop in Hchk as [Hchk Cband]. apply andb_prop in Hchk as [Hchk Cge]. apply andb_prop in Hchk as [Hchk Cjb].
  apply andb_prop in Hchk as [Hchk Csbw]. apply andb_prop in Hchk as [Hchk Cst]. apply andb_prop in Hchk as [Hchk Cro].
  apply andb_prop in Hchk as [Hchk Cwin]. apply andb_prop in Hchk as [Hchk Csphi]. apply andb_prop in Hchk as [Hchk Csplo].
  apply andb_prop in Hchk as [Hchk Cmod]. apply andb_prop in Hchk as [Hchk Cndhi]. apply andb_prop in Hchk as [Hchk Cndlo].
  apply andb_prop in Hchk as [Hchk Ca3]. apply andb_prop in Hchk as [Hchk Ca1]. apply andb_prop in Hchk as [Cperm Ca0].
  apply lin_eqb_eq in Ca0, Ca1, Ca3. apply Z.leb_le in Cndlo, Cndhi, Csplo, Csphi, Cjb.
  set (SPl := rget (s_regs S) (rk 2)) in *.
  set (front := firstn 3 (carve_rgs cv)) in *. set (rest := skipn 3 (carve_rgs cv)) in *.
  set (L := np_front S (s_next S) front) in *. set (Sp := np_rest S rest) in *.
  set (Lb := np_front S (s_next S + 66) front) in *.
  pose proof (HHA Hon) as HA0.
  assert (Hne : a_pri a <> []) by (intros Hn; rewrite Hn in Hlen; discriminate).
  pose proof (ha_pri _ _ _ _ HA0 Hne) as HP0.
  (* [comment removed for export] *)
  pose proof (den_carve ASEGS LIMIT model0 mem0 E S M ms model _ _ _ cv Hd Hcv Cperm) as Hd1.
  assert (EQ1 : with_rgs S (carve_rgs cv) = mrg L Sp).
  { destruct S as [pc0 rg0 rgs0 fs0 nx0 rv0]. cbn [s_pc s_resv] in Hpc, Hrs. subst pc0 rv0.
    unfold with_rgs, mrg, L, Sp, np_front, np_rest. cbn [s_pc s_regs s_rgs s_facts s_next s_resv]. unfold front, rest. rewrite firstn_skipn. reflexivity. }
  rewrite EQ1 in Hd1.
  assert (EQb : bump (mrg L Sp) (s_next S + 66) = mrg Lb Sp) by reflexivity.
  pose proof (den_bump ASEGS LIMIT model0 mem0 E _ M ms model (s_next S + 66)%positive Hd1 ltac:(cbn [mrg s_next L np_front]; lia)) as Hd2.
  rewrite EQb in Hd2.
  (* [comment removed for export] *)
  pose proof (po_inv _ _ _ _ HP0) as HI. unfold INV_A in HI. set (pz := pden E a) in *.
  pose proof (tg_pg_disj LIMIT model0 mem0 E S M ms model a mem0 Hd HP0) as Hdisj. fold pz in Hdisj.
  pose proof (az_geo pz mem0 HI) as G. pose proof (in_cls_rng c Hcin) as Hcr.
  destruct (cls_tbl c Hcin) as (Hszp & Hs8 & Hsz8 & Hnw & Hnm & Hmc).
  pose proof (sden_0 _ _ _ _ (dn_sden _ _ _ _ _ _ _ _ _ Hd)) as (_ & _ & _ & _ & HRG & _ & HF0 & _).
  assert (Ej : uE E (p_j a c) = z_j pz c) by (symmetry; apply zn_pden).
  assert (Eca : uE E (p_ca a) = z_ca pz) by (symmetry; apply zn_pden).
  assert (Esb : uE E (p_sb a) = z_sb pz) by (symmetry; apply zn_pden).
  assert (Hjhi : z_j pz c + mc_tbl c / 2 + 1 <= 262144 / sz_tbl c).
  { pose proof (irange_sound E (s_facts S) (p_j a c) HF0) as X. fold (uE E (p_j a c)) in X. rewrite Ej in X. clear - X Cjb. lia. }
  destruct (iz_cls _ _ HI c Hcin) as [(J0 & _)|(_ & Z1 & Jb & HIo & HPo)]; [clear - J0 Hj1; lia|].
  pose proof (iz_st _ _ HI) as HST.
  (* [comment removed for export] *)
  set (ndl := rget (s_regs S) (rk 12)) in *.
  pose proof (irange_sound E (s_facts S) SPl HF0) as Rsp. fold (uE E SPl) in Rsp.
  pose proof (irange_sound E (s_facts S) ndl HF0) as Rnd. fold (uE E ndl) in Rnd.
  assert (Hal : uE E SPl mod 16 = 0) by (pose proof (fact_implied_ok E _ _ HF0 Cmod) as X; cbn [fact_ok] in X; exact X).
  assert (HND : sz_tbl (c - 1) < uE E ndl <= sz_tbl c) by (clear - Rnd Cndlo Cndhi; lia).
  assert (HND1 : 1 <= uE E ndl <= 65536).
  { assert (0 <= sz_tbl (c - 1)) by (clear - Hcr; assert (Hc0 : c - 1 = 0 \/ In (c - 1) CLS) by (unfold CLS; cbn [In]; lia);
      destruct Hc0 as [->|Hc0]; [cbn; lia | destruct (cls_tbl _ Hc0) as (X & _); lia]). clear - H HND Hszp. lia. }
  (* [comment removed for export] *)
  destruct (rg_hdr_b_sound _ _ _ _ Cwin) as (cw & Pw). destruct (ro_b_sound _ Cro) as (zro & Hzro & Pro).
  destruct (rg_hdr_b_sound _ _ _ _ Cst) as (cs & Pst).
  assert (PS : np_shape Lb SPl (p_ca a) ndl 0 1 2).
  { constructor; cbn [Lb np_front s_pc s_resv s_regs s_rgs]; try reflexivity; try assumption.
    - exists cw. exact Pw.
    - exists zro. split; [exact Hzro | exact Pro].
    - exists (laddc (p_tg a) 2872), cs. exact Pst. }
  assert (HwLb : state_wf Lb = true) by (apply (np_front_wf_mono S (s_next S) (s_next S + 66)%positive front ltac:(lia) CwL)).
  (* [comment removed for export] *)
  unfold sb_words_ok in Csbw. destruct (rdw IMGP (s_rgs S) (lconst 929848) 8) as [l1|] eqn:W1; [|discriminate].
  destruct (rdw IMGP (s_rgs S) (lconst 929864) 8) as [l2|] eqn:W2; [|discriminate].
  apply andb_prop in Csbw as [Q1 Q2]. apply lin_eqb_eq in Q1, Q2. subst l1 l2.
  pose proof (rdw_sound IMGP IMGP_ok E _ (s_rgs S) (lconst 929848) 8 _ HRG ltac:(lia) W1) as RSB.
  pose proof (rdw_sound IMGP IMGP_ok E _ (s_rgs S) (lconst 929864) 8 _ HRG ltac:(lia) W2) as RRIB.
  rewrite uE_lc in RSB, RRIB by lia. rewrite Esb in RSB.
  assert (Erip : uE E (l_rip a) = z_sb pz + 137438953472).
  { unfold l_rip. rewrite uE_laddc2 by (rewrite ?Esb; unfold two64; clear - G; lia). rewrite Esb. reflexivity. }
  rewrite Erip in RRIB.
  (* [comment removed for export] *)
  assert (HCELL : forall x, 0 <= x < 2^64 -> ncell (z_ca pz) (z_sb pz) c (262144 / sz_tbl c) x ->
            own_pt E M x /\ outside E (s_rgs (mrg Lb Sp)) (wa x) /\ ~ frz_pt E M x).
  { intros x Hx Hn. destruct (ncell_fp pz mem0 HI Hdisj c x Hcin Z1 Hn) as (F1 & F2 & F3 & F4).
    split; [exact (po_own _ _ _ _ HP0 x Hx F1)|]. split.
    - exact (pri_outside_den LIMIT model0 mem0 E (mrg L Sp) M ms model a mem0 jP jT Hd1 HP0 HjP HjT Csep x ltac:(unfold two64; lia) F2 F3).
    - exact (pri_not_frz LIMIT model0 mem0 E S M ms model a mem0 Hd HA0 Hne x F1). }
  (* [comment removed for export] *)
  destruct (po_gp _ _ _ _ HP0) as (kp & Hgp). destruct (po_gt _ _ _ _ HP0) as (kt & Hgt).
  pose proof (band_hi LIMIT model0 mem0 E S M ms model SPl _ Hd Cband Hgp) as BP.
  pose proof (band_hi LIMIT model0 mem0 E S M ms model SPl _ Hd Cband Hgt) as BT.
  unfold gsz in BP, BT. cbn [fst snd] in BP, BT. unfold PG_SIZE, TG_SIZE in BP, BT. rewrite uE_lc in BP, BT by lia.
  assert (Epg : uE E (p_pg a) = z_pg pz) by (symmetry; apply zn_pden).
  assert (Etg : uE E (p_tg a) = z_tg pz) by (symmetry; apply zn_pden).
  rewrite Epg in BP. rewrite Etg in BT. fold (uE E SPl) in BP, BT.
  assert (ECA : uE E (p_ca a) = z_ca pz) by exact Eca.
  apply (den_npop_app cfg LIMIT model0 Hwx mem0 Lb Sp E M ms model T SPl (p_ca a) ndl 0 1 2 c (z_sb pz) (sz_tbl c) (mc_tbl c / 2) (262144 / sz_tbl c) (z_j pz c)
           Hd2 HwLb PS).
  - symmetry. exact (cls_of_tbl c (uE E ndl) Hcr HND).
  - exact HND1.
  - clear - Rsp Csplo Csphi. lia.
  - exact Hal.
  - rewrite ECA. exact HIo.
  - rewrite ECA. exact HST.
  - clear - Hjhi. lia.
  - exact RSB.
  - exact RRIB.
  - rewrite ECA. exact HCELL.
  - rewrite ECA. pose proof (iz_ca _ _ HI) as (X1 & X2 & X3). fold pz in X1, X2, X3. split; [exact X1|]. split; [exact X2|]. clear - G BT. lia.
  - pose proof (proj2 (iz_sb _ _ HI)) as X2. clear - G BP X2. split; [lia|]. split; [exact X2 | lia].
  - rewrite ECA. clear - G Hdisj. unfold PG_SIZE in Hdisj. lia.
  - intros E' ms' model' HD' Ha' Hfz' HI3 HST3 HR10 Hfr3.
    rewrite ECA in HI3, HST3, Hfr3.
    set (Lh := hand_post Lb 279076 KALLk [0%nat; 2%nat]) in *.
    set (hyb := hyb_p (ncell_b (z_ca pz) (z_sb pz) c (262144 / sz_tbl c)) (ms_mem ms') mem0).
    assert (HwfM : sm_wf (s_next Lb) M = true) by exact (dn_wf _ _ _ _ _ _ _ _ _ Hd2).
    assert (HbwS : bases_wf (s_next Lb) (s_rgs (mrg Lb Sp)) = true) by exact (dn_bases _ _ _ _ _ _ _ _ _ Hd2).
    assert (Hsh : shape (s_rgs (mrg Lh Sp)) = shape (s_rgs (mrg Lb Sp))).
    { cbn [mrg s_rgs]. unfold Lh, hand_post. cbn [s_rgs]. unfold shape. rewrite !map_app. f_equal.
      pose proof (empty_at_shape [0%nat; 2%nat] (s_rgs Lb) 0) as Hs. unfold shape in Hs. exact Hs. }
    pose proof (dn_own _ _ _ _ _ _ _ _ _ Hd2) as Hown2.
    (* [comment removed for export] *)
    assert (Hnwin : forall w, outside E (s_rgs (mrg Lb Sp)) (Z_to_bv 64 w) -> 0 <= w < two64 -> ~ (uE E SPl - 2048 <= w < uE E SPl)).
    { intros w Hout Hw Hc0. unfold outside in Hout. rewrite Forall_forall in Hout. cbn [mrg s_rgs] in Hout.
      specialize (Hout _ ltac:(apply in_or_app; left; exact (nth_error_In _ _ Pw))). cbn [rg_base] in Hout.
      unfold rsz in Hout. cbn [rg_size] in Hout. rewrite lden_lconst, (u_small64 2048) in Hout by (unfold two64; lia).
      rewrite lden_laddc in Hout. fold (uE E SPl) in Hout. rewrite (u_small64 (uE E SPl + -2048)) in Hout by (clear - Rsp Csplo Csphi; unfold two64; lia).
      rewrite u_small64 in Hout by exact Hw. clear - Hout Hc0. lia. }
    (* [comment removed for export] *)
    assert (Hkeep0 : forall w, 0 <= w < two64 -> own_pt E M w -> outside E (s_rgs (mrg Lb Sp)) (Z_to_bv 64 w) ->
              ~ owned_C (z_ca pz) (z_sb pz) c w -> ms_mem ms' (Z_to_bv 64 w) = mem0 (Z_to_bv 64 w)).
    { intros w Hw (q & Hq & Hqw) Hout Hnc. destruct (Hown2 q Hq w Hqw) as [Hv Hm]. rewrite <- (Hm Hout).
      apply Hfr3; [unfold two64 in Hw; lia | exact Hv | exact (Hnwin w Hout Hw) | exact Hnc]. }
    assert (Hkeep : forall w, 0 <= w < two64 -> own_pt E M w -> outside E (s_rgs (mrg Lb Sp)) (Z_to_bv 64 w) ->
              ~ ncell (z_ca pz) (z_sb pz) c (262144 / sz_tbl c) w -> ms_mem ms' (Z_to_bv 64 w) = mem0 (Z_to_bv 64 w)).
    { intros w Hw Hq Hout Hnc. apply (Hkeep0 w Hw Hq Hout).
      intros Hoc. apply Hnc. unfold owned_C in Hoc. unfold ncell, foot_Co. clear - Hoc. lia. }
    assert (Hfrzn : forall w, frz_pt E M w -> hyb (Z_to_bv 64 w) = mem0 (Z_to_bv 64 w)).
    { intros w Hw. unfold hyb, hyb_p. destruct (ncell_b _ _ _ _ _); [exact (Hfz' w Hw) | reflexivity]. }
    assert (HD3 : DEN ASEGS LIMIT model0 hyb E' (mrg Lh Sp) M ms' model').
    { apply (den_snap ASEGS LIMIT model0 (ms_mem ms') hyb E' _ M ms' model' HD').
      - intros w Hw. pose proof (proj1 (frz_pt_agree (s_next Lb) E E' M w HwfM Ha') Hw) as Hw0.
        rewrite (Hfrzn w Hw0). symmetry. exact (Hfz' w Hw0).
      - intros w Hw Hout. unfold hyb, hyb_p.
        destruct (ncell_b (z_ca pz) (z_sb pz) c (262144 / sz_tbl c) (bv_unsigned (Z_to_bv 64 w))) eqn:Eb; [reflexivity|].
        assert (Hw0 : own_pt E M w) by exact (proj1 (own_pt_agree (s_next Lb) E E' M w HwfM Ha') Hw).
        assert (Hout0 : outside E (s_rgs (mrg Lb Sp)) (Z_to_bv 64 w)) by exact (outside_agree_shape _ E E' _ _ _ HbwS Ha' Hsh Hout).
        assert (Hw64 : 0 <= w < two64).
        { destruct Hw0 as (q & Hq & Hqw). pose proof (uE_range E (fst q)). destruct (Hown2 q Hq w Hqw) as [Hv _].
          destruct (Z_lt_le_dec w two64) as [X|X]; [lia|]. exfalso.
          (* [comment removed for export] *)
          destruct (ha_ownx _ _ _ _ HA0 w (own_pt_a_M E M a w Hown_eq (ex_intro _ q (conj Hq Hqw)))) as [Dc|[_ Pf]].
          - destruct HA0 as [(n0 & F0 & st0 & I0 & _) _ _ _ _ _ _]. destruct I0 as [_ _ _ D1r _ _ _ _ _ B1r _ _ _].
            unfold dcov in Dc. unfold two64 in X. clear - Dc X D1r B1r. lia.
          - pose proof (pri_foot_rng E a mem0 HI w Pf). unfold two64 in X. lia. }
        rewrite u_small64 in Eb by exact Hw64. symmetry. apply (Hkeep w Hw64 Hw0 Hout0).
        intros Hn. apply ncell_b_spec in Hn. congruence. }
    (* [comment removed for export] *)
    pose proof (awf_pri _ a Haw) as Hwpri.
    assert (Hagr : forall E'', agree (s_next (mrg Lh Sp)) E' E'' -> agree (s_next S) E E'').
    { intros E'' Ha''. apply (agree_trans _ E E' E''); [apply (agree_mono _ (s_next Lb)); [cbn [Lb np_front s_next]; lia | exact Ha'] |
        apply (agree_mono _ (s_next (mrg Lh Sp))); [cbn [mrg Lh hand_post Lb np_front s_next]; lia | exact Ha'']]. }
    assert (Echk : uE E (chunk_lin a c) = z_sb pz + sz_tbl c * z_j pz c + 4294967296 * c).
    { unfold chunk_lin. rewrite u_lin3; [rewrite Esb, Ej; reflexivity | clear - Hszp; lia | clear - Hcr; lia |].
      rewrite Esb, Ej. destruct (cls_jb pz mem0 HI c Hcin) as (K0 & K1 & _). clear - G K0 K1 Hcr. unfold two64. lia. }
    assert (Hch : forall E'', agree (s_next (mrg Lh Sp)) E' E'' -> lden E'' (chunk_lin a c) = lden E'' (rget (s_regs (mrg Lh Sp)) (rk 10))).
    { intros E'' Ha''. pose proof (dn_sden _ _ _ _ _ _ _ _ _ HD3 E'' Ha'') as (_ & _ & _ & Hregs & _).
      specialize (Hregs (Z_to_bv 5 10)). cbn [restrict ms_regs] in Hregs. change (rkey (Z_to_bv 5 10)) with (rk 10) in Hregs.
      rewrite <- Hregs, HR10.
      rewrite (lden_agree_wf (s_next S) E E'' _ (proj1 (lwf_chunk_lin _ a c Hwpri)) (Hagr E'' Ha'')).
      rewrite <- (Z_to_bv_bv_unsigned _ (lden E (chunk_lin a c))). fold (uE E (chunk_lin a c)). rewrite Echk. unfold wa. f_equal. ring. }
    assert (Hrk : rk 10 <> xH) by (intros Hc0; vm_compute in Hc0; discriminate).
    pose proof (den_reg_eq ASEGS LIMIT model0 hyb E' _ M ms' model' (rk 10) (chunk_lin a c) HD3 Hrk Hch) as HD4.
    set (X := with_reg (mrg Lh Sp) (rk 10) (chunk_lin a c)) in *.
    pose proof (den_uncarve ASEGS LIMIT model0 hyb E' X M ms' model' _ _ l'' HD4 CpX Hsteps) as HD5.
    (* [comment removed for export] *)
    assert (HawLb : awf (s_next Lb) a = true) by (apply (awf_mono (s_next S)); [cbn [Lb np_front s_next]; lia | exact Haw]).
    pose proof (HA_on_agree (s_next Lb) E E' M a mem0 HA0 HwfM HawLb Ha') as HA0'.
    assert (Epz' : pden E' a = pz) by exact (pden_agree (s_next Lb) E E' a HawLb Ha').
    assert (T1 : z_ca pz + 2592 <= z_pg pz \/ z_pg pz + 137439023104 <= z_ca pz - 128) by (clear - Hdisj G; unfold PG_SIZE in Hdisj; lia).
    assert (S1 : 2199291686912 + 2147450880 <= z_sh pz /\ z_sh pz + 17179869184 <= z_pg pz) by (clear - G; lia).
    assert (S2 : z_ca pz + 2592 <= z_sh pz \/ z_sh pz + 17179869184 <= z_ca pz - 128) by (clear - G S1; lia).
    pose proof (sden_0 _ _ _ _ (dn_sden _ _ _ _ _ _ _ _ _ HD4)) as (_ & _ & _ & _ & _ & _ & HF4 & _).
    assert (Hnewpt : forall x, pri_foot_z pz x -> FPmax pz x -> ~ alloc_part pz x -> 0 <= x < 2^47 ->
              ~ ncell (z_ca pz) (z_sb pz) c (262144 / sz_tbl c) x ->
              own_pt E' M x /\ outside E' l'' (Z_to_bv 64 x) /\ ms_mem ms' (Z_to_bv 64 x) = mem0 (Z_to_bv 64 x)).
    { intros x F1 F2 F3 F4 F5. assert (Hx64 : 0 <= x < two64) by (unfold two64; clear - F4; lia).
      assert (Hox : own_pt E M x) by (apply (po_own _ _ _ _ HP0 x); [clear - F4; lia | exact F1]).
      pose proof (pri_outside_den LIMIT model0 mem0 E (mrg L Sp) M ms model a mem0 jP jT Hd1 HP0 HjP HjT Csep x Hx64 F2 F3) as Hout.
      split; [exact (proj2 (own_pt_agree (s_next Lb) E E' M x HwfM Ha') Hox)|]. split.
      - apply (uncarve_outside E' X _ 2 stk l'' _ HF4 CpX Hsteps).
        apply (outside_shape E' (s_rgs (mrg Lb Sp))); [exact Hsh|]. exact (proj1 (outside_agree (s_next Lb) E E' _ _ HbwS Ha') Hout).
      - exact (Hkeep x Hx64 Hox Hout F5). }
    destruct (cls_jb pz mem0 HI c Hcin) as (K0 & K1 & K2 & _).
    assert (Hjn : z_j pz c + 1 <= 262144 / sz_tbl c) by (clear - Hjhi Hmc; lia).
    set (CHB := z_sb pz + 4294967296 * c + sz_tbl c * z_j pz c) in *.
    set (CHS := z_sh pz + 536870912 * c + sz_tbl c / 8 * z_j pz c) in *.
    assert (HwLc : lwf (s_next Lb) (chunk_lin a c) = true /\ lwf (s_next Lb) (chsh_lin a c) = true).
    { destruct (lwf_chunk_lin (s_next S) a c Hwpri) as [W1' W2'].
      split; apply (lwf_mono' (s_next S) (s_next Lb)); first [assumption | cbn [Lb np_front s_next]; lia]. }
    assert (Echk' : uE E' (chunk_lin a c) = CHB).
    { rewrite (uE_agree (s_next Lb) E E' _ (proj1 HwLc) Ha'). rewrite Echk. unfold CHB. ring. }
    assert (Echs : uE E (chsh_lin a c) = CHS).
    { unfold chsh_lin. assert (Esh : uE E (p_sh a) = z_sh pz) by (symmetry; apply zn_pden).
      rewrite u_lin3; [rewrite Esh, Ej; unfold CHS; ring | clear - Hsz8; lia | clear - Hcr; lia |].
      rewrite Esh, Ej. clear - G S1 K0 K2 Hcr. unfold two64. lia. }
    assert (Echs' : uE E' (chsh_lin a c) = CHS).
    { rewrite (uE_agree (s_next Lb) E E' _ (proj2 HwLc) Ha'). exact Echs. }
    (* [comment removed for export] *)
    assert (Hcpt : forall x, CHB <= x < CHB + sz_tbl c ->
              own_pt E' M x /\ outside E' l'' (Z_to_bv 64 x) /\ ms_mem ms' (Z_to_bv 64 x) = Some (Z_to_bv 8 0) /\ app_pt model' x /\ x < alloc_top (m_vmmaps model')).
    { intros x Hx. destruct (chunk_fp pz mem0 HI c x Hcin Z1 Hjn Hx) as (F1 & F2 & F3 & F4 & F5).
      assert (F6 : ~ ncell (z_ca pz) (z_sb pz) c (262144 / sz_tbl c) x).
      { unfold ncell, foot_Co. unfold CHB in Hx. clear - Hx F5 T1 G Hcr K0 Hszp. lia. }
      destruct (Hnewpt x F1 F2 F3 F4 F6) as (N1 & N2 & N3).
      assert (Hns : in_shadow x = false).
      { unfold in_shadow, SH_LO, SH_HI. apply andb_false_iff. right. apply Z.ltb_ge. unfold CHB in Hx. clear - Hx G Hcr K0 Hszp. lia. }
      assert (Hcov : covered (vm_maps (m_vmmaps model')) x = true).
      { apply (pri_covered LIMIT model0 hyb E' _ M ms' model' a mem0 HD3 HA0' Hne x); [unfold pri_foot; rewrite Epz'; exact F1 | exact Hns |].
        unfold CHB in Hx. clear - Hx G Hcr K0 Hszp. lia. }
      split; [exact N1|]. split; [exact N2|]. split.
      - rewrite N3. destruct HPo as [Pm _ _]. apply Pm. unfold RBX. unfold CHB in Hx. clear - Hx F5. lia.
      - split; [|exact (covered_below_top ASEGS LIMIT model0 hyb E' _ M ms' model' x HD3 Hcov)].
        split; [left; unfold covered in *; rewrite existsb_app; rewrite Hcov; apply orb_true_r|]. split; [exact Hns | exact F4]. }
    (* [comment removed for export] *)
    assert (Hspt : forall x, CHS <= x < CHS + sz_tbl c / 8 ->
              own_pt E' M x /\ outside E' l'' (Z_to_bv 64 x) /\ ms_mem ms' (Z_to_bv 64 x) = Some (Z_to_bv 8 250) /\
              in_shadow x = true /\ covered (vm_maps (m_vmmaps model')) x = true /\ 0 <= x < 2^47).
    { intros x Hx. destruct (chsh_fp pz mem0 HI c x Hcin Hjn Hx) as (F1 & F2 & F3 & F4 & F5).
      assert (F6 : ~ ncell (z_ca pz) (z_sb pz) c (262144 / sz_tbl c) x).
      { unfold ncell, foot_Co. unfold CHS in Hx. clear - Hx F5 S1 S2 G Hcr K0 Hsz8. lia. }
      destruct (Hnewpt x F1 F2 F3 F4 F6) as (N1 & N2 & N3).
      assert (Hzr : in_zr (sm_zr M) x = true).
      { apply (po_zr _ _ _ _ HP0). exists c. split; [exact Hcin|]. left. fold pz. unfold CHS in Hx. clear - Hx F5 K0 Hsz8. split; [|exact F5].
        assert (0 <= sz_tbl c / 8 * z_j pz c) by (apply Z.mul_nonneg_nonneg; lia). lia. }
      split; [exact N1|]. split; [exact N2|]. split.
      - rewrite N3. destruct HPo as [_ Ps _]. apply Ps. unfold SHX. unfold CHS in Hx. clear - Hx F5. lia.
      - split; [exact (dn_zrsh _ _ _ _ _ _ _ _ _ HD3 x Hzr)|]. split; [exact (dn_zrm _ _ _ _ _ _ _ _ _ HD3 x Hzr) | exact F4]. }
    set (Y := with_rgs X l'') in *.
    set (R2 := RG (chsh_lin a c) (lconst (sz_tbl c / 8)) RW (fa_cont (Z.to_nat (sz_tbl c / 8)) TEmpty)).
    set (R1 := RG (chunk_lin a c) (lconst (sz_tbl c)) RZ TEmpty).
    assert (HnY : (s_next Lb <= s_next Y)%positive) by (cbn [Y with_rgs X with_reg mrg Lh hand_post s_next]; lia).
    assert (Er2 : rsz E' R2 = sz_tbl c / 8) by (unfold rsz, R2; cbn [rg_size]; fold (uE E' (lconst (sz_tbl c / 8))); apply uE_lc; clear - Hsz8; lia).
    assert (Er1 : rsz E' R1 = sz_tbl c) by (unfold rsz, R1; cbn [rg_size]; fold (uE E' (lconst (sz_tbl c))); apply uE_lc; clear - Hszp; lia).
    assert (E8 : 8 * (CHS - SH_OFF) = CHB).
    { unfold CHS, CHB, SH_OFF. destruct G as (_ & _ & _ & _ & _ & Gm8 & Gsh & _).
      pose proof (Z.div_mod (z_sb pz) 8 ltac:(lia)) as Ed. rewrite Gm8, Z.add_0_r in Ed. rewrite Gsh. clear - Ed Hs8. lia. }
    assert (HD6 : DEN ASEGS LIMIT model0 hyb E' (addo_post Y R2) M ms' model').
    { apply (den_add_own ASEGS LIMIT model0 hyb E' Y M ms' model' R2 HD5).
      - exact (lwf_mono' _ _ _ HnY (proj2 HwLc)).
      - apply lwf_lconst.
      - reflexivity.
      - intros p v Hp. unfold R2 in Hp. cbn [rg_cont] in Hp. destruct (fa_cont_get _ _ _ _ Hp) as [[-> _]|Hp']; [exists 250; reflexivity | rewrite tget_empty in Hp'; discriminate].
      - rewrite Er2. clear - Hsz8. lia.
      - rewrite Er2. change (rg_base R2) with (chsh_lin a c). rewrite Echs'.
        destruct (Hspt (CHS + sz_tbl c / 8 - 1) ltac:(clear - Hsz8; lia)) as (_ & _ & _ & _ & _ & N6). clear - N6. lia.
      - intros x Hx. rewrite Er2 in Hx. change (rg_base R2) with (chsh_lin a c) in Hx. rewrite Echs' in Hx.
        destruct (Hspt x Hx) as (N1 & _ & N3 & _ & N5 & _). split; [exact N1|]. split; [rewrite N3; discriminate|].
        exact (covered_below_top ASEGS LIMIT model0 hyb E' _ M ms' model' x HD3 N5).
      - intros p b Hp. unfold R2 in Hp. cbn [rg_cont] in Hp. rewrite Er2. change (rg_base R2) with (chsh_lin a c). rewrite Echs'.
        destruct (fa_cont_get _ _ _ _ Hp) as [[Hb Hlt]|Hp']; [|rewrite tget_empty in Hp'; discriminate]. injection Hb as ->.
        rewrite Z2Nat.id in Hlt by (clear - Hsz8; lia). split; [exact Hlt|].
        destruct (Hspt (CHS + (Z.pos p - 1)) ltac:(clear - Hlt; lia)) as (_ & _ & N3 & _). exact N3.
      - intros R' HR' w Hw Hc0. rewrite Er2 in Hc0. change (rg_base R2) with (chsh_lin a c) in Hc0. rewrite Echs' in Hc0.
        destruct (Hspt w Hc0) as (_ & N2 & _ & _ & _ & N6). unfold outside in N2. rewrite Forall_forall in N2. specialize (N2 R' HR').
        rewrite u_small64 in N2 by (clear - N6; unfold two64; lia). unfold uE in Hw. clear - N2 Hw. lia.
      - unfold rl_ok. cbv zeta. rewrite Er2. change (rg_base R2) with (chsh_lin a c). rewrite Echs'. split; [clear - Hsz8; lia|]. right.
        split; [unfold SH_OFF, CHS; clear - S1 K0 Hcr Hsz8; lia|]. split.
        + intros x Hx. apply (Hcpt x). rewrite <- E8. clear - Hx Hs8. lia.
        + intros w Hw. destruct (Hspt w Hw) as (_ & _ & _ & N4 & N5 & _). split; [exact N4 | exact N5]. }
    assert (HD7 : DEN ASEGS LIMIT model0 hyb E' (addo_post (addo_post Y R2) R1) M ms' model').
    { apply (den_add_own_z ASEGS LIMIT model0 hyb E' (addo_post Y R2) M ms' model' R1 HD6).
      - exact (lwf_mono' _ _ _ HnY (proj1 HwLc)).
      - apply lwf_lconst.
      - reflexivity.
      - reflexivity.
      - rewrite Er1. clear - Hszp. lia.
      - rewrite Er1. change (rg_base R1) with (chunk_lin a c). rewrite Echk'.
        destruct (chunk_fp pz mem0 HI c (CHB + sz_tbl c - 1) Hcin Z1 Hjn ltac:(unfold CHB; clear - Hszp; lia)) as (_ & _ & _ & F4 & _). clear - F4. lia.
      - intros x Hx. rewrite Er1 in Hx. change (rg_base R1) with (chunk_lin a c) in Hx. rewrite Echk' in Hx.
        destruct (Hcpt x Hx) as (N1 & _ & N3 & _ & N5). split; [exact N1|]. split; [exact N3 | exact N5].
      - intros R' HR' w Hw Hc0. rewrite Er1 in Hc0. change (rg_base R1) with (chunk_lin a c) in Hc0. rewrite Echk' in Hc0.
        cbn [addo_post s_rgs] in HR'. destruct HR' as [<-|HR'].
        + (* [comment removed for export] *)
          rewrite Er2 in Hw. change (rg_base R2) with (chsh_lin a c) in Hw. rewrite Echs' in Hw.
          destruct (Hspt w Hw) as (_ & _ & _ & N4 & _). destruct (Hcpt w Hc0) as (_ & _ & _ & Happ & _). unfold app_pt in Happ. destruct Happ as (_ & N4' & _). congruence.
        + destruct (Hcpt w Hc0) as (_ & N2 & _ & Happ & _). unfold app_pt in Happ. destruct Happ as (_ & _ & N6). unfold outside in N2. rewrite Forall_forall in N2. specialize (N2 R' HR').
          rewrite u_small64 in N2 by (clear - N6; unfold two64; lia). unfold uE in Hw. clear - N2 Hw. lia.
      - unfold rl_ok. cbv zeta. rewrite Er1. change (rg_base R1) with (chunk_lin a c). rewrite Echk'. split; [clear - Hszp; lia|]. left.
        intros w Hw. destruct (Hcpt w Hw) as (_ & _ & _ & N4 & _). exact N4. }
    (* [comment removed for export] *)
    assert (Hhyb_in : forall x, 0 <= x < 2^64 -> ncell (z_ca pz) (z_sb pz) c (262144 / sz_tbl c) x -> hyb (wa x) = ms_mem ms' (wa x)).
    { intros x Hx Hn. unfold hyb, hyb_p. rewrite u_wa_small by exact Hx. rewrite (proj2 (ncell_b_spec _ _ _ _ _) Hn). reflexivity. }
    assert (Hhyb_out : forall x, 0 <= x < 2^64 -> ~ ncell (z_ca pz) (z_sb pz) c (262144 / sz_tbl c) x -> hyb (wa x) = mem0 (wa x)).
    { intros x Hx Hn. unfold hyb, hyb_p. rewrite u_wa_small by exact Hx.
      destruct (ncell_b (z_ca pz) (z_sb pz) c (262144 / sz_tbl c) x) eqn:Eb; [exfalso; apply Hn; apply ncell_b_spec; exact Eb | reflexivity]. }
    assert (B0 : 0 <= z_ca pz /\ z_ca pz + 4096 <= 2^63 /\ 0 <= z_sb pz /\ z_sb pz + 137438953472 + 4096 <= 2^63) by (clear - G; lia).
    assert (HIo' : INV_Co hyb (z_ca pz) (z_sb pz) c (sz_tbl c) (mc_tbl c / 2) (262144 / sz_tbl c) (z_j pz c + 1)).
    { apply (INV_Co_frame (ms_mem ms')); [clear - B0; lia | clear - B0; lia | clear - B0; lia | clear - B0; lia | | exact (INV_G_o _ _ _ _ _ _ _ _ HI3)].
      intros x Hf. apply Hhyb_in; [unfold foot_Co in Hf; clear - Hf B0 Hcr Hnw; lia | left; exact Hf]. }
    assert (HST' : STATS hyb (z_ca pz)).
    { apply (STATS_frame (ms_mem ms')); [clear - B0; lia | clear - B0; lia | | exact HST3].
      intros x Hx. apply Hhyb_in; [clear - Hx B0; lia | right; exact Hx]. }
    assert (HPo' : POP_C hyb (z_sb pz) (z_sh pz) c (sz_tbl c) (z_j pz c + 1)).
    { assert (Hsz0 : 0 <= sz_tbl c) by (clear - Hszp; lia).
      apply (POP_C_frame mem0); [| clear - K0 Hsz8; nia | exact (POP_C_step mem0 (z_sb pz) (z_sh pz) c (sz_tbl c) (z_j pz c) Hsz0 K0 HPo)].
      intros x Hx. unfold RBX, SHX in Hx. apply Hhyb_out.
      - destruct Hx as [Hx|Hx]; [clear - Hx B0 Hcr K0 Hszp; nia | clear - Hx S1 G Hcr K0 Hsz8; nia].
      - unfold ncell, foot_Co. destruct Hx as [Hx|Hx].
        + assert (0 <= sz_tbl c * (z_j pz c + 1)) by (clear - K0 Hszp; nia). clear - Hx H T1 G Hcr. lia.
        + assert (0 <= sz_tbl c / 8 * (z_j pz c + 1)) by (clear - K0 Hsz8; nia). clear - Hx H S1 S2 G Hcr. lia. }
    assert (HIz' : INV_Az (pz_step pz c) hyb).
    { apply (INV_Az_step pz mem0 hyb c HI Hdisj Hcin ltac:(clear - Hjhi; lia) HIo' HPo' HST').
      intros x Hf Hno. destruct (ncell_b (z_ca pz) (z_sb pz) c (262144 / sz_tbl c) x) eqn:Eb.
      - apply ncell_b_spec in Eb. assert (Hx : 0 <= x < 2^64) by (pose proof (pri_foot_rng E a mem0 HI x Hf); lia).
        rewrite (Hhyb_in x Hx Eb). destruct (HCELL x Hx Eb) as (Q1 & Q2 & _).
        apply (Hkeep0 x ltac:(unfold two64; lia) Q1 Q2 Hno).
      - assert (Hx : 0 <= x < 2^64) by (pose proof (pri_foot_rng E a mem0 HI x Hf); lia).
        apply (Hhyb_out x Hx). intros Hn. apply ncell_b_spec in Hn. congruence. }
    set (a' := a_step a c) in *.
    assert (Epz2 : pden E' a' = pz_step pz c).
    { unfold a'. rewrite (a_step_eq a c). rewrite (pden_step E' a c) by (rewrite Epz'; clear - K0 Hjhi Hnw Hmc; unfold two64; lia). rewrite Epz'. reflexivity. }
    assert (Hne' : pri_step a c <> []).
    { intros Hn. pose proof (f_equal (@List.length lin) Hn) as XL. unfold pri_step in XL. rewrite !set_nth_length, Hlen in XL. discriminate. }
    assert (Hbase : forall k, (k < 5)%nat -> nth k (pri_step a c) lc0 = nth k (a_pri a) lc0).
    { intros k Hk5. pose proof (cidx_rng c Hcr) as Hci. unfold pri_step.
      rewrite nth_set_nth by (rewrite set_nth_length, Hlen; unfold PRI_LEN; lia).
      replace (Nat.eqb k (6 + 2 * cidx c)) with false by (symmetry; apply Nat.eqb_neq; lia).
      rewrite nth_set_nth by (rewrite Hlen; unfold PRI_LEN; lia).
      replace (Nat.eqb k (5 + 2 * cidx c)) with false by (symmetry; apply Nat.eqb_neq; lia). reflexivity. }
    assert (Hmono : forall x, pri_foot_z (pden E a) x -> pri_foot_z (pden E' (a_with a (pri_step a c))) x).
    { pose proof (iz_len _ _ HI) as Hlenz. intros x Hf. change (a_with a (pri_step a c)) with a'. rewrite Epz2. fold pz in Hf. unfold pri_foot_z in *.
      rewrite (step_ca pz c Hlenz Hcr), (step_sb pz c Hlenz Hcr), (step_sh pz c Hlenz Hcr).
      destruct Hf as [Hf|[Hf|[Hf|(c' & Hc' & Hf)]]]; [left; exact Hf | right; left; exact Hf | right; right; left; exact Hf |]. right. right. right. exists c'. split; [exact Hc'|].
      destruct (Z.eq_dec c' c) as [->|Hnc]; [rewrite (step_z_same pz c Hlenz Hcr); rewrite Z1 in Hf; exact Hf|].
      rewrite (step_z_other pz c Hlenz Hcr c' (in_cls_rng c' Hc') Hnc). exact Hf. }
    assert (Hdepf : forall x, 0 <= x < 2^64 -> downed (dD1 E a) (dB1 E a) x -> hyb (wa x) = mem0 (wa x)).
    { intros x Hx Hdw. apply (Hhyb_out x Hx). intros Hn. destruct (ncell_fp pz mem0 HI Hdisj c x Hcin Z1 Hn) as (F1 & _).
      exact (pri_not_downed LIMIT model0 mem0 E S M ms model a mem0 Hd HA0 Hne x F1 Hdw). }
    assert (Hjmono : forall c', In c' CLS -> z_j (pden E a) c' <= z_j (pden E' (a_with a (pri_step a c))) c').
    { pose proof (iz_len _ _ HI) as Hlenz. intros c' Hc'. change (a_with a (pri_step a c)) with a'. rewrite Epz2. fold pz.
      destruct (Z.eq_dec c' c) as [->|Hnc]; [rewrite (step_j_same pz c Hlenz Hcr); lia|].
      rewrite (step_j_other pz c Hlenz Hcr c' (in_cls_rng c' Hc') Hnc). lia. }
    assert (Hext_step : forall b z, ext_sem (pden E a) b z -> ext_sem (pden E' (a_with a (pri_step a c))) b z).
    { pose proof (iz_len _ _ HI) as Hlenz. intros b z Hbz. apply (ext_sem_mono (pden E a)); [| exact Hjmono | | | | | exact Hbz];
        change (a_with a (pri_step a c)) with a'; rewrite Epz2; fold pz.
      - exact (step_sb pz c Hlenz Hcr). - exact (step_qn pz c Hlenz Hcr). - exact (step_qj pz c Hlenz Hcr).
      - exact (step_gn pz c Hlenz Hcr). - exact (step_gl pz c Hlenz Hcr). }
    (* [comment removed for export] *)
    assert (Hext_fr : forall b z, ext_sem (pden E a) b z -> forall x, b <= x < b + z -> hyb (wa x) = mem0 (wa x)).
    { intros b z Hbz x Hxr. destruct (ext_sem_pt pz mem0 HI b z x Hbz Hxr) as (Rx & Hap & _ & HnQ & HnG).
      apply (Hhyb_out x ltac:(clear - Rx; lia)). intros Hn.
      exact (proj1 (proj2 (proj2 (ncell_fp pz mem0 HI Hdisj c x Hcin Z1 Hn))) Hap). }
    pose proof (HA_pri_step (s_next Lb) E E' M a mem0 hyb (pri_step a c) HA0 HawLb Ha' Hne Hne' Hown_eq
                  ltac:(change (a_with a (pri_step a c)) with a'; rewrite Epz2; exact HIz') Hbase Hmono Hdepf Hext_step Hext_fr) as HA'.
    pose proof (own_pt_with (s_next Lb) E E' M a mem0 hyb (pri_step a c) HA0 HawLb Ha' Hne Hown_eq
                  ltac:(change (a_with a (pri_step a c)) with a'; rewrite Epz2; exact HIz') Hbase Hmono) as Hsub.
    change (a_with a (pri_step a c)) with a' in HA', Hsub.
    (* [comment removed for export] *)
    set (Z := addo_post (addo_post Y R2) R1) in *.
    assert (HD8 : DEN ASEGS LIMIT model0 hyb E' Z (with_own M (a_own a')) ms' model').
    { apply (den_own_set ASEGS LIMIT model0 hyb hyb E' Z M ms' model' (a_own a') HD7).
      - apply forallb_forall. intros p Hp. rewrite forallb_forall in Cwo. specialize (Cwo p Hp). apply andb_prop in Cwo as [W1' W2'].
        apply andb_true_intro. split; apply (lwf_mono' (s_next S)); first [assumption | cbn [Z addo_post Y with_rgs X with_reg mrg Lh hand_post Lb np_front s_next]; lia].
      - intros w _. reflexivity.
      - intros w Hw. apply Hsub. exact (proj1 (own_pt_agree (s_next Lb) E E' M w HwfM Ha') Hw).
      - intros w (q & Hq & Hqw). cbn [with_own sm_own] in Hq.
        assert (Hw0 : own_pt E M w).
        { rewrite (ha_aown _ _ _ _ HA') in Hq. unfold aown_of in Hq. apply in_app_or in Hq as [Hq|Hq].
          * (* [comment removed for export] *)
            exists q. split.
            + rewrite Hown_eq, (ha_aown _ _ _ _ HA0). unfold aown_of. apply in_or_app. left. exact Hq.
            + assert (Hpw : pwf (s_next Lb) q = true).
              { pose proof HawLb as XW. unfold awf in XW. apply andb_prop in XW as [XW _]. apply andb_prop in XW as [XW _]. apply andb_prop in XW as [XW _]. apply andb_prop in XW as [_ XW].
                rewrite forallb_forall in XW. apply XW. rewrite (ha_aown _ _ _ _ HA0). unfold aown_of. apply in_or_app. left. exact Hq. }
              unfold pwf in Hpw. apply andb_prop in Hpw as [Hp1 Hp2]. rewrite <- (uE_agree _ E E' _ Hp1 Ha'), <- (uE_agree _ E E' _ Hp2 Ha'). exact Hqw.
          * assert (Hq' : In q (pri_own a')) by (unfold a' at 1 in Hq; cbn [a_step with_pri a_pri] in Hq; destruct (pri_step a c); [destruct Hq | exact Hq]).
            pose proof (pri_own_foot E' a' hyb ltac:(unfold INV_A; rewrite Epz2; exact HIz') q Hq' w Hqw) as Hf.
            unfold pri_foot in Hf. rewrite Epz2 in Hf. pose proof (iz_len _ _ HI) as Hlenz.
            assert (Hf0 : pri_foot_z pz w).
            { unfold pri_foot_z in *. rewrite (step_ca pz c Hlenz Hcr), (step_sb pz c Hlenz Hcr), (step_sh pz c Hlenz Hcr) in Hf.
              destruct Hf as [Hf|[Hf|[Hf|(c' & Hc' & Hf)]]]; [left; exact Hf | right; left; exact Hf | right; right; left; exact Hf |]. right. right. right. exists c'. split; [exact Hc'|].
              destruct (Z.eq_dec c' c) as [->|Hnc]; [rewrite (step_z_same pz c Hlenz Hcr) in Hf; rewrite Z1; exact Hf|].
              rewrite (step_z_other pz c Hlenz Hcr c' (in_cls_rng c' Hc') Hnc) in Hf. exact Hf. }
            apply (po_own _ _ _ _ HP0 w); [pose proof (pri_foot_rng E a mem0 HI w Hf0); lia | exact Hf0]. }
        pose proof (proj2 (own_pt_agree (s_next Lb) E E' M w HwfM Ha') Hw0) as (q0 & Hq0 & Hq0w).
        exact (dn_own _ _ _ _ _ _ _ _ _ HD7 q0 Hq0 w Hq0w). }
    apply (Hk E' hyb ms' model').
    + apply (agree_mono _ (s_next Lb)); [cbn [Lb np_front s_next]; lia | exact Ha'].
    + intros q Hq w Hw. apply Hfrzn. exists q. split; [exact Hq | exact Hw].
    + exact HD8.
    + intros _. exact HA'.
Qed.
End NPopNode.
(* [comment removed for export] *)
