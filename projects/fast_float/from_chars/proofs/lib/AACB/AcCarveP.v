(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec ShapeSet RealizesCfg AsanAcct PlacementCount AllocNodesCfg.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxLin FxCore FxSound FxMem FxFacts FxStep.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxLoop.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxSubst FxEnt FxPlan FxFrame FxDrv FxCall.
Import OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxLin OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxCore OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxSound OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxMem OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxFacts OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxStep OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxLoop.FxExplore OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxSubst OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxEnt OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxPlan OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxFrame OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxDrv OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxCall.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXC Require Import FxBacking FxChDen.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXC Require FxChDen.
From OSSVerify.Proofs.fast_float.from_chars.lib.AACB Require AcCarve AcSteps AcEntry AcMALp.
Import OSSVerify.Proofs.fast_float.from_chars.lib.FXC.FxChDen.AcMrg OSSVerify.Proofs.fast_float.from_chars.lib.AACB.AcCarve OSSVerify.Proofs.fast_float.from_chars.lib.AACB.AcSteps OSSVerify.Proofs.fast_float.from_chars.lib.AACB.AcEntry OSSVerify.Proofs.fast_float.from_chars.lib.AACB.AcMALp.
Import ListNotations.

Module AcStepsOut.
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec FxLin FxCore FxSound FxMem FxFacts FxStep FxSubst FxEnt FxDrv.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXC Require Import FxBacking FxChDen FxChFix.
From OSSVerify.Proofs.fast_float.from_chars.lib.AACB Require Import AcCarve AcSteps AcEntry.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.

Lemma mergeCC_outside : forall E n fs l i l' x, Forall (fact_ok E) fs -> step_rgs n fs l (RMergeCC i) = Some l' ->
  outside E l x -> outside E l' x.
Proof.
  intros E n fs l i l' x HF H Hout. cbn [step_rgs] in H.
  destruct (nth_error l i) as [R1|] eqn:H1; [|discriminate]. destruct (nth_error l (Datatypes.S i)) as [R2|] eqn:H2; [|discriminate].
  destruct (is_const (rg_size R1)) as [z1|] eqn:Z1; [|discriminate]. destruct (is_const (rg_size R2)) as [z2|] eqn:Z2; [|discriminate].
  destruct (lin_off (rg_base R2) (rg_base R1)) as [d|] eqn:Hd; [|discriminate]. cbv zeta in H.
  match type of H with (if ?b then _ else _) = _ => destruct b eqn:Hb; [|discriminate] end. injection H as <-.
  repeat match goal with H : (_ && _)%bool = true |- _ => apply andb_prop in H as [H ?] end.
  match goal with H : Z.eqb d z1 = true |- _ => apply Z.eqb_eq in H; subst d end.
  repeat match goal with H : Z.ltb _ _ = true |- _ => apply Z.ltb_lt in H end.
  pose proof (irange_sound E fs (rg_base R1) HF) as Rb.
  assert (E1 : rsz E R1 = z1) by (unfold rsz; exact (is_const_u E _ _ Z1)).
  assert (E2 : rsz E R2 = z2) by (unfold rsz; exact (is_const_u E _ _ Z2)).
  pose proof (bv_unsigned_in_range _ (lden E (rg_base R1))) as Rb0.
  assert (Hnw : bv_unsigned (lden E (rg_base R1)) + z1 < two64) by (clear - Rb H3 H6; lia).
  pose proof (lin_off_u E _ _ z1 Hd Hnw) as Eb.
  assert (Hz12 : 0 <= z1 + z2 < two64) by (clear - Rb Rb0 H3 H6 H7; lia).
  rewrite (nth_split2 l i R1 R2 H1 H2) in Hout. unfold outside in *. rewrite Forall_app in Hout. destruct Hout as [O1 O2].
  apply Forall_cons_iff in O2 as [OA O3]. apply Forall_cons_iff in O3 as [OB O4].
  apply Forall_app. split; [exact O1|]. constructor; [|exact O4].
  cbn [rg_base]. unfold rsz in *. cbn [rg_size]. rewrite lden_lconst, u_small64 by exact Hz12. rewrite E1 in OA. rewrite E2, Eb in OB. clear - OA OB. lia.
Qed.
Lemma mergeCCs_outside : forall E n fs k i l l' x, Forall (fact_ok E) fs -> steps_rgs n fs l (List.repeat (RMergeCC i) k) = Some l' ->
  outside E l x -> outside E l' x.
Proof.
  intros E n fs k i. induction k as [|k IH]; intros l l' x HF H Hout; cbn [List.repeat] in H; [rewrite steps_rgs_nil in H | rewrite steps_rgs_cons in H]; [injection H as <-; exact Hout|].
  destruct (step_rgs n fs l (RMergeCC i)) as [l1|] eqn:H1; [|discriminate].
  exact (IH l1 l' x HF H (mergeCC_outside E n fs l i l1 x HF H1 Hout)).
Qed.
(* [comment removed for export] *)
Lemma uncarve_outside : forall E X ixb k i l' x, Forall (fact_ok E) (s_facts X) -> perm_ix_ok (length (s_rgs X)) ixb = true ->
  steps_rgs (s_next X) (s_facts X) (List.map (fun t => nth t (s_rgs X) (RG lc0 lc0 RW TEmpty)) ixb) (List.repeat (RMergeCC i) k) = Some l' ->
  outside E (s_rgs X) x -> outside E l' x.
Proof.
  intros E X ixb k i l' x HF Hp Hs Hout.
  pose proof (perm_ix_sound (s_rgs X) (RG lc0 lc0 RW TEmpty) _ Hp) as HP.
  exact (mergeCCs_outside E _ _ k i _ l' x HF Hs (outside_perm E _ _ x HP Hout)).
Qed.
(* [comment removed for export] *)
End AcStepsOut.

Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
Fixpoint cut_steps (i : nat) (b : lin) (c : tree bval) (z off : Z) (cuts : list Z) : list rstep :=
  match cuts with
  | [] => []
  | o :: cuts' => let d := o - off in
                  let c2 := sub_cont c d (z - d) in      (* [comment removed for export] *)
                  RSplit i (RG b (lconst d) RW (sub_cont c 0 d)) (RG (laddc b d) (lconst (z - d)) RW c2) d ::
                  cut_steps (Datatypes.S i) (laddc b d) c2 (z - d) o cuts'
  end.
Fixpoint posn2 (s : nat) (ix : list nat) : nat := match ix with [] => O | x :: ix' => if Nat.eqb x s then O else Datatypes.S (posn2 s ix') end.

Record carve : Type := CV { cv_steps : list rstep ; cv_split : list region ; cv_ix : list nat }.
Definition carve_of (S : sst) (stk : nat) (cuts : list Z) (front : list nat) : option carve :=
  match nth_error (s_rgs S) stk with
  | Some (RG b z RW c) =>
      match is_const z with
      | Some zz =>
          let sts := cut_steps stk b c zz 0 cuts in
          match steps_rgs (s_next S) (s_facts S) (s_rgs S) sts with
          | Some l => Some (CV sts l (front ++ List.filter (fun k => negb (existsb (Nat.eqb k) front)) (seq 0 (length l))))
          | None => None
          end
      | None => None
      end
  | _ => None
  end.
Definition carve_rgs (cv : carve) : list region := List.map (fun k => nth k (cv_split cv) (RG lc0 lc0 RW TEmpty)) (cv_ix cv).

Section CarveP.
Variable segs : list Segment.
Variable LIMIT : Z.
Variable model0 : Model.
Variable mem0 : word -> option byte.

(* [comment removed for export] *)
#[using="Type"] Lemma den_carve : forall E S M ms model stk cuts front cv,
  DEN segs LIMIT model0 mem0 E S M ms model -> carve_of S stk cuts front = Some cv ->
  perm_ix_ok (length (cv_split cv)) (cv_ix cv) = true ->
  DEN segs LIMIT model0 mem0 E (with_rgs S (carve_rgs cv)) M ms model.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros E S M ms model stk cuts front cv Hd Hc Hp. unfold carve_of in Hc.
  destruct (nth_error (s_rgs S) stk) as [[b z k c]|]; [|discriminate]. destruct k; try discriminate.
  destruct (is_const z) as [zz|]; [|discriminate].
  destruct (steps_rgs (s_next S) (s_facts S) (s_rgs S) (cut_steps stk b c zz 0 cuts)) as [l|] eqn:Hl; [|discriminate].
  injection Hc as <-. cbn [cv_split cv_ix] in Hp.
  pose proof (den_steps segs LIMIT model0 mem0 _ E S M ms model l Hd Hl) as Hd1.
  pose proof (perm_ix_sound l (RG lc0 lc0 RW TEmpty) _ Hp) as HP.
  exact (den_perm segs LIMIT model0 mem0 E (with_rgs S l) M ms model _ Hd1 HP).
Qed.

(* [comment removed for export] *)
Definition inv_ix (ix : list nat) (len : nat) : list nat := List.map (fun s => posn2 s ix) (seq 0 len).
#[using="Type"] Lemma den_uncarve : forall E X M ms model ixb sts l',
  DEN segs LIMIT model0 mem0 E X M ms model ->
  perm_ix_ok (length (s_rgs X)) ixb = true ->
  steps_rgs (s_next X) (s_facts X) (List.map (fun t => nth t (s_rgs X) (RG lc0 lc0 RW TEmpty)) ixb) sts = Some l' ->
  DEN segs LIMIT model0 mem0 E (with_rgs X l') M ms model.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros E X M ms model ixb sts l' Hd Hp Hs.
  pose proof (perm_ix_sound (s_rgs X) (RG lc0 lc0 RW TEmpty) _ Hp) as HP.
  pose proof (den_perm segs LIMIT model0 mem0 E X M ms model _ Hd HP) as Hd1.
  exact (den_steps segs LIMIT model0 mem0 sts E _ M ms model l' Hd1 Hs).
Qed.
End CarveP.
(* [comment removed for export] *)
