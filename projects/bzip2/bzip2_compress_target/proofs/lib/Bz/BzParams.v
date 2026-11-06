(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith Lia Bool.
From Stdlib Require Lia.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope Z_scope.

Class BzParams : Type := mkBzParams {
  p_bs : Z;
  p_wf : Z;
  p_bs_rng : 1 <= p_bs <= 9;
  p_wf_rng : 1 <= p_wf <= 250 }.
Arguments p_bs {BzParams} : simpl never.
Arguments p_wf {BzParams} : simpl never.

Abbreviation BLOCKSIZE100K := (p_bs).
Abbreviation WORKFACTOR := (p_wf).
Abbreviation NBLOCK_CAP := (p_bs * 100000)%Z.
Abbreviation NBLOCKMAX := (p_bs * 100000 + -19)%Z.
Abbreviation ARR1_SIZE := (p_bs * 400000)%Z.
Abbreviation ARR2_SIZE := (p_bs * 400000 + 136)%Z.

(* [comment removed for export] *)
Definition wf_clamp (wf : Z) : Z := if wf <? 1 then 1 else if 100 <? wf then 100 else wf.
Definition budget_q {BZP : BzParams} : Z := (wf_clamp p_wf - 1) / 3.
Arguments budget_q {BZP} : simpl never.

(* [comment removed for export] *)
Lemma fdP_bs_rng : 1 <= 9 <= 9. Proof. lia. Qed.
Lemma fdP_wf_rng : 1 <= 30 <= 250. Proof. lia. Qed.
Definition fdP : BzParams := mkBzParams 9 30 fdP_bs_rng fdP_wf_rng.
Lemma fdP_bs : @p_bs fdP = 9. Proof. reflexivity. Qed.
Lemma fdP_wf : @p_wf fdP = 30. Proof. reflexivity. Qed.
Lemma fdP_budget_q : @budget_q fdP = 9. Proof. reflexivity. Qed.

Section Facts. Context {BZP : BzParams}.
  Lemma wf_clamp_rng_of : forall wf, 1 <= wf_clamp wf <= 100.
  Proof. intros wf. unfold wf_clamp. destruct (Z.ltb_spec wf 1); [lia|]. destruct (Z.ltb_spec 100 wf); lia. Qed.
  Lemma wf_clamp_rng : 1 <= wf_clamp p_wf <= 100.
  Proof. apply wf_clamp_rng_of. Qed.
  Lemma wf_clamp_id : forall wf, 1 <= wf <= 100 -> wf_clamp wf = wf.
  Proof. intros wf H. unfold wf_clamp. destruct (Z.ltb_spec wf 1); [lia|]. destruct (Z.ltb_spec 100 wf); lia. Qed.
  Lemma wf_clamp_hi : forall wf, 100 <= wf -> wf_clamp wf = 100.
  Proof. intros wf H. unfold wf_clamp. destruct (Z.ltb_spec wf 1); [lia|]. destruct (Z.ltb_spec 100 wf); lia. Qed.
  (* [comment removed for export] *)
  Lemma wf_clamp_lt100 : p_wf < 100 -> wf_clamp p_wf = p_wf.
  Proof. intros H. pose proof p_wf_rng. apply wf_clamp_id. lia. Qed.
  Lemma wf_clamp_ge100 : 100 <= p_wf -> wf_clamp p_wf = 100.
  Proof. apply wf_clamp_hi. Qed.
  (* [comment removed for export] *)

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma budget_q_rng : 0 <= budget_q <= 33.
  Proof.
    unfold budget_q. pose proof wf_clamp_rng as W.
    split; [apply Z.div_pos; lia| apply Z.div_le_upper_bound; lia].
  Qed.
  Lemma budget0_rng : forall n, 0 <= n <= 900019 -> 0 <= n * budget_q <= 29700627.
  Proof. intros n Hn. pose proof budget_q_rng. nia. Qed.
  (* [comment removed for export] *)

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
End Facts.

(* [comment removed for export] *)
Ltac bzp_evars :=
  repeat match goal with
         | |- context [@p_bs ?i] => is_evar i; let inst := constr:(_ : BzParams) in unify i inst
         | |- context [@p_wf ?i] => is_evar i; let inst := constr:(_ : BzParams) in unify i inst
         | |- context [@budget_q ?i] => is_evar i; let inst := constr:(_ : BzParams) in unify i inst
         | H : context [@p_bs ?i] |- _ => is_evar i; let inst := constr:(_ : BzParams) in unify i inst
         | H : context [@p_wf ?i] |- _ => is_evar i; let inst := constr:(_ : BzParams) in unify i inst
         | H : context [@budget_q ?i] |- _ => is_evar i; let inst := constr:(_ : BzParams) in unify i inst
         end.

(* [comment removed for export] *)
Ltac bz_params :=
  try bzp_evars;
  try (lazymatch goal with
       | _ : (1 <= p_bs)%Z |- _ => fail
       | _ => let inst := constr:(_ : BzParams) in
              pose proof (proj1 (@p_bs_rng inst)) as BZbsL__; pose proof (proj2 (@p_bs_rng inst)) as BZbsH__;
              pose proof (proj1 (@p_wf_rng inst)) as BZwfL__; pose proof (proj2 (@p_wf_rng inst)) as BZwfH__;
              pose proof (proj1 (@budget_q_rng inst)) as BZbqL__; pose proof (proj2 (@budget_q_rng inst)) as BZbqH__;
              (* [comment removed for export] *)
              try (constr_eq inst fdP;
                   pose proof fdP_bs as BZfdbs__; pose proof fdP_wf as BZfdwf__; pose proof fdP_budget_q as BZfdbq__)
       end).

(* [comment removed for export] *)
Ltac bz_params_occ :=
  try bzp_evars;
  try (lazymatch goal with
       | _ : (1 <= p_bs)%Z |- _ => fail
       | |- context [p_bs] => bz_params
       | _ : context [p_bs] |- _ => bz_params
       | |- context [p_wf] => bz_params
       | _ : context [p_wf] |- _ => bz_params
       | |- context [@budget_q _] => bz_params
       | _ : context [@budget_q _] |- _ => bz_params
       end).

Section SelfTest. Context {BZP : BzParams}.
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
End SelfTest.
(* [comment removed for export] *)
Section SelfTestFd.
  #[local] Existing Instance fdP.
  (* [comment removed for export] *)
End SelfTestFd.
