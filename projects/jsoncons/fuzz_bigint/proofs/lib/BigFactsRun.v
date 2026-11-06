(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith List Bool Lia.
From OSSVerify.Proofs.jsoncons.fuzz_bigint.lib Require Import BigModel BigRun BigFactsBase BigFactsOps BigFactsDiv.
Import ListNotations.
Unset Lia Cache. Unset Nra Cache. Unset Nia Cache.
Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)

Fixpoint dec_acc (acc : Z) (cs : list Z) : Z :=
  match cs with [] => acc | c :: t => dec_acc (acc * 10 + (c - 48)) t end.
Definition dec (cs : list Z) : Z := dec_acc 0 cs.
Definition all_digits (cs : list Z) : bool := forallb is_digit cs.

Lemma dec_acc_bound acc cs : 0 <= acc -> all_digits cs = true ->
  acc * 10 ^ Z.of_nat (length cs) <= dec_acc acc cs < (acc + 1) * 10 ^ Z.of_nat (length cs).
Proof.
  revert acc; induction cs as [|c t IH]; intros acc Hacc Hd; simpl dec_acc; simpl length.
  - simpl. lia.
  - simpl in Hd. apply andb_prop in Hd. destruct Hd as [Hc Ht]. unfold is_digit in Hc. apply andb_prop in Hc. destruct Hc as [H1 H2].
    apply Z.leb_le in H1. apply Z.leb_le in H2.
    specialize (IH (acc * 10 + (c - 48)) ltac:(lia) Ht). rewrite Nat2Z.inj_succ, Z.pow_succ_r by lia.
    pose proof (Z.pow_pos_nonneg 10 (Z.of_nat (length t))). nia.
Qed.
Lemma dec_bound cs : all_digits cs = true -> 0 <= dec cs < 10 ^ Z.of_nat (length cs).
Proof. intros. unfold dec. pose proof (dec_acc_bound 0 cs ltac:(lia) H). lia. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

Section Parse.
  Variable N : nat.          (* [comment removed for export] *)
  Variable Wd : nat.         (* [comment removed for export] *)
  Variable L : nat.          (* [comment removed for export] *)
  Hypothesis HWd : 10 ^ Z.of_nat L < W.M ^ Z.of_nat Wd.
  Hypothesis HN : (Wd + 1 <= N)%nat.

  Lemma size_of_small v : okN N v -> reduced v -> 0 <= val (s_words v) < 10 ^ Z.of_nat L -> (size v <= Wd)%nat.
  Proof. intros Hv Hr Hval. unfold size. apply size_le_of_val; auto. apply (okN_words N); auto. lia. Qed.

  Lemma digit_loop_mspec : forall fuel cs v acc (done : nat),
    (length cs <= fuel)%nat -> (done + length cs = L)%nat ->
    okN N v -> reduced v -> s_neg v = false ->
    val (s_words v) = acc -> 0 <= acc < 10 ^ Z.of_nat done ->
    mspec (digit_loop fuel cs v)
      (fun r => match r with
                | Some v' => all_digits cs = true /\ okN N v' /\ reduced v' /\ s_neg v' = false /\
                             val (s_words v') = dec_acc acc cs /\ (size v' <= Wd)%nat /\ (capacity v <= capacity v')%nat
                | None => all_digits cs = false end)
      (2 * length cs) (BB N).
  Proof.
    induction fuel as [|f IH]; intros cs v acc done Hf Hdone Hv Hr Hneg Hval Hacc.
    - destruct cs; simpl in Hf; try lia. cbn [digit_loop]. apply mspec_ret. simpl in Hdone. splits; auto.
      apply size_of_small; auto. rewrite Hval. rewrite Nat.add_0_r in Hdone. subst done. lia.
    - destruct cs as [|c t].
      + cbn [digit_loop]. apply mspec_ret. simpl in Hdone. splits; auto.
        apply size_of_small; auto. rewrite Hval. rewrite Nat.add_0_r in Hdone. subst done. lia.
      + cbn [digit_loop length]. simpl in Hdone, Hf.
        assert (P10: 10 ^ Z.of_nat done * 10 <= 10 ^ Z.of_nat L).
        { rewrite Z.mul_comm, <- Z.pow_succ_r by lia. apply Z.pow_le_mono_r; lia. }
        assert (Sv: (size v <= Wd)%nat). { apply size_of_small; auto. rewrite Hval. pose proof (Z.pow_pos_nonneg 10 (Z.of_nat done)). lia. }
        destruct (is_digit c) eqn:Hc.
        * unfold is_digit in Hc. apply andb_prop in Hc. destruct Hc as [H1 H2]. apply Z.leb_le in H1. apply Z.leb_le in H2.
          eapply mspec_bind' with (K1 := 1%nat). apply mul_word_mspec; eauto. unfold wordZ; rewrite M_val; lia. lia. 2: lia.
          intros v1 (Hv1 & Rv1 & Vv1 & Sv1 & Nv1 & Cv1).
          assert (Sv1': (size v1 <= Wd)%nat). { apply size_of_small; auto. rewrite Vv1, Hval. lia. }
          eapply mspec_bind' with (K1 := 1%nat). apply add_word_mspec; eauto. unfold wordZ; rewrite M_val; lia. lia. 2: lia.
          intros v2 (Hv2 & Rv2 & Vv2 & Sv2 & Nv2 & Cv2).
          assert (NEG: s_neg v2 = false). { rewrite Nv2. destruct (size v2 =? 0)%nat; auto. rewrite Nv1. destruct (size v1 =? 0)%nat; auto. }
          assert (VAL: val (s_words v2) = acc * 10 + (c - 48)). { rewrite Vv2, Vv1, Hval. reflexivity. }
          assert (ACC: 0 <= acc * 10 + (c - 48) < 10 ^ Z.of_nat (S done)). { rewrite Nat2Z.inj_succ, Z.pow_succ_r by lia. lia. }
          pose proof (IH t v2 (acc * 10 + (c - 48)) (S done) ltac:(lia) ltac:(lia) Hv2 Rv2 NEG VAL ACC) as IH'.
          eapply mspec_weaken. exact IH'. 2: lia. 2: lia.
          intros r Hr'. destruct r as [v'|]; simpl; simpl in Hr'.
          2:{ rewrite Hr'. apply andb_false_r. }
          destruct Hr' as (A1 & A2 & A3 & A4 & A5 & A6 & A7).
          splits; auto. unfold is_digit. rewrite (proj2 (Z.leb_le _ _) H1), (proj2 (Z.leb_le _ _) H2). simpl. exact A1. lia.
        * eapply mspec_bind' with (K1 := 0%nat). apply destroy_mspec with (P := fun _ => True); auto. 2: lia.
          intros _ _. apply mspec_ret. simpl. rewrite Hc. reflexivity.
  Qed.
End Parse.

(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma skip_zeros_le fuel cs : (skip_zeros fuel cs <= length cs)%nat.
Proof. revert cs; induction fuel; intros [|c t]; simpl; try lia. destruct (c =? 48); simpl; try lia. specialize (IHfuel t). lia. Qed.
Lemma skip_zeros_all fuel cs : (length cs <= fuel)%nat -> skip_zeros fuel cs = length cs -> Forall (fun c => c = 48) cs.
Proof. revert cs; induction fuel; intros [|c t] Hf Hs; simpl in *; try lia; try constructor.
  destruct (Z.eqb_spec c 48). auto. simpl in Hs. lia. destruct (Z.eqb_spec c 48). apply IHfuel. lia. lia. simpl in Hs; lia. Qed.
Lemma dec_acc_zeros acc cs : Forall (fun c => c = 48) cs -> dec_acc acc cs = acc * 10 ^ Z.of_nat (length cs).
Proof. revert acc; induction cs as [|c t IH]; intros acc Hf. simpl. lia. inversion Hf; subst. cbn [dec_acc length]. rewrite IH by auto.
  rewrite Nat2Z.inj_succ, Z.pow_succ_r by lia. lia. Qed.

Lemma num_words_est_mono a b : (a <= b)%nat -> (num_words_est a <= num_words_est b)%nat.
Proof.
  intros. unfold num_words_est.
  assert (M1: Z.of_nat a * 3402 / 1024 <= Z.of_nat b * 3402 / 1024). { apply Z.div_le_mono. lia. lia. }
  assert (M2: (Z.of_nat a * 3402 / 1024 + 1 + 63) / 64 <= (Z.of_nat b * 3402 / 1024 + 1 + 63) / 64). { apply Z.div_le_mono. lia. lia. }
  assert (P1: 1 <= (Z.of_nat b * 3402 / 1024 + 1 + 63) / 64). { apply Z.div_le_lower_bound. lia. pose proof (Z.div_pos (Z.of_nat b * 3402) 1024). lia. }
  pose proof (Z.div_pos (Z.of_nat a * 3402) 1024). assert (0 <= (Z.of_nat a * 3402 / 1024 + 1 + 63) / 64) by (apply Z.div_pos; lia).
  destruct (Nat.ltb_spec a 10); destruct (Nat.ltb_spec b 10); try lia.
  all: apply Nat2Z.inj_le; rewrite ?Z2Nat.id; simpl; lia.
Qed.
Lemma num_words_est_4999 n : (n <= 4999)%nat -> (num_words_est n <= 260)%nat.
Proof. intros. apply Nat.le_trans with (num_words_est 4999). apply num_words_est_mono; auto. vm_compute. lia. Qed.
Lemma pow10_le_words n : (n <= 4999)%nat -> 10 ^ Z.of_nat n < W.M ^ Z.of_nat 260.
Proof. intros. apply Z.le_lt_trans with (10 ^ 4999). apply Z.pow_le_mono_r; lia. vm_compute. reflexivity. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

Definition parse_post N Wd (neg : bool) (cs : list Z) (r : parse_outcome) : Prop :=
  match r with
  | ParseOk v => okN N v /\ reduced v /\ (size v <= Wd)%nat /\ val (s_words v) = dec cs /\ all_digits cs = true
                 /\ ((0 < size v)%nat -> s_neg v = neg)
  | ParseErr => cs = [] \/ all_digits cs = false
  end.

Lemma to_bigint_detail_mspec N Wd cs neg value :
  okN N value -> (size value = 0)%nat ->
  10 ^ Z.of_nat (length cs) < W.M ^ Z.of_nat Wd -> (Wd + 1 <= N)%nat -> (num_words_est (length cs) <= N)%nat ->
  mspec (to_bigint_detail cs neg value) (parse_post N Wd neg cs) (2 * length cs + 2) (BB N).
Proof.
  intros Hv Sv HWd HN Hnw. unfold to_bigint_detail.
  destruct (Nat.eqb_spec (length cs) 0).
  { apply mspec_ret. simpl. left. apply length_zero_iff_nil; auto. }
  destruct (Nat.eqb_spec (skip_zeros (length cs) cs) (length cs)).
  { eapply mspec_bind' with (K1 := 1%nat). apply assign_mspec; eauto. apply okN_of_word. unfold wordZ; rewrite M_val; lia.
    rewrite size_of_word. simpl. lia. 2: lia.
    intros v1 (Hv1 & Wv1 & Sv1 & Nv1 & _). apply mspec_ret. simpl.
    pose proof (skip_zeros_all (length cs) cs ltac:(lia) e) as AZ.
    assert (AD: all_digits cs = true). { unfold all_digits. apply forallb_forall. intros x Hx. eapply Forall_forall in AZ; eauto. subst x. reflexivity. }
    rewrite size_of_word in Sv1. simpl in Sv1. unfold sto_of_word in Wv1. simpl in Wv1.
    splits; auto; try lia; try (intros; lia).
    all: try (unfold reduced; rewrite Wv1; left; reflexivity).
    all: rewrite Wv1; unfold dec; rewrite dec_acc_zeros; auto; cbn [val]; lia. }
  eapply mspec_bind' with (K1 := 1%nat). apply reserve_mspec. apply okN_empty. auto. 2: lia.
  intros v (Hvv & Wv & Nv & _ & _).
  eapply mspec_bind' with (K1 := (2 * length cs)%nat).
  { apply (digit_loop_mspec N Wd (length cs) HWd HN (length cs) cs v 0 0); auto; try lia.
    all: try (unfold reduced; rewrite Wv; left; auto). all: try (rewrite Wv; reflexivity). all: simpl; lia. }
  2: lia.
  intros r Hr. destruct r as [v1|]; simpl in Hr.
  - destruct Hr as (AD & Hv1 & Rv1 & Nv1 & Vv1 & Sv1 & _).
    set (v2 := if neg then set_neg v1 true else v1).
    assert (Hv2: okN N v2) by (destruct neg; [apply okN_set_neg|]; auto).
    assert (Wv2: s_words v2 = s_words v1) by (destruct neg; reflexivity).
    assert (Sv2: size v2 = size v1) by (destruct neg; reflexivity).
    eapply mspec_bind' with (K1 := 1%nat). apply assign_mspec; eauto. lia. 2: lia.
    intros value1 (Hval1 & Wval1 & Sval1 & Nval1 & _).
    eapply mspec_bind' with (K1 := 0%nat). apply destroy_mspec with (P := fun _ => True); auto. 2: lia. intros _ _.
    apply mspec_ret. simpl. splits; auto.
    + unfold reduced. rewrite Wval1, Wv2. exact Rv1.
    + lia.
    + rewrite Wval1, Wv2, Vv1. reflexivity.
    + intros Hs. rewrite Nval1, Sv2. destruct (Nat.ltb_spec 0 (size v1)). destruct neg; simpl; auto. lia.
  - eapply mspec_ret. simpl. auto.
Qed.

Lemma to_bigint_mspec N Wd cs value :
  okN N value -> (size value = 0)%nat ->
  10 ^ Z.of_nat (length cs) < W.M ^ Z.of_nat Wd -> (Wd + 1 <= N)%nat -> (num_words_est (length cs) <= N)%nat ->
  mspec (to_bigint cs value)
    (fun r => match r with
              | ParseOk v => okN N v /\ reduced v /\ (size v <= Wd)%nat
              | ParseErr => True end)
    (2 * length cs + 2) (BB N).
Proof.
  intros Hv Sv HWd HN Hnw. unfold to_bigint. destruct cs as [|c t]. apply mspec_ret; auto.
  assert (HWd': 10 ^ Z.of_nat (length t) < W.M ^ Z.of_nat Wd).
  { apply Z.le_lt_trans with (10 ^ Z.of_nat (length (c :: t))); auto. apply Z.pow_le_mono_r. lia. simpl length; lia. }
  assert (Hnw': (num_words_est (length t) <= N)%nat). { apply Nat.le_trans with (num_words_est (length (c :: t))); auto. apply num_words_est_mono. simpl; lia. }
  destruct (Z.eqb_spec c 45).
  - eapply mspec_weaken. apply (to_bigint_detail_mspec N Wd t true value); eauto.
    intros r Hr; destruct r; simpl in *; tauto. simpl length; lia. lia.
  - eapply mspec_weaken. apply (to_bigint_detail_mspec N Wd (c :: t) false value); eauto.
    intros r Hr; destruct r; simpl in *; tauto. lia. lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

Definition a_sto := Sto false false [1634696772344632213; 3071233077104388850] inlined_capacity 0.
Lemma parse_a s0 : fst (to_bigint lit_a sto_empty s0) = ParseOk a_sto.
Proof. vm_compute. reflexivity. Qed.
Lemma parse_a_state s0 :
  st_evs (snd (to_bigint lit_a sto_empty s0)) = EFree (st_next s0) 64 :: EAlloc (st_next s0) 64 SiteReserve :: st_evs s0
  /\ st_next (snd (to_bigint lit_a sto_empty s0)) = S (st_next s0).
Proof. vm_compute. split; reflexivity. Qed.
Lemma a_val : val (s_words a_sto) = 56654250564056135415631554531554513813.
Proof. reflexivity. Qed.
Lemma a_okN N : (1 <= N)%nat -> okN N a_sto.
Proof. intros. split. split. cbn [s_words a_sto]. constructor. unfold wordZ; rewrite M_val; lia. constructor. unfold wordZ; rewrite M_val; lia. constructor.
  unfold size, capacity, a_sto, inlined_capacity; simpl. split. lia. auto.
  unfold capacity, a_sto, inlined_capacity; simpl. rewrite round_up_eq. lia. Qed.
Lemma a_reduced : reduced a_sto. Proof. right. simpl. lia. Qed.
Lemma a_size : size a_sto = 2%nat. Proof. reflexivity. Qed.

Lemma parse_a_mspec B : 64 <= B -> mspec (to_bigint lit_a sto_empty) (fun r => r = ParseOk a_sto) 1 B.
Proof.
  intros HB s0. unfold post. rewrite parse_a. split; auto. destruct (parse_a_state s0) as [E1 E2]. rewrite E1, E2.
  exists [EAlloc (st_next s0) 64 SiteReserve; EFree (st_next s0) 64]. simpl. repeat split; auto; try lia.
  constructor. simpl. lia. constructor. simpl. auto. constructor.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

Definition NW : nat := 266.
Lemma BB_NW : BB NW = 2176. Proof. reflexivity. Qed.

Definition body_post (r : option exn * option sto * option sto * option sto) : Prop :=
  let '(ex, ob, oc, od) := r in
  match ob with Some b => okN NW b /\ reduced b /\ (size b <= 260)%nat | None => True end.

Ltac destroy_step := eapply mspec_bind' with (K1 := 0%nat); [apply destroy_mspec with (P := fun _ => True); auto | intros _ _ | lia].
Ltac emit_step L := eapply mspec_bind' with (K1 := 0%nat); [apply L with (P := fun _ => True); auto | intros _ _ | lia].

Theorem harness_body_mspec p : (length p < 5000)%nat ->
  mspec (harness_body p) body_post (2 * length p + 70) (BB NW).
Proof.
  intros Hp. unfold harness_body. destruct (Nat.ltb_spec (length p) 5000); try lia.
  eapply mspec_bind' with (K1 := 1%nat). apply parse_a_mspec. rewrite BB_NW; lia. 2: lia.
  intros ra ->.
  pose proof (a_okN NW ltac:(unfold NW; lia)) as Ha.
  eapply mspec_bind' with (K1 := (2 * length p + 2)%nat).
  { apply (to_bigint_mspec NW 260 p sto_empty). apply okN_empty. reflexivity. apply pow10_le_words; lia. unfold NW; lia.
    apply Nat.le_trans with 260%nat. apply num_words_est_4999; lia. unfold NW; lia. }
  2: lia.
  intros rb Hrb. destruct rb as [b|].
  2:{ emit_step mspec_emit_throw. destroy_step. emit_step mspec_emit_catch. apply mspec_ret. exact I. }
  destruct Hrb as (Hb & Rb & Sb).
  eapply mspec_bind' with (K1 := 1%nat). apply copy_mspec; eauto. 2: lia.
  intros x (Hx & Wx & _).
  assert (Sx: size x = 2%nat) by (unfold size; rewrite Wx; reflexivity).
  eapply mspec_bind' with (K1 := 29%nat). 1:{ apply (mod_assign_mspec NW 260); eauto; try lia; try (unfold NW; lia). } 2: lia.
  intros m1 Hm1. destruct m1 as [x1 | | xc]; simpl in Hm1.
  2:{ do 3 destroy_step. emit_step mspec_emit_catch. apply mspec_ret. simpl. auto. }
  2:{ do 3 destroy_step. emit_step mspec_emit_catch. apply mspec_ret. simpl. auto. }
  eapply mspec_bind' with (K1 := 1%nat). apply copy_mspec; eauto. 2: lia. intros c (Hc & _).
  destroy_step.
  eapply mspec_bind' with (K1 := 1%nat). apply copy_mspec; eauto. 2: lia. intros x2 (Hx2 & Wx2 & _).
  assert (Sx2: (size x2 <= 260)%nat) by (unfold size; rewrite Wx2; auto).
  eapply mspec_bind' with (K1 := 29%nat). 1:{ apply (mod_assign_mspec NW 260); eauto; try lia; try apply a_reduced; try (rewrite a_size; lia); try (unfold NW; lia). } 2: lia.
  intros m2 Hm2. destruct m2 as [x3 | | xc]; simpl in Hm2.
  2:{ do 4 destroy_step. emit_step mspec_emit_catch. apply mspec_ret. simpl. auto. }
  2:{ do 4 destroy_step. emit_step mspec_emit_catch. apply mspec_ret. simpl. auto. }
  eapply mspec_bind' with (K1 := 1%nat). apply copy_mspec; eauto. 2: lia. intros d (Hdd & _).
  do 5 destroy_step. apply mspec_ret. simpl. auto.
Qed.

Lemma lor7_le n : 0 <= n -> Z.lor n 7 + 1 <= n + 8.
Proof. intros. pose proof (Z.add_lor_land n 7). pose proof (Z.land_nonneg n 7). lia. Qed.
Lemma str_alloc_bytes_le n : 0 <= str_alloc_bytes n <= Z.of_nat n + 8.
Proof. unfold str_alloc_bytes. destruct (Nat.eqb_spec n 23). lia. pose proof (lor7_le (Z.of_nat n) ltac:(lia)). pose proof (Z.lor_nonneg (Z.of_nat n) 7). lia. Qed.

Theorem harness_mspec p : (length p < 5000)%nat ->
  mspec (harness p) body_post (2 * length p + 71) (Z.max (BB NW) (Z.of_nat (length p) + 8)).
Proof.
  intros Hp. unfold harness.
  eapply mspec_bind' with (K1 := 1%nat) (P := fun _ => True).
  { destruct (Nat.ltb_spec sso_max (length p)). 2: apply mspec_ret; auto.
    eapply mspec_bind' with (K1 := 1%nat). apply mspec_alloc. pose proof (str_alloc_bytes_le (length p)). lia. 2: lia. intros blk _. apply mspec_ret. auto. }
  2: lia.
  intros sb _. eapply mspec_bind' with (K1 := (2 * length p + 70)%nat).
  eapply mspec_weaken. apply harness_body_mspec; auto. intros a Ha; exact Ha. lia. apply Z.le_max_l. 2: lia.
  intros r Hr. destruct sb. eapply mspec_bind' with (K1 := 0%nat). apply mspec_emit_free with (P := fun _ => True); auto. 2: lia.
  intros _ _. apply mspec_ret; auto. apply mspec_ret; auto.
Qed.

Theorem run_payload_bounds p : (length p < 5000)%nat ->
  Forall (ev_ok (Z.max 2176 (Z.of_nat (length p) + 8))) (payload_events p)
  /\ (nallocs (payload_events p) <= 2 * length p + 71)%nat
  /\ (match o_b (run_payload p) with Some b => okN NW b /\ reduced b /\ (size b <= 260)%nat | None => True end).
Proof.
  intros Hp. pose proof (harness_mspec p Hp st_init) as H. unfold post in H. unfold payload_events, run_payload.
  destruct (harness p st_init) as [[[[ex ob] oc] od] s] eqn:E. simpl in H. destruct H as [Hpost (l & El & Fl & Nl & _)].
  simpl in El. rewrite app_nil_r in El. simpl. rewrite El, rev_involutive. rewrite BB_NW in Fl. repeat split; auto.
Qed.

(* [comment removed for export] *)
Theorem run_payload_large p : (5000 <= length p)%nat ->
  payload_events p = [EAlloc 0 (str_alloc_bytes (length p)) SiteString; EFree 0 (str_alloc_bytes (length p))].
Proof.
  intros Hp. unfold payload_events, run_payload, harness, harness_body.
  destruct (Nat.ltb_spec sso_max (length p)). 2: unfold sso_max in *; lia.
  destruct (Nat.ltb_spec (length p) 5000); try lia. reflexivity.
Qed.
