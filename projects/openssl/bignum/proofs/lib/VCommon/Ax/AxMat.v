(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith Lia Bool List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase Fs RiscvSemantics MemImageType State Run.
Import ListNotations.

Local Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Lemma wvb_vmmaps (lz : list (word * word)) (pages : list word) (m : Model) : m_vmmaps (with_vm_backing lz pages m) = m_vmmaps m.
Proof. reflexivity. Qed.

Lemma wvb_lazy (lz : list (word * word)) (pages : list word) (m : Model) : m_vm_lazy (with_vm_backing lz pages m) = lz.
Proof. reflexivity. Qed.

Lemma wvb_mat (lz : list (word * word)) (pages : list word) (m : Model) : m_vm_materialized (with_vm_backing lz pages m) = pages.
Proof. reflexivity. Qed.

Lemma wvb_self (m : Model) : with_vm_backing (m_vm_lazy m) (m_vm_materialized m) m = m.
Proof. destruct m as [fd [maps lz mat] io fs proc lim tm]. reflexivity. Qed.

Lemma wvb_used (pages : list word) (m : Model) :
  vm_backing_used (with_vm_backing (m_vm_lazy m) pages m)
  = vm_backing_used m + (Z.of_nat (length pages) - Z.of_nat (length (m_vm_materialized m))) * 4096.
Proof. unfold vm_backing_used. rewrite wvb_vmmaps, wvb_lazy, wvb_mat. unfold page_size. lia. Qed.

Definition acc_pages (acc : list (word * nat)) : Z :=
  fold_right (fun p s => Z.of_nat (snd p) / 4096 + 2 + s) 0 acc.

Lemma acc_pages_nil : acc_pages [] = 0.
Proof. reflexivity. Qed.

Lemma acc_pages_cons (a : word) (n : nat) (acc : list (word * nat)) : acc_pages ((a, n) :: acc) = Z.of_nat n / 4096 + 2 + acc_pages acc.
Proof. reflexivity. Qed.

Lemma acc_pages_nonneg (acc : list (word * nat)) : 0 <= acc_pages acc.
Proof.
  induction acc as [|[a n] r IH]; [rewrite acc_pages_nil; lia|]. rewrite acc_pages_cons.
  pose proof (Z.div_pos (Z.of_nat n) 4096 ltac:(lia) ltac:(lia)). lia.
Qed.

Lemma acc_pages_one (a : word) (n : nat) : (n < 4096)%nat -> acc_pages [(a, n)] = 2.
Proof. intros H. rewrite acc_pages_cons, acc_pages_nil, Z.div_small by lia. lia. Qed.

Lemma acc_pages_two (a b : word) (n k : nat) : (n < 4096)%nat -> (k < 4096)%nat -> acc_pages [(a, n); (b, k)] = 4.
Proof. intros H1 H2. rewrite !acc_pages_cons, acc_pages_nil, !Z.div_small by lia. lia. Qed.

Definition missing (C pages : list word) : nat := length (List.filter (fun s => negb (page_mem s pages)) C).

Lemma page_mem_insert (p q : word) (pages : list word) : page_mem p (page_insert q pages) = bv_eqb p q || page_mem p pages.
Proof.
  unfold page_insert. destruct (page_mem q pages) eqn:E; [|reflexivity].
  destruct (bv_eqb p q) eqn:E2; [|reflexivity]. apply bv_eqb_eq in E2. subst q. rewrite E. reflexivity.
Qed.

Lemma missing_le (C pages : list word) : (missing C pages <= length C)%nat.
Proof. unfold missing. induction C as [|s r IH]; cbn [List.filter length]; [lia|]. destruct (negb (page_mem s pages)); cbn [length]; lia. Qed.

Lemma missing_insert_mono (C pages : list word) (q : word) : (missing C (page_insert q pages) <= missing C pages)%nat.
Proof.
  unfold missing. induction C as [|s r IH]; cbn [List.filter length]; [lia|].
  rewrite page_mem_insert. destruct (bv_eqb s q); cbn [orb negb]; destruct (page_mem s pages); cbn [negb length]; lia.
Qed.

Lemma insert_measure (C pages : list word) (q : word) :
  In q C -> (length (page_insert q pages) + missing C (page_insert q pages) <= length pages + missing C pages)%nat.
Proof.
  intros Hin. unfold page_insert at 1. destruct (page_mem q pages) eqn:E.
  - pose proof (missing_insert_mono C pages q). lia.
  - cbn [length]. assert (X : (1 + missing C (page_insert q pages) <= missing C pages)%nat); [|lia].
    unfold missing. induction C as [|s r IH]; [destruct Hin|]. cbn [List.filter]. rewrite page_mem_insert.
    destruct Hin as [->|Hin].
    + replace (bv_eqb q q) with true by (symmetry; apply bv_eqb_eq; reflexivity). rewrite E. cbn [orb negb length].
      pose proof (missing_insert_mono r pages q) as Y. unfold missing in Y. lia.
    + specialize (IH Hin). destruct (bv_eqb s q); cbn [orb negb]; destruct (page_mem s pages); cbn [negb length]; lia.
Qed.

Definition cand (base : Z) (n : nat) : list word :=
  map (fun j => page_base_of (base + 4096 * Z.of_nat j)) (seq 0 (Z.to_nat (Z.of_nat n / 4096 + 2))).

Lemma cand_length (base : Z) (n : nat) : Z.of_nat (length (cand base n)) = Z.of_nat n / 4096 + 2.
Proof.
  unfold cand. rewrite length_map, length_seq. pose proof (Z.div_pos (Z.of_nat n) 4096 ltac:(lia) ltac:(lia)). lia.
Qed.

Lemma cand_in (base : Z) (n : nat) (z : Z) : base <= z < base + Z.of_nat n -> In (page_base_of z) (cand base n).
Proof.
  intros Hz. unfold cand. apply in_map_iff. exists (Z.to_nat (z / 4096 - base / 4096)).
  pose proof (Z.div_le_mono base z 4096 ltac:(lia) ltac:(lia)) as Hq.
  assert (Hup : z / 4096 - base / 4096 <= Z.of_nat n / 4096 + 1).
  { pose proof (Z.div_mod base 4096 ltac:(lia)). pose proof (Z.mod_pos_bound base 4096 ltac:(lia)).
    pose proof (Z.div_mod (Z.of_nat n) 4096 ltac:(lia)). pose proof (Z.mod_pos_bound (Z.of_nat n) 4096 ltac:(lia)).
    assert (z / 4096 < base / 4096 + Z.of_nat n / 4096 + 2); [|lia].
    apply Z.div_lt_upper_bound; lia. }
  split.
  - unfold page_base_of, page_size. f_equal. rewrite Z2Nat.id by lia.
    replace (base + 4096 * (z / 4096 - base / 4096)) with (base + (z / 4096 - base / 4096) * 4096) by lia.
    rewrite Z.div_add by lia. lia.
  - apply in_seq. split; [lia|]. cbn [Nat.add]. apply Nat2Z.inj_lt. rewrite !Z2Nat.id by lia. lia.
Qed.

Lemma access_pages_measure (C : list word) : forall (n : nat) (base : Z) (pages : list word),
  (forall z, base <= z < base + Z.of_nat n -> In (page_base_of z) C) ->
  (length (access_pages_acc base n pages) + missing C (access_pages_acc base n pages) <= length pages + missing C pages)%nat.
Proof.
  induction n as [|k IH]; intros base pages HS; cbn [access_pages_acc]; [lia|].
  pose proof (insert_measure C pages (page_base_of base) (HS base ltac:(lia))) as X.
  pose proof (IH (base + 1) (page_insert (page_base_of base) pages) ltac:(intros z Hz; apply HS; lia)) as Y. lia.
Qed.

Lemma access_pages_len (n : nat) (base : Z) (pages : list word) :
  Z.of_nat (length (access_pages_acc base n pages)) <= Z.of_nat (length pages) + (Z.of_nat n / 4096 + 2).
Proof.
  pose proof (access_pages_measure (cand base n) n base pages (cand_in base n)) as X.
  pose proof (missing_le (cand base n) pages) as Y. pose proof (cand_length base n) as Z0. lia.
Qed.

Lemma accesses_pages_len : forall (acc : list (word * nat)) (pages : list word),
  Z.of_nat (length (accesses_pages acc pages)) <= Z.of_nat (length pages) + acc_pages acc.
Proof.
  induction acc as [|[a n] r IH]; intros pages; cbn [accesses_pages]; [rewrite acc_pages_nil; lia|].
  rewrite acc_pages_cons. pose proof (IH (access_pages_acc (bv_unsigned a) n pages)) as X.
  pose proof (access_pages_len n (bv_unsigned a) pages) as Y. lia.
Qed.

Lemma new_pages_len (lz : list (word * word)) (mat : list word) (acc : list (word * nat)) :
  Z.of_nat (length (newly_materialized_pages lz mat acc)) <= acc_pages acc.
Proof.
  unfold newly_materialized_pages. pose proof (accesses_pages_len acc []) as X. cbn [length] in X.
  assert (Y : (length (List.filter (fun p => page_in_ranges p lz && negb (page_mem p mat)) (accesses_pages acc [])) <= length (accesses_pages acc []))%nat).
  { generalize (accesses_pages acc []). intros l. induction l as [|p r IH]; cbn [List.filter length]; [lia|].
    destruct (page_in_ranges p lz && negb (page_mem p mat)); cbn [length]; lia. }
  lia.
Qed.

Theorem materialize_ok (m : Model) (acc : list (word * nat)) :
  vm_backing_used m + 4096 * acc_pages acc <= vm_limit (m_vmmaps m) ->
  exists pages, materialize_model_accesses m acc = Some (with_vm_backing (m_vm_lazy m) pages m)
    /\ vm_backing_used (with_vm_backing (m_vm_lazy m) pages m) <= vm_backing_used m + 4096 * acc_pages acc.
Proof.
  intros Hb. unfold materialize_model_accesses, materialize_accesses.
  pose proof (new_pages_len (m_vm_lazy m) (m_vm_materialized m) acc) as Hn. pose proof (acc_pages_nonneg acc) as Hp.
  destruct (newly_materialized_pages (m_vm_lazy m) (m_vm_materialized m) acc) as [|p r] eqn:E.
  - exists (m_vm_materialized m). split; [reflexivity|]. rewrite wvb_self. lia.
  - rewrite <- E. unfold page_size.
    replace (vm_backing_used m + Z.of_nat (length (newly_materialized_pages (m_vm_lazy m) (m_vm_materialized m) acc)) * 4096 <=? vm_limit (m_vmmaps m))
      with true by (symmetry; apply Z.leb_le; rewrite E in *; lia).
    eexists. split; [reflexivity|]. rewrite wvb_used, length_app. rewrite E in *. lia.
Qed.

Section Step.
Variable segs : list Segment.

Lemma account_none (ms ms' : machine_state) (model : Model) :
  RiscvSemantics.step_accesses segs ms = MachineOk (@mkAccessReport machine_state ms' []) ->
  mi_account_step segs ms model = MachineOk (ms', model).
Proof.
  intros H. unfold mi_account_step. rewrite H. cbn [accessed_ranges access_value].
  unfold materialize_model_accesses, materialize_accesses, newly_materialized_pages. cbn [accesses_pages List.filter].
  rewrite wvb_self. reflexivity.
Qed.

Lemma account_acc (ms ms' : machine_state) (model : Model) (acc : list (word * nat)) :
  RiscvSemantics.step_accesses segs ms = MachineOk (@mkAccessReport machine_state ms' acc) ->
  vm_backing_used model + 4096 * acc_pages acc <= vm_limit (m_vmmaps model) ->
  exists pages, mi_account_step segs ms model = MachineOk (ms', with_vm_backing (m_vm_lazy model) pages model)
    /\ vm_backing_used (with_vm_backing (m_vm_lazy model) pages model) <= vm_backing_used model + 4096 * acc_pages acc.
Proof.
  intros H Hb. destruct (materialize_ok model acc Hb) as [pages [E Hu]]. exists pages. split; [|exact Hu].
  unfold mi_account_step. rewrite H. cbn [accessed_ranges access_value]. rewrite E. reflexivity.
Qed.

End Step.
