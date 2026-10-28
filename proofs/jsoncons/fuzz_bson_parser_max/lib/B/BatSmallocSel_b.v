(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require BvWfKernel.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import HeapIface HeapIfaceA HeapIfaceABx. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import BatFsInv_b BatFsInvLaws_b.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.L5FastLia. Require OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.L5FastLiaT. Local Ltac lia := L5FastLiaT.plia1.
Open Scope Z_scope.

Section SEL.
  Variable fs : Z.
  Variable L : list fframe.                         (* [comment removed for export] *)
  Variables (gcb : bool) (sp bot : Z).              (* [comment removed for export] *)

  Definition sl_hit (c i : Z) (f : fframe) : bool := (ff_class f =? c) && (ff_addr f =? fs_frame fs c i).
  Definition sl_flag (c i : Z) : Z := if existsb (sl_hit c i) L then 1 else 0.
  Definition sl_rs (c i : Z) : Z := match find (sl_hit c i) L with Some f => ff_rs f - 32 | None => 0 end.
  (* [comment removed for export] *)
  Definition sl_colb (f : fframe) : bool := gcb && (bot <? ff_rs f - 32) && (ff_rs f - 32 <? sp).
  Definition sl_cols (c i : Z) : bool := gcb && negb (sl_flag c i =? 0) && (bot <? sl_rs c i) && (sl_rs c i <? sp).

  #[using="Type"] Lemma sl_hit_spec : forall c i f, sl_hit c i f = true <-> ff_class f = c /\ ff_addr f = fs_frame fs c i.
  Proof. intros c i f. unfold sl_hit. rewrite andb_true_iff, !Z.eqb_eq. tauto. Qed.
  #[using="Type"] Lemma sl_flag_01 : forall c i, sl_flag c i = 0 \/ sl_flag c i = 1.
  Proof. intros c i. unfold sl_flag. destruct (existsb _ L); [right | left]; reflexivity. Qed.
  #[using="Type"] Lemma sl_flag_taken : forall c i, sl_flag c i = 1 <-> fs_slot_taken fs L c i.
  Proof.
    intros c i. unfold sl_flag, fs_slot_taken. destruct (existsb (sl_hit c i) L) eqn:E.
    - split; [intros _ | reflexivity]. apply existsb_exists in E. destruct E as (f & Hf & Hh). apply sl_hit_spec in Hh. exists f. tauto.
    - split; [discriminate|]. intros (f & Hf & H1 & H2). exfalso.
      assert (X : existsb (sl_hit c i) L = true) by (apply existsb_exists; exists f; split; [exact Hf | apply sl_hit_spec; tauto]). congruence.
  Qed.
  #[using="Type"] Lemma sl_find : forall c i, sl_flag c i <> 0 -> exists f, In f L /\ ff_class f = c /\ ff_addr f = fs_frame fs c i /\ sl_rs c i = ff_rs f - 32.
  Proof.
    intros c i NZ. unfold sl_flag in NZ. unfold sl_rs. destruct (find (sl_hit c i) L) as [f|] eqn:E.
    - apply find_some in E. destruct E as [Hf Hh]. apply sl_hit_spec in Hh. exists f. tauto.
    - exfalso. destruct (existsb (sl_hit c i) L) eqn:X; [|apply NZ; reflexivity]. apply existsb_exists in X. destruct X as (f & Hf & Hh).
      pose proof (find_none _ _ E f Hf). congruence.
  Qed.

  Hypothesis ND : List.NoDup (map ff_addr L).
  #[using="ND"] Lemma sl_find_uniq : forall c i f, In f L -> ff_class f = c -> ff_addr f = fs_frame fs c i -> sl_flag c i = 1 /\ sl_rs c i = ff_rs f - 32.
  Proof.
    intros c i f Hf H1 H2. assert (T : sl_flag c i = 1) by (apply sl_flag_taken; exists f; tauto). split; [exact T|].
    destruct (sl_find c i ltac:(lia)) as (f' & Hf' & H1' & H2' & E). rewrite E.
    assert (f' = f) by (apply (nodup_map_inj _ _ ff_addr L f' f ND Hf' Hf); congruence). subst f'. reflexivity.
  Qed.
  (* [comment removed for export] *)
  #[using="ND"] Lemma sl_cols_frame : forall c i f, In f L -> ff_class f = c -> ff_addr f = fs_frame fs c i -> sl_cols c i = sl_colb f.
  Proof.
    intros c i f Hf H1 H2. destruct (sl_find_uniq c i f Hf H1 H2) as [T E]. unfold sl_cols, sl_colb. rewrite T, E. cbn. rewrite andb_true_r. reflexivity.
  Qed.
  #[using="Type"] Lemma sl_cols_true : forall c i, sl_cols c i = true <-> (gcb = true /\ sl_flag c i <> 0 /\ bot < sl_rs c i < sp).
  Proof.
    intros c i. unfold sl_cols. rewrite !andb_true_iff, negb_true_iff, Z.eqb_neq, !Z.ltb_lt. tauto.
  Qed.
End SEL.

(* [comment removed for export] *)
Lemma least_false : forall (f : Z -> bool) (n : nat), (exists i, 0 <= i < Z.of_nat n /\ f i = false) ->
  exists j, 0 <= j < Z.of_nat n /\ f j = false /\ forall i, 0 <= i < j -> f i = true.
Proof.
  intros f n. induction n as [|n IH]; intros (i & Hi & Fi); [lia|].
  destruct (Z.eq_dec i (Z.of_nat n)) as [->|NE].
  - destruct (existsb (fun m => negb (f (Z.of_nat m))) (seq 0 n)) eqn:E.
    + apply existsb_exists in E. destruct E as (m & Hm & Fm). apply in_seq in Hm. apply negb_true_iff in Fm.
      destruct (IH ltac:(exists (Z.of_nat m); split; [lia | exact Fm])) as (j & Hj & Fj & Lj). exists j. split; [lia | split; assumption].
    + exists (Z.of_nat n). split; [lia|]. split; [exact Fi|]. intros i Hi2.
      pose proof (existsb_nth (fun m => negb (f (Z.of_nat m))) (seq 0 n) 0%nat (n := Z.to_nat i) ltac:(rewrite length_seq; lia) E) as X.
      rewrite seq_nth in X by lia. cbn in X. rewrite Z2Nat.id in X by lia. apply negb_false_iff in X. exact X.
  - destruct (IH ltac:(exists i; split; [lia | exact Fi])) as (j & Hj & Fj & Lj). exists j. split; [lia | split; assumption].
Qed.

Lemma fs_nfr_cap : forall k, 0 <= k <= 5 -> ff_cap k = fs_nfr k /\ fs_nfr k = 2 ^ (14 - k) /\ 0 < fs_nfr k.      (* [comment removed for export] *)
Proof. intros k Hk. assert (E : k = 0 \/ k = 1 \/ k = 2 \/ k = 3 \/ k = 4 \/ k = 5) by lia. destruct E as [->|[->|[->|[->|[->| ->]]]]]; vm_compute; intuition congruence. Qed.

Section LEAST.
  Variable fs : Z.
  Variables FF LK : list fframe.
  Variables (gcb : bool) (sp bot : Z).
  Variables (k h : Z).
  Hypothesis Hk : 0 <= k <= 5.
  Hypothesis ND : List.NoDup (map ff_addr (FF ++ LK)).
  Hypothesis ROOM : ff_room k FF LK.

  (* [comment removed for export] *)
  Definition sl_taken (p : Z) : bool := negb (sl_flag fs (FF ++ LK) k p =? 0) && negb (sl_cols fs (FF ++ LK) gcb sp bot k p).

  #[using="Hk ROOM"] Lemma sl_some_free : exists p, 0 <= p < fs_nfr k /\ sl_taken p = false.
  Proof.
    destruct (fs_nfr_cap k Hk) as (EC & EN & NP).
    destruct (existsb (fun m => negb (sl_taken (Z.of_nat m))) (seq 0 (Z.to_nat (fs_nfr k)))) eqn:E.
    - apply existsb_exists in E. destruct E as (m & Hm & Fm). apply in_seq in Hm. apply negb_true_iff in Fm. exists (Z.of_nat m). split; [lia | exact Fm].
    - exfalso.
      assert (ALL : forall p, 0 <= p < fs_nfr k -> fs_slot_taken fs (FF ++ LK) k p).
      { intros p Hp.
        pose proof (existsb_nth (fun m => negb (sl_taken (Z.of_nat m))) (seq 0 (Z.to_nat (fs_nfr k))) 0%nat (n := Z.to_nat p) ltac:(rewrite length_seq; lia) E) as X.
        rewrite seq_nth in X by lia. cbn in X. rewrite Z2Nat.id in X by lia. apply negb_false_iff in X. unfold sl_taken in X.
        apply andb_true_iff in X. destruct X as [X _]. apply negb_true_iff, Z.eqb_neq in X.
        apply sl_flag_taken. destruct (sl_flag_01 fs (FF ++ LK) k p); [contradiction | assumption]. }
      set (g := fun m : nat => fs_frame fs k (Z.of_nat m)).
      set (LKk := filter (fun f => Z.eqb (ff_class f) k) (FF ++ LK)).
      assert (NDg : List.NoDup (map g (seq 0 (Z.to_nat (fs_nfr k))))).
      { apply Finite.Injective_map_NoDup_in; [|apply seq_NoDup]. intros a b _ _ Eab. unfold g in Eab. apply fs_frame_inj in Eab; lia. }
      assert (INC : incl (map g (seq 0 (Z.to_nat (fs_nfr k)))) (map ff_addr LKk)).
      { intros a Ha. apply in_map_iff in Ha. destruct Ha as (m & <- & Hm). apply in_seq in Hm.
        destruct (ALL (Z.of_nat m) ltac:(lia)) as (f & Hf & H1 & H2). apply in_map_iff. exists f. split; [exact H2|].
        unfold LKk. apply sfilter_In. split; [apply Is_true_eq_left, Z.eqb_eq; exact H1 | exact Hf]. }
      pose proof (NoDup_incl_length NDg INC) as LE. rewrite !length_map, length_seq in LE.
      unfold ff_room, ff_count in ROOM. fold LKk in ROOM. rewrite EC in ROOM. lia.
  Qed.

  #[using="Hk ROOM"] Lemma sl_least_free : exists j, 0 <= j < fs_nfr k /\ sl_taken ((h + j) mod fs_nfr k) = false /\ forall i, 0 <= i < j -> sl_taken ((h + i) mod fs_nfr k) = true.
  Proof.
    destruct (fs_nfr_cap k Hk) as (EC & EN & NP). destruct sl_some_free as (p & Hp & Fp).
    destruct (least_false (fun i => sl_taken ((h + i) mod fs_nfr k)) (Z.to_nat (fs_nfr k))) as (j & Hj & Fj & Lj).
    - exists ((p - h) mod fs_nfr k). pose proof (Z.mod_pos_bound (p - h) (fs_nfr k) NP). split; [lia|].
      replace ((h + (p - h) mod fs_nfr k) mod fs_nfr k) with p; [exact Fp|].
      rewrite Zplus_mod_idemp_r. replace (h + (p - h)) with p by ring. symmetry. apply Z.mod_small. exact Hp.
    - exists j. split; [lia | split; assumption].
  Qed.
End LEAST.
