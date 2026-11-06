(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Bool Lia.
From OSSVerify.Proofs.openssl.ct.lib.Spec Require Import Malloc.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Definition S_ (c : Z) : Z := UNIT * size_class c.
Definition cmax (c : Z) : Z :=
  if c <? 9 then small_cnt c 0 else halve_big 8 (med_cnt (Z.land c 3)) (S_ c).
Definition std_span (c : Z) : Z := cmax c * S_ c + UNIT.
Definition std_nested (c : Z) : bool := std_span c <=? PGSZ / 2.
Definition bighost (c : Z) : Z := if std_nested c then size_to_class (std_span c - IB) else -1.
Definition std_len (c : Z) : Z := round_up_pg (std_span c).

Definition classes : list Z := map Z.of_nat (seq 0 48).

Lemma In_classes c : 0 <= c < 48 <-> In c classes.
Proof.
  unfold classes. rewrite in_map_iff. split.
  - intros H. exists (Z.to_nat c). rewrite in_seq. split; lia.
  - intros (n & <- & Hn). rewrite in_seq in Hn. lia.
Qed.

Lemma forallb_classes (f : Z -> bool) : forallb f classes = true -> forall c, 0 <= c < 48 -> f c = true.
Proof. intros H c Hc. rewrite forallb_forall in H. apply H. apply In_classes. exact Hc. Qed.

Ltac by_table f :=
  let H := fresh in
  assert (H : forallb f classes = true) by (vm_compute; reflexivity);
  intros c Hc; pose proof (forallb_classes f H c Hc) as T; unfold f in T; cbn beta in T;
  repeat (apply andb_prop in T as [T ?]);
  repeat match goal with K : (_ =? _) = true |- _ => apply Z.eqb_eq in K | K : (_ <=? _) = true |- _ => apply Z.leb_le in K | K : (_ <? _) = true |- _ => apply Z.ltb_lt in K end.

(* [comment removed for export] *)
Definition tab_basic (c : Z) : bool :=
  (16 <=? S_ c) && (S_ c <=? 131056) && (8 <=? cmax c) && (cmax c <=? 32) && (std_span c <=? std_len c) && (std_len c <=? std_span c + 4095)
  && (std_len c <=? 1048576) && (Z.modulo (std_len c) PGSZ =? 0).
Lemma tab_basic_ok : forall c, 0 <= c < 48 ->
  16 <= S_ c <= 131056 /\ 8 <= cmax c <= 32 /\ std_span c <= std_len c <= std_span c + 4095 /\ std_len c <= 1048576 /\ std_len c mod PGSZ = 0.
Proof. by_table tab_basic. repeat split; assumption. Qed.

(* [comment removed for export] *)
Definition tab_host (c : Z) : bool :=
  if c <=? 6 then (std_nested c) && ((bighost c =? 15) || (bighost c =? 19) || (bighost c =? 23)) && (std_span c <=? S_ (bighost c)) && (c <? bighost c)
  else negb (std_nested c) && (bighost c =? -1).
Lemma tab_host_small : forall c, 0 <= c <= 6 ->
  std_nested c = true /\ (bighost c = 15 \/ bighost c = 19 \/ bighost c = 23) /\ std_span c <= S_ (bighost c) /\ c < bighost c.
Proof.
  intros c Hc. assert (H : forallb tab_host classes = true) by (vm_compute; reflexivity).
  pose proof (forallb_classes tab_host H c ltac:(lia)) as T. unfold tab_host in T.
  replace (c <=? 6) with true in T by (symmetry; apply Z.leb_le; lia).
  apply andb_prop in T as [T T4]. apply andb_prop in T as [T T3]. apply andb_prop in T as [T1 T2].
  apply Z.leb_le in T3. apply Z.ltb_lt in T4.
  split; [exact T1|]. split; [| auto].
  destruct (Z.eqb_spec (bighost c) 15); [auto|]. destruct (Z.eqb_spec (bighost c) 19); [auto|]. destruct (Z.eqb_spec (bighost c) 23); [auto|]. cbn in T2. discriminate.
Qed.
Lemma tab_host_big : forall c, 7 <= c < 48 -> std_nested c = false /\ bighost c = -1.
Proof.
  intros c Hc. assert (H : forallb tab_host classes = true) by (vm_compute; reflexivity).
  pose proof (forallb_classes tab_host H c ltac:(lia)) as T. unfold tab_host in T.
  replace (c <=? 6) with false in T by (symmetry; apply Z.leb_gt; lia).
  apply andb_prop in T as [T1 T2]. apply Z.eqb_eq in T2. destruct (std_nested c); [discriminate| auto].
Qed.

(* [comment removed for export] *)
Lemma bighost_inv : forall c, 0 <= c < 48 ->
  (bighost c = 15 <-> c = 0) /\ (bighost c = 19 <-> c = 1 \/ c = 2) /\ (bighost c = 23 <-> 3 <= c <= 6).
Proof.
  intros c Hc.
  assert (H : forallb (fun c => Bool.eqb (bighost c =? 15) (c =? 0) && Bool.eqb (bighost c =? 19) ((c =? 1) || (c =? 2)) && Bool.eqb (bighost c =? 23) ((3 <=? c) && (c <=? 6))) classes = true) by (vm_compute; reflexivity).
  pose proof (forallb_classes _ H c Hc) as T. cbn beta in T.
  apply andb_prop in T as [T T3]. apply andb_prop in T as [T1 T2].
  apply Bool.eqb_prop in T1. apply Bool.eqb_prop in T2. apply Bool.eqb_prop in T3.
  split; [| split].
  - rewrite <- Z.eqb_eq, T1, Z.eqb_eq. tauto.
  - rewrite <- Z.eqb_eq, T2, Bool.orb_true_iff, !Z.eqb_eq. tauto.
  - rewrite <- Z.eqb_eq, T3, Bool.andb_true_iff, Z.leb_le, Z.leb_le. tauto.
Qed.

(* [comment removed for export] *)
Lemma size_class_pos : forall c, 0 <= c < 48 -> 0 < size_class c.
Proof. intros c Hc. pose proof (tab_basic_ok c Hc). unfold S_, UNIT in *. lia. Qed.

(* [comment removed for export] *)
Lemma sum_S : fold_right Z.add 0 (map S_ classes) = 795632.
Proof. vm_compute. reflexivity. Qed.
