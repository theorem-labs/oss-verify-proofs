(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
(* [comment removed for export] *)
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Open Scope Z_scope.

(* [comment removed for export] *)
Definition ClassSize (c : Z) : Z :=
  if c =? 31 then 64
  else if c <=? 16 then 32 * c
  else let t := Z.shiftl 512 ((c - 16) / 2) in t + (t / 2) * (c mod 2).

(* [comment removed for export] *)
Definition ClassID (s : Z) : Z :=
  if s <=? 512 then (s + 31) / 32
  else let l := Z.log2 s in
       16 + 2 * (l - 9) + (s / 2 ^ (l - 1)) mod 2 + (if s mod 2 ^ (l - 1) =? 0 then 0 else 1).

(* [comment removed for export] *)
Definition MaxCount (c : Z) : Z := 2 * Z.max 1 (Z.min 8 (1024 / ClassSize c)).

(* [comment removed for export] *)
Definition rz_log (n : Z) : Z :=
  if n <=? 48 then 0 else if n <=? 96 then 1 else if n <=? 448 then 2 else if n <=? 3968 then 3
  else if n <=? 16128 then 4 else if n <=? 32256 then 5 else if n <=? 64512 then 6 else 7.
Definition rz_size (n : Z) : Z := 16 * 2 ^ rz_log n.
Definition rounded (n : Z) : Z := 8 * ((Z.max (Z.max n 1) 8 + 7) / 8).
Definition needed (n : Z) : Z := rounded n + rz_size n.
Definition from_primary (n : Z) : bool := needed n <=? 65536.

(* [comment removed for export] *)
Fixpoint allb_nat (f : Z -> bool) (lo : Z) (k : nat) : bool :=
  match k with O => true | S k' => f lo && allb_nat f (lo + 1) k' end.
Definition allb (f : Z -> bool) (lo hi : Z) : bool := allb_nat f lo (Z.to_nat (hi - lo + 1)).

Lemma allb_nat_ok : forall f k lo, allb_nat f lo k = true -> forall x, lo <= x < lo + Z.of_nat k -> f x = true.
Proof.
  intros f k. induction k as [|k IH]; intros lo H x Hx; cbn in *; [lia|].
  apply andb_true_iff in H as [H1 H2]. destruct (Z.eq_dec x lo) as [->|Hne]; [exact H1|].
  apply (IH (lo + 1) H2). lia.
Qed.

Lemma allb_ok : forall f lo hi, allb f lo hi = true -> forall x, lo <= x <= hi -> f x = true.
Proof. intros f lo hi H x Hx. apply (allb_nat_ok f _ lo H). rewrite Z2Nat.id by lia. lia. Qed.

(* [comment removed for export] *)
Definition class_table : list (Z * Z * Z) :=
  [(1,32,16);(2,64,16);(3,96,16);(4,128,16);(5,160,12);(6,192,10);(7,224,8);(8,256,8);(9,288,6);(10,320,6);
   (11,352,4);(12,384,4);(13,416,4);(14,448,4);(15,480,4);(16,512,4);(17,768,2);(18,1024,2);(19,1536,2);(20,2048,2);
   (21,3072,2);(22,4096,2);(23,6144,2);(24,8192,2);(25,12288,2);(26,16384,2);(27,24576,2);(28,32768,2);(29,49152,2);
   (30,65536,2);(31,64,16)].

Lemma class_table_ok : Forall (fun r => let '(c, sz, mc) := r in ClassSize c = sz /\ MaxCount c = mc) class_table.
Proof. repeat constructor. Qed.

Lemma ClassSize_range : forall c, 1 <= c <= 31 -> 32 <= ClassSize c <= 65536 /\ ClassSize c mod 32 = 0.
Proof.
  intros c Hc. assert (H : allb (fun c => (32 <=? ClassSize c) && (ClassSize c <=? 65536) && (ClassSize c mod 32 =? 0)) 1 31 = true)
    by (vm_compute; reflexivity).
  pose proof (allb_ok _ _ _ H c Hc) as E. cbv beta in E.
  apply andb_true_iff in E as [E E3]. apply andb_true_iff in E as [E1 E2].
  apply Z.leb_le in E1. apply Z.leb_le in E2. apply Z.eqb_eq in E3. lia.
Qed.

Lemma MaxCount_range : forall c, 1 <= c <= 31 -> 2 <= MaxCount c <= 16 /\ MaxCount c mod 2 = 0.
Proof.
  intros c Hc. assert (H : allb (fun c => (2 <=? MaxCount c) && (MaxCount c <=? 16) && (MaxCount c mod 2 =? 0)) 1 31 = true)
    by (vm_compute; reflexivity).
  pose proof (allb_ok _ _ _ H c Hc) as E. cbv beta in E.
  apply andb_true_iff in E as [E E3]. apply andb_true_iff in E as [E1 E2].
  apply Z.leb_le in E1. apply Z.leb_le in E2. apply Z.eqb_eq in E3. lia.
Qed.

(* [comment removed for export] *)
Lemma ClassID_props : forall s, 1 <= s <= 65536 ->
  1 <= ClassID s <= 30 /\ s <= ClassSize (ClassID s).
Proof.
  (* [comment removed for export] *)
  intros s Hs. unfold ClassID.
  destruct (Z.leb_spec s 512) as [Hsm|Hbig].
  - assert (Hc : 1 <= (s + 31) / 32 <= 16) by (Z.div_mod_to_equations; lia).
    split; [lia|]. unfold ClassSize.
    rewrite (proj2 (Z.eqb_neq ((s + 31) / 32) 31)) by lia. rewrite (proj2 (Z.leb_le ((s + 31) / 32) 16)) by lia.
    Z.div_mod_to_equations; lia.
  - assert (Hl : 2 ^ Z.log2 s <= s < 2 ^ (Z.succ (Z.log2 s))) by (apply Z.log2_spec; lia).
    assert (Hl9 : 9 <= Z.log2 s <= 16).
    { split; [change 9 with (Z.log2 513); apply Z.log2_le_mono; lia | change 16 with (Z.log2 65536); apply Z.log2_le_mono; lia]. }
    remember (Z.log2 s) as l eqn:El. clear El.
    assert (Hcases : l = 9 \/ l = 10 \/ l = 11 \/ l = 12 \/ l = 13 \/ l = 14 \/ l = 15 \/ l = 16) by lia.
    destruct Hcases as [E|[E|[E|[E|[E|[E|[E|E]]]]]]]; subst l;
    repeat match goal with |- context [2 ^ ?k] => let v := eval vm_compute in (2 ^ k) in change (2 ^ k) with v end;
    repeat match type of Hl with context [2 ^ ?k] => let v := eval vm_compute in (2 ^ k) in change (2 ^ k) with v in Hl end;
    match goal with |- context [s / ?hv] =>
      assert (Hq : s / hv = 2 \/ s / hv = 3) by (Z.div_mod_to_equations; lia);
      destruct (Z.eqb_spec (s mod hv) 0) as [Hr|Hr];
      destruct Hq as [Hq|Hq]; rewrite Hq;
      (match goal with |- context [?x mod 2] => let v := eval vm_compute in (x mod 2) in change (x mod 2) with v end);
      (split; [Z.div_mod_to_equations; lia|]);
      match goal with |- _ <= ClassSize ?c =>
        let cv := eval vm_compute in c in change c with cv;
        let v := eval vm_compute in (ClassSize cv) in change (ClassSize cv) with v end;
      Z.div_mod_to_equations; lia
    end.
Qed.

Lemma ClassID_small : forall s, 1 <= s <= 512 -> ClassID s = (s + 31) / 32.
Proof. intros s Hs. unfold ClassID. rewrite (proj2 (Z.leb_le s 512)) by lia. reflexivity. Qed.

Lemma ClassSize_ClassID : forall c, 1 <= c <= 30 -> ClassID (ClassSize c) = c.
Proof.
  intros c Hc. assert (H : allb (fun c => ClassID (ClassSize c) =? c) 1 30 = true) by (vm_compute; reflexivity).
  pose proof (allb_ok _ _ _ H c Hc) as E. apply Z.eqb_eq in E. exact E.
Qed.

(* [comment removed for export] *)
Lemma needed_range : forall n, 1 <= n <= 64512 -> 24 <= needed n <= 65536 /\ needed n mod 8 = 0.
Proof.
  (* [comment removed for export] *)
  intros n Hn. unfold needed, rounded, rz_size, rz_log.
  assert (E : exists k, 0 <= k <= 6 /\ (if n <=? 48 then 0 else if n <=? 96 then 1 else if n <=? 448 then 2 else if n <=? 3968 then 3
            else if n <=? 16128 then 4 else if n <=? 32256 then 5 else if n <=? 64512 then 6 else 7) = k).
  { destruct (Z.leb_spec n 48); [exists 0; split; [lia | reflexivity]|].
    destruct (Z.leb_spec n 96); [exists 1; split; [lia | reflexivity]|].
    destruct (Z.leb_spec n 448); [exists 2; split; [lia | reflexivity]|].
    destruct (Z.leb_spec n 3968); [exists 3; split; [lia | reflexivity]|].
    destruct (Z.leb_spec n 16128); [exists 4; split; [lia | reflexivity]|].
    destruct (Z.leb_spec n 32256); [exists 5; split; [lia | reflexivity]|].
    destruct (Z.leb_spec n 64512); [exists 6; split; [lia | reflexivity]|]. exfalso; lia. }
  destruct E as (k & Hk & ->).
  assert (P : 1 <= 2 ^ k <= 64) by (split; [change 1 with (2 ^ 0); apply Z.pow_le_mono_r; lia| change 64 with (2 ^ 6); apply Z.pow_le_mono_r; lia]).
  assert (Q1 : 16 * 2 ^ k <= 1024) by lia.
  pose proof (Z.div_mod (Z.max (Z.max n 1) 8 + 7) 8 ltac:(lia)) as D. pose proof (Z.mod_pos_bound (Z.max (Z.max n 1) 8 + 7) 8 ltac:(lia)) as D2.
  split; [lia|]. Z.div_mod_to_equations. lia.
Qed.

Lemma rounded_ge : forall n, 1 <= n -> n <= rounded n.
Proof.
  intros n Hn. unfold rounded. pose proof (Z.div_mod (Z.max (Z.max n 1) 8 + 7) 8 ltac:(lia)) as D.
  pose proof (Z.mod_pos_bound (Z.max (Z.max n 1) 8 + 7) 8 ltac:(lia)). lia.
Qed.

Lemma rz_log_big : forall n, 64512 < n -> rz_log n = 7.
Proof.
  intros n Hn. unfold rz_log.
  repeat (rewrite (proj2 (Z.leb_gt _ _)) by lia). reflexivity.
Qed.

Lemma from_primary_iff : forall n, 1 <= n -> from_primary n = true <-> n <= 64512.
Proof.
  intros n Hn. unfold from_primary. split; intros H.
  - apply Z.leb_le in H. destruct (Z.leb_spec n 64512) as [|Hg]; [lia|].
    exfalso. unfold needed, rz_size in H. rewrite rz_log_big in H by lia. pose proof (rounded_ge n Hn). change (16 * 2 ^ 7) with 2048 in H. lia.
  - pose proof (needed_range n ltac:(lia)) as [[_ E] _]. apply Z.leb_le. exact E.
Qed.
