(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Arith Bool.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzR2Theory.
From Stdlib Require Lia. Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma lexlt_app : forall u1 v1 u2 v2, length u1 = length v1 ->
  lexlt (u1 ++ u2) (v1 ++ v2) <-> lexlt u1 v1 \/ (u1 = v1 /\ lexlt u2 v2).
Proof.
  induction u1 as [|a u1 IH]; intros [|b v1] u2 v2 Hl; cbn in *; try lia.
  - tauto.
  - rewrite (IH v1 u2 v2) by lia. split.
    + intros [A|[-> [B|[-> C]]]]; [tauto| tauto | right; auto].
    + intros [[A|[-> B]]|[E C]]; [tauto | tauto |]. injection E as -> ->. tauto.
Qed.

Lemma app_eq_heads : forall (u1 v1 u2 v2 : list Z), length u1 = length v1 -> u1 ++ u2 = v1 ++ v2 -> u1 = v1 /\ u2 = v2.
Proof.
  induction u1 as [|a u1 IH]; intros [|b v1] u2 v2 Hl E; cbn in *; try lia; [auto|].
  injection E as -> E'. destruct (IH v1 u2 v2 ltac:(lia) E') as [-> ->]. auto.
Qed.

Lemma lexle_app : forall u1 v1 u2 v2, length u1 = length v1 ->
  lexle (u1 ++ u2) (v1 ++ v2) <-> lexlt u1 v1 \/ (u1 = v1 /\ lexle u2 v2).
Proof.
  intros u1 v1 u2 v2 Hl. unfold lexle. rewrite lexlt_app by exact Hl. split.
  - intros [[A|[-> B]]|E]; [tauto|tauto|]. destruct (app_eq_heads _ _ _ _ Hl E) as [-> ->]. tauto.
  - intros [A|[-> [B| ->]]]; tauto.
Qed.

(* [comment removed for export] *)
Lemma lexlt_heads : forall u1 v1 u2 v2, length u1 = length v1 -> lexlt u1 v1 -> lexlt (u1 ++ u2) (v1 ++ v2).
Proof. intros. apply lexlt_app; auto. Qed.
(* [comment removed for export] *)
Lemma lexle_heads_inv : forall u1 v1 u2 v2, length u1 = length v1 -> lexle (u1 ++ u2) (v1 ++ v2) -> lexle u1 v1.
Proof. intros u1 v1 u2 v2 Hl H. apply lexle_app in H; [|exact Hl]. unfold lexle. tauto. Qed.
Lemma lexlt_heads_inv : forall u1 v1 u2 v2, length u1 = length v1 -> lexlt (u1 ++ u2) (v1 ++ v2) -> lexle u1 v1.
Proof. intros u1 v1 u2 v2 Hl H. apply lexlt_app in H; [|exact Hl]. unfold lexle. tauto. Qed.

Lemma lexle_refl : forall u, lexle u u. Proof. intros; right; reflexivity. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section Pre.
  Variable t : list Z.
  Let n : nat := length t.
  Let nb : Z := Z.of_nat n.
  Hypothesis Hn : (0 < n)%nat.

  Definition ch (p k : Z) : Z := nth (Z.to_nat ((p + k) mod nb)) t 0%Z.
  Definition pre (H : nat) (p : Z) : list Z := map (fun k => ch p (Z.of_nat k)) (seq 0 H).

  Lemma pre_length : forall H p, length (pre H p) = H.
  Proof. intros. unfold pre. rewrite length_map, length_seq. reflexivity. Qed.

  Lemma pre_S : forall H p, pre (S H) p = pre H p ++ [ch p (Z.of_nat H)].
  Proof. intros. unfold pre. rewrite seq_S, map_app. reflexivity. Qed.

  Lemma ch_shift : forall p a k, ch p (a + k) = ch (p + a) k.
  Proof. intros. unfold ch. f_equal. f_equal. f_equal. lia. Qed.

  Lemma ch_mod : forall p k, ch (p mod nb) k = ch p k.
  Proof.
    intros. unfold ch. f_equal. f_equal. rewrite Z.add_mod_idemp_l by (unfold nb; lia). reflexivity.
  Qed.

  Lemma pre_mod : forall H p, pre H (p mod nb) = pre H p.
  Proof. intros. unfold pre. apply map_ext. intros; apply ch_mod. Qed.

  Lemma pre_app : forall a b p, pre (a + b)%nat p = pre a p ++ pre b (p + Z.of_nat a).
  Proof.
    intros a b p. induction b as [|b IH].
    - rewrite Nat.add_0_r. unfold pre at 3. cbn. rewrite app_nil_r. reflexivity.
    - rewrite Nat.add_succ_r, !pre_S, IH, <- app_assoc. f_equal. f_equal. f_equal.
      rewrite <- ch_shift. f_equal. lia.
  Qed.

  (* [comment removed for export] *)

  Lemma nth_firstn_lt : forall (l : list Z) (m k : nat) d, (k < m)%nat -> nth k (firstn m l) d = nth k l d.
  Proof.
    induction l as [|a l IH]; intros [|m] [|k] d Hk; cbn; try reflexivity; try lia. apply IH. lia.
  Qed.

  Lemma nth_rot : forall p k : nat, (p < n)%nat -> (k < n)%nat ->
    nth k (rot t p) 0%Z = nth ((p + k) mod n)%nat t 0%Z.
  Proof.
    intros p k Hp Hk. unfold rot.
    destruct (Nat.lt_ge_cases k (n - p)) as [L|G].
    - rewrite app_nth1 by (rewrite length_skipn; unfold n in *; lia).
      rewrite nth_skipn. rewrite Nat.mod_small by (unfold n in *; lia). reflexivity.
    - rewrite app_nth2 by (rewrite length_skipn; unfold n in *; lia).
      rewrite length_skipn. rewrite nth_firstn_lt by (unfold n in *; lia).
      f_equal. unfold n in *. replace (p + k)%nat with ((k - (length t - p)) + 1 * length t)%nat by lia.
      rewrite Nat.Div0.mod_add. rewrite Nat.mod_small by lia. reflexivity.
  Qed.

  Lemma pre_n_rot : forall p, 0 <= p < nb -> pre n p = rot t (Z.to_nat p).
  Proof.
    intros p Hp.
    apply (nth_ext _ _ 0%Z 0%Z).
    { rewrite pre_length, rot_length; [reflexivity| |unfold n in *; lia]. unfold n; lia. }
    intros k Hk. rewrite pre_length in Hk.
    unfold pre. rewrite (nth_map_seq _ _ 0%Z) by exact Hk. cbn [Nat.add].
    rewrite nth_rot by (unfold n, nb in *; lia). unfold ch. f_equal.
    unfold nb. rewrite <- (Nat2Z.id ((Z.to_nat p + k) mod n)%nat). f_equal.
    rewrite Nat2Z.inj_mod, Nat2Z.inj_add, Z2Nat.id by lia. reflexivity.
  Qed.

  (* [comment removed for export] *)
  Lemma pre_le_rot : forall H p q, (n <= H)%nat -> 0 <= p < nb -> 0 <= q < nb ->
    lexle (pre H p) (pre H q) -> lexle (rot t (Z.to_nat p)) (rot t (Z.to_nat q)).
  Proof.
    intros H p q HH Hp Hq L. rewrite <- !pre_n_rot by assumption.
    replace H with (n + (H - n))%nat in L by lia. rewrite !pre_app in L.
    eapply lexle_heads_inv; [|exact L]. rewrite !pre_length. reflexivity.
  Qed.

  Lemma pre_lt_rot : forall H p q, 0 <= p < nb -> 0 <= q < nb ->
    lexlt (pre H p) (pre H q) -> lexle (rot t (Z.to_nat p)) (rot t (Z.to_nat q)).
  Proof.
    intros H p q Hp Hq L. rewrite <- !pre_n_rot by assumption.
    destruct (Nat.le_gt_cases n H) as [A|A].
    - replace H with (n + (H - n))%nat in L by lia. rewrite !pre_app in L.
      eapply lexlt_heads_inv; [|exact L]. rewrite !pre_length. reflexivity.
    - left. replace n with (H + (n - H))%nat by lia. rewrite !pre_app. apply lexlt_heads; [|exact L].
      rewrite !pre_length. reflexivity.
  Qed.

  (* [comment removed for export] *)
  Lemma pre_lt_ext : forall H H' p q, (H <= H')%nat -> lexlt (pre H p) (pre H q) -> lexlt (pre H' p) (pre H' q).
  Proof.
    intros H H' p q HH L. replace H' with (H + (H' - H))%nat by lia. rewrite !pre_app.
    apply lexlt_heads; [rewrite !pre_length; reflexivity | exact L].
  Qed.
  (* [comment removed for export] *)

  (* [comment removed for export] *)
  Lemma pre2_lt : forall H p q,
    lexlt (pre (H + H)%nat p) (pre (H + H)%nat q) <->
    lexlt (pre H p) (pre H q) \/ (pre H p = pre H q /\ lexlt (pre H (p + Z.of_nat H)) (pre H (q + Z.of_nat H))).
  Proof. intros. rewrite !pre_app. apply lexlt_app. rewrite !pre_length; reflexivity. Qed.
  Lemma pre2_le : forall H p q,
    lexle (pre (H + H)%nat p) (pre (H + H)%nat q) <->
    lexlt (pre H p) (pre H q) \/ (pre H p = pre H q /\ lexle (pre H (p + Z.of_nat H)) (pre H (q + Z.of_nat H))).
  Proof. intros. rewrite !pre_app. apply lexle_app. rewrite !pre_length; reflexivity. Qed.
  (* [comment removed for export] *)

  (* [comment removed for export] *)
  (* [comment removed for export] *)

  (* [comment removed for export] *)
  Lemma pre_1 : forall p, pre 1 p = [ch p 0].
  Proof. intros. reflexivity. Qed.
  Lemma pre1_lt : forall p q, lexlt (pre 1 p) (pre 1 q) <-> ch p 0 < ch q 0.
  Proof. intros. rewrite !pre_1. cbn. tauto. Qed.
  Lemma pre1_le : forall p q, lexle (pre 1 p) (pre 1 q) <-> ch p 0 <= ch q 0.
  Proof.
    intros. unfold lexle. rewrite pre1_lt, !pre_1. split.
    - intros [A|E]; [lia|]. injection E. lia.
    - intros A. destruct (Z.lt_ge_cases (ch p 0) (ch q 0)); [left; lia|right]. f_equal. lia.
  Qed.
  Lemma ch_0 : forall p, 0 <= p < nb -> ch p 0 = nth (Z.to_nat p) t 0%Z.
  Proof. intros p Hp. unfold ch. rewrite Z.add_0_r, Z.mod_small by lia. reflexivity. Qed.
End Pre.
