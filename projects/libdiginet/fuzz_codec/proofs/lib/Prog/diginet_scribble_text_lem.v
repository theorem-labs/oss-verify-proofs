From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame Bytes Arr.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Spec Require Import DgnSpec DgnLib.
Import ListNotations.
Open Scope Z_scope.

Lemma u8arr_split : forall segs m A bs k, (k <= length bs)%nat -> u8arr segs m A bs ->
  u8arr segs m A (firstn k bs) /\ u8arr segs m (A + Z.of_nat k) (skipn k bs).
Proof.
  intros segs m A bs k Hk [Hb (Ha & Hn & Hw)].
  rewrite <- (firstn_skipn k bs) in Hb. apply bytes_at_app in Hb. destruct Hb as [H1 H2].
  rewrite firstn_length_le in H2 by lia.
  split; split; auto.
  - rewrite firstn_length_le by lia. split; [lia|]. split; [lia|]. intros i Hi. apply Hw. lia.
  - rewrite length_skipn. split; [lia|]. split; [lia|]. intros i Hi.
    replace (A + Z.of_nat k + i) with (A + (Z.of_nat k + i)) by lia. apply Hw. lia.
Qed.

Lemma u8arr_join : forall segs m A xs ys, u8arr segs m A xs -> u8arr segs m (A + Z.of_nat (length xs)) ys ->
  u8arr segs m A (xs ++ ys).
Proof.
  intros segs m A xs ys [Hb1 (Ha1 & Hn1 & Hw1)] [Hb2 (Ha2 & Hn2 & Hw2)].
  split; [apply bytes_at_app; auto|].
  rewrite length_app, Nat2Z.inj_add. split; [lia|]. split; [lia|].
  intros i Hi. destruct (Z.lt_ge_cases i (Z.of_nat (length xs))) as [H|H]; [apply Hw1; lia|].
  replace (A + i) with (A + Z.of_nat (length xs) + (i - Z.of_nat (length xs))) by lia. apply Hw2. lia.
Qed.

Lemma skipn_nth_cons : forall {X} (l : list X) i d, (i < length l)%nat -> skipn i l = nth i l d :: skipn (S i) l.
Proof. intros X l. induction l as [|x l IH]; intros [|i] d H; cbn in *; try lia; [reflexivity|]. apply IH. lia. Qed.

Lemma nth_error_nth' : forall {X} (l : list X) i d, (i < length l)%nat -> nth_error l i = Some (nth i l d).
Proof. intros X l. induction l as [|x l IH]; intros [|i] d H; cbn in *; try lia; [reflexivity|]. apply IH. lia. Qed.

Lemma le1_lit : forall z, le1 (Z_to_bv 64 z) = [Z_to_bv 8 z].
Proof.
  intros z. unfold le1. rewrite Z_to_bv_unsigned. cbn [Z_to_le_bytes]. f_equal.
  apply Z_to_bv8_mod. unfold bv_wrap, bv_modulus. apply mod_mod8_of_modw. lia.
Qed.

Lemma byte_range : forall b : byte, 0 <= bv_unsigned b < 256.
Proof. intros b. pose proof (bv_unsigned_in_range 8 b) as R. unfold bv_modulus in R. change (2 ^ Z.of_N 8) with 256 in R. lia. Qed.

Lemma land255 : forall x, 0 <= x < 256 -> Z.land x 255 = x.
Proof. intros x Hx. change 255 with (Z.ones 8). rewrite Z.land_ones by lia. apply Z.mod_small. change (2 ^ 8) with 256. lia. Qed.

Lemma u_zxb : forall b : byte, bv_unsigned (zxb b) = bv_unsigned b.
Proof. intros b. unfold zxb. apply unsigned_lit. pose proof (byte_range b). lia. Qed.

Lemma In_skipn_lt : forall {X} (x : X) l k, In x (skipn k l) -> (k < length l)%nat.
Proof.
  intros X x l k H. destruct (Nat.lt_ge_cases k (length l)) as [Hl|Hl]; [exact Hl|].
  rewrite skipn_all2 in H by lia. destruct H.
Qed.

Lemma Hp_snoc : forall (ob : list byte) o b pre, (Z.to_nat o < length ob)%nat -> 0 <= o ->
  firstn (Z.to_nat o) ob = pre -> firstn (Z.to_nat (o + 1)) (upd ob (Z.to_nat o) b) = pre ++ [b].
Proof.
  intros ob o b pre Hlt Ho Hp. replace (Z.to_nat (o + 1)) with (S (Z.to_nat o)) by lia.
  rewrite upd_firstn_skipn by exact Hlt. rewrite firstn_app, firstn_length_le by lia.
  replace (S (Z.to_nat o) - Z.to_nat o)%nat with 1%nat by lia. rewrite firstn_firstn.
  replace (Nat.min (S (Z.to_nat o)) (Z.to_nat o)) with (Z.to_nat o) by lia. rewrite Hp. reflexivity.
Qed.

Lemma scr_lib_0 : forall l, scr_lib l 0 = ([], 0).
Proof. intros [|x l]; reflexivity. Qed.

Lemma scr_zero : forall l k, scr_lib (0 :: l) k = (repeat 0x20 k, 0).
Proof. intros l [|k]; reflexivity. Qed.

Lemma scr_step : forall x y l k, x <> 0 ->
  scr_lib (x :: y :: l) (S k) =
  (if (x =? 0x2e) && (0x31 <=? y) && (y <=? 0x39)
   then ((y - 26) :: fst (scr_lib l k), snd (scr_lib l k) + 2)
   else ((if x <? 0x80 then x else 0x3f) :: fst (scr_lib (y :: l) k), snd (scr_lib (y :: l) k) + 1)).
Proof.
  intros x y l k Hx.
  change (scr_lib (x :: y :: l) (S k)) with
    (if x =? 0 then (repeat 0x20 (S k), 0)
     else if (x =? 0x2e) && (0x31 <=? y) && (y <=? 0x39)
     then let '(o, u) := scr_lib l k in ((y - 26) :: o, u + 2)
     else let '(o, u) := scr_lib (y :: l) k in ((if x <? 0x80 then x else 0x3f) :: o, u + 1)).
  rewrite (proj2 (Z.eqb_neq x 0) Hx).
  destruct ((x =? 0x2e) && (0x31 <=? y) && (y <=? 0x39)).
  - destruct (scr_lib l k); reflexivity.
  - destruct (scr_lib (y :: l) k); reflexivity.
Qed.
