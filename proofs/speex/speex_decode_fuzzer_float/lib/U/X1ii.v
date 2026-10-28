(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import X1cd X1bk X1bj X1cf.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.U Require Import X1ik.
Import ListNotations.
Open Scope Z_scope.

Lemma skipn_nth_cons : forall {A} (l : list A) n (d : A), (n < length l)%nat -> skipn n l = nth n l d :: skipn (S n) l.
Proof.
induction l as [|x l IH]; intros n d Hn; cbn in Hn; [lia|].
destruct n as [|n]; [reflexivity|]. cbn [skipn nth]. apply IH. lia.
Qed.

Lemma ubytes_skip_cons : forall bs i, 0 <= i -> (Z.to_nat i < length bs)%nat ->
skipn (Z.to_nat i) (ubytes bs) = bv_unsigned (nth (Z.to_nat i) bs (Z_to_bv 8 0)) :: skipn (Z.to_nat (i + 1)) (ubytes bs).
Proof.
intros bs i Hi Hl. rewrite (skipn_nth_cons (ubytes bs) (Z.to_nat i) (bv_unsigned (Z_to_bv 8 0))) by (rewrite ubytes_length; exact Hl).
unfold ubytes at 2. rewrite map_nth. fold (ubytes bs). f_equal. f_equal. lia.
Qed.

Lemma bytes_at_sub : forall m A bs (i n : nat), bytes_at rsegs m A bs -> (i + n <= length bs)%nat ->
bytes_at rsegs m (A + Z.of_nat i) (firstn n (skipn i bs)).
Proof.
intros m A bs i n HB Hin.
rewrite <- (firstn_skipn i bs) in HB. apply bytes_at_app in HB. destruct HB as [_ HB].
rewrite firstn_length_le in HB by lia.
rewrite <- (firstn_skipn n (skipn i bs)) in HB. apply bytes_at_app in HB. destruct HB as [HB _]. exact HB.
Qed.

Lemma upd_app_r : forall {X} (l1 l2 : list X) k y n, n = (length l1 + k)%nat -> upd (l1 ++ l2) n y = l1 ++ upd l2 k y.
Proof. induction l1; intros l2 k y n ->; cbn; [reflexivity|]. rewrite (IHl1 l2 k y (length l1 + k)%nat eq_refl). reflexivity. Qed.

Lemma upd_upd_bytes1 : forall (l : list byte) i a, (i < length l)%nat -> upd l i a = upd_bytes l i [a].
Proof. intros. unfold upd_bytes. cbn [length app]. rewrite upd_firstn_skipn by lia. rewrite Nat.add_1_r. reflexivity. Qed.

Lemma upd_bytes_snoc : forall (l : list byte) i xs y n, (i + length xs < length l)%nat -> n = (i + length xs)%nat ->
upd (upd_bytes l i xs) n y = upd_bytes l i (xs ++ [y]).
Proof.
intros l i xs y n Hl ->. unfold upd_bytes. rewrite app_assoc.
rewrite (upd_app_r _ _ 0 y) by (rewrite length_app, firstn_length_le; lia).
rewrite (skipn_nth_cons l (i + length xs) y) by lia. cbn [upd].
rewrite length_app. cbn [length]. replace (i + (length xs + 1))%nat with (S (i + length xs)) by lia.
rewrite <- (app_assoc xs [y]), <- app_assoc. reflexivity.
Qed.

Lemma upd4_upd_bytes : forall (l : list byte) i a b c d n1 n2 n3, (i + 4 <= length l)%nat ->
n1 = S i -> n2 = S (S i) -> n3 = S (S (S i)) ->
upd (upd (upd (upd l i a) n1 b) n2 c) n3 d = upd_bytes l i [a; b; c; d].
Proof.
intros l i a b c d n1 n2 n3 Hl -> -> ->.
rewrite (upd_upd_bytes1 l i a) by lia.
rewrite (upd_bytes_snoc l i [a] b) by (cbn; lia).
rewrite (upd_bytes_snoc l i ([a] ++ [b]) c) by (first [cbn; lia | rewrite upd_bytes_length; cbn; lia]).
rewrite (upd_bytes_snoc l i ([a] ++ [b] ++ [c]) d) by (first [cbn; lia | rewrite upd_bytes_length; cbn; lia]).
reflexivity.
Qed.

Lemma upd_bytes_twice : forall (l xs ys : list byte) i, length xs = length ys -> (i + length xs <= length l)%nat ->
upd_bytes (upd_bytes l i xs) i ys = upd_bytes l i ys.
Proof.
intros l xs ys i Hlen Hl. unfold upd_bytes.
assert (L1 : length (firstn i l) = i) by (rewrite firstn_length_le; lia).
rewrite firstn_app, L1, Nat.sub_diag, firstn_O, app_nil_r, firstn_firstn, Nat.min_id.
rewrite skipn_app, L1, (skipn_all2 (firstn i l)) by lia. cbn [app].
rewrite skipn_app, skipn_all2 by lia. rewrite Hlen.
replace (i + length ys - i - length ys)%nat with 0%nat by lia. reflexivity.
Qed.

Lemma slice_upd_bytes_in : forall (l xs : list byte) p i n,
(i + length xs <= n)%nat -> (p + n <= length l)%nat ->
firstn n (skipn p (upd_bytes l (p + i) xs)) = upd_bytes (firstn n (skipn p l)) i xs.
Proof.
intros l xs p i n Hin Hl. unfold upd_bytes.
rewrite skipn_app, firstn_length_le, skipn_firstn_comm by lia.
replace (p - (p + i))%nat with 0%nat by lia. replace (p + i - p)%nat with i by lia. cbn [skipn].
rewrite firstn_app, firstn_firstn. replace (Nat.min n i) with i by lia.
rewrite length_firstn, length_skipn. replace (Nat.min i (length l - p)) with i by lia.
rewrite firstn_app. rewrite (firstn_all2 xs) by lia.
rewrite firstn_firstn. replace (Nat.min i n) with i by lia.
rewrite skipn_firstn_comm, skipn_skipn.
f_equal. f_equal. replace (n - (i + length xs))%nat with (n - i - length xs)%nat by lia.
f_equal. f_equal. lia.
Qed.

Lemma slice_upd_bytes_out : forall (l xs : list byte) q i n,
(i + length xs <= q)%nat -> (i + length xs <= length l)%nat ->
firstn n (skipn q (upd_bytes l i xs)) = firstn n (skipn q l).
Proof.
intros l xs q i n Hq Hl. unfold upd_bytes. f_equal.
rewrite skipn_app, firstn_length_le, skipn_all2 by (rewrite ?firstn_length_le; lia). cbn [app].
rewrite skipn_app, skipn_all2, skipn_skipn by lia. cbn [app]. f_equal. lia.
Qed.

Lemma le1_lit : forall v, 0 <= v < 256 -> le1 (Z_to_bv 64 v) = [Z_to_bv 8 v].
Proof. intros v Hv. unfold le1. rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2^64). rewrite Z.mod_small by lia. cbn [Z_to_le_bytes]. reflexivity. Qed.

Lemma le1_bits : forall v b, 0 <= b < 256 -> Forall (fun i => Z.testbit v i = Z.testbit b i) (zseq 8) ->
le1 (Z_to_bv 64 v) = [Z_to_bv 8 b].
Proof.
intros v b Hb Hbits. unfold le1. rewrite Z_to_bv_unsigned. cbn [Z_to_le_bytes]. f_equal. apply bv_eq.
rewrite !Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 8) with (2^8). change (bv_modulus 64) with (2^64).
apply Z.bits_inj'. intros i Hi.
destruct (Z.lt_ge_cases i 8).
- rewrite !Z.mod_pow2_bits_low by lia. apply (forall_zseq _ 8 Hbits). lia.
- rewrite !Z.mod_pow2_bits_high by lia. reflexivity.
Qed.
Ltac le1_by_bits := apply le1_bits; [lia| let l := eval vm_compute in (zseq 8) in change (zseq 8) with l;
repeat (apply Forall_cons; [tb; tb_close|]); try apply Forall_nil].

Ltac arr_store ARR i b :=
lazymatch type of ARR with
| u8arr _ ?m ?A ?bs =>
lazymatch goal with
| |- evt _ _ (MS _ _ _ _ _ (write_to_mem m ?a ?v) _) =>
replace v with [b] by (symmetry; first [reflexivity | apply le1_lit; lia | idtac]);
replace (write_to_mem m a [b]) with (write_to_mem m (wa (A + i)) [b]) by (f_equal; unfold wa; f_equal; lia);
let ARR2 := fresh "ARR" in
pose proof (u8arr_write rsegs _ _ _ i b ARR ltac:(rewrite ?upd_length; lia)) as ARR2; clear ARR; store_done; rename ARR2 into ARR
end
end.

