(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude.
From OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib Require Import
  PropExec CatExec CatSim SeqExec StoreOk BnZX.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Module BM.
Import ZX.

Section WithSegs.
Variable segs : list Segment.

Definition cellN (m : word -> option byte) (a : Z) (n : nat) (v : Z) : Prop :=
  exists bs, rdn segs m (Z_to_bv 64 a) n = Some bs /\ bytes_le_to_Z bs = v.

Definition arr32 (m : word -> option byte) (a : Z) (l : list Z) : Prop :=
  forall i, (i < length l)%nat -> cellN m (a + 4 * Z.of_nat i) 4 (nth i l 0).

(* [comment removed for export] *)
Definition in_rs (x : Z) (rs : list (Z * Z)) : Prop := exists r, In r rs /\ fst r <= x < snd r.

Definition unch (m m' : word -> option byte) (rs : list (Z * Z)) : Prop :=
  forall x : word, ~ in_rs (bv_unsigned x) rs -> m' x = m x.

Lemma cellN_range : forall m a n v, cellN m a n v -> 0 <= v < 2 ^ (8 * Z.of_nat n).
Proof.
  intros m a n v (bs & H & <-). pose proof (rdn_length segs m n _ bs H) as <-.
  split; [apply bytes_le_to_Z_nonneg | apply bytes_le_to_Z_bound].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma u_lit : forall a, 0 <= a < M64 -> bv_unsigned (Z_to_bv 64 a) = a.
Proof. intros. rewrite u_Z2bv64. apply Z.mod_small. assumption. Qed.

Lemma cellN_store_same : forall m a n (w : word), (n <= 8)%nat -> 0 <= a -> a + Z.of_nat n <= M64 ->
  cellN (wbytes m (Z_to_bv 64 a) (word_to_le_bytes n w)) a n (bv_unsigned w mod 2 ^ (8 * Z.of_nat n)).
Proof.
  intros m a n w Hn Ha Hb. unfold cellN. exists (word_to_le_bytes n w). split.
  - pose proof (rdn_wbytes_hit segs (word_to_le_bytes n w) m (Z_to_bv 64 a)) as H.
    rewrite length_N_to_le_bytes in H. apply H.
    destruct n; [rewrite u_Z2bv64; pose proof (Z.mod_pos_bound a M64 ltac:(lia)); cbn; lia|].
    rewrite u_lit; lia.
  - apply bytes_le_N.
Qed.

Lemma cellN_store_other : forall m a n v a' n' (w : word),
  0 <= a -> a + Z.of_nat n <= M64 -> 0 <= a' -> a' + Z.of_nat n' <= M64 ->
  (a + Z.of_nat n <= a' \/ a' + Z.of_nat n' <= a) ->
  cellN (wbytes m (Z_to_bv 64 a') (word_to_le_bytes n' w)) a n v <-> cellN m a n v.
Proof.
  intros m a n v a' n' w Ha Hb Ha' Hb' Hd. unfold cellN.
  destruct n as [|n0].
  { cbn [rdn]. tauto. }
  destruct n' as [|n0'].
  { cbn [word_to_le_bytes Z_to_le_bytes wbytes]. tauto. }
  rewrite rdn_wbytes_out; [tauto | | |]; rewrite ?length_N_to_le_bytes, ?u_lit; lia.
Qed.

Lemma cellN_store_same' : forall m a n (w : word) v, (n <= 8)%nat -> 0 <= a -> a + Z.of_nat n <= M64 ->
  bv_unsigned w mod 2 ^ (8 * Z.of_nat n) = v ->
  cellN (wbytes m (Z_to_bv 64 a) (word_to_le_bytes n w)) a n v.
Proof. intros m a n w v Hn Ha Hb <-. apply cellN_store_same; assumption. Qed.

Lemma cellN_store_skip : forall m a n v a' n' (w : word),
  0 <= a -> a + Z.of_nat n <= M64 -> 0 <= a' -> a' + Z.of_nat n' <= M64 ->
  (a + Z.of_nat n <= a' \/ a' + Z.of_nat n' <= a) ->
  cellN m a n v -> cellN (wbytes m (Z_to_bv 64 a') (word_to_le_bytes n' w)) a n v.
Proof. intros. apply cellN_store_other; assumption. Qed.

Lemma arr32_length_bound : forall m a l, arr32 m a l -> True. Proof. auto. Qed.

Lemma nth_upd_app : forall (done : list Z) x t v i,
  nth i (done ++ v :: t) 0 = if Nat.eqb i (length done) then v else nth i (done ++ x :: t) 0.
Proof.
  intros done x t v i. destruct (Nat.eqb_spec i (length done)) as [->|Hne].
  - rewrite nth_middle. reflexivity.
  - destruct (Nat.lt_ge_cases i (length done)).
    + rewrite !app_nth1 by assumption. reflexivity.
    + rewrite !app_nth2 by lia. destruct (i - length done)%nat eqn:E; [lia|]. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma arr32_store : forall m a done x t (w : word),
  0 <= a -> a + 4 * Z.of_nat (length (done ++ x :: t)) <= M64 ->
  arr32 m a (done ++ x :: t) ->
  arr32 (wbytes m (Z_to_bv 64 (a + 4 * Z.of_nat (length done))) (word_to_le_bytes 4 w)) a
        (done ++ (bv_unsigned w mod 2 ^ 32) :: t).
Proof.
  intros m a done x t w Ha Hb H i Hi.
  assert (HL : forall y, length (done ++ y :: t) = S (length done + length t)) by (intros; rewrite length_app; cbn; lia).
  rewrite HL in Hi, Hb.
  rewrite (nth_upd_app done x t).
  destruct (Nat.eqb_spec i (length done)) as [->|Hne].
  - apply (cellN_store_same m _ 4 w); [lia|lia|lia].
  - apply cellN_store_other; try lia. apply H. rewrite HL. lia.
Qed.

Lemma arr32_store' : forall m a done x t (w : word) v,
  0 <= a -> a + 4 * Z.of_nat (length (done ++ x :: t)) <= M64 ->
  arr32 m a (done ++ x :: t) -> bv_unsigned w mod 2 ^ 32 = v ->
  arr32 (wbytes m (Z_to_bv 64 (a + 4 * Z.of_nat (length done))) (word_to_le_bytes 4 w)) a (done ++ v :: t).
Proof. intros m a done x t w v Ha Hb H <-. apply arr32_store with (x := x); assumption. Qed.

(* [comment removed for export] *)
Lemma arr32_snoc : forall m a l (w : word),
  0 <= a -> a + 4 * Z.of_nat (length l) + 4 <= M64 ->
  arr32 m a l ->
  arr32 (wbytes m (Z_to_bv 64 (a + 4 * Z.of_nat (length l))) (word_to_le_bytes 4 w)) a
        (l ++ [bv_unsigned w mod 2 ^ 32]).
Proof.
  intros m a l w Ha Hb H i Hi. rewrite length_app in Hi. cbn [length] in Hi.
  destruct (Nat.eqb_spec i (length l)) as [->|Hne].
  - rewrite nth_middle. apply (cellN_store_same m _ 4 w); lia.
  - rewrite app_nth1 by lia. apply cellN_store_other; try lia. apply H. lia.
Qed.

Lemma arr32_snoc' : forall m a l (w : word) v,
  0 <= a -> a + 4 * Z.of_nat (length l) + 4 <= M64 ->
  arr32 m a l -> bv_unsigned w mod 2 ^ 32 = v ->
  arr32 (wbytes m (Z_to_bv 64 (a + 4 * Z.of_nat (length l))) (word_to_le_bytes 4 w)) a (l ++ [v]).
Proof. intros m a l w v Ha Hb H <-. apply arr32_snoc; assumption. Qed.

(* [comment removed for export] *)
Lemma arr32_store_other : forall m a l a' n' (w : word),
  0 <= a -> a + 4 * Z.of_nat (length l) <= M64 -> 0 <= a' -> a' + Z.of_nat n' <= M64 ->
  (a + 4 * Z.of_nat (length l) <= a' \/ a' + Z.of_nat n' <= a) ->
  arr32 m a l -> arr32 (wbytes m (Z_to_bv 64 a') (word_to_le_bytes n' w)) a l.
Proof.
  intros m a l a' n' w Ha Hb Ha' Hb' Hd H i Hi. apply cellN_store_other; try lia. apply H, Hi.
Qed.

(* [comment removed for export] *)
Lemma arr32_store_beyond : forall m a l k n' (w : word),
  0 <= a -> a + 4 * k + Z.of_nat n' <= M64 -> Z.of_nat (length l) <= k ->
  arr32 m a l -> arr32 (wbytes m (Z_to_bv 64 (a + 4 * k)) (word_to_le_bytes n' w)) a l.
Proof.
  intros m a l k n' w Ha Hb Hk H i Hi. apply cellN_store_other; try lia. apply H, Hi.
Qed.

Lemma arr32_nil : forall m a, arr32 m a [].
Proof. intros m a i Hi. cbn in Hi. lia. Qed.

Lemma arr32_prefix : forall m a l1 l2, arr32 m a (l1 ++ l2) -> arr32 m a l1.
Proof.
  intros m a l1 l2 H i Hi. specialize (H i ltac:(rewrite length_app; lia)). rewrite app_nth1 in H by lia. exact H.
Qed.

Lemma arr32_cell : forall m a l i, arr32 m a l -> (i < length l)%nat ->
  cellN m (a + 4 * Z.of_nat i) 4 (nth i l 0).
Proof. intros. apply H, H0. Qed.

(* [comment removed for export] *)
Lemma arr32_nth_range : forall m a l i, arr32 m a l -> (i < length l)%nat -> 0 <= nth i l 0 < 2 ^ 32.
Proof. intros m a l i H Hi. exact (cellN_range _ _ _ _ (H i Hi)). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma unch_refl : forall m rs, unch m m rs.
Proof. intros m rs x _. reflexivity. Qed.

Lemma unch_trans : forall m1 m2 m3 rs, unch m1 m2 rs -> unch m2 m3 rs -> unch m1 m3 rs.
Proof. intros m1 m2 m3 rs H1 H2 x Hx. rewrite (H2 x Hx). apply H1, Hx. Qed.

Lemma in_rs_incl : forall x rs rs', in_rs x rs -> (forall r, In r rs -> exists r', In r' rs' /\ fst r' <= fst r /\ snd r <= snd r') -> in_rs x rs'.
Proof.
  intros x rs rs' (r & Hin & Hr) Hsub. destruct (Hsub r Hin) as (r' & Hin' & H1 & H2).
  exists r'. split; [exact Hin'|lia].
Qed.

(* [comment removed for export] *)
Lemma unch_widen : forall m m' rs rs', unch m m' rs ->
  (forall r, In r rs -> exists r', In r' rs' /\ fst r' <= fst r /\ snd r <= snd r') -> unch m m' rs'.
Proof. intros m m' rs rs' H Hsub x Hx. apply H. intros Hin. apply Hx. eapply in_rs_incl; eauto. Qed.

Lemma unch_store : forall m a n (w : word) rs lo hi,
  0 <= a -> a + Z.of_nat n <= M64 -> In (lo, hi) rs -> lo <= a -> a + Z.of_nat n <= hi ->
  unch m (wbytes m (Z_to_bv 64 a) (word_to_le_bytes n w)) rs.
Proof.
  intros m a n w rs lo hi Ha Hb Hin Hlo Hhi x Hx.
  destruct n as [|n0]; [reflexivity|].
  assert (Hu : bv_unsigned (Z_to_bv 64 a) = a) by (apply u_lit; lia).
  assert (Hout : ~ (a <= bv_unsigned x < a + Z.of_nat (S n0))).
  { intros Hc. apply Hx. exists (lo, hi). split; [exact Hin|]. cbn. lia. }
  destruct (Z.lt_ge_cases (bv_unsigned x) a).
  - apply wbytes_below; rewrite ?length_N_to_le_bytes, Hu; lia.
  - apply wbytes_above. rewrite length_N_to_le_bytes, Hu. lia.
Qed.

Lemma grows_store : forall m (a : word) bs, mem_grows m (wbytes m a bs).
Proof. intros. apply wbytes_grows. Qed.

Lemma store_ok_grows : forall m m' (a : word) n, mem_grows m m' ->
  RiscvSemantics.store_ok segs m a n = true -> RiscvSemantics.store_ok segs m' a n = true.
Proof. intros. eapply store_ok_mono; eauto. Qed.

(* [comment removed for export] *)
Lemma cellN_unch : forall m m' a n v rs,
  unch m m' rs -> 0 <= a -> a + Z.of_nat n <= M64 ->
  (forall r, In r rs -> a + Z.of_nat n <= fst r \/ snd r <= a) ->
  cellN m a n v -> cellN m' a n v.
Proof.
  intros m m' a n v rs Hu Ha Hb Hd (bs & Hr & Hv). exists bs. split; [|exact Hv].
  rewrite <- Hr. destruct n as [|n0]; [reflexivity|].
  apply rdn_ext; [rewrite u_lit; lia|].
  intros x Hx. apply Hu. rewrite u_lit in Hx by lia. intros (r & Hin & Hr'). specialize (Hd r Hin). lia.
Qed.

Lemma arr32_unch : forall m m' a l rs,
  unch m m' rs -> 0 <= a -> a + 4 * Z.of_nat (length l) <= M64 ->
  (forall r, In r rs -> a + 4 * Z.of_nat (length l) <= fst r \/ snd r <= a) ->
  arr32 m a l -> arr32 m' a l.
Proof.
  intros m m' a l rs Hu Ha Hb Hd H i Hi. apply (cellN_unch m m' _ 4 _ rs Hu); try lia.
  - intros r Hr. specialize (Hd r Hr). lia.
  - apply H, Hi.
Qed.

(* [comment removed for export] *)
Lemma wbytes_app : forall bs1 bs2 m (a : word),
  wbytes m a (bs1 ++ bs2) = wbytes (wbytes m a bs1) (Z_to_bv 64 (bv_unsigned a + Z.of_nat (length bs1))) bs2.
Proof.
  induction bs1 as [|b t IH]; intros bs2 m a.
  - cbn [app wbytes length]. rewrite Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity.
  - cbn [app wbytes length]. rewrite IH. f_equal. apply Z2bv_eqm.
    rewrite bv_add_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64).
    change (bv_unsigned (1%bv : word)) with 1.
    rewrite M64_eq, Zplus_mod_idemp_l. f_equal. lia.
Qed.

(* [comment removed for export] *)
Lemma bn_ctor_store : forall m o, 0 <= o -> o + 4 <= M64 ->
  let m' := wbytes m (Z_to_bv 64 o) (word_to_le_bytes 4 (Z_to_bv 64 0)) in
  cellN m' o 2 0 /\ cellN m' (o + 2) 2 0.
Proof.
  intros m o Ho Hb. cbn zeta.
  change (word_to_le_bytes 4 (Z_to_bv 64 0)) with (word_to_le_bytes 2 (Z_to_bv 64 0) ++ word_to_le_bytes 2 (Z_to_bv 64 0)).
  rewrite wbytes_app, length_N_to_le_bytes, u_lit by (lia).
  replace (o + Z.of_nat 2) with (o + 2) by lia. split.
  - apply (proj2 (cellN_store_other _ o 2 0 (o + 2) 2 _ ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia))).
    apply (cellN_store_same m o 2 (Z_to_bv 64 0)); lia.
  - apply (cellN_store_same _ (o + 2) 2 (Z_to_bv 64 0)); lia.
Qed.

End WithSegs.
End BM.
