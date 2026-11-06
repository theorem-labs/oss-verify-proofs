(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import Tac.
Import ListNotations.
Open Scope Z_scope.

Section WithSegs.
Variable segs : list Segment.

#[using="Type"] Lemma rw_cells_reshape : forall m A cs cs',
  rw_cells segs m A cs -> cells_wf cs' -> cells_bytes cs' = cells_bytes cs -> rw_cells segs m A cs'.
Proof.
  intros m A cs cs' [[Hwf Hb] Hw] Hwf' E. split; [split; [exact Hwf'|]|].
  - rewrite E. exact Hb.
  - rewrite <- (cells_bytes_length cs') by exact Hwf'. rewrite E. rewrite cells_bytes_length by exact Hwf. exact Hw.
Qed.

#[using="Type"] Lemma ro_cells_reshape : forall m A cs cs',
  ro_cells segs m A cs -> cells_wf cs' -> cells_bytes cs' = cells_bytes cs -> ro_cells segs m A cs'.
Proof.
  intros m A cs cs' [Hwf Hb] Hwf' E. split; [exact Hwf'|]. rewrite E. exact Hb.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma Z_to_le_bytes_app : forall n1 n2 z,
  Z_to_le_bytes (n1 + n2) z = Z_to_le_bytes n1 z ++ Z_to_le_bytes n2 (z / 2 ^ (8 * Z.of_nat n1)).
Proof.
  induction n1 as [|n1 IH]; intros n2 z; cbn [Z_to_le_bytes Nat.add app].
  - rewrite Z.mul_0_r, Z.pow_0_r, Z.div_1_r. reflexivity.
  - f_equal. rewrite IH. f_equal. f_equal.
    rewrite Z.shiftr_div_pow2 by lia. rewrite Z.div_div by lia.
    f_equal. rewrite <- Z.pow_add_r by lia. f_equal. lia.
Qed.

#[using="Type"] Lemma le4_split : forall v : word,
  le4 v = le2 v ++ le2 (Z_to_bv 64 (bv_unsigned v / 2^16)).
Proof.
  intros v. unfold le4, le2. change 4%nat with (2 + 2)%nat. rewrite Z_to_le_bytes_app.
  f_equal. rewrite Z_to_bv_unsigned. unfold bv_wrap.
  pose proof (bv_unsigned_in_range 64 v) as R.
  change (8 * Z.of_nat 2) with 16. unfold bv_modulus in *. change (Z.of_N 64) with 64 in *.
  rewrite Z.mod_small; [reflexivity|].
  split; [apply Z.div_pos; lia|]. apply Z.div_lt_upper_bound; [lia|]. lia.
Qed.

#[using="Type"] Lemma le8_split4 : forall v : word,
  le8 v = le4 v ++ le4 (Z_to_bv 64 (bv_unsigned v / 2^32)).
Proof.
  intros v. unfold le8, le4, word_to_le_bytes. change 8%nat with (4 + 4)%nat. rewrite Z_to_le_bytes_app.
  f_equal. change (8 * Z.of_nat 4) with 32. rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. change (Z.of_N 64) with 64.
  pose proof (bv_unsigned_in_range 64 v) as R. unfold bv_modulus in R. change (Z.of_N 64) with 64 in R.
  rewrite Z.mod_small; [reflexivity|].
  split; [apply Z.div_pos; lia|]. apply Z.div_lt_upper_bound; [lia|]. lia.
Qed.

#[using="Type"] Lemma rw_cells_split_C4 : forall m A pre v post,
  rw_cells segs m A (pre ++ C4 v :: post) ->
  rw_cells segs m A (pre ++ C2 v :: C2 (Z_to_bv 64 (bv_unsigned v / 2^16)) :: post).
Proof.
  intros m A pre v post H. eapply rw_cells_reshape; [exact H| |].
  - destruct H as [[Hwf _] _]. apply cells_wf_app in Hwf. destruct Hwf as [H1 [_ H3]].
    apply cells_wf_app. split; [exact H1|]. cbn. auto.
  - rewrite !cells_bytes_app. cbn [cells_bytes cbytes]. rewrite le4_split. rewrite <- app_assoc. reflexivity.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma Z_to_bv8_mod : forall z k, 0 <= k -> Z_to_bv 8 (z mod 2 ^ (8 + k)) = Z_to_bv 8 z.
Proof.
  intros z k Hk. apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. change (Z.of_N 8) with 8.
  rewrite Z.pow_add_r by lia. rewrite Z.rem_mul_r by lia.
  rewrite Z.mul_comm, Z.mod_add by lia. apply Z.mod_mod. lia.
Qed.

#[using="Type"] Lemma Z_to_le_bytes_mod : forall n z, Z_to_le_bytes n (z mod 2 ^ (8 * Z.of_nat n)) = Z_to_le_bytes n z.
Proof.
  induction n as [|n IH]; intros z; cbn [Z_to_le_bytes]; [reflexivity|].
  replace (8 * Z.of_nat (S n)) with (8 + 8 * Z.of_nat n) by lia.
  f_equal.
  - apply Z_to_bv8_mod. lia.
  - rewrite <- (IH (Z.shiftr z 8)). f_equal.
    rewrite !Z.shiftr_div_pow2 by lia.
    rewrite Z.pow_add_r by lia.
    rewrite Z.rem_mul_r by lia.
    rewrite Z.add_comm, Z.mul_comm, Z.div_add_l by lia. rewrite (Z.div_small (z mod 2^8) (2^8)) by (apply Z.mod_pos_bound; lia). lia.
Qed.

#[using="Type"] Lemma le2_of_Z : forall z, le2 (Z_to_bv 64 z) = Z_to_le_bytes 2 z.
Proof.
  intros z0. unfold le2. rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. change (Z.of_N 64) with 64.
  rewrite <- (Z_to_le_bytes_mod 2 z0). rewrite <- (Z_to_le_bytes_mod 2 (z0 mod 2 ^ 64)).
  f_equal. change (8 * Z.of_nat 2) with 16. change (2 ^ 64) with (2^16 * 2^48).
  rewrite Z.rem_mul_r by lia. rewrite (Z.mul_comm (2^16) _). rewrite Z.mod_add by lia. apply Z.mod_mod; lia.
Qed.

#[using="Type"] Lemma rw_cells_join_C2C2 : forall m A pre (v w : word) post,
  rw_cells segs m A (pre ++ C2 v :: C2 w :: post) ->
  rw_cells segs m A (pre ++ C4 (Z_to_bv 64 (bv_unsigned v mod 2^16 + 2^16 * bv_unsigned w)) :: post).
Proof.
  intros m A pre v w post H. eapply rw_cells_reshape; [exact H| |].
  - destruct H as [[Hwf _] _]. apply cells_wf_app in Hwf. destruct Hwf as [H1 [_ [_ H3]]].
    apply cells_wf_app. split; [exact H1|]. cbn. auto.
  - rewrite !cells_bytes_app. cbn [cells_bytes cbytes]. rewrite le4_split. rewrite <- app_assoc. cbn [app].
    set (z := bv_unsigned v mod 2 ^ 16 + 2 ^ 16 * bv_unsigned w).
    f_equal. f_equal; [|f_equal].
    + rewrite le2_of_Z. unfold le2. rewrite <- (Z_to_le_bytes_mod 2 z), <- (Z_to_le_bytes_mod 2 (bv_unsigned v)).
      f_equal. change (8 * Z.of_nat 2) with 16. subst z. rewrite (Z.mul_comm (2^16) _), Z.mod_add by lia. apply Z.mod_mod; lia.
    + pose proof (bv_unsigned_in_range 64 v) as Rv. pose proof (bv_unsigned_in_range 64 w) as Rw.
      unfold bv_modulus in Rv, Rw. change (2 ^ Z.of_N 64) with (2^64) in Rv, Rw.
      rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 64) with (2^16 * 2^48).
      rewrite le2_of_Z. unfold le2. rewrite <- (Z_to_le_bytes_mod 2), <- (Z_to_le_bytes_mod 2 (bv_unsigned w)). f_equal. change (8 * Z.of_nat 2) with 16.
      assert (HA : 0 <= z mod 2^16 < 2^16) by (apply Z.mod_pos_bound; lia).
      rewrite Z.rem_mul_r by lia.
      set (B := (z / 2 ^ 16) mod 2 ^ 48).
      assert (HB : 0 <= B < 2^48) by (apply Z.mod_pos_bound; lia).
      replace ((z mod 2 ^ 16 + 2 ^ 16 * B) / 2 ^ 16) with B.
      2: { rewrite Z.add_comm, (Z.mul_comm (2^16) B), Z.div_add_l by lia. rewrite Z.div_small by lia. lia. }
      subst B z.
      rewrite (Z.mul_comm (2^16) (bv_unsigned w)). rewrite Z.div_add by lia.
      rewrite (Z.div_small (bv_unsigned v mod 2^16) (2^16)) by (apply Z.mod_pos_bound; lia). rewrite Z.add_0_l.
      change (2^48) with (2^16 * 2^32). rewrite Z.rem_mul_r by lia. rewrite (Z.mul_comm (2^16) _), Z.mod_add by lia. apply Z.mod_mod; lia.
Qed.

(* [comment removed for export] *)
Fixpoint zero_cells (cs : list cell) : Prop :=
  match cs with
  | [] => True
  | C8 v :: r => v = Z_to_bv 64 0 /\ zero_cells r
  | C4 v :: r => v = Z_to_bv 64 0 /\ zero_cells r
  | C2 v :: r => v = Z_to_bv 64 0 /\ zero_cells r
  | C1 b :: r => b = Z_to_bv 8 0 /\ zero_cells r
  | CB n bs :: r => bs = repeat (Z_to_bv 8 0) n /\ zero_cells r
  end.

#[using="Type"] Lemma zero_cells_bytes : forall cs, zero_cells cs -> cells_bytes cs = repeat (Z_to_bv 8 0) (cells_size cs).
Proof.
  induction cs as [|c cs IH]; intros H; [reflexivity|].
  cbn [cells_bytes cells_size]. rewrite repeat_app.
  destruct c; cbn in H; destruct H as [-> H]; rewrite (IH H); reflexivity.
Qed.

#[using="Type"] Lemma zero_cells_wf : forall cs, zero_cells cs -> cells_wf cs.
Proof.
  induction cs as [|c cs IH]; intros H; [exact I|].
  destruct c; cbn in H |- *; destruct H as [E H]; split; auto. subst. apply repeat_length.
Qed.

#[using="Type"] Lemma rw_cells_zeros : forall m A n cs,
  rw_cells segs m A [CB n (repeat (Z_to_bv 8 0) n)] -> zero_cells cs -> cells_size cs = n ->
  rw_cells segs m A cs.
Proof.
  intros m A n cs H Z E. eapply rw_cells_reshape; [exact H| apply zero_cells_wf; exact Z|].
  cbn [cells_bytes cbytes]. rewrite app_nil_r. rewrite zero_cells_bytes by exact Z. rewrite E. reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

#[using="Type"] Lemma wr_at_app : forall m A n1 n2,
  0 <= n1 -> 0 <= n2 ->
  wr_at segs m A (n1 + n2) <-> wr_at segs m A n1 /\ wr_at segs m (A + n1) n2.
Proof.
  intros m A n1 n2 H1 H2. unfold wr_at. split.
  - intros (Ha & Hl & H). repeat split; try lia.
    + intros i Hi. apply H. lia.
    + intros i Hi. replace (A + n1 + i) with (A + (n1 + i)) by lia. apply H. lia.
  - intros ((Ha & Hl & Hx) & (Ha' & Hl' & Hy)). repeat split; try lia.
    intros i Hi. destruct (Z_lt_le_dec i n1).
    + apply Hx. lia.
    + replace (A + i) with (A + n1 + (i - n1)) by lia. apply Hy. lia.
Qed.

#[using="Type"] Lemma rw_cells_app : forall m A cs1 cs2,
  rw_cells segs m A (cs1 ++ cs2) <->
  rw_cells segs m A cs1 /\ rw_cells segs m (A + Z.of_nat (cells_size cs1)) cs2.
Proof.
  intros m A cs1 cs2. unfold rw_cells, cells_at. rewrite cells_wf_app, cells_bytes_app, cells_size_app.
  rewrite Nat2Z.inj_add.
  split.
  - intros [[[W1 W2] HB] HW].
    rewrite bytes_at_app in HB. destruct HB as [B1 B2]. rewrite cells_bytes_length in B2 by exact W1.
    apply wr_at_app in HW; [|lia|lia]. destruct HW as [X1 X2].
    exact (conj (conj (conj W1 B1) X1) (conj (conj W2 B2) X2)).
  - intros [[[W1 B1] X1] [[W2 B2] X2]]. refine (conj (conj (conj W1 W2) _) _).
    + apply bytes_at_app. rewrite cells_bytes_length by exact W1. auto.
    + apply wr_at_app; [lia|lia|auto].
Qed.

#[using="Type"] Lemma rw_cells_split3 : forall m A pre mid post,
  rw_cells segs m A (pre ++ mid ++ post) ->
  rw_cells segs m A pre
  /\ rw_cells segs m (A + Z.of_nat (cells_size pre)) mid
  /\ rw_cells segs m (A + Z.of_nat (cells_size pre) + Z.of_nat (cells_size mid)) post.
Proof.
  intros m A pre mid post H. apply rw_cells_app in H. destruct H as [H1 H23].
  apply rw_cells_app in H23. destruct H23 as [H2 H3]. auto.
Qed.

#[using="Type"] Lemma rw_cells_join3 : forall m A pre mid post,
  rw_cells segs m A pre ->
  rw_cells segs m (A + Z.of_nat (cells_size pre)) mid ->
  rw_cells segs m (A + Z.of_nat (cells_size pre) + Z.of_nat (cells_size mid)) post ->
  rw_cells segs m A (pre ++ mid ++ post).
Proof.
  intros m A pre mid post H1 H2 H3. apply rw_cells_app. split; [exact H1|]. apply rw_cells_app. auto.
Qed.

End WithSegs.
