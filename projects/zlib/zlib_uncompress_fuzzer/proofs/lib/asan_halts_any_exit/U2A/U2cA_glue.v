(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_halts_any_exit.Lib Require Import PropExec MState Mem Cells Step Frame Arr Bytes ZBridge Tac InitMem SysStep.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_halts_any_exit.zspec.zmodel Require Import ZIface InflateState InflateInv.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_halts_any_exit.IK Require Import IDefs.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_halts_any_exit.U2A Require Import U2AArr U2AObj U2ABlob InfPure.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Definition chunkZ (k : nat) (bs : list byte) (z : Z) : Z := bytes_le_to_Z (firstn k (skipn (k * Z.to_nat z) bs)).

Lemma chunkZ_range : forall k bs z, 0 <= chunkZ k bs z < 2 ^ (8 * Z.of_nat k).
Proof.
  intros k bs z. unfold chunkZ. split; [apply bytes_le_to_Z_nonneg|].
  eapply Z.lt_le_trans; [apply bytes_le_to_Z_bound|]. apply Z.pow_le_mono_r; [lia|]. rewrite length_firstn. lia.
Qed.

Lemma chunkZ_cons : forall k pre bs z, length pre = k -> 0 <= z -> chunkZ k (pre ++ bs) (z + 1) = chunkZ k bs z.
Proof.
  intros k pre bs z HL Hz. unfold chunkZ. f_equal. f_equal.
  replace (Z.to_nat (z + 1)) with (S (Z.to_nat z)) by lia. rewrite Nat.mul_succ_r.
  rewrite <- skipn_skipn. f_equal. rewrite skipn_app, HL, Nat.sub_diag, skipn_all2 by lia. reflexivity.
Qed.

Lemma u16s_chunks : forall n bs, length bs = (2 * n)%nat -> u16s (fws (chunkZ 2 bs) n) = bs.
Proof.
  induction n as [|n IH]; intros bs HL.
  - destruct bs; [reflexivity| discriminate].
  - destruct bs as [|b0 [|b1 rest]]; try (cbn in HL; lia).
    assert (HR : length rest = (2 * n)%nat) by (cbn in HL; lia).
    unfold fws. rewrite <- cons_seq. cbn [map u16s]. rewrite <- seq_shift, map_map.
    change (b0 :: b1 :: rest) with ([b0; b1] ++ rest) at 3. f_equal.
    + change (chunkZ 2 (b0 :: b1 :: rest) (Z.of_nat 0)) with (bytes_le_to_Z [b0; b1]).
      unfold le2. change (Z_to_bv 64 (bytes_le_to_Z [b0; b1])) with (le_bytes_to_word [b0; b1]). apply lek_of_bytes; [reflexivity| lia].
    + transitivity (u16s (fws (chunkZ 2 rest) n)); [| exact (IH rest HR)]. unfold fws. f_equal. apply map_ext. intros i. f_equal.
      rewrite Nat2Z.inj_succ. unfold Z.succ.
      exact (chunkZ_cons 2 [b0; b1] rest (Z.of_nat i) eq_refl ltac:(lia)).
Qed.

Lemma u32s_chunks : forall n bs, length bs = (4 * n)%nat -> u32s (fws (chunkZ 4 bs) n) = bs.
Proof.
  induction n as [|n IH]; intros bs HL.
  - destruct bs; [reflexivity| discriminate].
  - destruct bs as [|b0 [|b1 [|b2 [|b3 rest]]]]; try (cbn in HL; lia).
    assert (HR : length rest = (4 * n)%nat) by (cbn in HL; lia).
    unfold fws. rewrite <- cons_seq. cbn [map u32s]. rewrite <- seq_shift, map_map.
    change (b0 :: b1 :: b2 :: b3 :: rest) with ([b0; b1; b2; b3] ++ rest) at 3. f_equal.
    + change (chunkZ 4 (b0 :: b1 :: b2 :: b3 :: rest) (Z.of_nat 0)) with (bytes_le_to_Z [b0; b1; b2; b3]).
      unfold le4. change (Z_to_bv 64 (bytes_le_to_Z [b0; b1; b2; b3])) with (le_bytes_to_word [b0; b1; b2; b3]). apply lek_of_bytes; [reflexivity| lia].
    + transitivity (u32s (fws (chunkZ 4 rest) n)); [| exact (IH rest HR)]. unfold fws. f_equal. apply map_ext. intros i. f_equal.
      rewrite Nat2Z.inj_succ. unfold Z.succ.
      exact (chunkZ_cons 4 [b0; b1; b2; b3] rest (Z.of_nat i) eq_refl ltac:(lia)).
Qed.

Lemma u8_chunks : forall n bs, length bs = n -> map (fun i => Z_to_bv 8 (chunkZ 1 bs (Z.of_nat i))) (seq 0 n) = bs.
Proof.
  induction n as [|n IH]; intros bs HL.
  - destruct bs; [reflexivity| discriminate].
  - destruct bs as [|b0 rest]; [discriminate|].
    assert (HR : length rest = n) by (cbn in HL; lia).
    rewrite <- cons_seq. cbn [map]. rewrite <- seq_shift, map_map. f_equal.
    + change (chunkZ 1 (b0 :: rest) (Z.of_nat 0)) with (bytes_le_to_Z [b0]). cbn [bytes_le_to_Z]. rewrite Z.shiftl_0_l, Z.lor_0_r.
      apply stdpp.bitvector.definitions.Z_to_bv_bv_unsigned.
    + transitivity (map (fun i => Z_to_bv 8 (chunkZ 1 rest (Z.of_nat i))) (seq 0 n)); [| exact (IH rest HR)].
      apply map_ext. intros i. f_equal. rewrite Nat2Z.inj_succ. unfold Z.succ.
      exact (chunkZ_cons 1 [b0] rest (Z.of_nat i) eq_refl ltac:(lia)).
Qed.

Section Views.
Variable segs : list Segment.

Lemma f16arr_of_blob : forall m A n bs, rw_cells segs m A [CB (2 * n) bs] ->
  exists f, f16arr segs m A n f /\ forall i, 0 <= f i < 65536.
Proof.
  intros m A n bs [[Hwf Hb] Hw]. cbn in Hwf. destruct Hwf as [HL _].
  cbn [cells_bytes cbytes] in Hb. rewrite app_nil_r in Hb. cbn [cells_size csize] in Hw. rewrite Nat.add_0_r in Hw.
  exists (chunkZ 2 bs). split; [| intros i; exact (chunkZ_range 2 bs i)].
  unfold f16arr, u16arr. rewrite (u16s_chunks n bs HL), fws_length. split; [exact Hb|].
  replace (2 * Z.of_nat n) with (Z.of_nat (2 * n)) by lia. exact Hw.
Qed.

Lemma f32arr_of_blob : forall m A n bs, rw_cells segs m A [CB (4 * n) bs] ->
  exists f, f32arr segs m A n f /\ forall i, 0 <= f i < 4294967296.
Proof.
  intros m A n bs [[Hwf Hb] Hw]. cbn in Hwf. destruct Hwf as [HL _].
  cbn [cells_bytes cbytes] in Hb. rewrite app_nil_r in Hb. cbn [cells_size csize] in Hw. rewrite Nat.add_0_r in Hw.
  exists (chunkZ 4 bs). split; [| intros i; exact (chunkZ_range 4 bs i)].
  unfold f32arr, u32arr. rewrite (u32s_chunks n bs HL), fws_length. split; [exact Hb|].
  replace (4 * Z.of_nat n) with (Z.of_nat (4 * n)) by lia. exact Hw.
Qed.

Lemma f8arr_of_blob : forall m A n bs, rw_cells segs m A [CB n bs] ->
  exists f, f8arr segs m A n f /\ forall i, 0 <= f i < 256.
Proof.
  intros m A n bs [[Hwf Hb] Hw]. cbn in Hwf. destruct Hwf as [HL _].
  cbn [cells_bytes cbytes] in Hb. rewrite app_nil_r in Hb. cbn [cells_size csize] in Hw. rewrite Nat.add_0_r in Hw.
  exists (chunkZ 1 bs). split; [| intros i; exact (chunkZ_range 1 bs i)].
  unfold f8arr, u8arr. rewrite (u8_chunks n bs HL). split; [exact Hb|]. rewrite HL. exact Hw.
Qed.

Lemma le4_norm : forall w : word, le4 (Z_to_bv 64 (bv_unsigned w mod 4294967296)) = le4 w.
Proof.
  intros w. unfold le4. pose proof (bv_unsigned_in_range 64 w) as R. unfold bv_modulus in R. change (2 ^ Z.of_N 64) with (2^64) in R.
  pose proof (Z.mod_pos_bound (bv_unsigned w) 4294967296 ltac:(lia)) as B.
  rewrite unsigned_lit by lia. change 4294967296 with (2 ^ 32). apply (Z_to_le_bytes_mod 4 (bv_unsigned w) 32). lia.
Qed.
End Views.

Definition st_u2_init (vlen vofs vext vlb vdb vnc vnl vnd vsh : Z) : ist :=
  IST HEAD 0 (-1) 0 0 0 0 262144 0 vlen vofs vext (CDyn 0) (CDyn 0) vlb vdb vnc vnl vnd vsh 0 0 0.

Lemma ainv_u2_init : forall S D n OB W0 (lf cf : Z -> Z) vlen vofs vext vlb vdb vnc vnl vnd vsh,
  0 <= n ->
  (forall i, 0 <= lf i < 65536) -> (forall i, 0 <= cf i < 4294967296) ->
  0 <= vlen < 4294967296 -> 0 <= vofs < 4294967296 -> 0 <= vext < 4294967296 -> 0 <= vlb < 4294967296 -> 0 <= vdb < 4294967296 ->
  0 <= vnc < 4294967296 -> 0 <= vnl < 4294967296 -> 0 <= vnd < 4294967296 -> 0 <= vsh < 4294967296 ->
  ainv (icx_of S D n OB 262144 0 0 0 W0) (st_u2_init vlen vofs vext vlb vdb vnc vnl vnd vsh) lf cf.
Proof.
  intros S D n OB W0 lf cf vlen vofs vext vlb vdb vnc vnl vnd vsh Hn Hlf Hcf R1 R2 R3 R4 R5 R6 R7 R8 R9.
  unfold ainv, RNG, WIN, MODE, st_u2_init, icx_of; icx_cbn. cbv [N_CODES N_LENS WIN_SIZE].
  split; [| split].
  - split_conj; first [assumption | lia_std | change (2 ^ 0) with 1; lia_std | intros i _; apply Hlf | intros i _; apply Hcf].
  - split; [intros _; split; reflexivity | intros C; exfalso; exact (C eq_refl)].
  - split_conj.
    + left. reflexivity.
    + intros _. split; [left; reflexivity | reflexivity].
    + intros E. exfalso. revert E. cbv. discriminate.
    + intros E. exfalso. revert E. cbv. discriminate.
    + intros E. exfalso. revert E. unfold codes_liveP. cbv [LEN_ LIT HEAD]. lia_std.
    + intros E. exfalso. revert E. cbv. discriminate.
    + intros E. exfalso. revert E. cbv. discriminate.
    + intros E. exfalso. revert E. cbv. discriminate.
    + intros E. exfalso. revert E. cbv. discriminate.
    + intros [E|E]; exfalso; revert E; cbv; discriminate.
Qed.

Lemma ainv_rebase : forall cx st lf cf W' K,
  ainv cx st lf cf -> ainv (rebase cx (t_cin st) (t_cout st) W' K) st lf cf.
Proof.
  intros cx st lf cf W' K (R & Wn & Mo). destruct cx, st.
  unfold ainv, RNG, WIN, MODE, tables_live, ctable_live, rebase in *. icx_cbn.
  split; [| split; [exact Wn | exact Mo]]. destr_conj R. split_conj; try assumption; lia_std.
Qed.

Lemma M2_nonneg : forall cx st lf cf, ainv cx st lf cf -> 0 <= Wm cx st * 134217728 + (c_n cx - t_cin st).
Proof. intros cx st lf cf (R & _ & _). destruct cx, st. unfold RNG, Wm in *. icx_cbn. destr_conj R. lia_std. Qed.

Lemma mode_range : forall cx st lf cf, ainv cx st lf cf -> 16180 <= t_mode st <= 16211.
Proof.
  intros cx st lf cf (_ & _ & Mo). destruct Mo as [Re _]. revert Re. generalize (t_mode st). intros md Re.
  unfold reach in Re. mode_consts. lia.
Qed.
