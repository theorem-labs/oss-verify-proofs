(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.Lib Require Import PropExec MState Mem Cells Step Frame Arr Bytes ZBridge Tac InitMem SysStep.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Lemma zx32_small : forall e, 0 <= e < 4294967296 -> zx32 (Z_to_bv 64 e) = Z_to_bv 64 e.
Proof. intros e H. unfold zx32. rewrite unsigned_lit by lia. change (2^32) with 4294967296. rewrite Z.mod_small by lia. reflexivity. Qed.

Lemma sepI : forall a n b k, (a + n <= b \/ b + k <= a) ->
  0 <= a -> a + n <= 2^47 -> 0 <= b -> b + k <= 2^47 ->
  exists c : Z, 0 <= c <= 1 /\ a + n <= b + c * 2^48 /\ b + k <= a + (1 - c) * 2^48.
Proof. intros a n b k [H|H] ? ? ? ?; [exists 0| exists 1]; lia. Qed.

Section Blob.
Variable segs : list Segment.

Lemma rw_CB_sub : forall m A n bs k j,
  rw_cells segs m A [CB n bs] -> (k + j <= n)%nat ->
  rw_cells segs m (A + Z.of_nat k) [CB j (firstn j (skipn k bs))].
Proof.
  intros m A n bs k j [[Hwf Hb] Hw] Hk. cbn in Hwf. destruct Hwf as [Hl _].
  cbn [cells_bytes cbytes] in Hb. rewrite app_nil_r in Hb. cbn [cells_size csize] in Hw. rewrite Nat.add_0_r in Hw.
  split; [split|].
  - cbn. split; [| exact I]. rewrite firstn_length, skipn_length. lia.
  - cbn [cells_bytes cbytes]. rewrite app_nil_r.
    rewrite <- (firstn_skipn k bs) in Hb. apply bytes_at_app in Hb. destruct Hb as [_ Hb].
    rewrite firstn_length in Hb. replace (Nat.min k (length bs)) with k in Hb by lia.
    rewrite <- (firstn_skipn j (skipn k bs)) in Hb. apply bytes_at_app in Hb. destruct Hb as [Hb _]. exact Hb.
  - cbn [cells_size csize]. rewrite Nat.add_0_r. destruct Hw as (H0 & H1 & H). split; [lia|]. split; [lia|].
    intros i Hi. replace (A + Z.of_nat k + i) with (A + (Z.of_nat k + i)) by lia. apply H. lia.
Qed.

Lemma rw_CB_join3 : forall m A k j l b1 b2 b3,
  rw_cells segs m A [CB k b1] -> rw_cells segs m (A + Z.of_nat k) [CB j b2] -> rw_cells segs m (A + Z.of_nat k + Z.of_nat j) [CB l b3] ->
  rw_cells segs m A [CB (k + j + l) (b1 ++ b2 ++ b3)].
Proof.
  intros m A k j l b1 b2 b3 [[W1 B1] R1] [[W2 B2] R2] [[W3 B3] R3].
  cbn in W1, W2, W3. destruct W1 as [L1 _]. destruct W2 as [L2 _]. destruct W3 as [L3 _].
  cbn [cells_bytes cbytes] in B1, B2, B3. rewrite app_nil_r in B1, B2, B3.
  cbn [cells_size csize] in R1, R2, R3. rewrite Nat.add_0_r in R1, R2, R3.
  split; [split|].
  - cbn. split; [| exact I]. rewrite !app_length. lia.
  - cbn [cells_bytes cbytes]. rewrite app_nil_r. apply bytes_at_app. split; [exact B1|].
    rewrite L1. apply bytes_at_app. split; [exact B2|]. rewrite L2. exact B3.
  - cbn [cells_size csize]. rewrite Nat.add_0_r.
    destruct R1 as (A0 & A1 & H1). destruct R2 as (_ & A2 & H2). destruct R3 as (_ & A3 & H3).
    split; [lia|]. split; [lia|]. intros i Hi.
    destruct (Z_lt_ge_dec i (Z.of_nat k)) as [C1|C1]; [apply H1; lia|].
    destruct (Z_lt_ge_dec i (Z.of_nat k + Z.of_nat j)) as [C2|C2].
    + replace (A + i) with (A + Z.of_nat k + (i - Z.of_nat k)) by lia. apply H2. lia.
    + replace (A + i) with (A + Z.of_nat k + Z.of_nat j + (i - Z.of_nat k - Z.of_nat j)) by lia. apply H3. lia.
Qed.

Lemma blob_bytes_at : forall m A n bs k j,
  rw_cells segs m A [CB n bs] -> (k + j <= n)%nat ->
  bytes_at segs m (A + Z.of_nat k) (firstn j (skipn k bs)) /\ length (firstn j (skipn k bs)) = j.
Proof.
  intros m A n bs k j H Hk. pose proof (rw_CB_sub m A n bs k j H Hk) as [[Hwf Hb] _].
  cbn in Hwf. destruct Hwf as [Hl _]. cbn [cells_bytes cbytes] in Hb. rewrite app_nil_r in Hb. split; [exact Hb| exact Hl].
Qed.

Lemma blob_split3 : forall m A N bs k j,
  rw_cells segs m A [CB (Z.to_nat N) bs] -> 0 <= k -> 0 <= j -> k + j <= N ->
  exists b1 b2 b3, rw_cells segs m A [CB (Z.to_nat k) b1] /\ rw_cells segs m (A + k) [CB (Z.to_nat j) b2]
                   /\ rw_cells segs m (A + k + j) [CB (Z.to_nat (N - k - j)) b3].
Proof.
  intros m A N bs k j H K0 J0 KJ.
  exists (firstn (Z.to_nat k) (skipn 0 bs)), (firstn (Z.to_nat j) (skipn (Z.to_nat k) bs)),
         (firstn (Z.to_nat (N - k - j)) (skipn (Z.to_nat (k + j)) bs)).
  split; [| split].
  - pose proof (rw_CB_sub m A _ bs 0 (Z.to_nat k) H ltac:(lia)) as X. change (Z.of_nat 0) with 0 in X. rewrite Z.add_0_r in X. exact X.
  - pose proof (rw_CB_sub m A _ bs (Z.to_nat k) (Z.to_nat j) H ltac:(lia)) as X. rewrite Z2Nat.id in X by lia. exact X.
  - pose proof (rw_CB_sub m A _ bs (Z.to_nat (k + j)) (Z.to_nat (N - k - j)) H ltac:(lia)) as X. rewrite Z2Nat.id in X by lia.
    replace (A + (k + j)) with (A + k + j) in X by lia. exact X.
Qed.

Lemma blob_join3 : forall m A N k j b1 b2 b3,
  0 <= k -> 0 <= j -> k + j <= N ->
  rw_cells segs m A [CB (Z.to_nat k) b1] -> rw_cells segs m (A + k) [CB (Z.to_nat j) b2] ->
  rw_cells segs m (A + k + j) [CB (Z.to_nat (N - k - j)) b3] ->
  rw_cells segs m A [CB (Z.to_nat N) (b1 ++ b2 ++ b3)].
Proof.
  intros m A N k j b1 b2 b3 K0 J0 KJ H1 H2 H3.
  pose proof (rw_CB_join3 m A (Z.to_nat k) (Z.to_nat j) (Z.to_nat (N - k - j)) b1 b2 b3 H1) as X.
  rewrite !Z2Nat.id in X by lia. specialize (X H2 H3).
  replace (Z.to_nat k + Z.to_nat j + Z.to_nat (N - k - j))%nat with (Z.to_nat N) in X by lia. exact X.
Qed.

Lemma blob_src : forall m A N bs k j,
  rw_cells segs m A [CB (Z.to_nat N) bs] -> 0 <= k -> 0 <= j -> k + j <= N ->
  exists src, bytes_at segs m (A + k) src /\ length src = Z.to_nat j.
Proof.
  intros m A N bs k j H K0 J0 KJ.
  destruct (blob_bytes_at m A _ bs (Z.to_nat k) (Z.to_nat j) H ltac:(lia)) as [B L].
  rewrite Z2Nat.id in B by lia. eexists. split; [exact B| exact L].
Qed.
End Blob.
