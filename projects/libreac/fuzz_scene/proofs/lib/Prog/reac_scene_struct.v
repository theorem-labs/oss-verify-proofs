From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Lib Require Import PropExec MState Mem Cells Step.
From OSSVerify.Proofs.libreac.fuzz_scene.lib Require Import Img0.
Import ListNotations.
Open Scope Z_scope.

Definition REAC_SCENE_BYTES : Z := 8904.

Definition scene_ok (body n mac : word) : bool :=
  (bv_unsigned n =? REAC_SCENE_BYTES) && negb (bv_unsigned body =? 0) && negb (bv_unsigned mac =? 0).

Definition zb : byte := Z_to_bv 8 0.

Definition scene0 (macb : list byte) : list byte :=
  [Z_to_bv 8 0x31; Z_to_bv 8 0x32; Z_to_bv 8 0x33; Z_to_bv 8 0x34]
  ++ repeat zb 828 ++ macb ++ repeat zb 34
  ++ [Z_to_bv 8 0x53; Z_to_bv 8 0x59; Z_to_bv 8 0x53; Z_to_bv 8 0x50]
  ++ repeat zb 16
  ++ [Z_to_bv 8 0x53; Z_to_bv 8 0x43; Z_to_bv 8 0x45; Z_to_bv 8 0x4e]
  ++ repeat zb 8008.

Lemma scene_ok_true : forall b n mac, scene_ok b n mac = true ->
  bv_unsigned n = 8904 /\ bv_unsigned b <> 0 /\ bv_unsigned mac <> 0.
Proof.
  intros b n mac. unfold scene_ok, REAC_SCENE_BYTES.
  destruct (Z.eqb_spec (bv_unsigned n) 8904); destruct (Z.eqb_spec (bv_unsigned b) 0);
    destruct (Z.eqb_spec (bv_unsigned mac) 0); cbn; intro H; try discriminate; tauto.
Qed.

Lemma scene_ok_false : forall b n mac, scene_ok b n mac = false ->
  bv_unsigned n <> 8904 \/ bv_unsigned b = 0 \/ bv_unsigned mac = 0.
Proof.
  intros b n mac. unfold scene_ok, REAC_SCENE_BYTES.
  destruct (Z.eqb_spec (bv_unsigned n) 8904); destruct (Z.eqb_spec (bv_unsigned b) 0);
    destruct (Z.eqb_spec (bv_unsigned mac) 0); cbn; intro H; try discriminate; tauto.
Qed.

Definition scene_tail_cells : list cell :=
  [CB 34 (repeat zb 34); CB 1 [zb]; CB 1 [zb]; CB 1 [zb]; CB 1 [zb]; CB 16 (repeat zb 16);
   CB 1 [zb]; CB 1 [zb]; CB 1 [zb]; CB 1 [zb]; CB 8008 (repeat zb 8008)].

Definition scene_mid_cells : list cell := [CB 828 (repeat zb 828); CB 6 (repeat zb 6)] ++ scene_tail_cells.

Lemma scene_mid_bytes : cells_bytes scene_mid_cells = repeat zb 8900.
Proof. vm_compute. reflexivity. Qed.

Lemma scene_mid_wf : cells_wf scene_mid_cells.
Proof. vm_compute. repeat split. Qed.

Lemma rw_cells_split2 : forall m A B cs1 cs2,
  rw_cells rsegs m A (cs1 ++ cs2) -> B = A + Z.of_nat (cells_size cs1) ->
  rw_cells rsegs m A cs1 /\ rw_cells rsegs m B cs2.
Proof.
  intros m A B cs1 cs2 [[Hwf Hb] (Ha & Hn & Hw)] ->.
  apply cells_wf_app in Hwf. destruct Hwf as [W1 W2].
  rewrite cells_bytes_app in Hb. apply bytes_at_app in Hb. destruct Hb as [B1 B2].
  rewrite cells_size_app in Hn, Hw.
  split.
  - split; [split; assumption|]. split; [lia|]. split; [lia|]. intros i Hi. apply Hw. lia.
  - split; [split; [assumption|]|].
    + rewrite cells_bytes_length in B2 by assumption. exact B2.
    + split; [lia|]. split; [lia|]. intros i Hi.
      replace (A + Z.of_nat (cells_size cs1) + i) with (A + (Z.of_nat (cells_size cs1) + i)) by lia.
      apply Hw. lia.
Qed.

Lemma rw_cells_join2 : forall m A B cs1 cs2,
  rw_cells rsegs m A cs1 -> B = A + Z.of_nat (cells_size cs1) -> rw_cells rsegs m B cs2 ->
  rw_cells rsegs m A (cs1 ++ cs2).
Proof.
  intros m A B cs1 cs2 [[W1 B1] (Ha & Hn & Hw1)] -> [[W2 B2] (Hb & Hn2 & Hw2)].
  split; [split|].
  - apply cells_wf_app. tauto.
  - rewrite cells_bytes_app. apply bytes_at_app. split; [exact B1|].
    rewrite cells_bytes_length by exact W1. exact B2.
  - rewrite cells_size_app. split; [lia|]. split; [lia|]. intros i Hi.
    destruct (Z.ltb_spec i (Z.of_nat (cells_size cs1))).
    + apply Hw1. lia.
    + replace (A + i) with (A + Z.of_nat (cells_size cs1) + (i - Z.of_nat (cells_size cs1))) by lia.
      apply Hw2. lia.
Qed.

Lemma rw_cells_rebytes : forall m A cs cs',
  rw_cells rsegs m A cs -> cells_wf cs' -> cells_bytes cs' = cells_bytes cs -> rw_cells rsegs m A cs'.
Proof.
  intros m A cs cs' [[Hwf Hb] Hw] Hwf' Heq. split; [split; [exact Hwf' | rewrite Heq; exact Hb] |].
  rewrite <- (cells_bytes_length cs') by assumption. rewrite Heq. rewrite cells_bytes_length by assumption. exact Hw.
Qed.

Lemma cells_bytes_map_C1 : forall l, cells_bytes (map C1 l) = l.
Proof. induction l as [|x l IH]; cbn; [reflexivity|]. rewrite IH. reflexivity. Qed.

Lemma cells_wf_map_C1 : forall l, cells_wf (map C1 l).
Proof. induction l as [|x l IH]; cbn; [exact I|]. split; [exact I|exact IH]. Qed.

Lemma rw_cells_C1 : forall m A cs, rw_cells rsegs m A cs -> rw_cells rsegs m A (map C1 (cells_bytes cs)).
Proof.
  intros m A cs H. eapply rw_cells_rebytes; [exact H | apply cells_wf_map_C1 | apply cells_bytes_map_C1].
Qed.

Lemma bytes_at_slice : forall m A l k n, bytes_at rsegs m A l -> (k + n <= length l)%nat ->
  bytes_at rsegs m (A + Z.of_nat k) (firstn n (skipn k l)).
Proof.
  intros m A l k n H Hk.
  rewrite <- (CB3_bytes k n l Hk) in H.
  apply bytes_at_app in H. destruct H as [_ H]. apply bytes_at_app in H. destruct H as [H _].
  rewrite length_firstn in H. replace (Nat.min k (length l)) with k in H by lia. exact H.
Qed.
