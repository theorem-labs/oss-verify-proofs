(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude.
From OSSVerify.Proofs.zstd.simple_decompress.lib.Lib Require Import Tac.
From OSSVerify.Proofs.zstd.simple_decompress.lib.Lib Require Import Bytes.
From OSSVerify.Proofs.zstd.simple_decompress.lib.Common Require Import StrFun WStr ZdWalkKit.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Lemma cb_carve : forall segs m A (n : nat) junk a k,
  rw_cells segs m A [CB n junk] -> 0 <= a -> 0 <= k -> a + k <= Z.of_nat n ->
  exists j1 j2 j3,
    rw_cells segs m A [CB (Z.to_nat a) j1] /\ rw_cells segs m (A + a) [CB (Z.to_nat k) j2]
    /\ rw_cells segs m (A + a + k) [CB (n - Z.to_nat a - Z.to_nat k) j3].
Proof.
  intros segs m A n junk a k H Ha Hk Hn.
  apply (rw_cells_split_CB segs m A [] n junk [] [Z.to_nat a; Z.to_nat k; (n - Z.to_nat a - Z.to_nat k)%nat]) in H;
    [| cbn [sum_nat]; lia].
  cbn [mk_CB_cells app] in H.
  apply (proj1 (rw_cells_app segs m A [CB (Z.to_nat a) _] _)) in H. destruct H as [H1 H]. cbn [cells_size csize Nat.add] in H.
  apply (proj1 (rw_cells_app segs m _ [CB (Z.to_nat k) _] _)) in H. destruct H as [H2 H3]. cbn [cells_size csize Nat.add] in H3.
  do 3 eexists. split; [exact H1|]. split.
  - replace (A + a) with (A + Z.of_nat (Z.to_nat a + 0)) by lia. exact H2.
  - replace (A + a + k) with (A + Z.of_nat (Z.to_nat a + 0) + Z.of_nat (Z.to_nat k + 0)) by lia. exact H3.
Qed.

Lemma cb_uncarve : forall segs m A (n : nat) a k (n1 n2 n3 : nat) j1 j2 j3,
  rw_cells segs m A [CB n1 j1] -> rw_cells segs m (A + a) [CB n2 j2] -> rw_cells segs m (A + a + k) [CB n3 j3] ->
  Z.of_nat n1 = a -> Z.of_nat n2 = k -> (n1 + n2 + n3 = n)%nat ->
  exists j, rw_cells segs m A [CB n j].
Proof.
  intros segs m A n a k n1 n2 n3 j1 j2 j3 H1 H2 H3 E1 E2 E3.
  assert (H : rw_cells segs m A ([CB n1 j1] ++ [CB n2 j2] ++ [CB n3 j3])).
  { apply (proj2 (rw_cells_app segs m A _ _)). split; [exact H1|]. cbn [cells_size csize Nat.add].
    apply (proj2 (rw_cells_app segs m _ _ _)). split.
    - replace (A + Z.of_nat (n1 + 0)) with (A + a) by lia. exact H2.
    - cbn [cells_size csize Nat.add]. replace (A + Z.of_nat (n1 + 0) + Z.of_nat (n2 + 0)) with (A + a + k) by lia. exact H3. }
  destruct (rw_cells_forget segs m A _ H) as [j HJ]. cbn [app cells_size csize Nat.add] in HJ.
  replace (n1 + (n2 + (n3 + 0)))%nat with n in HJ by lia. exists j. exact HJ.
Qed.

(* [comment removed for export] *)
Lemma le8_of_bytes : forall bs : list byte, length bs = 8%nat -> le8 (le_bytes_to_word bs) = bs.
Proof.
  intros bs HL. unfold le8, word_to_le_bytes, le_bytes_to_word.
  pose proof (le_val_range _ (bytes_ok_map bs)) as HR. rewrite length_map, HL in HR.
  change (256 ^ Z.of_nat 8) with (2^64) in HR. rewrite <- bytes_le_to_Z_le_val in HR.
  rewrite unsigned_lit by lia. rewrite <- HL. apply Z_to_le_bytes_to_Z.
Qed.

Lemma cb8_as_c8 : forall segs m A pre j post,
  rw_cells segs m A (pre ++ CB 8 j :: post) -> exists w, rw_cells segs m A (pre ++ C8 w :: post).
Proof.
  intros segs m A pre j post H. exists (le_bytes_to_word j).
  pose proof H as [[WF _] _]. apply cells_wf_app in WF. destruct WF as [WF1 [WFJ WF2]]. cbn in WFJ.
  eapply rw_cells_recell; [exact H | |].
  - apply cells_wf_app. split; [exact WF1|]. split; [exact I| exact WF2].
  - rewrite !cells_bytes_app. cbn [cells_bytes cbytes]. rewrite le8_of_bytes by exact WFJ. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma cb32_as_c8s : forall segs m A c0 j,
  rw_cells segs m A [c0; CB 32 j] -> exists w0 w1 w2 w3, rw_cells segs m A [c0; C8 w0; C8 w1; C8 w2; C8 w3].
Proof.
  intros segs m A c0 j H.
  apply (rw_cells_split_CB segs m A [c0] 32 j [] [8; 8; 8; 8]%nat) in H; [| reflexivity]. cbn [mk_CB_cells app] in H.
  destruct (cb8_as_c8 segs m A [c0] _ _ H) as [w0 H0]. cbn [app] in H0.
  destruct (cb8_as_c8 segs m A [c0; C8 w0] _ _ H0) as [w1 H1]. cbn [app] in H1.
  destruct (cb8_as_c8 segs m A [c0; C8 w0; C8 w1] _ _ H1) as [w2 H2]. cbn [app] in H2.
  destruct (cb8_as_c8 segs m A [c0; C8 w0; C8 w1; C8 w2] _ _ H2) as [w3 H3]. cbn [app] in H3.
  exists w0, w1, w2, w3. exact H3.
Qed.

(* [comment removed for export] *)
Lemma stk_open : forall segs m lo hi a (n : nat),
  stk segs m lo hi -> lo <= a -> a + Z.of_nat n <= hi ->
  exists j, rw_cells segs m a [CB n j] /\ stk segs m lo a /\ stk segs m (a + Z.of_nat n) hi.
Proof.
  intros segs m lo hi a n S La Lh.
  destruct (stk_split segs m lo (a + Z.of_nat n) hi S ltac:(lia)) as [S1 S3].
  destruct (stk_carve segs m lo (a + Z.of_nat n) n S1 ltac:(lia)) as [S0 [j C]].
  replace (a + Z.of_nat n - Z.of_nat n) with a in * by lia.
  exists j. split; [exact C|]. split; [exact S0| exact S3].
Qed.

Lemma stk_close : forall segs m lo hi a cs,
  stk segs m lo a -> rw_cells segs m a cs -> stk segs m (a + Z.of_nat (cells_size cs)) hi ->
  lo <= a -> a + Z.of_nat (cells_size cs) <= hi ->
  stk segs m lo hi.
Proof.
  intros segs m lo hi a cs S0 C S3 La LE.
  eapply stk_merge; [eapply stk_release; [exact S0 | exact C | exact La] | exact S3 | lia].
Qed.
