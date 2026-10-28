(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BgLib Require Import ImageBg.
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.Lib Require Import MState Mem Cells Step Arr Bytes Frame Tac.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.Spec Require Import StrFun.
From OssFuzzTheorems.Proofs.openssl.bignum.lib.BnP Require Import BnKit2.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Lemma le8_of_bytes : forall bs : list byte, length bs = 8%nat -> le8 (le_bytes_to_word bs) = bs.
Proof.
  intros bs HL. unfold le8, word_to_le_bytes, le_bytes_to_word.
  pose proof (le_val_range _ (bytes_ok_map bs)) as HR. rewrite length_map, HL in HR. change (256 ^ Z.of_nat 8) with (2 ^ 64) in HR.
  rewrite <- bytes_le_to_Z_le_val in HR.
  rewrite unsigned_lit by lia. rewrite <- HL. apply Z_to_le_bytes_to_Z.
Qed.

Lemma u64s_exists : forall k (bs : list byte), length bs = (8 * k)%nat -> exists ws : list word, length ws = k /\ u64s ws = bs.
Proof.
  induction k as [|k IH]; intros bs H.
  - exists []. destruct bs; [split; reflexivity| cbn in H; lia].
  - destruct (IH (skipn 8 bs) ltac:(rewrite length_skipn; lia)) as (ws & Hl & E).
    exists (le_bytes_to_word (firstn 8 bs) :: ws). split; [cbn; lia|]. cbn [u64s].
    rewrite le8_of_bytes by (rewrite length_firstn; lia). rewrite E. apply firstn_skipn.
Qed.

Section WithSegs.
Variable segs : list Segment.

Lemma rw_cells_CB_u64arr : forall m A ws n, n = (8 * length ws)%nat ->
  rw_cells segs m A [CB n (u64s ws)] <-> u64arr segs m A ws.
Proof.
  intros m A ws n Hn. unfold rw_cells, cells_at, u64arr. cbn [cells_wf cell_wf cells_bytes cbytes cells_size csize].
  rewrite app_nil_r, u64s_length, Nat.add_0_r. subst n. rewrite Nat2Z.inj_mul. cbn [Z.of_nat Pos.of_succ_nat]. change (Z.pos 8) with 8. tauto.
Qed.

Lemma val_frame_split : forall m FB j0 ws rest, length ws = 32%nat ->
  rw_cells segs m FB (CB 8 j0 :: CB 256 (u64s ws) :: rest) ->
  rw_cells segs m FB [CB 8 j0] /\ u64arr segs m (FB + 8) ws /\ rw_cells segs m (FB + 264) rest.
Proof.
  intros m FB j0 ws rest HL H.
  change (CB 8 j0 :: CB 256 (u64s ws) :: rest) with ([CB 8 j0] ++ [CB 256 (u64s ws)] ++ rest) in H.
  apply bk_rw_cells_app in H. destruct H as [H1 H]. apply bk_rw_cells_app in H. destruct H as [H2 H3].
  cbn [cells_size csize Nat.add] in H2, H3. split; [exact H1|]. split.
  - apply (rw_cells_CB_u64arr m (FB + 8) ws 256); [rewrite HL; reflexivity|]. exact H2.
  - replace (FB + 264) with (FB + Z.of_nat 8 + Z.of_nat 256) by lia. exact H3.
Qed.

Lemma val_frame_join : forall m FB j0 ws rest, length ws = 32%nat ->
  rw_cells segs m FB [CB 8 j0] -> u64arr segs m (FB + 8) ws -> rw_cells segs m (FB + 264) rest ->
  rw_cells segs m FB (CB 8 j0 :: CB 256 (u64s ws) :: rest).
Proof.
  intros m FB j0 ws rest HL H1 H2 H3.
  change (CB 8 j0 :: CB 256 (u64s ws) :: rest) with ([CB 8 j0] ++ [CB 256 (u64s ws)] ++ rest).
  apply bk_rw_cells_app. split; [exact H1|]. apply bk_rw_cells_app. cbn [cells_size csize Nat.add]. split.
  - apply (rw_cells_CB_u64arr m (FB + Z.of_nat 8) ws 256); [rewrite HL; reflexivity|]. replace (FB + Z.of_nat 8) with (FB + 8) by lia. exact H2.
  - replace (FB + Z.of_nat 8 + Z.of_nat 256) with (FB + 264) by lia. exact H3.
Qed.

Lemma val_frame_init : forall m FB j0 (a0 : word) junk rest,
  rw_cells segs m FB (CB 8 j0 :: C8 a0 :: CB 248 junk :: rest) ->
  exists ws, length ws = 32%nat /\ nth_error ws 0 = Some a0 /\ rw_cells segs m FB (CB 8 j0 :: CB 256 (u64s ws) :: rest).
Proof.
  intros m FB j0 a0 junk rest H.
  assert (HLj : length junk = 248%nat).
  { destruct H as [[Hwf _] _]. cbn [cells_wf cell_wf] in Hwf. tauto. }
  destruct (u64s_exists 31 junk ltac:(rewrite HLj; reflexivity)) as (ws & Hl & E).
  exists (a0 :: ws). split; [cbn; lia|]. split; [reflexivity|].
  change (CB 8 j0 :: C8 a0 :: CB 248 junk :: rest) with ([CB 8 j0] ++ ([C8 a0] ++ [CB 248 junk]) ++ rest) in H.
  change (CB 8 j0 :: CB 256 (u64s (a0 :: ws)) :: rest) with ([CB 8 j0] ++ [CB 256 (u64s (a0 :: ws))] ++ rest).
  eapply bk_rw_cells_recast; [exact H| | |].
  - destruct H as [[Hwf _] _]. rewrite !cells_wf_app in *. cbn [cells_wf cell_wf] in *. rewrite u64s_length. cbn [length]. rewrite Hl. tauto.
  - rewrite !cells_bytes_app. cbn [cells_bytes cbytes u64s]. rewrite E, !app_nil_r, <- app_assoc. reflexivity.
  - rewrite !cells_size_app. reflexivity.
Qed.

End WithSegs.
