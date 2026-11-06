(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Lib Require Import Tac ZBridge.
Import ListNotations.
Open Scope Z_scope.

Ltac condn K := try rewrite Z.mod_small in K by lia; try rewrite unsigned_lit in K by lia.

Tactic Notation "side" tactic(t) :=
  lazymatch goal with |- evt _ _ _ => idtac | _ => t end.

Lemma word_lt64 : forall w : word, (0 <= bv_unsigned w < 2^64)%Z.
Proof. intros w. pose proof (bv_unsigned_in_range 64 w) as H. unfold bv_modulus in H. cbn in H. cbn. lia. Qed.

Lemma sx32_lit : forall e, (-2^31 <= e < 2^31)%Z -> sx32 (Z_to_bv 64 e) = Z_to_bv 64 e.
Proof.
  intros e He. unfold sx32. apply Z_to_bv_eqm. rewrite unsigned_lit_wrap.
  change (bv_swrap 32 (e mod 2^64)) with (((e mod 2^64) + 2^31) mod 2^32 - 2^31)%Z.
  change (2^64)%Z with 18446744073709551616%Z. Z.div_mod_to_equations. nia.
Qed.

Lemma mod64_small_signed : forall a, (-2^31 <= a < 2^31)%Z ->
  (a mod 2^64 = if (a <? 0)%Z then a + 2^64 else a)%Z.
Proof.
  intros a Ha. destruct (Z.ltb_spec0 a 0).
  - rewrite <- (Z.mod_add a 1 (2^64)) by lia. rewrite Z.mod_small by lia. lia.
  - apply Z.mod_small. lia.
Qed.

Lemma mod64_inj_signed : forall a b, (-2^31 <= a < 2^31)%Z -> (-2^31 <= b < 2^31)%Z ->
  (a mod 2^64 = b mod 2^64)%Z -> a = b.
Proof.
  intros a b Ha Hb E. rewrite !mod64_small_signed in E by lia.
  destruct (Z.ltb_spec0 a 0); destruct (Z.ltb_spec0 b 0); lia.
Qed.

Lemma swrap32_id : forall x, (-2^31 <= x < 2^31)%Z -> bv_swrap 32 x = x.
Proof.
  intros x Hx. unfold bv_swrap, bv_wrap.
  change (bv_modulus 32) with (2^32)%Z. change (bv_half_modulus 32) with (2^31)%Z.
  rewrite Z.mod_small by lia. lia.
Qed.

Lemma signed_lit : forall v, (-2^63 <= v < 2^63)%Z -> bv_signed (Z_to_bv 64 v) = v.
Proof.
  intros v Hv. rewrite zb_signed, unsigned_lit_wrap.
  destruct (Z.lt_ge_cases v 0).
  - rewrite <- (Z.mod_add _ 1) by lia. rewrite Z.mod_small by lia.
    destruct (Z.ltb_spec0 (v + 1 * 2^64) (2^63)); lia.
  - rewrite Z.mod_small by lia. destruct (Z.ltb_spec0 v (2^63)); lia.
Qed.

Lemma small_mod64_pos : forall r, (-2^31 <= r < 2^31)%Z ->
  ((0 < r mod 2^64 /\ r mod 2^64 < 2^63) <-> 0 < r)%Z.
Proof. intros r Hr. rewrite mod64_small_signed by lia. destruct (Z.ltb_spec0 r 0); lia. Qed.
Lemma small_mod64_neg : forall r, (-2^31 <= r < 2^31)%Z ->
  ((2^63 <= r mod 2^64) <-> r < 0)%Z.
Proof. intros r Hr. rewrite mod64_small_signed by lia. destruct (Z.ltb_spec0 r 0); lia. Qed.

Section WithSegs.
Variable segs : list Segment.

#[using="Type"] Lemma wr_at_app : forall m A n1 n2, 0 <= n1 -> 0 <= n2 ->
  wr_at segs m A (n1 + n2) <-> wr_at segs m A n1 /\ wr_at segs m (A + n1) n2.
Proof.
  intros m A n1 n2 H1 H2. unfold wr_at. split.
  - intros (Ha & Hb & H). repeat split; try lia.
    + intros i Hi. apply H. lia.
    + intros i Hi. replace (A + n1 + i) with (A + (n1 + i)) by lia. apply H. lia.
  - intros ((Ha & Hb & H) & (Ha' & Hb' & H')). repeat split; try lia.
    intros i Hi. destruct (Z.lt_ge_cases i n1).
    + apply H. lia.
    + replace (A + i) with (A + n1 + (i - n1)) by lia. apply H'. lia.
Qed.

#[using="Type"] Lemma rw_cells_app : forall m A cs1 cs2,
  rw_cells segs m A (cs1 ++ cs2) <-> rw_cells segs m A cs1 /\ rw_cells segs m (A + Z.of_nat (cells_size cs1)) cs2.
Proof.
  intros m A cs1 cs2. unfold rw_cells, cells_at. rewrite cells_wf_app, cells_bytes_app, cells_size_app. split.
  - intros (((W1 & W2) & B) & WR).
    rewrite bytes_at_app in B. destruct B as [B1 B2]. rewrite cells_bytes_length in B2 by exact W1.
    rewrite Nat2Z.inj_add in WR. apply wr_at_app in WR; [|lia|lia]. destruct WR as [WR1 WR2]. tauto.
  - intros (((W1 & B1) & WR1) & ((W2 & B2) & WR2)). split; [split; [tauto|]|].
    + apply bytes_at_app. rewrite cells_bytes_length by exact W1. tauto.
    + rewrite Nat2Z.inj_add. apply wr_at_app; [lia|lia|]. tauto.
Qed.

#[using="Type"] Lemma rw_cells_take3 : forall m A pre mid post,
  rw_cells segs m A (pre ++ mid ++ post) ->
  rw_cells segs m A pre /\ rw_cells segs m (A + Z.of_nat (cells_size pre)) mid
  /\ rw_cells segs m (A + Z.of_nat (cells_size pre) + Z.of_nat (cells_size mid)) post.
Proof.
  intros m A pre mid post H. apply rw_cells_app in H. destruct H as [H1 H23].
  apply rw_cells_app in H23. destruct H23 as [H2 H3]. auto.
Qed.

#[using="Type"] Lemma rw_cells_put3 : forall m A pre mid post,
  rw_cells segs m A pre -> rw_cells segs m (A + Z.of_nat (cells_size pre)) mid ->
  rw_cells segs m (A + Z.of_nat (cells_size pre) + Z.of_nat (cells_size mid)) post ->
  rw_cells segs m A (pre ++ mid ++ post).
Proof.
  intros m A pre mid post H1 H2 H3. apply rw_cells_app. split; [exact H1|]. apply rw_cells_app. auto.
Qed.
End WithSegs.
