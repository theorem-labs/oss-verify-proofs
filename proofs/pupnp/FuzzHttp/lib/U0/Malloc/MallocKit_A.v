(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.pupnp.FuzzHttp.lib.Lib Require Import Tac Image ZBridge SysStep SFModel ITree Nodes Decode Arr.
From OssFuzzTheorems.Proofs.pupnp.FuzzHttp.lib.U0.Malloc Require Import F_syscalls MallocRep F_malloc_free F_malloc_fast F_malloc_enframe MallocTree MallocFacts_A.
From OssFuzzTheorems.Proofs.pupnp.FuzzHttp.lib.Spec Require Import STree Malloc MallocCtrl Monad Prog.
Import ListNotations.
Open Scope Z_scope.

Lemma ticks_ok_upd_meta st g f : ticks_ok st -> ticks_ok (upd_meta g f st).
Proof. intros T; exact T. Qed.
Lemma ticks_ok_upd_ctx st f : ticks_ok st -> ticks_ok (upd_ctx f st).
Proof. intros T; exact T. Qed.
Lemma ticks_ok_wr16 st p v : ticks_ok st -> ticks_ok (wr16 p v st).
Proof. intros T. unfold wr16. apply ticks_ok_wr8, ticks_ok_wr8, T. Qed.
Lemma ticks_ok_wr32 st p v : ticks_ok st -> ticks_ok (wr32 p v st).
Proof. intros T. unfold wr32. repeat apply ticks_ok_wr8. exact T. Qed.
Lemma ticks_ok_set_size p e n b st : ticks_ok st -> ticks_ok (set_size p e n b st).
Proof.
  intros T. unfold set_size.
  destruct (5 <=? _); destruct (negb _); repeat first [apply ticks_ok_wr8 | apply ticks_ok_wr32]; exact T.
Qed.

Lemma get_shadow_set_tick st t rid : get_shadow (set_tick t st) rid = get_shadow st rid.
Proof. reflexivity. Qed.
Lemma get_shadow_upd_meta st g f rid : get_shadow (upd_meta g f st) rid = get_shadow st rid.
Proof. reflexivity. Qed.
Lemma s_regions_wr8 st p v : s_regions (wr8 p v st) = s_regions st.
Proof. reflexivity. Qed.
Lemma s_groups_wr8 st p v : s_groups (wr8 p v st) = s_groups st.
Proof. reflexivity. Qed.
Lemma conc_wr8 st p v q : conc (wr8 p v st) q = conc st q.
Proof. reflexivity. Qed.
Lemma conc_wr16 st p v q : conc (wr16 p v st) q = conc st q.
Proof. reflexivity. Qed.
Lemma conc_set_tick st t q : conc (set_tick t st) q = conc st q.
Proof. reflexivity. Qed.
Lemma conc_upd_meta st g f q : conc (upd_meta g f st) q = conc st q.
Proof. reflexivity. Qed.
Lemma conc_havoc st p n q : conc (havoc p n st) q = conc st q.
Proof. unfold havoc. destruct (n <=? 0); reflexivity. Qed.
Lemma conc_set_size p e n b st q : conc (set_size p e n b st) q = conc st q.
Proof. unfold set_size. destruct (5 <=? _); destruct (negb _); reflexivity. Qed.
Lemma conc_enframe_at st g k n off q : conc (fst (enframe_at st g k n off)) q = conc st q.
Proof. unfold enframe_at. destruct (negb (off =? 0)); cbn [fst]; rewrite conc_set_size; reflexivity. Qed.

Lemma le4_bytes : forall v, 0 <= v < 2^32 ->
  le4 (wz v) = [b8 (v mod 256); b8 ((v / 256) mod 256); b8 ((v / 65536) mod 256); b8 (v / 16777216)].
Proof.
  intros v Hv. unfold le4, wz, b8. rewrite unsigned_lit by lia. cbn [Z_to_le_bytes].
  rewrite !Z.shiftr_shiftr by lia.
  rewrite !Z.shiftr_div_pow2 by lia. change (2^8) with 256. change (2^(8+8)) with 65536. change (2^(8+8+8)) with 16777216.
  assert (E : forall x, Z_to_bv 8 x = Z_to_bv 8 (x mod 256)).
  { intros x. apply Z_to_bv8_mod. change (2^8) with 256. rewrite Z.mod_mod by lia. reflexivity. }
  rewrite (E v) at 1. rewrite (E (v / 256)) at 1. rewrite (E (v / 65536)) at 1. reflexivity.
Qed.

Lemma lowbit_facts : forall v, 0 < v < 2^32 -> exists k, 0 <= k < 32 /\ lowbit v = 2 ^ k.
Proof.
  intros v Hv. destruct (lowbit_pow2 v ltac:(lia)) as (k & Hk & E & Hle). exists k.
  split; [|unfold lowbit; exact E]. split; [exact Hk|].
  destruct (Z.lt_ge_cases k 32) as [?|GE]; [assumption|].
  assert (2 ^ 32 <= 2 ^ k) by (apply Z.pow_le_mono_r; lia). lia.
Qed.

Lemma b8_of_byte : forall x : byte, b8 (bv_unsigned x) = x.
Proof. intros x. unfold b8. apply bv_eq. rewrite Z_to_bv_unsigned. apply bv_wrap_small. apply bv_unsigned_in_range. Qed.

Lemma byte_range : forall x : byte, 0 <= bv_unsigned x < 256.
Proof. intros x. pose proof (bv_unsigned_in_range 8 x) as H. unfold bv_modulus in H. cbn in H. lia. Qed.