(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Tac Image ZBridge SysStep.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Nodes.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Nodes Decode Arr SFMisc.
Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib.Tac OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib.Image OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib.ZBridge OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib.SysStep OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib.Nodes.ITree OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib.Nodes OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib.Decode OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib.Arr OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib.SFMisc.
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA Require Import F_syscalls MallocRep F_malloc_free F_malloc_fast F_malloc_enframe MallocTree MallocFacts_A.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Spec Require Import STree Malloc MallocCtrl Monad Prog.
From Stdlib Require Lia. Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib Require Import ACeil RunW.
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import CpsOpen.
Section ACeilS1. Context {ACEIL__ : ACeil} {RUNW__ : RunW}.


(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma ticks_ok_upd_meta st g f : ticks_ok st -> ticks_ok (upd_meta g f st).
Proof. intros T; exact T. Qed.
(* [comment removed for export] *)
Lemma ticks_ok_wr16 st p v : ticks_ok st -> ticks_ok (wr16 p v st).
Proof. intros T. unfold wr16. apply ticks_ok_wr8, ticks_ok_wr8, T. Qed.
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma s_regions_wr8 st p v : s_regions (wr8 p v st) = s_regions st.
Proof. reflexivity. Qed.
Lemma s_groups_wr8 st p v : s_groups (wr8 p v st) = s_groups st.
Proof. reflexivity. Qed.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma conc_havoc st p n q : conc (havoc p n st) q = conc st q.
Proof. unfold havoc. destruct (n <=? 0); reflexivity. Qed.
Lemma conc_set_size p e n b st q : conc (set_size p e n b st) q = conc st q.
Proof. unfold set_size. destruct (5 <=? _); destruct (negb _); reflexivity. Qed.
Lemma conc_enframe_at st g k n off q : conc (fst (enframe_at st g k n off)) q = conc st q.
Proof. unfold enframe_at. destruct (negb (off =? 0)); cbn [fst]; rewrite conc_set_size; reflexivity. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

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

(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma lowbit_facts : forall v, 0 < v < 2^32 -> exists k, 0 <= k < 32 /\ lowbit v = 2 ^ k.
Proof.
  intros v Hv. cps_destruct (lowbit_pow2 v ltac:(lia)) as (k & Hk & E & Hle). exists k.
  split; [|unfold lowbit; exact E]. split; [exact Hk|].
  destruct (Z.lt_ge_cases k 32) as [?|GE]; [assumption|].
  assert (2 ^ 32 <= 2 ^ k) by (apply Z.pow_le_mono_r; lia). lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

Lemma b8_of_byte : forall x : byte, b8 (bv_unsigned x) = x.
Proof. intros x. unfold b8. apply bv_eq. rewrite Z_to_bv_unsigned. apply bv_wrap_small. apply bv_unsigned_in_range. Qed.

Lemma byte_range : forall x : byte, 0 <= bv_unsigned x < 256.
Proof. intros x. pose proof (bv_unsigned_in_range 8 x) as H. unfold bv_modulus in H. cbn in H. lia. Qed.

End ACeilS1.
