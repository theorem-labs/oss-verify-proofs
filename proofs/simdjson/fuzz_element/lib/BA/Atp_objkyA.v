(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.AS Require Import ShapeAlg AsanAcct.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Lib Require Import Tac Arr Bytes ImageA RzCPS StoreFast FP SysStep.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Spec Require Import Prelim.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Sj Require Import SjTape SjTapeList.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.P Require Import Str_tac Sj_h_arith Sj_stage1_kit.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.A Require Import Shadow.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.A Require Import Layout RT_iface. From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.BA Require Import RT_iface2. From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.A Require Import D_defs D_kit D_clx D_rlkit Sj_rtf Sj_akit Sj_acps Sj_hkit. From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.BA Require Import Atp_defsA Atp_kitA Atp_objkwA.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.
Notation wz z := (Z_to_bv 64 z) (only parsing).

Definition atkey_frame (j0 : list byte) (sret Kp : Z) (ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) : list cell :=
  [CB 8 j0; C8 (wz sret); C8 (wz 4294967295); C8 (wz 4294967297); C8 (wz Kp)] ++ atkey_saved ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11.

Lemma key_word_rangeB : forall (T S : Z -> Z) (sn i : Z), is_str T S sn i -> sn < 2^56 ->
  0 <= T i < 2^64 /\ Z.land (T i) 72057594037927935 = tval (T i) /\ ttype (T i) = t_str.
Proof.
  intros T S sn i (o & l & X & (Y1 & Y2 & Y3 & _)) Hsn. rewrite X.
  split; [apply tword_range; [unfold t_str; lia| lia]|].
  split; [| apply ttype_tword; lia].
  change 72057594037927935 with (Z.ones 56). rewrite Z.land_ones by (unfold tword, t_str; lia).
  unfold tval. reflexivity.
Qed.
Lemma shl_mod_smallB : forall b k, 0 <= b < 256 -> 0 <= k <= 24 -> (Z.shiftl b k) mod 18446744073709551616 = Z.shiftl b k.
Proof.
  intros b k Hb Hk. apply Z.mod_small. rewrite Z.shiftl_mul_pow2 by lia.
  assert (0 < 2 ^ k <= 2 ^ 24) by (split; [apply Z.pow_pos_nonneg; lia| apply Z.pow_le_mono_r; lia]). nia.
Qed.
Lemma land_shiftl_smallB : forall x y n, 0 <= n -> 0 <= x < 2^n -> Z.land (Z.shiftl y n) x = 0.
Proof.
  intros x y n Hn Hx. apply Z.bits_inj'. intros i Hi. rewrite Z.land_spec, Z.bits_0.
  destruct (Z.lt_ge_cases i n) as [L|G].
  - rewrite Z.shiftl_spec_low by lia. reflexivity.
  - destruct (Z.eq_dec x 0) as [->|NZ]; [rewrite Z.bits_0; apply Bool.andb_false_r|].
    assert (LG : Z.log2 x < i).
    { apply (Z.lt_le_trans _ n); [| lia]. apply Z.log2_lt_pow2; lia. }
    rewrite (Z.bits_above_log2 x i) by lia. apply Bool.andb_false_r.
Qed.
Lemma lor_shiftl_smallB : forall x y n, 0 <= n -> 0 <= x < 2^n -> 0 <= y -> Z.lor (Z.shiftl y n) x = y * 2^n + x.
Proof.
  intros x y n Hn Hx Hy. rewrite <- Z.lxor_lor by (apply land_shiftl_smallB; lia).
  rewrite <- Z.add_nocarry_lxor by (apply land_shiftl_smallB; lia). rewrite Z.shiftl_mul_pow2 by lia. reflexivity.
Qed.
Lemma le32_of_lbu4B : forall b0 b1 b2 b3, 0 <= b0 < 256 -> 0 <= b1 < 256 -> 0 <= b2 < 256 -> 0 <= b3 < 256 ->
  Z.lor (Z.lor (Z.shiftl b3 24) (Z.shiftl b2 16)) (Z.lor (Z.shiftl b1 8) b0) = b0 + 2^8 * b1 + 2^16 * b2 + 2^24 * b3.
Proof.
  intros b0 b1 b2 b3 H0 H1 H2 H3.
  rewrite (lor_shiftl_smallB b0 b1 8) by lia.
  replace (Z.shiftl b3 24) with (Z.shiftl (Z.shiftl b3 8) 16) by (rewrite Z.shiftl_shiftl by lia; reflexivity).
  rewrite <- Z.shiftl_lor. rewrite (lor_shiftl_smallB b2 b3 8) by lia.
  rewrite (lor_shiftl_smallB (b1 * 2^8 + b0) (b3 * 2^8 + b2) 16); [lia| lia| |lia].
  change (2^16) with (2^8 * 2^8). lia.
Qed.
Lemma land64_shl_smallB : forall b k, 0 <= b < 256 -> 0 <= k <= 24 -> Z.land (Z.shiftl b k) 18446744073709551615 = Z.shiftl b k.
Proof.
  intros b k Hb Hk. rewrite land64_mod. apply Z.mod_small. rewrite Z.shiftl_mul_pow2 by lia.
  assert (0 < 2 ^ k <= 2 ^ 24) by (split; [apply Z.pow_pos_nonneg; lia| apply Z.pow_le_mono_r; lia]). nia.
Qed.

