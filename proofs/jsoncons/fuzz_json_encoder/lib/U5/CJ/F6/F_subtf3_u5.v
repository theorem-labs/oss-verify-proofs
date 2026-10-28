(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.CJ.FA Require Import SFW1_lemmas.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.CJ.FA Require Import SFW_add_split.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5.CJ.F6 Require Import F_fe_getround_u5.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5.CJ.F6 Require Import F_addtf3_A_u5.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5.CJ.F6 Require Import F_addtf3_E_u5.
From OssFuzzTheorems.jsoncons.fuzz_json_encoder.images Require Import Ubsan.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.

Definition subtf3_entry := 0xb6c8c%Z.

Lemma land_shl64_low : forall h l, (0 <= l < 2^64)%Z -> Z.land (Z.shiftl h 64) l = 0%Z.
Proof.
  intros h l Hl. apply Z.bits_inj'. intros i Hi. rewrite Z.land_spec, Z.bits_0.
  destruct (Z.lt_ge_cases i 64).
  - rewrite Z.shiftl_spec_low by lia. reflexivity.
  - replace (Z.testbit l i) with false; [apply Bool.andb_false_r|].
    symmetry. destruct (Z.eq_dec l 0) as [->|]; [apply Z.bits_0|].
    apply Z.bits_above_log2; [lia|]. apply Z.lt_le_trans with 64%Z; [apply Z.log2_lt_pow2; lia|lia].
Qed.

Lemma f128_sub_split : forall aLo aHi bLo bHi,
  (0 <= bLo < 2^64)%Z -> (0 <= bHi < 2^64)%Z ->
  f128_sub (aLo + 2^64 * aHi) (bLo + 2^64 * bHi) = f128_add (aLo + 2^64 * aHi) (bLo + 2^64 * Z.lxor bHi 9223372036854775808).
Proof.
  intros aLo aHi bLo bHi Hl Hh. unfold f128_sub. rewrite lo64_words, hi64_words by lia.
  unfold mk128, SIGN64. rewrite Z.lor_comm, lor_disjoint_add.
  - rewrite Z.shiftl_mul_pow2 by lia. f_equal. lia.
  - rewrite Z.land_comm. apply land_shl64_low. lia.
Qed.

Lemma subtf3_spec : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte),
  stk rsegs m (bv_unsigned sp - 48) (bv_unsigned sp) ->
  mem_inv rsegs m ->
  frm0 fc ->
  evt rsegs (addtf3_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F
               (f128_sub (bv_unsigned a0 + 2^64 * bv_unsigned a1) (bv_unsigned a2 + 2^64 * bv_unsigned a3)) m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0xb6c8c) fc None m (seg_rom rsegs)).
Proof.
  intros until m. intros ST MI FRM. pose_word_ranges.
  pose proof (munch_refl [(bv_unsigned sp - 48, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl rsegs m) as WM.
  rewrite f128_sub_split by lia.
  do 4 zstep.
  eapply evt_mono; [ eapply addtf3_spec; eassumption | ].
  intros ms' PO. unfold addtf3_post in *.
  rewrite (inr64_unsigned_lit (Z.lxor (bv_unsigned a3) 9223372036854775808)) in PO by zrange.
  exact PO.
Qed.
