(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)
(* reloc14 *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.Lib Require Import Arr Bytes ZBridge.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.cks Require Import CkTables CkModel CkMathCrc CkMathAdler CkWalk CkHarness.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.CkA Require Import FuzzAGlue.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.CkB Require Import CkBImg CkBTables CkBShadow CkBIface CkBKit AdlB_closed.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.LibA Require Import Shadow.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.LibA Require Import StepF.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Ltac acc_hint ::= acc_hint_shrng.

Definition fz_FRAME (sp ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (m1 : amem) : Prop := exists junk,
  rw_cells asegs m1 (bv_unsigned sp + -112)
    [CB 8 junk; C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].
Definition fz_FRAME1 (sp ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (m1 : amem) : Prop :=
  rw_cells asegs m1 (bv_unsigned sp + -112)
    [C8 (Z_to_bv 64 1); C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].
Lemma fz_FRAME1_0 : forall sp ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m1,
  fz_FRAME1 sp ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m1 -> fz_FRAME sp ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m1.
Proof.
  intros sp ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m1 F. exists (cells_bytes [C8 (Z_to_bv 64 1)]).
  exact (rw_cells_merge asegs m1 _ [] [C8 (Z_to_bv 64 1)] _ F).
Qed.
Definition fz_INVG (FRAME : amem -> Prop) (sp : word) (m : amem) (lo D : Z) (bs : list Z) (m1 : amem) : Prop :=
  FRAME m1 /\ stk asegs m1 lo (bv_unsigned sp + -112)
  /\ munch [(bv_unsigned sp - 288, bv_unsigned sp)] m m1 /\ wmono asegs m m1 /\ mem_inv asegs m1
  /\ bytes_at asegs m1 D (zb bs) /\ rt_got m1 /\ rt_shbase m1.

Definition fz_INV (sp ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) := fz_INVG (fz_FRAME sp ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11) sp.
Definition fz_INV1 (sp ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) := fz_INVG (fz_FRAME1 sp ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11) sp.
Lemma fz_INV1_0 : forall sp ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m lo D bs m1,
  fz_INV1 sp ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m lo D bs m1 -> fz_INV sp ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m lo D bs m1.
Proof. intros until m1. intros (F & R). split; [apply fz_FRAME1_0; exact F| exact R]. Qed.

Lemma fz_W_above : forall sp : word, wabove [(bv_unsigned sp - 288, bv_unsigned sp)] (bv_unsigned sp - 288).
Proof. intros sp. cbn. split; [lia| exact I]. Qed.

Lemma CRC32Z_u : crc32_z_stmtA -> ltac:(let T := eval unfold crc32_z_stmtA, CK_CRC32Z_STACK in crc32_z_stmtA in exact T).
Proof. exact (fun H => H). Qed.
Lemma CRC32_u : crc32_stmtA -> ltac:(let T := eval unfold crc32_stmtA, CK_CRC32Z_STACK in crc32_stmtA in exact T).
Proof. exact (fun H => H). Qed.
Lemma CRC32N_u : crc32_null_stmtA -> ltac:(let T := eval unfold crc32_null_stmtA, CK_CRC32Z_STACK in crc32_null_stmtA in exact T).
Proof. exact (fun H => H). Qed.
Lemma COMB_u : crc32_combine_stmtA -> ltac:(let T := eval unfold crc32_combine_stmtA, CK_COMBINE_STACK in crc32_combine_stmtA in exact T).
Proof. exact (fun H => H). Qed.
Lemma GEN_u : crc32_combine_gen_stmtA -> ltac:(let T := eval unfold crc32_combine_gen_stmtA, CK_GEN_STACK in crc32_combine_gen_stmtA in exact T).
Proof. exact (fun H => H). Qed.
Lemma ADLZ_u : ltac:(let T := eval unfold adler32_z_stmtA, CK_ADLER32Z_STACK in adler32_z_stmtA in exact T).
Proof. exact adler32_z_A. Qed.
Lemma ADL_u : ltac:(let T := eval unfold adler32_stmtA, CK_ADLER32Z_STACK in adler32_stmtA in exact T).
Proof. exact adler32_A. Qed.
Lemma ADLN_u : ltac:(let T := eval unfold adler32_null_stmtA, CK_ADLER32Z_STACK in adler32_null_stmtA in exact T).
Proof. exact adler32_null_A. Qed.

Section P.
  Variables (RNG : footprint)
            (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word)
            (FR : bvmap 5 word) (fc : bv 32) (m : amem) (lo : Z) (D n : Z) (bs : list Z).
  Hypothesis LOS : lo <= bv_unsigned sp - 288.
  Hypothesis KLO : KHIGH <= lo.
  Hypothesis D1 : 1 <= D.
  Hypothesis NL : Z.of_nat (length bs) = n.
  Hypothesis DLO : D + n <= lo.
  Hypothesis BF : Forall (fun b => 0 <= b < 256) bs.
  Hypothesis UNP : unpoisoned m D (D + n).
  Hypothesis RB : rng RNG D n.
  Hypothesis RS : shrng RNG D (D + n).
  Hypothesis CKSH : ck_sh m.
  Hypothesis RI : rng_aimg RNG.
  Hypothesis RISH : rng_aimg_sh RNG.
  Hypothesis RSTK : rng RNG lo (bv_unsigned sp - lo).

  Notation SP := (bv_unsigned sp).
  Notation W := [(SP - 288, SP)].
  Notation POST res := (ck_postA 288 ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc res lo m).
  Notation INV := (fz_INV sp ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m lo D bs).

  Lemma fz_cksh : forall m1, INV m1 -> ck_sh m1.
  Proof using All.
    intros m1 (_ & _ & MU & _). eapply (ck_sh_mu W (SP - 288)); [exact CKSH| exact MU| apply fz_W_above|]. unfold KHIGH in *. lia.
  Qed.

  Lemma fz_buf : forall m1 (off k : nat), INV m1 -> (off + k <= length bs)%nat ->
    ck_buf RNG m1 (D + Z.of_nat off) (firstn k (skipn off bs)).
  Proof using All.
    intros m1 off k (_ & _ & MU & _ & _ & BY & _) Hk.
    apply ck_buf_sub; [|exact Hk].
    split; [exact BY|]. split; [exact BF|]. rewrite NL. split; [|split; [exact RB| exact RS]].
    eapply (unpoisoned_mu W (SP - 288)); [exact UNP| exact MU| apply fz_W_above| lia| unfold KHIGH in *; lia].
  Qed.

  Lemma fz_bufZ : forall m1 off k, INV m1 -> 0 <= off -> 0 <= k -> off + k <= n ->
    ck_buf RNG m1 (D + off) (fz_chunk bs off k).
  Proof using All.
    intros m1 off k I1 H0 Hk H. unfold fz_chunk.
    replace (D + off) with (D + Z.of_nat (Z.to_nat off)) by lia. apply fz_buf; [exact I1| lia].
  Qed.

  Lemma fz_buf_whole : forall m1, INV m1 -> ck_buf RNG m1 D bs.
  Proof using All.
    intros m1 (_ & _ & MU & _ & _ & BY & _).
    split; [exact BY|]. split; [exact BF|]. rewrite NL. split; [|split; [exact RB| exact RS]].
    eapply (unpoisoned_mu W (SP - 288)); [exact UNP| exact MU| apply fz_W_above| lia| unfold KHIGH in *; lia].
  Qed.

  Lemma fz_epi : forall m1 (x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word),
    INV m1 ->
    evtF asegs RNG (POST 0)
      (MS (mkR x1 (Z_to_bv 64 (SP + -112)) gp tp x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
          FR (Z_to_bv 64 0x80774) fc None m1 (seg_rom asegs)).
  Proof using All.
    intros m1 x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31
           ([junk FRM] & ST & MU & WM & MI & BY & GOT & SHB).
    pose proof KLO as KLO'. unfold KHIGH in KLO'.
    do 16 zstep.
    release_frame FRM ST (bv_unsigned sp).
    finish.
    all: try assumption.
  Qed.
End P.
