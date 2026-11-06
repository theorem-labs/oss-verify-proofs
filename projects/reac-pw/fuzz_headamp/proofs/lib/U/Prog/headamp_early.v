(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Copyright 2026 Theorem Labs *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libdiginet/fuzz_decode/lib/Prog/LLVMFuzzerTestOneInput_fr.v, with its module paths and module names changed; 457 of its 574 lines of code are new or changed and 410 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_rate/lib/Prog/Seg/Tac_slot.v, with its module paths and module names changed; 215 of its 252 lines of code are new or changed and 537 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_rate/lib/Prog/RateSlot.v, with its module paths, module names and numbers changed; 9 of its 44 lines of code are new or changed and 217 lines of the source are left out. *)
(* The n >= 2^26 run of reac-pw/fuzz_headamp LLVMFuzzerTestOneInput (UBSan): headamp_early_contract
   (U/Prog/LLVMFuzzerTestOneInput_c.v). 0x12fa8 `addi sp,sp,-0x260`; the thirteen saves ra, s0 .. s11 (0x12fac ..
   0x12fdc) and the four fsd of fs0 .. fs3 (0x12fe0 .. 0x12fec); 0x12ff0 `srli a2,a1,26`; 0x12ff4 `beqz a2` not taken
   (n >= 2^26); 0x12ff8 `j 0x1484c`; 0x1484c `mv a0,zero`, the thirteen restores (0x14850 .. 0x14880), the four fld of
   fs0 .. fs3 (0x14884 .. 0x14890), `addi sp,sp,0x260`, `ret`. No call, no trap. The integer registers come back from
   their saves; the FP registers are whatever the fld read (the contract leaves F' open), fcsr is untouched.
   reac-pw/fuzz_role's U/Prog/RoleSlot.early_evt with headamp's 608-byte frame and the FP saves. *)
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.U Require Import Img0 FrameAPI.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Lib Require Import PropExec MState Mem Exec Frame Step Cells Tac.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.U.Prog Require Import LLVMFuzzerTestOneInput_c.
Import ListNotations.
Open Scope Z_scope.

Lemma he_bv_eqb : forall a b, -2 ^ 63 <= a < 2 ^ 63 -> -2 ^ 63 <= b < 2 ^ 63 ->
  bv_eqb (Z_to_bv 64 a) (Z_to_bv 64 b) = (a =? b).
Proof.
  intros a b Ha Hb. unfold bv_eqb. rewrite !Z_to_bv_unsigned. unfold bv_wrap, bv_modulus.
  change (2 ^ Z.of_N 64) with 18446744073709551616.
  destruct (Z.eqb_spec a b) as [->|Hn]; [apply Z.eqb_refl|]. apply Z.eqb_neq.
  intros E. apply Hn. Z.div_mod_to_equations. lia.
Qed.

(* 0x12ff4 `beqz a2, 8` with a2 = n >> 26 <> 0: not taken. *)
Lemma he_cond : forall u, 2 ^ 26 <= u < 2 ^ 64 ->
  bv_eqb (Z_to_bv 64 (Z.shiftr u 26)) (Z_to_bv 64 0) = false.
Proof.
  intros u Hu. rewrite Z.shiftr_div_pow2 by lia.
  assert (H1 : 1 <= u / 2 ^ 26) by (apply Z.div_le_lower_bound; lia).
  assert (H2 : u / 2 ^ 26 < 2 ^ 38) by (apply Z.div_lt_upper_bound; lia).
  rewrite (he_bv_eqb (u / 2 ^ 26) 0) by lia.
  destruct (Z.eqb_spec (u / 2 ^ 26) 0); [lia | reflexivity].
Qed.

Theorem headamp_early_holds : headamp_early_contract.
Proof.
  unfold headamp_early_contract.
  intros ra gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m S lo ST LO HS MI Ha1.
  pose proof (munch_refl [(S - 608, S)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  pose proof (bv_unsigned_in_range 64 a1) as Ra1. unfold bv_modulus in Ra1. change (2 ^ Z.of_N 64) with (2 ^ 64) in Ra1.
  assert (S0 : 0 <= lo) by (destruct ST as [H _]; exact H).
  unfold ENTRY.
  carve_frame 608%nat ST.
  do 20 step.
  if_false_by (he_cond (bv_unsigned a1) ltac:(lia)).
  do 21 step.
  release_frame FR ST S.
  finish.
  all: try (f_equal; lia).
Qed.
