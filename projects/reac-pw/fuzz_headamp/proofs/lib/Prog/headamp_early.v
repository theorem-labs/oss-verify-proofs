(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Copyright 2026 Theorem Labs *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libdiginet/fuzz_decode/lib/Prog/LLVMFuzzerTestOneInput_fr.v, with its module paths and module names changed; 457 of its 574 lines of code are new or changed and 410 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_rate/lib/Prog/Seg/Tac_slot.v, with its module paths and module names changed; 215 of its 252 lines of code are new or changed and 537 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_rate/lib/Prog/RateSlot.v, with its module paths and numbers changed; 8 of its 48 lines of code are new or changed and 212 lines of the source are left out. *)
(* The n >= 2^26 run of reac-pw/fuzz_headamp LLVMFuzzerTestOneInput (plain): Prog/LLVMFuzzerTestOneInput_c.v's
   headamp_early_contract.
   0x12f88 `addi sp,sp,-0x230`; the thirteen saves ra, s0 .. s11 (0x12f8c .. 0x12fbc) and the three `fsd` of fs0,
   fs1, fs2 (0x12fc0 .. 0x12fc8); 0x12fcc `srli a2,a1,26`; 0x12fd0 `beqz a2` not taken (n >= 2^26); 0x12fd4
   `j 0x141d4`; 0x141d4 `mv a0,zero`, the thirteen restores (0x141d8 .. 0x14208), the three `fld` of fs0 .. fs2
   (0x1420c .. 0x14214), 0x14218 `addi sp,sp,0x230`, 0x1421c `ret`. No call. The run writes only the frame
   [S - 560, S); the `fld` write fs0 .. fs2, so the post holds at the FP registers the run leaves (fcsr is kept:
   fsd and fld accrue no flag).
   Adapted from reac-pw/fuzz_role's early_evt (Prog/RoleSlot.v), whose prologue and epilogue have no FP save.
   No function is proved here by itself: this is the early-return run of LLVMFuzzerTestOneInput's walk. *)
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YL01 YL00 YL0g YI06 YI16 YI14.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YM05 YL0i.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib Require Import Contract Img0 FrameAPI.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Lib Require Import PropExec MState Mem Exec Frame Step Cells Tac.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Prog Require Import SlotFR SlotInv LLVMFuzzerTestOneInput_c.
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

(* 0x12fd0 `beqz a2, 8` with a2 = n >> 26 <> 0: not taken. *)
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
  unfold headamp_early_contract, ENTRY.
  intros ra gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m S lo ST LO HS MI Ha1.
  pose proof (munch_refl [(S - 560, S)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  pose proof (bv_unsigned_in_range 64 a1) as Ra1. unfold bv_modulus in Ra1. change (2 ^ Z.of_N 64) with (2 ^ 64) in Ra1.
  assert (S0 : 0 <= lo) by (destruct ST as [H _]; exact H).
  carve_frame 560%nat ST.
  do 19 step.
  if_false_by (he_cond (bv_unsigned a1) ltac:(lia)).
  do 20 step.
  release_frame FR ST S.
  finish.
  all: try (f_equal; lia).
Qed.
