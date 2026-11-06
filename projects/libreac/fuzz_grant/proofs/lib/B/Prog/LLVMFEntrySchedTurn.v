(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: a phase of the entry function LLVMFuzzerTestOneInput on fuzz_grant.asan (GrantEntrySchedTurn), written for libreac/fuzz_grant with proof steps adapted from proofs/cgif/cgif_file_fuzzer/lib/A/ACjo.v. *)
(* Modified by Theorem Labs, 2026-10: image-B twin of lib/A/Prog/GrantEntrySchedTurn.v. *)
(* The image-B (UBSan) walk of the same turn and the same
   loop, over image B's own addresses, registers, spill slots and UBSan guards; the shape is
   image A's, less its segment D, whose work image B does inside the want_of call.
   Ported from proofs/libreac/fuzz_grant/lib/A/Prog/GrantEntrySchedTurn.v at e6bd82f51c9.

   One turn of the scheduler's frame loop in fuzz_grant's entry function
   LLVMFuzzerTestOneInput (0x80a3c) on the ASan+UBSan build, and the loop: from the head of
   the loop (0x81bb0, GI_sched) to the free of the table (0x81da4, GI_freeT),
   fuzz_grant.c:396-449.

   The turn is cut into the segments of LLVMFEntrySchedTurnDefs.v, each proved in its own
   file; this file composes them and closes the loop by induction on the turns left.
   Image B's counter is s5 (register 21), where image A's is s2 (register 18). *)
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.B Require Import YCbq.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YI16.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.B Require Import YC5d.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import PaTable PaSym PaShadow PaRun.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.B Require Import PaJournal PaBase.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.B.Prog Require Import
GrantTop GrantSyms GrantList GrantPa GrantPaLib.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.B.Prog Require Import
GrantBContracts LLVMFEntryDefs LLVMFEntrySeat.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Prog Require GrantSlotPlan Seg_sched_turn.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.B.Prog Require Import LLVMFEntrySchedTurnDefs
LLVMFEntrySchedTurnA LLVMFEntrySchedTurnB LLVMFEntrySchedTurnC LLVMFEntrySchedTurnCr
LLVMFEntrySchedTurnE LLVMFEntrySchedTurnF.
Import ListNotations.
Local Unset Lia Cache. Local Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section b.
Context {PI : PAImg grant_listing}.
#[local] Notation SEGS := (pa_segs).

Section c.
Variable B : asyms.
Variable MT : ameter_ops.
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis TL : PALib B.
Hypothesis NXT : GrantBContracts.tb_reac_headamp_tx_next_spec B.
Hypothesis EFF : GrantBContracts.tb_reac_headamp_tx_effective_spec B.
Hypothesis WOF : GrantBContracts.tb_want_of_spec B.

Theorem ge_sched_turn : forall POST,
  ge_from B MT POST (GI_freeT B MT) -> ge_from B MT POST (GI_sched B MT).
Proof.
  intros POST HFT.
  assert (SA : seg_A_ok B MT POST) by (eapply segA; eauto).
  assert (SB : seg_B_ok B MT POST) by (eapply segB; eauto).
  assert (SC : seg_C_ok B MT POST) by (eapply segC; eauto).
  assert (SCr : seg_Cr_ok B MT POST) by (eapply segCr; eauto).
  assert (SE : seg_E_ok B MT POST) by (eapply segE; eauto).
  assert (SF : seg_F_ok B MT POST) by (eapply segF; eauto).
  (* the loop, by induction on the turns left *)
  assert (IND : forall n, ge_from B MT POST (GSn B MT n)).
  { induction n as [|n IH].
    - intros cx fp k acc ly3 S3 W3 ms3 md3 HB HJ Hfr HMLE (HGI & R21m & _).
      exfalso. destruct HGI as (i & t & _ & _ & _ & _ & _ & Hi & R21 & _).
      pose proof (Seg_sched_turn.frames_range (c_pl cx)) as HFR.
      rewrite R21 in R21m. apply (f_equal (@bv_unsigned 64)) in R21m. unfold w64 in R21m.
      rewrite !Z_to_bv_unsigned in R21m. unfold bv_wrap in R21m. change (bv_modulus 64) with (2 ^ 64) in R21m.
      cbn [Z.of_nat Z.opp] in R21m. rewrite Z.mod_0_l in R21m by lia.
      apply Z.mod_divide in R21m; [|lia]. destruct R21m as (q & Hq).
      change (2 ^ 64) with 18446744073709551616 in Hq. lia.
    - pose proof (SF n HFT IH) as HTF.
      pose proof (SE (S n) HTF) as HTE.
      pose proof (SCr (S n) HTE) as HTCr.
      pose proof (SC (S n) HTCr) as HTC.
      pose proof (SB (S n) HTF HTC) as HTB.
      exact (SA (S n) HTB). }
  intros cx fp k acc ly3 S3 W3 ms3 md3 HB HJ Hfr HMLE HGI.
  pose proof HGI as (i & t & _ & _ & _ & _ & _ & Hi & R21 & _).
  pose proof (Seg_sched_turn.frames_range (c_pl cx)) as HFR.
  apply (IND (Z.to_nat (GrantSlotPlan.frames (c_pl cx) - Z.of_nat i)) cx fp k acc ly3 S3 W3 ms3 md3 HB HJ Hfr HMLE).
  split; [exact HGI|]. split; [|lia].
  rewrite R21. f_equal. lia.
Qed.

End c.
End b.
End a.
