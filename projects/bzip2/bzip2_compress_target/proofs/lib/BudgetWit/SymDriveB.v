(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* Modified by Theorem Labs, 2026-11: made from SymDrive.v: the R-typed declarations restated over the budget carrier, with twin modules imported last. *)
From Stdlib Require Lia.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib Require PropExec CatExec CatSim SeqExec StoreOk SimInv.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib Require CatSim.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib Require ShapeAlg SymExec Frame RefMemcpyLib.
Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.PropExec OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.CatExec OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.CatSim OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.SeqExec OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.StoreOk OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.SimInv OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.CatSim.ExitSim OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.ShapeAlg OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.SymExec OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Frame OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.RefMemcpyLib.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib Require SymExec2.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib Require SymRun.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib Require SymRun.
Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.SymExec2 OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.SymRun.SymExec2Sound OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.SymRun.
Import ListNotations.
Import SX2.
Import SX2S.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import CpsOpen.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib Require Import SymDrive.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.BudgetWit Require Import Rzb.

Unset Lia Cache.
Unset Nia Cache.
Unset Nra Cache.
Open Scope bv_scope.
Section Drive.
Variable segs : list Segment.
Theorem rzb_run : forall fuel stops scr pc sr kn nx ss' scs scr' kn' scs2 hs2
                         E M rom R model T,
  sym_exec segs fuel true stops scr (SS pc sr [] kn nx) [] = (ss', scs, scr') ->
  carry (s_log ss') kn [] = (kn', scs2, hs2) ->
  regs_ok E sr R -> know_ok segs E M kn ->
  scs_denot segs M E scs -> scs_denot segs M E scs2 ->
  m_halted model = None ->
  m_vm_lazy model = [] ->
  (forall R' M', regs_ok E (s_regs ss') R' -> know_ok segs E M' kn' ->
     M' = mem_denot E M (s_log ss') ->
     Rzb.rzb segs (mkCfg (mkst R' (Z_to_bv 64 (s_pc ss')) M' rom) model) T) ->
  Rzb.rzb segs (mkCfg (mkst R (Z_to_bv 64 pc) M rom) model) T.
Proof.
  intros fuel stops scr pc sr kn nx ss' scs scr' kn' scs2 hs2 E M rom R model T
         Hex Hc HR HK Hsc Hsc2 Hh Hlazy Hcont.
  cps_destruct (run_sound segs fuel stops scr pc sr kn nx ss' scs scr' E M rom R Hex HR HK Hsc)
    as (R' & HR' & Hlf & Hms).
  eapply Rzb.rzb_msteps; [exact Hh | exact Hlazy | exact Hms |].
  apply (Hcont R' _ HR'); [|reflexivity].
  eapply carry_after; eassumption.
Qed.
End Drive.
