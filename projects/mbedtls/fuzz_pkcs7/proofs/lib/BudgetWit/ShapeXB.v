(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from BB/ShapeX.v's rz_exit, over BudgetWit.Rzb.realizes; the exit node discharges its no-allocation-call check from the exit number. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (rz_exit's proof also discharges node_ok's third conjunct, sys_rob, by sys_rob_exit; RomBase imported). *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.LinuxProcessSem.Checks Require Import ExecutableSpecs.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Common Require Import SimInv ExitSim.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.BB Require Import CatSim MmapSim AllocSim WallSim.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import Shape.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.BB Require Import ShapeX.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.BudgetWit Require Import Rzb.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Common.Cfg Require Import RomBase.

Import ListNotations.
Open Scope bv_scope.

Section WithSegs.
Variable segs : list Segment.

#[using="Type"] Lemma rz_exit : forall ms model x8,
  m_halted model = None ->
  ms_svc_pending ms = Some x8 ->
  is_exit_no x8 ->
  realizes segs (mkCfg ms model)
           (t_exit (bv_and (ms_gpr ms 0) (Z_to_bv 64 255)) (m_fs model)).
Proof.
  intros ms model x8 Hh Hsvc Hx8.
  set (code := bv_and (ms_gpr ms 0) (Z_to_bv 64 255)).
  unfold t_exit.
  eapply (rz_emit1 segs (mkCfg ms model) (mkCfg ms (with_halted code model))).
  - split; [|split].
    + intros []. cbn.
      replace [ExitEv code (m_fs model)]
        with ([] ++ [ExitEv code (m_fs (with_halted code model))]) by reflexivity.
      apply (sstep_exit segs ms model x8 (mkEffect (Z_to_bv 64 0) [] [])
               (with_halted code model) [] code);
        [exact Hh | exact Hsvc
         | apply (exit_dispatch_ok (sys_input segs ms x8) model);
           rewrite in_sysno_sys_input; exact Hx8
         | reflexivity
         | apply m_killed_with_halted ].
    + intros e st Hss.
      destruct (sstep_exit_inv segs ms model x8 e st Hh Hsvc Hx8 Hss) as [-> ->].
      exists tt. split; reflexivity.
    + apply (sys_rob_exit segs ms model x8 Hsvc). exact Hx8.
  - exact (grant_free_no segs ms model x8 Hsvc (not_alloc_exit x8 Hx8)).
  - apply rz_halt. split; [exists (ms_gpr ms 0); reflexivity | apply m_killed_with_halted].
Qed.

End WithSegs.
