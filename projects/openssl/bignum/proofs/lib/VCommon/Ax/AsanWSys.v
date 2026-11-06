(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.LinuxProcessSem.Sys Require Import Uapi.
From LinuxProcessSemantics.LinuxProcessSem.Checks Require Import ExecutableSpecs.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.Proofs.openssl.bignum.lib.VCommon Require Import
  PropExec SimInv CatSim CatExec SeqExec FileSim ShapeAlg ShapeAlgCfg AgentLib AgentNodes Nodes NodesCfg
  NodesOpenCfg StoreOk.
From OSSVerify.Proofs.openssl.bignum.lib.VCommon.BootWitness Require Import BootDefs BootStep.
From OSSVerify.Proofs.openssl.bignum.lib.VCommon.Ax Require Import AsanWLazy AsanWAcc.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.

Section Gen.
Variable segs : list Segment.
Variable cfg : SpuriousCfg.

End Gen.

Lemma lg0 : forall S, ms_gpr (latch S) 0 = rg S 10. Proof. reflexivity. Qed.
Lemma lg1 : forall S, ms_gpr (latch S) 1 = rg S 11. Proof. reflexivity. Qed.
Lemma lg2 : forall S, ms_gpr (latch S) 2 = rg S 12. Proof. reflexivity. Qed.

Definition fds_std : list (word * FdEntry) :=
  [ (Z_to_bv 64 0, FdChannel (Z_to_bv 64 0));
    (Z_to_bv 64 1, FdChannel (Z_to_bv 64 1));
    (Z_to_bv 64 2, FdChannel (Z_to_bv 64 2)) ].

Section Sys.
Variable segs : list Segment.
Variable cfg : SpuriousCfg.
Hypothesis Hcfg : cfg_nonalloc_on cfg.

Local Existing Instance PropExec.fx0.

End Sys.
