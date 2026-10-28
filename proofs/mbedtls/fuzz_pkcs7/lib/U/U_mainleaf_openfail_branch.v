(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OssFuzzTheorems.mbedtls.fuzz_pkcs7.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import PropExec Shape.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BB Require Import Amb CatExec CatSim SeqExec StoreOk ShapeX SymExec SymExec2 SymExec2Sound SymRun SymDrive SymDriveX.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Spec Require Import Spec.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.U Require Import U_startup U_main_entry U_mainleaf_openfail_defs U_mainleaf_openfail U_main_open_defs U_main_open.
Import ListNotations.
Open Scope bv_scope.
Import SX2. Import SX2S.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
Ltac2 gd_tbl_P_mainleaf_openfail_branch () : Init.string Init.list := ["RocqVerifyHarness.AgentSubmission.U.U_main_open.open_err_branch"; "RocqVerifyHarness.AgentSubmission.Spec.Spec.t_die"; "RocqVerifyHarness.AgentSubmission.Spec.Spec.msg_cannot_open"].

#[local] Existing Instance PropExec.fx0.

Section Branch.
  Context {AMB : Amb}.
  Context {LM : Lim}.
  Variable sp0 : word.
  Variables a0s path : list byte.
  Variable envv : list (list byte).
  Variable tid : word.
  Variable rd : EntryDraw.
  Variable regs0 : bvmap 5 word.
  Variable mem0 : word -> option byte.
  Variable brk : word.
  Variable mbase : word.
  Variable fs0 : Fs.
  Variable stdin0 : InputStream.
  Hypothesis Hva : valid_argv [a0s; path].
  Hypothesis Hve : valid_envp envv.
  Hypothesis Hvsp : valid_sp sp0.
  Hypothesis Htid : (0 < bv_unsigned tid < 2 ^ 22)%Z.
  Hypothesis ME : main_entry sp0 [a0s; path] envv tid rd regs0 mem0.

  #[using="rd regs0 Hva Hve Hvsp ME"] Theorem open_err_branch_cannot_open : ltac2:(CDefT.buildp (gd_tbl_P_mainleaf_openfail_branch ()) "(0.VAMB,VLM,Vsp0,Va0s,Vpath,Venvv,Vtid,Vmem0,Vbrk,Vmbase,Vfs0,Vstdin0,(1.(2.Vpath,)Vfs0,))")
(* [comment removed for export] *).
  Proof.
    intros e vals R M He HL P0 P38 P1 P2 P5 HR HK Habove.
    apply (U_mainleaf_openfail.ref_open_fail_errno sp0 a0s path envv tid rd regs0 mem0 brk mbase fs0 stdin0 LIM Hva Hve Hvsp ME
             e vals R M (openat_errnos_range e He) HL P0 P38 P2 HR HK Habove).
  Qed.
End Branch.

(* [comment removed for export] *)
