(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib Require Import ModelAmb.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib Require Import ImgP.
From OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib Require Import RefStartupDefs.   (* [comment removed for export] *)
From OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib Require Import
  PropExec CatExec CatSim SeqExec StoreOk ShapeAlg
  SymExec SymExec2 SymExec2Sound SymRun SymDrive SymDriveX
  Spec RefStartup RefMainEntry RefOpenFail_defs RefOpenFail RefPilotOOM_defs RefPilotOOM RefLim.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.
Import SX2. Import SX2S.
Section FPW_1. Context {fx : PropExec.FPState}.


Section Branch.
  Context {AL : AllocLim}.
  Variable sp0 : word.
  Variables a0s path : list byte.
  Variable envv : list (list byte).
  Variable uid : word.   (* [comment removed for export] *)
  Variable hw : word.    (* [comment removed for export] *)
  Variable rdraw : EntryDraw.   (* [comment removed for export] *)
  Variable tid : word.
  Variable regs0 : bvmap 5 word.
  Variable mem0 : word -> option byte.
  Variable brk : word.
  Variable mbase : word.
  Variable fs0 : Fs.
  Variable stdin0 : AmbIn.
  Hypothesis Hva : valid_argv [a0s; path].
  Hypothesis Hve : valid_envp envv.
  Hypothesis Hvsp : valid_sp sp0.
  Hypothesis Hfits : entry_stack_fits sp0 [a0s; path] envv.   (* [comment removed for export] *)
  Hypothesis ME : main_entry sp0 [a0s; path] envv uid hw rdraw tid regs0 mem0.

  (* [comment removed for export] *)
  Theorem open_err_branch_cannot_open :
    RefPilotOOM.open_err_branch sp0 a0s path envv rdraw tid mem0 brk mbase fs0 stdin0 (t_die (msg_cannot_open path) fs0).
  Proof.
    intros e vals R M He HL P0 P38 P1 P2 P5 P6 P7 HR HK Habove.
    pose proof (openat_errnos_range e He) as Her.
    apply (RefOpenFail.ref_open_fail_errno sp0 a0s path envv uid hw rdraw tid regs0 mem0 brk mbase fs0 stdin0 LIM Hva Hve Hvsp Hfits ME
             e vals R M Her HL P0 P38 P2 HR HK Habove).
  Qed.
End Branch.

(* [comment removed for export] *)
Corollary cannot_open_branch {AL : AllocLim} : forall (sp0 : word) (a0s : list byte) (envv : list (list byte)) (uid hw : word) (rdraw : EntryDraw) (tid : word)
    (regs0 : bvmap 5 word) (mem0 : word -> option byte) (brk mbase : word) (fs0 : Fs) (stdin0 : AmbIn),
  valid_argv [a0s; dot_path] -> valid_envp envv -> valid_sp sp0 -> entry_stack_fits sp0 [a0s; dot_path] envv ->
  main_entry sp0 [a0s; dot_path] envv uid hw rdraw tid regs0 mem0 ->
  open_err_branch sp0 a0s dot_path envv rdraw tid mem0 brk mbase fs0 stdin0 (t_die (msg_cannot_open dot_path) fs0).
Proof.
  intros sp0 a0s envv uid hw rdraw tid regs0 mem0 brk mbase fs0 stdin0 Hva Hve Hvsp Hfits ME.
  exact (open_err_branch_cannot_open sp0 a0s dot_path envv uid hw rdraw tid regs0 mem0 brk mbase fs0 stdin0 Hva Hve Hvsp Hfits ME).
Qed.

End FPW_1.
