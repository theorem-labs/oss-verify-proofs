(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.openssl.hashtable.lib Require Import ModelAmb.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OssFuzzTheorems.openssl.hashtable.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.openssl.hashtable.lib Require Import
  PropExec CatExec CatSim SeqExec StoreOk ShapeAlg
  SymExec SymExec2 SymExec2Sound SymRun SymDrive SymDriveX
  Spec HUStartup HUMainEntry HUMainEntryX HUOpenFail_defs HUOpenFail HUPilotOOM_defs HUPilotOOM.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
From OssFuzzTheorems.Proofs.openssl.hashtable.lib Require Import ConeCfg.   (* [comment removed for export] *)
Import ListNotations.
Import ConeCfg.
Open Scope bv_scope.
Import SX2. Import SX2S.
Import ConeCfg.

(* [comment removed for export] *)
Lemma kn_exec_shared : HUMainEntryX.kn_exec = HUPilotOOM_defs.kn_exec. Proof. reflexivity. Qed.
Lemma srA_shared : HUOpenFail_defs.srA = HUPilotOOM_defs.srA. Proof. reflexivity. Qed.
Lemma knA_shared : HUOpenFail_defs.knA = HUPilotOOM_defs.knA. Proof. reflexivity. Qed.

Section Branch.
  Variable sp0 : word.
  Variables a0s path : list byte.
  Variable envv : list (list byte).
  Variables uid hw : word.
  Variable rdraw : EntryDraw.
  Variable tid : word.
  Variable regs0 : bvmap 5 word.
  Variable mem0 : word -> option byte.
  Variable brk : word.
  Variable mbase : word.
  Variable fs0 : Fs.
  Variable stdin0 : AmbIn.
  Variable lim : Z.                              (* [comment removed for export] *)
  Hypothesis Hva : valid_argv [a0s; path].
  Hypothesis Hve : valid_envp envv.
  Hypothesis Hvsp : valid_sp sp0.
  Hypothesis Hfits : entry_stack_fits sp0 [a0s; path] envv.
  Hypothesis Htid : (0 < bv_unsigned tid < 2 ^ 22)%Z.
  Hypothesis ME : main_entry sp0 [a0s; path] envv uid hw rdraw tid regs0 mem0.

  Theorem open_err_branch_cannot_open :
    HUPilotOOM.open_err_branch sp0 a0s path envv rdraw tid mem0 brk mbase fs0 stdin0 lim (t_die (msg_cannot_open path) fs0).
  Proof.
    intros e vals R M He HL P0 P41 P1 P2 P5 HR HK Habove.
    apply (HUOpenFail.ref_open_fail_errno sp0 a0s path envv uid hw rdraw tid regs0 mem0 brk mbase fs0 stdin0 lim Hva Hve Hvsp Hfits ME
             e vals R M (openat_errnos_range e He) HL P0 P41 P2 HR HK Habove).
  Qed.
End Branch.

(* [comment removed for export] *)
Corollary cannot_open_branch : forall (sp0 : word) (a0s : list byte) (envv : list (list byte)) (uid hw : word)
    (rdraw : EntryDraw) (tid : word) (regs0 : bvmap 5 word) (mem0 : word -> option byte) (brk mbase : word) (fs0 : Fs) (stdin0 : AmbIn) (lim : Z),
  valid_argv [a0s; dot_path] -> valid_envp envv -> valid_sp sp0 -> entry_stack_fits sp0 [a0s; dot_path] envv ->
  main_entry sp0 [a0s; dot_path] envv uid hw rdraw tid regs0 mem0 ->
  open_err_branch sp0 a0s dot_path envv rdraw tid mem0 brk mbase fs0 stdin0 lim (t_die (msg_cannot_open dot_path) fs0).
Proof.
  intros sp0 a0s envv uid hw rdraw tid regs0 mem0 brk mbase fs0 stdin0 lim Hva Hve Hvsp Hfits ME.
  exact (open_err_branch_cannot_open sp0 a0s dot_path envv uid hw rdraw tid regs0 mem0 brk mbase fs0 stdin0 lim Hva Hve Hvsp Hfits ME).
Qed.
