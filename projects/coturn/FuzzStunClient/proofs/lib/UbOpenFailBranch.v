(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: for LPS 727298f3, the section and cannot_open_branch take the launch input, entry point, uid and hwcap of the 12-argument main_entry, the thread-id bound and the stderr write's channel reader. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.coturn.FuzzStunClient.images Require Import Ubsan.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib Require Import Amb.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common Require Import PropExec CatExec CatSim SeqExec StoreOk ShapeAlg SymExec.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib Require Import SymExec2 SymExec2Sound SymRun SymDrive SymDriveX Spec UbStartup UbMainEntry UbOpenFail_defs UbOpenFail UbPilotOOM_defs UbPilotOOM.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common Require Import WalkFast.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common Require Import WalkFastK.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common Require Import WalkFastS.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common Require Import WalkFastM.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib Require Import SumWalkFast.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Ltac OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common.WalkTac.gres ::= gres_fast.
#[local] Ltac OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common.WalkTac.vnorm ::= vnorm_fast.
#[local] Ltac OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common.StepTac.step_simpl ::= step_simpl_fast.
#[local] Ltac OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common.RefMemcpyLib.not_kept ::= not_kept_fast.
#[local] Ltac OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common.StartupTac.in_list ::= in_list_fast.
#[local] Ltac OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common.StartupTac.peel ::= peel_fast.
#[local] Ltac OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common.StoreOk.store_ok_peel ::= store_ok_peel_fast.
#[local] Ltac OSSVerify.Proofs.coturn.FuzzStunClient.lib.SumWalkTac.rdn_peel1 ::= rdn_peel1_fast.
(* [comment removed for export] *)
#[local] Existing Instance PropExec.fx0.  (* [comment removed for export] *)
Import ListNotations.
Open Scope bv_scope.
Import SX2. Import SX2S.

Section Branch.
  Context {AMB : Amb}.
  Variable sp0 : word.
  Variables a0s path : list byte.
  Variable envv : list (list byte).
  Variable rdraw : EntryDraw.   (* [comment removed for export] *)
  Variable tid : word.
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
  (* LPS 08b1429: the launch input, entry point, uid/hwcap and the 12-argument [main_entry], and
     the stderr write's channel reader (as in RefOpenFail / RefPilotOOM). *)
  Variable inp : ProcInput.
  Variable entry : word.
  Variables uid hw : word.
  Hypothesis ME : main_entry inp mbase entry sp0 [a0s; path] envv uid hw rdraw tid regs0 mem0.
  Hypothesis Hrdr0 : a_channel_reader = true.

  Theorem open_err_branch_cannot_open :
    UbPilotOOM.open_err_branch sp0 a0s path envv rdraw tid mem0 brk mbase fs0 stdin0 inp (t_die (msg_cannot_open path) fs0).
  Proof.
    intros e vals R M He HL P0 P38 P1 P2 P5 HR HK Habove.
    apply UbOpenFail.ref_open_fail_errno with (sp0 := sp0) (a0s := a0s) (path := path) (envv := envv) (rdraw := rdraw)
      (tid := tid) (regs0 := regs0) (mem0 := mem0) (brk := brk) (mbase := mbase) (fs0 := fs0) (stdin0 := stdin0)
      (lim := LIM) (inp := inp) (entry := entry) (uid := uid) (hw := hw) (e := e) (vals := vals) (R := R) (M := M);
      try eassumption.
    apply openat_errnos_range. exact He.
  Qed.
End Branch.

(* [comment removed for export] *)
Corollary cannot_open_branch {AMB : Amb} : forall (sp0 : word) (a0s : list byte) (envv : list (list byte)) (rdraw : EntryDraw) (tid : word)
    (regs0 : bvmap 5 word) (mem0 : word -> option byte) (brk mbase : word) (fs0 : Fs) (stdin0 : InputStream)
    (inp : ProcInput) (entry uid hw : word),
  valid_argv [a0s; dot_path] -> valid_envp envv -> valid_sp sp0 ->
  (* LPS 08b1429: UbMainEntry's register/knowledge facts take the tid bound (its callers,
     UbLeafDir and UbMain, hold it as [Htid]). *)
  (0 < bv_unsigned tid < 2 ^ 22)%Z ->
  main_entry inp mbase entry sp0 [a0s; dot_path] envv uid hw rdraw tid regs0 mem0 ->
  a_channel_reader = true ->
  open_err_branch sp0 a0s dot_path envv rdraw tid mem0 brk mbase fs0 stdin0 inp (t_die (msg_cannot_open dot_path) fs0).
Proof.
  intros sp0 a0s envv rdraw tid regs0 mem0 brk mbase fs0 stdin0 inp entry uid hw Hva Hve Hvsp Htid ME Hrdr0.
  apply open_err_branch_cannot_open with (regs0 := regs0) (inp := inp) (entry := entry) (uid := uid) (hw := hw);
    assumption.
Qed.
