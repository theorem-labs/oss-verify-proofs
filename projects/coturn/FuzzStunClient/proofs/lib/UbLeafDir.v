(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: for LPS 727298f3, the section and ref_dir_path take the launch input, entry point, uid and hwcap of the 12-argument main_entry, the thread-id bound and the stderr writes' channel reader, and the out-of-memory branch takes the auxv base. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.coturn.FuzzStunClient.images Require Import Ubsan.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib Require Import Amb.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common Require Import PropExec CatExec CatSim SeqExec StoreOk ShapeAlg SymExec.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib Require Import SymExec2 SymExec2Sound SymRun SymDrive SymDriveX Spec UbStartup UbMainEntry UbReadBase UbWorld UbPilotOOM_defs UbPilotOOM UbDirTail UbDirFront UbDirMid.
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

Lemma teq_pilot_dir : forall A O K : TSet,
  t_eq (t_alt2 A (t_alt2 (t_alt2 O (t_alt2 O (t_alt2 O K))) (t_alt2 O K))) (t_alt2 A (t_alt2 O K)).
Proof. intros A O K tr. unfold t_alt2. tauto. Qed.

Section LeafDir.
  Context {AMB : Amb}.
(* Twin of RefLeafDir.v; the two
   differ only in Plain/Ubsan, the Ref*/Ub* imports, the missing AllocLim context and the pc
   constant 0x139e0/0x13ac0.  [cannot_open_branch] is stated exactly as
   UbOpenFailBranch.cannot_open_branch (UbOpenFailBranch.v:75-84), which UbMain passes for it. *)
  Hypothesis cannot_open_branch : forall (sp0 : word) (a0s : list byte) (envv : list (list byte)) (rdraw : EntryDraw) (tid : word)
      (regs0 : bvmap 5 word) (mem0 : word -> option byte) (brk mbase : word) (fs0 : Fs) (stdin0 : InputStream)
      (inp : ProcInput) (entry uid hw : word),
    valid_argv [a0s; dot_path] -> valid_envp envv -> valid_sp sp0 ->
    (0 < bv_unsigned tid < 2 ^ 22)%Z ->
    main_entry inp mbase entry sp0 [a0s; dot_path] envv uid hw rdraw tid regs0 mem0 ->
    a_channel_reader = true ->
    open_err_branch sp0 a0s dot_path envv rdraw tid mem0 brk mbase fs0 stdin0 inp (t_die (msg_cannot_open dot_path) fs0).

(* [comment removed for export] *)
Lemma ref_dir_path : forall (sp0 : word) (a0s : list byte) (envv : list (list byte)) (rdraw : EntryDraw) (tid : word)
    (regs0 : bvmap 5 word) (mem0 : word -> option byte) (brk mbase : word) (fs0 : Fs) (stdin0 : InputStream)
    (inp : ProcInput) (entry uid hw : word),
  valid_argv [a0s; dot_path] -> valid_envp envv -> valid_sp sp0 -> (0 < bv_unsigned tid < 2 ^ 22)%Z ->
  main_entry inp mbase entry sp0 [a0s; dot_path] envv uid hw rdraw tid regs0 mem0 ->
  a_channel_reader = true ->
  valid_brk RSEGS brk ->
  realizes RSEGS (mkCfg (mkst regs0 (0x13ac0 : word) mem0 (seg_rom RSEGS))
                          (with_tid tid (init_model (segments_reserved RSEGS) brk mbase sp0 LIM (mkProcInputC [a0s; dot_path] envv fs0 stdin0))))
             (t_alt2 (t_die (msg_cannot_open dot_path) fs0) (t_opened_dir dot_path fs0)).
Proof.
  intros sp0 a0s envv rdraw tid regs0 mem0 brk mbase fs0 stdin0 inp entry uid hw
         Hva Hve Hvsp Htid ME Hrdr0 Hbrk.
  set (K := t_die (msg_read_error dot_path) fs0).
  (* Section lemmas by [eapply] and [eassumption], never a positional list, for the reason the
     Ref twin records. *)
  assert (AM : after_malloc_dir sp0 a0s envv rdraw tid mem0 mbase fs0 stdin0 inp K).
  { eapply dir_read; try eassumption.
    intros R' M' VM' P. subst K.
    change fs0 with (m_fs (modelDir tid fs0 stdin0 VM')).
    eapply dir_tail; try eassumption; try reflexivity. }
  eapply rz_conseq; [ | apply teq_pilot_dir ].
  replace (0x13ac0 : word) with (Z_to_bv 64 0x13ac0) by (apply bv_eq; reflexivity).
  change (with_tid tid (init_model (segments_reserved RSEGS) brk mbase sp0 LIM (mkProcInputC [a0s; dot_path] envv fs0 stdin0)))
    with (model0 sp0 a0s dot_path envv tid brk mbase fs0 stdin0).
  (* [dir_seg1] leaves its two continuations: the openat error branch, then [dir_seg2_kont]. *)
  eapply dir_seg1; try eassumption.
  1: eapply cannot_open_branch; eassumption.
  (* [oom_seg2] asks the auxv base [vals_ev vals 3 = auxvp ..] since LPS 08b1429/75d69e00;
     [dir_seg2_kont] hands it over as [P3] (UbDirFront.v:96-97). *)
  unfold dir_seg2_kont. intros vals R M HL P0 P1 P2 P5 P3 HR HK HA.
  change (modelD1 sp0 tid brk mbase fs0 stdin0) with (model1g sp0 tid brk mbase fs0 stdin0 FdDir).
  eapply oom_seg2; try eassumption; try (cbn; lia).
  1: eapply dir_brk; eassumption.
  eapply dir_mmap; eassumption.
Qed.
End LeafDir.
