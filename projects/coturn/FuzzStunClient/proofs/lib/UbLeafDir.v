(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
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
  (* [comment removed for export] *)
  Hypothesis cannot_open_branch : forall (sp0 : word) (a0s : list byte) (envv : list (list byte)) (rdraw : EntryDraw) (tid : word)
      (regs0 : bvmap 5 word) (mem0 : word -> option byte) (brk mbase : word) (fs0 : Fs) (stdin0 : InputStream),
    valid_argv [a0s; dot_path] -> valid_envp envv -> valid_sp sp0 ->
    main_entry sp0 [a0s; dot_path] envv rdraw tid regs0 mem0 ->
    open_err_branch sp0 a0s dot_path envv tid mem0 brk mbase fs0 stdin0 (t_die (msg_cannot_open dot_path) fs0).

(* [comment removed for export] *)
Lemma ref_dir_path : forall (sp0 : word) (a0s : list byte) (envv : list (list byte)) (rdraw : EntryDraw) (tid : word)
    (regs0 : bvmap 5 word) (mem0 : word -> option byte) (brk mbase : word) (fs0 : Fs) (stdin0 : InputStream),
  valid_argv [a0s; dot_path] -> valid_envp envv -> valid_sp sp0 -> (0 < bv_unsigned tid < 2 ^ 22)%Z ->
  main_entry sp0 [a0s; dot_path] envv rdraw tid regs0 mem0 -> valid_brk RSEGS brk ->
  realizes RSEGS (mkCfg (mkst regs0 (0x13ac0 : word) mem0 (seg_rom RSEGS))
                          (with_tid tid (init_model (segments_reserved RSEGS) brk mbase sp0 LIM (mkProcInputC [a0s; dot_path] envv fs0 stdin0))))
             (t_alt2 (t_die (msg_cannot_open dot_path) fs0) (t_opened_dir dot_path fs0)).
Proof.
  intros sp0 a0s envv rdraw tid regs0 mem0 brk mbase fs0 stdin0 Hva Hve Hvsp Htid ME Hbrk.
  set (K := t_die (msg_read_error dot_path) fs0).
  assert (AM : after_malloc_dir sp0 a0s envv tid mem0 fs0 stdin0 K).
  { apply (dir_read sp0 a0s envv tid mem0 fs0 stdin0 Hvsp Htid). intros R' M' VM' P. subst K.
    change fs0 with (m_fs (modelDir tid fs0 stdin0 VM')).
    apply (dir_tail sp0 a0s envv rdraw tid regs0 mem0 Hva Hve Hvsp ME R' M' (modelDir tid fs0 stdin0 VM') eq_refl eq_refl eq_refl P). }
  eapply rz_conseq; [ | apply teq_pilot_dir ].
  replace (0x13ac0 : word) with (Z_to_bv 64 0x13ac0) by (apply bv_eq; reflexivity).
  change (with_tid tid (init_model (segments_reserved RSEGS) brk mbase sp0 LIM (mkProcInputC [a0s; dot_path] envv fs0 stdin0)))
    with (model0 sp0 a0s dot_path envv tid brk mbase fs0 stdin0).
  apply (dir_seg1 sp0 a0s envv rdraw tid regs0 mem0 brk mbase fs0 stdin0 Hva Hve Hvsp Htid ME).
  - apply (cannot_open_branch sp0 a0s envv rdraw tid regs0 mem0 brk mbase fs0 stdin0 Hva Hve Hvsp ME).
  - unfold dir_seg2_kont. intros vals R M HL P0 P1 P2 P5 HR HK HA.
    change (modelD1 sp0 tid brk mbase fs0 stdin0) with (model1g sp0 tid brk mbase fs0 stdin0 FdDir).
    apply (oom_seg2 sp0 a0s dot_path envv tid mem0 brk mbase fs0 stdin0 Hvsp Hbrk ltac:(cbn; lia) FdDir
             (t_alt2 (t_die msg_oom fs0) K)
             (t_alt2 (t_die msg_oom fs0) (t_alt2 (t_die msg_oom fs0) K))
             vals R M
             (dir_brk sp0 a0s envv rdraw tid mem0 brk mbase fs0 stdin0 Hva Hve Hvsp Htid Hbrk K AM)
             (dir_mmap sp0 a0s envv rdraw tid mem0 brk mbase fs0 stdin0 Hva Hve Hvsp Htid Hbrk K AM)
             HL P0 P1 P2 P5 HR HK HA).
Qed.
End LeafDir.
