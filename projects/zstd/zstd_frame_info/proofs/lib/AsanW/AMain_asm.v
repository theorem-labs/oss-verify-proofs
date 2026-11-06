(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.Common Require Import RunDraw.
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib Require Import TopLevel.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.Lib Require Import ITree Nodes InitMem RunConst.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.LibA Require Import ExecF AcctCore TopLevelGen ITreeA NodesA ModelX SysStepF.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.AS Require ShapeAlg SpinAlg.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.AS Require Import MainExport MainFactsAsan MainEntry.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.Spec Require Import Monad Stdio Driver Prog ProgA EquivPA AsanProgDeps AsanOK AsanHandoff.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.Plain Require Import PImg.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib.AsanW Require Import AImg AProto AMalloc_iface AProg_kit ADriver_iface.
From OSSVerify.Proofs.zstd.zstd_frame_info.lib Require Import AsanMain.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.

(* [comment removed for export] *)
Definition TT : unit -> footprint -> machine_state -> Prop := fun _ _ _ => True.

Section Asm.
  (* [comment removed for export] *)
  Variable NMAX : nat.
  Variable A0 : (nat -> Z) -> alw.

  (* [comment removed for export] *)
  Definition RNG0 (V : nat -> Z) (mo : Model) : footprint := fp_ok (m_vm_lazy (MX mo [])) (A0 V).

  (* [comment removed for export] *)
  Definition adrv_stmt {rc : runConstT} : Prop :=
    forall en inp w V m ms mo,
      valid_entry (mkImage asegs a_init_pc a_phdrs) en inp -> valid_input_either inp ->
      amain_open en inp w V m ms mo -> atop_of (en_sp en) = ATOP ->
      implS asegs (RNG0 V mo) (progA_tree AAllocAsan (aps_init (a_space_beg0 V) (a_ptr_array0 V) (resv_of V) ATOP) ASTAGE (argv_Z (in_argv inp)))
            (epostF TT) ms.

  (* [comment removed for export] *)
  Definition progA_model_ok {rc : runConstT} : Prop :=
    forall en inp w V m ms mo,
      valid_entry (mkImage asegs a_init_pc a_phdrs) en inp -> valid_input_either inp ->
      amain_open en inp w V m ms mo -> atop_of (en_sp en) = ATOP ->
      tsafeA nstepA (nsafeA NMAX) fstepS NMAX (RNG0 V mo) (A0 V)
             (progA_tree AAllocAsan (aps_init (a_space_beg0 V) (a_ptr_array0 V) (resv_of V) ATOP) ASTAGE (argv_Z (in_argv inp))) (MX mo []).

  (* [comment removed for export] *)
  Definition A0_init_stmt : Prop :=
    forall V (p : word), bv_unsigned p mod 4096 = 0 -> aallowed (allow_of ASHOFF V asan_vis) p -> A0 V p.

  (* [comment removed for export] *)
  Section Decomposed.
    Context {rc : runConstT}.
    Variable apat : alayout -> footprint -> ProcInput -> APS -> machine_state -> Prop.
    Hypothesis APAT : forall en inp w V m ms mo,
      valid_entry (mkImage asegs a_init_pc a_phdrs) en inp -> valid_input_either inp ->
      amain_open en inp w V m ms mo -> atop_of (en_sp en) = ATOP ->
      exists L, apat L (RNG0 V mo) inp (aps_init (a_space_beg0 V) (a_ptr_array0 V) (resv_of V) ATOP) ms.
    Hypothesis AMAIN : forall L RNG inp s0 ms,
      apat L RNG inp s0 ms ->
      implMA RNG (main_model (ioA AAllocAsan) amalloc_M afree_M ASTAGE (alloc_initA AAllocAsan) (runA AAllocAsan)
                             (alloc_countA AAllocAsan) (argv_Z (in_argv inp))) s0
             (fun code s' RNG' ms' => aat_exit code s' RNG' ms') ms.

    #[using="apat APAT AMAIN"] Lemma adrv_of_parts : adrv_stmt.
    Proof.
      unfold adrv_stmt. intros en inp w V m ms mo Hv Hi HM HA.
      destruct (APAT en inp w V m ms mo Hv Hi HM HA) as [L HP].
      unfold progA_tree. eapply implF_ebind.
      - (* [comment removed for export] *)
        unfold progA_main. apply (implMA_unfold _ _ _ (fun (_ : Empty_set) _ _ _ => True)). eapply implMA_bind.
        + exact (AMAIN L _ inp _ ms HP).
        + cbv beta. intros code s' RNG' ms' HE. apply aexit_from_aat_exit. exact HE.
      - intros [e ?] RNG' ms' _. destruct e.
    Qed.
  End Decomposed.

  Hypothesis ADRV : forall rc : runConstT, @adrv_stmt rc.
  Hypothesis MODEL_OK : forall rc : runConstT, @progA_model_ok rc.
  Hypothesis A0_init : A0_init_stmt.

  (* [comment removed for export] *)
  #[using="Type"] Lemma valid_sp_of_entry : forall en inp, valid_entry (mkImage asegs a_init_pc a_phdrs) en inp -> valid_input_either inp -> valid_sp (en_sp en).
  Proof.
    intros [sp brk mb draw] inp Hv Hi. rewrite (valid_entry_either _ _ _ _ _ _ _ _ Hi) in Hv. destruct Hv as (Hsp & _). exact Hsp.
  Qed.

  #[using="NMAX A0 ADRV MODEL_OK A0_init"] Theorem asan_impl : asan_impl_stmt ASTAGE.
  Proof.
    unfold asan_impl_stmt. intros en inp w V m ms mo Hv Hi HM.
    set (rc := run_consts_of en (Z_to_bv 64 0) (valid_sp_of_entry en inp Hv Hi)).
    assert (HA : atop_of (en_sp en) = @ATOP rc) by reflexivity.
    exists NMAX, (RNG0 V mo), (A0 V), (epostF TT).
    pose proof HM as (_ & HV & _ & _ & HP & _ & _ & _ & _ & [HLIM HMOD]).   (* [comment removed for export] *)
    apply Forall_app in HP as [HP _].
    rewrite HA.
    split; [exact (ADRV rc en inp w V m ms mo Hv Hi HM HA)|].
    split. { (* [comment removed for export] *)
      rewrite <- HA. destruct (equiv_PA_asan_toP_LL (vm_limit (m_vmmaps mo)) HLIM source_alloc_limit ltac:(vm_compute; discriminate)
                                 PREAD_STAGE ASTAGE V (en_sp en) _ _ _ en inp mo Hv Hi HMOD HP) as [_ HL].
      exact HL. }
    split. { rewrite m_halted_MX. exact (amL_halted _ _ _ _ _ HMOD). }
    split. { apply minvA_std_fds; [rewrite m_fds_MX; exact (amL_fds _ _ _ _ _ HMOD) | reflexivity |].
             rewrite m_vmmaps_MX, (amL_top _ _ _ _ _ HMOD). pose proof (amL_usp _ _ _ _ _ HMOD). unfold sp_window_lo, sp_window_hi. Local Ltac2 Set LiaHints.tbl := fun () => "0010>44775902271.22000003S1H".
lia. }
    split. { exact (MODEL_OK rc en inp w V m ms mo Hv Hi HM HA). }
    (* [comment removed for export] *)
    change (MX mo []) with (canon mo). apply mrel_canon.
    - exact (amL_mat_nodup _ _ _ _ _ HMOD).
    - intros p Hp. destruct (amL_mat _ _ _ _ _ HMOD p Hp) as (Hal & _ & Hallow). apply A0_init; assumption.
  Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
End Asm.
