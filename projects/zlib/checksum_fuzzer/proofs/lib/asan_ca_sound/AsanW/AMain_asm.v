(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.asan_ca_sound.Common Require Import RunDraw.
From Stdlib Require Import ZArith List Lia.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.asan_ca_sound Require Import TopLevel.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.asan_ca_sound.Lib Require Import ITree Nodes InitMem RunConst.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.asan_ca_sound.LibA Require Import ExecF AcctCore TopLevelGen ITreeA NodesA ModelX SysStepF.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.asan_ca_sound.AS Require ShapeAlg SpinAlg.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.asan_ca_sound.AS Require Import MainExport MainFactsAsan MainEntry.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.asan_ca_sound.Spec Require Import Monad Stdio Driver Prog ProgA EquivPA AsanProgDeps AsanOK AsanHandoff.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.asan_ca_sound.Plain Require Import PImg.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.asan_ca_sound.AsanW Require Import AImg AProto AMalloc_iface AUri_kit ADriver_iface.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.asan_ca_sound.AsanW Require AF_atexit_proof.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.asan_ca_sound Require Import AsanMain.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.

Definition TT : unit -> footprint -> machine_state -> Prop := fun _ _ _ => True.

Section Asm.
  Variable NMAX : nat.
  Variable A0 : (nat -> Z) -> alw.

  Definition RNG0 (V : nat -> Z) (mo : Model) : footprint := fp_ok (m_vm_lazy (MX mo [])) (A0 V).

  Definition adrv_stmt {rc : runConstT} : Prop :=
    forall en inp w V m ms mo,
      valid_entry (mkImage asegs a_init_pc a_phdrs) en inp -> valid_input_either inp ->
      amain_open en inp w V m ms mo -> atop_of (en_sp en) = ATOP ->
      implS asegs (RNG0 V mo) (progA_tree AAllocAsan (aps_init (a_space_beg0 V) (a_ptr_array0 V) (resv_of V) ATOP) ASTAGE (argv_Z (in_argv inp)))
            (epostF TT) ms.

  Definition progA_model_ok {rc : runConstT} : Prop :=
    forall en inp w V m ms mo,
      valid_entry (mkImage asegs a_init_pc a_phdrs) en inp -> valid_input_either inp ->
      amain_open en inp w V m ms mo -> atop_of (en_sp en) = ATOP ->
      tsafeA nstepA (nsafeA NMAX) fstepS NMAX (RNG0 V mo) (A0 V)
             (progA_tree AAllocAsan (aps_init (a_space_beg0 V) (a_ptr_array0 V) (resv_of V) ATOP) ASTAGE (argv_Z (in_argv inp))) (MX mo []).

  Definition A0_init_stmt : Prop :=
    forall V (p : word), bv_unsigned p mod 4096 = 0 -> aallowed (allow_of ASHOFF V asan_vis) p -> A0 V p.

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

    Lemma adrv_of_parts : adrv_stmt.
    Proof.
      unfold adrv_stmt. intros en inp w V m ms mo Hv Hi HM HA.
      destruct (APAT en inp w V m ms mo Hv Hi HM HA) as [L HP].
      unfold progA_tree. eapply implF_ebind.
      -
        unfold progA_main. apply (implMA_unfold _ _ _ (fun (_ : Empty_set) _ _ _ => True)). eapply implMA_bind.
        + exact (AMAIN L _ inp _ ms HP).
        + cbv beta. intros code s' RNG' ms' HE. apply (aexit_from_aat_exit AF_atexit_proof.funcs_on_exit_proofA). exact HE.
      - intros [e ?] RNG' ms' _. destruct e.
    Qed.
  End Decomposed.

  Hypothesis ADRV : forall rc : runConstT, @adrv_stmt rc.
  Hypothesis MODEL_OK : forall rc : runConstT, @progA_model_ok rc.
  Hypothesis A0_init : A0_init_stmt.

  Lemma valid_sp_of_entry : forall en inp, valid_entry (mkImage asegs a_init_pc a_phdrs) en inp -> valid_input_either inp -> valid_sp (en_sp en).
  Proof.
    intros [sp brk mb draw] inp Hv Hi. rewrite (valid_entry_either _ _ _ _ _ _ _ _ Hi) in Hv. destruct Hv as (Hsp & _). exact Hsp.
  Qed.

  Theorem asan_impl : asan_impl_stmt ASTAGE.
  Proof.
    unfold asan_impl_stmt. intros en inp w V m ms mo Hv Hi HM.
    set (rc := run_consts_of en (Z_to_bv 64 0) (valid_sp_of_entry en inp Hv Hi)).
    assert (HA : atop_of (en_sp en) = @ATOP rc) by reflexivity.
    exists NMAX, (RNG0 V mo), (A0 V), (epostF TT).
    (* amain_open gains the argv-facts conjunct (AS/MainEntry , batch 4 row e) *)
    pose proof HM as (_ & HV & _ & _ & HP & _ & _ & _ & _ & _ & HMOD).
    apply Forall_app in HP as [HP _].
    rewrite HA.
    split; [exact (ADRV rc en inp w V m ms mo Hv Hi HM HA)|].
    split. {
      rewrite <- HA. destruct (equiv_PA_asan_toP (2^31) ltac:(lia) PREAD_STAGE ASTAGE V (en_sp en) _ _ _ en inp mo Hv Hi HMOD HP) as [_ HL].
      exact HL. }
    split. { rewrite m_halted_MX. exact (am_halted _ _ _ _ HMOD). }
    (* minvA_std_fds also takes the channel reader (minv's last conjunct): amodel's am_rdr *)
    split. { apply minvA_std_fds; [rewrite m_fds_MX; exact (am_fds _ _ _ _ HMOD) | reflexivity | | exact (am_rdr _ _ _ _ HMOD)].
             rewrite m_vmmaps_MX, (am_top _ _ _ _ HMOD). pose proof (am_usp _ _ _ _ HMOD). unfold sp_window_lo, sp_window_hi. lia. }
    split. { exact (MODEL_OK rc en inp w V m ms mo Hv Hi HM HA). }
    change (MX mo []) with (canon mo). apply mrel_canon.
    - exact (am_mat_nodup _ _ _ _ HMOD).
    - intros p Hp. destruct (am_mat _ _ _ _ HMOD p Hp) as (Hal & _ & Hallow). apply A0_init; assumption.
  Qed.
End Asm.
