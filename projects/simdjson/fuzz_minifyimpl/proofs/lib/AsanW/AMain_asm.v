(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.Common Require Import RunDraw.
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib Require Import TopLevel.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.Lib Require Import ITree Nodes InitMem RunConst.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.LibA Require Import ExecF AcctCore TopLevelGen ITreeA NodesA ModelX SysStepF.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.AS Require ShapeAlg SpinAlg.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.AS Require Import MainExport MainFactsAsan MainEntry.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.Spec Require Import Monad Stdio Driver Prog ProgA EquivZA AsanProgDeps RSim AsanInv AsanNodeSem AsanOK AsanHandoff.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.Plain Require Import PImg.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.AsanW Require Import AImg AProto AMalloc_iface AU_kit ADriver_iface H16_relimit.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.Spec Require Import ZSafe ModelZ HarnessM.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib Require Import AsanMainU.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.

(* [comment removed for export] *)
Set Keyed Unification.   (* [comment removed for export] *)
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
      main_open en inp w V m ms mo -> atop_of (en_sp en) = ATOP ->
      implS asegs (RNG0 V mo) (progA_tree AAllocAsan (aps_init (a_space_beg0 V) (a_ptr_array0 V) (resv_of V) ATOP) ASTAGE (argv_Z (in_argv inp)))
            (epostF TT) ms.

  (* [comment removed for export] *)
  Definition progA_model_ok {rc : runConstT} : Prop :=
    forall en inp w V m ms mo,
      valid_entry (mkImage asegs a_init_pc a_phdrs) en inp -> valid_input_either inp ->
      main_open en inp w V m ms mo -> atop_of (en_sp en) = ATOP ->
      tsafeA nstepA (nsafeA NMAX) fstepS NMAX (RNG0 V mo) (A0 V)
             (progA_tree AAllocAsan (aps_init (a_space_beg0 V) (a_ptr_array0 V) (resv_of V) ATOP) ASTAGE (argv_Z (in_argv inp))) (MX mo [])
      /\ tglob nstepA PhiA (progA_tree AAllocAsan (aps_init (a_space_beg0 V) (a_ptr_array0 V) (resv_of V) ATOP) ASTAGE (argv_Z (in_argv inp))) (MX mo []).

  (* [comment removed for export] *)
  Definition main_openL (L : Z) (en : ExecEntry) (inp : ProcInput) (w : bool) (V : nat -> Z) (m : word -> option byte)
      (ms : machine_state) (mo : Model) : Prop :=
    main_open en inp w V m ms (relimit target_alloc_limit mo) /\ amodelL L V (en_sp en) (in_fs inp) mo.

  Lemma main_atL_open : forall L, L <= target_alloc_limit -> forall en inp ms mo,
    amain_atL L en inp ms mo -> exists w V m, main_openL L en inp w V m ms mo.
  Proof.
    intros L HLT en inp ms mo (w & V & m & H). exists w, V, m.
    destruct H as (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10). split; [| exact H10].
    split; [exact H1|]. split; [exact H2|]. split; [exact H3|]. split; [exact H4|]. split; [exact H5|]. split; [exact H6|].
    split; [exact H7|]. split; [exact H8|]. split; [exact H9|]. exact (amodelL_relimit L target_alloc_limit V (en_sp en) (in_fs inp) mo H10 HLT).
  Qed.

  Definition progA_model_okL (L : Z) {rc : runConstT} : Prop :=
    forall en inp w V m ms mo,
      valid_entry (mkImage asegs a_init_pc a_phdrs) en inp -> valid_input_either inp ->
      main_openL L en inp w V m ms mo -> atop_of (en_sp en) = ATOP ->
      tsafeA nstepA (nsafeA NMAX) fstepS NMAX (RNG0 V mo) (A0 V)
             (progA_tree AAllocAsan (aps_init (a_space_beg0 V) (a_ptr_array0 V) (resv_of V) ATOP) ASTAGE (argv_Z (in_argv inp))) (MX mo [])
      /\ tglob nstepA PhiA (progA_tree AAllocAsan (aps_init (a_space_beg0 V) (a_ptr_array0 V) (resv_of V) ATOP) ASTAGE (argv_Z (in_argv inp))) (MX mo []).

  Definition impl_stmtL (L : Z) (rsA : Z) : Prop :=
    forall en inp w V m ms mo,
      valid_entry (mkImage asegs a_init_pc a_phdrs) en inp -> valid_input_either inp ->
      main_openL L en inp w V m ms mo ->
      exists NMAX RNG A Q,
        tree_atA asegs (at_nodeA asegs) nstepA minvA (nsafeA NMAX) fstepS NMAX RNG A
          (progA_tree AAllocAsan (aps_init (a_space_beg0 V) (a_ptr_array0 V) (resv_of V) (atop_of (en_sp en))) rsA (argv_Z (in_argv inp)))
          Q ms (MX mo []) mo
        /\ tglob nstepA PhiA
             (progA_tree AAllocAsan (aps_init (a_space_beg0 V) (a_ptr_array0 V) (resv_of V) (atop_of (en_sp en))) rsA (argv_Z (in_argv inp))) (MX mo []).

  (* [comment removed for export] *)
  Definition A0_init_stmt : Prop :=
    forall V (p : word), bv_unsigned p mod 4096 = 0 -> aallowed (allow_of ASHOFF V asan_vis) p -> A0 V p.

  (* [comment removed for export] *)
  Section Decomposed.
    Context {rc : runConstT}.
    Variable apat : alayout -> footprint -> ProcInput -> APS -> machine_state -> Prop.
    Hypothesis APAT : forall en inp w V m ms mo,
      valid_entry (mkImage asegs a_init_pc a_phdrs) en inp -> valid_input_either inp ->
      main_open en inp w V m ms mo -> atop_of (en_sp en) = ATOP ->
      exists L, apat L (RNG0 V mo) inp (aps_init (a_space_beg0 V) (a_ptr_array0 V) (resv_of V) ATOP) ms.
    (* [comment removed for export] *)
    Variable aatx : Z -> APS -> footprint -> machine_state -> Prop.
    Hypothesis AMAIN : forall L RNG inp s0 ms,
      apat L RNG inp s0 ms ->
      implMA RNG (main_model (ioA AAllocAsan) amalloc_M afree_M ASTAGE (alloc_initA AAllocAsan) (runA AAllocAsan)
                             (alloc_countA AAllocAsan) (argv_Z (in_argv inp))) s0
             (fun code s' RNG' ms' => aatx code s' RNG' ms') ms.
    Hypothesis AEXIT : forall code (s : APS) RNG ms (Q : Empty_set -> APS -> footprint -> machine_state -> Prop),
      aatx code s RNG ms -> implMA RNG (mbind (client_exitA AAllocAsan) (fun _ => exit_model (ioA AAllocAsan) code)) s Q ms.

    (* [comment removed for export] *)
    Lemma adrv_of_parts_at : forall inp V mo ms L,
      apat L (RNG0 V mo) inp (aps_init (a_space_beg0 V) (a_ptr_array0 V) (resv_of V) ATOP) ms ->
      implS asegs (RNG0 V mo) (progA_tree AAllocAsan (aps_init (a_space_beg0 V) (a_ptr_array0 V) (resv_of V) ATOP) ASTAGE (argv_Z (in_argv inp)))
            (epostF TT) ms.
    Proof.
      intros inp V mo ms L HP.
      unfold progA_tree. eapply implF_ebind.
      - (* [comment removed for export] *)
        unfold progA_main. apply (implMA_unfold _ _ _ (fun (_ : Empty_set) _ _ _ => True)). eapply implMA_bind.
        + exact (AMAIN L _ inp _ ms HP).
        + cbv beta. intros code s' RNG' ms' HE. apply AEXIT. exact HE.
      - intros [e ?] RNG' ms' _. destruct e.
    Qed.

    Lemma adrv_of_parts : adrv_stmt.
    Proof.
      unfold adrv_stmt. intros en inp w V m ms mo Hv Hi HM HA.
      destruct (APAT en inp w V m ms mo Hv Hi HM HA) as [L HP].
      exact (adrv_of_parts_at inp V mo ms L HP).
    Qed.
  End Decomposed.

  Hypothesis ADRV : forall rc : runConstT, @adrv_stmt rc.
  Hypothesis MODEL_OK : forall rc : runConstT, @progA_model_ok rc.
  Hypothesis A0_init : A0_init_stmt.

  (* [comment removed for export] *)
  Lemma valid_sp_of_entry : forall en inp, valid_entry (mkImage asegs a_init_pc a_phdrs) en inp -> valid_input_either inp -> valid_sp (en_sp en).
  Proof.
    intros [sp brk mb draw] inp Hv Hi. rewrite (valid_entry_either _ _ _ _ _ _ _ _ Hi) in Hv. destruct Hv as (Hsp & _). exact Hsp.
  Qed.

  Theorem asan_impl : impl_stmt ASTAGE.
  Proof.
    unfold impl_stmt. intros en inp w V m ms mo Hv Hi HM.
    set (rc := run_consts_of en (Z_to_bv 64 0) (valid_sp_of_entry en inp Hv Hi)).
    assert (HA : atop_of (en_sp en) = @ATOP rc) by reflexivity.
    exists NMAX, (RNG0 V mo), (A0 V), (epostF TT).
    pose proof HM as (_ & HV & _ & _ & HP & _ & _ & _ & _ & HMOD).
    apply Forall_app in HP as [HP _].
    rewrite HA.
    destruct (MODEL_OK rc en inp w V m ms mo Hv Hi HM HA) as [HTS HG]. pose proof HG as HG'. rewrite <- HA in HG'.
    split; [| exact HG'].
    split; [exact (ADRV rc en inp w V m ms mo Hv Hi HM HA)|].
    split. { (* [comment removed for export] *)
      rewrite <- HA. destruct (moZ0_ok inp) as (MZ & HZ & FdZ & FsZ).
      destruct (equiv_ZA_asan ASTAGE ASTAGE V (en_sp en) inp mo (moZ0 inp) Hi HMOD HP HG' MZ HZ FdZ FsZ
                  (progZ_no_leaf inp (moZ0 inp) ASTAGE Hi MZ HZ FdZ FsZ)) as [_ HL].
      exact HL. }
    split. { rewrite m_halted_MX. exact (am_halted _ _ _ _ HMOD). }
    split. { apply minvA_std_fds; [rewrite m_fds_MX; exact (am_fds _ _ _ _ HMOD) | reflexivity |].
             rewrite m_vmmaps_MX, (am_top _ _ _ _ HMOD). pose proof (am_usp _ _ _ _ HMOD). unfold sp_window_lo, sp_window_hi. lia. }
    split. { exact HTS. }
    (* [comment removed for export] *)
    change (MX mo []) with (canon mo). apply mrel_canon.
    - exact (am_mat_nodup _ _ _ _ HMOD).
    - intros p Hp. destruct (am_mat _ _ _ _ HMOD p Hp) as (Hal & _ & Hallow). apply A0_init; assumption.
  Qed.

  (* [comment removed for export] *)
  Hypothesis MODEL_OKL : forall L, LIMIT <= L -> forall rc : runConstT, @progA_model_okL L rc.

  Theorem implL_asm : forall L, LIMIT <= L <= target_alloc_limit -> impl_stmtL L ASTAGE.
  Proof.
    intros L [HLL HLT]. unfold impl_stmtL. intros en inp w V m ms mo Hv Hi [HM HMOD].
    set (rc := run_consts_of en (Z_to_bv 64 0) (valid_sp_of_entry en inp Hv Hi)).
    assert (HA : atop_of (en_sp en) = @ATOP rc) by reflexivity.
    exists NMAX, (RNG0 V mo), (A0 V), (epostF TT).
    pose proof HM as (_ & HV & _ & _ & HP & _).
    apply Forall_app in HP as [HP _].
    rewrite HA.
    destruct (MODEL_OKL L HLL rc en inp w V m ms mo Hv Hi (conj HM HMOD) HA) as [HTS HG]. pose proof HG as HG'. rewrite <- HA in HG'.
    split; [| exact HG'].
    split. { (* [comment removed for export] *)
      exact (ADRV rc en inp w V m ms (relimit target_alloc_limit mo) Hv Hi HM HA). }
    split. { rewrite <- HA. destruct (moZ0_ok inp) as (MZ & HZ & FdZ & FsZ).
      destruct (equiv_ZA_asanL L HLL ASTAGE ASTAGE V (en_sp en) inp mo (moZ0 inp) Hi HMOD HP HG' MZ HZ FdZ FsZ
                  (progZ_no_leaf inp (moZ0 inp) ASTAGE Hi MZ HZ FdZ FsZ)) as [_ HL].
      exact HL. }
    split. { rewrite m_halted_MX. exact (am_halted _ _ _ _ HMOD). }
    split. { apply minvA_std_fds; [rewrite m_fds_MX; exact (am_fds _ _ _ _ HMOD) | reflexivity |].
             rewrite m_vmmaps_MX, (am_top _ _ _ _ HMOD). pose proof (am_usp _ _ _ _ HMOD). unfold sp_window_lo, sp_window_hi. lia. }
    split. { exact HTS. }
    change (MX mo []) with (canon mo). apply mrel_canon.
    - exact (am_mat_nodup _ _ _ _ HMOD).
    - intros p Hp. destruct (am_mat _ _ _ _ HMOD p Hp) as (Hal & _ & Hallow). apply A0_init; assumption.
  Qed.
End Asm.
