(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.Lib Require Import PropExec MState Mem Cells Step Frame Arr InitMem ITree Nodes.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.LibA Require Import ExecF ITreeA ModelX.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.Spec Require Import STree AsanCtrl AsanEmbed AsanProgDeps ProgA AsanHandoff.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.AS Require Import MainExport MainFactsAsan MainEntry.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib Require Import AsanMainU.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.AsanW Require Import AProto AImg ABase ABytes ALayout ARep AHeapP AQConst ARepQ AFake_iface AFake_init AFake_arep ADepot_iface ADepot ADepot_init F_adepot AMalloc_iface AU_iface AU_parts_iface AHarnessU_iface APoisonR_iface ADriver_iface Strnlen_iface Strnlen_proof AResv ASec AInstance ARepInit_A ARepInit ARepInit_S ARepInit_glue AMain_asm AD_target_run AD_handoff AIos_iface AExitU_kit AExitU_closed ATsafeMain.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.Common Require Import RunDraw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Set Keyed Unification.   (* [comment removed for export] *)
Section CANSEC0. Context {rc : runConstT} {XP : ExitParams}.
(* [comment removed for export] *)
Definition xp_chains_stmt : Prop :=
     wcrtomb0_stmt xp_ICPT xp_ICPTR xp_SLO xp_SHI
  /\ fwrite0_out_stmt xp_ICPT xp_ICPTR /\ fwrite0_err_stmt xp_ICPT xp_ICPTR
  /\ fflush_out_stmt xp_ICPT xp_ICPTR aps_so aset_so
  /\ fflush_out_stmt xp_ICPT xp_ICPTR (St := Stdio.stdout_st) (fun so => so) (fun so _ => so)
  /\ fflush_err_stmt xp_ICPT xp_ICPTR
  /\ xp_SLO <= ATOP + 4096 /\ ATOP + 8388608 <= xp_SHI.
End CANSEC0.

Section CANSEC1. Context {rc : runConstT}.
(* [comment removed for export] *)
Definition asan_client_at (AI : AMallocIface) : Prop := fuzz_oneU_stmt AI afake_rng /\ avdtor_stmt AI.

Section Closed.
  (* [comment removed for export] *)
  Let H : aholes := AFake_arep.AH adepot_iface AQUAR ASEC_of.     (* [comment removed for export] *)
  Let HL : ahole_laws H := AH_laws.                                (* [comment removed for export] *)
  Variable AI : AMallocIface.
  Hypothesis E : AHEAP AI = AHEAP_P H.
  Hypothesis CI_OK : forall iv, In iv (aci AI) -> 0 <= fst iv /\ snd iv <= AIMG_HI.
  Hypothesis DRV_CI : forall iv, In iv drv_img_ranges -> In iv (aci AI).
  Hypothesis URI_CI : forall iv, In iv uri_img_ranges -> In iv (aci AI).
  Hypothesis AI_chunk : forall L RNG st LB m p A n, AHEAP AI L RNG st LB m -> In (HB p A n) LB ->
    exists ch, (a_live st) !! p = Some ch /\ chunk_size ch = n /\ (is_primary n = false -> A = chunk_user_beg ch) /\ achunk_kind_ok ch n.
  Hypothesis AI_premap : forall L RNG st LB m, AHEAP AI L RNG st LB m -> premap_cells m.
  (* [comment removed for export] *)
  Hypothesis AI_lsan : forall L RNG st LB m, AHEAP AI L RNG st LB m -> rw_cells asegs m 0x6a4df8 [C4 (Z_to_bv 64 0)].
  Hypothesis AI_frame_lsan : forall L RNG st LB m m' W, AHEAP AI L RNG st LB m -> munch W m m' -> wmono asegs m m' ->
    Forall (fun iv => aclient_range (aci AI) LB (ATOP + 4096) (fst iv) (snd iv - fst iv) \/ iv = (0x6a4df8, 0x6a4dfc)) W ->
    rw_cells asegs m' 0x6a4df8 [C4 (Z_to_bv 64 0)] -> AHEAP AI L RNG st LB m'.
  Hypothesis EXIT_CI : forall iv, In iv exit_ci_need -> In iv (aci AI).
  Hypothesis CLIENT : asan_client_at AI.      (* [comment removed for export] *)
  Lemma UDRV_len : (length UDRV <= 4096)%nat.
  Proof. cbn. lia. Qed.
  Lemma UDRV_traces : Forall (fun u => (length u <= 254)%nat) UDRV.
  Proof. unfold UDRV. repeat constructor. Qed.

  (* [comment removed for export] *)
  Lemma aheap_init : aheap_init_stmt AI ATsafeMain.A0.
  Proof.
    intros en inp w V m ms mo HV HI HM HA. rewrite E. unfold H, AFake_arep.AH, LDRV.
    apply (aheapP_at_main ATsafeMain.A0 ATsafeMain.A0_init ATsafeMain.A0_win0 UDRV UDRV_len UDRV_traces ASEC_of en inp w V m ms mo HV HI HM HA).
    pose proof HM as (_ & _ & PIN & HMF & HPF & _ & _ & _ & SH0 & _). apply Forall_app in HMF as [HMF _]. apply Forall_app in HPF as [HPF _].
    assert (HAT : 32768 * V 0%nat + 4096 * V 10%nat + 16 * V 6%nat - 8388608 = ATOP).
    { destruct PIN as (_ & _ & _ & USP & _). rewrite USP. exact HA. }
    apply (ASEC_of_init V w UDRV m HMF HPF); first [exact HAT | exact SH0 | unfold AUMAX; cbn; lia].
  Qed.

  Lemma aresv_init : aresv_init_stmt.
  Proof.
    intros en inp w V m ms mo _ _ HM. pose proof HM as (_ & _ & _ & _ & HPF & _). apply Forall_app in HPF as [HPF _].
    apply aresv_ok_handoff. exact HPF.
  Qed.

  (* [comment removed for export] *)
  Section WithXP.
  Context {XP : ExitParams}.
  Hypothesis XCH : xp_chains_stmt.

  Lemma fuzz_oneU : fuzz_oneU_stmt AI afake_rng.
  Proof. exact (proj1 CLIENT). Qed.

  (* [comment removed for export] *)
  Lemma avdtor : avdtor_stmt AI.
  Proof. exact (proj2 CLIENT). Qed.

  Lemma trun : atarget_run_stmtA AI afake_rng.
  Proof.
    exact (atarget_run_proofA AI afake_rng afake_rng_mono DRV_CI URI_CI (fun iv Hiv => proj1 (CI_OK iv Hiv))
             (dmalloc_of_AI AI) (dfree_of_AI AI) (dfree_null_of_AI AI) (ashenv_law_holds AI) fuzz_oneU strnlen_a_proof).
  Qed.

  Lemma adrv_at : forall en inp w V m ms mo,
    valid_entry (mkImage asegs a_init_pc a_phdrs) en inp -> valid_input_either inp -> main_open en inp w V m ms mo ->
    atop_of (en_sp en) = ATOP ->
    xp_ICPT m -> xp_ICPTR (RNG0 ATsafeMain.A0 V mo) ->
    implS asegs (RNG0 ATsafeMain.A0 V mo)
          (progA_tree AAllocAsan (aps_init (a_space_beg0 V) (a_ptr_array0 V) (resv_of V) ATOP) ASTAGE (Prog.argv_Z (in_argv inp))) (epostF TT) ms.
  Proof.
    destruct XCH as (WCR & FW0 & FW0E & FFL & FFLS & FFLE & XSLO_H & XSHI_H).
    exact (adrv_closed_at AI afake_rng ATsafeMain.A0 ATsafeMain.A0_init aheap_init aresv_init (afake_rng_init _ ATsafeMain.A0_init)
             XSLO_H XSHI_H afake_rng_mono DRV_CI URI_CI (dmalloc_of_AI AI) (dfree_of_AI AI) strnlen_a_proof trun
             (aexit_closed AI DRV_CI EXIT_CI WCR FW0 FW0E FFL FFLS FFLE avdtor)).
  Qed.
  End WithXP.

  (* [comment removed for export] *)
  Variable XPf : Z -> ExitParams.
  Hypothesis XCHf : forall T, @xp_chains_stmt rc (XPf T).
  Hypothesis XP_INIT : xp_init_fam_stmt XPf ATsafeMain.A0.
  Lemma adrv : adrv_stmt ATsafeMain.A0.
  Proof.
    intros en inp w V m ms mo Hv Hi HM HA.
    destruct (XP_INIT en inp w V m ms mo Hv Hi HM HA) as [XI XR].
    exact (@adrv_at (XPf (XT V)) (XCHf (XT V)) en inp w V m ms mo Hv Hi HM HA XI XR).
  Qed.

  (* [comment removed for export] *)
  Lemma model_ok : progA_model_ok ATsafeMain.NMAX ATsafeMain.A0.
  Proof.
    intros en inp w V m ms mo _ _ HM HA. pose proof HM as (_ & _ & PIN & _ & HP & _ & _ & _ & _ & HMOD). apply Forall_app in HP as [HP _].
    assert (HAT : a_usp0 V - 8388608 = ATOP).
    { unfold a_usp0. destruct PIN as (_ & _ & _ & USP & _). rewrite USP. exact HA. }
    rewrite <- HA. exact (progA_tsafe_open ASTAGE V (en_sp en) inp mo HP HAT HA HMOD).
  Qed.
End Closed.
End CANSEC1.

(* [comment removed for export] *)
