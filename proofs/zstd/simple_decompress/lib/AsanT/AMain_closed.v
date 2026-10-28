(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Lib Require Import PropExec MState Mem Cells Step Frame Arr InitMem ITree Nodes.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.LibA Require Import ExecF ITreeA ModelX.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Spec Require Import STree AsanCtrl AsanEmbed AsanProgDeps ProgA AsanHandoff.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.AS Require Import MainExport MainFactsAsan MainEntryAsan.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib Require Import AsanMain.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.AsanT Require Import BImg ABase ABytes ALayout ARep AHeapP AQConst ARepQ AFake_iface AFake_init AFake_arep
     ADepot_iface ADepot ADepot_init F_adepot AMalloc_iface AHarness_iface APoisonR_iface ADriver_iface Strnlen_iface Strnlen_proof
     AResv ASec AInstance ARepInit_A ARepInit ARepInit_S ARepInit_glue AMain_asm AD_handoff ATsafeMain.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import RunDraw.
Import ListNotations.
Open Scope Z_scope.

Section CANSEC1. Context {rc : runConstT}.
Section Closed.
  (* [comment removed for export] *)
  Let H : aholes := AFake_arep.AH adepot_iface AQUAR ASEC_of.     (* [comment removed for export] *)
  Let HL : ahole_laws H := AH_laws.                                (* [comment removed for export] *)
  Variable AI : AMallocIface.
  Hypothesis E : AHEAP AI = AHEAP_P H.
  Hypothesis CI_OK : forall iv, In iv (aci AI) -> 0 <= fst iv /\ snd iv <= AIMG_HI.
  Hypothesis DRV_CI : forall iv, In iv drv_img_ranges -> In iv (aci AI).
  Hypothesis CLI_CI : forall iv, In iv cli_img_ranges -> In iv (aci AI).
  (* [comment removed for export] *)
  Hypothesis FUZZ : fuzz_oneA_stmt AI afake_rng.
  Lemma UDRV_len : (length UDRV <= 4096)%nat.
  Proof. cbn. lia. Qed.
  Lemma UDRV_traces : Forall (fun u => (length u <= 254)%nat) UDRV.
  Proof. unfold UDRV. repeat constructor. Qed.

  (* [comment removed for export] *)
  Lemma aheap_init : aheap_init_stmt AI ATsafeMain.A0.
  Proof.
    intros en inp w V m ms mo HV HI HM HA. rewrite E. unfold H, AFake_arep.AH, LDRV.
    apply (aheapP_at_main ATsafeMain.A0 ATsafeMain.A0_init ATsafeMain.A0_ash UDRV UDRV_len UDRV_traces ASEC_of en inp w V m ms mo HV HI HM HA).
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

  Lemma fuzz_oneA : fuzz_oneA_stmt AI afake_rng.
  Proof. exact FUZZ. Qed.

  Lemma adrv : adrv_stmt ATsafeMain.A0.
  Proof.
    exact (adrv_closed AI afake_rng ATsafeMain.A0 ATsafeMain.A0_init aheap_init aresv_init (afake_rng_init _ ATsafeMain.A0_init)
             afake_rng_mono DRV_CI CLI_CI (fun iv Hiv => proj1 (CI_OK iv Hiv))
             (dmalloc_of_AI AI) (dfree_of_AI AI) (dfree_null_of_AI AI) fuzz_oneA strnlen_a_proof).
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
