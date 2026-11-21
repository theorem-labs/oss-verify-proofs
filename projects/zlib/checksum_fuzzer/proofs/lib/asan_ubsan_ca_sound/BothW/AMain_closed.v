(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.asan_ubsan_ca_sound.Lib Require Import PropExec MState Mem Cells Step Frame Arr InitMem ITree Nodes.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.asan_ubsan_ca_sound.LibA Require Import ExecF ITreeA ModelX.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.asan_ubsan_ca_sound.Spec Require Import STree AsanCtrl AsanEmbed AsanProgDeps ProgA AsanHandoffBoth.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.asan_ubsan_ca_sound.AS Require Import MainExport MainFactsBoth MainEntryBoth.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.asan_ubsan_ca_sound Require Import BothMain.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.asan_ubsan_ca_sound.BothW Require Import BImg ABase ABytes ALayout ARep AHeapP AQConst ARepQ
     ADepot_iface ADepot ADepot_init F_adepot F_amalloc_arep AMalloc_iface AHarness_iface ADriver_iface Strnlen_iface Strnlen_proof
     AResv ASec AInstance ARepInit_A ARepInit ARepInit_S ARepInit_glue AMain_asm AD_handoff AHarness_closed ATsafeMain.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.asan_ubsan_ca_sound.CkB Require CkBIface CkB_closed.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.asan_ubsan_ca_sound.Common Require Import RunDraw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Definition rng_fs0 : alayout -> footprint -> Prop := fun _ _ => True.

Section CANSEC1. Context {rc : runConstT}.
Section Closed.
  Let H : aholes := AH adepot_iface AQUAR ASEC_of AFK0.
  Let HL : ahole_laws H := AH_laws.
  Variable AI : AMallocIface.
  Hypothesis E : AHEAP AI = AHEAP_P H.
  Hypothesis CI_OK : forall iv, In iv (aci AI) -> 0 <= fst iv /\ snd iv <= AIMG_HI.
  Hypothesis DRV_CI : forall iv, In iv drv_img_ranges -> In iv (aci AI).

  Lemma UDRV_len : (length UDRV <= 4096)%nat.
  Proof. cbn. lia. Qed.
  Lemma UDRV_traces : Forall (fun u => (length u <= 254)%nat) UDRV.
  Proof. unfold UDRV. repeat constructor. Qed.

  Lemma aheap_init : aheap_init_stmt AI ATsafeMain.A0.
  Proof.
    intros en inp w V m ms mo HV HI HM HA. rewrite E. unfold H, AH, LDRV.
    apply (aheapP_at_main ATsafeMain.A0 ATsafeMain.A0_init ATsafeMain.A0_ashc UDRV UDRV_len UDRV_traces ASEC_of en inp w V m ms mo HV HI HM HA).
    (* amain_open gains the argv-facts conjunct (AS/MainEntry , batch 4 row e) *)
    pose proof HM as (_ & _ & PIN & HMF & HPF & _ & _ & _ & _ & SH0 & _). apply Forall_app in HMF as [HMF _]. apply Forall_app in HPF as [HPF _].
    assert (HAT : 32768 * V 0%nat + 4096 * V 10%nat + 16 * V 6%nat - 8388608 = ATOP).
    { destruct PIN as (_ & _ & _ & USP & _). rewrite USP. exact HA. }
    apply (ASEC_of_init V w UDRV m HMF HPF); first [exact HAT | exact SH0 | unfold AUMAX; cbn; lia].
  Qed.

  Lemma aresv_init : aresv_init_stmt.
  Proof.
    intros en inp w V m ms mo _ _ HM. pose proof HM as (_ & _ & _ & _ & HPF & _). apply Forall_app in HPF as [HPF _].
    apply aresv_ok_handoff. exact HPF.
  Qed.

  Lemma fuzz_oneA : fuzz_oneA_stmt AI rng_fs0.
  Proof. exact (fuzz_oneA_of_ck CkB_closed.ck_fuzz_B AI rng_fs0). Qed.

  Lemma adrv : adrv_stmt ATsafeMain.A0.
  Proof.
    exact (adrv_closed AI rng_fs0 ATsafeMain.A0 ATsafeMain.A0_init aheap_init aresv_init (fun _ _ _ _ _ => I)
             (fun _ _ _ _ _ => I) DRV_CI (fun iv Hiv => proj1 (CI_OK iv Hiv))
             (dmalloc_of_AI AI) (dfree_of_AI AI) (dfree_null_of_AI AI) fuzz_oneA strnlen_a_proof).
  Qed.

  Lemma model_ok : progA_model_ok ATsafeMain.NMAX ATsafeMain.A0.
  Proof.
    intros en inp w V m ms mo _ _ HM HA. pose proof HM as (_ & _ & PIN & _ & HP & _ & _ & _ & _ & _ & HMOD).   (* + the argv-facts conjunct *) apply Forall_app in HP as [HP _].
    assert (HAT : a_usp0 V - 8388608 = ATOP).
    { unfold a_usp0. destruct PIN as (_ & _ & _ & USP & _). rewrite USP. exact HA. }
    rewrite <- HA. exact (progA_tsafe_open ASTAGE V (en_sp en) inp mo HP HAT HA HMOD).
  Qed.
End Closed.
End CANSEC1.
