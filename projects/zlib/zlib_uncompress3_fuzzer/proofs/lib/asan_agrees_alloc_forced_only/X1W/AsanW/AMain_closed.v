(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_agrees_alloc_forced_only.Lib Require Import PropExec MState Mem Cells Step Frame Arr InitMem ITree Nodes.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_agrees_alloc_forced_only.LibA Require Import ExecF ITreeA ModelX.
Require Import OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_agrees_alloc_forced_only.Spec.STree OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_agrees_alloc_forced_only.Spec.AsanCtrl OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_agrees_alloc_forced_only.Spec.AsanEmbed OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_agrees_alloc_forced_only.Spec.AsanProgDeps OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_agrees_alloc_forced_only.Spec.ProgA OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_agrees_alloc_forced_only.X1W.Spec.AsanHandoff.
Require Import OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_agrees_alloc_forced_only.AS.MainExport OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_agrees_alloc_forced_only.AS.MainFactsAsan OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_agrees_alloc_forced_only.X1W.AS.MainEntry.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_agrees_alloc_forced_only.X1W Require Import AsanMain.
Require Import OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_agrees_alloc_forced_only.AsanW.AImg OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_agrees_alloc_forced_only.AsanW.ABase OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_agrees_alloc_forced_only.AsanW.ABytes OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_agrees_alloc_forced_only.AsanW.ALayout OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_agrees_alloc_forced_only.AsanW.ARep OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_agrees_alloc_forced_only.AsanW.AHeapP OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_agrees_alloc_forced_only.AsanW.AQConst OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_agrees_alloc_forced_only.AsanW.ARepQ OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_agrees_alloc_forced_only.AsanW.AFake_iface OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_agrees_alloc_forced_only.AsanW.AFake_init OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_agrees_alloc_forced_only.AsanW.AFake_arep OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_agrees_alloc_forced_only.AsanW.ADepot_iface OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_agrees_alloc_forced_only.AsanW.ADepot OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_agrees_alloc_forced_only.X1W.AsanW.ADepot_init OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_agrees_alloc_forced_only.AsanW.F_adepot OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_agrees_alloc_forced_only.AsanW.AMalloc_iface OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_agrees_alloc_forced_only.AsanW.AHarness_iface OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_agrees_alloc_forced_only.AsanW.ADriver_iface OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_agrees_alloc_forced_only.AsanW.Strnlen_iface OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_agrees_alloc_forced_only.AsanW.Strnlen_proof OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_agrees_alloc_forced_only.X1W.AsanW.AResv OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_agrees_alloc_forced_only.AsanW.ASec OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_agrees_alloc_forced_only.AsanW.AInstance OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_agrees_alloc_forced_only.X1W.AsanW.ARepInit_A OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_agrees_alloc_forced_only.X1W.AsanW.ARepInit OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_agrees_alloc_forced_only.X1W.AsanW.ARepInit_S OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_agrees_alloc_forced_only.X1W.AsanW.ARepInit_glue OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_agrees_alloc_forced_only.X1W.AsanW.AMain_asm OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_agrees_alloc_forced_only.X1W.AsanW.AD_handoff OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_agrees_alloc_forced_only.X1W.AsanW.ATsafeMain.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_agrees_alloc_forced_only.Common Require Import RunDraw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Section CANSEC1. Context {rc : runConstT}.
Section Closed.
  Let H : aholes := AFake_arep.AH adepot_iface AQUAR ASEC_of.
  Variable AI : AMallocIface.
  Hypothesis E : AHEAP AI = AHEAP_P H.
  Hypothesis CI_OK : forall iv, In iv (aci AI) -> 0 <= fst iv /\ snd iv <= AIMG_HI.
  Hypothesis DRV_CI : forall iv, In iv drv_img_ranges -> In iv (aci AI).
  Hypothesis FUZZ : fuzz_oneA_stmt AI afake_rng.

  Lemma UDRV_len : (length UDRV <= 4096)%nat.
  Proof. cbn. lia. Qed.
  Lemma UDRV_traces : Forall (fun u => (length u <= 254)%nat) UDRV.
  Proof. unfold UDRV. repeat constructor. Qed.

  Lemma aheap_init : aheap_init_stmt AI ATsafeMain.A0.
  Proof.
    intros en inp w V m ms mo HV HI HM HA. rewrite E. unfold H, AFake_arep.AH, LDRV.
    apply (aheapP_at_main ATsafeMain.A0 ATsafeMain.A0_init ATsafeMain.A0_ashc UDRV UDRV_len UDRV_traces ASEC_of en inp w V m ms mo HV HI HM HA).
    (* amain_open gains the argv-facts conjunct (AS/MainEntry, batch 4 row e) *)
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

  Lemma adrv : adrv_stmt ATsafeMain.A0.
  Proof.
    exact (adrv_closed AI afake_rng ATsafeMain.A0 ATsafeMain.A0_init aheap_init aresv_init (afake_rng_init _ ATsafeMain.A0_init)
             afake_rng_mono DRV_CI (fun iv Hiv => proj1 (CI_OK iv Hiv))
             (dmalloc_of_AI AI) (dfree_of_AI AI) (dfree_null_of_AI AI) FUZZ strnlen_a_proof).
  Qed.
End Closed.
End CANSEC1.
