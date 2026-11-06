(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Lib Require Import PropExec MState Mem Cells Step Frame Arr InitMem ITree Nodes.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.LibA Require Import ExecF ITreeA ModelX.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Spec Require Import STree AsanCtrl AsanEmbed AsanProgDeps ProgA AsanHandoff.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.AS Require Import MainExport MainFactsAsan MainEntry.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib Require Import AsanMainU ADkModel.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.AsanW Require Import AProto AImg ABase ABytes ALayout ARep AHeapP AQConst ARepQ AFake_iface AFake_init AFake_arep ADepot_iface ADepot ADepot_init F_adepot AMalloc_iface AU_iface AU_parts_iface AHarnessU_iface APoisonR_iface ADriver_iface Strnlen_iface Strnlen_proof AResv ASec AInstance ARepInit_A ARepInit ARepInit_S ARepInit_glue AMain_asm AD_target_run AD_handoff AExitU_closed ATsafeMain
     AInstanceW AInstanceW2.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Common Require Import RunDraw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Set Keyed Unification.   (* [comment removed for export] *)

Section CANSEC1. Context {rc : runConstT}.

(* [comment removed for export] *)
Lemma aresv_init : aresv_init_stmt.
Proof.
  intros en inp w V m ms mo _ _ HM. pose proof HM as (_ & _ & _ & _ & HPF & _). apply Forall_app in HPF as [HPF _].
  apply aresv_ok_handoff. exact HPF.
Qed.

Lemma model_ok : progA_model_ok ATsafeMain.NMAX ATsafeMain.A0.
Proof.
  intros en inp w V m ms mo _ _ HM HA. pose proof HM as (_ & _ & PIN & _ & HP & _ & _ & _ & _ & HMOD). apply Forall_app in HP as [HP _].
  assert (HAT : a_usp0 V - 8388608 = ATOP).
  { unfold a_usp0. destruct PIN as (_ & _ & _ & USP & _). rewrite USP. exact HA. }
  rewrite <- HA. exact (progA_tsafe_open ASTAGE V (en_sp en) inp mo HP HAT HA HMOD).
Qed.

(* [comment removed for export] *)
Section ClosedW.
  (* [comment removed for export] *)
  Hypothesis FUZZ : fuzz_oneU_stmt AI_W afake_rng.

  Lemma trunW : atarget_run_stmtA AI_W afake_rng.
  Proof.
    exact (atarget_run_proofA AI_W afake_rng afake_rng_mono AI_W_DRV_CI AI_W_URI_CI (fun iv Hiv => proj1 (AI_W_CI_OK iv Hiv))
             (dmalloc_of_AI AI_W) (dfree_of_AI AI_W) (dfree_null_of_AI AI_W) (ashenv_law_holds AI_W) AHW_fresh FUZZ strnlen_a_proof).
  Qed.

  (* [comment removed for export] *)
  Lemma adrvW : adrv_stmt ATsafeMain.A0.
  Proof.
    intros en inp w V m ms mo Hv Hi HM HA.
    exact (@adrv_closed_at rc XP0 AI_W afake_rng ATsafeMain.A0 ATsafeMain.A0_init aheap_init_W aresv_init (afake_rng_init _ ATsafeMain.A0_init)
             XP0_SLO XP0_SHI afake_rng_mono AI_W_DRV_CI AI_W_URI_CI (dmalloc_of_AI AI_W) (dfree_of_AI AI_W) strnlen_a_proof trunW
             (@aexit_closed rc XP0 AI_W) en inp w V m ms mo Hv Hi HM HA I I).
  Qed.
End ClosedW.
End CANSEC1.

(* [comment removed for export] *)
Theorem asan_impl_W : (forall rc : runConstT, @fuzz_oneU_stmt rc AI_W afake_rng) -> impl_stmt ASTAGE.
Proof.
  intros FUZZ.
  exact (asan_impl ATsafeMain.NMAX ATsafeMain.A0
           (fun rc : runConstT => @adrvW rc (FUZZ rc))
           (fun rc : runConstT => @model_ok rc)
           ATsafeMain.A0_init).
Qed.
