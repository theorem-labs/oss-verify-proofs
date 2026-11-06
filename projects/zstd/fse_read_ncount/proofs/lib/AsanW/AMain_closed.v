(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib Require Import PropExec MState Mem Cells Step Frame Arr InitMem ITree Nodes.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.LibA Require Import ExecF ITreeA ModelX.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Spec Require Import STree AsanCtrl AsanEmbed AsanProgDeps ProgA AsanHandoff.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.AS Require Import MainExport MainFactsAsan MainEntry.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib Require Import AsanMain.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.AsanW Require Import AImg ABase ABytes ALayout ARep AHeapP AQConst ARepQ AFake_iface AFake_init AFake_arep
ADepot_iface ADepot ADepot_init F_adepot AMalloc_iface AHarness_iface APoisonR_iface ADriver_iface Strnlen_iface Strnlen_proof
AResv ASec AInstance ARepInit_A ARepInit ARepInit_S ARepInit_glue AMain_asm AD_handoff ATsafeMain.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Common Require Import RunDraw.
Import ListNotations.
(* [comment removed for export] *)
Local Ltac OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.LiaTuning.lia_orc_old ::= OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.LiaTuning.lia_k12.   (* [comment removed for export] *)
Local Ltac OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.Step.slia ::= OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.Tac.slia_k12.
Local Ltac OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.ZBridge.flia ::= OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.Tac.flia_k12.
Local Ltac OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.ZBridge.zrange ::= OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.Tac.zrange_k12.
Local Ltac OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.ZBridge.zrange_nonneg ::= OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.Tac.zrange_nonneg_k12.
Local Ltac OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.Step.solve_load ::= OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.Tac.solve_load_k12.
Local Ltac OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.ZBridge.word_eq_tac ::= OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.Tac.word_eq_tac_k12.
Local Ltac OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.Tac.simpl_arr_sizes ::= OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.Tac.simpl_arr_sizes_k12.
(* [comment removed for export] *)

Open Scope Z_scope.
Section CANSEC1. Context {rc : runConstT}.
Section Closed.
Let H : aholes := AFake_arep.AH adepot_iface AQUAR ASEC_of.
Let HL : ahole_laws H := AH_laws.
Variable AI : AMallocIface.
Hypothesis E : AHEAP AI = AHEAP_P H.
Hypothesis CI_OK : forall iv, In iv (aci AI) -> 0 <= fst iv /\ snd iv <= AIMG_HI.
Hypothesis DRV_CI : forall iv, In iv drv_img_ranges -> In iv (aci AI).
Hypothesis CLI_CI : forall iv, In iv cli_img_ranges -> In iv (aci AI).
Hypothesis FUZZ : fuzz_oneA_stmt AI afake_rng.
#[using="Type"] Lemma UDRV_len : (length UDRV <= 4096)%nat.
Proof. cbn. Local Ltac2 Set LiaHints.tbl := fun () => "0010=25276102397.9000001S".
lia. Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
#[using="Type"] Lemma UDRV_traces : Forall (fun u => (length u <= 254)%nat) UDRV.
Proof. unfold UDRV. repeat constructor. Qed.
#[using="H E"] Lemma aheap_init : aheap_init_stmt AI ATsafeMain.A0.
Proof.
intros en inp w V m ms mo HV HI HM HA. rewrite E. unfold H, AFake_arep.AH, LDRV.
apply (aheapP_at_main ATsafeMain.A0 ATsafeMain.A0_init ATsafeMain.A0_lat UDRV UDRV_len UDRV_traces ASEC_of en inp w V m ms mo HV HI HM HA).
pose proof HM as (_ & _ & PIN & HMF & HPF & _ & _ & _ & SH0 & _). apply Forall_app in HMF as [HMF _]. apply Forall_app in HPF as [HPF _].
assert (HAT : 32768 * V 0%nat + 4096 * V 10%nat + 16 * V 6%nat - 8388608 = ATOP).
{ destruct PIN as (_ & _ & _ & USP & _). rewrite USP. exact HA. }
Local Ltac2 Set LiaHints.tbl := fun () => "0010>63989141300.2600000<S3PIN3HAT2H0".
apply (ASEC_of_init V w UDRV m HMF HPF); first [exact HAT | exact SH0 | unfold AUMAX; cbn; lia].
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
#[using="Type"] Lemma aresv_init : aresv_init_stmt.
Proof.
intros en inp w V m ms mo _ _ HM. pose proof HM as (_ & _ & _ & _ & HPF & _). apply Forall_app in HPF as [HPF _].
apply aresv_ok_handoff. exact HPF.
Qed.
#[using="FUZZ"] Lemma fuzz_oneA : fuzz_oneA_stmt AI afake_rng.
Proof. exact FUZZ. Qed.
#[using="H AI E CI_OK DRV_CI CLI_CI FUZZ"] Lemma adrv : adrv_stmt ATsafeMain.A0.
Proof.
exact (adrv_closed AI afake_rng ATsafeMain.A0 ATsafeMain.A0_init aheap_init aresv_init (afake_rng_init _ ATsafeMain.A0_init)
afake_rng_mono DRV_CI CLI_CI (fun iv Hiv => proj1 (CI_OK iv Hiv))
(dmalloc_of_AI AI) (dfree_of_AI AI) (dfree_null_of_AI AI) fuzz_oneA strnlen_a_proof).
Qed.
#[using="Type"] Lemma model_ok : progA_model_ok ATsafeMain.NMAX ATsafeMain.A0.
Proof.
intros en inp w V m ms mo _ _ HM HA. pose proof HM as (_ & _ & PIN & _ & HP & _ & _ & _ & _ & [HLIM HMOD]). apply Forall_app in HP as [HP _].
assert (HAT : a_usp0 V - 8388608 = ATOP).
{ unfold a_usp0. destruct PIN as (_ & _ & _ & USP & _). rewrite USP. exact HA. }
rewrite <- HA. exact (progA_tsafe_open_L (vm_limit (m_vmmaps mo)) ASTAGE V (en_sp en) inp mo HLIM HP HAT HA HMOD).
Qed.
End Closed.
End CANSEC1.
