(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.Lib Require Import Tac Image ZBridge SysStep ITree Nodes Decode Arr FP Frame InitMem RunConst.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.Common Require Import DrvAgree RunDraw.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.Spec Require Import Prelim Monad STree AsanCtrl AsanEmbed HarnessM ProgA AsanProgDeps.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.LibA Require Import ExecF ITreeA SysStepF Shadow.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.AsanW Require Import AImg RtCells AProto ABase ARep ALayout AHeapP AQConst ARepQ ASec AMalloc_iface APoisonR_iface AFake_iface AFake_arep
     ADepot_iface ADepot F_adepot F_annot_grow AH_opnew AH_opdelete_top
     AInstance AInstanceM AInstanceF AFreeAll AU_kit AU_iface AHarnessU_iface AU_parts_iface AU_fake_arep AU_vdtor_M
     ALoose ALooseInst ALooseSet ALooseLaws ALoose_iface ALooseOps AM_iface ALooseKitI AM_fake_arep3 AM_lambda_iface AMain_closed AMain_final.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition ai_kind_stmt {rc : runConstT} (AI : AMallocIface) : Prop :=
  forall L RNG st LB m p A n, AHEAP AI L RNG st LB m -> In (HB p A n) LB ->
    exists ch, (a_live st) !! p = Some ch /\ chunk_size ch = n /\ (is_primary n = false -> A = chunk_user_beg ch) /\ achunk_kind_ok ch n.
Definition ai_premap_stmt {rc : runConstT} (AI : AMallocIface) : Prop := forall L RNG st LB m, AHEAP AI L RNG st LB m -> premap_cells m.
Definition img_ci_stmt {rc : runConstT} (AI : AMallocIface) : Prop := forall iv, In iv client_ranges -> In iv (aci AI).
Definition fake_flag_stmt {rc : runConstT} (AI : AMallocIface) (fflag : alayout -> Z -> Z -> Z) : Prop :=
  forall L RNG st LB m cls F N,
    AHEAP AI L RNG st LB m -> In (mkABlock (ABFake cls) F N) LB ->
    rw_cells asegs m (fflag L cls F) [C1 (Z_to_bv 8 1)] /\ rng RNG (fflag L cls F) 1
    /\ ablk (fflag L cls F) (fflag L cls F + 1) /\ fflag L cls F + 1 <= ATOP
    /\ (forall b, In b LB -> fflag L cls F + 1 <= ab_addr b \/ ab_addr b + ab_size b <= fflag L cls F)
    /\ ~ in_ranges (aci AI) (fflag L cls F).
Definition fake_release_stmt {rc : runConstT} (AI : AMallocIface) (fflag : alayout -> Z -> Z -> Z) : Prop :=
  forall L RNG st LB m cls F N,
    AHEAP AI L RNG st (mkABlock (ABFake cls) F N :: LB) m ->
    AHEAP AI L RNG st LB (write_to_mem m (wa (fflag L cls F)) [Z_to_bv 8 0]).
Definition rng_fs_mono_stmt (rng_fs : alayout -> footprint -> Prop) : Prop := forall L R R', fp_le R R' -> rng_fs L R -> rng_fs L R'.
(* [comment removed for export] *)
Definition lsan_stmt {rc : runConstT} (AI : AMallocIface) : Prop :=
  forall L RNG st LB m, AHEAP AI L RNG st LB m -> rw_cells asegs m 0x6a4df8 [C4 (Z_to_bv 64 0)].
Definition frame_lsan_stmt {rc : runConstT} (AI : AMallocIface) : Prop :=
  forall L RNG st LB m m' W, AHEAP AI L RNG st LB m -> munch W m m' -> wmono asegs m m' ->
    Forall (fun iv => aclient_range (aci AI) LB (ATOP + 4096) (fst iv) (snd iv - fst iv) \/ iv = (0x6a4df8, 0x6a4dfc)) W ->
    rw_cells asegs m' 0x6a4df8 [C4 (Z_to_bv 64 0)] -> AHEAP AI L RNG st LB m'.

(* [comment removed for export] *)
Definition lambda_thm_type : Prop :=
  forall (rc : runConstT) (AI : AMallocIface) (fflag : alayout -> Z -> Z -> Z) (rng_fs : alayout -> footprint -> Prop) (K : ALooseKit AI fflag rng_fs),
    img_ci_stmt AI -> opnew_stmtA AI -> opdelete_stmtA AI -> ai_kind_stmt AI -> ai_premap_stmt AI -> stack_malloc_1_stmt AI fflag rng_fs ->
    lambda_stmt AI fflag rng_fs K.
(* [comment removed for export] *)
Definition harness_thm_type : Prop :=
  forall (rc : runConstT) (AI : AMallocIface) (fflag : alayout -> Z -> Z -> Z) (rng_fs : alayout -> footprint -> Prop) (K : ALooseKit AI fflag rng_fs),
    img_ci_stmt AI -> stack_malloc_3_stmt AI fflag rng_fs -> fake_flag_stmt AI fflag -> fake_release_stmt AI fflag ->
    lambda_stmt AI fflag rng_fs K -> rng_fs_mono_stmt rng_fs ->
    opnew_stmtA AI -> lsan_stmt AI -> frame_lsan_stmt AI ->
    fuzz_oneU_stmt AI rng_fs.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section CANSEC1. Context {rc : runConstT}.
Section I.
  Hypothesis FREE : afree_stmt aci_I AHEAP_I.
  Notation AIx := (AI_of FREE).

  Lemma IMG_CI_I : img_ci_stmt AIx.
  Proof. intros iv H. exact (AI_of_URI_CI FREE iv H). Qed.
  Lemma ONTA_I : opnew_stmtA AIx.
  Proof. exact (opnew_proofA AIx). Qed.
  Lemma OD_I : opdelete_stmtA AIx.
  Proof. exact (opdelete_proofA AIx). Qed.
  Lemma KIND_I : ai_kind_stmt AIx.
  Proof. exact (AI_of_chunk FREE). Qed.
  Lemma PREMAP_I : ai_premap_stmt AIx.
  Proof. exact (AI_of_premap FREE). Qed.
  Lemma RFSM_I : rng_fs_mono_stmt afake_rng.
  Proof. exact afake_rng_mono. Qed.
  Lemma LSAN_I : lsan_stmt AIx.
  Proof. exact (AI_of_lsan FREE). Qed.
  Lemma FRAME_LSAN_I : frame_lsan_stmt AIx.
  Proof. exact (AI_of_frame_lsan' FREE). Qed.

  (* [comment removed for export] *)
  Lemma fake_flag_I : fake_flag_stmt AIx fflag.
  Proof.
    pose proof AH_laws as HL. pose proof (AI_of_CI_OK FREE) as CI_OK.
    intros L RNG st LB m cls F N AHx Hin. rewrite (AI_of_E FREE) in AHx. unfold AHI in AHx.
    eapply (fake_flag_P adepot_iface AQUAR ASEC_of); eassumption.
  Qed.
  Lemma fake_release_I : fake_release_stmt AIx fflag.
  Proof.
    pose proof AH_laws as HL. pose proof (AI_of_CI_OK FREE) as CI_OK.
    intros L RNG st LB m cls F N AHx. rewrite (AI_of_E FREE) in AHx |- *. unfold AHI in AHx |- *.
    eapply (fake_release_P adepot_iface AQUAR ASEC_of); eassumption.
  Qed.

  (* [comment removed for export] *)
  Lemma SM1_I : stack_malloc_1_stmt AIx fflag afake_rng.
  Proof.
    pose proof AH_laws as HL. pose proof (AI_of_CI_OK FREE) as CI_OK.
    unfold stack_malloc_1_stmt. intros until lo. intros AHx NOFK MI ST BOT LO SPT TP RSTK RI RFS.
    rewrite (AI_of_E FREE) in AHx. unfold AHI in AHx.
    eapply evtF_mono; [eapply (stack_malloc_1_P adepot_iface AQUAR ASEC_of); try eassumption; unfold SM_STACK, SM1_STACK in *; lia|].
    cbv beta. intros ms' PO. unfold sm1_postP in PO. unfold sm1_post.
    destruct PO as (F & x0 & x1 & x2 & y1 & y2 & y3 & y4 & y5 & y6 & y7 & x3 & x4 & x5 & x6 & m' & j0 & j1 & j2 & junk & EQ & MI' & ST' & HPR & AH' & REST).
    exists F, x0, x1, x2, y1, y2, y3, y4, y5, y6, y7, x3, x4, x5, x6, m', j0, j1, j2, junk.
    rewrite (AI_of_E FREE). unfold AHI. repeat (split; [assumption|]). exact REST.
  Qed.
  Lemma SM3_I : stack_malloc_3_stmt AIx fflag afake_rng.
  Proof. pose proof AH_laws as HL. pose proof (AI_of_CI_OK FREE) as CI_OK. eapply (stack_malloc_3_AI adepot_iface AQUAR ASEC_of); try eassumption; first [exact (AI_of_E FREE) | reflexivity]. Qed.

  (* [comment removed for export] *)
  Definition KI : ALooseKit AIx fflag afake_rng := ALooseKitI FREE.

  (* [comment removed for export] *)
  Lemma avdtor_I : avdtor_stmt AIx.
  Proof. exact (avdtor_proof AIx IMG_CI_I (opdelete_data_proofA AIx) annot_grow_full KIND_I PREMAP_I). Qed.

  (* [comment removed for export] *)
  Section Plug.
    Hypothesis lambda_thm : lambda_thm_type.
    Hypothesis harness_thm : harness_thm_type.

    Lemma lambda_I : lambda_stmt AIx fflag afake_rng KI.
    Proof. exact (lambda_thm rc AIx fflag afake_rng KI IMG_CI_I ONTA_I OD_I KIND_I PREMAP_I SM1_I). Qed.
    Lemma fuzz_oneU_I : fuzz_oneU_stmt AIx afake_rng.
    Proof. exact (harness_thm rc AIx fflag afake_rng KI IMG_CI_I SM3_I fake_flag_I fake_release_I lambda_I RFSM_I ONTA_I LSAN_I FRAME_LSAN_I). Qed.
    Theorem asan_client_I : asan_client_at AIx.
    Proof. split; [exact fuzz_oneU_I| exact avdtor_I]. Qed.
  End Plug.
End I.
End CANSEC1.

(* [comment removed for export] *)
Theorem asan_client_of : lambda_thm_type -> harness_thm_type -> asan_client_stmt.
Proof. intros LT HT rc. exact (@asan_client_I rc (@AHI_free rc) LT HT). Qed.
