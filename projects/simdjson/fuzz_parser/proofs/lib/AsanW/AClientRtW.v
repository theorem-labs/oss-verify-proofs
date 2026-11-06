(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Lib Require Import Tac Image ZBridge SysStep ITree Nodes Decode Arr FP.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.LibA Require Import ExecF ITreeA SysStepF Shadow.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Spec Require Import Prelim Monad STree AsanCtrl AsanEmbed HarnessP ProgA AsanProgDeps.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib Require Import ADkModel.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.AsanW Require Import AImg ABase AMalloc_iface ADepot_iface ARep ALayout AHeapP AQConst ARepQ ASec
     F_adepot AFake_iface AFake_arep AInstance AInstanceM AInstanceF AU_kit AU_iface AU_parts_iface AFake_arep2m AFake_arep4m AFake_arep5m
     AFake_arep5 ADepotW F_adepotW AInstanceW0 AInstanceW AInstanceW2.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Common Require Import RunDraw.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Section CANSEC1. Context {rc : runConstT}.
Notation AI := AI_W.
Let CI_OK : forall iv, In iv (aci AI) -> 0 <= fst iv /\ snd iv <= AIMG_HI := AI_W_CI_OK.

(* [comment removed for export] *)
Lemma crtW_IMG_CI : forall iv, In iv client_ranges -> In iv (aci AI).
Proof. exact AI_W_URI_CI. Qed.

(* [comment removed for export] *)
Lemma crtW_fake_flag : forall L RNG st LB m cls F N,
  AHEAP AI L RNG st LB m -> In (mkABlock (ABFake cls) F N) LB ->
  rw_cells asegs m (fflag L cls F) [C1 (Z_to_bv 8 1)] /\ rng RNG (fflag L cls F) 1
  /\ ablk (fflag L cls F) (fflag L cls F + 1) /\ fflag L cls F + 1 <= ATOP
  /\ (forall b, In b LB -> fflag L cls F + 1 <= ab_addr b \/ ab_addr b + ab_size b <= fflag L cls F)
  /\ ~ in_ranges (aci AI) (fflag L cls F).
Proof.
  intros L RNG st LB m cls F N AHx Hin. pose proof (AHW_weak _ _ _ _ _ AHx) as AH0.
  exact (fake_flag_P adepot_iface AQUAR ASEC_of (aci AI) CI_OK L RNG st LB m cls F N AH0 Hin).
Qed.

Lemma crtW_fake_release : forall L RNG st LB m cls F N,
  AHEAP AI L RNG st (mkABlock (ABFake cls) F N :: LB) m ->
  AHEAP AI L RNG st LB (write_to_mem m (wa (fflag L cls F)) [Z_to_bv 8 0]).
Proof.
  intros L RNG st LB m cls F N (HF & k & Hk & AHx). split; [exact HF|]. exists k. split; [exact Hk|].
  exact (fake_release_P (DI_of k) AQUAR ASEC_of (AHI_k_laws k) L RNG st LB m cls F N AHx).
Qed.

Lemma crtW_rng_fs_mono : forall L R R', fp_le R R' -> afake_rng L R -> afake_rng L R'.
Proof. exact afake_rng_mono. Qed.

(* [comment removed for export] *)
Local Ltac wrapW k Hk :=
  lazymatch goal with
  | H : context [AHEAP (AI_k k) ?L ?RNG ?st ?LB ?m] |- _ => idtac
  | _ => idtac
  end.

Lemma crtW_sm2 : stack_malloc_2_stmt AI fflag afake_rng.
Proof.
  unfold stack_malloc_2_stmt. intros L RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 FR fc m st LB lo
    (HF & k & Hk & AH). intros NF MI ST BOT LOS TOP TP R1 R2 R3.
  pose proof (stack_malloc_2_AI (DI_of k) AQUAR ASEC_of (AHI_k_laws k) (aci (AI_k k)) CI_OK (AI_k k) (AI_k_E k) eq_refl) as SM.
  eapply evtF_mono; [exact (SM L RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 FR fc m st LB lo
                              AH NF MI ST BOT LOS TOP TP R1 R2 R3)|].
  intros ms' (F & x0 & x1 & x2 & x3 & x4 & x5 & x6 & x7 & x8 & x9 & x10 & x11 & x12 & x13 & m' & j0 & j1 & j2 & junk & E & P1 & P2 & P3 & P4 & REST).
  exists F, x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, m', j0, j1, j2, junk.
  exact (conj E (conj P1 (conj P2 (conj P3 (conj (conj HF (ex_intro _ k (conj Hk P4))) REST))))).
Qed.

Lemma crtW_sm4_1 : stack_malloc_4_stmt1 AI fflag afake_rng.
Proof.
  unfold stack_malloc_4_stmt1. intros L RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 FR fc m st LB lo
    (HF & k & Hk & AH). intros NF MI ST BOT LOS TOP TP R1 R2 R3.
  pose proof (stack_malloc_4_AI1 (DI_of k) AQUAR ASEC_of (AHI_k_laws k) (aci (AI_k k)) CI_OK (AI_k k) (AI_k_E k) eq_refl) as SM.
  eapply evtF_mono; [exact (SM L RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 FR fc m st LB lo
                              AH NF MI ST BOT LOS TOP TP R1 R2 R3)|].
  intros ms' (F & x0 & x1 & x2 & x3 & x4 & x5 & x6 & x7 & x8 & x9 & x10 & x11 & x12 & x13 & m' & j0 & j1 & j2 & junk & E & P1 & P2 & P3 & P4 & REST).
  exists F, x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, m', j0, j1, j2, junk.
  exact (conj E (conj P1 (conj P2 (conj P3 (conj (conj HF (ex_intro _ k (conj Hk P4))) REST))))).
Qed.

Lemma crtW_sm5_1 : stack_malloc_5_stmt1 AI fflag afake_rng.
Proof.
  unfold stack_malloc_5_stmt1. intros L RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 FR fc m st LB lo
    (HF & k & Hk & AH). intros NF MI ST BOT LOS TOP TP R1 R2 R3.
  pose proof (stack_malloc_5_AI1 (DI_of k) AQUAR ASEC_of (AHI_k_laws k) (aci (AI_k k)) CI_OK (AI_k k) (AI_k_E k) eq_refl) as SM.
  eapply evtF_mono; [exact (SM L RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 FR fc m st LB lo
                              AH NF MI ST BOT LOS TOP TP R1 R2 R3)|].
  intros ms' (F & x0 & x1 & x2 & x3 & x4 & x5 & x6 & x7 & x8 & x9 & x10 & x11 & x12 & x13 & m' & j0 & j1 & j2 & junk & E & P1 & P2 & P3 & P4 & REST).
  exists F, x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, m', j0, j1, j2, junk.
  exact (conj E (conj P1 (conj P2 (conj P3 (conj (conj HF (ex_intro _ k (conj Hk P4))) REST))))).
Qed.

Lemma crtW_sm2' : stack_malloc_2_stmt AI fflag afake_rng.
Proof. exact crtW_sm2. Qed.

Lemma crtW_sf5 : stack_free_5_stmt AI fflag.
Proof.
  unfold stack_free_5_stmt. intros L RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 FR fc m st LB lo F
    (HF & k & Hk & AH). intros MI ST BOT LOS A0 FC RL.
  pose proof (stack_free_5_AI (DI_of k) AQUAR ASEC_of (AHI_k_laws k) (aci (AI_k k)) CI_OK (AI_k k) (AI_k_E k) eq_refl) as SM.
  eapply evtF_mono; [exact (SM L RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 FR fc m st LB lo F
                              AH MI ST BOT LOS A0 FC RL)|].
  intros ms' (x0 & x1 & x2 & x3 & x4 & x5 & x6 & x7 & x8 & x9 & x10 & x11 & x12 & x13 & x14 & m' & E & P1 & P2 & P3 & P4 & REST).
  exists x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, m'.
  exact (conj E (conj P1 (conj P2 (conj P3 (conj (conj HF (ex_intro _ k (conj Hk P4))) REST))))).
Qed.
End CANSEC1.
