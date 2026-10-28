(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OssFuzzTheorems.jsoncons.fuzz_json_cursor.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib Require Import PropExec CatExec CatSim SeqExec StoreOk StreamSim Hoare ShapeAlg SpinAlg
  AxSymExec3 AxSymExec3B AxSymExec3Sound AxSymRun3 AsanPlanCore AsanPlan AsanPlanSound AsanPlanSoundSums LibSym SegRun SegPlan SegPlanAuto
  HeapIface L5Defs L5Core. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U Require Import Pm10PlanKit_u PmLibDefs_u PmLibSpecs_u PmLayout_u.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.CutCert Require Import CutCert CutOps CutHeap CutAuto CutLib. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U.CutCert Require Import Pm10CutKit_u. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.CutCert Require Import CutL5.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U.PmTop Require Import TopKit_u TopKit2_u TopSpecs_u ReadKit_u ChunkKit_u Skel_u.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U.CutGen Require Cut_atexit2_csrc_u.
Import ListNotations. Import AX2. Import AX2B. Import AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Module SKC.
Module GX2 := Cut_atexit2_csrc_u.
Abbreviation RSEGS := PML.RSEGS.
Abbreviation mem := (word -> option byte).

Lemma u64_norm : forall (M : mem) A z, L5.u64_at RSEGS M A z -> L5.u64_at RSEGS M A (bv_unsigned (Z_to_bv 64 z)).
Proof. intros M A z H. unfold L5.u64_at in *. rewrite Z_to_bv_bv_unsigned. exact H. Qed.

Section S.
Context {SCFG_P : ScfgP}.
Variable L : heap_layout.
Hypothesis FPM : forall (fx fx' : FPState) R pc M R' pc' M',
  msteps RSEGS (@mkst fx R (Z_to_bv 64 pc) M (seg_rom RSEGS)) (@mkst fx' R' (Z_to_bv 64 pc') M' (seg_rom RSEGS)) -> PML.fp_ok fx -> PML.fp_ok fx'.

Theorem cxa_atexit2_ok : PMS.cxa_atexit2_spec L.
Proof.
  intros f a dso sp r [hf ha] fx R M model K Hh Hl HK0 Hfp (EN & A0 & A1 & A2 & (C0 & C4 & C8 & C16 & C24 & C32 & C288 & (C40 & C296)) & WR & (Q1 & Q2)) Hcont.
  destruct EN as (Hra & Hrok & Hsp & Htp & (S1 & S2 & S3 & S4 & S5)). unfold PML.a0, PML.a1 in A0, A1. cbn [length Z.of_nat Z.add] in C8. unfold PML.NEED_LOCKS in Q1.
  unfold PML.AX, PML.ATEXIT_CALL, PML.AEF_EXIT_GUARD in C0, C4, C8, C16, C24, C32, C288.
  apply u64_norm in C40. apply u64_norm in C296.
  pose proof (bv_unsigned_in_range _ (Z_to_bv 64 hf)) as RF. pose proof (bv_unsigned_in_range _ (Z_to_bv 64 ha)) as RA. change (bv_modulus 64) with (2 ^ 64) in RF, RA.
  set (gl := [bv_unsigned (Z_to_bv 64 hf); bv_unsigned (Z_to_bv 64 ha)]).
  change PML.PC_CXA_ATEXIT with (CC.cp_pc GX2.cp0).
  ck_open FPM GX2.cp0 (GX2.plans 0%nat _ eq_refl) 0 gl (fun _ : nat => @nil byte) (@nil (nat * Z)) sp R M fx model K Hh Hl Hfp Hsp ck_no_pins.
  - ck_gh E 0%nat (bv_unsigned (Z_to_bv 64 hf)). ck_gh E 1%nat (bv_unsigned (Z_to_bv 64 ha)).
    unfold know_ok, GX2.cp0. cbn [CC.cp_know]. repeat (apply Forall_cons); [.. | apply Forall_nil].
    + e_range. + e_align S1. + e_unk. + e_wr.
    + ck_kw8 1010323 0 Q1. + ck_kw8 1009736 0 C0. + ck_kw32 1009740 0 C4. + ck_kw32 1009744 2 C8. + ck_kw64 1009752 1009760 C16. + ck_kw64 1009760 0 C24. + ck_kw64 1009768 684300 C32. + ck_kw64 1010024 235124 C288.
    + ck_kw64 1009776 (bv_unsigned (Z_to_bv 64 hf)) C40. + ck_kw64 1010032 (bv_unsigned (Z_to_bv 64 ha)) C296.
    + eapply CK.kwr_of_writable with (A := 1009736) (N := 544); [ev_start | ev_len | lia | lia | exact WR].
  - intros fx' E' R' M' k ps Hnth Hag HLF Hfp'.
    assert (GH : forall j z, nth_error gl j = Some z -> ev E' (64 + j) = Z_to_bv 64 z).
    { intros j z Hj. assert (Hj2 : (j < 2)%nat) by (change 2%nat with (length gl); apply nth_error_Some; rewrite Hj; discriminate). change (CC.cp_nx GX2.cp0) with 66%nat in Hag.
      rewrite <- (proj1 Hag (64 + j)%nat) by lia. exact (CK.hvB_gh_w _ _ _ _ j z Hj). }
    ck_leaf Hag E'.
    ck_leaf_k k Hnth; [|ck_leaf_end k Hnth].
    apply (SK.fin_ret _ _ sp R _ _ E' R' M M' fx' model K _ r HLF Hag64 SK.ret_ax Hh Hl eq_refl eq_refl Hra Hrok Hsp ltac:(lia)). intros RP.
    assert (REG : forall (q : reg), (32 + ridx q < 64)%nat -> ev E' (32 + ridx q) = getr R q).
    { intros q Hq. rewrite <- (proj1 Hag64 (32 + ridx q)%nat Hq). exact (CK.hvB_reg _ _ _ _ q). }
    apply (Hcont fx' R' M' Hfp').
    + split; [unfold PML.a0; tk_lin HLF (10%bv : reg)|]. unfold PML.atexit_cells, PML.u8, PML.u32, PML.u64, PML.AX, PML.ATEXIT_CALL, PML.AEF_EXIT_GUARD. cbn [length Z.of_nat Z.add].
      split; [ck_cell8 HLF (ELit 0) 1009736 (ELit 0); reflexivity|]. split; [ck_cell32 HLF (ELit 0) 1009740 (ELit 0); reflexivity|]. split; [ck_cell32 HLF (ELit 0) 1009744 (ELit 3); reflexivity|].
      split; [ck_cell64 HLF (ELit 0) 1009752 (ELit 1009760); reflexivity|]. split; [ck_cell64 HLF (ELit 0) 1009760 (ELit 0); reflexivity|].
      split; [ck_cell64 HLF (ELit 0) 1009768 (ELit 684300); reflexivity|]. split; [ck_cell64 HLF (ELit 0) 1010024 (ELit 235124); reflexivity|].
      split.
      { apply (SK.u64_of_word M' _ (Z_to_bv 64 hf) hf); [|reflexivity]. ck_cell64 HLF (ELit 0) 1009776 (EVar 64). cbn [edenot]. f_equal. rewrite <- (Z_to_bv_bv_unsigned _ (Z_to_bv 64 hf)). exact (GH 0%nat _ eq_refl). }
      split.
      { apply (SK.u64_of_word M' _ (Z_to_bv 64 ha) ha); [|reflexivity]. ck_cell64 HLF (ELit 0) 1010032 (EVar 65). cbn [edenot]. f_equal. rewrite <- (Z_to_bv_bv_unsigned _ (Z_to_bv 64 ha)). exact (GH 1%nat _ eq_refl). }
      split.
      * apply (SK.u64_of_word M' _ (getr R 10%bv) f); [|exact A0]. ck_cell64 HLF (ELit 0) 1009784 (EVar 42). cbn [edenot]. f_equal. exact (REG 10%bv ltac:(vm_compute; lia)).
      * apply (SK.u64_of_word M' _ (getr R 11%bv) a); [|exact A1]. ck_cell64 HLF (ELit 0) 1010040 (EVar 43). cbn [edenot]. f_equal. exact (REG 11%bv ltac:(vm_compute; lia)).
    + exact RP.
    + apply (CK.samem_frame_but (fun a0 => ~ (sp - 48 <= a0 < sp) /\ ~ (1009736 <= a0 < 1010280))).
      * apply (TK.frame_samem _ _ _ _ _ _ _ HLF). intros a0 Ha [Hk1 Hk2]. cbn [CC.cp_F]. tk_outside.
      * intros a0 Ha. pose proof (Ha (sp - 128, 128) ltac:(ck_in)) as X1. pose proof (Ha (0xf6848, 544) ltac:(ck_in)) as X2. unfold L5.in_rng in *. cbn [fst snd] in *. lia.
    + exact (CC.lf_grows _ _ _ _ _ _ _ HLF).
Qed.
End S.
End SKC.
