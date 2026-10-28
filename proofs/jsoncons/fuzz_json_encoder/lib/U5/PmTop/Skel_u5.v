(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OssFuzzTheorems.jsoncons.fuzz_json_encoder.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib Require Import PropExec CatExec CatSim SeqExec StoreOk StreamSim Hoare ShapeAlg SpinAlg
  AxSymExec3 AxSymExec3B AxSymExec3Sound AxSymRun3 AsanPlanCore AsanPlan AsanPlanSound AsanPlanSoundSums LibSym SegRun SegPlan SegPlanAuto
  HeapIface L5Defs L5Core. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5 Require Import Pm6PlanKit_u5 PmLibDefs_u5 PmLibSpecs_u5 PmLayout_u5.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.CutCert Require Import CutCert CutOps CutHeap CutAuto CutLib. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5.CutCert Require Import Pm6CutKit_u5. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.CutCert Require Import CutL5.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5.PmTop Require Import TopKit_u5 TopKit2_u5 TopSpecs_u5 ReadKit_u5 ChunkKit_u5.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5.CutGen Require Cut_locale_xsrc_u5 Cut_guard_xsrc_u5 Cut_syscat_xsrc_u5 Cut_atexit_xsrc_u5.
Import ListNotations. Import AX2. Import AX2B. Import AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Module SK.
Module GL := Cut_locale_xsrc_u5.  Module GG := Cut_guard_xsrc_u5.  Module GS := Cut_syscat_xsrc_u5.  Module GX := Cut_atexit_xsrc_u5.
Abbreviation RSEGS := PML.RSEGS.
Abbreviation mem := (word -> option byte).
Lemma ret_lc : CL.is_ret_at RSEGS 0x9475c. Proof. CL.solve_is_ret. Qed.
Lemma ret_ga : CL.is_ret_at RSEGS 0x4bb80. Proof. CL.solve_is_ret. Qed.
Lemma ret_gr : CL.is_ret_at RSEGS 0x4bba8. Proof. CL.solve_is_ret. Qed.
Lemma ret_sc : CL.is_ret_at RSEGS 0x6ed90. Proof. CL.solve_is_ret. Qed.
Lemma ret_ax : CL.is_ret_at RSEGS 0xad7f8. Proof. CL.solve_is_ret. Qed.
(* [comment removed for export] *)
Lemma u64_of_word : forall (M : mem) A (w : word) z, L5.u64_at RSEGS M A (bv_unsigned w) -> w = Z_to_bv 64 z -> L5.u64_at RSEGS M A z.
Proof. intros M A w z H E. unfold L5.u64_at in *. rewrite Z_to_bv_bv_unsigned in H. rewrite <- E. exact H. Qed.
(* [comment removed for export] *)
Definition KRA : list nat := 1%nat :: CK.CSR.
Lemma csr_kra : forall q, In q CK.CSR -> In q KRA. Proof. intros q H. right. exact H. Qed.
Lemma guard_wr : StreamSim.wseg_ok RSEGS (Z_to_bv 64 0xdb840) 2 = true. Proof. vm_compute. reflexivity. Qed.

Section S.
Context {SCFG_P : ScfgP}.
Variable L : heap_layout.
Hypothesis FPM : forall (fx fx' : FPState) R pc M R' pc' M',
  msteps RSEGS (@mkst fx R (Z_to_bv 64 pc) M (seg_rom RSEGS)) (@mkst fx' R' (Z_to_bv 64 pc') M' (seg_rom RSEGS)) -> PML.fp_ok fx -> PML.fp_ok fx'.

(* [comment removed for export] *)
Lemma fin_ret : forall c ps sp0 R gl bl E' R' (M M' : mem) (fx' : FPState) model K pc rav,
  CC.leaf_facts RSEGS c ps E' R' M M' -> env_agree 64 (CK.hvB sp0 R gl bl) E' -> CL.is_ret_at RSEGS pc -> m_halted model = None -> m_vm_lazy model = [] ->
  CL.ps_reg_is ps 2 (EVar 2) = true -> TK.keeps_hv ps KRA = true -> getr R 1%bv = Z_to_bv 64 rav -> L5.ra_ok rav -> getr R 2%bv = Z_to_bv 64 sp0 -> 0 <= sp0 < 2 ^ 64 ->
  (regs_preserved R R' -> srealizes RSEGS SCFG (@PML.cfg fx' R' rav M' model) K) ->
  srealizes RSEGS SCFG (@PML.cfg fx' R' pc M' model) K.
Proof.
  intros c ps sp0 R gl bl E' R' M M' fx' model K pc rav HLF Hag Hret Hh Hl Gsp Gk H1 Hra H2 Hsp Hcont.
  assert (R1 : getr R' 1%bv = Z_to_bv 64 rav) by (rewrite (CK.keeps_hvB_sound _ _ _ _ _ _ _ _ _ _ KRA 1%bv HLF Gk Hag ltac:(ck_in)); exact H1).
  apply (CK.ret_leaf fx' R' pc M' model K rav Hret Hh Hl R1 Hra). apply Hcont.
  apply CK.rp_of_keeps.
  - rewrite <- (ridx_roundtrip 2%bv) at 1. etransitivity; [exact (CL.ps_reg_is_sound RSEGS _ _ _ _ _ _ _ _ HLF Gsp)|]. cbn [edenot]. rewrite <- (proj1 Hag 2%nat) by lia. rewrite H2. reflexivity.
  - intros q Hq. exact (CK.keeps_hvB_sound _ _ _ _ _ _ _ _ _ _ KRA q HLF Gk Hag (csr_kra _ Hq)).
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Theorem locale_ctor_later_ok : PMS.locale_ctor_later_spec L.
Proof.
  intros o sp r fx R M model K Hh Hl HK0 Hfp (EN & A0 & (LD1 & LD2) & RO & (O1 & O2 & O3) & DO) Hcont.
  destruct EN as (Hra & Hrok & Hsp & Htp & (S1 & S2 & S3 & S4 & S5)). unfold PML.a0 in A0.
  change PML.PC_LOCALE_CTOR with (CC.cp_pc GL.cp0).
  ck_open FPM GL.cp0 (GL.plans 0%nat _ eq_refl) 0 (@nil Z) (fun _ : nat => @nil byte) (@nil (nat * Z)) sp R M fx model K Hh Hl Hfp Hsp ck_no_pins.
  - ck_reg E (10%bv : reg) A0.
    unfold know_ok, GL.cp0. cbn [CC.cp_know]. repeat (apply Forall_cons); [.. | apply Forall_nil].
    + e_range. + e_align S1. + e_unk. + e_wr. + e_range.
    + ck_kw8 899648 1 LD1. + unfold PML.CLASSIC_IMP in LD2. ck_kw64 899640 900688 LD2. + e_unk. + e_wr. + e_disj.
  - intros fx' E' R' M' k ps Hnth Hag HLF Hfp'.
    ck_reg E (10%bv : reg) A0. ck_leaf Hag E'.
    ck_leaf_k k Hnth; [|ck_leaf_end k Hnth].
    apply (fin_ret _ _ sp R _ _ E' R' M M' fx' model K _ r HLF Hag64 ret_lc Hh Hl eq_refl eq_refl Hra Hrok Hsp ltac:(lia)). intros RP.
    apply (Hcont fx' R' M' Hfp').
    + unfold PML.u64, PML.CLASSIC_IMP. ck_cell64 HLF (EVar 42) 0 (ELit 900688). reflexivity.
    + exact RP.
    + apply (CK.samem_frame_but (fun a => ~ (sp - 32 <= a < sp) /\ ~ (o <= a < o + 8))).
      * apply (TK.frame_samem _ _ _ _ _ _ _ HLF). intros a Ha [Hk1 Hk2]. cbn [CC.cp_F]. tk_outside.
      * intros a Ha. pose proof (Ha (sp - 32, 32) ltac:(ck_in)) as X1. pose proof (Ha (o, 8) ltac:(ck_in)) as X2. unfold L5.in_rng in *. cbn [fst snd] in *. lia.
    + exact (CC.lf_grows _ _ _ _ _ _ _ HLF).
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Theorem guard_acquire_ok : PMS.guard_acquire_spec L.
Proof.
  intros G sp r fx R M model K Hh Hl HK0 Hfp (EN & A0 & HG & C0 & C1 & WR) Hcont.
  destruct EN as (Hra & Hrok & Hsp & Htp & (S1 & S2 & S3 & S4 & S5)). unfold PML.a0 in A0.
  change PML.PC_GUARD_ACQ with (CC.cp_pc GG.cp0).
  ck_open FPM GG.cp0 (GG.plans 0%nat _ eq_refl) 0 (@nil Z) (fun _ : nat => @nil byte) (@nil (nat * Z)) sp R M fx model K Hh Hl Hfp Hsp ck_no_pins.
  - ck_reg E (10%bv : reg) A0.
    unfold know_ok, GG.cp0. cbn [CC.cp_know]. repeat (apply Forall_cons); [.. | apply Forall_nil].
    + e_range. + e_align S1. + e_range. + ck_kw8 G 0 C0. + ck_kw8 (G + 1) 0 C1.
    + eapply CK.kwr_of_writable with (A := G) (N := 2); [ev_start | ev_len | lia | lia | exact WR].
  - intros fx' E' R' M' k ps Hnth Hag HLF Hfp'.
    ck_reg E (10%bv : reg) A0. ck_leaf Hag E'.
    ck_leaf_k k Hnth; [|ck_leaf_end k Hnth].
    apply (fin_ret _ _ sp R _ _ E' R' M M' fx' model K _ r HLF Hag64 ret_ga Hh Hl eq_refl eq_refl Hra Hrok Hsp ltac:(lia)). intros RP.
    apply (Hcont fx' R' M' Hfp').
    + split; [unfold PML.a0; tk_lin HLF (10%bv : reg)|]. unfold PML.u8.
      split; [ck_cell8 HLF (EVar 42) 0 (ELit 0); reflexivity | ck_cell8 HLF (EVar 42) 1 (ELit 2); reflexivity].
    + exact RP.
    + apply (CK.samem_frame_but (fun a => ~ (G <= a < G + 2))).
      * apply (TK.frame_samem _ _ _ _ _ _ _ HLF). intros a Ha Hk1. cbn [CC.cp_F]. tk_outside.
      * intros a Ha. pose proof (Ha (G, 2) ltac:(ck_in)) as X2. unfold L5.in_rng in *. cbn [fst snd] in *. lia.
    + exact (CC.lf_grows _ _ _ _ _ _ _ HLF).
Qed.

Theorem guard_release_ok : PMS.guard_release_spec L.
Proof.
  intros G sp r fx R M model K Hh Hl HK0 Hfp (EN & A0 & HG & WR) Hcont.
  destruct EN as (Hra & Hrok & Hsp & Htp & (S1 & S2 & S3 & S4 & S5)). unfold PML.a0 in A0.
  change PML.PC_GUARD_REL with (CC.cp_pc GG.cp1).
  ck_open FPM GG.cp1 (GG.plans 1%nat _ eq_refl) 0 (@nil Z) (fun _ : nat => @nil byte) (@nil (nat * Z)) sp R M fx model K Hh Hl Hfp Hsp ck_no_pins.
  - ck_reg E (10%bv : reg) A0.
    unfold know_ok, GG.cp1. cbn [CC.cp_know]. repeat (apply Forall_cons); [.. | apply Forall_nil].
    + e_range. + e_align S1. + e_range.
    + eapply CK.kwr_of_writable with (A := G) (N := 2); [ev_start | ev_len | lia | lia | exact WR].
  - intros fx' E' R' M' k ps Hnth Hag HLF Hfp'.
    ck_reg E (10%bv : reg) A0. ck_leaf Hag E'.
    ck_leaf_k k Hnth; [|ck_leaf_end k Hnth].
    apply (fin_ret _ _ sp R _ _ E' R' M M' fx' model K _ r HLF Hag64 ret_gr Hh Hl eq_refl eq_refl Hra Hrok Hsp ltac:(lia)). intros RP.
    apply (Hcont fx' R' M' Hfp').
    + unfold PML.u8. split; [ck_cell8 HLF (EVar 42) 0 (ELit 1); reflexivity | ck_cell8 HLF (EVar 42) 1 (ELit 1); reflexivity].
    + exact RP.
    + apply (CK.samem_frame_but (fun a => ~ (G <= a < G + 2))).
      * apply (TK.frame_samem _ _ _ _ _ _ _ HLF). intros a Ha Hk1. cbn [CC.cp_F]. tk_outside.
      * intros a Ha. pose proof (Ha (G, 2) ltac:(ck_in)) as X2. unfold L5.in_rng in *. cbn [fst snd] in *. lia.
    + exact (CC.lf_grows _ _ _ _ _ _ _ HLF).
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Theorem system_category_ok : PMS.system_category_spec L.
Proof.
  intros sp r fx R M model K Hh Hl HK0 Hfp (EN & RO & CASE) Hcont.
  destruct EN as (Hra & Hrok & Hsp & Htp & (S1 & S2 & S3 & S4 & S5)).
  destruct CASE as [[C0 C1] | C0].
  - (* [comment removed for export] *)
    change PML.PC_SYSTEM_CATEGORY with (CC.cp_pc GS.cp1).
    ck_open FPM GS.cp1 (GS.plans 1%nat _ eq_refl) 0 (@nil Z) (fun _ : nat => @nil byte) (@nil (nat * Z)) sp R M fx model K Hh Hl Hfp Hsp ck_no_pins.
    + unfold know_ok, GS.cp1. cbn [CC.cp_know]. repeat (apply Forall_cons); [.. | apply Forall_nil].
      * e_range. * e_align S1. * e_unk. * e_wr. * ck_kw8 899136 0 C0. * ck_kw8 899137 0 C1.
      * eapply CK.kwr_of_writable with (A := 899136) (N := 2); [ev_start | ev_len | lia | lia | exact (CK.writable_static M 0xdb840 2 guard_wr ltac:(lia) ltac:(lia))].
    + intros fx' E' R' M' k ps Hnth Hag HLF Hfp'. ck_leaf Hag E'.
      ck_leaf_k k Hnth; [|ck_leaf_end k Hnth].
      apply (fin_ret _ _ sp R _ _ E' R' M M' fx' model K _ r HLF Hag64 ret_sc Hh Hl eq_refl eq_refl Hra Hrok Hsp ltac:(lia)). intros RP.
      apply (Hcont fx' R' M' Hfp').
      * split; [unfold PML.a0, PML.OBJ_SYSTEM_CATEGORY; tk_lin HLF (10%bv : reg)|]. unfold PML.u8. ck_cell8 HLF (ELit 0) 899136 (ELit 1). reflexivity.
      * exact RP.
      * apply (CK.samem_frame_but (fun a => ~ (sp - 16 <= a < sp) /\ ~ (899136 <= a < 899138))).
        -- apply (TK.frame_samem _ _ _ _ _ _ _ HLF). intros a Ha [Hk1 Hk2]. cbn [CC.cp_F]. tk_outside.
        -- intros a Ha. pose proof (Ha (sp - 64, 64) ltac:(ck_in)) as X1. pose proof (Ha (0xdb840, 2) ltac:(ck_in)) as X2. unfold L5.in_rng in *. cbn [fst snd] in *. lia.
      * exact (CC.lf_grows _ _ _ _ _ _ _ HLF).
  - (* [comment removed for export] *)
    change PML.PC_SYSTEM_CATEGORY with (CC.cp_pc GS.cp0).
    ck_open FPM GS.cp0 (GS.plans 0%nat _ eq_refl) 0 (@nil Z) (fun _ : nat => @nil byte) (@nil (nat * Z)) sp R M fx model K Hh Hl Hfp Hsp ck_no_pins.
    + unfold know_ok, GS.cp0. cbn [CC.cp_know]. repeat (apply Forall_cons); [.. | apply Forall_nil].
      * e_range. * e_align S1. * ck_kw8 899136 1 C0.
    + intros fx' E' R' M' k ps Hnth Hag HLF Hfp'. ck_leaf Hag E'. pose proof (TK.frame_nil _ _ _ _ _ _ HLF eq_refl) as EQ. subst M'.
      ck_leaf_k k Hnth; [|ck_leaf_end k Hnth].
      apply (fin_ret _ _ sp R _ _ E' R' M M fx' model K _ r HLF Hag64 ret_sc Hh Hl eq_refl eq_refl Hra Hrok Hsp ltac:(lia)). intros RP.
      apply (Hcont fx' R' M Hfp').
      * split; [unfold PML.a0, PML.OBJ_SYSTEM_CATEGORY; tk_lin HLF (10%bv : reg) | exact C0].
      * exact RP.
      * apply L5.frame_but_refl.
      * apply mem_grows_refl.
Qed.
(* [comment removed for export] *)
(* [comment removed for export] *)
Theorem cxa_atexit_ok : PMS.cxa_atexit_spec L.
Proof.
  intros f a dso sp r fx R M model K Hh Hl HK0 Hfp (EN & A0 & A1 & A2 & (C0 & C4 & C8 & C16 & C24 & C32 & C288 & _) & WR & (Q1 & Q2)) Hcont.   (* [comment removed for export] *)
  destruct EN as (Hra & Hrok & Hsp & Htp & (S1 & S2 & S3 & S4 & S5)). unfold PML.a0, PML.a1 in A0, A1. cbn [length Z.of_nat Z.add] in C8. unfold PML.NEED_LOCKS in Q1. unfold PML.AX, PML.ATEXIT_CALL, PML.AEF_EXIT_GUARD in C0, C4, C8, C16, C24, C32, C288. cbn [Z.add] in C4, C8, C16, C24, C32, C288.
  change PML.PC_CXA_ATEXIT with (CC.cp_pc GX.cp0).
  ck_open FPM GX.cp0 (GX.plans 0%nat _ eq_refl) 0 (@nil Z) (fun _ : nat => @nil byte) (@nil (nat * Z)) sp R M fx model K Hh Hl Hfp Hsp ck_no_pins.
  - unfold know_ok, GX.cp0. cbn [CC.cp_know]. repeat (apply Forall_cons); [.. | apply Forall_nil].
    + e_range. + e_align S1. + e_unk. + e_wr.
    + ck_kw8 1036963 0 Q1. + ck_kw8 1036376 0 C0. + ck_kw32 1036380 0 C4. + ck_kw32 1036384 1 C8. + ck_kw64 1036392 1036400 C16. + ck_kw64 1036400 0 C24. + ck_kw64 1036408 710848 C32. + ck_kw64 1036664 239000 C288.
    + eapply CK.kwr_of_writable with (A := 1036376) (N := 544); [ev_start | ev_len | lia | lia | exact WR].
  - intros fx' E' R' M' k ps Hnth Hag HLF Hfp'. ck_leaf Hag E'.
    ck_leaf_k k Hnth; [|ck_leaf_end k Hnth].
    apply (fin_ret _ _ sp R _ _ E' R' M M' fx' model K _ r HLF Hag64 ret_ax Hh Hl eq_refl eq_refl Hra Hrok Hsp ltac:(lia)). intros RP.
    assert (REG : forall (q : reg), (32 + ridx q < 64)%nat -> ev E' (32 + ridx q) = getr R q).
    { intros q Hq. rewrite <- (proj1 Hag64 (32 + ridx q)%nat Hq). exact (CK.hvB_reg _ _ _ _ q). }
    apply (Hcont fx' R' M' Hfp').
    + split; [unfold PML.a0; tk_lin HLF (10%bv : reg)|]. unfold PML.atexit_cells, PML.u8, PML.u32, PML.u64, PML.AX, PML.ATEXIT_CALL, PML.AEF_EXIT_GUARD. cbn [length Z.of_nat Z.add].
      split; [ck_cell8 HLF (ELit 0) 1036376 (ELit 0); reflexivity|]. split; [ck_cell32 HLF (ELit 0) 1036380 (ELit 0); reflexivity|]. split; [ck_cell32 HLF (ELit 0) 1036384 (ELit 2); reflexivity|].
      split; [ck_cell64 HLF (ELit 0) 1036392 (ELit 1036400); reflexivity|]. split; [ck_cell64 HLF (ELit 0) 1036400 (ELit 0); reflexivity|].
      split; [ck_cell64 HLF (ELit 0) 1036408 (ELit 710848); reflexivity|]. split; [ck_cell64 HLF (ELit 0) 1036664 (ELit 239000); reflexivity|].   (* [comment removed for export] *)
      split.
      * apply (u64_of_word M' _ (getr R 10%bv) f); [|exact A0]. ck_cell64 HLF (ELit 0) 1036416 (EVar 42). cbn [edenot]. f_equal. exact (REG 10%bv ltac:(vm_compute; lia)).
      * apply (u64_of_word M' _ (getr R 11%bv) a); [|exact A1]. ck_cell64 HLF (ELit 0) 1036672 (EVar 43). cbn [edenot]. f_equal. exact (REG 11%bv ltac:(vm_compute; lia)).
    + exact RP.
    + apply (CK.samem_frame_but (fun a0 => ~ (sp - 48 <= a0 < sp) /\ ~ (1036376 <= a0 < 1036920))).
      * apply (TK.frame_samem _ _ _ _ _ _ _ HLF). intros a0 Ha [Hk1 Hk2]. cbn [CC.cp_F]. tk_outside.
      * intros a0 Ha. pose proof (Ha (sp - 128, 128) ltac:(ck_in)) as X1. pose proof (Ha (0xfd058, 544) ltac:(ck_in)) as X2. unfold L5.in_rng in *. cbn [fst snd] in *. lia.
    + exact (CC.lf_grows _ _ _ _ _ _ _ HLF).
Qed.
End S.
End SK.
