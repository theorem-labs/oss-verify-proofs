(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OssFuzzTheorems.jsoncons.fuzz_json_cursor.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib Require Import PropExec CatExec CatSim SeqExec StoreOk StreamSim Hoare ShapeAlg SpinAlg
  AxSymExec3 AxSymExec3B AxSymExec3Sound AxSymRun3 AsanPlanCore AsanPlan AsanPlanSound AsanPlanSoundSums LibSym SegRun SegPlan SegPlanAuto
  HeapIface L5Defs L5Core. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U Require Import Pm10PlanKit_u PmLibDefs_u PmCurDefs_u PmLibSpecs_u PmLayout_u.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.CutCert Require Import CutCert CutOps CutHeap CutAuto CutLib. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U.CutCert Require Import Pm10CutKit_u. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.CutCert Require Import CutL5.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U.PmTop Require Import TopKit_u TopKit2_u TopSpecs_u ReadKit_u ChunkKit_u Skel_u.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U.CutGen Require Cut_visit_null_csrc_u Cut_visit_bool_csrc_u Cut_visit_u64_csrc_u Cut_visit_i64_csrc_u Cut_visit_key_csrc_u Cut_visit_string_csrc_u
  Cut_visit_begin_object_csrc_u Cut_visit_end_object_csrc_u Cut_visit_begin_array_csrc_u Cut_visit_end_array_csrc_u.
Import ListNotations. Import AX2. Import AX2B. Import AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Module VIS.
Abbreviation RSEGS := PML.RSEGS.
Abbreviation mem := (word -> option byte).

Lemma blob_of_defined : forall (M : mem) A, 0 <= A -> A + 8 <= 2 ^ 64 -> L5.defined M A 8 ->
  exists bs : list byte, length bs = 8%nat /\ L5.bytes_at RSEGS M A (map bv_unsigned bs).
Proof.
  intros M A H0 H1 HD.
  destruct (AX2S.rdn_defined RSEGS M 8 (Z_to_bv 64 A)) as (bs & Hr & Hl).
  - rewrite u64_of_Z by lia. cbn. lia.
  - intros j Hj. unfold AX2S.rd1. rewrite u64_of_Z by lia. pose proof (HD (Z.of_nat j) ltac:(lia)) as X.
    destruct (M (Z_to_bv 64 (A + Z.of_nat j))); [discriminate | exfalso; apply X; reflexivity].
  - exists bs. split; [exact Hl|]. rewrite <- Hl in Hr. apply (L5C.rdn_bytes_at RSEGS M bs A H0); [rewrite Hl; cbn; lia | exact Hr].
Qed.
Lemma blob_map : forall bs : list byte, bs = map (Z_to_bv 8) (map bv_unsigned bs).
Proof. intros bs. rewrite map_map. symmetry. rewrite <- (map_id bs) at 2. apply map_ext. intros b. apply (Z_to_bv_bv_unsigned _ b). Qed.

Lemma ev_defined : forall (M M' : mem) V, L5.defined M V 48 -> mem_grows M M' -> L5.defined M' (V + 8) 40.
Proof. intros M M' V H G. apply (L5.defined_grows M M' _ _ G). eapply (L5.defined_sub _ _ _ _ _ H); lia. Qed.
Lemma u64_norm : forall (M : mem) A z, L5.u64_at RSEGS M A z -> L5.u64_at RSEGS M A (bv_unsigned (Z_to_bv 64 z)).
Proof. intros M A z H. unfold L5.u64_at in *. rewrite Z_to_bv_bv_unsigned. exact H. Qed.

Module GN := Cut_visit_null_csrc_u.
Lemma ret_null : CL.is_ret_at RSEGS 0x41f2c. Proof. CL.solve_is_ret. Qed.

Module GBO := Cut_visit_begin_object_csrc_u.
Lemma ret_begin_object : CL.is_ret_at RSEGS 0x41d88. Proof. CL.solve_is_ret. Qed.

Module GBA := Cut_visit_begin_array_csrc_u.
Lemma ret_begin_array : CL.is_ret_at RSEGS 0x41ea0. Proof. CL.solve_is_ret. Qed.

Module GEO := Cut_visit_end_object_csrc_u.
Lemma ret_end_object : CL.is_ret_at RSEGS 0x41e44. Proof. CL.solve_is_ret. Qed.

Module GEA := Cut_visit_end_array_csrc_u.
Lemma ret_end_array : CL.is_ret_at RSEGS 0x41cbc. Proof. CL.solve_is_ret. Qed.

Module GB := Cut_visit_bool_csrc_u.
Lemma ret_bool : CL.is_ret_at RSEGS 0x41f50. Proof. CL.solve_is_ret. Qed.

Module GU := Cut_visit_u64_csrc_u.
Lemma ret_u64 : CL.is_ret_at RSEGS 0x41ce0. Proof. CL.solve_is_ret. Qed.

Module GI := Cut_visit_i64_csrc_u.
Lemma ret_i64 : CL.is_ret_at RSEGS 0x41d04. Proof. CL.solve_is_ret. Qed.

Module GK := Cut_visit_key_csrc_u.
Lemma ret_key : CL.is_ret_at RSEGS 0x41ed0. Proof. CL.solve_is_ret. Qed.

Module GS := Cut_visit_string_csrc_u.
Lemma ret_string : CL.is_ret_at RSEGS 0x41f7c. Proof. CL.solve_is_ret. Qed.

Section S.
Context {SCFG_P : ScfgP}.
Variable L : heap_layout.
Hypothesis FPM : forall (fx fx' : FPState) R pc M R' pc' M',
  msteps RSEGS (@mkst fx R (Z_to_bv 64 pc) M (seg_rom RSEGS)) (@mkst fx' R' (Z_to_bv 64 pc') M' (seg_rom RSEGS)) -> PML.fp_ok fx -> PML.fp_ok fx'.

Theorem visit_null_ok : PMS.visit_null_spec L PMS.PC_VIS_NULL.
Proof.
  intros V sp r fx R M model K Hh Hl HK0 Hfp (EN & A0 & (VP & VD) & (O1 & O2 & O3) & _) Hcont.
  destruct EN as (Hra & Hrok & Hsp & Htp & (S1 & S2 & S3 & S4 & S5)). unfold PML.a0 in A0. pose proof (L5C.stk_floor _ _ _ _ (conj S1 (conj S2 (conj S3 (conj S4 S5))))) as FLR. unfold PMS.VIS_SCR in *.
  destruct (blob_of_defined M (sp + (-56)) ltac:(lia) ltac:(lia) ltac:(eapply (L5.defined_sub _ _ _ _ _ S5); unfold PMS.VIS_SCR; lia)) as (bsb & Hbl & Hbat).
  change PMS.PC_VIS_NULL with (CC.cp_pc GN.cp0).
  ck_open FPM GN.cp0 (GN.plans 0%nat _ eq_refl) 0 (@nil Z) (fun _ : nat => bsb) (@nil (nat * Z)) sp R M fx model K Hh Hl Hfp Hsp ck_no_pins.
  - ck_reg E (10%bv : reg) A0.
    unfold know_ok, GN.cp0. cbn [CC.cp_know]. repeat (apply Forall_cons); [.. | apply Forall_nil].
    + e_range. + e_align S1. + e_range. + e_unk. + e_wr. + e_unk. + e_wr. + e_disj.
    + eapply CL5.kblob_intro with (A := sp + (-56)) (bs := map bv_unsigned bsb);
        [ev_start | rewrite length_map, Hbl; ev_len | lia | rewrite length_map, Hbl; cbn; lia | lia | cbn; apply blob_map | exact Hbat | rewrite length_map, Hbl; ev_def].
  - intros fx' E' R' M' k ps Hnth Hag HLF Hfp'.
    ck_reg E (10%bv : reg) A0. ck_leaf Hag E'.
    ck_leaf_k k Hnth; [|ck_leaf_end k Hnth].
    apply (SK.fin_ret _ _ sp R _ _ E' R' M M' fx' model K _ r HLF Hag64 ret_null Hh Hl eq_refl eq_refl Hra Hrok Hsp ltac:(lia)). intros RPv.
    apply (Hcont fx' R' M' Hfp').
    + split; [unfold PML.a0; tk_lin HLF (10%bv : reg)|]. exists PMCUR.EvNull. split; [reflexivity|].
      unfold PMCUR.ev_at. split; [exact (ev_defined M M' V VD (CC.lf_grows _ _ _ _ _ _ _ HLF)) | ck_cell64 HLF (EVar 42) 8 (ELit 4); reflexivity].
    + exact RPv.
    + apply (CK.samem_frame_but (fun a => ~ (sp - 64 <= a < sp) /\ ~ (V + 8 <= a < V + 48))).
      * apply (TK.frame_samem _ _ _ _ _ _ _ HLF). intros a Ha [Hk1 Hk2]. cbn [CC.cp_F]. tk_outside.
      * intros a Ha. pose proof (Ha (sp - 64, 64) ltac:(ck_in)) as X1. pose proof (Ha (V + 8, 40) ltac:(ck_in)) as X2. unfold L5.in_rng in *. cbn [fst snd] in *. lia.
    + exact (CC.lf_grows _ _ _ _ _ _ _ HLF).
Qed.

Theorem visit_begin_object_ok : PMS.visit_begin_object_spec L PMS.PC_VIS_BEGIN_OBJECT_TAG.
Proof.
  intros V sp r fx R M model K Hh Hl HK0 Hfp (EN & A0 & (VP & VD) & (O1 & O2 & O3) & _) Hcont.
  destruct EN as (Hra & Hrok & Hsp & Htp & (S1 & S2 & S3 & S4 & S5)). unfold PML.a0 in A0. pose proof (L5C.stk_floor _ _ _ _ (conj S1 (conj S2 (conj S3 (conj S4 S5))))) as FLR. unfold PMS.VIS_SCR in *.
  destruct (blob_of_defined M (sp + (-56)) ltac:(lia) ltac:(lia) ltac:(eapply (L5.defined_sub _ _ _ _ _ S5); unfold PMS.VIS_SCR; lia)) as (bsb & Hbl & Hbat).
  change PMS.PC_VIS_BEGIN_OBJECT_TAG with (CC.cp_pc GBO.cp0).
  ck_open FPM GBO.cp0 (GBO.plans 0%nat _ eq_refl) 0 (@nil Z) (fun _ : nat => bsb) (@nil (nat * Z)) sp R M fx model K Hh Hl Hfp Hsp ck_no_pins.
  - ck_reg E (10%bv : reg) A0.
    unfold know_ok, GBO.cp0. cbn [CC.cp_know]. repeat (apply Forall_cons); [.. | apply Forall_nil].
    + e_range. + e_align S1. + e_range. + e_unk. + e_wr. + e_unk. + e_wr. + e_disj.
    + eapply CL5.kblob_intro with (A := sp + (-56)) (bs := map bv_unsigned bsb);
        [ev_start | rewrite length_map, Hbl; ev_len | lia | rewrite length_map, Hbl; cbn; lia | lia | cbn; apply blob_map | exact Hbat | rewrite length_map, Hbl; ev_def].
  - intros fx' E' R' M' k ps Hnth Hag HLF Hfp'.
    ck_reg E (10%bv : reg) A0. ck_leaf Hag E'.
    ck_leaf_k k Hnth; [|ck_leaf_end k Hnth].
    apply (SK.fin_ret _ _ sp R _ _ E' R' M M' fx' model K _ r HLF Hag64 ret_begin_object Hh Hl eq_refl eq_refl Hra Hrok Hsp ltac:(lia)). intros RPv.
    apply (Hcont fx' R' M' Hfp').
    + split; [unfold PML.a0; tk_lin HLF (10%bv : reg)|]. exists PMCUR.EvBeginObj. split; [reflexivity|].
      unfold PMCUR.ev_at. split; [exact (ev_defined M M' V VD (CC.lf_grows _ _ _ _ _ _ _ HLF)) | ck_cell64 HLF (EVar 42) 8 (ELit 256); reflexivity].
    + exact RPv.
    + apply (CK.samem_frame_but (fun a => ~ (sp - 64 <= a < sp) /\ ~ (V + 8 <= a < V + 48))).
      * apply (TK.frame_samem _ _ _ _ _ _ _ HLF). intros a Ha [Hk1 Hk2]. cbn [CC.cp_F]. tk_outside.
      * intros a Ha. pose proof (Ha (sp - 64, 64) ltac:(ck_in)) as X1. pose proof (Ha (V + 8, 40) ltac:(ck_in)) as X2. unfold L5.in_rng in *. cbn [fst snd] in *. lia.
    + exact (CC.lf_grows _ _ _ _ _ _ _ HLF).
Qed.

Theorem visit_begin_array_ok : PMS.visit_begin_array_spec L PMS.PC_VIS_BEGIN_ARRAY_TAG.
Proof.
  intros V sp r fx R M model K Hh Hl HK0 Hfp (EN & A0 & (VP & VD) & (O1 & O2 & O3) & _) Hcont.
  destruct EN as (Hra & Hrok & Hsp & Htp & (S1 & S2 & S3 & S4 & S5)). unfold PML.a0 in A0. pose proof (L5C.stk_floor _ _ _ _ (conj S1 (conj S2 (conj S3 (conj S4 S5))))) as FLR. unfold PMS.VIS_SCR in *.
  destruct (blob_of_defined M (sp + (-56)) ltac:(lia) ltac:(lia) ltac:(eapply (L5.defined_sub _ _ _ _ _ S5); unfold PMS.VIS_SCR; lia)) as (bsb & Hbl & Hbat).
  change PMS.PC_VIS_BEGIN_ARRAY_TAG with (CC.cp_pc GBA.cp0).
  ck_open FPM GBA.cp0 (GBA.plans 0%nat _ eq_refl) 0 (@nil Z) (fun _ : nat => bsb) (@nil (nat * Z)) sp R M fx model K Hh Hl Hfp Hsp ck_no_pins.
  - ck_reg E (10%bv : reg) A0.
    unfold know_ok, GBA.cp0. cbn [CC.cp_know]. repeat (apply Forall_cons); [.. | apply Forall_nil].
    + e_range. + e_align S1. + e_range. + e_unk. + e_wr. + e_unk. + e_wr. + e_disj.
    + eapply CL5.kblob_intro with (A := sp + (-56)) (bs := map bv_unsigned bsb);
        [ev_start | rewrite length_map, Hbl; ev_len | lia | rewrite length_map, Hbl; cbn; lia | lia | cbn; apply blob_map | exact Hbat | rewrite length_map, Hbl; ev_def].
  - intros fx' E' R' M' k ps Hnth Hag HLF Hfp'.
    ck_reg E (10%bv : reg) A0. ck_leaf Hag E'.
    ck_leaf_k k Hnth; [|ck_leaf_end k Hnth].
    apply (SK.fin_ret _ _ sp R _ _ E' R' M M' fx' model K _ r HLF Hag64 ret_begin_array Hh Hl eq_refl eq_refl Hra Hrok Hsp ltac:(lia)). intros RPv.
    apply (Hcont fx' R' M' Hfp').
    + split; [unfold PML.a0; tk_lin HLF (10%bv : reg)|]. exists PMCUR.EvBeginArr. split; [reflexivity|].
      unfold PMCUR.ev_at. split; [exact (ev_defined M M' V VD (CC.lf_grows _ _ _ _ _ _ _ HLF)) | ck_cell64 HLF (EVar 42) 8 (ELit 1024); reflexivity].
    + exact RPv.
    + apply (CK.samem_frame_but (fun a => ~ (sp - 64 <= a < sp) /\ ~ (V + 8 <= a < V + 48))).
      * apply (TK.frame_samem _ _ _ _ _ _ _ HLF). intros a Ha [Hk1 Hk2]. cbn [CC.cp_F]. tk_outside.
      * intros a Ha. pose proof (Ha (sp - 64, 64) ltac:(ck_in)) as X1. pose proof (Ha (V + 8, 40) ltac:(ck_in)) as X2. unfold L5.in_rng in *. cbn [fst snd] in *. lia.
    + exact (CC.lf_grows _ _ _ _ _ _ _ HLF).
Qed.

Theorem visit_end_object_ok : PMS.visit_end_object_spec L PMS.PC_VIS_END_OBJECT.
Proof.
  intros V sp r fx R M model K Hh Hl HK0 Hfp (EN & A0 & (VP & VD) & (O1 & O2 & O3) & _) Hcont.
  destruct EN as (Hra & Hrok & Hsp & Htp & (S1 & S2 & S3 & S4 & S5)). unfold PML.a0 in A0. pose proof (L5C.stk_floor _ _ _ _ (conj S1 (conj S2 (conj S3 (conj S4 S5))))) as FLR. unfold PMS.VIS_SCR in *.
  destruct (blob_of_defined M (sp + (-48)) ltac:(lia) ltac:(lia) ltac:(eapply (L5.defined_sub _ _ _ _ _ S5); unfold PMS.VIS_SCR; lia)) as (bsb & Hbl & Hbat).
  change PMS.PC_VIS_END_OBJECT with (CC.cp_pc GEO.cp0).
  ck_open FPM GEO.cp0 (GEO.plans 0%nat _ eq_refl) 0 (@nil Z) (fun _ : nat => bsb) (@nil (nat * Z)) sp R M fx model K Hh Hl Hfp Hsp ck_no_pins.
  - ck_reg E (10%bv : reg) A0.
    unfold know_ok, GEO.cp0. cbn [CC.cp_know]. repeat (apply Forall_cons); [.. | apply Forall_nil].
    + e_range. + e_align S1. + e_range. + e_unk. + e_wr. + e_unk. + e_wr. + e_disj.
    + eapply CL5.kblob_intro with (A := sp + (-48)) (bs := map bv_unsigned bsb);
        [ev_start | rewrite length_map, Hbl; ev_len | lia | rewrite length_map, Hbl; cbn; lia | lia | cbn; apply blob_map | exact Hbat | rewrite length_map, Hbl; ev_def].
  - intros fx' E' R' M' k ps Hnth Hag HLF Hfp'.
    ck_reg E (10%bv : reg) A0. ck_leaf Hag E'.
    ck_leaf_k k Hnth; [|ck_leaf_end k Hnth].
    apply (SK.fin_ret _ _ sp R _ _ E' R' M M' fx' model K _ r HLF Hag64 ret_end_object Hh Hl eq_refl eq_refl Hra Hrok Hsp ltac:(lia)). intros RPv.
    apply (Hcont fx' R' M' Hfp').
    + split; [unfold PML.a0; tk_lin HLF (10%bv : reg)|]. exists PMCUR.EvEndObj. split; [reflexivity|].
      unfold PMCUR.ev_at. split; [exact (ev_defined M M' V VD (CC.lf_grows _ _ _ _ _ _ _ HLF)) | ck_cell64 HLF (EVar 42) 8 (ELit 512); reflexivity].
    + exact RPv.
    + apply (CK.samem_frame_but (fun a => ~ (sp - 48 <= a < sp) /\ ~ (V + 8 <= a < V + 48))).
      * apply (TK.frame_samem _ _ _ _ _ _ _ HLF). intros a Ha [Hk1 Hk2]. cbn [CC.cp_F]. tk_outside.
      * intros a Ha. pose proof (Ha (sp - 64, 64) ltac:(ck_in)) as X1. pose proof (Ha (V + 8, 40) ltac:(ck_in)) as X2. unfold L5.in_rng in *. cbn [fst snd] in *. lia.
    + exact (CC.lf_grows _ _ _ _ _ _ _ HLF).
Qed.

Theorem visit_end_array_ok : PMS.visit_end_array_spec L PMS.PC_VIS_END_ARRAY.
Proof.
  intros V sp r fx R M model K Hh Hl HK0 Hfp (EN & A0 & (VP & VD) & (O1 & O2 & O3) & _) Hcont.
  destruct EN as (Hra & Hrok & Hsp & Htp & (S1 & S2 & S3 & S4 & S5)). unfold PML.a0 in A0. pose proof (L5C.stk_floor _ _ _ _ (conj S1 (conj S2 (conj S3 (conj S4 S5))))) as FLR. unfold PMS.VIS_SCR in *.
  destruct (blob_of_defined M (sp + (-48)) ltac:(lia) ltac:(lia) ltac:(eapply (L5.defined_sub _ _ _ _ _ S5); unfold PMS.VIS_SCR; lia)) as (bsb & Hbl & Hbat).
  change PMS.PC_VIS_END_ARRAY with (CC.cp_pc GEA.cp0).
  ck_open FPM GEA.cp0 (GEA.plans 0%nat _ eq_refl) 0 (@nil Z) (fun _ : nat => bsb) (@nil (nat * Z)) sp R M fx model K Hh Hl Hfp Hsp ck_no_pins.
  - ck_reg E (10%bv : reg) A0.
    unfold know_ok, GEA.cp0. cbn [CC.cp_know]. repeat (apply Forall_cons); [.. | apply Forall_nil].
    + e_range. + e_align S1. + e_range. + e_unk. + e_wr. + e_unk. + e_wr. + e_disj.
    + eapply CL5.kblob_intro with (A := sp + (-48)) (bs := map bv_unsigned bsb);
        [ev_start | rewrite length_map, Hbl; ev_len | lia | rewrite length_map, Hbl; cbn; lia | lia | cbn; apply blob_map | exact Hbat | rewrite length_map, Hbl; ev_def].
  - intros fx' E' R' M' k ps Hnth Hag HLF Hfp'.
    ck_reg E (10%bv : reg) A0. ck_leaf Hag E'.
    ck_leaf_k k Hnth; [|ck_leaf_end k Hnth].
    apply (SK.fin_ret _ _ sp R _ _ E' R' M M' fx' model K _ r HLF Hag64 ret_end_array Hh Hl eq_refl eq_refl Hra Hrok Hsp ltac:(lia)). intros RPv.
    apply (Hcont fx' R' M' Hfp').
    + split; [unfold PML.a0; tk_lin HLF (10%bv : reg)|]. exists PMCUR.EvEndArr. split; [reflexivity|].
      unfold PMCUR.ev_at. split; [exact (ev_defined M M' V VD (CC.lf_grows _ _ _ _ _ _ _ HLF)) | ck_cell64 HLF (EVar 42) 8 (ELit 2048); reflexivity].
    + exact RPv.
    + apply (CK.samem_frame_but (fun a => ~ (sp - 48 <= a < sp) /\ ~ (V + 8 <= a < V + 48))).
      * apply (TK.frame_samem _ _ _ _ _ _ _ HLF). intros a Ha [Hk1 Hk2]. cbn [CC.cp_F]. tk_outside.
      * intros a Ha. pose proof (Ha (sp - 64, 64) ltac:(ck_in)) as X1. pose proof (Ha (V + 8, 40) ltac:(ck_in)) as X2. unfold L5.in_rng in *. cbn [fst snd] in *. lia.
    + exact (CC.lf_grows _ _ _ _ _ _ _ HLF).
Qed.

Theorem visit_bool_ok : PMS.visit_bool_spec L PMS.PC_VIS_BOOL.
Proof.
  intros V sp r fx R M model K Hh Hl HK0 Hfp (EN & A0 & (VP & VD) & (O1 & O2 & O3) & (x & A1 & Hx)) Hcont.
  destruct EN as (Hra & Hrok & Hsp & Htp & (S1 & S2 & S3 & S4 & S5)). unfold PML.a0 in A0. pose proof (L5C.stk_floor _ _ _ _ (conj S1 (conj S2 (conj S3 (conj S4 S5))))) as FLR. unfold PMS.VIS_SCR in *.
  unfold PML.a1 in A1.
  change PMS.PC_VIS_BOOL with (CC.cp_pc GB.cp0).
  ck_open FPM GB.cp0 (GB.plans 0%nat _ eq_refl) 0 (@nil Z) (fun _ : nat => @nil byte) (@nil (nat * Z)) sp R M fx model K Hh Hl Hfp Hsp ck_no_pins.
  - ck_reg E (10%bv : reg) A0. ck_reg E (11%bv : reg) A1.
    unfold know_ok, GB.cp0. cbn [CC.cp_know]. repeat (apply Forall_cons); [.. | apply Forall_nil].
    + e_range. + e_align S1. + e_range. + e_unk. + e_wr. + e_range.
  - intros fx' E' R' M' k ps Hnth Hag HLF Hfp'.
    ck_reg E (10%bv : reg) A0. ck_reg E (11%bv : reg) A1. ck_leaf Hag E'.
    ck_leaf_k k Hnth; [|ck_leaf_end k Hnth].
    apply (SK.fin_ret _ _ sp R _ _ E' R' M M' fx' model K _ r HLF Hag64 ret_bool Hh Hl eq_refl eq_refl Hra Hrok Hsp ltac:(lia)). intros RPv.
    apply (Hcont fx' R' M' Hfp').
    + split; [unfold PML.a0; tk_lin HLF (10%bv : reg)|]. exists (PMCUR.EvBool (Z.eqb x 1)). split; [exists x; split; [exact A1 | split; [exact Hx | reflexivity]]|].
      unfold PMCUR.ev_at. split; [exact (ev_defined M M' V VD (CC.lf_grows _ _ _ _ _ _ _ HLF))|]. split; [ck_cell64 HLF (EVar 42) 8 (ELit 8); reflexivity|].
      ck_cell8 HLF (EVar 42) 32 (EVar 43). cbn [edenot]. destruct (Z.eqb_spec x 1) as [->|Nx]; [ck_atom | assert (x = 0) as -> by lia; ck_atom].
    + exact RPv.
    + apply (CK.samem_frame_but (fun a => ~ (V + 8 <= a < V + 48))).
      * apply (TK.frame_samem _ _ _ _ _ _ _ HLF). intros a Ha Hk. cbn [CC.cp_F]. tk_outside.
      * intros a Ha. pose proof (Ha (V + 8, 40) ltac:(ck_in)) as X2. unfold L5.in_rng in *. cbn [fst snd] in *. lia.
    + exact (CC.lf_grows _ _ _ _ _ _ _ HLF).
Qed.

Theorem visit_u64_ok : PMS.visit_u64_spec L PMS.PC_VIS_U64.
Proof.
  intros V sp r fx R M model K Hh Hl HK0 Hfp (EN & A0 & (VP & VD) & (O1 & O2 & O3) & _) Hcont.
  destruct EN as (Hra & Hrok & Hsp & Htp & (S1 & S2 & S3 & S4 & S5)). unfold PML.a0 in A0. pose proof (L5C.stk_floor _ _ _ _ (conj S1 (conj S2 (conj S3 (conj S4 S5))))) as FLR. unfold PMS.VIS_SCR in *.
  assert (A1 : getr R 11%bv = Z_to_bv 64 (bv_unsigned (getr R 11%bv))) by (symmetry; apply Z_to_bv_bv_unsigned). pose proof (bv_unsigned_in_range _ (getr R 11%bv)) as RA1. change (bv_modulus 64) with (2 ^ 64) in RA1.
  change PMS.PC_VIS_U64 with (CC.cp_pc GU.cp0).
  ck_open FPM GU.cp0 (GU.plans 0%nat _ eq_refl) 0 (@nil Z) (fun _ : nat => @nil byte) (@nil (nat * Z)) sp R M fx model K Hh Hl Hfp Hsp ck_no_pins.
  - ck_reg E (10%bv : reg) A0. ck_reg E (11%bv : reg) A1.
    unfold know_ok, GU.cp0. cbn [CC.cp_know]. repeat (apply Forall_cons); [.. | apply Forall_nil].
    + e_range. + e_align S1. + e_range. + e_unk. + e_wr.
  - intros fx' E' R' M' k ps Hnth Hag HLF Hfp'.
    ck_reg E (10%bv : reg) A0. ck_reg E (11%bv : reg) A1. ck_leaf Hag E'.
    ck_leaf_k k Hnth; [|ck_leaf_end k Hnth].
    apply (SK.fin_ret _ _ sp R _ _ E' R' M M' fx' model K _ r HLF Hag64 ret_u64 Hh Hl eq_refl eq_refl Hra Hrok Hsp ltac:(lia)). intros RPv.
    apply (Hcont fx' R' M' Hfp').
    + split; [unfold PML.a0; tk_lin HLF (10%bv : reg)|]. exists (PMCUR.EvU64 (bv_unsigned (getr R 11%bv))). split; [exists (bv_unsigned (getr R 11%bv)); split; [unfold PML.a1; symmetry; apply Z_to_bv_bv_unsigned | reflexivity]|].
      unfold PMCUR.ev_at. split; [exact (ev_defined M M' V VD (CC.lf_grows _ _ _ _ _ _ _ HLF))|]. split; [ck_cell64 HLF (EVar 42) 8 (ELit 32); reflexivity|].
      ck_cell64 HLF (EVar 42) 32 (EVar 43). ck_atom.
    + exact RPv.
    + apply (CK.samem_frame_but (fun a => ~ (V + 8 <= a < V + 48))).
      * apply (TK.frame_samem _ _ _ _ _ _ _ HLF). intros a Ha Hk. cbn [CC.cp_F]. tk_outside.
      * intros a Ha. pose proof (Ha (V + 8, 40) ltac:(ck_in)) as X2. unfold L5.in_rng in *. cbn [fst snd] in *. lia.
    + exact (CC.lf_grows _ _ _ _ _ _ _ HLF).
Qed.

Theorem visit_i64_ok : PMS.visit_i64_spec L PMS.PC_VIS_I64.
Proof.
  intros V sp r fx R M model K Hh Hl HK0 Hfp (EN & A0 & (VP & VD) & (O1 & O2 & O3) & _) Hcont.
  destruct EN as (Hra & Hrok & Hsp & Htp & (S1 & S2 & S3 & S4 & S5)). unfold PML.a0 in A0. pose proof (L5C.stk_floor _ _ _ _ (conj S1 (conj S2 (conj S3 (conj S4 S5))))) as FLR. unfold PMS.VIS_SCR in *.
  assert (A1 : getr R 11%bv = Z_to_bv 64 (bv_unsigned (getr R 11%bv))) by (symmetry; apply Z_to_bv_bv_unsigned). pose proof (bv_unsigned_in_range _ (getr R 11%bv)) as RA1. change (bv_modulus 64) with (2 ^ 64) in RA1.
  change PMS.PC_VIS_I64 with (CC.cp_pc GI.cp0).
  ck_open FPM GI.cp0 (GI.plans 0%nat _ eq_refl) 0 (@nil Z) (fun _ : nat => @nil byte) (@nil (nat * Z)) sp R M fx model K Hh Hl Hfp Hsp ck_no_pins.
  - ck_reg E (10%bv : reg) A0. ck_reg E (11%bv : reg) A1.
    unfold know_ok, GI.cp0. cbn [CC.cp_know]. repeat (apply Forall_cons); [.. | apply Forall_nil].
    + e_range. + e_align S1. + e_range. + e_unk. + e_wr.
  - intros fx' E' R' M' k ps Hnth Hag HLF Hfp'.
    ck_reg E (10%bv : reg) A0. ck_reg E (11%bv : reg) A1. ck_leaf Hag E'.
    ck_leaf_k k Hnth; [|ck_leaf_end k Hnth].
    apply (SK.fin_ret _ _ sp R _ _ E' R' M M' fx' model K _ r HLF Hag64 ret_i64 Hh Hl eq_refl eq_refl Hra Hrok Hsp ltac:(lia)). intros RPv.
    apply (Hcont fx' R' M' Hfp').
    + split; [unfold PML.a0; tk_lin HLF (10%bv : reg)|]. exists (PMCUR.EvI64 (bv_unsigned (getr R 11%bv))). split; [exists (bv_unsigned (getr R 11%bv)); split; [unfold PML.a1; symmetry; apply Z_to_bv_bv_unsigned | reflexivity]|].
      unfold PMCUR.ev_at. split; [exact (ev_defined M M' V VD (CC.lf_grows _ _ _ _ _ _ _ HLF))|]. split; [ck_cell64 HLF (EVar 42) 8 (ELit 16); reflexivity|].
      ck_cell64 HLF (EVar 42) 32 (EVar 43). ck_atom.
    + exact RPv.
    + apply (CK.samem_frame_but (fun a => ~ (V + 8 <= a < V + 48))).
      * apply (TK.frame_samem _ _ _ _ _ _ _ HLF). intros a Ha Hk. cbn [CC.cp_F]. tk_outside.
      * intros a Ha. pose proof (Ha (V + 8, 40) ltac:(ck_in)) as X2. unfold L5.in_rng in *. cbn [fst snd] in *. lia.
    + exact (CC.lf_grows _ _ _ _ _ _ _ HLF).
Qed.

Theorem visit_key_ok : PMS.visit_key_spec L PMS.PC_VIS_KEY.
Proof.
  intros V sp r fx R M model K Hh Hl HK0 Hfp (EN & A0 & (VP & VD) & (O1 & O2 & O3) & (sv & p & n & A1 & Cp & Cn & Sv0 & Sv1)) Hcont.
  destruct EN as (Hra & Hrok & Hsp & Htp & (S1 & S2 & S3 & S4 & S5)). unfold PML.a0 in A0. pose proof (L5C.stk_floor _ _ _ _ (conj S1 (conj S2 (conj S3 (conj S4 S5))))) as FLR. unfold PMS.VIS_SCR in *.
  unfold PML.a1 in A1.
  pose proof Cp as Cp0. pose proof Cn as Cn0. unfold PML.u64 in Cp, Cn. apply u64_norm in Cp. apply u64_norm in Cn.
  pose proof (bv_unsigned_in_range _ (Z_to_bv 64 p)) as RP0. pose proof (bv_unsigned_in_range _ (Z_to_bv 64 n)) as RN0. change (bv_modulus 64) with (2 ^ 64) in RP0, RN0.
  change PMS.PC_VIS_KEY with (CC.cp_pc GK.cp0).
  ck_open FPM GK.cp0 (GK.plans 0%nat _ eq_refl) 0 [bv_unsigned (Z_to_bv 64 p); bv_unsigned (Z_to_bv 64 n)] (fun _ : nat => @nil byte) (@nil (nat * Z)) sp R M fx model K Hh Hl Hfp Hsp ck_no_pins.
  - ck_reg E (10%bv : reg) A0. ck_reg E (11%bv : reg) A1. ck_gh E 0%nat (bv_unsigned (Z_to_bv 64 p)). ck_gh E 1%nat (bv_unsigned (Z_to_bv 64 n)).
    unfold know_ok, GK.cp0. cbn [CC.cp_know]. repeat (apply Forall_cons); [.. | apply Forall_nil].
    + e_range. + e_align S1. + e_range. + e_unk. + e_wr. + e_range. + ck_kw64 sv (bv_unsigned (Z_to_bv 64 p)) Cp. + ck_kw64 (sv + 8) (bv_unsigned (Z_to_bv 64 n)) Cn.
  - intros fx' E' R' M' k ps Hnth Hag HLF Hfp'.
    ck_reg E (10%bv : reg) A0. ck_reg E (11%bv : reg) A1. ck_gh E 0%nat (bv_unsigned (Z_to_bv 64 p)). ck_gh E 1%nat (bv_unsigned (Z_to_bv 64 n)). ck_leaf Hag E'.
    ck_leaf_k k Hnth; [|ck_leaf_end k Hnth].
    apply (SK.fin_ret _ _ sp R _ _ E' R' M M' fx' model K _ r HLF Hag64 ret_key Hh Hl eq_refl eq_refl Hra Hrok Hsp ltac:(lia)). intros RPv.
    apply (Hcont fx' R' M' Hfp').
    + split; [unfold PML.a0; tk_lin HLF (10%bv : reg)|]. exists (PMCUR.EvKey p n). split; [exists sv, p, n; split; [exact A1|]; split; [exact Cp0 | split; [exact Cn0 | reflexivity]]|].
      unfold PMCUR.ev_at. split; [exact (ev_defined M M' V VD (CC.lf_grows _ _ _ _ _ _ _ HLF))|]. split; [ck_cell64 HLF (EVar 42) 8 (ELit 4097); reflexivity|].
      split; [apply (SK.u64_of_word M' _ (Z_to_bv 64 p) p); [|reflexivity]; ck_cell64 HLF (EVar 42) 32 (EVar 64); cbn [edenot]; ck_atom
             | apply (SK.u64_of_word M' _ (Z_to_bv 64 n) n); [|reflexivity]; ck_cell64 HLF (EVar 42) 40 (EVar 65); cbn [edenot]; ck_atom].
    + exact RPv.
    + apply (CK.samem_frame_but (fun a => ~ (V + 8 <= a < V + 48))).
      * apply (TK.frame_samem _ _ _ _ _ _ _ HLF). intros a Ha Hk. cbn [CC.cp_F]. tk_outside.
      * intros a Ha. pose proof (Ha (V + 8, 40) ltac:(ck_in)) as X2. unfold L5.in_rng in *. cbn [fst snd] in *. lia.
    + exact (CC.lf_grows _ _ _ _ _ _ _ HLF).
Qed.

Theorem visit_string_ok : PMS.visit_string_spec L PMS.PC_VIS_STRING.
Proof.
  intros V sp r fx R M model K Hh Hl HK0 Hfp (EN & A0 & (VP & VD) & (O1 & O2 & O3) & (sv & p & n & A1 & Cp & Cn & Sv0 & Sv1)) Hcont.
  destruct EN as (Hra & Hrok & Hsp & Htp & (S1 & S2 & S3 & S4 & S5)). unfold PML.a0 in A0. pose proof (L5C.stk_floor _ _ _ _ (conj S1 (conj S2 (conj S3 (conj S4 S5))))) as FLR. unfold PMS.VIS_SCR in *.
  unfold PML.a1 in A1.
  pose proof Cp as Cp0. pose proof Cn as Cn0. unfold PML.u64 in Cp, Cn. apply u64_norm in Cp. apply u64_norm in Cn.
  pose proof (bv_unsigned_in_range _ (Z_to_bv 64 p)) as RP0. pose proof (bv_unsigned_in_range _ (Z_to_bv 64 n)) as RN0. change (bv_modulus 64) with (2 ^ 64) in RP0, RN0.
  change PMS.PC_VIS_STRING with (CC.cp_pc GS.cp0).
  ck_open FPM GS.cp0 (GS.plans 0%nat _ eq_refl) 0 [bv_unsigned (Z_to_bv 64 p); bv_unsigned (Z_to_bv 64 n)] (fun _ : nat => @nil byte) (@nil (nat * Z)) sp R M fx model K Hh Hl Hfp Hsp ck_no_pins.
  - ck_reg E (10%bv : reg) A0. ck_reg E (11%bv : reg) A1. ck_gh E 0%nat (bv_unsigned (Z_to_bv 64 p)). ck_gh E 1%nat (bv_unsigned (Z_to_bv 64 n)).
    unfold know_ok, GS.cp0. cbn [CC.cp_know]. repeat (apply Forall_cons); [.. | apply Forall_nil].
    + e_range. + e_align S1. + e_range. + e_unk. + e_wr. + e_range. + ck_kw64 sv (bv_unsigned (Z_to_bv 64 p)) Cp. + ck_kw64 (sv + 8) (bv_unsigned (Z_to_bv 64 n)) Cn.
  - intros fx' E' R' M' k ps Hnth Hag HLF Hfp'.
    ck_reg E (10%bv : reg) A0. ck_reg E (11%bv : reg) A1. ck_gh E 0%nat (bv_unsigned (Z_to_bv 64 p)). ck_gh E 1%nat (bv_unsigned (Z_to_bv 64 n)). ck_leaf Hag E'.
    ck_leaf_k k Hnth; [|ck_leaf_end k Hnth].
    apply (SK.fin_ret _ _ sp R _ _ E' R' M M' fx' model K _ r HLF Hag64 ret_string Hh Hl eq_refl eq_refl Hra Hrok Hsp ltac:(lia)). intros RPv.
    apply (Hcont fx' R' M' Hfp').
    + split; [unfold PML.a0; tk_lin HLF (10%bv : reg)|]. exists (PMCUR.EvStr p n). split; [exists sv, p, n; split; [exact A1|]; split; [exact Cp0 | split; [exact Cn0 | reflexivity]]|].
      unfold PMCUR.ev_at. split; [exact (ev_defined M M' V VD (CC.lf_grows _ _ _ _ _ _ _ HLF))|]. split; [ck_cell64 HLF (EVar 42) 8 (ELit 1); reflexivity|].
      split; [apply (SK.u64_of_word M' _ (Z_to_bv 64 p) p); [|reflexivity]; ck_cell64 HLF (EVar 42) 32 (EVar 64); cbn [edenot]; ck_atom
             | apply (SK.u64_of_word M' _ (Z_to_bv 64 n) n); [|reflexivity]; ck_cell64 HLF (EVar 42) 40 (EVar 65); cbn [edenot]; ck_atom].
    + exact RPv.
    + apply (CK.samem_frame_but (fun a => ~ (V + 8 <= a < V + 48))).
      * apply (TK.frame_samem _ _ _ _ _ _ _ HLF). intros a Ha Hk. cbn [CC.cp_F]. tk_outside.
      * intros a Ha. pose proof (Ha (V + 8, 40) ltac:(ck_in)) as X2. unfold L5.in_rng in *. cbn [fst snd] in *. lia.
    + exact (CC.lf_grows _ _ _ _ _ _ _ HLF).
Qed.

End S.
End VIS.
