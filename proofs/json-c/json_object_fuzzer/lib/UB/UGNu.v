(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)


From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib Require CodeAt StepGen GwInst GwEq GwEqH GwApply GwApply2. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Q6nq.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Qe1A.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UKNz.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require Unip.

From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QXup.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QXup. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QWxq.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QWxq.Mq0. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Lib.GwApply.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Qfw3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qfw3.Mq2. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Q9A7.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q9A7.Mq1. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Q5Rg.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q5Rg. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QlEo.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QlEo.Mq0. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QWxq.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QWxq.Mq1. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Q5Rg.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q5Rg.Mq0.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UEQM.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UEQM.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Q2qa.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q2qa.Mq1. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Qy5Y.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qy5Y.Mq4. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Q4J3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q4J3.Mq3. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QlQE.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QlQE. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QPjm.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QPjm.Mq1. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QPjm.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QPjm.Mq4.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QZAi.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QZAi.Mq2. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QUZl.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QUZl. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Q7S0.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q7S0.Mq0. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Ql2m.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Ql2m.Mq3. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QGeV.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QGeV.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Qy5Y.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qy5Y.Mq6. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QPjm.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QPjm.Mq2. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QFkE.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QFkE. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Q6y7.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q6y7. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QJE4.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QJE4.Mq2. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Q3o5.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q3o5.Mq0. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QULt.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QULt.Mq0.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UQXM.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UQXM. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require Uv2Y.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Uv2Y. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UIMz.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UIMz. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require Un7h.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Un7h. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UXT6.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UXT6. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require Unip.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Unip. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require Uhxl.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Uhxl. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UKaC.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UKaC. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require U3Uw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import U3Uw.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Q3o5. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QNAo.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import QlEo.Mq0.Exc. Local Ltac Qfw3.Mq3.model_reg_tac n X mexpr ::= Qfw3.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Qfw3.Mq3.zeq_fast ::= Qfw3.Mq3.mkr__zeq_fast_0.
Open Scope Z_scope.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Q6q3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q6q3.

From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib Require CodeAt StepGen GwInst GwApply GwApply2.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module GwI.
Definition segs := rsegs.
Definition RATP := UKNz.RATP.
Definition RDEBRUIJN := UKNz.RDEBRUIJN.
Definition RGOT_SSP := UKNz.RGOT_SSP.
Definition RIMG_HI := UKNz.RIMG_HI.
Definition RDATA_LO := UKNz.RDATA_LO.
Definition gw_RTEXT_LO := ltac:(let gw_v_ := eval cbv in (fst (nth 1 UKNz.ref_reserved (0%Z, 0%Z))) in exact gw_v_).
Definition gw_RDATA2_LO := ltac:(let gw_v_ := eval cbv in (fst (nth 3 UKNz.ref_reserved (0%Z, 0%Z))) in exact gw_v_).
Definition ref_reserved := UKNz.ref_reserved.
Definition rfree_sym := UKNz.rfree_sym.
Definition rfree_entry := UKNz.rfree_entry.
Definition rnontrivial_free_entry := UKNz.rnontrivial_free_entry.
Definition ref_find_segment_none := @UKNz.ref_find_segment_none.
Definition ref_ro_addr_false := @UKNz.ref_ro_addr_false.
Definition ref_memory_read_none := @UKNz.ref_memory_read_none.
Definition ref_wview_overlay := @UKNz.ref_wview_overlay.
Definition ref_seg_rom_none := @UKNz.ref_seg_rom_none.
Definition ref_mrd_overlay := @UKNz.ref_mrd_overlay.
Definition rfree_fp_lt := @rfree_fp_lt.
Definition rlibc_free_implT := @rlibc_free_implT.
Definition rfree_stmt_of_impl := @Unip.rfree_stmt_of_impl.
Lemma LAY_hi_RATP : ltac2:(GwEq.gw_fact_ty 'segs '(@Qe1A.Mq9.gw_all) @LAY_hi_RATP). Proof. GwApply.gw_side. Qed.
End GwI.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

#[using="Type"] Lemma rauxv_ok_pres_B : forall C m m' B,
rauxv_ok m B -> rpres_except C m m' ->
(forall a, B <= a -> ~ C a) -> (forall a, RAUXV_CELL <= a < RAUXV_CELL + 8 -> ~ C a) ->
rauxv_ok m' B.
Proof. ltac2:(GwEq.gw_rw [[@gw_eq_rauxv_ok__3; @gw_eq_rauxv_ok__2; @gw_eq_rauxv_ok]; [@gw_eq_rpres_except__3; @gw_eq_rpres_except__2; @gw_eq_rpres_except]]); first [GwApply2.gw_by_name2 GwI.segs (@Qe1A.Mq9.rauxv_ok_pres_B) | autorewrite with gw_eqs; GwApply2.gw_by_name2 GwI.segs (@Qe1A.Mq9.rauxv_ok_pres_B)]. Qed.

Section FP.
Variables (st st' : mstate) (LB0 : list block) (blk : block) (lo sp : Z) (m m' : mem).
Hypothesis C : CINV st LB0.
Hypothesis MR : rmrep st m.
Hypothesis LO : alloc_ceiling <= lo.
Hypothesis LS : lo <= sp.
Hypothesis BLKR : forall blk', In blk' (lbrm LB0 blk) -> exists r', (s_regions st') !! fst (blk_slot blk') = Some r'.
Hypothesis SHR : forall rid r', (s_regions st') !! rid = Some r' -> (s_regions st) !! rid = Some r'.
Hypothesis PE : rpres_except (fun a => rfree_fp st lo sp a \/ DROPPED st st' a \/ 490332 <= a < 490336) m m'.

Let FPT := fun a => rfree_fp st lo sp a \/ DROPPED st st' a \/ 490332 <= a < 490336.

#[using="RC__ m MR LO LS"] Lemma rfp_not_high a : sp <= a -> ~ FPT a.
Proof. first [GwApply2.gw_by_name2 GwI.segs (@Qe1A.Mq9.rfp_not_high) | autorewrite with gw_eqs; GwApply2.gw_by_name2 GwI.segs (@Qe1A.Mq9.rfp_not_high)]. Qed.

#[using="RC__ m MR LO"] Lemma rfp_not_img a : 0x62000 <= a < 0x99000 -> ~ (RCTX <= a < RCTX + 928) -> ~ (490332 <= a < 490336) -> ~ FPT a.
Proof. first [GwApply2.gw_by_name2 GwI.segs (@Qe1A.Mq9.rfp_not_img) | autorewrite with gw_eqs; GwApply2.gw_by_name2 GwI.segs (@Qe1A.Mq9.rfp_not_img)]. Qed.

#[using="RC__ m MR LO"] Lemma rfp_not_image a : 0x62000 <= a < 0x99000 -> ~ ralloc_static a -> ~ FPT a.
Proof. ltac2:(GwEq.gw_rw [[@gw_eq_ralloc_static__3; @gw_eq_ralloc_static__2; @gw_eq_ralloc_static]]); first [GwApply2.gw_by_name2 GwI.segs (@Qe1A.Mq9.rfp_not_image) | autorewrite with gw_eqs; GwApply2.gw_by_name2 GwI.segs (@Qe1A.Mq9.rfp_not_image)]. Qed.

#[using="RC__ m C MR LO BLKR SHR"] Lemma rfp_not_block blk' a : In blk' (lbrm LB0 blk) -> blk_addr blk' <= a < blk_addr blk' + blk_size blk' -> ~ FPT a.
Proof. first [GwApply2.gw_by_name2 GwI.segs (@Qe1A.Mq9.rfp_not_block) | autorewrite with gw_eqs; GwApply2.gw_by_name2 GwI.segs (@Qe1A.Mq9.rfp_not_block)]. Qed.

#[using="RC__ st st' lo C MR LO LS BLKR SHR PE FPT"] Lemma rheap_pres_free LB' : (forall b, In b LB' -> In b (lbrm LB0 blk)) -> rheap_pres LB' sp m m'.
Proof. ltac2:(GwEq.gw_rw [[@gw_eq_rheap_pres__3; @gw_eq_rheap_pres__2; @gw_eq_rheap_pres]]); first [ (pose proof PE as gw_h_; clear PE; ltac2:(GwEqH.gw_rw_in @gw_h_ [[@gw_eq_rfree_fp__3; @gw_eq_rfree_fp__2; @gw_eq_rfree_fp]; [@gw_eq_rpres_except__3; @gw_eq_rpres_except__2; @gw_eq_rpres_except]]); rename gw_h_ into PE) | idtac ]; first [GwApply2.gw_by_name2 GwI.segs (@Qe1A.Mq9.rheap_pres_free) | autorewrite with gw_eqs; GwApply2.gw_by_name2 GwI.segs (@Qe1A.Mq9.rheap_pres_free)]. Qed.

#[using="st st' lo MR LO LS PE FPT"] Lemma rauxv_ok_free B : rauxv_ok m B -> sp <= B -> rauxv_ok m' B.
Proof. ltac2:(GwEq.gw_rw [[@gw_eq_rauxv_ok__3; @gw_eq_rauxv_ok__2; @gw_eq_rauxv_ok]]); first [ (pose proof PE as gw_h_; clear PE; ltac2:(GwEqH.gw_rw_in @gw_h_ [[@gw_eq_rfree_fp__3; @gw_eq_rfree_fp__2; @gw_eq_rfree_fp]; [@gw_eq_rpres_except__3; @gw_eq_rpres_except__2; @gw_eq_rpres_except]]); rename gw_h_ into PE) | idtac ]; first [GwApply2.gw_by_name2 GwI.segs (@Qe1A.Mq9.rauxv_ok_free) | autorewrite with gw_eqs; GwApply2.gw_by_name2 GwI.segs (@Qe1A.Mq9.rauxv_ok_free)]. Qed.
End FP.

#[using="Type"] Theorem rfree_impl_spec_proof : rfree_impl_stmt.
Proof. ltac2:(GwEq.gw_rw [[@gw_eq_rfree_impl_stmt__3; @gw_eq_rfree_impl_stmt__2; @gw_eq_rfree_impl_stmt]]); first [GwApply2.gw_by_name2 GwI.segs (@Qe1A.Mq9.rfree_impl_spec_proof) | autorewrite with gw_eqs; GwApply2.gw_by_name2 GwI.segs (@Qe1A.Mq9.rfree_impl_spec_proof)]. Qed.

#[using="Type"] Theorem rfree_spec_proof : rfree_stmt.
Proof. ltac2:(GwEq.gw_rw [[@gw_eq_rfree_stmt__3; @gw_eq_rfree_stmt__2; @gw_eq_rfree_stmt]]); first [GwApply2.gw_by_name2 GwI.segs (@Qe1A.Mq9.rfree_spec_proof) | autorewrite with gw_eqs; GwApply2.gw_by_name2 GwI.segs (@Qe1A.Mq9.rfree_spec_proof)]. Qed.

End RC__1.
