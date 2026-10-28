(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)


From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib Require CodeAt StepGen GwInst GwEq GwApply GwApply2. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Q6nq.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Qe1A.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UKNz.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UaAJ.

From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QXup.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QXup. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QWxq.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QWxq.Mq0. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Lib.GwApply.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Qfw3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qfw3.Mq2. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Q9A7.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q9A7.Mq1. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QlEo.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QlEo.Mq0. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QWxq.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QWxq.Mq1. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Q5Rg.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q5Rg.Mq0. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Q5Rg.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q5Rg.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UEQM.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UEQM.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QytA.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QytA. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Qnxq.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qnxq. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Q4J3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q4J3.Mq3. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QLsg.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QLsg. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QkQT.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QkQT. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QM7w.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QM7w. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QNAo.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QNAo.Mq0. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Q8P7.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q8P7. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QTyG.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QTyG.Mq1.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QZAi.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QZAi.Mq2. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QUZl.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QUZl. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Q7S0.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q7S0.Mq0. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Ql2m.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Ql2m.Mq3. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QGeV.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QGeV.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UQXM.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UQXM. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require Uv2Y.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Uv2Y. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UDxd.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UDxd. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UWfR.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UWfR. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require Un81.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Un81. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UeMs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UeMs. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UrId.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UrId. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UaAJ.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UaAJ.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QULt.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Local Ltac Qfw3.Mq3.model_reg_tac n X mexpr ::= Qfw3.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Qfw3.Mq3.zeq_fast ::= Qfw3.Mq3.mkr__zeq_fast_0.
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
Definition ralloc_meta_entry := UKNz.ralloc_meta_entry.
Definition ralloc_slot_entry := UKNz.ralloc_slot_entry.
Definition ref_find_segment_none := @UKNz.ref_find_segment_none.
Definition ref_ro_addr_false := @UKNz.ref_ro_addr_false.
Definition ref_memory_read_none := @UKNz.ref_memory_read_none.
Definition ref_wview_overlay := @UKNz.ref_wview_overlay.
Definition ref_seg_rom_none := @UKNz.ref_seg_rom_none.
Definition ref_mrd_overlay := @UKNz.ref_mrd_overlay.
Definition ralloc_meta_spec := @ralloc_meta_spec.
Definition ralloc_slot_ok := @UaAJ.ralloc_slot_ok.
End GwI.

Section RC__1. Context {RC__ : Q6q3.RunConsts}.

Local Definition gwt_X : unit := (Q6nq.gwt_def (@Q8QT.Mq4.rshadow_rep) (@UQXM.rshadow_rep) (Q6nq.gwt_def (@Qe1A.Mq7.rshadow_rep) (@UQXM.rshadow_rep) (Q6nq.gwt_def (@Q8QT.Mq4.rregions_wf) (@UQXM.rregions_wf) (Q6nq.gwt_def (@Qe1A.Mq7.rregions_wf) (@UQXM.rregions_wf) (Q6nq.gwt_def (@QCa8.Mq5.rpres_except) (@Uv2Y.rpres_except) (Q6nq.gwt_def (@Qe1A.Mq7.rpres_except) (@Uv2Y.rpres_except) (Q6nq.gwt_def (@Q8QT.Mq4.rmrep_shadow) (@UQXM.rmrep_shadow) (Q6nq.gwt_def (@Qe1A.Mq7.rmrep_shadow) (@UQXM.rmrep_shadow) (Q6nq.gwt_def (@Q8QT.Mq4.rmrep_groups) (@UQXM.rmrep_groups) (Q6nq.gwt_def (@Qe1A.Mq7.rmrep_groups) (@UQXM.rmrep_groups) (Q6nq.gwt_def (@Q8QT.Mq4.rmrep_globals) (@UQXM.rmrep_globals) (Q6nq.gwt_def (@Qe1A.Mq7.rmrep_globals) (@UQXM.rmrep_globals) (Q6nq.gwt_def (@Q8QT.Mq4.rmrep_ctx) (@UQXM.rmrep_ctx) (Q6nq.gwt_def (@Qe1A.Mq7.rmrep_ctx) (@UQXM.rmrep_ctx) (Q6nq.gwt_def (@Q8QT.Mq4.rmrep_areas) (@UQXM.rmrep_areas) (Q6nq.gwt_def (@Qe1A.Mq7.rmrep_areas) (@UQXM.rmrep_areas) (Q6nq.gwt_def (@Q8QT.Mq4.rmrep) (@UQXM.rmrep) (Q6nq.gwt_def (@Qe1A.Mq7.rmrep) (@UQXM.rmrep) (Q6nq.gwt_def (@QkTt.Mq5.rmalloc_fp) (@UDxd.rmalloc_fp) (Q6nq.gwt_def (@Qe1A.Mq7.rmalloc_fp) (@UDxd.rmalloc_fp) (Q6nq.gwt_def (@QCa8.Mq5.rimplT) (@Uv2Y.rimplT) (Q6nq.gwt_def (@Qe1A.Mq7.rimplT) (@Uv2Y.rimplT) (Q6nq.gwt_def (@Q8QT.Mq4.rgroup_rep) (@UQXM.rgroup_rep) (Q6nq.gwt_def (@Qe1A.Mq7.rgroup_rep) (@UQXM.rgroup_rep) (Q6nq.gwt_def (@QCa8.Mq5.rauxv_ok) (@Uv2Y.rauxv_ok) (Q6nq.gwt_def (@Qe1A.Mq7.rauxv_ok) (@Uv2Y.rauxv_ok) (Q6nq.gwt_def (@Qe1A.Mq7.ras_pre2) (@Un81.ras_pre2) (Q6nq.gwt_def (@QQRC.Mq4.ras_pre2) (@Un81.ras_pre2) (Q6nq.gwt_def (@Qe1A.Mq7.ras_post2) (@Un81.ras_post2) (Q6nq.gwt_def (@QQRC.Mq4.ras_post2) (@Un81.ras_post2) (Q6nq.gwt_def (@Qe1A.Mq7.ras_post) (@UWfR.ras_post) (Q6nq.gwt_def (@Qy8Z.Mq1.ras_post) (@UWfR.ras_post) (Q6nq.gwt_def (@Q8QT.Mq4.rarea_rep) (@UQXM.rarea_rep) (Q6nq.gwt_def (@Qe1A.Mq7.rarea_rep) (@UQXM.rarea_rep) (Q6nq.gwt_def (@QCa8.Mq5.ram_post) (@Uv2Y.ram_post) (Q6nq.gwt_def (@Qe1A.Mq7.ram_post) (@Uv2Y.ram_post) (Q6nq.gwt_def (@Qe1A.Mq7.ralloc_slot_stmt2) (@Un81.ralloc_slot_stmt2) (Q6nq.gwt_def (@QQRC.Mq4.ralloc_slot_stmt2) (@Un81.ralloc_slot_stmt2) (Q6nq.gwt_def (@Qe1A.Mq7.ralloc_slot_stmt) (@UWfR.ralloc_slot_stmt) (Q6nq.gwt_def (@Qy8Z.Mq1.ralloc_slot_stmt) (@UWfR.ralloc_slot_stmt) (Q6nq.gwt_def (@QCa8.Mq5.ralloc_meta_stmt) (@Uv2Y.ralloc_meta_stmt) (Q6nq.gwt_def (@Qe1A.Mq7.ralloc_meta_stmt) (@Uv2Y.ralloc_meta_stmt) (Q6nq.gwt_def (@QCa8.Mq5.ralloc_fp) (@Uv2Y.ralloc_fp) (Q6nq.gwt_def (@Qe1A.Mq7.ralloc_fp) (@Uv2Y.ralloc_fp) Q6nq.gwt_nil)))))))))))))))))))))))))))))))))))))))))))).
#[using="Type"] Lemma ras_pre2_intro : ltac2:(Q6nq.ty2 'GwI.segs '(@Qe1A.Mq7.ras_pre2_intro) [[@gw_eq_ras_pre2__3; @gw_eq_ras_pre2__2; @gw_eq_ras_pre2]] '(@nil Z) 'gwt_X).
Proof. ltac2:(GwEq.gw_rw [[@gw_eq_ras_pre2__3; @gw_eq_ras_pre2__2; @gw_eq_ras_pre2]]); first [GwApply2.gw_by_name2 GwI.segs (@Qe1A.Mq7.ras_pre2_intro) | autorewrite with gw_eqs; GwApply2.gw_by_name2 GwI.segs (@Qe1A.Mq7.ras_pre2_intro)]. Qed.

#[using="Type"] Theorem ralloc_slot_spec : ralloc_slot_stmt ras_pre2 as_inv2.
Proof. ltac2:(GwEq.gw_rw [[@gw_eq_ralloc_slot_stmt__3; @gw_eq_ralloc_slot_stmt__2; @gw_eq_ralloc_slot_stmt]; [@gw_eq_ras_pre2__3; @gw_eq_ras_pre2__2; @gw_eq_ras_pre2]]); first [GwApply2.gw_by_name2 GwI.segs (@Qe1A.Mq7.ralloc_slot_spec) | autorewrite with gw_eqs; GwApply2.gw_by_name2 GwI.segs (@Qe1A.Mq7.ralloc_slot_spec)]. Qed.

End RC__1.
