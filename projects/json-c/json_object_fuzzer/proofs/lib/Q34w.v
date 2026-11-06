(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)


From OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib Require CodeAt StepGen GwInst GwEq GwApply GwApply2. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q6nq.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qe1A.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QKNz.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QaAJ.

From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QXup.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QXup. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QWxq_c1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QWxq_c1.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Lib.GwApply.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qfw3_c1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qfw3_c1.Mq2. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q9A7.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q9A7.Mq1. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QlEo_c1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QlEo_c1.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QWxq_c1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QWxq_c1.Mq1. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q5Rg.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q5Rg.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q5Rg.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q5Rg.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QEQM.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QEQM.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QytA.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QytA. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qnxq.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qnxq. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q4J3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q4J3.Mq3. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QLsg.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QLsg. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QkQT.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QkQT. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QM7w.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QM7w. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QNAo.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QNAo.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q8P7.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q8P7. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QTyG.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QTyG.Mq1.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QZAi.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QZAi.Mq2. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QUZl.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QUZl. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q7S0.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q7S0.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Ql2m.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Ql2m.Mq3. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QGeV.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QGeV.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QQXM.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QQXM. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qv2Y.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qv2Y. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QDxd_c1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QDxd_c1. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QWfR.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QWfR. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qn81.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qn81. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QeMs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QeMs. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QrId.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QrId. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QaAJ.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QaAJ.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QULt.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0.
Open Scope Z_scope.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q6q3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q6q3.

From OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib Require CodeAt StepGen GwInst GwApply GwApply2.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module GwI.
Definition segs := rsegs.
Definition RATP := QKNz.RATP.
Definition RDEBRUIJN := QKNz.RDEBRUIJN.
Definition RGOT_SSP := QKNz.RGOT_SSP.
Definition RIMG_HI := QKNz.RIMG_HI.
Definition RDATA_LO := QKNz.RDATA_LO.
Definition gw_RTEXT_LO := ltac:(let gw_v_ := eval cbv in (fst (nth 1 QKNz.ref_reserved (0%Z, 0%Z))) in exact gw_v_).
Definition gw_RDATA2_LO := ltac:(let gw_v_ := eval cbv in (fst (nth 3 QKNz.ref_reserved (0%Z, 0%Z))) in exact gw_v_).
Definition ref_reserved := QKNz.ref_reserved.
Definition ralloc_meta_entry := QKNz.ralloc_meta_entry.
Definition ralloc_slot_entry := QKNz.ralloc_slot_entry.
Definition ref_find_segment_none := @QKNz.ref_find_segment_none.
Definition ref_ro_addr_false := @QKNz.ref_ro_addr_false.
Definition ref_memory_read_none := @QKNz.ref_memory_read_none.
Definition ref_wview_overlay := @QKNz.ref_wview_overlay.
Definition ref_seg_rom_none := @QKNz.ref_seg_rom_none.
Definition ref_mrd_overlay := @QKNz.ref_mrd_overlay.
Definition ralloc_meta_spec := @ralloc_meta_spec.
Definition ralloc_slot_ok := @QaAJ.ralloc_slot_ok.
End GwI.

Section RC__1. Context {RC__ : Q6q3.RunConsts}.

Local Definition gwt_X : unit := (Q6nq.gwt_def (@Q8QT.Mq4.rshadow_rep) (@QQXM.rshadow_rep) (Q6nq.gwt_def (@Qe1A.Mq7.rshadow_rep) (@QQXM.rshadow_rep) (Q6nq.gwt_def (@Q8QT.Mq4.rregions_wf) (@QQXM.rregions_wf) (Q6nq.gwt_def (@Qe1A.Mq7.rregions_wf) (@QQXM.rregions_wf) (Q6nq.gwt_def (@QCa8.Mq5.rpres_except) (@Qv2Y.rpres_except) (Q6nq.gwt_def (@Qe1A.Mq7.rpres_except) (@Qv2Y.rpres_except) (Q6nq.gwt_def (@Q8QT.Mq4.rmrep_shadow) (@QQXM.rmrep_shadow) (Q6nq.gwt_def (@Qe1A.Mq7.rmrep_shadow) (@QQXM.rmrep_shadow) (Q6nq.gwt_def (@Q8QT.Mq4.rmrep_groups) (@QQXM.rmrep_groups) (Q6nq.gwt_def (@Qe1A.Mq7.rmrep_groups) (@QQXM.rmrep_groups) (Q6nq.gwt_def (@Q8QT.Mq4.rmrep_globals) (@QQXM.rmrep_globals) (Q6nq.gwt_def (@Qe1A.Mq7.rmrep_globals) (@QQXM.rmrep_globals) (Q6nq.gwt_def (@Q8QT.Mq4.rmrep_ctx) (@QQXM.rmrep_ctx) (Q6nq.gwt_def (@Qe1A.Mq7.rmrep_ctx) (@QQXM.rmrep_ctx) (Q6nq.gwt_def (@Q8QT.Mq4.rmrep_areas) (@QQXM.rmrep_areas) (Q6nq.gwt_def (@Qe1A.Mq7.rmrep_areas) (@QQXM.rmrep_areas) (Q6nq.gwt_def (@Q8QT.Mq4.rmrep) (@QQXM.rmrep) (Q6nq.gwt_def (@Qe1A.Mq7.rmrep) (@QQXM.rmrep) (Q6nq.gwt_def (@QkTt.Mq5.rmalloc_fp) (@QDxd_c1.rmalloc_fp) (Q6nq.gwt_def (@Qe1A.Mq7.rmalloc_fp) (@QDxd_c1.rmalloc_fp) (Q6nq.gwt_def (@QCa8.Mq5.rimplT) (@Qv2Y.rimplT) (Q6nq.gwt_def (@Qe1A.Mq7.rimplT) (@Qv2Y.rimplT) (Q6nq.gwt_def (@Q8QT.Mq4.rgroup_rep) (@QQXM.rgroup_rep) (Q6nq.gwt_def (@Qe1A.Mq7.rgroup_rep) (@QQXM.rgroup_rep) (Q6nq.gwt_def (@QCa8.Mq5.rauxv_ok) (@Qv2Y.rauxv_ok) (Q6nq.gwt_def (@Qe1A.Mq7.rauxv_ok) (@Qv2Y.rauxv_ok) (Q6nq.gwt_def (@Qe1A.Mq7.ras_pre2) (@Qn81.ras_pre2) (Q6nq.gwt_def (@QQRC.Mq4.ras_pre2) (@Qn81.ras_pre2) (Q6nq.gwt_def (@Qe1A.Mq7.ras_post2) (@Qn81.ras_post2) (Q6nq.gwt_def (@QQRC.Mq4.ras_post2) (@Qn81.ras_post2) (Q6nq.gwt_def (@Qe1A.Mq7.ras_post) (@QWfR.ras_post) (Q6nq.gwt_def (@Qy8Z.Mq1.ras_post) (@QWfR.ras_post) (Q6nq.gwt_def (@Q8QT.Mq4.rarea_rep) (@QQXM.rarea_rep) (Q6nq.gwt_def (@Qe1A.Mq7.rarea_rep) (@QQXM.rarea_rep) (Q6nq.gwt_def (@QCa8.Mq5.ram_post) (@Qv2Y.ram_post) (Q6nq.gwt_def (@Qe1A.Mq7.ram_post) (@Qv2Y.ram_post) (Q6nq.gwt_def (@Qe1A.Mq7.ralloc_slot_stmt2) (@Qn81.ralloc_slot_stmt2) (Q6nq.gwt_def (@QQRC.Mq4.ralloc_slot_stmt2) (@Qn81.ralloc_slot_stmt2) (Q6nq.gwt_def (@Qe1A.Mq7.ralloc_slot_stmt) (@QWfR.ralloc_slot_stmt) (Q6nq.gwt_def (@Qy8Z.Mq1.ralloc_slot_stmt) (@QWfR.ralloc_slot_stmt) (Q6nq.gwt_def (@QCa8.Mq5.ralloc_meta_stmt) (@Qv2Y.ralloc_meta_stmt) (Q6nq.gwt_def (@Qe1A.Mq7.ralloc_meta_stmt) (@Qv2Y.ralloc_meta_stmt) (Q6nq.gwt_def (@QCa8.Mq5.ralloc_fp) (@Qv2Y.ralloc_fp) (Q6nq.gwt_def (@Qe1A.Mq7.ralloc_fp) (@Qv2Y.ralloc_fp) Q6nq.gwt_nil)))))))))))))))))))))))))))))))))))))))))))).
#[using="Type"] Lemma ras_pre2_intro : ltac2:(Q6nq.ty2 'GwI.segs '(@Qe1A.Mq7.ras_pre2_intro) [[@gw_eq_ras_pre2__3; @gw_eq_ras_pre2__2; @gw_eq_ras_pre2]] '(@nil Z) 'gwt_X).
Proof. ltac2:(GwEq.gw_rw [[@gw_eq_ras_pre2__3; @gw_eq_ras_pre2__2; @gw_eq_ras_pre2]]); first [GwApply2.gw_by_name2 GwI.segs (@Qe1A.Mq7.ras_pre2_intro) | autorewrite with gw_eqs; GwApply2.gw_by_name2 GwI.segs (@Qe1A.Mq7.ras_pre2_intro)]. Qed.

#[using="Type"] Theorem ralloc_slot_spec : ralloc_slot_stmt ras_pre2 as_inv2.
Proof. ltac2:(GwEq.gw_rw [[@gw_eq_ralloc_slot_stmt__3; @gw_eq_ralloc_slot_stmt__2; @gw_eq_ralloc_slot_stmt]; [@gw_eq_ras_pre2__3; @gw_eq_ras_pre2__2; @gw_eq_ras_pre2]]); first [GwApply2.gw_by_name2 GwI.segs (@Qe1A.Mq7.ralloc_slot_spec) | autorewrite with gw_eqs; GwApply2.gw_by_name2 GwI.segs (@Qe1A.Mq7.ralloc_slot_spec)]. Qed.

End RC__1.
