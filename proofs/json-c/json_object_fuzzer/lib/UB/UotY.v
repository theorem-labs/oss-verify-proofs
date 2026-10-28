(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)


From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib Require CodeAt StepGen GwInst GwEq GwApply GwApply2. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Q6nq.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QKZH.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UEQM.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UKNz.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UJOB.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require U7Ti.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UaAJ.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require Unip.

From Stdlib Require Import ZArith NArith List Lia Bool.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QytA.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QytA. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QM7w.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QM7w. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Q8P7.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q8P7. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QTyG.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QTyG.Mq1.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require Uv2Y.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Uv2Y. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UXT6.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UXT6. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require Unip.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Unip. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UWfR.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UWfR. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UwoZ.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UwoZ. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require Uwa0.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Uwa0. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require Un81.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Un81. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require U34w.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import U34w. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UmMO.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UmMO. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UeMs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UeMs. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UrId.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UrId.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Q1u2.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Q6q3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q6q3.

From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib Require CodeAt StepGen GwInst GwApply GwApply2.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Local Ltac Qfw3.Mq3.model_reg_tac n X mexpr ::= Qfw3.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Qfw3.Mq3.zeq_fast ::= Qfw3.Mq3.mkr__zeq_fast_0.

Module GwI.
Definition segs := UEQM.rsegs.
Definition RATP := UKNz.RATP.
Definition RDEBRUIJN := UKNz.RDEBRUIJN.
Definition RGOT_SSP := UKNz.RGOT_SSP.
Definition RIMG_HI := UKNz.RIMG_HI.
Definition RDATA_LO := UKNz.RDATA_LO.
Definition gw_RTEXT_LO := ltac:(let gw_v_ := eval cbv in (fst (nth 1 UKNz.ref_reserved (0%Z, 0%Z))) in exact gw_v_).
Definition gw_RDATA2_LO := ltac:(let gw_v_ := eval cbv in (fst (nth 3 UKNz.ref_reserved (0%Z, 0%Z))) in exact gw_v_).
Definition ref_reserved := UKNz.ref_reserved.
Definition rmalloc_sym := UKNz.rmalloc_sym.
Definition ralloc_meta_entry := UKNz.ralloc_meta_entry.
Definition rmalloc_entry := UKNz.rmalloc_entry.
Definition ralloc_slot_entry := UKNz.ralloc_slot_entry.
Definition ref_find_segment_none := @UKNz.ref_find_segment_none.
Definition ref_ro_addr_false := @UKNz.ref_ro_addr_false.
Definition ref_memory_read_none := @UKNz.ref_memory_read_none.
Definition ref_wview_overlay := @UKNz.ref_wview_overlay.
Definition ref_seg_rom_none := @UKNz.ref_seg_rom_none.
Definition ref_mrd_overlay := @UKNz.ref_mrd_overlay.
Definition ramp_big := @ramp_big.
Definition rbig_spec := @rbig_spec.
Definition ralloc_meta_spec := @ralloc_meta_spec.
Definition renf_implT := @UJOB.renf_implT.
Definition rmalloc_fp_cases := @U7Ti.rmalloc_fp_cases.
Definition rmalloc_fp_image := @U7Ti.rmalloc_fp_image.
Definition rauxv_ok_malloc_fp := @U7Ti.rauxv_ok_malloc_fp.
Definition rmalloc_core_implT := @rmalloc_core_implT.
Definition ralloc_slot_ok := @UaAJ.ralloc_slot_ok.
Definition rmalloc_stmt_of_impl := @Unip.rmalloc_stmt_of_impl.
End GwI.

Section RC__1. Context {RC__ : Q6q3.RunConsts}.

#[using="Type"] Lemma mcz_proof : malloc_core_allzero_stmt.
Proof. ltac2:(GwEq.gw_rw [[@gw_eq_malloc_core_allzero_stmt__3; @gw_eq_malloc_core_allzero_stmt__2; @gw_eq_malloc_core_allzero_stmt]]); first [GwApply2.gw_by_name2 GwI.segs (@QKZH.Mq4.mcz_proof) | autorewrite with gw_eqs; GwApply2.gw_by_name2 GwI.segs (@QKZH.Mq4.mcz_proof)]. Qed.

#[using="Type"] Theorem rmalloc_impl_spec : rmalloc_impl_stmt.
Proof. ltac2:(GwEq.gw_rw [[@gw_eq_rmalloc_impl_stmt__3; @gw_eq_rmalloc_impl_stmt__2; @gw_eq_rmalloc_impl_stmt]]); first [GwApply2.gw_by_name2 GwI.segs (@QKZH.Mq4.rmalloc_impl_spec) | autorewrite with gw_eqs; GwApply2.gw_by_name2 GwI.segs (@QKZH.Mq4.rmalloc_impl_spec)]. Qed.

#[using="Type"] Theorem rmalloc_spec : rmalloc_stmt.
Proof. ltac2:(GwEq.gw_rw [[@gw_eq_rmalloc_stmt__3; @gw_eq_rmalloc_stmt__2; @gw_eq_rmalloc_stmt]]); first [GwApply2.gw_by_name2 GwI.segs (@QKZH.Mq4.rmalloc_spec) | autorewrite with gw_eqs; GwApply2.gw_by_name2 GwI.segs (@QKZH.Mq4.rmalloc_spec)]. Qed.

End RC__1.
