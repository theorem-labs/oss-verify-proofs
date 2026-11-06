(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)


From OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib Require CodeAt StepGen GwInst GwEq GwApply GwApply2. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q6nq.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QKZH.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QEQM.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QKNz.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QJOB.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q7Ti.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QaAJ.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qnip.

From Stdlib Require Import ZArith NArith List Lia Bool.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QytA.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QytA. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QM7w.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QM7w. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q8P7.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q8P7. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QTyG.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QTyG.Mq1.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qv2Y.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qv2Y. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QXT6.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QXT6. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qnip.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qnip. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QWfR.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QWfR. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QwoZ.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QwoZ. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qwa0.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qwa0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qn81.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qn81. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q34w.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q34w. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QmMO.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QmMO. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QeMs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QeMs. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QrId.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QrId.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q1u2.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q6q3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q6q3.

From OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib Require CodeAt StepGen GwInst GwApply GwApply2.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0.

Module GwI.
Definition segs := QEQM.rsegs.
Definition RATP := QKNz.RATP.
Definition RDEBRUIJN := QKNz.RDEBRUIJN.
Definition RGOT_SSP := QKNz.RGOT_SSP.
Definition RIMG_HI := QKNz.RIMG_HI.
Definition RDATA_LO := QKNz.RDATA_LO.
Definition gw_RTEXT_LO := ltac:(let gw_v_ := eval cbv in (fst (nth 1 QKNz.ref_reserved (0%Z, 0%Z))) in exact gw_v_).
Definition gw_RDATA2_LO := ltac:(let gw_v_ := eval cbv in (fst (nth 3 QKNz.ref_reserved (0%Z, 0%Z))) in exact gw_v_).
Definition ref_reserved := QKNz.ref_reserved.
Definition rmalloc_sym := QKNz.rmalloc_sym.
Definition ralloc_meta_entry := QKNz.ralloc_meta_entry.
Definition rmalloc_entry := QKNz.rmalloc_entry.
Definition ralloc_slot_entry := QKNz.ralloc_slot_entry.
Definition ref_find_segment_none := @QKNz.ref_find_segment_none.
Definition ref_ro_addr_false := @QKNz.ref_ro_addr_false.
Definition ref_memory_read_none := @QKNz.ref_memory_read_none.
Definition ref_wview_overlay := @QKNz.ref_wview_overlay.
Definition ref_seg_rom_none := @QKNz.ref_seg_rom_none.
Definition ref_mrd_overlay := @QKNz.ref_mrd_overlay.
Definition ramp_big := @ramp_big.
Definition rbig_spec := @rbig_spec.
Definition ralloc_meta_spec := @ralloc_meta_spec.
Definition renf_implT := @QJOB.renf_implT.
Definition rmalloc_fp_cases := @Q7Ti.rmalloc_fp_cases.
Definition rmalloc_fp_image := @Q7Ti.rmalloc_fp_image.
Definition rauxv_ok_malloc_fp := @Q7Ti.rauxv_ok_malloc_fp.
Definition rmalloc_core_implT := @rmalloc_core_implT.
Definition ralloc_slot_ok := @QaAJ.ralloc_slot_ok.
Definition rmalloc_stmt_of_impl := @Qnip.rmalloc_stmt_of_impl.
End GwI.

Section RC__1. Context {RC__ : Q6q3.RunConsts}.

#[using="Type"] Lemma mcz_proof : malloc_core_allzero_stmt.
Proof. ltac2:(GwEq.gw_rw [[@gw_eq_malloc_core_allzero_stmt__3; @gw_eq_malloc_core_allzero_stmt__2; @gw_eq_malloc_core_allzero_stmt]]); first [GwApply2.gw_by_name2 GwI.segs (@QKZH.Mq4.mcz_proof) | autorewrite with gw_eqs; GwApply2.gw_by_name2 GwI.segs (@QKZH.Mq4.mcz_proof)]. Qed.

#[using="Type"] Theorem rmalloc_impl_spec : rmalloc_impl_stmt.
Proof. ltac2:(GwEq.gw_rw [[@gw_eq_rmalloc_impl_stmt__3; @gw_eq_rmalloc_impl_stmt__2; @gw_eq_rmalloc_impl_stmt]]); first [GwApply2.gw_by_name2 GwI.segs (@QKZH.Mq4.rmalloc_impl_spec) | autorewrite with gw_eqs; GwApply2.gw_by_name2 GwI.segs (@QKZH.Mq4.rmalloc_impl_spec)]. Qed.

#[using="Type"] Theorem rmalloc_spec : rmalloc_stmt.
Proof. ltac2:(GwEq.gw_rw [[@gw_eq_rmalloc_stmt__3; @gw_eq_rmalloc_stmt__2; @gw_eq_rmalloc_stmt]]); first [GwApply2.gw_by_name2 GwI.segs (@QKZH.Mq4.rmalloc_spec) | autorewrite with gw_eqs; GwApply2.gw_by_name2 GwI.segs (@QKZH.Mq4.rmalloc_spec)]. Qed.

End RC__1.
