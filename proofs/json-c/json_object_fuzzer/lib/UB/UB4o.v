(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)


From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib Require CodeAt StepGen GwInst GwEq GwEqH GwApply GwApply2. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Q6nq.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Q2TC.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UKNz.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UpkF.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UznK.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require U4l4.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UiOj.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QQRC.

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
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q5Rg. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Lib.GwApply.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.Bytes. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Lib.SepCache.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib.SepCache.StrFun. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QlEo.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QlEo.Mq0. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QWxq.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QWxq.Mq1. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Q5Rg.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q5Rg.Mq0.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UEQM.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UEQM.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Q2qa.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q2qa.Mq1. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Qy5Y.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qy5Y.Mq1. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QytA.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QytA. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Qy5Y.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qy5Y.Mq4. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Q4J3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q4J3.Mq3. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QlQE.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QlQE. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QPjm.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QPjm.Mq1. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QPjm.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QPjm.Mq4. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QULt.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QULt.Mq2. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Q3o5.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q3o5.Mq0. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QULt.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QULt.Mq0. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QDUx.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QDUx.Mq9.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QZAi.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QZAi.Mq2. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QUZl.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QUZl. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Q7S0.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q7S0.Mq0. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Q7S0.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q7S0.Mq1. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Ql2m.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Ql2m.Mq3. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QGeV.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QGeV. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Qatc.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qatc. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QSfG.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QSfG.Mq2. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Q7S0.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q7S0. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QSfG.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QSfG. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QdBa.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QdBa.Mq2. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QYTG.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QYTG.Mq1. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QaiD.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QaiD. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QhnL.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QhnL. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Q1u2.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q1u2.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QJE4.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QJE4.Mq4. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Qy5Y.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qy5Y.Mq6. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QPjm.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QPjm.Mq2. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QPjm.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QPjm.Mq3. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QFkE.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QFkE.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UKNz.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UKNz. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UQXM.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UQXM. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require Uv2Y.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Uv2Y. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require U8FW.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import U8FW. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UIMz.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UIMz. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require Un7h.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Un7h. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require U8eV.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import U8eV. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UXT6.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UXT6. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UOpO.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UOpO. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require Unip.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Unip. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UZr4.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UZr4. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require Upt0.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Upt0. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require U1ti.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import U1ti. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UdkX.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UdkX. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require U7ZX.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import U7ZX. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require Uh29.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Uh29. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require U4EM.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import U4EM. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UncX.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UncX. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require U1sW.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import U1sW. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require Ua73.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Ua73.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Q3o5. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QNAo.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import QlEo.Mq0.Exc. Local Ltac Qfw3.Mq3.model_reg_tac n X mexpr ::= Qfw3.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Qfw3.Mq3.zeq_fast ::= Qfw3.Mq3.mkr__zeq_fast_0.
Open Scope Z_scope.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Q6q3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q6q3.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Q3CA.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q3CA.

From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib Require CodeAt StepGen GwInst GwApply GwApply2.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module GwI.
Definition segs := rsegs.
Definition base := 0x53d40%Z.
Definition w_15 := 0xde5fc0ef%Z.
Definition w_59 := 0x00044797%Z.
Definition w_62 := 0x1547b783%Z.
Definition w_67 := 0xfffc2797%Z.
Definition w_70 := 0x6f478793%Z.
Definition w_145 := 0xfffc2317%Z.
Definition w_147 := 0x59c30313%Z.
Definition w_185 := 0x31c000ef%Z.
Definition w_238 := 0x3400b0ef%Z.
Definition hi_59 := (Z_to_bv 20 68).
Definition hi_67 := (Z_to_bv 20 1048514).
Definition hi_145 := (Z_to_bv 20 1048514).
Definition lo_62 := (Z_to_bv 12 340).
Definition lo_70 := (Z_to_bv 12 1780).
Definition lo_147 := (Z_to_bv 12 1436).
Definition joff_15 := (Z_to_bv 21 2084324).
Definition joff_185 := (Z_to_bv 21 796).
Definition joff_238 := (Z_to_bv 21 45888).
Definition e_memcpy := 0x5f438%Z.
Definition RATP := UKNz.RATP.
Definition RDEBRUIJN := UKNz.RDEBRUIJN.
Definition RGOT_SSP := UKNz.RGOT_SSP.
Definition RIMG_HI := UKNz.RIMG_HI.
Definition RDATA_LO := UKNz.RDATA_LO.
Definition gw_RTEXT_LO := ltac:(let gw_v_ := eval cbv in (fst (nth 1 UKNz.ref_reserved (0%Z, 0%Z))) in exact gw_v_).
Definition gw_RDATA2_LO := ltac:(let gw_v_ := eval cbv in (fst (nth 3 UKNz.ref_reserved (0%Z, 0%Z))) in exact gw_v_).
Definition ref_reserved := UKNz.ref_reserved.
Definition rerrno_loc_entry := UKNz.rerrno_loc_entry.
Definition rsysret_entry := UKNz.rsysret_entry.
Definition rvm_wait_entry := UKNz.rvm_wait_entry.
Lemma CODE : CodeAt.code_at rsegs 0x53d40 (QQRC.Mqa.realloc_code 0xde5fc0ef%Z 0x00044797%Z 0x1547b783%Z 0xfffc2797%Z 0x6f478793%Z 0xfffc2317%Z 0x59c30313%Z 0x31c000ef%Z 0x3400b0ef%Z).  Proof. StepGen.code_at_vm. Qed.
Lemma BASE4 : (0x53d40 mod 4 = 0)%Z.  Proof. reflexivity. Qed.
Lemma BASER : (0 <= 0x53d40 /\ 0x53d40 + 1092 <= 2^40)%Z.  Proof. vm_compute. split; discriminate. Qed.
Lemma CODE_rerrno_loc_entry : CodeAt.code_at rsegs rerrno_loc_entry Q2TC.Mq0.errno_loc_code.  Proof. StepGen.code_at_vm. Qed.
Definition ref_find_segment_none := @UKNz.ref_find_segment_none.
Definition ref_ro_addr_false := @UKNz.ref_ro_addr_false.
Definition ref_memory_read_none := @UKNz.ref_memory_read_none.
Definition ref_wview_overlay := @UKNz.ref_wview_overlay.
Definition ref_seg_rom_none := @UKNz.ref_seg_rom_none.
Definition ref_mrd_overlay := @UKNz.ref_mrd_overlay.
Definition meta_word_pg := @meta_word_pg.
Definition rmremap_spec := ltac:(pose proof (@rmremap_spec) as gw_h_; ltac2:(GwEqH.gw_rw_in @gw_h_ [[@gw_eq_rmremap_entry__3; @gw_eq_rmremap_entry__2; @gw_eq_rmremap_entry]; [@gw_eq_mremap_mem__3; @gw_eq_mremap_mem__2; @gw_eq_mremap_mem]; [@gw_eq_mremap_ret__3; @gw_eq_mremap_ret__2; @gw_eq_mremap_ret]]); exact gw_h_).
Definition rmremap_huge_spec := ltac:(pose proof (@rmremap_huge_spec) as gw_h_; ltac2:(GwEqH.gw_rw_in @gw_h_ [[@gw_eq_rmremap_entry__3; @gw_eq_rmremap_entry__2; @gw_eq_rmremap_entry]; [@gw_eq_mremap_mem__3; @gw_eq_mremap_mem__2; @gw_eq_mremap_mem]; [@gw_eq_mremap_ret__3; @gw_eq_mremap_ret__2; @gw_eq_mremap_ret]]); exact gw_h_).
Definition land_pow2_testbit := ltac:(pose proof (@UpkF.land_pow2_testbit) as gw_h_; ltac2:(GwEqH.gw_rw_in @gw_h_ [[@gw_eq_rget_meta_post__3; @gw_eq_rget_meta_post__2; @gw_eq_rget_meta_post]; [@gw_eq_runlock_post__3; @gw_eq_runlock_post__2; @gw_eq_runlock_post]]); exact gw_h_).
Definition sllw1_word' := ltac:(pose proof (@UpkF.sllw1_word') as gw_h_; ltac2:(GwEqH.gw_rw_in @gw_h_ [[@gw_eq_rget_meta_post__3; @gw_eq_rget_meta_post__2; @gw_eq_rget_meta_post]; [@gw_eq_runlock_post__3; @gw_eq_runlock_post__2; @gw_eq_runlock_post]]); exact gw_h_).
Definition zx32_wz := @zx32_wz.
Definition rdbi_range := ltac:(pose proof (@UznK.rdbi_range) as gw_h_; ltac2:(GwEqH.gw_rw_in @gw_h_ [[@gw_eq_rDB32__3; @gw_eq_rDB32__2; @gw_eq_rDB32]; [@gw_eq_rdbi__3; @gw_eq_rdbi__2; @gw_eq_rdbi]; [@gw_eq_rdebruijn_bytes__3; @gw_eq_rdebruijn_bytes__2; @gw_eq_rdebruijn_bytes]; [@gw_eq_rclz_v4__3; @gw_eq_rclz_v4__2; @gw_eq_rclz_v4]; [@gw_eq_rclz_pow__3; @gw_eq_rclz_pow__2; @gw_eq_rclz_pow]; [@gw_eq_rclz_fn__3; @gw_eq_rclz_fn__2; @gw_eq_rclz_fn]; [@gw_eq_rentry_post__3; @gw_eq_rentry_post__2; @gw_eq_rentry_post]; [@gw_eq_rentry_big_post__3; @gw_eq_rentry_big_post__2; @gw_eq_rentry_big_post]; [@gw_eq_rentry_ovf_post__3; @gw_eq_rentry_ovf_post__2; @gw_eq_rentry_ovf_post]]); exact gw_h_).
Definition rdebruijn_read := ltac:(pose proof (@UznK.rdebruijn_read) as gw_h_; ltac2:(GwEqH.gw_rw_in @gw_h_ [[@gw_eq_rDB32__3; @gw_eq_rDB32__2; @gw_eq_rDB32]; [@gw_eq_rdbi__3; @gw_eq_rdbi__2; @gw_eq_rdbi]; [@gw_eq_rdebruijn_bytes__3; @gw_eq_rdebruijn_bytes__2; @gw_eq_rdebruijn_bytes]; [@gw_eq_rclz_v4__3; @gw_eq_rclz_v4__2; @gw_eq_rclz_v4]; [@gw_eq_rclz_pow__3; @gw_eq_rclz_pow__2; @gw_eq_rclz_pow]; [@gw_eq_rclz_fn__3; @gw_eq_rclz_fn__2; @gw_eq_rclz_fn]; [@gw_eq_rentry_post__3; @gw_eq_rentry_post__2; @gw_eq_rentry_post]; [@gw_eq_rentry_big_post__3; @gw_eq_rentry_big_post__2; @gw_eq_rentry_big_post]; [@gw_eq_rentry_ovf_post__3; @gw_eq_rentry_ovf_post__2; @gw_eq_rentry_ovf_post]]); exact gw_h_).
Definition mul_srliw27 := ltac:(pose proof (@UznK.mul_srliw27) as gw_h_; ltac2:(GwEqH.gw_rw_in @gw_h_ [[@gw_eq_rDB32__3; @gw_eq_rDB32__2; @gw_eq_rDB32]; [@gw_eq_rdbi__3; @gw_eq_rdbi__2; @gw_eq_rdbi]; [@gw_eq_rdebruijn_bytes__3; @gw_eq_rdebruijn_bytes__2; @gw_eq_rdebruijn_bytes]; [@gw_eq_rclz_v4__3; @gw_eq_rclz_v4__2; @gw_eq_rclz_v4]; [@gw_eq_rclz_pow__3; @gw_eq_rclz_pow__2; @gw_eq_rclz_pow]; [@gw_eq_rclz_fn__3; @gw_eq_rclz_fn__2; @gw_eq_rclz_fn]; [@gw_eq_rentry_post__3; @gw_eq_rentry_post__2; @gw_eq_rentry_post]; [@gw_eq_rentry_big_post__3; @gw_eq_rentry_big_post__2; @gw_eq_rentry_big_post]; [@gw_eq_rentry_ovf_post__3; @gw_eq_rentry_ovf_post__2; @gw_eq_rentry_ovf_post]]); exact gw_h_).
Definition rclz_pow_eq := ltac:(pose proof (@UznK.rclz_pow_eq) as gw_h_; ltac2:(GwEqH.gw_rw_in @gw_h_ [[@gw_eq_rDB32__3; @gw_eq_rDB32__2; @gw_eq_rDB32]; [@gw_eq_rdbi__3; @gw_eq_rdbi__2; @gw_eq_rdbi]; [@gw_eq_rdebruijn_bytes__3; @gw_eq_rdebruijn_bytes__2; @gw_eq_rdebruijn_bytes]; [@gw_eq_rclz_v4__3; @gw_eq_rclz_v4__2; @gw_eq_rclz_v4]; [@gw_eq_rclz_pow__3; @gw_eq_rclz_pow__2; @gw_eq_rclz_pow]; [@gw_eq_rclz_fn__3; @gw_eq_rclz_fn__2; @gw_eq_rclz_fn]; [@gw_eq_rentry_post__3; @gw_eq_rentry_post__2; @gw_eq_rentry_post]; [@gw_eq_rentry_big_post__3; @gw_eq_rentry_big_post__2; @gw_eq_rentry_big_post]; [@gw_eq_rentry_ovf_post__3; @gw_eq_rentry_ovf_post__2; @gw_eq_rentry_ovf_post]]); exact gw_h_).
Definition lxor_4k_124 := ltac:(pose proof (@UznK.lxor_4k_124) as gw_h_; ltac2:(GwEqH.gw_rw_in @gw_h_ [[@gw_eq_rDB32__3; @gw_eq_rDB32__2; @gw_eq_rDB32]; [@gw_eq_rdbi__3; @gw_eq_rdbi__2; @gw_eq_rdbi]; [@gw_eq_rdebruijn_bytes__3; @gw_eq_rdebruijn_bytes__2; @gw_eq_rdebruijn_bytes]; [@gw_eq_rclz_v4__3; @gw_eq_rclz_v4__2; @gw_eq_rclz_v4]; [@gw_eq_rclz_pow__3; @gw_eq_rclz_pow__2; @gw_eq_rclz_pow]; [@gw_eq_rclz_fn__3; @gw_eq_rclz_fn__2; @gw_eq_rclz_fn]; [@gw_eq_rentry_post__3; @gw_eq_rentry_post__2; @gw_eq_rentry_post]; [@gw_eq_rentry_big_post__3; @gw_eq_rentry_big_post__2; @gw_eq_rentry_big_post]; [@gw_eq_rentry_ovf_post__3; @gw_eq_rentry_ovf_post__2; @gw_eq_rentry_ovf_post]]); exact gw_h_).
Definition lor_even_1 := ltac:(pose proof (@UznK.lor_even_1) as gw_h_; ltac2:(GwEqH.gw_rw_in @gw_h_ [[@gw_eq_rDB32__3; @gw_eq_rDB32__2; @gw_eq_rDB32]; [@gw_eq_rdbi__3; @gw_eq_rdbi__2; @gw_eq_rdbi]; [@gw_eq_rdebruijn_bytes__3; @gw_eq_rdebruijn_bytes__2; @gw_eq_rdebruijn_bytes]; [@gw_eq_rclz_v4__3; @gw_eq_rclz_v4__2; @gw_eq_rclz_v4]; [@gw_eq_rclz_pow__3; @gw_eq_rclz_pow__2; @gw_eq_rclz_pow]; [@gw_eq_rclz_fn__3; @gw_eq_rclz_fn__2; @gw_eq_rclz_fn]; [@gw_eq_rentry_post__3; @gw_eq_rentry_post__2; @gw_eq_rentry_post]; [@gw_eq_rentry_big_post__3; @gw_eq_rentry_big_post__2; @gw_eq_rentry_big_post]; [@gw_eq_rentry_ovf_post__3; @gw_eq_rentry_ovf_post__2; @gw_eq_rentry_ovf_post]]); exact gw_h_).
Definition memcpy_spec := @U4l4.memcpy_spec.
Definition lor_shl5 := ltac:(pose proof (@UiOj.lor_shl5) as gw_h_; ltac2:(GwEqH.gw_rw_in @gw_h_ [[@gw_eq_renframe_tail_mem__3; @gw_eq_renframe_tail_mem__2; @gw_eq_renframe_tail_mem]; [@gw_eq_ren3_post__3; @gw_eq_ren3_post__2; @gw_eq_ren3_post]; [@gw_eq_renframe_off_mem__3; @gw_eq_renframe_off_mem__2; @gw_eq_renframe_off_mem]]); exact gw_h_).
Definition land_m4096 := ltac:(pose proof (@UiOj.land_m4096) as gw_h_; ltac2:(GwEqH.gw_rw_in @gw_h_ [[@gw_eq_renframe_tail_mem__3; @gw_eq_renframe_tail_mem__2; @gw_eq_renframe_tail_mem]; [@gw_eq_ren3_post__3; @gw_eq_ren3_post__2; @gw_eq_ren3_post]; [@gw_eq_renframe_off_mem__3; @gw_eq_renframe_off_mem__2; @gw_eq_renframe_off_mem]]); exact gw_h_).
Lemma ROM_RSIZE_CLASSES : ltac2:(GwEq.gw_fact_ty 'segs '(@Q2TC.Mq0.gw_all) @ROM_RSIZE_CLASSES). Proof. first [ apply QWxq.Mq0.ro_bytes_b_sound; vm_compute; reflexivity | GwApply.gw_side ]. Qed.
Lemma ROM_reservedZ : ltac2:(GwEq.gw_fact_ty 'segs '(@Q2TC.Mq0.gw_all) @ROM_reservedZ). Proof. first [ apply QWxq.Mq0.ro_bytes_b_sound; vm_compute; reflexivity | GwApply.gw_side ]. Qed.
End GwI.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

Local Definition gwt_X : unit := (Q6nq.gwt_def (@Q8QT.Mq4.rshadow_rep) (@UQXM.rshadow_rep) (Q6nq.gwt_def (@Q2TC.Mq0.rshadow_rep) (@UQXM.rshadow_rep) (Q6nq.gwt_def (@Q2TC.Mq0.rrhead_post) (@UdkX.rrhead_post) (Q6nq.gwt_def (@QQRC.Mqa.rrhead_post) (@UdkX.rrhead_post) (Q6nq.gwt_def (@Q8QT.Mq4.rregions_wf) (@UQXM.rregions_wf) (Q6nq.gwt_def (@Q2TC.Mq0.rregions_wf) (@UQXM.rregions_wf) (Q6nq.gwt_def (@QkTt.Mq2.rrealloc_stmt) (@Upt0.rrealloc_stmt) (Q6nq.gwt_def (@Q2TC.Mq0.rrealloc_stmt) (@Upt0.rrealloc_stmt) (Q6nq.gwt_def (@QkTt.Mq2.rrealloc_post) (@Upt0.rrealloc_post) (Q6nq.gwt_def (@Q2TC.Mq0.rrealloc_post) (@Upt0.rrealloc_post) (Q6nq.gwt_def (@Q2TC.Mq0.rrealloc_entry) (@UdkX.rrealloc_entry) (Q6nq.gwt_def (@QQRC.Mqa.rrealloc_entry) (@UdkX.rrealloc_entry) (Q6nq.gwt_def (@Q2TC.Mq0.rr_tail2_post) (@UncX.rr_tail2_post) (Q6nq.gwt_def (@Qkeu.rr_tail2_post) (@UncX.rr_tail2_post) (Q6nq.gwt_def (@Q2TC.Mq0.rr_inplace_post) (@U4EM.rr_inplace_post) (Q6nq.gwt_def (@QKZH.rr_inplace_post) (@U4EM.rr_inplace_post) (Q6nq.gwt_def (@Q2TC.Mq0.rr_general) (@Uh29.rr_general) (Q6nq.gwt_def (@QSsB.Mq9.rr_general) (@Uh29.rr_general) (Q6nq.gwt_def (@QCa8.Mq5.rpres_except) (@Uv2Y.rpres_except) (Q6nq.gwt_def (@Q2TC.Mq0.rpres_except) (@Uv2Y.rpres_except) (Q6nq.gwt_def (@Q8QT.Mq4.rmrep_shadow) (@UQXM.rmrep_shadow) (Q6nq.gwt_def (@Q2TC.Mq0.rmrep_shadow) (@UQXM.rmrep_shadow) (Q6nq.gwt_def (@Q8QT.Mq4.rmrep_groups) (@UQXM.rmrep_groups) (Q6nq.gwt_def (@Q2TC.Mq0.rmrep_groups) (@UQXM.rmrep_groups) (Q6nq.gwt_def (@Q8QT.Mq4.rmrep_globals) (@UQXM.rmrep_globals) (Q6nq.gwt_def (@Q2TC.Mq0.rmrep_globals) (@UQXM.rmrep_globals) (Q6nq.gwt_def (@Q8QT.Mq4.rmrep_ctx) (@UQXM.rmrep_ctx) (Q6nq.gwt_def (@Q2TC.Mq0.rmrep_ctx) (@UQXM.rmrep_ctx) (Q6nq.gwt_def (@Q8QT.Mq4.rmrep_areas) (@UQXM.rmrep_areas) (Q6nq.gwt_def (@Q2TC.Mq0.rmrep_areas) (@UQXM.rmrep_areas) (Q6nq.gwt_def (@Q8QT.Mq4.rmrep) (@UQXM.rmrep) (Q6nq.gwt_def (@Q2TC.Mq0.rmrep) (@UQXM.rmrep) (Q6nq.gwt_def (@Q2TC.Mq0.rmremap_post) (@U1sW.rmremap_post) (Q6nq.gwt_def (@Q8QT.Mq3.rmremap_post) (@U1sW.rmremap_post) (Q6nq.gwt_def (@QDXD.Mq3.rmalloc_post) (@UXT6.rmalloc_post) (Q6nq.gwt_def (@Q2TC.Mq0.rmalloc_post) (@UXT6.rmalloc_post) (Q6nq.gwt_def (@QkTt.Mq6.rmalloc_impl_stmt) (@Unip.rmalloc_impl_stmt) (Q6nq.gwt_def (@Q2TC.Mq0.rmalloc_impl_stmt) (@Unip.rmalloc_impl_stmt) (Q6nq.gwt_def (@QDXD.Mq3.rheap_pres) (@UXT6.rheap_pres) (Q6nq.gwt_def (@Q2TC.Mq0.rheap_pres) (@UXT6.rheap_pres) (Q6nq.gwt_def (@Q8QT.Mq4.rgroup_rep) (@UQXM.rgroup_rep) (Q6nq.gwt_def (@Q2TC.Mq0.rgroup_rep) (@UQXM.rgroup_rep) (Q6nq.gwt_def (@QDXD.Mq3.rfree_post) (@UXT6.rfree_post) (Q6nq.gwt_def (@Q2TC.Mq0.rfree_post) (@UXT6.rfree_post) (Q6nq.gwt_def (@QkTt.Mq6.rfree_impl_stmt) (@Unip.rfree_impl_stmt) (Q6nq.gwt_def (@Q2TC.Mq0.rfree_impl_stmt) (@Unip.rfree_impl_stmt) (Q6nq.gwt_def (@QDXD.Mq3.rclient_write_ok) (@UXT6.rclient_write_ok) (Q6nq.gwt_def (@Q2TC.Mq0.rclient_write_ok) (@UXT6.rclient_write_ok) (Q6nq.gwt_def (@QDXD.Mq3.rclient_addr) (@UXT6.rclient_addr) (Q6nq.gwt_def (@Q2TC.Mq0.rclient_addr) (@UXT6.rclient_addr) (Q6nq.gwt_def (@QDXD.Mq3.rblock_range) (@UXT6.rblock_range) (Q6nq.gwt_def (@Q2TC.Mq0.rblock_range) (@UXT6.rblock_range) (Q6nq.gwt_def (@QCa8.Mq5.rauxv_ok) (@Uv2Y.rauxv_ok) (Q6nq.gwt_def (@Q2TC.Mq0.rauxv_ok) (@Uv2Y.rauxv_ok) (Q6nq.gwt_def (@Q8QT.Mq4.rarea_rep) (@UQXM.rarea_rep) (Q6nq.gwt_def (@Q2TC.Mq0.rarea_rep) (@UQXM.rarea_rep) (Q6nq.gwt_def (@QDXD.Mq3.ralloc_static) (@UXT6.ralloc_static) (Q6nq.gwt_def (@Q2TC.Mq0.ralloc_static) (@UXT6.ralloc_static) (Q6nq.gwt_def (@QDXD.Mq3.raddr_exposed) (@UXT6.raddr_exposed) (Q6nq.gwt_def (@Q2TC.Mq0.raddr_exposed) (@UXT6.raddr_exposed) (Q6nq.gwt_def (@Q2TC.Mq0.mremap_safe) (@U1sW.mremap_safe) (Q6nq.gwt_def (@Q8QT.Mq3.mremap_safe) (@U1sW.mremap_safe) (Q6nq.gwt_def (@Q8l1.Mqb.cond_mremap) (@U7ZX.cond_mremap) (Q6nq.gwt_def (@Q8l1.Mqb.cond_inplace) (@U7ZX.cond_inplace) (Q6nq.gwt_def (@QkTt.Mq2.RREALLOC_SYM) (@Upt0.RREALLOC_SYM) (Q6nq.gwt_def (@Q2TC.Mq0.RREALLOC_SYM) (@Upt0.RREALLOC_SYM) (Q6nq.gwt_def (@QDXD.Mq3.RHEAP) (@UXT6.RHEAP) (Q6nq.gwt_def (@Q2TC.Mq0.RHEAP) (@UXT6.RHEAP) Q6nq.gwt_nil)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))).
#[using="Type"] Lemma rr_prologue : ltac2:(Q6nq.ty2 'GwI.segs '(@Q2TC.Mq0.rr_prologue) [[@gw_eq_rrealloc_entry__3; @gw_eq_rrealloc_entry__2; @gw_eq_rrealloc_entry]] '([(-4097); 343452; 9223372036854771711]%Z : list Z) '(Q6nq.gwt_zc rrealloc_entry gwt_X)).
Proof. ltac2:(GwEq.gw_rw [[@gw_eq_rrealloc_entry__3; @gw_eq_rrealloc_entry__2; @gw_eq_rrealloc_entry]]); first [GwApply2.gw_by_name2 GwI.segs (@Q2TC.Mq0.rr_prologue) | autorewrite with gw_eqs; GwApply2.gw_by_name2 GwI.segs (@Q2TC.Mq0.rr_prologue)]. Qed.

#[using="Type"] Lemma rr_ovf_walk : ltac2:(Q6nq.ty2 'GwI.segs '(@Q2TC.Mq0.rr_ovf_walk) [[@gw_eq_rrealloc_entry__3; @gw_eq_rrealloc_entry__2; @gw_eq_rrealloc_entry]] '([(-4097)]%Z : list Z) '(Q6nq.gwt_zc rrealloc_entry (Q6nq.gwt_zc RATP (Q6nq.gwt_pat (@RATP) (@RATP) (Q6nq.gwt_hdr GwI.RATP (@RATP) gwt_X))))).
Proof. ltac2:(GwEq.gw_rw [[@gw_eq_rrealloc_entry__3; @gw_eq_rrealloc_entry__2; @gw_eq_rrealloc_entry]]); first [GwApply2.gw_by_name2 GwI.segs (@Q2TC.Mq0.rr_ovf_walk) | autorewrite with gw_eqs; GwApply2.gw_by_name2 GwI.segs (@Q2TC.Mq0.rr_ovf_walk)]. Qed.

#[using="Type"] Lemma rmrep_shadow_byte : ltac2:(Q6nq.ty2 'GwI.segs '(@Q2TC.Mq0.rmrep_shadow_byte) [[@gw_eq_rmrep__3; @gw_eq_rmrep__2; @gw_eq_rmrep]] '(@nil Z) 'gwt_X).
Proof. ltac2:(GwEq.gw_rw [[@gw_eq_rmrep__3; @gw_eq_rmrep__2; @gw_eq_rmrep]]); first [GwApply2.gw_by_name2 GwI.segs (@Q2TC.Mq0.rmrep_shadow_byte) | autorewrite with gw_eqs; GwApply2.gw_by_name2 GwI.segs (@Q2TC.Mq0.rmrep_shadow_byte)]. Qed.

#[using="Type"] Lemma byte_of_eq v k : 0 <= k -> byte_of v k = (v / 2 ^ (8 * k)) mod 256.
Proof. first [GwApply2.gw_by_name2 GwI.segs (@Q2TC.Mq0.byte_of_eq) | autorewrite with gw_eqs; GwApply2.gw_by_name2 GwI.segs (@Q2TC.Mq0.byte_of_eq)]. Qed.

#[using="Type"] Lemma le4_byte_of v : 0 <= v < 2^32 -> le4 (wz v) = [b8 (byte_of v 0); b8 (byte_of v 1); b8 (byte_of v 2); b8 (byte_of v 3)].
Proof. first [GwApply2.gw_by_name2 GwI.segs (@Q2TC.Mq0.le4_byte_of) | autorewrite with gw_eqs; GwApply2.gw_by_name2 GwI.segs (@Q2TC.Mq0.le4_byte_of)]. Qed.

#[using="Type"] Lemma bytes_at_cons m a x bs : bytes_at rsegs m a [x] -> bytes_at rsegs m (a + 1) bs -> bytes_at rsegs m a (x :: bs).
Proof. first [GwApply2.gw_by_name2 GwI.segs (@Q2TC.Mq0.bytes_at_cons) | autorewrite with gw_eqs; GwApply2.gw_by_name2 GwI.segs (@Q2TC.Mq0.bytes_at_cons)]. Qed.

Definition rr_mremap_tree (cs : mstate) (slot : cptr) (off n : Z) (g : aptr) : QUZl.M (mstate * option rr_where) :=
let mr := get_meta_rec cs g in
guard 70 (m_sizeclass mr =? 63) (
match m_mem mr with
| None => SVis (EUndef UBadPtr) (fun _ => ret (cs, @None rr_where))
| Some gmem =>
let needed := rr_needed n (UNIT * off) in
let oldlen := m_maplen mr * 4096 in
let rid := fst gmem in
if oldlen =? needed then ret (cs, Some RRSame)
else if PTRDIFF_MAX <=? needed then rr_general cs slot n
else
SVis (EMremap (conc cs gmem) oldlen needed MREMAP_MAYMOVE) (fun r =>
if negb (mremap_answer_ok (live_ranges cs) (conc cs gmem) oldlen needed r) then bad_answer (ret (cs, @None rr_where))
else if is_err r then rr_general cs slot n
else ret (strip (remap_region rid r needed g cs), Some RRSame))
end) (ret (cs, @None rr_where)).

#[using="Type"] Lemma crealloc_cases : ltac2:(Q6nq.ty2 'GwI.segs '(@Q2TC.Mq0.crealloc_cases) [[@gw_eq_cond_inplace__3; @gw_eq_cond_inplace__2; @gw_eq_cond_inplace]; [@gw_eq_cond_mremap__3; @gw_eq_cond_mremap__2; @gw_eq_cond_mremap]; [@gw_eq_rr_general__3; @gw_eq_rr_general__2; @gw_eq_rr_general]] '(@nil Z) '(Q6nq.gwt_zc UNIT (Q6nq.gwt_zc IB (Q6nq.gwt_def (@Q2TC.Mq0.rr_mremap_tree) (@rr_mremap_tree) gwt_X)))).
Proof. ltac2:(GwEq.gw_rw [[@gw_eq_cond_inplace__3; @gw_eq_cond_inplace__2; @gw_eq_cond_inplace]; [@gw_eq_cond_mremap__3; @gw_eq_cond_mremap__2; @gw_eq_cond_mremap]; [@gw_eq_rr_general__3; @gw_eq_rr_general__2; @gw_eq_rr_general]]); first [GwApply2.gw_by_name2 GwI.segs (@Q2TC.Mq0.crealloc_cases) | autorewrite with gw_eqs; GwApply2.gw_by_name2 GwI.segs (@Q2TC.Mq0.crealloc_cases)]. Qed.

#[using="Type"] Lemma size_overflows_small n : 0 <= n < 2^32 -> size_overflows n = false.
Proof. first [GwApply2.gw_by_name2 GwI.segs (@Q2TC.Mq0.size_overflows_small) | autorewrite with gw_eqs; GwApply2.gw_by_name2 GwI.segs (@Q2TC.Mq0.size_overflows_small)]. Qed.

#[using="Type"] Lemma ctx_havoc p n st : ctx (havoc p n st) = ctx st.
Proof. first [GwApply2.gw_by_name2 GwI.segs (@Q2TC.Mq0.ctx_havoc) | autorewrite with gw_eqs; GwApply2.gw_by_name2 GwI.segs (@Q2TC.Mq0.ctx_havoc)]. Qed.
#[using="Type"] Lemma ctx_set_size p e n b st : ctx (set_size p e n b st) = ctx st.
Proof. first [GwApply2.gw_by_name2 GwI.segs (@Q2TC.Mq0.ctx_set_size) | autorewrite with gw_eqs; GwApply2.gw_by_name2 GwI.segs (@Q2TC.Mq0.ctx_set_size)]. Qed.
#[using="Type"] Lemma brk_link_ext st st' pb : ctx st' = ctx st -> (forall q, conc st' q = conc st q) -> brk_link st pb -> brk_link st' pb.
Proof. first [GwApply2.gw_by_name2 GwI.segs (@Q2TC.Mq0.brk_link_ext) | autorewrite with gw_eqs; GwApply2.gw_by_name2 GwI.segs (@Q2TC.Mq0.brk_link_ext)]. Qed.

#[using="Type"] Lemma bytes_at_prefix_eq : ltac2:(Q6nq.ty2 'GwI.segs '(@Q2TC.Mq0.bytes_at_prefix_eq) [] '(@nil Z) '(Q6nq.gwt_def (@Q2TC.Mq0.rr_mremap_tree) (@rr_mremap_tree) gwt_X)).
Proof. first [GwApply2.gw_by_name2 GwI.segs (@Q2TC.Mq0.bytes_at_prefix_eq) | autorewrite with gw_eqs; GwApply2.gw_by_name2 GwI.segs (@Q2TC.Mq0.bytes_at_prefix_eq)]. Qed.

#[using="Type"] Lemma rheap_pres_of_rpres : ltac2:(Q6nq.ty2 'GwI.segs '(@Q2TC.Mq0.rheap_pres_of_rpres) [[@gw_eq_rclient_addr__3; @gw_eq_rclient_addr__2; @gw_eq_rclient_addr]; [@gw_eq_rheap_pres__3; @gw_eq_rheap_pres__2; @gw_eq_rheap_pres]; [@gw_eq_rpres_except__3; @gw_eq_rpres_except__2; @gw_eq_rpres_except]] '(@nil Z) '(Q6nq.gwt_def (@Q2TC.Mq0.rr_mremap_tree) (@rr_mremap_tree) gwt_X)).
Proof. ltac2:(GwEq.gw_rw [[@gw_eq_rclient_addr__3; @gw_eq_rclient_addr__2; @gw_eq_rclient_addr]; [@gw_eq_rheap_pres__3; @gw_eq_rheap_pres__2; @gw_eq_rheap_pres]; [@gw_eq_rpres_except__3; @gw_eq_rpres_except__2; @gw_eq_rpres_except]]); first [GwApply2.gw_by_name2 GwI.segs (@Q2TC.Mq0.rheap_pres_of_rpres) | autorewrite with gw_eqs; GwApply2.gw_by_name2 GwI.segs (@Q2TC.Mq0.rheap_pres_of_rpres)]. Qed.

#[using="Type"] Lemma bytes_at_mext m m' a bs : (forall x, m' x = m x) -> bytes_at rsegs m a bs -> bytes_at rsegs m' a bs.
Proof. first [GwApply2.gw_by_name2 GwI.segs (@Q2TC.Mq0.bytes_at_mext) | autorewrite with gw_eqs; GwApply2.gw_by_name2 GwI.segs (@Q2TC.Mq0.bytes_at_mext)]. Qed.

#[using="Type"] Lemma munch_of_mext W m m' : (forall x, m' x = m x) -> munch W m m'.
Proof. ltac2:(GwEq.gw_rw [[@gw_eq_W__3; @gw_eq_W__2; @gw_eq_W]]); first [GwApply2.gw_by_name2 GwI.segs (@Q2TC.Mq0.munch_of_mext) | autorewrite with gw_eqs; GwApply2.gw_by_name2 GwI.segs (@Q2TC.Mq0.munch_of_mext)]. Qed.

#[using="Type"] Lemma wmono_of_mext m m' : (forall x, m' x = m x) -> wmono rsegs m m'.
Proof. first [GwApply2.gw_by_name2 GwI.segs (@Q2TC.Mq0.wmono_of_mext) | autorewrite with gw_eqs; GwApply2.gw_by_name2 GwI.segs (@Q2TC.Mq0.wmono_of_mext)]. Qed.

#[using="Type"] Lemma mem_inv_mext m m' : (forall x, m' x = m x) -> mem_inv rsegs m -> mem_inv rsegs m'.
Proof. first [GwApply2.gw_by_name2 GwI.segs (@Q2TC.Mq0.mem_inv_mext) | autorewrite with gw_eqs; GwApply2.gw_by_name2 GwI.segs (@Q2TC.Mq0.mem_inv_mext)]. Qed.

Section TOP.
Hypothesis RMI : rmalloc_impl_stmt.
Hypothesis RFI : rfree_impl_stmt.
#[using="Type"] Lemma implM_unr_bind {A B} (f : A -> Ql2m.Mq3.M PState B) s Q ms : implM rsegs (mbind munr f) s Q ms.
Proof. first [GwApply2.gw_by_name2 GwI.segs (@Q2TC.Mq0.implM_unr_bind) | autorewrite with gw_eqs; GwApply2.gw_by_name2 GwI.segs (@Q2TC.Mq0.implM_unr_bind)]. Qed.

#[using="RMI RFI"] Theorem rrealloc_spec_proof : rrealloc_stmt.
Proof. ltac2:(GwEq.gw_rw [[@gw_eq_RFI__3; @gw_eq_RFI__2; @gw_eq_RFI]; [@gw_eq_rrealloc_stmt__3; @gw_eq_rrealloc_stmt__2; @gw_eq_rrealloc_stmt]]); first [GwApply2.gw_by_name2 GwI.segs (@Q2TC.Mq0.rrealloc_spec_proof) | autorewrite with gw_eqs; GwApply2.gw_by_name2 GwI.segs (@Q2TC.Mq0.rrealloc_spec_proof)]. Qed.
End TOP.

End RC__1.
