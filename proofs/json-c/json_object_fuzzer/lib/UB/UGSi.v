(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)


From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib Require CodeAt StepGen GwInst GwEq GwApply GwApply2. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Q6nq.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QROt.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UKNz.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QQRC.

From Stdlib Require Import ZArith NArith List Lia Bool.
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
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q2qa.Mq1. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QytA.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QytA. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Q4J3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q4J3.Mq4. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QPjm.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QPjm.Mq0. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Q4J3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q4J3.Mq2. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Qy5Y.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qy5Y.Mq6. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QPjm.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QPjm.Mq3. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QJE4.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QJE4.Mq0. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QJE4.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QJE4.Mq1. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QWTl.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QWTl.Mq1. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QDUx.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QDUx.Mq2.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QZAi.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QZAi.Mq2. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QUZl.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QUZl. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Q7S0.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q7S0.Mq0. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QGeV.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QGeV.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UQXM.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UQXM. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require Uv2Y.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Uv2Y. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UIMz.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UIMz. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require U8eV.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import U8eV. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UC00.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UC00. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UlEO.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UlEO. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UNR4.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UNR4. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UWzX.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UWzX. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UA2f.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UA2f.
Import ListNotations. Local Ltac Qfw3.Mq3.model_reg_tac n X mexpr ::= Qfw3.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Qfw3.Mq3.zeq_fast ::= Qfw3.Mq3.mkr__zeq_fast_0.
Open Scope bv_scope.
Open Scope Z_scope.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Q6q3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q6q3.

From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib Require CodeAt StepGen GwInst GwApply GwApply2.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module GwI.
Definition segs := rsegs.
Definition base := 0x52b8c%Z.
Definition w_7 := 0x00013517%Z.
Definition w_8 := 0xe2853903%Z.
Definition w_10 := 0x00045597%Z.
Definition w_12 := 0x3c458993%Z.
Definition w_14 := 0x00045597%Z.
Definition w_15 := 0x2cc58413%Z.
Definition w_30 := 0x0350c0ef%Z.
Definition w_98 := 0x4f8010ef%Z.
Definition w_120 := 0x4a0010ef%Z.
Definition w_173 := 0x4b8010ef%Z.
Definition w_175 := 0xd19fd0ef%Z.
Definition w_181 := 0x9c4fe0ef%Z.
Definition hi_7 := (Z_to_bv 20 19).
Definition hi_10 := (Z_to_bv 20 69).
Definition hi_14 := (Z_to_bv 20 69).
Definition lo_8 := (Z_to_bv 12 3624).
Definition lo_12 := (Z_to_bv 12 964).
Definition lo_15 := (Z_to_bv 12 716).
Definition joff_30 := (Z_to_bv 21 51252).
Definition joff_98 := (Z_to_bv 21 5368).
Definition joff_120 := (Z_to_bv 21 5280).
Definition joff_173 := (Z_to_bv 21 5304).
Definition joff_175 := (Z_to_bv 21 2088216).
Definition joff_181 := (Z_to_bv 21 2089412).
Definition e_197bc := 0x51024%Z.
Definition e_24f80 := 0x5f438%Z.
Definition RATP := UKNz.RATP.
Definition RDEBRUIJN := UKNz.RDEBRUIJN.
Definition RGOT_SSP := UKNz.RGOT_SSP.
Definition RIMG_HI := UKNz.RIMG_HI.
Definition RDATA_LO := UKNz.RDATA_LO.
Definition gw_RTEXT_LO := ltac:(let gw_v_ := eval cbv in (fst (nth 1 UKNz.ref_reserved (0%Z, 0%Z))) in exact gw_v_).
Definition gw_RDATA2_LO := ltac:(let gw_v_ := eval cbv in (fst (nth 3 UKNz.ref_reserved (0%Z, 0%Z))) in exact gw_v_).
Definition ref_reserved := UKNz.ref_reserved.
Definition rerrno_loc_entry := UKNz.rerrno_loc_entry.
Definition rvm_wait_entry := UKNz.rvm_wait_entry.
Lemma CODE : CodeAt.code_at rsegs 0x52b8c (QQRC.Mq5.alloc_meta_code 0x00013517%Z 0xe2853903%Z 0x00045597%Z 0x3c458993%Z 0x00045597%Z 0x2cc58413%Z 0x0350c0ef%Z 0x4f8010ef%Z 0x4a0010ef%Z 0x4b8010ef%Z 0xd19fd0ef%Z 0x9c4fe0ef%Z).  Proof. StepGen.code_at_vm. Qed.
Lemma BASE4 : (0x52b8c mod 4 = 0)%Z.  Proof. reflexivity. Qed.
Lemma BASER : (0 <= 0x52b8c /\ 0x52b8c + 728 <= 2^40)%Z.  Proof. vm_compute. split; discriminate. Qed.
Lemma CODE_rerrno_loc_entry : CodeAt.code_at rsegs rerrno_loc_entry QROt.errno_loc_code.  Proof. StepGen.code_at_vm. Qed.
Definition ref_find_segment_none := @UKNz.ref_find_segment_none.
Definition ref_ro_addr_false := @UKNz.ref_ro_addr_false.
Definition ref_memory_read_none := @UKNz.ref_memory_read_none.
Definition ref_wview_overlay := @UKNz.ref_wview_overlay.
Definition ref_seg_rom_none := @UKNz.ref_seg_rom_none.
Definition ref_mrd_overlay := @UKNz.ref_mrd_overlay.
End GwI.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

Local Definition gwt_X : unit := (Q6nq.gwt_def (@Q8QT.Mq4.rshadow_rep) (@UQXM.rshadow_rep) (Q6nq.gwt_def (@QROt.rshadow_rep) (@UQXM.rshadow_rep) (Q6nq.gwt_def (@Q8QT.Mq4.rregions_wf) (@UQXM.rregions_wf) (Q6nq.gwt_def (@QROt.rregions_wf) (@UQXM.rregions_wf) (Q6nq.gwt_def (@QCa8.Mq5.rpres_except) (@Uv2Y.rpres_except) (Q6nq.gwt_def (@QROt.rpres_except) (@Uv2Y.rpres_except) (Q6nq.gwt_def (@Q8QT.Mq4.rmrep_shadow) (@UQXM.rmrep_shadow) (Q6nq.gwt_def (@QROt.rmrep_shadow) (@UQXM.rmrep_shadow) (Q6nq.gwt_def (@Q8QT.Mq4.rmrep_groups) (@UQXM.rmrep_groups) (Q6nq.gwt_def (@QROt.rmrep_groups) (@UQXM.rmrep_groups) (Q6nq.gwt_def (@Q8QT.Mq4.rmrep_globals) (@UQXM.rmrep_globals) (Q6nq.gwt_def (@QROt.rmrep_globals) (@UQXM.rmrep_globals) (Q6nq.gwt_def (@Q8QT.Mq4.rmrep_ctx) (@UQXM.rmrep_ctx) (Q6nq.gwt_def (@QROt.rmrep_ctx) (@UQXM.rmrep_ctx) (Q6nq.gwt_def (@Q8QT.Mq4.rmrep_areas) (@UQXM.rmrep_areas) (Q6nq.gwt_def (@QROt.rmrep_areas) (@UQXM.rmrep_areas) (Q6nq.gwt_def (@Q8QT.Mq4.rmrep) (@UQXM.rmrep) (Q6nq.gwt_def (@QROt.rmrep) (@UQXM.rmrep) (Q6nq.gwt_def (@Q8QT.Mq4.rgroup_rep) (@UQXM.rgroup_rep) (Q6nq.gwt_def (@QROt.rgroup_rep) (@UQXM.rgroup_rep) (Q6nq.gwt_def (@Q8QT.Mq4.rarea_rep) (@UQXM.rarea_rep) (Q6nq.gwt_def (@QROt.rarea_rep) (@UQXM.rarea_rep) (Q6nq.gwt_def (@QROt.ram_ret_post) (@UNR4.ram_ret_post) (Q6nq.gwt_def (@QQRC.Mq5.ram_ret_post) (@UNR4.ram_ret_post) (Q6nq.gwt_def (@QROt.ram_frame) (@UNR4.ram_frame) (Q6nq.gwt_def (@QQRC.Mq5.ram_frame) (@UNR4.ram_frame) (Q6nq.gwt_def (@QROt.ram_fp) (@UNR4.ram_fp) (Q6nq.gwt_def (@QQRC.Mq5.ram_fp) (@UNR4.ram_fp) Q6nq.gwt_nil)))))))))))))))))))))))))))).
#[using="Type"] Lemma ram_disp_fin : ltac2:(Q6nq.ty2 'GwI.segs '(@QROt.ram_disp_fin) [[@gw_eq_rmrep__3; @gw_eq_rmrep__2; @gw_eq_rmrep]] '([4096; 339092; 339508]%Z : list Z) '(Q6nq.gwt_unf (@PGSZ) (Q6nq.gwt_zc RSSP_GUARD (Q6nq.gwt_zc RMLOCK gwt_X)))).
Proof. ltac2:(GwEq.gw_rw [[@gw_eq_rmrep__3; @gw_eq_rmrep__2; @gw_eq_rmrep]]); first [GwApply2.gw_by_name2 GwI.segs (@QROt.ram_disp_fin) | autorewrite with gw_eqs; GwApply2.gw_by_name2 GwI.segs (@QROt.ram_disp_fin)]. Qed.

#[using="Type"] Lemma ram_to_mprotect : ltac2:(Q6nq.ty2 'GwI.segs '(@QROt.ram_to_mprotect) [] '([4096; 339508; 339524]%Z : list Z) '(Q6nq.gwt_unf (@PGSZ) (Q6nq.gwt_zc rmprotect_entry gwt_X))).
Proof. first [GwApply2.gw_by_name2 GwI.segs (@QROt.ram_to_mprotect) | autorewrite with gw_eqs; GwApply2.gw_by_name2 GwI.segs (@QROt.ram_to_mprotect)]. Qed.

#[using="Type"] Lemma ram_mp_ok0 : ltac2:(Q6nq.ty2 'GwI.segs '(@QROt.ram_mp_ok0) [] '([339364; 339524]%Z : list Z) 'gwt_X).
Proof. first [GwApply2.gw_by_name2 GwI.segs (@QROt.ram_mp_ok0) | autorewrite with gw_eqs; GwApply2.gw_by_name2 GwI.segs (@QROt.ram_mp_ok0)]. Qed.

#[using="Type"] Lemma ram_mp_fail : ltac2:(Q6nq.ty2 'GwI.segs '(@QROt.ram_mp_fail) [[@gw_eq_ram_fp__3; @gw_eq_ram_fp__2; @gw_eq_ram_fp]; [@gw_eq_ram_frame__3; @gw_eq_ram_frame__2; @gw_eq_ram_frame]; [@gw_eq_ram_ret_post__3; @gw_eq_ram_ret_post__2; @gw_eq_ram_ret_post]; [@gw_eq_rmrep__3; @gw_eq_rmrep__2; @gw_eq_rmrep]; [@gw_eq_rpres_except__3; @gw_eq_rpres_except__2; @gw_eq_rpres_except]] '([4095; 339524; 490496]%Z : list Z) '(Q6nq.gwt_unf (@RATP) (Q6nq.gwt_zc RSSP_GUARD (Q6nq.gwt_zc RMLOCK (Q6nq.gwt_pat (@RATP) (@RATP) (Q6nq.gwt_hdr GwI.RATP (@RATP) gwt_X)))))).
Proof. ltac2:(GwEq.gw_rw [[@gw_eq_ram_fp__3; @gw_eq_ram_fp__2; @gw_eq_ram_fp]; [@gw_eq_ram_frame__3; @gw_eq_ram_frame__2; @gw_eq_ram_frame]; [@gw_eq_ram_ret_post__3; @gw_eq_ram_ret_post__2; @gw_eq_ram_ret_post]; [@gw_eq_rmrep__3; @gw_eq_rmrep__2; @gw_eq_rmrep]; [@gw_eq_rpres_except__3; @gw_eq_rpres_except__2; @gw_eq_rpres_except]]); first [GwApply2.gw_by_name2 GwI.segs (@QROt.ram_mp_fail) | autorewrite with gw_eqs; GwApply2.gw_by_name2 GwI.segs (@QROt.ram_mp_fail)]. Qed.

End RC__1.
