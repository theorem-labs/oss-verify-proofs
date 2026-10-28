(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)


From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib Require CodeAt StepGen GwInst GwEq GwEqH GwApply GwApply2. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Q6nq.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Qe1A.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UKNz.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Qy8Z.

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
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Q2qa.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q2qa.Mq1. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Qy5Y.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qy5Y.Mq1. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Q4J3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q4J3.Mq1. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QytA.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QytA. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Qnxq.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qnxq. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QJE4.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QJE4.Mq4. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Qy5Y.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qy5Y.Mq5. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QWTl.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QWTl.Mq5. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Qy5Y.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qy5Y.Mq4. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Q4J3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q4J3.Mq3.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QZAi.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QZAi.Mq2. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QUZl.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QUZl. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Q7S0.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q7S0.Mq0. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Ql2m.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Ql2m.Mq3. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QGeV.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QGeV.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QLsg.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QLsg. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QDUx.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QDUx.Mq8. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Q9Ay.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q9Ay.Mqa. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QXxF.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QXxF.Mq3. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QDUx.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QDUx.Mq9. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Q6y7.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q6y7.Mq2. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QDUx.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QDUx.Mq7. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Q3o5.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q3o5. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Q8P7.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q8P7. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QTyG.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QTyG.Mq1.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UQXM.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UQXM. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require Uv2Y.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Uv2Y. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UpkF.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UpkF. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UIMz.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UIMz. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require Un7h.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Un7h. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require U8eV.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import U8eV. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UC00.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UC00. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require U8FW.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import U8FW. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UDxd.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UDxd. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UiOj.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UiOj. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UJOB.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UJOB. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UWfR.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UWfR. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UznK.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UznK. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require U7Ti.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import U7Ti. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UAr0.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UAr0. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UwoZ.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UwoZ. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UxSL.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UxSL. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UYQW.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UYQW.
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
Definition base := 0x52e64%Z.
Definition w_11 := 0xcd1fd0ef%Z.
Definition w_26 := 0x00045597%Z.
Definition w_27 := 0xac58493%Z.
Definition w_37 := 0x314010ef%Z.
Definition w_40 := 0x00045517%Z.
Definition w_41 := 0xf8f54503%Z.
Definition w_43 := 0x00045517%Z.
Definition w_44 := 0x06850513%Z.
Definition w_45 := 0x6380d0ef%Z.
Definition w_57 := 0xfffc3617%Z.
Definition w_59 := 0x5d860993%Z.
Definition w_85 := 0xfffc3617%Z.
Definition w_90 := 0x58860593%Z.
Definition w_125 := 0x00045517%Z.
Definition w_126 := 0xe3b54503%Z.
Definition w_128 := 0x00045517%Z.
Definition w_129 := 0xf1450513%Z.
Definition w_130 := 0x4e40d0ef%Z.
Definition w_147 := 0x00045517%Z.
Definition w_148 := 0xec850513%Z.
Definition w_149 := 0x7200d0ef%Z.
Definition w_152 := 0x350010ef%Z.
Definition w_203 := 0x6480d0ef%Z.
Definition w_216 := 0x00045517%Z.
Definition w_217 := 0xdb450513%Z.
Definition w_218 := 0x60c0d0ef%Z.
Definition hi_26 := (Z_to_bv 20 69).
Definition hi_40 := (Z_to_bv 20 69).
Definition hi_43 := (Z_to_bv 20 69).
Definition hi_57 := (Z_to_bv 20 1048515).
Definition hi_85 := (Z_to_bv 20 1048515).
Definition hi_125 := (Z_to_bv 20 69).
Definition hi_128 := (Z_to_bv 20 69).
Definition hi_147 := (Z_to_bv 20 69).
Definition hi_216 := (Z_to_bv 20 69).
Definition lo_27 := (Z_to_bv 12 172).
Definition lo_41 := (Z_to_bv 12 3983).
Definition lo_44 := (Z_to_bv 12 104).
Definition lo_59 := (Z_to_bv 12 1496).
Definition lo_90 := (Z_to_bv 12 1416).
Definition lo_126 := (Z_to_bv 12 3643).
Definition lo_129 := (Z_to_bv 12 3860).
Definition lo_148 := (Z_to_bv 12 3784).
Definition lo_217 := (Z_to_bv 12 3508).
Definition joff_11 := (Z_to_bv 21 2088144).
Definition joff_37 := (Z_to_bv 21 4884).
Definition joff_45 := (Z_to_bv 21 54840).
Definition joff_130 := (Z_to_bv 21 54500).
Definition joff_149 := (Z_to_bv 21 55072).
Definition joff_152 := (Z_to_bv 21 4944).
Definition joff_203 := (Z_to_bv 21 54856).
Definition joff_218 := (Z_to_bv 21 54796).
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
Definition rlock_entry := UKNz.rlock_entry.
Definition runlock_entry := UKNz.runlock_entry.
Lemma CODE : CodeAt.code_at rsegs 0x52e64 (Qy8Z.Mq7.malloc_code 0xcd1fd0ef%Z 0x00045597%Z 0xac58493%Z 0x314010ef%Z 0x00045517%Z 0xf8f54503%Z 0x00045517%Z 0x06850513%Z 0x6380d0ef%Z 0xfffc3617%Z 0x5d860993%Z 0xfffc3617%Z 0x58860593%Z 0x00045517%Z 0xe3b54503%Z 0x00045517%Z 0xf1450513%Z 0x4e40d0ef%Z 0x00045517%Z 0xec850513%Z 0x7200d0ef%Z 0x350010ef%Z 0x6480d0ef%Z 0x00045517%Z 0xdb450513%Z 0x60c0d0ef%Z).  Proof. StepGen.code_at_vm. Qed.
Lemma BASE4 : (0x52e64 mod 4 = 0)%Z.  Proof. reflexivity. Qed.
Lemma BASER : (0 <= 0x52e64 /\ 0x52e64 + 880 <= 2^40)%Z.  Proof. vm_compute. split; discriminate. Qed.
Lemma CODE_rerrno_loc_entry : CodeAt.code_at rsegs rerrno_loc_entry Qe1A.Mqa.errno_loc_code.  Proof. StepGen.code_at_vm. Qed.
Definition ref_find_segment_none := @UKNz.ref_find_segment_none.
Definition ref_ro_addr_false := @UKNz.ref_ro_addr_false.
Definition ref_memory_read_none := @UKNz.ref_memory_read_none.
Definition ref_wview_overlay := @UKNz.ref_wview_overlay.
Definition ref_seg_rom_none := @UKNz.ref_seg_rom_none.
Definition ref_mrd_overlay := @UKNz.ref_mrd_overlay.
Definition rmunmap_spec := ltac:(pose proof (@rmunmap_spec) as gw_h_; ltac2:(GwEqH.gw_rw_in @gw_h_ [[@gw_eq_rmunmap_post__3; @gw_eq_rmunmap_post__2; @gw_eq_rmunmap_post]; [@gw_eq_rmprotect_post__3; @gw_eq_rmprotect_post__2; @gw_eq_rmprotect_post]; [@gw_eq_rmmap_fixed_post__3; @gw_eq_rmmap_fixed_post__2; @gw_eq_rmmap_fixed_post]]); exact gw_h_).
Definition rmmap_anon_spec := ltac:(pose proof (@rmmap_anon_spec) as gw_h_; ltac2:(GwEqH.gw_rw_in @gw_h_ [[@gw_eq_rmunmap_post__3; @gw_eq_rmunmap_post__2; @gw_eq_rmunmap_post]; [@gw_eq_rmprotect_post__3; @gw_eq_rmprotect_post__2; @gw_eq_rmprotect_post]; [@gw_eq_rmmap_fixed_post__3; @gw_eq_rmmap_fixed_post__2; @gw_eq_rmmap_fixed_post]]); exact gw_h_).
Definition runlock_spec := ltac:(pose proof (@runlock_spec) as gw_h_; ltac2:(GwEqH.gw_rw_in @gw_h_ [[@gw_eq_rget_meta_post__3; @gw_eq_rget_meta_post__2; @gw_eq_rget_meta_post]; [@gw_eq_runlock_post__3; @gw_eq_runlock_post__2; @gw_eq_runlock_post]]); exact gw_h_).
Definition land_m4096 := ltac:(pose proof (@land_m4096) as gw_h_; ltac2:(GwEqH.gw_rw_in @gw_h_ [[@gw_eq_renframe_tail_mem__3; @gw_eq_renframe_tail_mem__2; @gw_eq_renframe_tail_mem]; [@gw_eq_ren3_post__3; @gw_eq_ren3_post__2; @gw_eq_ren3_post]; [@gw_eq_renframe_off_mem__3; @gw_eq_renframe_off_mem__2; @gw_eq_renframe_off_mem]]); exact gw_h_).
Lemma ROM_reservedZ : ltac2:(GwEq.gw_fact_ty 'segs '(@Qe1A.Mqa.gw_all) @ROM_reservedZ). Proof. first [ apply QWxq.Mq0.ro_bytes_b_sound; vm_compute; reflexivity | GwApply.gw_side ]. Qed.
End GwI.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

Local Definition gwt_X : unit := (Q6nq.gwt_def (@Qe1A.Mqa.runlock_post) (@UpkF.runlock_post) (Q6nq.gwt_def (@QCa8.Mq4.runlock_post) (@UpkF.runlock_post) (Q6nq.gwt_def (@Q8QT.Mq4.rshadow_rep) (@UQXM.rshadow_rep) (Q6nq.gwt_def (@Qe1A.Mqa.rshadow_rep) (@UQXM.rshadow_rep) (Q6nq.gwt_def (@QQRC.Mq7.rseq_post) (@UYQW.rseq_post) (Q6nq.gwt_def (@Qe1A.Mqa.rseq_post) (@UYQW.rseq_post) (Q6nq.gwt_def (@QDXD.Mq2.rrepfoot) (@UIMz.rrepfoot) (Q6nq.gwt_def (@Qe1A.Mqa.rrepfoot) (@UIMz.rrepfoot) (Q6nq.gwt_def (@Q8QT.Mq4.rregions_wf) (@UQXM.rregions_wf) (Q6nq.gwt_def (@Qe1A.Mqa.rregions_wf) (@UQXM.rregions_wf) (Q6nq.gwt_def (@QCa8.Mq5.rpres_except) (@Uv2Y.rpres_except) (Q6nq.gwt_def (@Qe1A.Mqa.rpres_except) (@Uv2Y.rpres_except) (Q6nq.gwt_def (@Q8QT.Mq2.rmunmap_post) (@UC00.rmunmap_post) (Q6nq.gwt_def (@Qe1A.Mqa.rmunmap_post) (@UC00.rmunmap_post) (Q6nq.gwt_def (@Q8QT.Mq4.rmrep_shadow) (@UQXM.rmrep_shadow) (Q6nq.gwt_def (@Qe1A.Mqa.rmrep_shadow) (@UQXM.rmrep_shadow) (Q6nq.gwt_def (@Q8QT.Mq4.rmrep_groups) (@UQXM.rmrep_groups) (Q6nq.gwt_def (@Qe1A.Mqa.rmrep_groups) (@UQXM.rmrep_groups) (Q6nq.gwt_def (@Q8QT.Mq4.rmrep_globals) (@UQXM.rmrep_globals) (Q6nq.gwt_def (@Qe1A.Mqa.rmrep_globals) (@UQXM.rmrep_globals) (Q6nq.gwt_def (@Q8QT.Mq4.rmrep_ctx) (@UQXM.rmrep_ctx) (Q6nq.gwt_def (@Qe1A.Mqa.rmrep_ctx) (@UQXM.rmrep_ctx) (Q6nq.gwt_def (@Q8QT.Mq4.rmrep_areas) (@UQXM.rmrep_areas) (Q6nq.gwt_def (@Qe1A.Mqa.rmrep_areas) (@UQXM.rmrep_areas) (Q6nq.gwt_def (@Q8QT.Mq4.rmrep) (@UQXM.rmrep) (Q6nq.gwt_def (@Qe1A.Mqa.rmrep) (@UQXM.rmrep) (Q6nq.gwt_def (@Q8QT.Mq2.rmmap_anon_post) (@UC00.rmmap_anon_post) (Q6nq.gwt_def (@Qe1A.Mqa.rmmap_anon_post) (@UC00.rmmap_anon_post) (Q6nq.gwt_def (@QkTt.Mq5.rmalloc_fp) (@UDxd.rmalloc_fp) (Q6nq.gwt_def (@Qe1A.Mqa.rmalloc_fp) (@UDxd.rmalloc_fp) (Q6nq.gwt_def (@QCa8.Mq5.rimplT) (@Uv2Y.rimplT) (Q6nq.gwt_def (@Qe1A.Mqa.rimplT) (@Uv2Y.rimplT) (Q6nq.gwt_def (@Q8QT.Mq4.rgroup_rep) (@UQXM.rgroup_rep) (Q6nq.gwt_def (@Qe1A.Mqa.rgroup_rep) (@UQXM.rgroup_rep) (Q6nq.gwt_def (@QROt.Mq5.rcoreQ) (@UwoZ.rcoreQ) (Q6nq.gwt_def (@Qe1A.Mqa.rcoreQ) (@UwoZ.rcoreQ) (Q6nq.gwt_def (@QROt.Mq5.rbig_stmt) (@UwoZ.rbig_stmt) (Q6nq.gwt_def (@Qe1A.Mqa.rbig_stmt) (@UwoZ.rbig_stmt) (Q6nq.gwt_def (@QCa8.Mq5.rauxv_ok) (@Uv2Y.rauxv_ok) (Q6nq.gwt_def (@Qe1A.Mqa.rauxv_ok) (@Uv2Y.rauxv_ok) (Q6nq.gwt_def (@Q8QT.Mq4.rarea_rep) (@UQXM.rarea_rep) (Q6nq.gwt_def (@Qe1A.Mqa.rarea_rep) (@UQXM.rarea_rep) (Q6nq.gwt_def (@QCa8.Mq5.ram_post) (@Uv2Y.ram_post) (Q6nq.gwt_def (@Qe1A.Mqa.ram_post) (@Uv2Y.ram_post) (Q6nq.gwt_def (@QCa8.Mq5.ralloc_meta_stmt) (@Uv2Y.ralloc_meta_stmt) (Q6nq.gwt_def (@Qe1A.Mqa.ralloc_meta_stmt) (@Uv2Y.ralloc_meta_stmt) (Q6nq.gwt_def (@QCa8.Mq5.ralloc_fp) (@Uv2Y.ralloc_fp) (Q6nq.gwt_def (@Qe1A.Mqa.ralloc_fp) (@Uv2Y.ralloc_fp) Q6nq.gwt_nil)))))))))))))))))))))))))))))))))))))))))))))))).
#[using="Type"] Lemma rmrep_ext : ltac2:(Q6nq.ty2 'GwI.segs '(@Qe1A.Mqa.rmrep_ext) [[@gw_eq_rmrep__3; @gw_eq_rmrep__2; @gw_eq_rmrep]] '(@nil Z) 'gwt_X).
Proof. ltac2:(GwEq.gw_rw [[@gw_eq_rmrep__3; @gw_eq_rmrep__2; @gw_eq_rmrep]]); first [GwApply2.gw_by_name2 GwI.segs (@Qe1A.Mqa.rmrep_ext) | autorewrite with gw_eqs; GwApply2.gw_by_name2 GwI.segs (@Qe1A.Mqa.rmrep_ext)]. Qed.

Section FINAL.
Variables (st3 : mstate) (g : aptr) (rid : N) (xa n c : Z).
Hypothesis G0 : get_meta_rec st3 g = meta0.
Hypothesis GN : (s_groups st3) !! (rid, 0) = None.
Hypothesis HC : c_mmap_counter (ctx st3) = c.
Hypothesis NR : 0 <= n < 2^63.
Hypothesis RR : (s_regions st3) !! rid = Some (mkRegion RKGroup xa (n + IB + UNIT)).

Let stF := big_final st3 g rid n.
Let stM := big_st st3 g rid n (u32 (c + 1)).

#[using="G0"] Lemma rbf_meta : get_meta_rec stF g = big_meta rid n.
Proof. first [GwApply2.gw_by_name2 GwI.segs (@Qe1A.Mqa.rbf_meta) | autorewrite with gw_eqs; GwApply2.gw_by_name2 GwI.segs (@Qe1A.Mqa.rbf_meta)]. Qed.

#[using="Type"] Lemma rbf_meta_other q : q <> g -> get_meta_rec stF q = get_meta_rec st3 q.
Proof. first [GwApply2.gw_by_name2 GwI.segs (@Qe1A.Mqa.rbf_meta_other) | autorewrite with gw_eqs; GwApply2.gw_by_name2 GwI.segs (@Qe1A.Mqa.rbf_meta_other)]. Qed.

#[using="Type"] Lemma rbm_meta : get_meta_rec stM g = big_meta rid n.
Proof. first [GwApply2.gw_by_name2 GwI.segs (@Qe1A.Mqa.rbm_meta) | autorewrite with gw_eqs; GwApply2.gw_by_name2 GwI.segs (@Qe1A.Mqa.rbm_meta)]. Qed.
#[using="Type"] Lemma rbm_meta_other q : q <> g -> get_meta_rec stM q = get_meta_rec st3 q.
Proof. first [GwApply2.gw_by_name2 GwI.segs (@Qe1A.Mqa.rbm_meta_other) | autorewrite with gw_eqs; GwApply2.gw_by_name2 GwI.segs (@Qe1A.Mqa.rbm_meta_other)]. Qed.

#[using="Type"] Lemma rbf_regions : s_regions stF = s_regions st3. Proof. first [GwApply2.gw_by_name2 GwI.segs (@Qe1A.Mqa.rbf_regions) | autorewrite with gw_eqs; GwApply2.gw_by_name2 GwI.segs (@Qe1A.Mqa.rbf_regions)]. Qed.
#[using="Type"] Lemma rbf_areas : s_areas stF = s_areas st3. Proof. first [GwApply2.gw_by_name2 GwI.segs (@Qe1A.Mqa.rbf_areas) | autorewrite with gw_eqs; GwApply2.gw_by_name2 GwI.segs (@Qe1A.Mqa.rbf_areas)]. Qed.
#[using="Type"] Lemma rbf_reserved : s_reserved stF = s_reserved st3. Proof. first [GwApply2.gw_by_name2 GwI.segs (@Qe1A.Mqa.rbf_reserved) | autorewrite with gw_eqs; GwApply2.gw_by_name2 GwI.segs (@Qe1A.Mqa.rbf_reserved)]. Qed.
#[using="Type"] Lemma rbf_next : s_next_rid stF = s_next_rid st3. Proof. first [GwApply2.gw_by_name2 GwI.segs (@Qe1A.Mqa.rbf_next) | autorewrite with gw_eqs; GwApply2.gw_by_name2 GwI.segs (@Qe1A.Mqa.rbf_next)]. Qed.
#[using="GN"] Lemma rbf_groups : s_groups stF = <[(rid, 0) := mkGhdr (Some g) 0]> (s_groups st3).
Proof. first [GwApply2.gw_by_name2 GwI.segs (@Qe1A.Mqa.rbf_groups) | autorewrite with gw_eqs; GwApply2.gw_by_name2 GwI.segs (@Qe1A.Mqa.rbf_groups)]. Qed.
#[using="Type"] Lemma rbm_groups : s_groups stM = <[(rid, 0) := mkGhdr (Some g) 0]> (s_groups st3).
Proof. first [GwApply2.gw_by_name2 GwI.segs (@Qe1A.Mqa.rbm_groups) | autorewrite with gw_eqs; GwApply2.gw_by_name2 GwI.segs (@Qe1A.Mqa.rbm_groups)]. Qed.
#[using="Type"] Lemma rbf_shadow q : get_shadow stF q = get_shadow stM q.
Proof. first [GwApply2.gw_by_name2 GwI.segs (@Qe1A.Mqa.rbf_shadow) | autorewrite with gw_eqs; GwApply2.gw_by_name2 GwI.segs (@Qe1A.Mqa.rbf_shadow)]. Qed.
#[using="Type"] Lemma rbf_shadow_other q : q <> rid -> get_shadow stF q = get_shadow st3 q.
Proof. first [GwApply2.gw_by_name2 GwI.segs (@Qe1A.Mqa.rbf_shadow_other) | autorewrite with gw_eqs; GwApply2.gw_by_name2 GwI.segs (@Qe1A.Mqa.rbf_shadow_other)]. Qed.
#[using="HC"] Lemma rbf_ctx : ctx stF = ctx stM.
Proof. first [GwApply2.gw_by_name2 GwI.segs (@Qe1A.Mqa.rbf_ctx) | autorewrite with gw_eqs; GwApply2.gw_by_name2 GwI.segs (@Qe1A.Mqa.rbf_ctx)]. Qed.
#[using="HC stM"] Lemma rbf_counter : c_mmap_counter (ctx stF) = u32 (c + 1).
Proof. first [GwApply2.gw_by_name2 GwI.segs (@Qe1A.Mqa.rbf_counter) | autorewrite with gw_eqs; GwApply2.gw_by_name2 GwI.segs (@Qe1A.Mqa.rbf_counter)]. Qed.

#[using="G0 GN HC"] Lemma rmrep_big_final m : rmrep stM m -> rmrep stF m.
Proof. ltac2:(GwEq.gw_rw [[@gw_eq_rmrep__3; @gw_eq_rmrep__2; @gw_eq_rmrep]]); first [GwApply2.gw_by_name2 GwI.segs (@Qe1A.Mqa.rmrep_big_final) | autorewrite with gw_eqs; GwApply2.gw_by_name2 GwI.segs (@Qe1A.Mqa.rmrep_big_final)]. Qed.

#[using="Type"] Lemma rticks_ok_big_final : ticks_ok stM -> ticks_ok stF.
Proof. first [GwApply2.gw_by_name2 GwI.segs (@Qe1A.Mqa.rticks_ok_big_final) | autorewrite with gw_eqs; GwApply2.gw_by_name2 GwI.segs (@Qe1A.Mqa.rticks_ok_big_final)]. Qed.

#[using="NR"] Lemma rbf_stride : get_stride (big_meta rid n) = big_ml n * 4096 - 16.
Proof. first [GwApply2.gw_by_name2 GwI.segs (@Qe1A.Mqa.rbf_stride) | autorewrite with gw_eqs; GwApply2.gw_by_name2 GwI.segs (@Qe1A.Mqa.rbf_stride)]. Qed.

#[using="Type"] Lemma rbf_slots : s_slots stF = <[(rid, 16) := (g, 0)]> (s_slots st3).
Proof. first [GwApply2.gw_by_name2 GwI.segs (@Qe1A.Mqa.rbf_slots) | autorewrite with gw_eqs; GwApply2.gw_by_name2 GwI.segs (@Qe1A.Mqa.rbf_slots)]. Qed.
End FINAL.

#[using="Type"] Lemma rrepfoot_where2 st m a : rmrep st m -> rrepfoot st a ->
a < alloc_ceiling /\ (RCTX <= a < RCTX + 928 \/ RMLOCK <= a < RMLOCK + 4 \/ RLIBC <= a < RLIBC + 0x38 \/ RGOT_SSP <= a < RGOT_SSP + 8 \/ RSSP_GUARD <= a < RSSP_GUARD + 8 \/ a < 0x10000 \/ 0x99000 <= a).
Proof. ltac2:(GwEq.gw_rw [[@gw_eq_rmrep__3; @gw_eq_rmrep__2; @gw_eq_rmrep]; [@gw_eq_rrepfoot__3; @gw_eq_rrepfoot__2; @gw_eq_rrepfoot]]); first [GwApply2.gw_by_name2 GwI.segs (@Qe1A.Mqa.rrepfoot_where2) | autorewrite with gw_eqs; GwApply2.gw_by_name2 GwI.segs (@Qe1A.Mqa.rrepfoot_where2)]. Qed.

#[using="Type"] Lemma rwrapper_munch_keeps : ltac2:(Q6nq.ty2 'GwI.segs '(@Qe1A.Mqa.rwrapper_munch_keeps) [[@gw_eq_rmrep__3; @gw_eq_rmrep__2; @gw_eq_rmrep]] '([(-80); 490332]%Z : list Z) '(Q6nq.gwt_unf (@RERRNO) (Q6nq.gwt_pat (@RATP) (@RATP) (Q6nq.gwt_hdr GwI.RATP (@RATP) gwt_X)))).
Proof. ltac2:(GwEq.gw_rw [[@gw_eq_rmrep__3; @gw_eq_rmrep__2; @gw_eq_rmrep]]); first [GwApply2.gw_by_name2 GwI.segs (@Qe1A.Mqa.rwrapper_munch_keeps) | autorewrite with gw_eqs; GwApply2.gw_by_name2 GwI.segs (@Qe1A.Mqa.rwrapper_munch_keeps)]. Qed.

#[using="Type"] Lemma rpres_except_of_munch_nw C W m m' :
munch W m m' -> (forall a, 0 <= a < 2^64 -> ~ C a -> outside W a) -> rpres_except C m m'.
Proof. ltac2:(GwEq.gw_rw [[@gw_eq_W__3; @gw_eq_W__2; @gw_eq_W]; [@gw_eq_rpres_except__3; @gw_eq_rpres_except__2; @gw_eq_rpres_except]]); first [GwApply2.gw_by_name2 GwI.segs (@Qe1A.Mqa.rpres_except_of_munch_nw) | autorewrite with gw_eqs; GwApply2.gw_by_name2 GwI.segs (@Qe1A.Mqa.rpres_except_of_munch_nw)]. Qed.

#[using="Type"] Lemma rfp_below_ceiling : ltac2:(Q6nq.ty2 'GwI.segs '(@Qe1A.Mqa.rfp_below_ceiling) [[@gw_eq_ralloc_fp__3; @gw_eq_ralloc_fp__2; @gw_eq_ralloc_fp]; [@gw_eq_rmrep__3; @gw_eq_rmrep__2; @gw_eq_rmrep]] '(@nil Z) 'gwt_X).
Proof. ltac2:(GwEq.gw_rw [[@gw_eq_ralloc_fp__3; @gw_eq_ralloc_fp__2; @gw_eq_ralloc_fp]; [@gw_eq_rmrep__3; @gw_eq_rmrep__2; @gw_eq_rmrep]]); first [GwApply2.gw_by_name2 GwI.segs (@Qe1A.Mqa.rfp_below_ceiling) | autorewrite with gw_eqs; GwApply2.gw_by_name2 GwI.segs (@Qe1A.Mqa.rfp_below_ceiling)]. Qed.

#[using="Type"] Lemma rbig_stride n rid : 0 <= n < 2^63 -> get_stride (big_meta rid n) = round_up_pg (n + IB + UNIT) - 16.
Proof. first [GwApply2.gw_by_name2 GwI.segs (@Qe1A.Mqa.rbig_stride) | autorewrite with gw_eqs; GwApply2.gw_by_name2 GwI.segs (@Qe1A.Mqa.rbig_stride)]. Qed.

#[using="Type"] Lemma rregion_facts_hi : ltac2:(Q6nq.ty2 'GwI.segs '(@Qe1A.Mqa.rregion_facts_hi) [[@gw_eq_rmrep__3; @gw_eq_rmrep__2; @gw_eq_rmrep]] '([417792; 626688]%Z : list Z) '(Q6nq.gwt_unf (@RIMG_HI) (Q6nq.gwt_pat (@RIMG_HI) (@RIMG_HI) (Q6nq.gwt_hdr GwI.RIMG_HI (@RIMG_HI) gwt_X)))).
Proof. ltac2:(GwEq.gw_rw [[@gw_eq_rmrep__3; @gw_eq_rmrep__2; @gw_eq_rmrep]]); first [GwApply2.gw_by_name2 GwI.segs (@Qe1A.Mqa.rregion_facts_hi) | autorewrite with gw_eqs; GwApply2.gw_by_name2 GwI.segs (@Qe1A.Mqa.rregion_facts_hi)]. Qed.

Definition rAMP_BIG (ram_pre : mstate -> Prop) : Prop :=
forall st LB t xa n, RAREACH st LB -> MMAP_THRESHOLD <= n < 2^63 - 4097 ->
mmap_answer_ok (live_ranges (set_tick t st)) (n + IB + UNIT) xa = true -> is_err xa = false ->
ram_pre (step_seq (fst (new_region RKGroup xa (n + IB + UNIT) (set_tick t st)))).

#[using="Type"] Lemma ramp_big : rAMP_BIG (am_pre_g ref_reserved rc_secret).
Proof. first [GwApply2.gw_by_name2 GwI.segs (@Qe1A.Mqa.ramp_big) | autorewrite with gw_eqs; GwApply2.gw_by_name2 GwI.segs (@Qe1A.Mqa.ramp_big)]. Qed.

Section BIG.
Variable ram_pre : mstate -> Prop.
Hypothesis AM : ralloc_meta_stmt ram_pre.
Hypothesis AMP : rAMP_BIG ram_pre.

#[using="ram_pre AM AMP"] Lemma rbig_spec : rbig_stmt.
Proof. ltac2:(GwEq.gw_rw [[@gw_eq_rbig_stmt__3; @gw_eq_rbig_stmt__2; @gw_eq_rbig_stmt]]); first [GwApply2.gw_by_name2 GwI.segs (@Qe1A.Mqa.rbig_spec) | autorewrite with gw_eqs; GwApply2.gw_by_name2 GwI.segs (@Qe1A.Mqa.rbig_spec)]. Qed.
End BIG.

End RC__1.
