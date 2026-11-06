(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)


From OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib Require CodeAt StepGen GwInst GwEq GwEqH GwApply GwApply2. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q6nq.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qe1A.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QKNz.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qy8Z.

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
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q2qa.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q2qa.Mq1. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qy5Y.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qy5Y.Mq1. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q4J3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q4J3.Mq1. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QytA.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QytA. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qnxq.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qnxq. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QJE4.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QJE4.Mq4. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qy5Y.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qy5Y.Mq5. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QWTl.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QWTl.Mq5. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qy5Y.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qy5Y.Mq4. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q4J3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q4J3.Mq3.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QZAi.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QZAi.Mq2. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QUZl.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QUZl. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q7S0.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q7S0.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Ql2m.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Ql2m.Mq3. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QGeV.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QGeV.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QLsg.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QLsg. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QDUx.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QDUx.Mq8. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q9Ay.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q9Ay.Mqa. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QXxF.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QXxF.Mq3. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QDUx.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QDUx.Mq9. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q6y7.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q6y7.Mq2. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QDUx.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QDUx.Mq7. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q3o5.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q3o5. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q8P7.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q8P7. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QTyG.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QTyG.Mq1.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QQXM.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QQXM. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qv2Y.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qv2Y. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QpkF.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QpkF. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QIMz.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QIMz. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qn7h.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qn7h. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q8eV.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q8eV. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QC00.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QC00. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q8FW.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q8FW. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QDxd_c1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QDxd_c1. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QiOj.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QiOj. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QJOB.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QJOB. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QWfR.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QWfR. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QznK.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QznK. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q7Ti.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q7Ti. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QAr0.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QAr0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QwoZ.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QwoZ. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QxSL.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QxSL. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QYQW.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QYQW.
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
Definition base := 0x510dc%Z.
Definition w_11 := 0xcd1fd0ef%Z.
Definition w_26 := 0x00045597%Z.
Definition w_27 := 0xa458493%Z.
Definition w_37 := 0x314010ef%Z.
Definition w_40 := 0x00045517%Z.
Definition w_41 := 0xf8754503%Z.
Definition w_43 := 0x00045517%Z.
Definition w_44 := 0x06050513%Z.
Definition w_45 := 0x6380d0ef%Z.
Definition w_57 := 0xfffc5617%Z.
Definition w_59 := 0x33860993%Z.
Definition w_85 := 0xfffc5617%Z.
Definition w_90 := 0x2e860593%Z.
Definition w_125 := 0x00045517%Z.
Definition w_126 := 0xe3354503%Z.
Definition w_128 := 0x00045517%Z.
Definition w_129 := 0xf0c50513%Z.
Definition w_130 := 0x4e40d0ef%Z.
Definition w_147 := 0x00045517%Z.
Definition w_148 := 0xec050513%Z.
Definition w_149 := 0x7200d0ef%Z.
Definition w_152 := 0x350010ef%Z.
Definition w_203 := 0x6480d0ef%Z.
Definition w_216 := 0x00045517%Z.
Definition w_217 := 0xdac50513%Z.
Definition w_218 := 0x60c0d0ef%Z.
Definition hi_26 := (Z_to_bv 20 69).
Definition hi_40 := (Z_to_bv 20 69).
Definition hi_43 := (Z_to_bv 20 69).
Definition hi_57 := (Z_to_bv 20 1048517).
Definition hi_85 := (Z_to_bv 20 1048517).
Definition hi_125 := (Z_to_bv 20 69).
Definition hi_128 := (Z_to_bv 20 69).
Definition hi_147 := (Z_to_bv 20 69).
Definition hi_216 := (Z_to_bv 20 69).
Definition lo_27 := (Z_to_bv 12 164).
Definition lo_41 := (Z_to_bv 12 3975).
Definition lo_44 := (Z_to_bv 12 96).
Definition lo_59 := (Z_to_bv 12 824).
Definition lo_90 := (Z_to_bv 12 744).
Definition lo_126 := (Z_to_bv 12 3635).
Definition lo_129 := (Z_to_bv 12 3852).
Definition lo_148 := (Z_to_bv 12 3776).
Definition lo_217 := (Z_to_bv 12 3500).
Definition joff_11 := (Z_to_bv 21 2088144).
Definition joff_37 := (Z_to_bv 21 4884).
Definition joff_45 := (Z_to_bv 21 54840).
Definition joff_130 := (Z_to_bv 21 54500).
Definition joff_149 := (Z_to_bv 21 55072).
Definition joff_152 := (Z_to_bv 21 4944).
Definition joff_203 := (Z_to_bv 21 54856).
Definition joff_218 := (Z_to_bv 21 54796).
Definition RATP := QKNz.RATP.
Definition RDEBRUIJN := QKNz.RDEBRUIJN.
Definition RGOT_SSP := QKNz.RGOT_SSP.
Definition RIMG_HI := QKNz.RIMG_HI.
Definition RDATA_LO := QKNz.RDATA_LO.
Definition gw_RTEXT_LO := ltac:(let gw_v_ := eval cbv in (fst (nth 1 QKNz.ref_reserved (0%Z, 0%Z))) in exact gw_v_).
Definition gw_RDATA2_LO := ltac:(let gw_v_ := eval cbv in (fst (nth 3 QKNz.ref_reserved (0%Z, 0%Z))) in exact gw_v_).
Definition ref_reserved := QKNz.ref_reserved.
Definition rerrno_loc_entry := QKNz.rerrno_loc_entry.
Definition rsysret_entry := QKNz.rsysret_entry.
Definition rvm_wait_entry := QKNz.rvm_wait_entry.
Definition rlock_entry := QKNz.rlock_entry.
Definition runlock_entry := QKNz.runlock_entry.
Lemma CODE : CodeAt.code_at rsegs 0x510dc (Qy8Z.Mq7.malloc_code 0xcd1fd0ef%Z 0x00045597%Z 0xa458493%Z 0x314010ef%Z 0x00045517%Z 0xf8754503%Z 0x00045517%Z 0x06050513%Z 0x6380d0ef%Z 0xfffc5617%Z 0x33860993%Z 0xfffc5617%Z 0x2e860593%Z 0x00045517%Z 0xe3354503%Z 0x00045517%Z 0xf0c50513%Z 0x4e40d0ef%Z 0x00045517%Z 0xec050513%Z 0x7200d0ef%Z 0x350010ef%Z 0x6480d0ef%Z 0x00045517%Z 0xdac50513%Z 0x60c0d0ef%Z).  Proof. StepGen.code_at_vm. Qed.
Lemma BASE4 : (0x510dc mod 4 = 0)%Z.  Proof. reflexivity. Qed.
Lemma BASER : (0 <= 0x510dc /\ 0x510dc + 880 <= 2^40)%Z.  Proof. vm_compute. split; discriminate. Qed.
Lemma CODE_rerrno_loc_entry : CodeAt.code_at rsegs rerrno_loc_entry Qe1A.Mqa.errno_loc_code.  Proof. StepGen.code_at_vm. Qed.
Definition ref_find_segment_none := @QKNz.ref_find_segment_none.
Definition ref_ro_addr_false := @QKNz.ref_ro_addr_false.
Definition ref_memory_read_none := @QKNz.ref_memory_read_none.
Definition ref_wview_overlay := @QKNz.ref_wview_overlay.
Definition ref_seg_rom_none := @QKNz.ref_seg_rom_none.
Definition ref_mrd_overlay := @QKNz.ref_mrd_overlay.
Definition rmunmap_spec := ltac:(pose proof (@rmunmap_spec) as gw_h_; ltac2:(GwEqH.gw_rw_in @gw_h_ [[@gw_eq_rmunmap_post__3; @gw_eq_rmunmap_post__2; @gw_eq_rmunmap_post]; [@gw_eq_rmprotect_post__3; @gw_eq_rmprotect_post__2; @gw_eq_rmprotect_post]; [@gw_eq_rmmap_fixed_post__3; @gw_eq_rmmap_fixed_post__2; @gw_eq_rmmap_fixed_post]]); exact gw_h_).
Definition rmmap_anon_spec := ltac:(pose proof (@rmmap_anon_spec) as gw_h_; ltac2:(GwEqH.gw_rw_in @gw_h_ [[@gw_eq_rmunmap_post__3; @gw_eq_rmunmap_post__2; @gw_eq_rmunmap_post]; [@gw_eq_rmprotect_post__3; @gw_eq_rmprotect_post__2; @gw_eq_rmprotect_post]; [@gw_eq_rmmap_fixed_post__3; @gw_eq_rmmap_fixed_post__2; @gw_eq_rmmap_fixed_post]]); exact gw_h_).
Definition runlock_spec := ltac:(pose proof (@runlock_spec) as gw_h_; ltac2:(GwEqH.gw_rw_in @gw_h_ [[@gw_eq_rget_meta_post__3; @gw_eq_rget_meta_post__2; @gw_eq_rget_meta_post]; [@gw_eq_runlock_post__3; @gw_eq_runlock_post__2; @gw_eq_runlock_post]]); exact gw_h_).
Definition land_m4096 := ltac:(pose proof (@land_m4096) as gw_h_; ltac2:(GwEqH.gw_rw_in @gw_h_ [[@gw_eq_renframe_tail_mem__3; @gw_eq_renframe_tail_mem__2; @gw_eq_renframe_tail_mem]; [@gw_eq_ren3_post__3; @gw_eq_ren3_post__2; @gw_eq_ren3_post]; [@gw_eq_renframe_off_mem__3; @gw_eq_renframe_off_mem__2; @gw_eq_renframe_off_mem]]); exact gw_h_).
Lemma ROM_reservedZ : ltac2:(GwEq.gw_fact_ty 'segs '(@Qe1A.Mqa.gw_all) @ROM_reservedZ). Proof. first [ apply QWxq_c1.Mq0.ro_bytes_b_sound; vm_compute; reflexivity | GwApply.gw_side ]. Qed.
End GwI.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

Local Definition gwt_X : unit := (Q6nq.gwt_def (@Qe1A.Mqa.runlock_post) (@QpkF.runlock_post) (Q6nq.gwt_def (@QCa8.Mq4.runlock_post) (@QpkF.runlock_post) (Q6nq.gwt_def (@Q8QT.Mq4.rshadow_rep) (@QQXM.rshadow_rep) (Q6nq.gwt_def (@Qe1A.Mqa.rshadow_rep) (@QQXM.rshadow_rep) (Q6nq.gwt_def (@QQRC.Mq7.rseq_post) (@QYQW.rseq_post) (Q6nq.gwt_def (@Qe1A.Mqa.rseq_post) (@QYQW.rseq_post) (Q6nq.gwt_def (@QDXD.Mq2.rrepfoot) (@QIMz.rrepfoot) (Q6nq.gwt_def (@Qe1A.Mqa.rrepfoot) (@QIMz.rrepfoot) (Q6nq.gwt_def (@Q8QT.Mq4.rregions_wf) (@QQXM.rregions_wf) (Q6nq.gwt_def (@Qe1A.Mqa.rregions_wf) (@QQXM.rregions_wf) (Q6nq.gwt_def (@QCa8.Mq5.rpres_except) (@Qv2Y.rpres_except) (Q6nq.gwt_def (@Qe1A.Mqa.rpres_except) (@Qv2Y.rpres_except) (Q6nq.gwt_def (@Q8QT.Mq2.rmunmap_post) (@QC00.rmunmap_post) (Q6nq.gwt_def (@Qe1A.Mqa.rmunmap_post) (@QC00.rmunmap_post) (Q6nq.gwt_def (@Q8QT.Mq4.rmrep_shadow) (@QQXM.rmrep_shadow) (Q6nq.gwt_def (@Qe1A.Mqa.rmrep_shadow) (@QQXM.rmrep_shadow) (Q6nq.gwt_def (@Q8QT.Mq4.rmrep_groups) (@QQXM.rmrep_groups) (Q6nq.gwt_def (@Qe1A.Mqa.rmrep_groups) (@QQXM.rmrep_groups) (Q6nq.gwt_def (@Q8QT.Mq4.rmrep_globals) (@QQXM.rmrep_globals) (Q6nq.gwt_def (@Qe1A.Mqa.rmrep_globals) (@QQXM.rmrep_globals) (Q6nq.gwt_def (@Q8QT.Mq4.rmrep_ctx) (@QQXM.rmrep_ctx) (Q6nq.gwt_def (@Qe1A.Mqa.rmrep_ctx) (@QQXM.rmrep_ctx) (Q6nq.gwt_def (@Q8QT.Mq4.rmrep_areas) (@QQXM.rmrep_areas) (Q6nq.gwt_def (@Qe1A.Mqa.rmrep_areas) (@QQXM.rmrep_areas) (Q6nq.gwt_def (@Q8QT.Mq4.rmrep) (@QQXM.rmrep) (Q6nq.gwt_def (@Qe1A.Mqa.rmrep) (@QQXM.rmrep) (Q6nq.gwt_def (@Q8QT.Mq2.rmmap_anon_post) (@QC00.rmmap_anon_post) (Q6nq.gwt_def (@Qe1A.Mqa.rmmap_anon_post) (@QC00.rmmap_anon_post) (Q6nq.gwt_def (@QkTt.Mq5.rmalloc_fp) (@QDxd_c1.rmalloc_fp) (Q6nq.gwt_def (@Qe1A.Mqa.rmalloc_fp) (@QDxd_c1.rmalloc_fp) (Q6nq.gwt_def (@QCa8.Mq5.rimplT) (@Qv2Y.rimplT) (Q6nq.gwt_def (@Qe1A.Mqa.rimplT) (@Qv2Y.rimplT) (Q6nq.gwt_def (@Q8QT.Mq4.rgroup_rep) (@QQXM.rgroup_rep) (Q6nq.gwt_def (@Qe1A.Mqa.rgroup_rep) (@QQXM.rgroup_rep) (Q6nq.gwt_def (@QROt.Mq5.rcoreQ) (@QwoZ.rcoreQ) (Q6nq.gwt_def (@Qe1A.Mqa.rcoreQ) (@QwoZ.rcoreQ) (Q6nq.gwt_def (@QROt.Mq5.rbig_stmt) (@QwoZ.rbig_stmt) (Q6nq.gwt_def (@Qe1A.Mqa.rbig_stmt) (@QwoZ.rbig_stmt) (Q6nq.gwt_def (@QCa8.Mq5.rauxv_ok) (@Qv2Y.rauxv_ok) (Q6nq.gwt_def (@Qe1A.Mqa.rauxv_ok) (@Qv2Y.rauxv_ok) (Q6nq.gwt_def (@Q8QT.Mq4.rarea_rep) (@QQXM.rarea_rep) (Q6nq.gwt_def (@Qe1A.Mqa.rarea_rep) (@QQXM.rarea_rep) (Q6nq.gwt_def (@QCa8.Mq5.ram_post) (@Qv2Y.ram_post) (Q6nq.gwt_def (@Qe1A.Mqa.ram_post) (@Qv2Y.ram_post) (Q6nq.gwt_def (@QCa8.Mq5.ralloc_meta_stmt) (@Qv2Y.ralloc_meta_stmt) (Q6nq.gwt_def (@Qe1A.Mqa.ralloc_meta_stmt) (@Qv2Y.ralloc_meta_stmt) (Q6nq.gwt_def (@QCa8.Mq5.ralloc_fp) (@Qv2Y.ralloc_fp) (Q6nq.gwt_def (@Qe1A.Mqa.ralloc_fp) (@Qv2Y.ralloc_fp) Q6nq.gwt_nil)))))))))))))))))))))))))))))))))))))))))))))))).
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
a < alloc_ceiling /\ (RCTX <= a < RCTX + 928 \/ RMLOCK <= a < RMLOCK + 4 \/ RLIBC <= a < RLIBC + 0x38 \/ RGOT_SSP <= a < RGOT_SSP + 8 \/ RSSP_GUARD <= a < RSSP_GUARD + 8 \/ a < 0x10000 \/ 0x97000 <= a).
Proof. ltac2:(GwEq.gw_rw [[@gw_eq_rmrep__3; @gw_eq_rmrep__2; @gw_eq_rmrep]; [@gw_eq_rrepfoot__3; @gw_eq_rrepfoot__2; @gw_eq_rrepfoot]]); first [GwApply2.gw_by_name2 GwI.segs (@Qe1A.Mqa.rrepfoot_where2) | autorewrite with gw_eqs; GwApply2.gw_by_name2 GwI.segs (@Qe1A.Mqa.rrepfoot_where2)]. Qed.

#[using="Type"] Lemma rwrapper_munch_keeps : ltac2:(Q6nq.ty2 'GwI.segs '(@Qe1A.Mqa.rwrapper_munch_keeps) [[@gw_eq_rmrep__3; @gw_eq_rmrep__2; @gw_eq_rmrep]] '([(-80); 482764]%Z : list Z) '(Q6nq.gwt_unf (@RERRNO) (Q6nq.gwt_pat (@RATP) (@RATP) (Q6nq.gwt_hdr GwI.RATP (@RATP) gwt_X)))).
Proof. ltac2:(GwEq.gw_rw [[@gw_eq_rmrep__3; @gw_eq_rmrep__2; @gw_eq_rmrep]]); first [GwApply2.gw_by_name2 GwI.segs (@Qe1A.Mqa.rwrapper_munch_keeps) | autorewrite with gw_eqs; GwApply2.gw_by_name2 GwI.segs (@Qe1A.Mqa.rwrapper_munch_keeps)]. Qed.

#[using="Type"] Lemma rpres_except_of_munch_nw C W m m' :
munch W m m' -> (forall a, 0 <= a < 2^64 -> ~ C a -> outside W a) -> rpres_except C m m'.
Proof. ltac2:(GwEq.gw_rw [[@gw_eq_W__3; @gw_eq_W__2; @gw_eq_W]; [@gw_eq_rpres_except__3; @gw_eq_rpres_except__2; @gw_eq_rpres_except]]); first [GwApply2.gw_by_name2 GwI.segs (@Qe1A.Mqa.rpres_except_of_munch_nw) | autorewrite with gw_eqs; GwApply2.gw_by_name2 GwI.segs (@Qe1A.Mqa.rpres_except_of_munch_nw)]. Qed.

#[using="Type"] Lemma rfp_below_ceiling : ltac2:(Q6nq.ty2 'GwI.segs '(@Qe1A.Mqa.rfp_below_ceiling) [[@gw_eq_ralloc_fp__3; @gw_eq_ralloc_fp__2; @gw_eq_ralloc_fp]; [@gw_eq_rmrep__3; @gw_eq_rmrep__2; @gw_eq_rmrep]] '(@nil Z) 'gwt_X).
Proof. ltac2:(GwEq.gw_rw [[@gw_eq_ralloc_fp__3; @gw_eq_ralloc_fp__2; @gw_eq_ralloc_fp]; [@gw_eq_rmrep__3; @gw_eq_rmrep__2; @gw_eq_rmrep]]); first [GwApply2.gw_by_name2 GwI.segs (@Qe1A.Mqa.rfp_below_ceiling) | autorewrite with gw_eqs; GwApply2.gw_by_name2 GwI.segs (@Qe1A.Mqa.rfp_below_ceiling)]. Qed.

#[using="Type"] Lemma rbig_stride n rid : 0 <= n < 2^63 -> get_stride (big_meta rid n) = round_up_pg (n + IB + UNIT) - 16.
Proof. first [GwApply2.gw_by_name2 GwI.segs (@Qe1A.Mqa.rbig_stride) | autorewrite with gw_eqs; GwApply2.gw_by_name2 GwI.segs (@Qe1A.Mqa.rbig_stride)]. Qed.

#[using="Type"] Lemma rregion_facts_hi : ltac2:(Q6nq.ty2 'GwI.segs '(@Qe1A.Mqa.rregion_facts_hi) [[@gw_eq_rmrep__3; @gw_eq_rmrep__2; @gw_eq_rmrep]] '([409600; 618496]%Z : list Z) '(Q6nq.gwt_unf (@RIMG_HI) (Q6nq.gwt_pat (@RIMG_HI) (@RIMG_HI) (Q6nq.gwt_hdr GwI.RIMG_HI (@RIMG_HI) gwt_X)))).
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
