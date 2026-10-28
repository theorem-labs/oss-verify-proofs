(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)


From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib Require CodeAt StepGen GwInst GwEq GwEqH GwApply GwApply2. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Q6nq.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Q5m9.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UKNz.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UUSO.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QQRC.

From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run Fs.
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
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QWTl.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QWTl.Mq5.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require U4l4.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import U4l4.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Q2qa.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q2qa.Mq1. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QytA.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QytA. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QlQE.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QlQE. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QFkE.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QFkE. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Q4J3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q4J3.Mq4. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QPjm.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QPjm.Mq0. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Q4J3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q4J3.Mq2. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Qy5Y.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qy5Y.Mq6. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QPjm.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QPjm.Mq2. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QPjm.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QPjm.Mq3.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QZAi.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QZAi.Mq2. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QUZl.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QUZl. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Q7S0.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q7S0.Mq0. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Ql2m.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Ql2m.Mq3. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QGeV.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QGeV.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QYTG.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QJE4.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QJE4.Mq0. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QJE4.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QJE4.Mq1. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QDUx.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QDUx.Mq3. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QWTl.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QWTl.Mq1. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QWTl.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QWTl.Mq2. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QWTl.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QWTl.Mq3. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QDUx.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QDUx.Mq2. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Q9Ay.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q9Ay.Mq9. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QXxF.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QXxF. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QBeb.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QBeb. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Q6y7.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q6y7.Mq1.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UQXM.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UQXM. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require Uv2Y.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Uv2Y. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UIMz.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UIMz. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require Un7h.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Un7h. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require U8eV.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import U8eV. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UC00.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UC00. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UxSL.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UxSL. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UlEO.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UlEO.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UNR4.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UNR4. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UWzX.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UWzX. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UqSq.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UqSq. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UA2f.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UA2f. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UMTV.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UMTV. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require U4Oe.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import U4Oe. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UGSi.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UGSi. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UbdL.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UbdL. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UC1t.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UC1t. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UeMs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UeMs.
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
Definition rsysret_entry := UKNz.rsysret_entry.
Definition rvm_wait_entry := UKNz.rvm_wait_entry.
Lemma CODE : CodeAt.code_at rsegs 0x52b8c (QQRC.Mq5.alloc_meta_code 0x00013517%Z 0xe2853903%Z 0x00045597%Z 0x3c458993%Z 0x00045597%Z 0x2cc58413%Z 0x0350c0ef%Z 0x4f8010ef%Z 0x4a0010ef%Z 0x4b8010ef%Z 0xd19fd0ef%Z 0x9c4fe0ef%Z).  Proof. StepGen.code_at_vm. Qed.
Lemma BASE4 : (0x52b8c mod 4 = 0)%Z.  Proof. reflexivity. Qed.
Lemma BASER : (0 <= 0x52b8c /\ 0x52b8c + 728 <= 2^40)%Z.  Proof. vm_compute. split; discriminate. Qed.
Lemma CODE_rerrno_loc_entry : CodeAt.code_at rsegs rerrno_loc_entry Q5m9.Mq9.errno_loc_code.  Proof. StepGen.code_at_vm. Qed.
Definition ref_find_segment_none := @UKNz.ref_find_segment_none.
Definition ref_ro_addr_false := @UKNz.ref_ro_addr_false.
Definition ref_memory_read_none := @UKNz.ref_memory_read_none.
Definition ref_wview_overlay := @UKNz.ref_wview_overlay.
Definition ref_seg_rom_none := @UKNz.ref_seg_rom_none.
Definition ref_mrd_overlay := @UKNz.ref_mrd_overlay.
Definition rmprotect_spec := ltac:(pose proof (@rmprotect_spec) as gw_h_; ltac2:(GwEqH.gw_rw_in @gw_h_ [[@gw_eq_rmunmap_post__3; @gw_eq_rmunmap_post__2; @gw_eq_rmunmap_post]; [@gw_eq_rmprotect_post__3; @gw_eq_rmprotect_post__2; @gw_eq_rmprotect_post]; [@gw_eq_rmmap_fixed_post__3; @gw_eq_rmmap_fixed_post__2; @gw_eq_rmmap_fixed_post]]); exact gw_h_).
Definition rmmap_anon_spec := ltac:(pose proof (@rmmap_anon_spec) as gw_h_; ltac2:(GwEqH.gw_rw_in @gw_h_ [[@gw_eq_rmunmap_post__3; @gw_eq_rmunmap_post__2; @gw_eq_rmunmap_post]; [@gw_eq_rmprotect_post__3; @gw_eq_rmprotect_post__2; @gw_eq_rmprotect_post]; [@gw_eq_rmmap_fixed_post__3; @gw_eq_rmmap_fixed_post__2; @gw_eq_rmmap_fixed_post]]); exact gw_h_).
Definition rmmap_fixed_spec := ltac:(pose proof (@rmmap_fixed_spec) as gw_h_; ltac2:(GwEqH.gw_rw_in @gw_h_ [[@gw_eq_rmunmap_post__3; @gw_eq_rmunmap_post__2; @gw_eq_rmunmap_post]; [@gw_eq_rmprotect_post__3; @gw_eq_rmprotect_post__2; @gw_eq_rmprotect_post]; [@gw_eq_rmmap_fixed_post__3; @gw_eq_rmmap_fixed_post__2; @gw_eq_rmmap_fixed_post]]); exact gw_h_).
Definition rconc_meta_inj := @UUSO.rconc_meta_inj.
Definition memcpy_spec := @memcpy_spec.
Lemma RNG_RATP : ltac2:(GwEq.gw_fact_ty 'segs '(@Q5m9.Mq9.gw_all) @RNG_RATP). Proof. GwApply.gw_side. Qed.
Lemma LAY_lo_RATP : ltac2:(GwEq.gw_fact_ty 'segs '(@Q5m9.Mq9.gw_all) @LAY_lo_RATP). Proof. GwApply.gw_side. Qed.
Lemma LAY_hi_RATP : ltac2:(GwEq.gw_fact_ty 'segs '(@Q5m9.Mq9.gw_all) @LAY_hi_RATP). Proof. GwApply.gw_side. Qed.
Lemma LAY_lo_RGOT_SSP : ltac2:(GwEq.gw_fact_ty 'segs '(@Q5m9.Mq9.gw_all) @LAY_lo_RGOT_SSP). Proof. GwApply.gw_side. Qed.
Lemma LAY_hi_RGOT_SSP : ltac2:(GwEq.gw_fact_ty 'segs '(@Q5m9.Mq9.gw_all) @LAY_hi_RGOT_SSP). Proof. GwApply.gw_side. Qed.
Lemma LAY_win_0 : ltac2:(GwEq.gw_fact_ty 'segs '(@Q5m9.Mq9.gw_all) @LAY_win_0). Proof. GwApply.gw_side. Qed.
Lemma LAY_win_1 : ltac2:(GwEq.gw_fact_ty 'segs '(@Q5m9.Mq9.gw_all) @LAY_win_1). Proof. GwApply.gw_side. Qed.
Lemma LAY_win_2 : ltac2:(GwEq.gw_fact_ty 'segs '(@Q5m9.Mq9.gw_all) @LAY_win_2). Proof. GwApply.gw_side. Qed.
Lemma LAY_win_3 : ltac2:(GwEq.gw_fact_ty 'segs '(@Q5m9.Mq9.gw_all) @LAY_win_3). Proof. GwApply.gw_side. Qed.
Lemma LAY_win_4 : ltac2:(GwEq.gw_fact_ty 'segs '(@Q5m9.Mq9.gw_all) @LAY_win_4). Proof. GwApply.gw_side. Qed.
Lemma ROM_reservedZ : ltac2:(GwEq.gw_fact_ty 'segs '(@Q5m9.Mq9.gw_all) @ROM_reservedZ). Proof. first [ apply QWxq.Mq0.ro_bytes_b_sound; vm_compute; reflexivity | GwApply.gw_side ]. Qed.
Lemma LAY_ref_reserved : ltac2:(GwEq.gw_fact_ty 'segs '(@Q5m9.Mq9.gw_all) @LAY_ref_reserved). Proof. GwApply.gw_side. Qed.
End GwI.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Module A2 := QWTl.Mq5.
Module RA2 := UxSL.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

#[using="Type"] Lemma rmagree_of_pres C m m' : rpres_except C m m' -> magree C m m'.
Proof. ltac2:(GwEq.gw_rw [[@gw_eq_rpres_except__3; @gw_eq_rpres_except__2; @gw_eq_rpres_except]]); first [GwApply2.gw_by_name2 GwI.segs (@Q5m9.Mq9.rmagree_of_pres) | autorewrite with gw_eqs; GwApply2.gw_by_name2 GwI.segs (@Q5m9.Mq9.rmagree_of_pres)]. Qed.
#[using="Type"] Lemma rpres_of_magree C m m' : magree C m m' -> rpres_except C m m'.
Proof. ltac2:(GwEq.gw_rw [[@gw_eq_rpres_except__3; @gw_eq_rpres_except__2; @gw_eq_rpres_except]]); first [GwApply2.gw_by_name2 GwI.segs (@Q5m9.Mq9.rpres_of_magree) | autorewrite with gw_eqs; GwApply2.gw_by_name2 GwI.segs (@Q5m9.Mq9.rpres_of_magree)]. Qed.

Local Definition gwt_X : unit := (Q6nq.gwt_def (@Q8QT.Mq4.rshadow_rep) (@UQXM.rshadow_rep) (Q6nq.gwt_def (@Q5m9.Mq9.rshadow_rep) (@UQXM.rshadow_rep) (Q6nq.gwt_def (@QDXD.Mq2.rrepfoot) (@UIMz.rrepfoot) (Q6nq.gwt_def (@Q5m9.Mq9.rrepfoot) (@UIMz.rrepfoot) (Q6nq.gwt_def (@Q8QT.Mq4.rregions_wf) (@UQXM.rregions_wf) (Q6nq.gwt_def (@Q5m9.Mq9.rregions_wf) (@UQXM.rregions_wf) (Q6nq.gwt_def (@QCa8.Mq5.rpres_except) (@Uv2Y.rpres_except) (Q6nq.gwt_def (@Q5m9.Mq9.rpres_except) (@Uv2Y.rpres_except) (Q6nq.gwt_def (@Q8QT.Mq4.rmrep_shadow) (@UQXM.rmrep_shadow) (Q6nq.gwt_def (@Q5m9.Mq9.rmrep_shadow) (@UQXM.rmrep_shadow) (Q6nq.gwt_def (@Q8QT.Mq4.rmrep_groups) (@UQXM.rmrep_groups) (Q6nq.gwt_def (@Q5m9.Mq9.rmrep_groups) (@UQXM.rmrep_groups) (Q6nq.gwt_def (@Q8QT.Mq4.rmrep_globals) (@UQXM.rmrep_globals) (Q6nq.gwt_def (@Q5m9.Mq9.rmrep_globals) (@UQXM.rmrep_globals) (Q6nq.gwt_def (@Q8QT.Mq4.rmrep_ctx) (@UQXM.rmrep_ctx) (Q6nq.gwt_def (@Q5m9.Mq9.rmrep_ctx) (@UQXM.rmrep_ctx) (Q6nq.gwt_def (@Q8QT.Mq4.rmrep_areas) (@UQXM.rmrep_areas) (Q6nq.gwt_def (@Q5m9.Mq9.rmrep_areas) (@UQXM.rmrep_areas) (Q6nq.gwt_def (@Q8QT.Mq4.rmrep) (@UQXM.rmrep) (Q6nq.gwt_def (@Q5m9.Mq9.rmrep) (@UQXM.rmrep) (Q6nq.gwt_def (@Q8QT.Mq2.rmprotect_post) (@UC00.rmprotect_post) (Q6nq.gwt_def (@Q5m9.Mq9.rmprotect_post) (@UC00.rmprotect_post) (Q6nq.gwt_def (@Q8QT.Mq2.rmmap_fixed_post) (@UC00.rmmap_fixed_post) (Q6nq.gwt_def (@Q5m9.Mq9.rmmap_fixed_post) (@UC00.rmmap_fixed_post) (Q6nq.gwt_def (@Q8QT.Mq2.rmmap_anon_post) (@UC00.rmmap_anon_post) (Q6nq.gwt_def (@Q5m9.Mq9.rmmap_anon_post) (@UC00.rmmap_anon_post) (Q6nq.gwt_def (@QCa8.Mq5.rimplT) (@Uv2Y.rimplT) (Q6nq.gwt_def (@Q5m9.Mq9.rimplT) (@Uv2Y.rimplT) (Q6nq.gwt_def (@QkTt.Mq3.rgrp_region_addr) (@Un7h.rgrp_region_addr) (Q6nq.gwt_def (@Q8QT.Mq4.rgroup_rep) (@UQXM.rgroup_rep) (Q6nq.gwt_def (@Q5m9.Mq9.rgroup_rep) (@UQXM.rgroup_rep) (Q6nq.gwt_def (@QCa8.Mq5.rauxv_ok) (@Uv2Y.rauxv_ok) (Q6nq.gwt_def (@Q5m9.Mq9.rauxv_ok) (@Uv2Y.rauxv_ok) (Q6nq.gwt_def (@Q8QT.Mq4.rarea_rep) (@UQXM.rarea_rep) (Q6nq.gwt_def (@Q5m9.Mq9.rarea_rep) (@UQXM.rarea_rep) (Q6nq.gwt_def (@QQRC.Mq5.ram_ret_post) (@UNR4.ram_ret_post) (Q6nq.gwt_def (@Q5m9.Mq9.ram_ret_post) (@UNR4.ram_ret_post) (Q6nq.gwt_def (@QCa8.Mq5.ram_post) (@Uv2Y.ram_post) (Q6nq.gwt_def (@Q5m9.Mq9.ram_post) (@Uv2Y.ram_post) (Q6nq.gwt_def (@QQRC.Mq5.ram_frame) (@UNR4.ram_frame) (Q6nq.gwt_def (@Q5m9.Mq9.ram_frame) (@UNR4.ram_frame) (Q6nq.gwt_def (@QQRC.Mq5.ram_fp) (@UNR4.ram_fp) (Q6nq.gwt_def (@Q5m9.Mq9.ram_fp) (@UNR4.ram_fp) (Q6nq.gwt_def (@Q8l1.Mq7.ram_entry_post) (@U4Oe.ram_entry_post) (Q6nq.gwt_def (@Q5m9.Mq9.ram_entry_post) (@U4Oe.ram_entry_post) (Q6nq.gwt_def (@QCa8.Mq5.ralloc_meta_stmt) (@Uv2Y.ralloc_meta_stmt) (Q6nq.gwt_def (@Q5m9.Mq9.ralloc_meta_stmt) (@Uv2Y.ralloc_meta_stmt) (Q6nq.gwt_def (@QCa8.Mq5.ralloc_fp) (@Uv2Y.ralloc_fp) (Q6nq.gwt_def (@Q5m9.Mq9.ralloc_fp) (@Uv2Y.ralloc_fp) (Q6nq.gwt_def (@Q5m9.Mq9.memcpy_post) (@U4l4.memcpy_post) (Q6nq.gwt_def (@QVbl.Mq3.memcpy_post) (@U4l4.memcpy_post) (Q6nq.gwt_def (@QCa8.Mq5.RAM_STACK) (@Uv2Y.RAM_STACK) Q6nq.gwt_nil)))))))))))))))))))))))))))))))))))))))))))))))))))).
#[using="Type"] Lemma rrw_cells_magree : ltac2:(Q6nq.ty2 'GwI.segs '(@Q5m9.Mq9.rrw_cells_magree) [] '(@nil Z) 'gwt_X).
Proof. first [GwApply2.gw_by_name2 GwI.segs (@Q5m9.Mq9.rrw_cells_magree) | autorewrite with gw_eqs; GwApply2.gw_by_name2 GwI.segs (@Q5m9.Mq9.rrw_cells_magree)]. Qed.
#[using="Type"] Lemma rbytes_at_magree : ltac2:(Q6nq.ty2 'GwI.segs '(@Q5m9.Mq9.rbytes_at_magree) [] '(@nil Z) 'gwt_X).
Proof. first [GwApply2.gw_by_name2 GwI.segs (@Q5m9.Mq9.rbytes_at_magree) | autorewrite with gw_eqs; GwApply2.gw_by_name2 GwI.segs (@Q5m9.Mq9.rbytes_at_magree)]. Qed.
#[using="Type"] Lemma rwr_at_magree : ltac2:(Q6nq.ty2 'GwI.segs '(@Q5m9.Mq9.rwr_at_magree) [] '(@nil Z) 'gwt_X).
Proof. first [GwApply2.gw_by_name2 GwI.segs (@Q5m9.Mq9.rwr_at_magree) | autorewrite with gw_eqs; GwApply2.gw_by_name2 GwI.segs (@Q5m9.Mq9.rwr_at_magree)]. Qed.

#[using="Type"] Lemma rauxv_ok_magree C m m' B :
rauxv_ok m B -> magree C m m' -> (forall a, C a -> a < B /\ ~ (RAUXV_CELL <= a < RAUXV_CELL + 8)) -> rauxv_ok m' B.
Proof. ltac2:(GwEq.gw_rw [[@gw_eq_rauxv_ok__3; @gw_eq_rauxv_ok__2; @gw_eq_rauxv_ok]]); first [GwApply2.gw_by_name2 GwI.segs (@Q5m9.Mq9.rauxv_ok_magree) | autorewrite with gw_eqs; GwApply2.gw_by_name2 GwI.segs (@Q5m9.Mq9.rauxv_ok_magree)]. Qed.

Section ASM.
Variables (R : Type) (k : mstate -> optr -> QUZl.M R) (bail : QUZl.M R) (o : mem) (s : PState) (Q : R -> PState -> machine_state -> Prop).
Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem) (st : mstate) (lo : Z) (errv : word).
Hypothesis AMP : RAMpre st.
Hypothesis MR : rmrep st m.
Hypothesis TK : ticks_ok st.
Hypothesis BL : brk_link_ps st s.
Hypothesis AUX : rauxv_ok m (bv_unsigned sp).
Hypothesis ST : stk rsegs m lo (bv_unsigned sp).
Hypothesis LO : alloc_ceiling <= lo.
Hypothesis LOLE : lo <= bv_unsigned sp - RAM_STACK.
Hypothesis ERR : rw_cells rsegs m (errno_addr tp) [C4 errv].
Hypothesis MI : mem_inv rsegs m.
Hypothesis TP : tp = Z_to_bv 64 0x77c00.
Hypothesis KH : forall st1 mo s' ms',
ram_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc st s lo m st1 mo s' ms' ->
brk_link_ps st1 s' ->
rimplT o (k st1 mo) s' Q ms'.

Definition rFP (stX : mstate) (a : Z) : Prop := ralloc_fp (fun k => k <> RKGroup) stX lo (bv_unsigned sp) a \/ fresh_addr st a.

#[using="Type"] Lemma rFP_am stX a : ram_fp stX lo (bv_unsigned sp) a -> rFP stX a.
Proof. ltac2:(GwEq.gw_rw [[@gw_eq_ram_fp__3; @gw_eq_ram_fp__2; @gw_eq_ram_fp]]); first [GwApply2.gw_by_name2 GwI.segs (@Q5m9.Mq9.rFP_am) | autorewrite with gw_eqs; GwApply2.gw_by_name2 GwI.segs (@Q5m9.Mq9.rFP_am)]. Qed.

#[using="RC__ TP"] Lemma rETP : errno_addr tp = 0x77c00 - 164.
Proof. first [GwApply2.gw_by_name2 GwI.segs (@Q5m9.Mq9.rETP) | autorewrite with gw_eqs; GwApply2.gw_by_name2 GwI.segs (@Q5m9.Mq9.rETP)]. Qed.

#[using="TK KH"] Lemma rfinish_K : ltac2:(Q6nq.ty2 'GwI.segs '(@Q5m9.Mq9.rfinish_K) [[@gw_eq_rauxv_ok__3; @gw_eq_rauxv_ok__2; @gw_eq_rauxv_ok]; [@gw_eq_rimplT__3; @gw_eq_rimplT__2; @gw_eq_rimplT]; [@gw_eq_rmrep__3; @gw_eq_rmrep__2; @gw_eq_rmrep]] '(@nil Z) '(Q6nq.gwt_def (@Q5m9.Mq9.rFP) (@rFP) gwt_X)).
Proof. ltac2:(GwEq.gw_rw [[@gw_eq_rauxv_ok__3; @gw_eq_rauxv_ok__2; @gw_eq_rauxv_ok]; [@gw_eq_rimplT__3; @gw_eq_rimplT__2; @gw_eq_rimplT]; [@gw_eq_rmrep__3; @gw_eq_rmrep__2; @gw_eq_rmrep]]); first [GwApply2.gw_by_name2 GwI.segs (@Q5m9.Mq9.rfinish_K) | autorewrite with gw_eqs; GwApply2.gw_by_name2 GwI.segs (@Q5m9.Mq9.rfinish_K)]. Qed.

#[using="Type"] Lemma rFP_mono : ltac2:(Q6nq.ty2 'GwI.segs '(@Q5m9.Mq9.rFP_mono) [] '(@nil Z) '(Q6nq.gwt_def (@Q5m9.Mq9.rFP) (@rFP) gwt_X)).
Proof. first [GwApply2.gw_by_name2 GwI.segs (@Q5m9.Mq9.rFP_mono) | autorewrite with gw_eqs; GwApply2.gw_by_name2 GwI.segs (@Q5m9.Mq9.rFP_mono)]. Qed.

#[using="Type"] Lemma rFP_same stX stY a : s_regions stY = s_regions stX -> rFP stX a -> rFP stY a.
Proof. first [GwApply2.gw_by_name2 GwI.segs (@Q5m9.Mq9.rFP_same) | autorewrite with gw_eqs; GwApply2.gw_by_name2 GwI.segs (@Q5m9.Mq9.rFP_same)]. Qed.

#[using="AMP LO LOLE"] Lemma rFP_below stX a : rregions_wf stX -> rFP stX a -> a < bv_unsigned sp /\ ~ (RAUXV_CELL <= a < RAUXV_CELL + 8).
Proof. ltac2:(GwEq.gw_rw [[@gw_eq_rregions_wf__3; @gw_eq_rregions_wf__2; @gw_eq_rregions_wf]]); first [ (pose proof LOLE as gw_h_; clear LOLE; ltac2:(GwEqH.gw_rw_in @gw_h_ [[@gw_eq_RAM_STACK__3; @gw_eq_RAM_STACK__2; @gw_eq_RAM_STACK]]); rename gw_h_ into LOLE) | idtac ]; first [GwApply2.gw_by_name2 GwI.segs (@Q5m9.Mq9.rFP_below) | autorewrite with gw_eqs; GwApply2.gw_by_name2 GwI.segs (@Q5m9.Mq9.rFP_below)]. Qed.

#[using="LO TP"] Lemma rerrno_not_amfp stX a : rregions_wf stX -> ram_fp stX lo (bv_unsigned sp) a -> ~ (errno_addr tp <= a < errno_addr tp + 4).
Proof. ltac2:(GwEq.gw_rw [[@gw_eq_ram_fp__3; @gw_eq_ram_fp__2; @gw_eq_ram_fp]; [@gw_eq_rregions_wf__3; @gw_eq_rregions_wf__2; @gw_eq_rregions_wf]]); first [GwApply2.gw_by_name2 GwI.segs (@Q5m9.Mq9.rerrno_not_amfp) | autorewrite with gw_eqs; GwApply2.gw_by_name2 GwI.segs (@Q5m9.Mq9.rerrno_not_amfp)]. Qed.

#[using="Type"] Lemma rbrk_am_took X q c : c_brk (ctx (am_took X q c)) = c_brk (ctx X). Proof. first [GwApply2.gw_by_name2 GwI.segs (@Q5m9.Mq9.rbrk_am_took) | autorewrite with gw_eqs; GwApply2.gw_by_name2 GwI.segs (@Q5m9.Mq9.rbrk_am_took)]. Qed.

#[using="Type"] Lemma ram_take_took : ltac2:(Q6nq.ty2 'GwI.segs '(@Q5m9.Mq9.ram_take_took) [] '([100]%Z : list Z) '(Q6nq.gwt_zc NSLOTS (Q6nq.gwt_zc AREA_HDR (Q6nq.gwt_def (@Q5m9.Mq9.rFP) (@rFP) gwt_X)))).
Proof. first [GwApply2.gw_by_name2 GwI.segs (@Q5m9.Mq9.ram_take_took) | autorewrite with gw_eqs; GwApply2.gw_by_name2 GwI.segs (@Q5m9.Mq9.ram_take_took)]. Qed.
#[using="Type"] Lemma rconc_am_took X q c y : conc (am_took X q c) y = conc X y. Proof. first [GwApply2.gw_by_name2 GwI.segs (@Q5m9.Mq9.rconc_am_took) | autorewrite with gw_eqs; GwApply2.gw_by_name2 GwI.segs (@Q5m9.Mq9.rconc_am_took)]. Qed.
#[using="Type"] Lemma rbrk_carve stY p : c_brk (ctx (carve_st stY p)) = c_brk (ctx stY).
Proof. first [GwApply2.gw_by_name2 GwI.segs (@Q5m9.Mq9.rbrk_carve) | autorewrite with gw_eqs; GwApply2.gw_by_name2 GwI.segs (@Q5m9.Mq9.rbrk_carve)]. Qed.
#[using="Type"] Lemma rconc_carve stY p y : conc (carve_st stY p) y = conc stY y.
Proof. first [GwApply2.gw_by_name2 GwI.segs (@Q5m9.Mq9.rconc_carve) | autorewrite with gw_eqs; GwApply2.gw_by_name2 GwI.segs (@Q5m9.Mq9.rconc_carve)]. Qed.

#[using="AMP TK LO LOLE TP KH"] Lemma rcarve_K : ltac2:(Q6nq.ty2 'GwI.segs '(@Q5m9.Mq9.rcarve_K) [[@gw_eq_ram_frame__3; @gw_eq_ram_frame__2; @gw_eq_ram_frame]; [@gw_eq_rauxv_ok__3; @gw_eq_rauxv_ok__2; @gw_eq_rauxv_ok]; [@gw_eq_rimplT__3; @gw_eq_rimplT__2; @gw_eq_rimplT]; [@gw_eq_rmrep__3; @gw_eq_rmrep__2; @gw_eq_rmrep]; [@gw_eq_RAM_STACK__3; @gw_eq_RAM_STACK__2; @gw_eq_RAM_STACK]] '([100; 4096; 339364]%Z : list Z) '(Q6nq.gwt_unf (@PGSZ) (Q6nq.gwt_zc RSSP_GUARD (Q6nq.gwt_zc RMLOCK (Q6nq.gwt_zc NSLOTS (Q6nq.gwt_zc META_SIZE (Q6nq.gwt_zc AREA_HDR (Q6nq.gwt_def (@Q5m9.Mq9.rFP) (@rFP) (Q6nq.gwt_pat (@RATP) (@RATP) (Q6nq.gwt_hdr GwI.RATP (@RATP) gwt_X)))))))))).
Proof. ltac2:(GwEq.gw_rw [[@gw_eq_ram_frame__3; @gw_eq_ram_frame__2; @gw_eq_ram_frame]; [@gw_eq_rauxv_ok__3; @gw_eq_rauxv_ok__2; @gw_eq_rauxv_ok]; [@gw_eq_rimplT__3; @gw_eq_rimplT__2; @gw_eq_rimplT]; [@gw_eq_rmrep__3; @gw_eq_rmrep__2; @gw_eq_rmrep]]); first [ (pose proof LOLE as gw_h_; clear LOLE; ltac2:(GwEqH.gw_rw_in @gw_h_ [[@gw_eq_RAM_STACK__3; @gw_eq_RAM_STACK__2; @gw_eq_RAM_STACK]]); rename gw_h_ into LOLE) | idtac ]; first [GwApply2.gw_by_name2 GwI.segs (@Q5m9.Mq9.rcarve_K) | autorewrite with gw_eqs; GwApply2.gw_by_name2 GwI.segs (@Q5m9.Mq9.rcarve_K)]. Qed.

#[using="TP"] Lemma rrepfoot_low : ltac2:(Q6nq.ty2 'GwI.segs '(@Q5m9.Mq9.rrepfoot_low) [[@gw_eq_rregions_wf__3; @gw_eq_rregions_wf__2; @gw_eq_rregions_wf]; [@gw_eq_rrepfoot__3; @gw_eq_rrepfoot__2; @gw_eq_rrepfoot]] '(@nil Z) '(Q6nq.gwt_def (@Q5m9.Mq9.rFP) (@rFP) gwt_X)).
Proof. ltac2:(GwEq.gw_rw [[@gw_eq_rregions_wf__3; @gw_eq_rregions_wf__2; @gw_eq_rregions_wf]; [@gw_eq_rrepfoot__3; @gw_eq_rrepfoot__2; @gw_eq_rrepfoot]]); first [GwApply2.gw_by_name2 GwI.segs (@Q5m9.Mq9.rrepfoot_low) | autorewrite with gw_eqs; GwApply2.gw_by_name2 GwI.segs (@Q5m9.Mq9.rrepfoot_low)]. Qed.

Lemma rfinish_path : ltac2:(Q6nq.ty2 'GwI.segs '(@Q5m9.Mq9.rfinish_path) [[@gw_eq_ram_frame__3; @gw_eq_ram_frame__2; @gw_eq_ram_frame]; [@gw_eq_rauxv_ok__3; @gw_eq_rauxv_ok__2; @gw_eq_rauxv_ok]; [@gw_eq_rimplT__3; @gw_eq_rimplT__2; @gw_eq_rimplT]; [@gw_eq_rmrep__3; @gw_eq_rmrep__2; @gw_eq_rmrep]; [@gw_eq_RAM_STACK__3; @gw_eq_RAM_STACK__2; @gw_eq_RAM_STACK]] '([4096; 339508]%Z : list Z) '(Q6nq.gwt_unf (@PGSZ) (Q6nq.gwt_zc RSSP_GUARD (Q6nq.gwt_zc RMLOCK (Q6nq.gwt_zc NSLOTS (Q6nq.gwt_zc META_SIZE (Q6nq.gwt_zc AREA_HDR (Q6nq.gwt_def (@Q5m9.Mq9.rFP) (@rFP) (Q6nq.gwt_pat (@RATP) (@RATP) (Q6nq.gwt_hdr GwI.RATP (@RATP) gwt_X)))))))))).
Proof using AMP KH LO LOLE TK TP. ltac2:(GwEq.gw_rw [[@gw_eq_ram_frame__3; @gw_eq_ram_frame__2; @gw_eq_ram_frame]; [@gw_eq_rauxv_ok__3; @gw_eq_rauxv_ok__2; @gw_eq_rauxv_ok]; [@gw_eq_rimplT__3; @gw_eq_rimplT__2; @gw_eq_rimplT]; [@gw_eq_rmrep__3; @gw_eq_rmrep__2; @gw_eq_rmrep]]); first [ (pose proof LOLE as gw_h_; clear LOLE; ltac2:(GwEqH.gw_rw_in @gw_h_ [[@gw_eq_RAM_STACK__3; @gw_eq_RAM_STACK__2; @gw_eq_RAM_STACK]]); rename gw_h_ into LOLE) | idtac ]; first [GwApply2.gw_by_name2 GwI.segs (@Q5m9.Mq9.rfinish_path) | autorewrite with gw_eqs; GwApply2.gw_by_name2 GwI.segs (@Q5m9.Mq9.rfinish_path)]. Qed.

#[using="Type"] Lemma rlive_ranges_same : ltac2:(Q6nq.ty2 'GwI.segs '(@Q5m9.Mq9.rlive_ranges_same) [] '(@nil Z) '(Q6nq.gwt_def (@Q5m9.Mq9.rFP) (@rFP) gwt_X)).
Proof. first [GwApply2.gw_by_name2 GwI.segs (@Q5m9.Mq9.rlive_ranges_same) | autorewrite with gw_eqs; GwApply2.gw_by_name2 GwI.segs (@Q5m9.Mq9.rlive_ranges_same)]. Qed.

#[using="Type"] Lemma rfresh_of_ranges_free : ltac2:(Q6nq.ty2 'GwI.segs '(@Q5m9.Mq9.rfresh_of_ranges_free) [] '(@nil Z) '(Q6nq.gwt_def (@Q5m9.Mq9.rFP) (@rFP) gwt_X)).
Proof. first [GwApply2.gw_by_name2 GwI.segs (@Q5m9.Mq9.rfresh_of_ranges_free) | autorewrite with gw_eqs; GwApply2.gw_by_name2 GwI.segs (@Q5m9.Mq9.rfresh_of_ranges_free)]. Qed.

#[using="Type"] Lemma rrepfoot_clear : ltac2:(Q6nq.ty2 'GwI.segs '(@Q5m9.Mq9.rrepfoot_clear) [[@gw_eq_rgrp_region_addr__3; @gw_eq_rgrp_region_addr__2; @gw_eq_rgrp_region_addr]; [@gw_eq_rmrep__3; @gw_eq_rmrep__2; @gw_eq_rmrep]; [@gw_eq_rrepfoot__3; @gw_eq_rrepfoot__2; @gw_eq_rrepfoot]] '(@nil Z) '(Q6nq.gwt_def (@Q5m9.Mq9.rFP) (@rFP) gwt_X)).
Proof. ltac2:(GwEq.gw_rw [[@gw_eq_rgrp_region_addr__3; @gw_eq_rgrp_region_addr__2; @gw_eq_rgrp_region_addr]; [@gw_eq_rmrep__3; @gw_eq_rmrep__2; @gw_eq_rmrep]; [@gw_eq_rrepfoot__3; @gw_eq_rrepfoot__2; @gw_eq_rrepfoot]]); first [GwApply2.gw_by_name2 GwI.segs (@Q5m9.Mq9.rrepfoot_clear) | autorewrite with gw_eqs; GwApply2.gw_by_name2 GwI.segs (@Q5m9.Mq9.rrepfoot_clear)]. Qed.

#[using="AMP TK LO LOLE TP KH"] Lemma rmmap_path : ltac2:(Q6nq.ty2 'GwI.segs '(@Q5m9.Mq9.rmmap_path) [[@gw_eq_ram_frame__3; @gw_eq_ram_frame__2; @gw_eq_ram_frame]; [@gw_eq_rauxv_ok__3; @gw_eq_rauxv_ok__2; @gw_eq_rauxv_ok]; [@gw_eq_rimplT__3; @gw_eq_rimplT__2; @gw_eq_rimplT]; [@gw_eq_rmrep__3; @gw_eq_rmrep__2; @gw_eq_rmrep]; [@gw_eq_RAM_STACK__3; @gw_eq_RAM_STACK__2; @gw_eq_RAM_STACK]] '([4096; 339268]%Z : list Z) '(Q6nq.gwt_unf (@PGSZ) (Q6nq.gwt_zc RSSP_GUARD (Q6nq.gwt_zc RMLOCK (Q6nq.gwt_def (@Q5m9.Mq9.rFP) (@rFP) (Q6nq.gwt_pat (@RATP) (@RATP) (Q6nq.gwt_hdr GwI.RATP (@RATP) gwt_X))))))).
Proof. ltac2:(GwEq.gw_rw [[@gw_eq_ram_frame__3; @gw_eq_ram_frame__2; @gw_eq_ram_frame]; [@gw_eq_rauxv_ok__3; @gw_eq_rauxv_ok__2; @gw_eq_rauxv_ok]; [@gw_eq_rimplT__3; @gw_eq_rimplT__2; @gw_eq_rimplT]; [@gw_eq_rmrep__3; @gw_eq_rmrep__2; @gw_eq_rmrep]]); first [ (pose proof LOLE as gw_h_; clear LOLE; ltac2:(GwEqH.gw_rw_in @gw_h_ [[@gw_eq_RAM_STACK__3; @gw_eq_RAM_STACK__2; @gw_eq_RAM_STACK]]); rename gw_h_ into LOLE) | idtac ]; first [GwApply2.gw_by_name2 GwI.segs (@Q5m9.Mq9.rmmap_path) | autorewrite with gw_eqs; GwApply2.gw_by_name2 GwI.segs (@Q5m9.Mq9.rmmap_path)]. Qed.

#[using="RC__"] Lemma rimage_range_clear : ltac2:(Q6nq.ty2 'GwI.segs '(@Q5m9.Mq9.rimage_range_clear) [] '([65536; 626688]%Z : list Z) '(Q6nq.gwt_unf (@RIMG_LO) (Q6nq.gwt_unf (@RIMG_HI) (Q6nq.gwt_def (@Q5m9.Mq9.rFP) (@rFP) (Q6nq.gwt_pat (@ref_reserved) (@ref_reserved) (Q6nq.gwt_hdr GwI.ref_reserved (@ref_reserved) (Q6nq.gwt_pat (@RIMG_HI) (@RIMG_HI) (Q6nq.gwt_hdr GwI.RIMG_HI (@RIMG_HI) gwt_X)))))))).
Proof. first [GwApply2.gw_by_name2 GwI.segs (@Q5m9.Mq9.rimage_range_clear) | autorewrite with gw_eqs; GwApply2.gw_by_name2 GwI.segs (@Q5m9.Mq9.rimage_range_clear)]. Qed.

#[using="errv AMP TK LO LOLE ERR TP KH"] Lemma rbrk_live_path : forall (stI : mstate) (brid : N) (boff : Z) (m1 : mem) (junk : list byte) (e1 : word)
(x1 t0 t1 t2 s1x a0 a1 a2 a3 a4 a5 a6 a7 s4x t3 t4 t5 t6 : word),
RAMpre stI -> AMI st stI -> s_regions stI = s_regions st -> brk_link_ps stI s ->
c_avail_meta_area_count (ctx stI) = 0 -> c_brk (ctx stI) = BrkLive brid boff ->
ptrs_in (fun rid => (rid < s_next_rid stI)%N) stI ->
rmrep stI m1 -> mem_inv rsegs m1 ->
rw_cells rsegs m1 (bv_unsigned sp + -64) (ram_frame junk s4 s3 s2 s1 s0 ra) -> stk rsegs m1 lo (bv_unsigned sp + -64) ->
rw_cells rsegs m1 (errno_addr tp) [C4 e1] -> rauxv_ok m1 (bv_unsigned sp) -> magree (rFP stI) m m1 ->
rimplT o (let old := conc stI (brid, boff) in
let new := old + PGSZ in
SVis (EBrk new) (fun r =>
if negb (brk_answer_ok old new r) then bad_answer bail else
if negb (r =? new) then am_after_brk (upd_ctx (set_brk BrkDead) stI) true k bail
else if negb (brk_pages_ok stI old PGSZ) then bad_answer bail
else
let st1 := upd_region brid (fun rg => mkRegion (r_kind rg) (r_base rg) (boff + PGSZ)) stI in
let st2 := upd_ctx (fun c => set_avail_meta_area_count 1 (set_avail_meta_areas (Some (brid, boff)) (set_brk (BrkLive brid (boff + PGSZ)) c))) st1 in
am_after_brk st2 false k bail)) s Q
(MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -64)) gp tp t0 t1 t2 (Z_to_bv 64 4096) s1x a0 a1 a2 a3 a4 a5 a6 a7
(Z_to_bv 64 RSSP_GUARD) (Z_to_bv 64 RMLOCK) s4x s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x52c94) fc None m1 (seg_rom rsegs)).
Proof. ltac2:(GwEq.gw_rw [[@gw_eq_ram_frame__3; @gw_eq_ram_frame__2; @gw_eq_ram_frame]; [@gw_eq_rauxv_ok__3; @gw_eq_rauxv_ok__2; @gw_eq_rauxv_ok]; [@gw_eq_rimplT__3; @gw_eq_rimplT__2; @gw_eq_rimplT]; [@gw_eq_rmrep__3; @gw_eq_rmrep__2; @gw_eq_rmrep]]); first [ (pose proof LOLE as gw_h_; clear LOLE; ltac2:(GwEqH.gw_rw_in @gw_h_ [[@gw_eq_RAM_STACK__3; @gw_eq_RAM_STACK__2; @gw_eq_RAM_STACK]]); rename gw_h_ into LOLE) | idtac ]; first [GwApply2.gw_by_name2 GwI.segs (@Q5m9.Mq9.rbrk_live_path) | autorewrite with gw_eqs; GwApply2.gw_by_name2 GwI.segs (@Q5m9.Mq9.rbrk_live_path)]. Qed.

Lemma rbrk_untried_path : forall (stI : mstate) (m1 : mem) (junk : list byte) (e1 : word)
(x1 t0 t1 t2 s1x a0 a1 a2 a3 a4 a5 a6 a7 s4x t3 t4 t5 t6 : word),
RAMpre stI -> AMI st stI -> s_regions stI = s_regions st ->
c_avail_meta_area_count (ctx stI) = 0 -> c_brk (ctx stI) = BrkUntried ->
ptrs_in (fun rid => (rid < s_next_rid stI)%N) stI ->
rmrep stI m1 -> mem_inv rsegs m1 ->
rw_cells rsegs m1 (bv_unsigned sp + -64) (ram_frame junk s4 s3 s2 s1 s0 ra) -> stk rsegs m1 lo (bv_unsigned sp + -64) ->
rw_cells rsegs m1 (errno_addr tp) [C4 e1] -> rauxv_ok m1 (bv_unsigned sp) -> magree (rFP stI) m m1 ->
ps_m s = ps_m s ->
rimplT o (SVis (EBrk 0) (fun cur =>
if negb (brk0_answer_ok cur) then bad_answer bail else
let base := round_up_pg cur in
let new := base + 2 * PGSZ in
SVis (EBrk new) (fun r =>
if negb (brk_answer_ok cur new r) then bad_answer bail else
if negb (r =? new) then am_after_brk (upd_ctx (set_brk BrkDead) stI) true k bail
else if negb (brk_pages_ok stI base (2 * PGSZ)) then bad_answer bail
else
SVis (EMmap base PGSZ PROT_NONE (MAP_PRIVATE + MAP_ANON + MAP_FIXED)) (fun rg =>
if negb (mmap_fixed_answer_ok base rg) then bad_answer bail else
let '(st1, rid) := new_region RKBrk base (2 * PGSZ) stI in
let st2 := upd_ctx (fun c => set_avail_meta_area_count 1
(set_avail_meta_areas (Some (rid, PGSZ))
(set_brk (BrkLive rid (2 * PGSZ)) c))) st1 in
am_after_brk st2 false k bail)))) s Q
(MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -64)) gp tp t0 t1 t2 (Z_to_bv 64 4096) s1x a0 a1 a2 a3 a4 a5 a6 a7
(Z_to_bv 64 RSSP_GUARD) (Z_to_bv 64 RMLOCK) s4x s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x52c94) fc None m1 (seg_rom rsegs)).
Proof using AMP ERR KH LO LOLE TK TP. ltac2:(GwEq.gw_rw [[@gw_eq_ram_frame__3; @gw_eq_ram_frame__2; @gw_eq_ram_frame]; [@gw_eq_rauxv_ok__3; @gw_eq_rauxv_ok__2; @gw_eq_rauxv_ok]; [@gw_eq_rimplT__3; @gw_eq_rimplT__2; @gw_eq_rimplT]; [@gw_eq_rmrep__3; @gw_eq_rmrep__2; @gw_eq_rmrep]]); first [ (pose proof LOLE as gw_h_; clear LOLE; ltac2:(GwEqH.gw_rw_in @gw_h_ [[@gw_eq_RAM_STACK__3; @gw_eq_RAM_STACK__2; @gw_eq_RAM_STACK]]); rename gw_h_ into LOLE) | idtac ]; first [GwApply2.gw_by_name2 GwI.segs (@Q5m9.Mq9.rbrk_untried_path) | autorewrite with gw_eqs; GwApply2.gw_by_name2 GwI.segs (@Q5m9.Mq9.rbrk_untried_path)]. Qed.

#[using="errv AMP TK LO LOLE ERR TP KH"] Lemma rbody_spec : ltac2:(Q6nq.ty2 'GwI.segs '(@Q5m9.Mq9.rbody_spec) [[@gw_eq_ram_frame__3; @gw_eq_ram_frame__2; @gw_eq_ram_frame]; [@gw_eq_rauxv_ok__3; @gw_eq_rauxv_ok__2; @gw_eq_rauxv_ok]; [@gw_eq_rimplT__3; @gw_eq_rimplT__2; @gw_eq_rimplT]; [@gw_eq_rmrep__3; @gw_eq_rmrep__2; @gw_eq_rmrep]; [@gw_eq_RAM_STACK__3; @gw_eq_RAM_STACK__2; @gw_eq_RAM_STACK]] '([4096; 339008]%Z : list Z) '(Q6nq.gwt_unf (@PGSZ) (Q6nq.gwt_zc RSSP_GUARD (Q6nq.gwt_zc RMLOCK (Q6nq.gwt_def (@Q5m9.Mq9.rFP) (@rFP) (Q6nq.gwt_pat (@ref_reserved) (@ref_reserved) (Q6nq.gwt_hdr GwI.ref_reserved (@ref_reserved) (Q6nq.gwt_pat (@RATP) (@RATP) (Q6nq.gwt_hdr GwI.RATP (@RATP) gwt_X))))))))).
Proof. ltac2:(GwEq.gw_rw [[@gw_eq_ram_frame__3; @gw_eq_ram_frame__2; @gw_eq_ram_frame]; [@gw_eq_rauxv_ok__3; @gw_eq_rauxv_ok__2; @gw_eq_rauxv_ok]; [@gw_eq_rimplT__3; @gw_eq_rimplT__2; @gw_eq_rimplT]; [@gw_eq_rmrep__3; @gw_eq_rmrep__2; @gw_eq_rmrep]]); first [ (pose proof LOLE as gw_h_; clear LOLE; ltac2:(GwEqH.gw_rw_in @gw_h_ [[@gw_eq_RAM_STACK__3; @gw_eq_RAM_STACK__2; @gw_eq_RAM_STACK]]); rename gw_h_ into LOLE) | idtac ]; first [GwApply2.gw_by_name2 GwI.segs (@Q5m9.Mq9.rbody_spec) | autorewrite with gw_eqs; GwApply2.gw_by_name2 GwI.segs (@Q5m9.Mq9.rbody_spec)]. Qed.

#[using="lo errv AMP MR TK BL AUX ST LO LOLE ERR MI TP KH"] Lemma ralloc_meta_main : ltac2:(Q6nq.ty2 'GwI.segs '(@Q5m9.Mq9.ralloc_meta_main) [[@gw_eq_rimplT__3; @gw_eq_rimplT__2; @gw_eq_rimplT]; [@gw_eq_RAM_STACK__3; @gw_eq_RAM_STACK__2; @gw_eq_RAM_STACK]] '(@nil Z) '(Q6nq.gwt_zc ralloc_meta_entry (Q6nq.gwt_def (@Q5m9.Mq9.rFP) (@rFP) gwt_X))).
Proof. ltac2:(GwEq.gw_rw [[@gw_eq_rimplT__3; @gw_eq_rimplT__2; @gw_eq_rimplT]]); first [ (pose proof LOLE as gw_h_; clear LOLE; ltac2:(GwEqH.gw_rw_in @gw_h_ [[@gw_eq_RAM_STACK__3; @gw_eq_RAM_STACK__2; @gw_eq_RAM_STACK]]); rename gw_h_ into LOLE) | idtac ]; first [GwApply2.gw_by_name2 GwI.segs (@Q5m9.Mq9.ralloc_meta_main) | autorewrite with gw_eqs; GwApply2.gw_by_name2 GwI.segs (@Q5m9.Mq9.ralloc_meta_main)]. Qed.
End ASM.

#[using="Type"] Theorem ralloc_meta_spec : ralloc_meta_stmt ram_pre.
Proof. ltac2:(GwEq.gw_rw [[@gw_eq_ralloc_meta_stmt__3; @gw_eq_ralloc_meta_stmt__2; @gw_eq_ralloc_meta_stmt]]); first [GwApply2.gw_by_name2 GwI.segs (@Q5m9.Mq9.ralloc_meta_spec) | autorewrite with gw_eqs; GwApply2.gw_by_name2 GwI.segs (@Q5m9.Mq9.ralloc_meta_spec)]. Qed.

End RC__1.
