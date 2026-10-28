(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)


From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib Require CodeAt StepGen GwInst GwEq GwApply GwApply2. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Q6nq.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Q8l1.
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
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q5Rg.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UEQM.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UEQM.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require U4l4.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import U4l4.
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
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QWTl.Mq3.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QZAi.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QZAi.Mq2. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QUZl.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QUZl. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Q7S0.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q7S0.Mq0.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UQXM.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UQXM. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require Uv2Y.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Uv2Y. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UIMz.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UIMz. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require U8eV.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import U8eV. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UlEO.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UlEO. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UNR4.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UNR4.
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
Lemma CODE_rerrno_loc_entry : CodeAt.code_at rsegs rerrno_loc_entry Q8l1.Mq7.errno_loc_code.  Proof. StepGen.code_at_vm. Qed.
Definition ref_find_segment_none := @UKNz.ref_find_segment_none.
Definition ref_ro_addr_false := @UKNz.ref_ro_addr_false.
Definition ref_memory_read_none := @UKNz.ref_memory_read_none.
Definition ref_wview_overlay := @UKNz.ref_wview_overlay.
Definition ref_seg_rom_none := @UKNz.ref_seg_rom_none.
Definition ref_mrd_overlay := @UKNz.ref_mrd_overlay.
Definition memcpy_spec := @memcpy_spec.
End GwI.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

Local Definition gwt_X : unit := (Q6nq.gwt_def (@Q8QT.Mq4.rshadow_rep) (@UQXM.rshadow_rep) (Q6nq.gwt_def (@Q8l1.Mq7.rshadow_rep) (@UQXM.rshadow_rep) (Q6nq.gwt_def (@Q8QT.Mq4.rregions_wf) (@UQXM.rregions_wf) (Q6nq.gwt_def (@Q8l1.Mq7.rregions_wf) (@UQXM.rregions_wf) (Q6nq.gwt_def (@Q8QT.Mq4.rmrep_shadow) (@UQXM.rmrep_shadow) (Q6nq.gwt_def (@Q8l1.Mq7.rmrep_shadow) (@UQXM.rmrep_shadow) (Q6nq.gwt_def (@Q8QT.Mq4.rmrep_groups) (@UQXM.rmrep_groups) (Q6nq.gwt_def (@Q8l1.Mq7.rmrep_groups) (@UQXM.rmrep_groups) (Q6nq.gwt_def (@Q8QT.Mq4.rmrep_globals) (@UQXM.rmrep_globals) (Q6nq.gwt_def (@Q8l1.Mq7.rmrep_globals) (@UQXM.rmrep_globals) (Q6nq.gwt_def (@Q8QT.Mq4.rmrep_ctx) (@UQXM.rmrep_ctx) (Q6nq.gwt_def (@Q8l1.Mq7.rmrep_ctx) (@UQXM.rmrep_ctx) (Q6nq.gwt_def (@Q8QT.Mq4.rmrep_areas) (@UQXM.rmrep_areas) (Q6nq.gwt_def (@Q8l1.Mq7.rmrep_areas) (@UQXM.rmrep_areas) (Q6nq.gwt_def (@Q8QT.Mq4.rmrep) (@UQXM.rmrep) (Q6nq.gwt_def (@Q8l1.Mq7.rmrep) (@UQXM.rmrep) (Q6nq.gwt_def (@Q8QT.Mq4.rgroup_rep) (@UQXM.rgroup_rep) (Q6nq.gwt_def (@Q8l1.Mq7.rgroup_rep) (@UQXM.rgroup_rep) (Q6nq.gwt_def (@QCa8.Mq5.rauxv_ok) (@Uv2Y.rauxv_ok) (Q6nq.gwt_def (@Q8l1.Mq7.rauxv_ok) (@Uv2Y.rauxv_ok) (Q6nq.gwt_def (@Q8QT.Mq4.rarea_rep) (@UQXM.rarea_rep) (Q6nq.gwt_def (@Q8l1.Mq7.rarea_rep) (@UQXM.rarea_rep) (Q6nq.gwt_def (@Q8l1.Mq7.ram_frame) (@UNR4.ram_frame) (Q6nq.gwt_def (@QQRC.Mq5.ram_frame) (@UNR4.ram_frame) (Q6nq.gwt_def (@Q8l1.Mq7.memcpy_post) (@U4l4.memcpy_post) (Q6nq.gwt_def (@QVbl.Mq3.memcpy_post) (@U4l4.memcpy_post) Q6nq.gwt_nil)))))))))))))))))))))))))).
#[using="Type"] Lemma rmemcpy_callZ3 : ltac2:(Q6nq.ty2 'GwI.segs '(@Q8l1.Mq7.rmemcpy_callZ3) [] '([390200]%Z : list Z) '(Q6nq.gwt_unf (@memcpy_entry) gwt_X)).
Proof. first [GwApply2.gw_by_name2 GwI.segs (@Q8l1.Mq7.rmemcpy_callZ3) | autorewrite with gw_eqs; GwApply2.gw_by_name2 GwI.segs (@Q8l1.Mq7.rmemcpy_callZ3)]. Qed.

#[using="Type"] Lemma ru64s_read : ltac2:(Q6nq.ty2 'GwI.segs '(@Q8l1.Mq7.ru64s_read) [] '(@nil Z) 'gwt_X).
Proof. first [GwApply2.gw_by_name2 GwI.segs (@Q8l1.Mq7.ru64s_read) | autorewrite with gw_eqs; GwApply2.gw_by_name2 GwI.segs (@Q8l1.Mq7.ru64s_read)]. Qed.

#[using="Type"] Lemma rrw_cells_app_split : ltac2:(Q6nq.ty2 'GwI.segs '(@Q8l1.Mq7.rrw_cells_app_split) [] '(@nil Z) 'gwt_X).
Proof. first [GwApply2.gw_by_name2 GwI.segs (@Q8l1.Mq7.rrw_cells_app_split) | autorewrite with gw_eqs; GwApply2.gw_by_name2 GwI.segs (@Q8l1.Mq7.rrw_cells_app_split)]. Qed.

#[using="Type"] Lemma rrw_cells_app_join : ltac2:(Q6nq.ty2 'GwI.segs '(@Q8l1.Mq7.rrw_cells_app_join) [] '(@nil Z) 'gwt_X).
Proof. first [GwApply2.gw_by_name2 GwI.segs (@Q8l1.Mq7.rrw_cells_app_join) | autorewrite with gw_eqs; GwApply2.gw_by_name2 GwI.segs (@Q8l1.Mq7.rrw_cells_app_join)]. Qed.

Definition ram_entry_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
(lo : Z) (st : mstate) (m : word -> option byte) : machine_state -> Prop :=
fun ms' => exists x1 t0 t1 t2 s1x s4x a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m' junk,
ms' = MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -64)) gp tp t0 t1 t2 (Z_to_bv 64 4096) s1x a0 a1 a2 a3 a4 a5 a6 a7
(Z_to_bv 64 RSSP_GUARD) (Z_to_bv 64 RMLOCK) s4x s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0x52c40) fc None m' (seg_rom rsegs)
/\ munch [(bv_unsigned sp - 64, bv_unsigned sp); (RCTX, RCTX + 16)]%Z m m' /\ wmono rsegs m m' /\ mem_inv rsegs m'
/\ rw_cells rsegs m' (bv_unsigned sp + -64) (ram_frame junk s4 s3 s2 s1 s0 ra)
/\ stk rsegs m' lo (bv_unsigned sp + -64)
/\ rmrep (am_init_st st) m'.

#[using="Type"] Lemma ram_entry : ltac2:(Q6nq.ty2 'GwI.segs '(@Q8l1.Mq7.ram_entry) [[@gw_eq_rauxv_ok__3; @gw_eq_rauxv_ok__2; @gw_eq_rauxv_ok]; [@gw_eq_rmrep__3; @gw_eq_rmrep__2; @gw_eq_rmrep]] '([338828]%Z : list Z) '(Q6nq.gwt_unf (@ralloc_meta_entry) (Q6nq.gwt_def (@Q8l1.Mq7.ram_entry_post) (@ram_entry_post) gwt_X))).
Proof. ltac2:(GwEq.gw_rw [[@gw_eq_rauxv_ok__3; @gw_eq_rauxv_ok__2; @gw_eq_rauxv_ok]; [@gw_eq_rmrep__3; @gw_eq_rmrep__2; @gw_eq_rmrep]]); first [GwApply2.gw_by_name2 GwI.segs (@Q8l1.Mq7.ram_entry) | autorewrite with gw_eqs; GwApply2.gw_by_name2 GwI.segs (@Q8l1.Mq7.ram_entry)]. Qed.

End RC__1.
