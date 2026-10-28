(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)


From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib Require CodeAt StepGen GwInst GwEq GwEqH GwApply GwApply2. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Q6nq.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QZxv.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UKNz.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require U1ti.
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
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q9A7.Mq1. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Q5Rg.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q5Rg. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QlEo.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QlEo.Mq0. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QWxq.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QWxq.Mq1. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Q5Rg.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q5Rg.Mq0.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UEQM.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UEQM.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Q2qa.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q2qa.Mq1. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Qy5Y.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qy5Y.Mq1. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Q4J3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q4J3.Mq1. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Qy5Y.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qy5Y.Mq4. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QlQE.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QlQE.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QZAi.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QZAi.Mq2. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QUZl.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QUZl. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Q7S0.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q7S0.Mq0. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Ql2m.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Ql2m.Mq3. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QGeV.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QGeV.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Qy5Y.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qy5Y.Mq6. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QPjm.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QPjm.Mq2. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Q4J3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q4J3.Mq4. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QPjm.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QPjm.Mq0. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Q4J3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q4J3.Mq2. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QJE4.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QJE4.Mq3. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QPjm.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QPjm.Mq3. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QWTl.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QWTl.Mq4. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QDUx.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QDUx.Mqa. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Q9Ay.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q9Ay.Mqb. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QXxF.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QXxF.Mq4. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Q4vs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q4vs. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Q6y7.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q6y7. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QFkE.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QFkE.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UQXM.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UQXM. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require Uv2Y.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Uv2Y. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UIMz.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UIMz. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require Un7h.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Un7h. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require U8eV.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import U8eV.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UpkF.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UpkF. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UlEO.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UlEO. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UUSO.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UUSO. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require U9xa.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import U9xa. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UlqM.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UlqM. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require Uuvn.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Uuvn. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UjYE.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UjYE. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UGig.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UGig.
Import ListNotations.
Import QlEo.Mq0.Exc. Local Ltac Qfw3.Mq3.model_reg_tac n X mexpr ::= Qfw3.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Qfw3.Mq3.zeq_fast ::= Qfw3.Mq3.mkr__zeq_fast_0.
Open Scope Z_scope.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Q6q3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q6q3.

From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib Require CodeAt StepGen GwInst GwApply GwApply2.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module GwI.
Definition segs := rsegs.
Definition base := 0x527b4%Z.
Definition w_6 := 0x00013617%Z.
Definition w_7 := 0x20463483%Z.
Definition w_26 := 0x00045817%Z.
Definition w_27 := 0x76480913%Z.
Definition w_31 := 0xfffc4817%Z.
Definition w_32 := 0xd1080813%Z.
Definition w_93 := 0x00045697%Z.
Definition w_94 := 0x65868693%Z.
Definition w_245 := 0xc9cfe0ef%Z.
Definition hi_6 := (Z_to_bv 20 19).
Definition hi_26 := (Z_to_bv 20 69).
Definition hi_31 := (Z_to_bv 20 1048516).
Definition hi_93 := (Z_to_bv 20 69).
Definition lo_7 := (Z_to_bv 12 516).
Definition lo_27 := (Z_to_bv 12 1892).
Definition lo_32 := (Z_to_bv 12 3344).
Definition lo_94 := (Z_to_bv 12 1624).
Definition joff_245 := (Z_to_bv 21 2090140).
Definition e_197bc := 0x51024%Z.
Definition RATP := UKNz.RATP.
Definition RDEBRUIJN := UKNz.RDEBRUIJN.
Definition RGOT_SSP := UKNz.RGOT_SSP.
Definition RIMG_HI := UKNz.RIMG_HI.
Definition RDATA_LO := UKNz.RDATA_LO.
Definition gw_RTEXT_LO := ltac:(let gw_v_ := eval cbv in (fst (nth 1 UKNz.ref_reserved (0%Z, 0%Z))) in exact gw_v_).
Definition gw_RDATA2_LO := ltac:(let gw_v_ := eval cbv in (fst (nth 3 UKNz.ref_reserved (0%Z, 0%Z))) in exact gw_v_).
Definition ref_reserved := UKNz.ref_reserved.
Lemma CODE : CodeAt.code_at rsegs 0x527b4 (Qy8Z.Mq9.ntf_code 0x00013617%Z 0x20463483%Z 0x00045817%Z 0x76480913%Z 0xfffc4817%Z 0xd1080813%Z 0x00045697%Z 0x65868693%Z 0xc9cfe0ef%Z).  Proof. StepGen.code_at_vm. Qed.
Lemma BASE4 : (0x527b4 mod 4 = 0)%Z.  Proof. reflexivity. Qed.
Lemma BASER : (0 <= 0x527b4 /\ 0x527b4 + 984 <= 2^40)%Z.  Proof. vm_compute. split; discriminate. Qed.
Definition ref_find_segment_none := @UKNz.ref_find_segment_none.
Definition ref_ro_addr_false := @UKNz.ref_ro_addr_false.
Definition ref_memory_read_none := @UKNz.ref_memory_read_none.
Definition ref_wview_overlay := @UKNz.ref_wview_overlay.
Definition ref_seg_rom_none := @UKNz.ref_seg_rom_none.
Definition ref_mrd_overlay := @UKNz.ref_mrd_overlay.
Definition meta_word_pg := @U1ti.meta_word_pg.
Definition rget_meta_walk := ltac:(pose proof (@rget_meta_walk) as gw_h_; ltac2:(GwEqH.gw_rw_in @gw_h_ [[@gw_eq_rget_meta_post__3; @gw_eq_rget_meta_post__2; @gw_eq_rget_meta_post]; [@gw_eq_runlock_post__3; @gw_eq_runlock_post__2; @gw_eq_runlock_post]]); exact gw_h_).
Definition meta_word_sc2 := @U1ti.meta_word_sc2.
Lemma ROM_RSIZE_CLASSES : ltac2:(GwEq.gw_fact_ty 'segs '(@QZxv.Mqp.gw_all) @ROM_RSIZE_CLASSES). Proof. first [ apply QWxq.Mq0.ro_bytes_b_sound; vm_compute; reflexivity | GwApply.gw_side ]. Qed.
Lemma ROM_reservedZ : ltac2:(GwEq.gw_fact_ty 'segs '(@QZxv.Mqp.gw_all) @ROM_reservedZ). Proof. first [ apply QWxq.Mq0.ro_bytes_b_sound; vm_compute; reflexivity | GwApply.gw_side ]. Qed.
End GwI.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

Definition rntf_q (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
(st : mstate) (LB : list block) (Zs : list aptr) (lo : Z) (m o : word -> option byte)
(st' : mstate) (mi : mapinfo) : machine_state -> Prop :=
fun ms' => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc ra) fc None m' (seg_rom rsegs)
/\ mem_inv rsegs m' /\ stk rsegs m' lo (bv_unsigned sp) /\ rmrep st' m'
/\ rpres_except (rfree_fp st lo (bv_unsigned sp)) m m'
/\ (exists c, KINV st' LB c) /\ ZINV st' Zs /\ ntf_frame st st' /\ ntf_result st' mi a0 a1 /\ oracle_ok o m' st'.

Local Definition gwt_X : unit := (Q6nq.gwt_def (@Q8QT.Mq4.rshadow_rep) (@UQXM.rshadow_rep) (Q6nq.gwt_def (@QZxv.Mqp.rshadow_rep) (@UQXM.rshadow_rep) (Q6nq.gwt_def (@Q8QT.Mq4.rregions_wf) (@UQXM.rregions_wf) (Q6nq.gwt_def (@QZxv.Mqp.rregions_wf) (@UQXM.rregions_wf) (Q6nq.gwt_def (@QQRC.Mq9.rqpath_post) (@UUSO.rqpath_post) (Q6nq.gwt_def (@QZxv.Mqp.rqpath_post) (@UUSO.rqpath_post) (Q6nq.gwt_def (@QCa8.Mq5.rpres_except) (@Uv2Y.rpres_except) (Q6nq.gwt_def (@QZxv.Mqp.rpres_except) (@Uv2Y.rpres_except) (Q6nq.gwt_def (@QDXD.Mq2.rntf_ret_post) (@UIMz.rntf_ret_post) (Q6nq.gwt_def (@QZxv.Mqp.rntf_ret_post) (@UIMz.rntf_ret_post) (Q6nq.gwt_def (@Qy8Z.Mq9.rntf_frame) (@UlEO.rntf_frame) (Q6nq.gwt_def (@QZxv.Mqp.rntf_frame) (@UlEO.rntf_frame) (Q6nq.gwt_def (@QROt.Mq8.rnest_call_post) (@UjYE.rnest_call_post) (Q6nq.gwt_def (@QZxv.Mqp.rnest_call_post) (@UjYE.rnest_call_post) (Q6nq.gwt_def (@Q8QT.Mq4.rmrep_shadow) (@UQXM.rmrep_shadow) (Q6nq.gwt_def (@QZxv.Mqp.rmrep_shadow) (@UQXM.rmrep_shadow) (Q6nq.gwt_def (@Q8QT.Mq4.rmrep_groups) (@UQXM.rmrep_groups) (Q6nq.gwt_def (@QZxv.Mqp.rmrep_groups) (@UQXM.rmrep_groups) (Q6nq.gwt_def (@Q8QT.Mq4.rmrep_globals) (@UQXM.rmrep_globals) (Q6nq.gwt_def (@QZxv.Mqp.rmrep_globals) (@UQXM.rmrep_globals) (Q6nq.gwt_def (@Q8QT.Mq4.rmrep_ctx) (@UQXM.rmrep_ctx) (Q6nq.gwt_def (@QZxv.Mqp.rmrep_ctx) (@UQXM.rmrep_ctx) (Q6nq.gwt_def (@Q8QT.Mq4.rmrep_areas) (@UQXM.rmrep_areas) (Q6nq.gwt_def (@QZxv.Mqp.rmrep_areas) (@UQXM.rmrep_areas) (Q6nq.gwt_def (@Q8QT.Mq4.rmrep) (@UQXM.rmrep) (Q6nq.gwt_def (@QZxv.Mqp.rmrep) (@UQXM.rmrep) (Q6nq.gwt_def (@QCa8.Mq5.rimplT) (@Uv2Y.rimplT) (Q6nq.gwt_def (@QZxv.Mqp.rimplT) (@Uv2Y.rimplT) (Q6nq.gwt_def (@Q8QT.Mq4.rgroup_rep) (@UQXM.rgroup_rep) (Q6nq.gwt_def (@QZxv.Mqp.rgroup_rep) (@UQXM.rgroup_rep) (Q6nq.gwt_def (@QZxv.Mqp.rget_meta_post) (@UpkF.rget_meta_post) (Q6nq.gwt_def (@QCa8.Mq4.rget_meta_post) (@UpkF.rget_meta_post) (Q6nq.gwt_def (@QDXD.Mq2.rfree_fp) (@UIMz.rfree_fp) (Q6nq.gwt_def (@QZxv.Mqp.rfree_fp) (@UIMz.rfree_fp) (Q6nq.gwt_def (@QROt.Mq6.rfg_post) (@U9xa.rfg_post) (Q6nq.gwt_def (@QZxv.Mqp.rfg_post) (@U9xa.rfg_post) (Q6nq.gwt_def (@Q8l1.Mqa.rentry_post) (@UGig.rentry_post) (Q6nq.gwt_def (@QZxv.Mqp.rentry_post) (@UGig.rentry_post) (Q6nq.gwt_def (@Q8l1.Mqa.rentry_cases) (@UGig.rentry_cases) (Q6nq.gwt_def (@QZxv.Mqp.rentry_cases) (@UGig.rentry_cases) (Q6nq.gwt_def (@Q8l1.Mq9.rat9c_post) (@UlqM.rat9c_post) (Q6nq.gwt_def (@QZxv.Mqp.rat9c_post) (@UlqM.rat9c_post) (Q6nq.gwt_def (@Q8l1.Mq9.rat00_post) (@UlqM.rat00_post) (Q6nq.gwt_def (@QZxv.Mqp.rat00_post) (@UlqM.rat00_post) (Q6nq.gwt_def (@Q8QT.Mq4.rarea_rep) (@UQXM.rarea_rep) (Q6nq.gwt_def (@QZxv.Mqp.rarea_rep) (@UQXM.rarea_rep) (Q6nq.gwt_def (@Q8l1.Mqa.RAT) (@UGig.RAT) (Q6nq.gwt_def (@QZxv.Mqp.RAT) (@UGig.RAT) Q6nq.gwt_nil)))))))))))))))))))))))))))))))))))))))))))))))).
#[using="Type"] Lemma rpres_except_entry : ltac2:(Q6nq.ty2 'GwI.segs '(@QZxv.Mqp.rpres_except_entry) [[@gw_eq_rfree_fp__3; @gw_eq_rfree_fp__2; @gw_eq_rfree_fp]; [@gw_eq_rpres_except__3; @gw_eq_rpres_except__2; @gw_eq_rpres_except]] '([(-96)]%Z : list Z) '(Q6nq.gwt_def (@QZxv.Mqp.rntf_q) (@rntf_q) gwt_X)).
Proof. ltac2:(GwEq.gw_rw [[@gw_eq_rfree_fp__3; @gw_eq_rfree_fp__2; @gw_eq_rfree_fp]; [@gw_eq_rpres_except__3; @gw_eq_rpres_except__2; @gw_eq_rpres_except]]); first [GwApply2.gw_by_name2 GwI.segs (@QZxv.Mqp.rpres_except_entry) | autorewrite with gw_eqs; GwApply2.gw_by_name2 GwI.segs (@QZxv.Mqp.rpres_except_entry)]. Qed.

#[using="Type"] Lemma roracle_ok_pres : ltac2:(Q6nq.ty2 'GwI.segs '(@QZxv.Mqp.roracle_ok_pres) [[@gw_eq_rfree_fp__3; @gw_eq_rfree_fp__2; @gw_eq_rfree_fp]; [@gw_eq_rmrep__3; @gw_eq_rmrep__2; @gw_eq_rmrep]; [@gw_eq_rpres_except__3; @gw_eq_rpres_except__2; @gw_eq_rpres_except]] '(@nil Z) '(Q6nq.gwt_def (@QZxv.Mqp.rntf_q) (@rntf_q) gwt_X)).
Proof. ltac2:(GwEq.gw_rw [[@gw_eq_rfree_fp__3; @gw_eq_rfree_fp__2; @gw_eq_rfree_fp]; [@gw_eq_rmrep__3; @gw_eq_rmrep__2; @gw_eq_rmrep]; [@gw_eq_rpres_except__3; @gw_eq_rpres_except__2; @gw_eq_rpres_except]]); first [GwApply2.gw_by_name2 GwI.segs (@QZxv.Mqp.roracle_ok_pres) | autorewrite with gw_eqs; GwApply2.gw_by_name2 GwI.segs (@QZxv.Mqp.roracle_ok_pres)]. Qed.

#[using="Type"] Lemma rfree_fp_frame st st' lo (sp sp' : Z) a : ntf_frame st st' -> sp' <= sp -> rfree_fp st' lo sp' a -> rfree_fp st lo sp a.
Proof. ltac2:(GwEq.gw_rw [[@gw_eq_rfree_fp__3; @gw_eq_rfree_fp__2; @gw_eq_rfree_fp]]); first [GwApply2.gw_by_name2 GwI.segs (@QZxv.Mqp.rfree_fp_frame) | autorewrite with gw_eqs; GwApply2.gw_by_name2 GwI.segs (@QZxv.Mqp.rfree_fp_frame)]. Qed.

#[using="Type"] Lemma rfree_fp_same : ltac2:(Q6nq.ty2 'GwI.segs '(@QZxv.Mqp.rfree_fp_same) [[@gw_eq_rfree_fp__3; @gw_eq_rfree_fp__2; @gw_eq_rfree_fp]] '(@nil Z) '(Q6nq.gwt_def (@QZxv.Mqp.rntf_q) (@rntf_q) gwt_X)).
Proof. ltac2:(GwEq.gw_rw [[@gw_eq_rfree_fp__3; @gw_eq_rfree_fp__2; @gw_eq_rfree_fp]]); first [GwApply2.gw_by_name2 GwI.segs (@QZxv.Mqp.rfree_fp_same) | autorewrite with gw_eqs; GwApply2.gw_by_name2 GwI.segs (@QZxv.Mqp.rfree_fp_same)]. Qed.

#[using="Type"] Lemma rfree_fp_lt st mw lo (sp : Z) a : rmrep st mw -> alloc_ceiling <= lo -> lo <= sp -> rfree_fp st lo sp a -> a < sp.
Proof. ltac2:(GwEq.gw_rw [[@gw_eq_rfree_fp__3; @gw_eq_rfree_fp__2; @gw_eq_rfree_fp]; [@gw_eq_rmrep__3; @gw_eq_rmrep__2; @gw_eq_rmrep]]); first [GwApply2.gw_by_name2 GwI.segs (@QZxv.Mqp.rfree_fp_lt) | autorewrite with gw_eqs; GwApply2.gw_by_name2 GwI.segs (@QZxv.Mqp.rfree_fp_lt)]. Qed.

#[using="Type"] Lemma rknown_byte : ltac2:(Q6nq.ty2 'GwI.segs '(@QZxv.Mqp.rknown_byte) [[@gw_eq_rmrep__3; @gw_eq_rmrep__2; @gw_eq_rmrep]] '(@nil Z) '(Q6nq.gwt_def (@QZxv.Mqp.rntf_q) (@rntf_q) gwt_X)).
Proof. ltac2:(GwEq.gw_rw [[@gw_eq_rmrep__3; @gw_eq_rmrep__2; @gw_eq_rmrep]]); first [GwApply2.gw_by_name2 GwI.segs (@QZxv.Mqp.rknown_byte) | autorewrite with gw_eqs; GwApply2.gw_by_name2 GwI.segs (@QZxv.Mqp.rknown_byte)]. Qed.

#[using="Type"] Lemma rimplT_queue {R} o h g st0 (k : mstate -> QUZl.M R) bail s Q ms :
(m_next (get_meta_rec st0 g) = None -> m_prev (get_meta_rec st0 g) = None -> rimplT o (k (queue_st h g st0)) s Q ms) ->
rimplT o (queue h g st0 k bail) s Q ms.
Proof. ltac2:(GwEq.gw_rw [[@gw_eq_rimplT__3; @gw_eq_rimplT__2; @gw_eq_rimplT]]); first [GwApply2.gw_by_name2 GwI.segs (@QZxv.Mqp.rimplT_queue) | autorewrite with gw_eqs; GwApply2.gw_by_name2 GwI.segs (@QZxv.Mqp.rimplT_queue)]. Qed.

#[using="Type"] Lemma rntf_frame_size junk (s3 s2 s1 s0 ra : word) : cells_size (rntf_frame junk s3 s2 s1 s0 ra) = 96%nat.
Proof. ltac2:(GwEq.gw_rw [[@gw_eq_rntf_frame__3; @gw_eq_rntf_frame__2; @gw_eq_rntf_frame]]); first [GwApply2.gw_by_name2 GwI.segs (@QZxv.Mqp.rntf_frame_size) | autorewrite with gw_eqs; GwApply2.gw_by_name2 GwI.segs (@QZxv.Mqp.rntf_frame_size)]. Qed.

Section NTF.
Variables (gp tp s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32).
Variables (o : word -> option byte) (LB : list block) (lo : Z).
Hypothesis LO : alloc_ceiling <= lo.

#[using="LO"] Lemma rntf_q_intro : ltac2:(Q6nq.ty2 'GwI.segs '(@QZxv.Mqp.rntf_q_intro) [[@gw_eq_rfree_fp__3; @gw_eq_rfree_fp__2; @gw_eq_rfree_fp]; [@gw_eq_rmrep__3; @gw_eq_rmrep__2; @gw_eq_rmrep]; [@gw_eq_rntf_ret_post__3; @gw_eq_rntf_ret_post__2; @gw_eq_rntf_ret_post]; [@gw_eq_rpres_except__3; @gw_eq_rpres_except__2; @gw_eq_rpres_except]] '(@nil Z) '(Q6nq.gwt_def (@QZxv.Mqp.rntf_q) (@rntf_q) gwt_X)).
Proof. ltac2:(GwEq.gw_rw [[@gw_eq_rfree_fp__3; @gw_eq_rfree_fp__2; @gw_eq_rfree_fp]; [@gw_eq_rmrep__3; @gw_eq_rmrep__2; @gw_eq_rmrep]; [@gw_eq_rntf_ret_post__3; @gw_eq_rntf_ret_post__2; @gw_eq_rntf_ret_post]; [@gw_eq_rpres_except__3; @gw_eq_rpres_except__2; @gw_eq_rpres_except]]); first [GwApply2.gw_by_name2 GwI.segs (@QZxv.Mqp.rntf_q_intro) | autorewrite with gw_eqs; GwApply2.gw_by_name2 GwI.segs (@QZxv.Mqp.rntf_q_intro)]. Qed.

#[using="LO"] Theorem rntf_implT : forall (fuel : nat) (R : Type) (k : mstate -> mapinfo -> QUZl.M R) (bail : QUZl.M R)
(s : PState) (Q : R -> PState -> machine_state -> Prop)
(ra sp s0 s1 s2 s3 t0 t1 t2 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m : word -> option byte)
(st : mstate) (g p : aptr) (i c : Z) (Zs : list aptr),
KINV st LB c -> LPRE st LB c g p i -> ZINV st Zs ->
rmrep st m -> mem_inv rsegs m -> oracle_ok o m st ->
stk rsegs m lo (bv_unsigned sp) -> lo + 96 * Z.of_nat fuel <= bv_unsigned sp ->
(forall st' mi ms', rntf_q ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc st LB Zs lo m o st' mi ms' -> rimplT o (k st' mi) s Q ms') ->
rimplT o (nontrivial_free dec_hdr fuel st g i k bail) s Q
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (conc st g)) (Z_to_bv 64 i) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0x527b4) fc None m (seg_rom rsegs)).
Proof. ltac2:(GwEq.gw_rw [[@gw_eq_rimplT__3; @gw_eq_rimplT__2; @gw_eq_rimplT]; [@gw_eq_rmrep__3; @gw_eq_rmrep__2; @gw_eq_rmrep]]); first [GwApply2.gw_by_name2 GwI.segs (@QZxv.Mqp.rntf_implT) | autorewrite with gw_eqs; GwApply2.gw_by_name2 GwI.segs (@QZxv.Mqp.rntf_implT)]. Qed.
End NTF.

End RC__1.
