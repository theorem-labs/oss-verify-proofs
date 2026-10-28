(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)


From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib Require CodeAt StepGen GwInst GwEq GwApply GwApply2. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Q6nq.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QSsB.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UKNz.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require Unip.

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
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qy5Y.Mq4. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Q4J3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q4J3.Mq3. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QPjm.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QPjm.Mq4.
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
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q6y7.Mq2. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QNAo.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QNAo.Mq1.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UQXM.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UQXM. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require Uv2Y.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Uv2Y. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UpkF.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UpkF. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UIMz.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UIMz. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require Un7h.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Un7h. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require U8FW.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import U8FW. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UDxd.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UDxd. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UiOj.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UiOj. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UJOB.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UJOB. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UWfR.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UWfR. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UznK.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UznK. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require U7Ti.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import U7Ti. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UAr0.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UAr0. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UwoZ.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UwoZ. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UXT6.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UXT6. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UOpO.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UOpO. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require Unip.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Unip.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Q3o5. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QTyG.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Qatc.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import QlEo.Mq0.Exc. Local Ltac Qfw3.Mq3.model_reg_tac n X mexpr ::= Qfw3.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Qfw3.Mq3.zeq_fast ::= Qfw3.Mq3.mkr__zeq_fast_0.
Open Scope Z_scope.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Q6q3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q6q3.

From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib Require CodeAt StepGen GwInst GwApply GwApply2.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module GwI.
Definition segs := rsegs.
Definition RATP := UKNz.RATP.
Definition RDEBRUIJN := UKNz.RDEBRUIJN.
Definition RGOT_SSP := UKNz.RGOT_SSP.
Definition RIMG_HI := UKNz.RIMG_HI.
Definition RDATA_LO := UKNz.RDATA_LO.
Definition gw_RTEXT_LO := ltac:(let gw_v_ := eval cbv in (fst (nth 1 UKNz.ref_reserved (0%Z, 0%Z))) in exact gw_v_).
Definition gw_RDATA2_LO := ltac:(let gw_v_ := eval cbv in (fst (nth 3 UKNz.ref_reserved (0%Z, 0%Z))) in exact gw_v_).
Definition ref_reserved := UKNz.ref_reserved.
Definition rmalloc_sym := UKNz.rmalloc_sym.
Definition rmalloc_entry := UKNz.rmalloc_entry.
Definition ralloc_slot_entry := UKNz.ralloc_slot_entry.
Definition ref_find_segment_none := @UKNz.ref_find_segment_none.
Definition ref_ro_addr_false := @UKNz.ref_ro_addr_false.
Definition ref_memory_read_none := @UKNz.ref_memory_read_none.
Definition ref_wview_overlay := @UKNz.ref_wview_overlay.
Definition ref_seg_rom_none := @UKNz.ref_seg_rom_none.
Definition ref_mrd_overlay := @UKNz.ref_mrd_overlay.
Definition renf_implT := @renf_implT.
Definition rmalloc_fp_cases := @rmalloc_fp_cases.
Definition rmalloc_fp_image := @rmalloc_fp_image.
Definition rauxv_ok_malloc_fp := @rauxv_ok_malloc_fp.
Definition rmalloc_core_implT := @rmalloc_core_implT.
Definition rmalloc_stmt_of_impl := @Unip.rmalloc_stmt_of_impl.
End GwI.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

Local Definition gwt_X : unit := (Q6nq.gwt_def (@Q8QT.Mq4.rshadow_rep) (@UQXM.rshadow_rep) (Q6nq.gwt_def (@QSsB.rshadow_rep) (@UQXM.rshadow_rep) (Q6nq.gwt_def (@Q8QT.Mq4.rregions_wf) (@UQXM.rregions_wf) (Q6nq.gwt_def (@QSsB.rregions_wf) (@UQXM.rregions_wf) (Q6nq.gwt_def (@QCa8.Mq5.rpres_except) (@Uv2Y.rpres_except) (Q6nq.gwt_def (@QSsB.rpres_except) (@Uv2Y.rpres_except) (Q6nq.gwt_def (@Q8QT.Mq4.rmrep_shadow) (@UQXM.rmrep_shadow) (Q6nq.gwt_def (@QSsB.rmrep_shadow) (@UQXM.rmrep_shadow) (Q6nq.gwt_def (@Q8QT.Mq4.rmrep_groups) (@UQXM.rmrep_groups) (Q6nq.gwt_def (@QSsB.rmrep_groups) (@UQXM.rmrep_groups) (Q6nq.gwt_def (@Q8QT.Mq4.rmrep_globals) (@UQXM.rmrep_globals) (Q6nq.gwt_def (@QSsB.rmrep_globals) (@UQXM.rmrep_globals) (Q6nq.gwt_def (@Q8QT.Mq4.rmrep_ctx) (@UQXM.rmrep_ctx) (Q6nq.gwt_def (@QSsB.rmrep_ctx) (@UQXM.rmrep_ctx) (Q6nq.gwt_def (@Q8QT.Mq4.rmrep_areas) (@UQXM.rmrep_areas) (Q6nq.gwt_def (@QSsB.rmrep_areas) (@UQXM.rmrep_areas) (Q6nq.gwt_def (@Q8QT.Mq4.rmrep) (@UQXM.rmrep) (Q6nq.gwt_def (@QSsB.rmrep) (@UQXM.rmrep) (Q6nq.gwt_def (@QDXD.Mq3.rmalloc_stmt) (@UXT6.rmalloc_stmt) (Q6nq.gwt_def (@QSsB.rmalloc_stmt) (@UXT6.rmalloc_stmt) (Q6nq.gwt_def (@QDXD.Mq3.rmalloc_post) (@UXT6.rmalloc_post) (Q6nq.gwt_def (@QSsB.rmalloc_post) (@UXT6.rmalloc_post) (Q6nq.gwt_def (@QkTt.Mq6.rmalloc_impl_stmt) (@Unip.rmalloc_impl_stmt) (Q6nq.gwt_def (@QSsB.rmalloc_impl_stmt) (@Unip.rmalloc_impl_stmt) (Q6nq.gwt_def (@QkTt.Mq5.rmalloc_fp) (@UDxd.rmalloc_fp) (Q6nq.gwt_def (@QSsB.rmalloc_fp) (@UDxd.rmalloc_fp) (Q6nq.gwt_def (@QCa8.Mq5.rimplT) (@Uv2Y.rimplT) (Q6nq.gwt_def (@QSsB.rimplT) (@Uv2Y.rimplT) (Q6nq.gwt_def (@QDXD.Mq3.rheap_pres) (@UXT6.rheap_pres) (Q6nq.gwt_def (@QSsB.rheap_pres) (@UXT6.rheap_pres) (Q6nq.gwt_def (@Q8QT.Mq4.rgroup_rep) (@UQXM.rgroup_rep) (Q6nq.gwt_def (@QSsB.rgroup_rep) (@UQXM.rgroup_rep) (Q6nq.gwt_def (@QSsB.renf_post) (@UJOB.renf_post) (Q6nq.gwt_def (@Qy8Z.Mq7.renf_post) (@UJOB.renf_post) (Q6nq.gwt_def (@QSsB.rcoreQ) (@UwoZ.rcoreQ) (Q6nq.gwt_def (@QROt.Mq5.rcoreQ) (@UwoZ.rcoreQ) (Q6nq.gwt_def (@QDXD.Mq3.rclient_addr) (@UXT6.rclient_addr) (Q6nq.gwt_def (@QSsB.rclient_addr) (@UXT6.rclient_addr) (Q6nq.gwt_def (@QDXD.Mq3.rblock_range) (@UXT6.rblock_range) (Q6nq.gwt_def (@QSsB.rblock_range) (@UXT6.rblock_range) (Q6nq.gwt_def (@QSsB.rbig_stmt) (@UwoZ.rbig_stmt) (Q6nq.gwt_def (@QROt.Mq5.rbig_stmt) (@UwoZ.rbig_stmt) (Q6nq.gwt_def (@QCa8.Mq5.rauxv_ok) (@Uv2Y.rauxv_ok) (Q6nq.gwt_def (@QSsB.rauxv_ok) (@Uv2Y.rauxv_ok) (Q6nq.gwt_def (@QSsB.ras_post) (@UWfR.ras_post) (Q6nq.gwt_def (@Qy8Z.Mq1.ras_post) (@UWfR.ras_post) (Q6nq.gwt_def (@Q8QT.Mq4.rarea_rep) (@UQXM.rarea_rep) (Q6nq.gwt_def (@QSsB.rarea_rep) (@UQXM.rarea_rep) (Q6nq.gwt_def (@QDXD.Mq3.ralloc_static) (@UXT6.ralloc_static) (Q6nq.gwt_def (@QSsB.ralloc_static) (@UXT6.ralloc_static) (Q6nq.gwt_def (@QSsB.ralloc_slot_stmt) (@UWfR.ralloc_slot_stmt) (Q6nq.gwt_def (@Qy8Z.Mq1.ralloc_slot_stmt) (@UWfR.ralloc_slot_stmt) (Q6nq.gwt_def (@QCa8.Mq5.ralloc_fp) (@Uv2Y.ralloc_fp) (Q6nq.gwt_def (@QSsB.ralloc_fp) (@Uv2Y.ralloc_fp) (Q6nq.gwt_def (@QDXD.Mq3.raddr_exposed) (@UXT6.raddr_exposed) (Q6nq.gwt_def (@QSsB.raddr_exposed) (@UXT6.raddr_exposed) (Q6nq.gwt_def (@QDXD.Mq3.RMALLOC_SYM) (@UXT6.RMALLOC_SYM) (Q6nq.gwt_def (@QSsB.RMALLOC_SYM) (@UXT6.RMALLOC_SYM) (Q6nq.gwt_def (@QDXD.Mq3.RHEAP) (@UXT6.RHEAP) (Q6nq.gwt_def (@QSsB.RHEAP) (@UXT6.RHEAP) Q6nq.gwt_nil)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))).
#[using="Type"] Lemma rmembed_strel_follow : ltac2:(Q6nq.ty2 'GwI.segs '(@QSsB.rmembed_strel_follow) [] '(@nil Z) 'gwt_X).
Proof. first [GwApply2.gw_by_name2 GwI.segs (@QSsB.rmembed_strel_follow) | autorewrite with gw_eqs; GwApply2.gw_by_name2 GwI.segs (@QSsB.rmembed_strel_follow)]. Qed.

#[using="Type"] Lemma rraw_malloc_bridge2 : ltac2:(Q6nq.ty2 'GwI.segs '(@QSsB.rraw_malloc_bridge2) [[@gw_eq_rimplT__3; @gw_eq_rimplT__2; @gw_eq_rimplT]] '(@nil Z) 'gwt_X).
Proof. ltac2:(GwEq.gw_rw [[@gw_eq_rimplT__3; @gw_eq_rimplT__2; @gw_eq_rimplT]]); first [GwApply2.gw_by_name2 GwI.segs (@QSsB.rraw_malloc_bridge2) | autorewrite with gw_eqs; GwApply2.gw_by_name2 GwI.segs (@QSsB.rraw_malloc_bridge2)]. Qed.

#[using="Type"] Lemma rimplT_silent {R} o (t : QUZl.M R) o' (x : R) s Q ms :
mrun o t = SRet (o', x) -> rimplT o t s Q ms -> evt rsegs (Q x s) ms.
Proof. ltac2:(GwEq.gw_rw [[@gw_eq_rimplT__3; @gw_eq_rimplT__2; @gw_eq_rimplT]]); first [GwApply2.gw_by_name2 GwI.segs (@QSsB.rimplT_silent) | autorewrite with gw_eqs; GwApply2.gw_by_name2 GwI.segs (@QSsB.rimplT_silent)]. Qed.

#[using="Type"] Lemma rheap_pres_of_fp : ltac2:(Q6nq.ty2 'GwI.segs '(@QSsB.rheap_pres_of_fp) [[@gw_eq_rheap_pres__3; @gw_eq_rheap_pres__2; @gw_eq_rheap_pres]; [@gw_eq_rmalloc_fp__3; @gw_eq_rmalloc_fp__2; @gw_eq_rmalloc_fp]; [@gw_eq_rmrep__3; @gw_eq_rmrep__2; @gw_eq_rmrep]; [@gw_eq_rpres_except__3; @gw_eq_rpres_except__2; @gw_eq_rpres_except]] '(@nil Z) '(Q6nq.gwt_pat (@ref_reserved) (@ref_reserved) (Q6nq.gwt_hdr GwI.ref_reserved (@ref_reserved) gwt_X))).
Proof. ltac2:(GwEq.gw_rw [[@gw_eq_rheap_pres__3; @gw_eq_rheap_pres__2; @gw_eq_rheap_pres]; [@gw_eq_rmalloc_fp__3; @gw_eq_rmalloc_fp__2; @gw_eq_rmalloc_fp]; [@gw_eq_rmrep__3; @gw_eq_rmrep__2; @gw_eq_rmrep]; [@gw_eq_rpres_except__3; @gw_eq_rpres_except__2; @gw_eq_rpres_except]]); first [GwApply2.gw_by_name2 GwI.segs (@QSsB.rheap_pres_of_fp) | autorewrite with gw_eqs; GwApply2.gw_by_name2 GwI.segs (@QSsB.rheap_pres_of_fp)]. Qed.

#[using="Type"] Lemma ruser_chunk : ltac2:(Q6nq.ty2 'GwI.segs '(@QSsB.ruser_chunk) [[@gw_eq_rmrep__3; @gw_eq_rmrep__2; @gw_eq_rmrep]] '(@nil Z) 'gwt_X).
Proof. ltac2:(GwEq.gw_rw [[@gw_eq_rmrep__3; @gw_eq_rmrep__2; @gw_eq_rmrep]]); first [GwApply2.gw_by_name2 GwI.segs (@QSsB.ruser_chunk) | autorewrite with gw_eqs; GwApply2.gw_by_name2 GwI.segs (@QSsB.ruser_chunk)]. Qed.

Definition malloc_core_allzero_stmt : Prop :=
forall st L BL LS n (o : mem) ans (o' : mem) st1 g idx,
Qatc.INVL Qatc.x0 st L BL LS -> 0 <= n ->
follow (mrun o (malloc_core full_lay (set_tick (N.succ (s_tick st)) st) n)) ans = Some (o', (st1, Some (g, idx))) ->
is_allzero_ctrl (Qatc.MR st1 g) = true ->
exists bg, m_mem (Qatc.MR st1 g) = Some bg /\
forall k, 0 <= k < get_stride (Qatc.MR st1 g) - IB ->
cell_read (get_shadow st1 (fst bg)) (Qatc.sstart (Qatc.MR st1 g) idx + k) = Known 0.

#[using="Type"] Lemma bytes_at_inj0 m a bs bs' : bytes_at rsegs m a bs -> bytes_at rsegs m a bs' -> length bs = length bs' -> bs = bs'.
Proof. first [GwApply2.gw_by_name2 GwI.segs (@QSsB.bytes_at_inj0) | autorewrite with gw_eqs; GwApply2.gw_by_name2 GwI.segs (@QSsB.bytes_at_inj0)]. Qed.

#[using="Type"] Lemma rzeros_of_shadow : ltac2:(Q6nq.ty2 'GwI.segs '(@QSsB.rzeros_of_shadow) [[@gw_eq_rmrep__3; @gw_eq_rmrep__2; @gw_eq_rmrep]] '(@nil Z) '(Q6nq.gwt_def (@QSsB.malloc_core_allzero_stmt) (@malloc_core_allzero_stmt) gwt_X)).
Proof. ltac2:(GwEq.gw_rw [[@gw_eq_rmrep__3; @gw_eq_rmrep__2; @gw_eq_rmrep]]); first [GwApply2.gw_by_name2 GwI.segs (@QSsB.rzeros_of_shadow) | autorewrite with gw_eqs; GwApply2.gw_by_name2 GwI.segs (@QSsB.rzeros_of_shadow)]. Qed.

Section TOPLEVEL.
Variables (as_pre : mstate -> mstate -> Z -> Z -> nat -> Prop) (as_inv : mstate -> mstate -> mstate -> Z -> Z -> Prop).
Hypothesis RAS : ralloc_slot_stmt as_pre as_inv.
Hypothesis MCZ : malloc_core_allzero_stmt.
Hypothesis AS_PRE : forall st LB t sc n, RAREACH st LB -> RMFACTS st LB -> (s_tick st < t)%N -> 0 <= sc < 48 -> 0 <= n < 2^32 ->
n + 4 <= 16 * size_class sc -> as_pre st (set_tick t st) sc n FUEL.
Hypothesis RBIG : rbig_stmt.

Definition rmidQ (o : mem) (st : mstate) (LB : list block) (s : PState)
(ra sp gp tp s5 s6 s7 s8 s9 s10 s11 s0v s1v s2v s3v s4v : word) (F : bvmap 5 word) (fc : bv 32) (n lo : Z)
(res : mstate * option cptr) (s' : PState) (ms' : machine_state) : Prop :=
exists st2 r ans o1,
fst res = strip st2
/\ snd res = match r with Some (g, idx) => Some (slot_of st2 g idx) | None => None end
/\ follow (mrun o (malloc_core full_lay (set_tick (N.succ (s_tick st)) st) n)) ans = Some (o1, (st2, r))
/\ follow (malloc_core lay_none (strip st) n) ans = Some (strip st2, r)
/\ rcoreQ o o st s ra sp gp tp s5 s6 s7 s8 s9 s10 s11 s0v s1v s2v s3v s4v F fc n lo (st2, r) s' ms'.

#[using="as_pre as_inv RAS MCZ AS_PRE RBIG"] Theorem rmalloc_impl_spec_proof : rmalloc_impl_stmt.
Proof. ltac2:(GwEq.gw_rw [[@gw_eq_rmalloc_impl_stmt__3; @gw_eq_rmalloc_impl_stmt__2; @gw_eq_rmalloc_impl_stmt]]); first [GwApply2.gw_by_name2 GwI.segs (@QSsB.rmalloc_impl_spec_proof) | autorewrite with gw_eqs; GwApply2.gw_by_name2 GwI.segs (@QSsB.rmalloc_impl_spec_proof)]. Qed.

#[using="as_pre as_inv RAS MCZ AS_PRE RBIG"] Theorem rmalloc_spec_proof : rmalloc_stmt.
Proof. ltac2:(GwEq.gw_rw [[@gw_eq_rmalloc_stmt__3; @gw_eq_rmalloc_stmt__2; @gw_eq_rmalloc_stmt]]); first [GwApply2.gw_by_name2 GwI.segs (@QSsB.rmalloc_spec_proof) | autorewrite with gw_eqs; GwApply2.gw_by_name2 GwI.segs (@QSsB.rmalloc_spec_proof)]. Qed.

End TOPLEVEL.

End RC__1.
