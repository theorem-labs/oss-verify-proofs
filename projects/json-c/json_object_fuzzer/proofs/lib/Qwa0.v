(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)


From OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib Require CodeAt StepGen GwInst GwEq GwApply GwApply2. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q6nq.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QSsB.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QKNz.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qnip.

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
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qy5Y.Mq4. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q4J3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q4J3.Mq3. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QPjm.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QPjm.Mq4.
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
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q6y7.Mq2. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QNAo.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QNAo.Mq1.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QQXM.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QQXM. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qv2Y.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qv2Y. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QpkF.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QpkF. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QIMz.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QIMz. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qn7h.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qn7h. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q8FW.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q8FW. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QDxd_c1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QDxd_c1. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QiOj.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QiOj. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QJOB.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QJOB. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QWfR.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QWfR. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QznK.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QznK. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q7Ti.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q7Ti. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QAr0.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QAr0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QwoZ.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QwoZ. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QXT6.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QXT6. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QOpO.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QOpO. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qnip.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qnip.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q3o5. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QTyG.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qatc.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import QlEo_c1.Mq0.Exc. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0.
Open Scope Z_scope.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q6q3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q6q3.

From OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib Require CodeAt StepGen GwInst GwApply GwApply2.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module GwI.
Definition segs := rsegs.
Definition RATP := QKNz.RATP.
Definition RDEBRUIJN := QKNz.RDEBRUIJN.
Definition RGOT_SSP := QKNz.RGOT_SSP.
Definition RIMG_HI := QKNz.RIMG_HI.
Definition RDATA_LO := QKNz.RDATA_LO.
Definition gw_RTEXT_LO := ltac:(let gw_v_ := eval cbv in (fst (nth 1 QKNz.ref_reserved (0%Z, 0%Z))) in exact gw_v_).
Definition gw_RDATA2_LO := ltac:(let gw_v_ := eval cbv in (fst (nth 3 QKNz.ref_reserved (0%Z, 0%Z))) in exact gw_v_).
Definition ref_reserved := QKNz.ref_reserved.
Definition rmalloc_sym := QKNz.rmalloc_sym.
Definition rmalloc_entry := QKNz.rmalloc_entry.
Definition ralloc_slot_entry := QKNz.ralloc_slot_entry.
Definition ref_find_segment_none := @QKNz.ref_find_segment_none.
Definition ref_ro_addr_false := @QKNz.ref_ro_addr_false.
Definition ref_memory_read_none := @QKNz.ref_memory_read_none.
Definition ref_wview_overlay := @QKNz.ref_wview_overlay.
Definition ref_seg_rom_none := @QKNz.ref_seg_rom_none.
Definition ref_mrd_overlay := @QKNz.ref_mrd_overlay.
Definition renf_implT := @renf_implT.
Definition rmalloc_fp_cases := @rmalloc_fp_cases.
Definition rmalloc_fp_image := @rmalloc_fp_image.
Definition rauxv_ok_malloc_fp := @rauxv_ok_malloc_fp.
Definition rmalloc_core_implT := @rmalloc_core_implT.
Definition rmalloc_stmt_of_impl := @Qnip.rmalloc_stmt_of_impl.
End GwI.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

Local Definition gwt_X : unit := (Q6nq.gwt_def (@Q8QT.Mq4.rshadow_rep) (@QQXM.rshadow_rep) (Q6nq.gwt_def (@QSsB.rshadow_rep) (@QQXM.rshadow_rep) (Q6nq.gwt_def (@Q8QT.Mq4.rregions_wf) (@QQXM.rregions_wf) (Q6nq.gwt_def (@QSsB.rregions_wf) (@QQXM.rregions_wf) (Q6nq.gwt_def (@QCa8.Mq5.rpres_except) (@Qv2Y.rpres_except) (Q6nq.gwt_def (@QSsB.rpres_except) (@Qv2Y.rpres_except) (Q6nq.gwt_def (@Q8QT.Mq4.rmrep_shadow) (@QQXM.rmrep_shadow) (Q6nq.gwt_def (@QSsB.rmrep_shadow) (@QQXM.rmrep_shadow) (Q6nq.gwt_def (@Q8QT.Mq4.rmrep_groups) (@QQXM.rmrep_groups) (Q6nq.gwt_def (@QSsB.rmrep_groups) (@QQXM.rmrep_groups) (Q6nq.gwt_def (@Q8QT.Mq4.rmrep_globals) (@QQXM.rmrep_globals) (Q6nq.gwt_def (@QSsB.rmrep_globals) (@QQXM.rmrep_globals) (Q6nq.gwt_def (@Q8QT.Mq4.rmrep_ctx) (@QQXM.rmrep_ctx) (Q6nq.gwt_def (@QSsB.rmrep_ctx) (@QQXM.rmrep_ctx) (Q6nq.gwt_def (@Q8QT.Mq4.rmrep_areas) (@QQXM.rmrep_areas) (Q6nq.gwt_def (@QSsB.rmrep_areas) (@QQXM.rmrep_areas) (Q6nq.gwt_def (@Q8QT.Mq4.rmrep) (@QQXM.rmrep) (Q6nq.gwt_def (@QSsB.rmrep) (@QQXM.rmrep) (Q6nq.gwt_def (@QDXD.Mq3.rmalloc_stmt) (@QXT6.rmalloc_stmt) (Q6nq.gwt_def (@QSsB.rmalloc_stmt) (@QXT6.rmalloc_stmt) (Q6nq.gwt_def (@QDXD.Mq3.rmalloc_post) (@QXT6.rmalloc_post) (Q6nq.gwt_def (@QSsB.rmalloc_post) (@QXT6.rmalloc_post) (Q6nq.gwt_def (@QkTt.Mq6.rmalloc_impl_stmt) (@Qnip.rmalloc_impl_stmt) (Q6nq.gwt_def (@QSsB.rmalloc_impl_stmt) (@Qnip.rmalloc_impl_stmt) (Q6nq.gwt_def (@QkTt.Mq5.rmalloc_fp) (@QDxd_c1.rmalloc_fp) (Q6nq.gwt_def (@QSsB.rmalloc_fp) (@QDxd_c1.rmalloc_fp) (Q6nq.gwt_def (@QCa8.Mq5.rimplT) (@Qv2Y.rimplT) (Q6nq.gwt_def (@QSsB.rimplT) (@Qv2Y.rimplT) (Q6nq.gwt_def (@QDXD.Mq3.rheap_pres) (@QXT6.rheap_pres) (Q6nq.gwt_def (@QSsB.rheap_pres) (@QXT6.rheap_pres) (Q6nq.gwt_def (@Q8QT.Mq4.rgroup_rep) (@QQXM.rgroup_rep) (Q6nq.gwt_def (@QSsB.rgroup_rep) (@QQXM.rgroup_rep) (Q6nq.gwt_def (@QSsB.renf_post) (@QJOB.renf_post) (Q6nq.gwt_def (@Qy8Z.Mq7.renf_post) (@QJOB.renf_post) (Q6nq.gwt_def (@QSsB.rcoreQ) (@QwoZ.rcoreQ) (Q6nq.gwt_def (@QROt.Mq5.rcoreQ) (@QwoZ.rcoreQ) (Q6nq.gwt_def (@QDXD.Mq3.rclient_addr) (@QXT6.rclient_addr) (Q6nq.gwt_def (@QSsB.rclient_addr) (@QXT6.rclient_addr) (Q6nq.gwt_def (@QDXD.Mq3.rblock_range) (@QXT6.rblock_range) (Q6nq.gwt_def (@QSsB.rblock_range) (@QXT6.rblock_range) (Q6nq.gwt_def (@QSsB.rbig_stmt) (@QwoZ.rbig_stmt) (Q6nq.gwt_def (@QROt.Mq5.rbig_stmt) (@QwoZ.rbig_stmt) (Q6nq.gwt_def (@QCa8.Mq5.rauxv_ok) (@Qv2Y.rauxv_ok) (Q6nq.gwt_def (@QSsB.rauxv_ok) (@Qv2Y.rauxv_ok) (Q6nq.gwt_def (@QSsB.ras_post) (@QWfR.ras_post) (Q6nq.gwt_def (@Qy8Z.Mq1.ras_post) (@QWfR.ras_post) (Q6nq.gwt_def (@Q8QT.Mq4.rarea_rep) (@QQXM.rarea_rep) (Q6nq.gwt_def (@QSsB.rarea_rep) (@QQXM.rarea_rep) (Q6nq.gwt_def (@QDXD.Mq3.ralloc_static) (@QXT6.ralloc_static) (Q6nq.gwt_def (@QSsB.ralloc_static) (@QXT6.ralloc_static) (Q6nq.gwt_def (@QSsB.ralloc_slot_stmt) (@QWfR.ralloc_slot_stmt) (Q6nq.gwt_def (@Qy8Z.Mq1.ralloc_slot_stmt) (@QWfR.ralloc_slot_stmt) (Q6nq.gwt_def (@QCa8.Mq5.ralloc_fp) (@Qv2Y.ralloc_fp) (Q6nq.gwt_def (@QSsB.ralloc_fp) (@Qv2Y.ralloc_fp) (Q6nq.gwt_def (@QDXD.Mq3.raddr_exposed) (@QXT6.raddr_exposed) (Q6nq.gwt_def (@QSsB.raddr_exposed) (@QXT6.raddr_exposed) (Q6nq.gwt_def (@QDXD.Mq3.RMALLOC_SYM) (@QXT6.RMALLOC_SYM) (Q6nq.gwt_def (@QSsB.RMALLOC_SYM) (@QXT6.RMALLOC_SYM) (Q6nq.gwt_def (@QDXD.Mq3.RHEAP) (@QXT6.RHEAP) (Q6nq.gwt_def (@QSsB.RHEAP) (@QXT6.RHEAP) Q6nq.gwt_nil)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))).
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
