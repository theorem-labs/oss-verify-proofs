(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)


From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib Require CodeAt StepGen GwInst GwEq GwApply GwApply2. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Q6nq.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QSsB.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UKNz.

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
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qy5Y.Mq4. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Q4J3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q4J3.Mq3. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QPjm.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QPjm.Mq4. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QULt.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QULt.Mq2.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QZAi.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QZAi.Mq2. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QUZl.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QUZl. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Q7S0.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q7S0.Mq0. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Q7S0.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q7S0.Mq1. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Ql2m.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Ql2m.Mq3. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QGeV.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QGeV. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QSfG.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QSfG.Mq2.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UKNz.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UKNz. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UQXM.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UQXM. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require Uv2Y.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Uv2Y. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UXT6.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UXT6. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UOpO.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UOpO. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require Unip.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Unip. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UZr4.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UZr4. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require U4l4.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import U4l4. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require Upt0.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Upt0.
Import ListNotations.
Import QlEo.Mq0.Exc. Local Ltac Qfw3.Mq3.model_reg_tac n X mexpr ::= Qfw3.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Qfw3.Mq3.zeq_fast ::= Qfw3.Mq3.mkr__zeq_fast_0.
Open Scope Z_scope.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Q6q3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q6q3.

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
Definition rvm_wait_entry := UKNz.rvm_wait_entry.
Lemma CODE : CodeAt.code_at rsegs 0x53d40 (QSsB.Mq9.realloc_code 0xde5fc0ef%Z 0x00044797%Z 0x1547b783%Z 0xfffc2797%Z 0x6f478793%Z 0xfffc2317%Z 0x59c30313%Z 0x31c000ef%Z 0x3400b0ef%Z).  Proof. StepGen.code_at_vm. Qed.
Lemma BASE4 : (0x53d40 mod 4 = 0)%Z.  Proof. reflexivity. Qed.
Lemma BASER : (0 <= 0x53d40 /\ 0x53d40 + 1092 <= 2^40)%Z.  Proof. vm_compute. split; discriminate. Qed.
Lemma CODE_rerrno_loc_entry : CodeAt.code_at rsegs rerrno_loc_entry QSsB.Mq9.errno_loc_code.  Proof. StepGen.code_at_vm. Qed.
Definition ref_find_segment_none := @UKNz.ref_find_segment_none.
Definition ref_ro_addr_false := @UKNz.ref_ro_addr_false.
Definition ref_memory_read_none := @UKNz.ref_memory_read_none.
Definition ref_wview_overlay := @UKNz.ref_wview_overlay.
Definition ref_seg_rom_none := @UKNz.ref_seg_rom_none.
Definition ref_mrd_overlay := @UKNz.ref_mrd_overlay.
Definition memcpy_spec := @memcpy_spec.
Lemma ROM_reservedZ : ltac2:(GwEq.gw_fact_ty 'segs '(@QSsB.Mq9.gw_all) @ROM_reservedZ). Proof. first [ apply QWxq.Mq0.ro_bytes_b_sound; vm_compute; reflexivity | GwApply.gw_side ]. Qed.
End GwI.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

Local Definition gwt_X : unit := (Q6nq.gwt_def (@Q8QT.Mq4.rshadow_rep) (@UQXM.rshadow_rep) (Q6nq.gwt_def (@QSsB.Mq9.rshadow_rep) (@UQXM.rshadow_rep) (Q6nq.gwt_def (@Q8QT.Mq4.rregions_wf) (@UQXM.rregions_wf) (Q6nq.gwt_def (@QSsB.Mq9.rregions_wf) (@UQXM.rregions_wf) (Q6nq.gwt_def (@QkTt.Mq2.rrealloc_post) (@Upt0.rrealloc_post) (Q6nq.gwt_def (@QSsB.Mq9.rrealloc_post) (@Upt0.rrealloc_post) (Q6nq.gwt_def (@Q8QT.Mq4.rmrep_shadow) (@UQXM.rmrep_shadow) (Q6nq.gwt_def (@QSsB.Mq9.rmrep_shadow) (@UQXM.rmrep_shadow) (Q6nq.gwt_def (@Q8QT.Mq4.rmrep_groups) (@UQXM.rmrep_groups) (Q6nq.gwt_def (@QSsB.Mq9.rmrep_groups) (@UQXM.rmrep_groups) (Q6nq.gwt_def (@Q8QT.Mq4.rmrep_globals) (@UQXM.rmrep_globals) (Q6nq.gwt_def (@QSsB.Mq9.rmrep_globals) (@UQXM.rmrep_globals) (Q6nq.gwt_def (@Q8QT.Mq4.rmrep_ctx) (@UQXM.rmrep_ctx) (Q6nq.gwt_def (@QSsB.Mq9.rmrep_ctx) (@UQXM.rmrep_ctx) (Q6nq.gwt_def (@Q8QT.Mq4.rmrep_areas) (@UQXM.rmrep_areas) (Q6nq.gwt_def (@QSsB.Mq9.rmrep_areas) (@UQXM.rmrep_areas) (Q6nq.gwt_def (@Q8QT.Mq4.rmrep) (@UQXM.rmrep) (Q6nq.gwt_def (@QSsB.Mq9.rmrep) (@UQXM.rmrep) (Q6nq.gwt_def (@QDXD.Mq3.rmalloc_post) (@UXT6.rmalloc_post) (Q6nq.gwt_def (@QSsB.Mq9.rmalloc_post) (@UXT6.rmalloc_post) (Q6nq.gwt_def (@QkTt.Mq6.rmalloc_impl_stmt) (@Unip.rmalloc_impl_stmt) (Q6nq.gwt_def (@QSsB.Mq9.rmalloc_impl_stmt) (@Unip.rmalloc_impl_stmt) (Q6nq.gwt_def (@QDXD.Mq3.rheap_pres) (@UXT6.rheap_pres) (Q6nq.gwt_def (@QSsB.Mq9.rheap_pres) (@UXT6.rheap_pres) (Q6nq.gwt_def (@Q8QT.Mq4.rgroup_rep) (@UQXM.rgroup_rep) (Q6nq.gwt_def (@QSsB.Mq9.rgroup_rep) (@UQXM.rgroup_rep) (Q6nq.gwt_def (@QDXD.Mq3.rfree_post) (@UXT6.rfree_post) (Q6nq.gwt_def (@QSsB.Mq9.rfree_post) (@UXT6.rfree_post) (Q6nq.gwt_def (@QkTt.Mq6.rfree_impl_stmt) (@Unip.rfree_impl_stmt) (Q6nq.gwt_def (@QSsB.Mq9.rfree_impl_stmt) (@Unip.rfree_impl_stmt) (Q6nq.gwt_def (@QkTt.Mq2.real_off) (@Upt0.real_off) (Q6nq.gwt_def (@QDXD.Mq3.rclient_write_ok) (@UXT6.rclient_write_ok) (Q6nq.gwt_def (@QSsB.Mq9.rclient_write_ok) (@UXT6.rclient_write_ok) (Q6nq.gwt_def (@QDXD.Mq3.rclient_range) (@UXT6.rclient_range) (Q6nq.gwt_def (@QSsB.Mq9.rclient_range) (@UXT6.rclient_range) (Q6nq.gwt_def (@QDXD.Mq3.rclient_addr) (@UXT6.rclient_addr) (Q6nq.gwt_def (@QSsB.Mq9.rclient_addr) (@UXT6.rclient_addr) (Q6nq.gwt_def (@QDXD.Mq3.rblock_range) (@UXT6.rblock_range) (Q6nq.gwt_def (@QSsB.Mq9.rblock_range) (@UXT6.rblock_range) (Q6nq.gwt_def (@QCa8.Mq5.rauxv_ok) (@Uv2Y.rauxv_ok) (Q6nq.gwt_def (@QSsB.Mq9.rauxv_ok) (@Uv2Y.rauxv_ok) (Q6nq.gwt_def (@Q8QT.Mq4.rarea_rep) (@UQXM.rarea_rep) (Q6nq.gwt_def (@QSsB.Mq9.rarea_rep) (@UQXM.rarea_rep) (Q6nq.gwt_def (@QDXD.Mq3.ralloc_static) (@UXT6.ralloc_static) (Q6nq.gwt_def (@QSsB.Mq9.ralloc_static) (@UXT6.ralloc_static) (Q6nq.gwt_def (@QDXD.Mq3.raddr_exposed) (@UXT6.raddr_exposed) (Q6nq.gwt_def (@QSsB.Mq9.raddr_exposed) (@UXT6.raddr_exposed) (Q6nq.gwt_def (@QSsB.Mq9.memcpy_post) (@U4l4.memcpy_post) (Q6nq.gwt_def (@QVbl.Mq3.memcpy_post) (@U4l4.memcpy_post) (Q6nq.gwt_def (@QkTt.Mq2.RREALLOC_STACK) (@Upt0.RREALLOC_STACK) (Q6nq.gwt_def (@QDXD.Mq3.RHEAP) (@UXT6.RHEAP) (Q6nq.gwt_def (@QSsB.Mq9.RHEAP) (@UXT6.RHEAP) Q6nq.gwt_nil)))))))))))))))))))))))))))))))))))))))))))))))))))).
#[using="Type"] Lemma rheap_pres_of_munch : ltac2:(Q6nq.ty2 'GwI.segs '(@QSsB.Mq9.rheap_pres_of_munch) [[@gw_eq_W__3; @gw_eq_W__2; @gw_eq_W]; [@gw_eq_rclient_addr__3; @gw_eq_rclient_addr__2; @gw_eq_rclient_addr]; [@gw_eq_rheap_pres__3; @gw_eq_rheap_pres__2; @gw_eq_rheap_pres]] '(@nil Z) 'gwt_X).
Proof. ltac2:(GwEq.gw_rw [[@gw_eq_W__3; @gw_eq_W__2; @gw_eq_W]; [@gw_eq_rclient_addr__3; @gw_eq_rclient_addr__2; @gw_eq_rclient_addr]; [@gw_eq_rheap_pres__3; @gw_eq_rheap_pres__2; @gw_eq_rheap_pres]]); first [GwApply2.gw_by_name2 GwI.segs (@QSsB.Mq9.rheap_pres_of_munch) | autorewrite with gw_eqs; GwApply2.gw_by_name2 GwI.segs (@QSsB.Mq9.rheap_pres_of_munch)]. Qed.

#[using="Type"] Lemma lb_remove_cons_neq p b LB : bptr_eqb (blk_id b) p = false -> lb_remove p (b :: LB) = b :: lb_remove p LB.
Proof. first [GwApply2.gw_by_name2 GwI.segs (@QSsB.Mq9.lb_remove_cons_neq) | autorewrite with gw_eqs; GwApply2.gw_by_name2 GwI.segs (@QSsB.Mq9.lb_remove_cons_neq)]. Qed.

#[using="Type"] Lemma bptr_eqb_false_of_neq (p q : bptr) : p <> q -> bptr_eqb p q = false.
Proof. first [GwApply2.gw_by_name2 GwI.segs (@QSsB.Mq9.bptr_eqb_false_of_neq) | autorewrite with gw_eqs; GwApply2.gw_by_name2 GwI.segs (@QSsB.Mq9.bptr_eqb_false_of_neq)]. Qed.

#[using="Type"] Lemma In_lb_remove p b LB : In b (lb_remove p LB) -> In b LB /\ bptr_eqb (blk_id b) p = false.
Proof. first [GwApply2.gw_by_name2 GwI.segs (@QSsB.Mq9.In_lb_remove) | autorewrite with gw_eqs; GwApply2.gw_by_name2 GwI.segs (@QSsB.Mq9.In_lb_remove)]. Qed.

Definition rr_general (cs : mstate) (slot : cptr) (n : Z) : QUZl.M (mstate * option rr_where) :=
sbind (cmalloc cs n) (fun x__ => match x__ with (cs1, r) =>
match r with
| None => ret (cs1, @None rr_where)
| Some c => sbind (cfree cs1 (Some slot)) (fun cs2 => ret (cs2, Some (RRNew (c, fresh_off cs1 c n))))
end end).

Definition rr_conv (slot : cptr) (off : Z) (x : mstate * option rr_where) : option bptr :=
match snd x with
| None => None
| Some RRSame => Some (slot, off)
| Some (RRNew b) => Some b
end.
Lemma gw_eq_rr_conv : @rr_conv = ltac:(GwInst.gw_term (@QSsB.Mq9.rr_conv) (@rr_conv)). Proof. unfold rr_conv, QSsB.Mq9.rr_conv; first [reflexivity | autorewrite with gw_eqs; reflexivity]. Qed.
#[local] Hint Rewrite gw_eq_rr_conv : gw_eqs.

#[using="Type"] Lemma rr_epilogue : ltac2:(Q6nq.ty2 'GwI.segs '(@QSsB.Mq9.rr_epilogue) [[@gw_eq_rr_conv__3; @gw_eq_rr_conv__2; @gw_eq_rr_conv]] '([344412]%Z : list Z) '(Q6nq.gwt_def (@QSsB.Mq9.rr_general) (@rr_general) gwt_X)).
Proof. first [GwApply2.gw_by_name2 GwI.segs (@QSsB.Mq9.rr_epilogue) | autorewrite with gw_eqs; GwApply2.gw_by_name2 GwI.segs (@QSsB.Mq9.rr_epilogue)]. Qed.

Section GENERAL.
Hypothesis RMI : rmalloc_impl_stmt.
Hypothesis RFI : rfree_impl_stmt.

#[using="RMI RFI"] Lemma rr_general_spec : ltac2:(Q6nq.ty2 'GwI.segs '(@QSsB.Mq9.rr_general_spec) [[@gw_eq_RFI__3; @gw_eq_RFI__2; @gw_eq_RFI]; [@gw_eq_RHEAP__3; @gw_eq_RHEAP__2; @gw_eq_RHEAP]; [@gw_eq_RREALLOC_STACK__3; @gw_eq_RREALLOC_STACK__2; @gw_eq_RREALLOC_STACK]; [@gw_eq_rauxv_ok__3; @gw_eq_rauxv_ok__2; @gw_eq_rauxv_ok]; [@gw_eq_real_off__3; @gw_eq_real_off__2; @gw_eq_real_off]; [@gw_eq_rheap_pres__3; @gw_eq_rheap_pres__2; @gw_eq_rheap_pres]; [@gw_eq_rrealloc_post__3; @gw_eq_rrealloc_post__2; @gw_eq_rrealloc_post]; [@gw_eq_rr_conv]] '([344268]%Z : list Z) '(Q6nq.gwt_zc RREALLOC_STACK (Q6nq.gwt_zc RATP (Q6nq.gwt_def (@QSsB.Mq9.rr_general) (@rr_general) (Q6nq.gwt_pat (@RATP) (@RATP) (Q6nq.gwt_hdr GwI.RATP (@RATP) gwt_X)))))).
Proof. rewrite ?gw_eq_rr_conv; ltac2:(GwEq.gw_rw [[@gw_eq_RFI__3; @gw_eq_RFI__2; @gw_eq_RFI]; [@gw_eq_RHEAP__3; @gw_eq_RHEAP__2; @gw_eq_RHEAP]; [@gw_eq_RREALLOC_STACK__3; @gw_eq_RREALLOC_STACK__2; @gw_eq_RREALLOC_STACK]; [@gw_eq_rauxv_ok__3; @gw_eq_rauxv_ok__2; @gw_eq_rauxv_ok]; [@gw_eq_real_off__3; @gw_eq_real_off__2; @gw_eq_real_off]; [@gw_eq_rheap_pres__3; @gw_eq_rheap_pres__2; @gw_eq_rheap_pres]; [@gw_eq_rrealloc_post__3; @gw_eq_rrealloc_post__2; @gw_eq_rrealloc_post]]); first [GwApply2.gw_by_name2 GwI.segs (@QSsB.Mq9.rr_general_spec) | autorewrite with gw_eqs; GwApply2.gw_by_name2 GwI.segs (@QSsB.Mq9.rr_general_spec)]. Qed.
End GENERAL.

End RC__1.
Lemma gw_eq_rr_conv__2 : @rr_conv = ltac:(GwInst.gw_term (@QSsB.Mq9.rr_conv) (@rr_conv)). Proof. unfold rr_conv, QSsB.Mq9.rr_conv; first [reflexivity | autorewrite with gw_eqs; reflexivity]. Qed.
#[export] Hint Rewrite gw_eq_rr_conv__2 : gw_eqs.
