(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)


From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib Require CodeAt StepGen GwInst GwEq GwEqH GwApply. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Q6nq.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Q6Iq.

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Q9A7.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q9A7.Mq1. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Q5Rg.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q5Rg. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Qfw3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qfw3.Mq2. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QWxq.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QWxq.Mq0. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Qc3B.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qc3B. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QlEo.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QlEo.Mq0. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QWxq.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QWxq.Mq1. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Q5Rg.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q5Rg.Mq0.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Lib.GwApply. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QsjA.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QZAi.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QZAi.Mq1. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Ql2m.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Ql2m.Mq3. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QZAi.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QZAi. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QqdR.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QqdR. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QYTG.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QYTG.Mq2.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QnDM.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QnDM.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UjdK.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UjdK. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require U4l4.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import U4l4. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UxrO.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UxrO. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require Um2h.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Um2h. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UDgQ.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UDgQ.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Q8Ie.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q8Ie.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UzOj.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UzOj.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QSCw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QSCw. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Qbz7.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qbz7.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UTru.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UTru. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require U3Uw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import U3Uw.Mq0.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UrBC.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UrBC. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UeSv.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UeSv. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UwP2.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UwP2. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require U0Ae.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import U0Ae.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UEQM.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UEQM.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Qfw3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qfw3.Mq1.
Import ListNotations.
Import QlEo.Mq0.Exc. Unset Keyed Unification. Local Ltac Q2qa.Mq0.sf_vocab ::= Q2qa.Mq0.mkr__sf_vocab_5. Local Ltac Qfw3.Mq3.zeq_fast ::= Qfw3.Mq3.mkr__zeq_fast_0.
Open Scope Z_scope.
Open Scope mspec_scope.

From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib Require CodeAt StepGen GwInst GwApply.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module GwI.
Definition segs := rsegs.
Definition base := 0x59eac%Z.
Definition w_8 := 0x0000c617%Z.
Definition w_9 := 0xb0463903%Z.
Definition w_24 := 0x2ad050ef%Z.
Definition w_39 := 0xd2cfb0ef%Z.
Definition w_50 := 0x8b0f70ef%Z.
Definition hi_8 := (Z_to_bv 20 12).
Definition lo_9 := (Z_to_bv 12 2820).
Definition joff_24 := (Z_to_bv 21 23212).
Definition joff_39 := (Z_to_bv 21 2077996).
Definition joff_50 := (Z_to_bv 21 2060464).
Definition got_ssp := got_ssp.
Definition GLOBALS_TOP := GLOBALS_TOP.
Definition STATIC_SPLIT := STATIC_SPLIT.
Definition ssp_guard := ssp_guard.
Definition e_197bc := 0x51024%Z.
Definition e_fwritex := 0x54f20%Z.
Definition e_towrite := 0x54d28%Z.
Definition e_sn_write := 0x59f78%Z.
Definition e_memset := 0x5f9b8%Z.
Definition e_vfprintf := 0x55474%Z.
Lemma CODE : CodeAt.code_at rsegs 0x59eac (Q6Iq.Mq4.vsnprintf_code 0x0000c617%Z 0xb0463903%Z 0x2ad050ef%Z 0xd2cfb0ef%Z 0x8b0f70ef%Z).  Proof. StepGen.code_at_vm. Qed.
Lemma BASE4 : (0x59eac mod 4 = 0)%Z.  Proof. reflexivity. Qed.
Lemma BASER : (0 <= 0x59eac /\ 0x59eac + 204 <= 2^40)%Z.  Proof. vm_compute. split; discriminate. Qed.
Definition memset_spec := @memset_spec.
Definition rw_CB_length := ltac:(pose proof (@rw_CB_length) as gw_h_; ltac2:(GwEqH.gw_rw_in @gw_h_ [[@gw_eq_hide__3; @gw_eq_hide__2; @gw_eq_hide]; [@gw_eq_sfx__3; @gw_eq_sfx__2; @gw_eq_sfx]; [@gw_eq_ctx_all__3; @gw_eq_ctx_all__2; @gw_eq_ctx_all]; [@gw_eq_W__3; @gw_eq_W__2; @gw_eq_W]; [@gw_eq_Fokd__3; @gw_eq_Fokd__2; @gw_eq_Fokd]; [@gw_eq_Fok__3; @gw_eq_Fok__2; @gw_eq_Fok]; [@gw_eq_POST__3; @gw_eq_POST__2; @gw_eq_POST]; [@gw_eq_hi_cells__3; @gw_eq_hi_cells__2; @gw_eq_hi_cells]; [@gw_eq_lo_cells__3; @gw_eq_lo_cells__2; @gw_eq_lo_cells]; [@gw_eq_finv__3; @gw_eq_finv__2; @gw_eq_finv]; [@gw_eq_PFXSTR__3; @gw_eq_PFXSTR__2; @gw_eq_PFXSTR]; [@gw_eq_lo_cells14__3; @gw_eq_lo_cells14__2; @gw_eq_lo_cells14]; [@gw_eq_out_postq__3; @gw_eq_out_postq__2; @gw_eq_out_postq]; [@gw_eq_fp_postq__3; @gw_eq_fp_postq__2; @gw_eq_fp_postq]; [@gw_eq_S_EXIT__3; @gw_eq_S_EXIT__2; @gw_eq_S_EXIT]; [@gw_eq_S_SCAN__3; @gw_eq_S_SCAN__2; @gw_eq_S_SCAN]; [@gw_eq_S_FLAGS__3; @gw_eq_S_FLAGS__2; @gw_eq_S_FLAGS]; [@gw_eq_S_WLOOP__3; @gw_eq_S_WLOOP__2; @gw_eq_S_WLOOP]; [@gw_eq_S_WIDTH__3; @gw_eq_S_WIDTH__2; @gw_eq_S_WIDTH]; [@gw_eq_S_PLOOP__3; @gw_eq_S_PLOOP__2; @gw_eq_S_PLOOP]; [@gw_eq_S_PREC__3; @gw_eq_S_PREC__2; @gw_eq_S_PREC]; [@gw_eq_S_STATE__3; @gw_eq_S_STATE__2; @gw_eq_S_STATE]; [@gw_eq_S_STATEL__3; @gw_eq_S_STATEL__2; @gw_eq_S_STATEL]; [@gw_eq_S_DIR__3; @gw_eq_S_DIR__2; @gw_eq_S_DIR]; [@gw_eq_S_END__3; @gw_eq_S_END__2; @gw_eq_S_END]; [@gw_eq_S_HEAD__3; @gw_eq_S_HEAD__2; @gw_eq_S_HEAD]; [@gw_eq_S_CONV__3; @gw_eq_S_CONV__2; @gw_eq_S_CONV]; [@gw_eq_body_loc__3; @gw_eq_body_loc__2; @gw_eq_body_loc]; [@gw_eq_S_TAIL__3; @gw_eq_S_TAIL__2; @gw_eq_S_TAIL]; [@gw_eq_tregs__3; @gw_eq_tregs__2; @gw_eq_tregs]; [@gw_eq_tinv__3; @gw_eq_tinv__2; @gw_eq_tinv]; [@gw_eq_S_T6__3; @gw_eq_S_T6__2; @gw_eq_S_T6]; [@gw_eq_S_T5__3; @gw_eq_S_T5__2; @gw_eq_S_T5]; [@gw_eq_S_T4__3; @gw_eq_S_T4__2; @gw_eq_S_T4]; [@gw_eq_S_T3__3; @gw_eq_S_T3__2; @gw_eq_S_T3]; [@gw_eq_S_T2__3; @gw_eq_S_T2__2; @gw_eq_S_T2]; [@gw_eq_S_T1__3; @gw_eq_S_T1__2; @gw_eq_S_T1]; [@gw_eq_S_INTC2__3; @gw_eq_S_INTC2__2; @gw_eq_S_INTC2]; [@gw_eq_S_INTC__3; @gw_eq_S_INTC__2; @gw_eq_S_INTC]; [@gw_eq_dloop_post__3; @gw_eq_dloop_post__2; @gw_eq_dloop_post]; [@gw_eq_S_DLOOP__3; @gw_eq_S_DLOOP__2; @gw_eq_S_DLOOP]; [@gw_eq_S_FMTU2__3; @gw_eq_S_FMTU2__2; @gw_eq_S_FMTU2]; [@gw_eq_S_FMTU__3; @gw_eq_S_FMTU__2; @gw_eq_S_FMTU]; [@gw_eq_S_CV_D__3; @gw_eq_S_CV_D__2; @gw_eq_S_CV_D]; [@gw_eq_S_CV_U__3; @gw_eq_S_CV_U__2; @gw_eq_S_CV_U]; [@gw_eq_S_CV_C__3; @gw_eq_S_CV_C__2; @gw_eq_S_CV_C]; [@gw_eq_xloop_post__3; @gw_eq_xloop_post__2; @gw_eq_xloop_post]; [@gw_eq_S_XLOOP__3; @gw_eq_S_XLOOP__2; @gw_eq_S_XLOOP]; [@gw_eq_S_CV_X__3; @gw_eq_S_CV_X__2; @gw_eq_S_CV_X]; [@gw_eq_S_CV_S__3; @gw_eq_S_CV_S__2; @gw_eq_S_CV_S]; [@gw_eq_S_CV_FP__3; @gw_eq_S_CV_FP__2; @gw_eq_S_CV_FP]; [@gw_eq_POST1__3; @gw_eq_POST1__2; @gw_eq_POST1]; [@gw_eq_S_EXIT1__3; @gw_eq_S_EXIT1__2; @gw_eq_S_EXIT1]; [@gw_eq_S_P1__3; @gw_eq_S_P1__2; @gw_eq_S_P1]; [@gw_eq_S_PRO__3; @gw_eq_S_PRO__2; @gw_eq_S_PRO]; [@gw_eq_memcpy_postv__3; @gw_eq_memcpy_postv__2; @gw_eq_memcpy_postv]; [@gw_eq_sn_write_post__3; @gw_eq_sn_write_post__2; @gw_eq_sn_write_post]; [@gw_eq_sn_write0_post__3; @gw_eq_sn_write0_post__2; @gw_eq_sn_write0_post]]); exact gw_h_).
Definition rwc_eq := ltac:(pose proof (@rwc_eq) as gw_h_; ltac2:(GwEqH.gw_rw_in @gw_h_ [[@gw_eq_gfile_cells__3; @gw_eq_gfile_cells__2; @gw_eq_gfile_cells]; [@gw_eq_towrite_g_stmt__3; @gw_eq_towrite_g_stmt__2; @gw_eq_towrite_g_stmt]; [@gw_eq_snfile_head__3; @gw_eq_snfile_head__2; @gw_eq_snfile_head]; [@gw_eq_snfile_rest__3; @gw_eq_snfile_rest__2; @gw_eq_snfile_rest]; [@gw_eq_VF_FRAME__3; @gw_eq_VF_FRAME__2; @gw_eq_VF_FRAME]; [@gw_eq_vfprintf_sn_post__3; @gw_eq_vfprintf_sn_post__2; @gw_eq_vfprintf_sn_post]; [@gw_eq_vfprintf_sn_stmt__3; @gw_eq_vfprintf_sn_stmt__2; @gw_eq_vfprintf_sn_stmt]]); exact gw_h_).
Definition vfprintf_sn_proof := ltac:(pose proof (@vfprintf_sn_proof) as gw_h_; ltac2:(GwEqH.gw_rw_in @gw_h_ [[@gw_eq_gfile_cells__3; @gw_eq_gfile_cells__2; @gw_eq_gfile_cells]; [@gw_eq_towrite_g_stmt__3; @gw_eq_towrite_g_stmt__2; @gw_eq_towrite_g_stmt]; [@gw_eq_snfile_head__3; @gw_eq_snfile_head__2; @gw_eq_snfile_head]; [@gw_eq_snfile_rest__3; @gw_eq_snfile_rest__2; @gw_eq_snfile_rest]; [@gw_eq_VF_FRAME__3; @gw_eq_VF_FRAME__2; @gw_eq_VF_FRAME]; [@gw_eq_vfprintf_sn_post__3; @gw_eq_vfprintf_sn_post__2; @gw_eq_vfprintf_sn_post]; [@gw_eq_vfprintf_sn_stmt__3; @gw_eq_vfprintf_sn_stmt__2; @gw_eq_vfprintf_sn_stmt]]); exact gw_h_).
End GwI.

Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs. Local Ltac mkr__transport_chunks_0 segs m a bs := transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs. Local Ltac mkr__footprint_after_store_1 segs m a bs := footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast. Local Ltac mkr__mem_after_store_2 := mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM. Local Ltac mkr__transport_after_call_3 segs m m' MU WM := transport_after_call_fast segs m m' MU WM.
Local Ltac lia ::= lia3. Local Ltac mkr__lia_4 := lia3.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Ltac zs := zstep; try (fix_litstore; mem_after_store_opt).
Ltac fix_ret := lazymatch goal with |- evt _ _ (MS _ _ (ret_pc (Z_to_bv 64 ?n)) _ _ _ _) =>
replace (ret_pc (Z_to_bv 64 n)) with (Z_to_bv 64 n) by (symmetry; apply ret_pc_even; [ lia | reflexivity ]) end.

Local Definition gwt_X : unit := (Q6nq.gwt_def (@QQRC.Mq0.zb) (@UDgQ.zb) (Q6nq.gwt_def (@Q6Iq.Mq4.vfprintf_sn_stmt) (@UwP2.vfprintf_sn_stmt) (Q6nq.gwt_def (@QzQg.Mq1.vfprintf_sn_stmt) (@UwP2.vfprintf_sn_stmt) (Q6nq.gwt_def (@Q6Iq.Mq4.vfprintf_sn_post) (@UwP2.vfprintf_sn_post) (Q6nq.gwt_def (@QzQg.Mq1.vfprintf_sn_post) (@UwP2.vfprintf_sn_post) (Q6nq.gwt_def (@Q6Iq.Mq4.va_area) (@UzOj.va_area) (Q6nq.gwt_def (@Q91D.Mq3.va_area) (@UzOj.va_area) (Q6nq.gwt_def (@Q6Iq.Mq4.ssp_cells) (@Um2h.ssp_cells) (Q6nq.gwt_def (@Q91D.Mq2.ssp_cells) (@Um2h.ssp_cells) (Q6nq.gwt_def (@Q6Iq.Mq4.snfile_head) (@UwP2.snfile_head) (Q6nq.gwt_def (@QzQg.Mq1.snfile_head) (@UwP2.snfile_head) (Q6nq.gwt_def (@OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.G.T_pe.Printf_model.printf_model) (@QSCw.printf_model) (Q6nq.gwt_def (@OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.G.T_pe.Printf_model.pass1_ok) (@QSCw.pass1_ok) (Q6nq.gwt_def (@Q6Iq.Mq4.memset_post) (@UjdK.memset_post) (Q6nq.gwt_def (@QVbl.Mq4.memset_post) (@UjdK.memset_post) (Q6nq.gwt_def (@OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.G.T_pe.Printf_model.fp_calls) (@QSCw.fp_calls) (Q6nq.gwt_def (@OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.G.T_shp.F_fmt_fp.fmt_fp_facts) (@Q8Ie.fmt_fp_facts) (Q6nq.gwt_def (@Q6Iq.Mq4.args_ok) (@UTru.args_ok) (Q6nq.gwt_def (@Q8l1.Mq1.args_ok) (@UTru.args_ok) (Q6nq.gwt_def (@Q6Iq.Mq4.arg_ok) (@UTru.arg_ok) (Q6nq.gwt_def (@Q8l1.Mq1.arg_ok) (@UTru.arg_ok) (Q6nq.gwt_def (@Q8l1.Mq1.OUT_sn) (@UTru.OUT_sn) (Q6nq.gwt_def (@Q8l1.Mq1.OUTFP_sn) (@UTru.OUTFP_sn) Q6nq.gwt_nil))))))))))))))))))))))).
Lemma rw_cells_recast : ltac2:(Q6nq.ty1 'GwI.segs '(@Q6Iq.Mq4.rw_cells_recast) [] '(@nil Z) 'gwt_X).
Proof. first [GwApply.gw_by_name GwI.segs (@Q6Iq.Mq4.rw_cells_recast) | autorewrite with gw_eqs; GwApply.gw_by_name GwI.segs (@Q6Iq.Mq4.rw_cells_recast)]. Qed.

Lemma rw_cells_C4_eqv : ltac2:(Q6nq.ty1 'GwI.segs '(@Q6Iq.Mq4.rw_cells_C4_eqv) [] '(@nil Z) 'gwt_X).
Proof. first [GwApply.gw_by_name GwI.segs (@Q6Iq.Mq4.rw_cells_C4_eqv) | autorewrite with gw_eqs; GwApply.gw_by_name GwI.segs (@Q6Iq.Mq4.rw_cells_C4_eqv)]. Qed.

Ltac c4_eqv H k v' :=
lazymatch type of H with rw_cells _ ?m ?A ?cs =>
let pre := eval cbv beta iota delta [firstn] in (firstn k cs) in
let post := eval cbv beta iota delta [skipn] in (skipn (S k) cs) in
lazymatch eval cbv beta iota delta [nth_error] in (nth_error cs k) with Some (C4 ?v) =>
let H' := fresh in
pose proof (rw_cells_C4_eqv m A pre v v' post) as H'; cbn [app] in H';
specialize (H' H ltac:(unfold le4; cbn [Z_to_le_bytes]; repeat (apply (f_equal2 cons); [apply bv_eq; vm_compute; reflexivity|]); reflexivity)); clear H; rename H' into H
end end.

Definition no_s (a : parg) : Prop := match a with PA_s _ => False | _ => True end.
Lemma gw_eq_no_s : @no_s = ltac:(GwInst.gw_term (@Q6Iq.Mq4.no_s) (@no_s)). Proof. unfold no_s, Q6Iq.Mq4.no_s; first [reflexivity | autorewrite with gw_eqs; reflexivity]. Qed.
#[export] Hint Rewrite gw_eq_no_s : gw_eqs.
Lemma args_ok_nos : ltac2:(Q6nq.ty1 'GwI.segs '(@Q6Iq.Mq4.args_ok_nos) [[@gw_eq_args_ok__3; @gw_eq_args_ok__2; @gw_eq_args_ok]; [@gw_eq_no_s]] '(@nil Z) 'gwt_X).
Proof. rewrite ?gw_eq_no_s; ltac2:(GwEq.gw_rw [[@gw_eq_args_ok__3; @gw_eq_args_ok__2; @gw_eq_args_ok]]); first [GwApply.gw_by_name GwI.segs (@Q6Iq.Mq4.args_ok_nos) | autorewrite with gw_eqs; GwApply.gw_by_name GwI.segs (@Q6Iq.Mq4.args_ok_nos)]. Qed.

Definition VSN_FRAME : Z := 304.
Lemma gw_eq_VSN_FRAME : @VSN_FRAME = ltac:(GwInst.gw_term (@Q6Iq.Mq4.VSN_FRAME) (@VSN_FRAME)). Proof. unfold VSN_FRAME, Q6Iq.Mq4.VSN_FRAME; first [reflexivity | autorewrite with gw_eqs; reflexivity]. Qed.
#[export] Hint Rewrite gw_eq_VSN_FRAME : gw_eqs.
Definition VSN_DEPTH : Z := 5856.
Lemma gw_eq_VSN_DEPTH : @VSN_DEPTH = ltac:(GwInst.gw_term (@Q6Iq.Mq4.VSN_DEPTH) (@VSN_DEPTH)). Proof. unfold VSN_DEPTH, Q6Iq.Mq4.VSN_DEPTH; first [reflexivity | autorewrite with gw_eqs; reflexivity]. Qed.
#[export] Hint Rewrite gw_eq_VSN_DEPTH : gw_eqs.

Definition vsnprintf_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word)
(D : Z) (dn : nat) (junkd : list byte) (r : Z) (o : list Z) (lo : Z) (canary : word) (m : mem) : machine_state -> Prop :=
fun ms' => exists (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (Ft : bvmap 5 word) (fc' : bv 32) (m' : mem),
ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 r) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
Ft (ret_pc ra) fc' None m' (seg_rom rsegs)
/\ munch [(lo, bv_unsigned sp); (D, D + Z.of_nat dn)] m m' /\ wmono rsegs m m' /\ mem_inv rsegs m'
/\ frm0 fc'
/\ (forall k : reg, bv_unsigned k <> 10 -> reg_get Ft k = reg_get F k)
/\ stk rsegs m' lo (bv_unsigned sp)
/\ ssp_cells m' canary
/\ rw_cells rsegs m' D [CB dn (zb o ++ Z_to_bv 8 0 :: skipn (S (length o)) junkd)].
Lemma gw_eq_vsnprintf_post : @vsnprintf_post = ltac:(GwInst.gw_term (@Q6Iq.Mq4.vsnprintf_post rsegs got_ssp ssp_guard) (@vsnprintf_post)). Proof. unfold vsnprintf_post, Q6Iq.Mq4.vsnprintf_post; ltac2:(GwEq.gw_rw [[@gw_eq_ssp_cells__3; @gw_eq_ssp_cells__2; @gw_eq_ssp_cells]; [@gw_eq_zb__3; @gw_eq_zb__2; @gw_eq_zb]]); first [reflexivity | autorewrite with gw_eqs; reflexivity]. Qed.
#[export] Hint Rewrite gw_eq_vsnprintf_post : gw_eqs.

Definition vsnprintf_stmt : Prop :=
forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : mem)
(D n A VA : Z) (dn : nat) (junkd : list byte) (fmt : list Z) (slots : list word) (args : list parg)
(lo : Z) (canary : word) (r : Z) (o : list Z),
let q := bv_unsigned sp in
a0 = Z_to_bv 64 D -> a1 = Z_to_bv 64 n -> a2 = Z_to_bv 64 A -> a3 = Z_to_bv 64 VA ->
rw_cells rsegs m D [CB dn junkd] ->
bytes_at rsegs m A (zb fmt) -> Forall (fun c => 0 <= c < 256) fmt -> pass1_ok fmt = true ->
va_area m VA slots -> Forall no_s args -> args_ok 0 0 0 m lo q 0 slots args ->
printf_model OUT_sn OUTFP_sn fmt args [] = QlEo.Mq0.Ret (Ok (r, o)) ->
Forall (fun c => let '(y, w, p, fl, t) := c in fmt_fp_facts y fl p t) (fp_calls (length fmt) fmt args) ->
(length o < dn)%nat -> (zlength o <= n - 1) -> (1 <= n < 2^63) ->
stk rsegs m lo q -> (lo <= q - VSN_DEPTH) -> (GLOBALS_TOP <= lo) -> (q < 2^63) ->
ssp_cells m canary -> mem_inv rsegs m -> frm0 fc ->
(65536 <= A) -> (A + zlength fmt <= STATIC_SPLIT) ->
(q <= VA) -> (VA + 8 * zlength slots <= 2^64) ->
(D + Z.of_nat dn <= lo \/ q <= D) -> (D + Z.of_nat dn <= VA \/ VA + 8 * zlength slots <= D) -> (D + Z.of_nat dn <= 65536 \/ GLOBALS_TOP <= D \/ (STATIC_SPLIT <= D /\ D + Z.of_nat dn <= got_ssp) \/ (got_ssp + 8 <= D /\ D + Z.of_nat dn <= ssp_guard) \/ (ssp_guard + 8 <= D /\ D + Z.of_nat dn <= GLOBALS_TOP)) ->
evt rsegs (vsnprintf_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F D dn junkd r o lo canary m)
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0x59eac) fc None m (seg_rom rsegs)).
Lemma gw_eq_vsnprintf_stmt : @vsnprintf_stmt = ltac:(GwInst.gw_term (@Q6Iq.Mq4.vsnprintf_stmt rsegs 0x59eac got_ssp GLOBALS_TOP STATIC_SPLIT ssp_guard) (@vsnprintf_stmt)). Proof. unfold vsnprintf_stmt, Q6Iq.Mq4.vsnprintf_stmt; rewrite ?gw_eq_no_s, ?gw_eq_VSN_DEPTH, ?gw_eq_vsnprintf_post; ltac2:(GwEq.gw_rw [[@gw_eq_OUTFP_sn__3; @gw_eq_OUTFP_sn__2; @gw_eq_OUTFP_sn]; [@gw_eq_OUT_sn__3; @gw_eq_OUT_sn__2; @gw_eq_OUT_sn]; [@gw_eq_args_ok__3; @gw_eq_args_ok__2; @gw_eq_args_ok]; [@gw_eq_fmt_fp_facts__3; @gw_eq_fmt_fp_facts__2; @gw_eq_fmt_fp_facts]; [@gw_eq_fp_calls__3; @gw_eq_fp_calls__2; @gw_eq_fp_calls]; [@gw_eq_pass1_ok__3; @gw_eq_pass1_ok__2; @gw_eq_pass1_ok]; [@gw_eq_printf_model__3; @gw_eq_printf_model__2; @gw_eq_printf_model]; [@gw_eq_ssp_cells__3; @gw_eq_ssp_cells__2; @gw_eq_ssp_cells]; [@gw_eq_va_area__3; @gw_eq_va_area__2; @gw_eq_va_area]; [@gw_eq_zb__3; @gw_eq_zb__2; @gw_eq_zb]]); first [reflexivity | autorewrite with gw_eqs; reflexivity]. Qed.
#[export] Hint Rewrite gw_eq_vsnprintf_stmt : gw_eqs.

Theorem vsnprintf_proof : vsnprintf_stmt.
Proof. rewrite ?gw_eq_vsnprintf_stmt; first [GwApply.gw_by_name GwI.segs (@Q6Iq.Mq4.vsnprintf_proof) | autorewrite with gw_eqs; GwApply.gw_by_name GwI.segs (@Q6Iq.Mq4.vsnprintf_proof)]. Qed.

Lemma fmt_bytes_at : ltac2:(Q6nq.ty1 'GwI.segs '(@Q6Iq.Mq4.fmt_bytes_at) [[@gw_eq_zb__3; @gw_eq_zb__2; @gw_eq_zb]; [@gw_eq_no_s__3; @gw_eq_no_s__2; @gw_eq_no_s]; [@gw_eq_VSN_FRAME__3; @gw_eq_VSN_FRAME__2; @gw_eq_VSN_FRAME]; [@gw_eq_VSN_DEPTH__3; @gw_eq_VSN_DEPTH__2; @gw_eq_VSN_DEPTH]; [@gw_eq_vsnprintf_post__3; @gw_eq_vsnprintf_post__2; @gw_eq_vsnprintf_post]; [@gw_eq_vsnprintf_stmt__3; @gw_eq_vsnprintf_stmt__2; @gw_eq_vsnprintf_stmt]] '(@nil Z) 'gwt_X).
Proof. ltac2:(GwEq.gw_rw [[@gw_eq_zb__3; @gw_eq_zb__2; @gw_eq_zb]]); first [GwApply.gw_by_name GwI.segs (@Q6Iq.Mq4.fmt_bytes_at) | autorewrite with gw_eqs; GwApply.gw_by_name GwI.segs (@Q6Iq.Mq4.fmt_bytes_at)]. Qed.

Ltac forall_range := repeat (apply Forall_cons; [lia|]); apply Forall_nil.

