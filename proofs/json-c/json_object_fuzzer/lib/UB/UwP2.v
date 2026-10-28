(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)


From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib Require CodeAt StepGen GwInst GwEq GwEqH GwApply. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Q6nq.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QzQg.

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
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Qfw3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qfw3.Mq1.
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
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UeSv.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UEQM.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UEQM.
Import ListNotations.
Import QlEo.Mq0.Exc. Unset Keyed Unification. Local Ltac Q2qa.Mq0.sf_vocab ::= Q2qa.Mq0.mkr__sf_vocab_5. Local Ltac Qfw3.Mq3.zeq_fast ::= Qfw3.Mq3.mkr__zeq_fast_0.
Open Scope Z_scope.
Open Scope mspec_scope.

From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib Require CodeAt StepGen GwInst GwApply.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module GwI.
Definition segs := rsegs.
Definition base := 0x55474%Z.
Definition w_10 := 0x00010517%Z.
Definition w_11 := 0x53453903%Z.
Definition w_30 := 0xc5cff0ef%Z.
Definition w_54 := 0xfdcff0ef%Z.
Definition w_93 := 0xc5cff0ef%Z.
Definition w_107 := 0xa05fb0ef%Z.
Definition hi_10 := (Z_to_bv 20 16).
Definition lo_11 := (Z_to_bv 12 1332).
Definition joff_30 := (Z_to_bv 21 2094172).
Definition joff_54 := (Z_to_bv 21 2095068).
Definition joff_93 := (Z_to_bv 21 2094172).
Definition joff_107 := (Z_to_bv 21 2079236).
Definition got_ssp := got_ssp.
Definition GLOBALS_TOP := GLOBALS_TOP.
Definition STATIC_SPLIT := STATIC_SPLIT.
Definition ssp_guard := ssp_guard.
Definition e_194bc := 0x50b60%Z.
Definition e_194c8 := 0x50b6c%Z.
Definition e_197bc := 0x51024%Z.
Definition e_fwritex := 0x54f20%Z.
Definition e_towrite := 0x54d28%Z.
Definition e_1cd64 := 0x54948%Z.
Definition e_1ce60 := 0x54a44%Z.
Definition e_sn_write := 0x59f78%Z.
Definition e_memcpy := 0x5f438%Z.
Definition e_memset := 0x5f9b8%Z.
Definition e_2596c := 0x5fe24%Z.
Lemma CODE : CodeAt.code_at rsegs 0x55474 (QzQg.Mq1.vfprintf_code 0x00010517%Z 0x53453903%Z 0xc5cff0ef%Z 0xfdcff0ef%Z 0xc5cff0ef%Z 0xa05fb0ef%Z).  Proof. StepGen.code_at_vm. Qed.
Lemma BASE4 : (0x55474 mod 4 = 0)%Z.  Proof. reflexivity. Qed.
Lemma BASER : (0 <= 0x55474 /\ 0x55474 + 432 <= 2^40)%Z.  Proof. vm_compute. split; discriminate. Qed.
Lemma CODE_e_towrite : CodeAt.code_at rsegs e_towrite QzQg.Mq1.towrite_code.  Proof. StepGen.code_at_vm. Qed.
Definition printf_core_proof := @printf_core_proof.
Definition printf_core1_proof := @printf_core1_proof.
Definition sn_sink_frame := @sn_sink_frame.
Definition sn_sink_flags := @sn_sink_flags.
Definition sn_topok := @sn_topok.
Definition sn_out := @sn_out.
Definition sn_fpcall := @sn_fpcall.
Definition rw_CB_length := ltac:(pose proof (@rw_CB_length) as gw_h_; ltac2:(GwEqH.gw_rw_in @gw_h_ [[@gw_eq_hide__3; @gw_eq_hide__2; @gw_eq_hide]; [@gw_eq_sfx__3; @gw_eq_sfx__2; @gw_eq_sfx]; [@gw_eq_ctx_all__3; @gw_eq_ctx_all__2; @gw_eq_ctx_all]; [@gw_eq_W__3; @gw_eq_W__2; @gw_eq_W]; [@gw_eq_Fokd__3; @gw_eq_Fokd__2; @gw_eq_Fokd]; [@gw_eq_Fok__3; @gw_eq_Fok__2; @gw_eq_Fok]; [@gw_eq_POST__3; @gw_eq_POST__2; @gw_eq_POST]; [@gw_eq_hi_cells__3; @gw_eq_hi_cells__2; @gw_eq_hi_cells]; [@gw_eq_lo_cells__3; @gw_eq_lo_cells__2; @gw_eq_lo_cells]; [@gw_eq_finv__3; @gw_eq_finv__2; @gw_eq_finv]; [@gw_eq_PFXSTR__3; @gw_eq_PFXSTR__2; @gw_eq_PFXSTR]; [@gw_eq_lo_cells14__3; @gw_eq_lo_cells14__2; @gw_eq_lo_cells14]; [@gw_eq_out_postq__3; @gw_eq_out_postq__2; @gw_eq_out_postq]; [@gw_eq_fp_postq__3; @gw_eq_fp_postq__2; @gw_eq_fp_postq]; [@gw_eq_S_EXIT__3; @gw_eq_S_EXIT__2; @gw_eq_S_EXIT]; [@gw_eq_S_SCAN__3; @gw_eq_S_SCAN__2; @gw_eq_S_SCAN]; [@gw_eq_S_FLAGS__3; @gw_eq_S_FLAGS__2; @gw_eq_S_FLAGS]; [@gw_eq_S_WLOOP__3; @gw_eq_S_WLOOP__2; @gw_eq_S_WLOOP]; [@gw_eq_S_WIDTH__3; @gw_eq_S_WIDTH__2; @gw_eq_S_WIDTH]; [@gw_eq_S_PLOOP__3; @gw_eq_S_PLOOP__2; @gw_eq_S_PLOOP]; [@gw_eq_S_PREC__3; @gw_eq_S_PREC__2; @gw_eq_S_PREC]; [@gw_eq_S_STATE__3; @gw_eq_S_STATE__2; @gw_eq_S_STATE]; [@gw_eq_S_STATEL__3; @gw_eq_S_STATEL__2; @gw_eq_S_STATEL]; [@gw_eq_S_DIR__3; @gw_eq_S_DIR__2; @gw_eq_S_DIR]; [@gw_eq_S_END__3; @gw_eq_S_END__2; @gw_eq_S_END]; [@gw_eq_S_HEAD__3; @gw_eq_S_HEAD__2; @gw_eq_S_HEAD]; [@gw_eq_S_CONV__3; @gw_eq_S_CONV__2; @gw_eq_S_CONV]; [@gw_eq_body_loc__3; @gw_eq_body_loc__2; @gw_eq_body_loc]; [@gw_eq_S_TAIL__3; @gw_eq_S_TAIL__2; @gw_eq_S_TAIL]; [@gw_eq_tregs__3; @gw_eq_tregs__2; @gw_eq_tregs]; [@gw_eq_tinv__3; @gw_eq_tinv__2; @gw_eq_tinv]; [@gw_eq_S_T6__3; @gw_eq_S_T6__2; @gw_eq_S_T6]; [@gw_eq_S_T5__3; @gw_eq_S_T5__2; @gw_eq_S_T5]; [@gw_eq_S_T4__3; @gw_eq_S_T4__2; @gw_eq_S_T4]; [@gw_eq_S_T3__3; @gw_eq_S_T3__2; @gw_eq_S_T3]; [@gw_eq_S_T2__3; @gw_eq_S_T2__2; @gw_eq_S_T2]; [@gw_eq_S_T1__3; @gw_eq_S_T1__2; @gw_eq_S_T1]; [@gw_eq_S_INTC2__3; @gw_eq_S_INTC2__2; @gw_eq_S_INTC2]; [@gw_eq_S_INTC__3; @gw_eq_S_INTC__2; @gw_eq_S_INTC]; [@gw_eq_dloop_post__3; @gw_eq_dloop_post__2; @gw_eq_dloop_post]; [@gw_eq_S_DLOOP__3; @gw_eq_S_DLOOP__2; @gw_eq_S_DLOOP]; [@gw_eq_S_FMTU2__3; @gw_eq_S_FMTU2__2; @gw_eq_S_FMTU2]; [@gw_eq_S_FMTU__3; @gw_eq_S_FMTU__2; @gw_eq_S_FMTU]; [@gw_eq_S_CV_D__3; @gw_eq_S_CV_D__2; @gw_eq_S_CV_D]; [@gw_eq_S_CV_U__3; @gw_eq_S_CV_U__2; @gw_eq_S_CV_U]; [@gw_eq_S_CV_C__3; @gw_eq_S_CV_C__2; @gw_eq_S_CV_C]; [@gw_eq_xloop_post__3; @gw_eq_xloop_post__2; @gw_eq_xloop_post]; [@gw_eq_S_XLOOP__3; @gw_eq_S_XLOOP__2; @gw_eq_S_XLOOP]; [@gw_eq_S_CV_X__3; @gw_eq_S_CV_X__2; @gw_eq_S_CV_X]; [@gw_eq_S_CV_S__3; @gw_eq_S_CV_S__2; @gw_eq_S_CV_S]; [@gw_eq_S_CV_FP__3; @gw_eq_S_CV_FP__2; @gw_eq_S_CV_FP]; [@gw_eq_POST1__3; @gw_eq_POST1__2; @gw_eq_POST1]; [@gw_eq_S_EXIT1__3; @gw_eq_S_EXIT1__2; @gw_eq_S_EXIT1]; [@gw_eq_S_P1__3; @gw_eq_S_P1__2; @gw_eq_S_P1]; [@gw_eq_S_PRO__3; @gw_eq_S_PRO__2; @gw_eq_S_PRO]; [@gw_eq_memcpy_postv__3; @gw_eq_memcpy_postv__2; @gw_eq_memcpy_postv]; [@gw_eq_sn_write_post__3; @gw_eq_sn_write_post__2; @gw_eq_sn_write_post]; [@gw_eq_sn_write0_post__3; @gw_eq_sn_write0_post__2; @gw_eq_sn_write0_post]]); exact gw_h_).
Definition sn_write_spec := ltac:(pose proof (@sn_write_spec) as gw_h_; ltac2:(GwEqH.gw_rw_in @gw_h_ [[@gw_eq_memcpy_postv__3; @gw_eq_memcpy_postv__2; @gw_eq_memcpy_postv]; [@gw_eq_sn_write_post__3; @gw_eq_sn_write_post__2; @gw_eq_sn_write_post]]); exact gw_h_).
End GwI.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs. Local Ltac mkr__transport_chunks_1 segs m a bs := transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs. Local Ltac mkr__footprint_after_store_2 segs m a bs := footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast. Local Ltac mkr__mem_after_store_3 := mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM. Local Ltac mkr__transport_after_call_4 segs m m' MU WM := transport_after_call_fast segs m m' MU WM.
Local Ltac lia ::= lia3. Local Ltac mkr__lia_5 := lia3.
Notation z64 := (Z_to_bv 64 0) (only parsing).
Ltac zs := zstep; try (fix_litstore; mem_after_store_opt).
Ltac fix_ret := lazymatch goal with |- evt _ _ (MS _ _ (ret_pc (Z_to_bv 64 ?n)) _ _ _ _) =>
replace (ret_pc (Z_to_bv 64 n)) with (Z_to_bv 64 n) by (symmetry; apply ret_pc_even; [ lia | reflexivity ]) end.

Definition gfile_cells (flags : word) (rpos rend close wend wpos wbase writefn seekfn buf bufsize fd : Z) (mode lock : word) (lbf : Z) : list cell :=
[C4 flags; C4 z64; C8 (Z_to_bv 64 rpos); C8 (Z_to_bv 64 rend); C8 (Z_to_bv 64 close);
C8 (Z_to_bv 64 wend); C8 (Z_to_bv 64 wpos); C8 z64; C8 (Z_to_bv 64 wbase); C8 z64;
C8 (Z_to_bv 64 writefn); C8 (Z_to_bv 64 seekfn); C8 (Z_to_bv 64 buf); C8 (Z_to_bv 64 bufsize);
C8 z64; C8 z64; C4 (Z_to_bv 64 fd); C4 z64; C8 z64; C4 mode; C4 lock; C4 (Z_to_bv 64 lbf)].
Lemma gw_eq_gfile_cells : @gfile_cells = ltac:(GwInst.gw_term (@QzQg.Mq1.gfile_cells) (@gfile_cells)). Proof. unfold gfile_cells, QzQg.Mq1.gfile_cells; first [reflexivity | autorewrite with gw_eqs; reflexivity]. Qed.
#[export] Hint Rewrite gw_eq_gfile_cells : gw_eqs.

Definition towrite_g_stmt : Prop :=
forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : mem)
(flags mode lock : word) (rpos rend close wend wpos wbase writefn seekfn buf bufsize fd lbf : Z),
rw_cells rsegs m (bv_unsigned a0) (gfile_cells flags rpos rend close wend wpos wbase writefn seekfn buf bufsize fd mode lock lbf) ->
Z.land (bv_unsigned flags) 8 = 0 ->
(0 <= buf) -> (buf + bufsize < 2^64) -> (0 <= bufsize) ->
mem_inv rsegs m ->
evt rsegs (fun ms' => exists (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (mode' : word) (m' : mem),
ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 0) a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
F (ret_pc ra) fc None m' (seg_rom rsegs)
/\ munch [(bv_unsigned a0, bv_unsigned a0 + 148)] m m' /\ wmono rsegs m m' /\ mem_inv rsegs m'
/\ rw_cells rsegs m' (bv_unsigned a0) (gfile_cells flags 0 0 close (buf + bufsize) buf buf writefn seekfn buf bufsize fd mode' lock lbf))
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0x54d28) fc None m (seg_rom rsegs)).
Lemma gw_eq_towrite_g_stmt : @towrite_g_stmt = ltac:(GwInst.gw_term (@QzQg.Mq1.towrite_g_stmt rsegs 0x54d28%Z) (@towrite_g_stmt)). Proof. unfold towrite_g_stmt, QzQg.Mq1.towrite_g_stmt; rewrite ?gw_eq_gfile_cells; first [reflexivity | autorewrite with gw_eqs; reflexivity]. Qed.
#[export] Hint Rewrite gw_eq_towrite_g_stmt : gw_eqs.

Theorem towrite_g_proof : towrite_g_stmt.
Proof. rewrite ?gw_eq_towrite_g_stmt; first [GwApply.gw_by_name GwI.segs (@QzQg.Mq1.towrite_g_proof) | autorewrite with gw_eqs; GwApply.gw_by_name GwI.segs (@QzQg.Mq1.towrite_g_proof)]. Qed.

Local Definition gwt_X : unit := (Q6nq.gwt_def (@QzQg.Mq1.args_ok) (@UTru.args_ok) (Q6nq.gwt_def (@Q8l1.Mq1.args_ok) (@UTru.args_ok) (Q6nq.gwt_def (@QzQg.Mq1.arg_ok) (@UTru.arg_ok) (Q6nq.gwt_def (@Q8l1.Mq1.arg_ok) (@UTru.arg_ok) Q6nq.gwt_nil)))).
Lemma arg_ok_vf : ltac2:(Q6nq.ty1 'GwI.segs '(@QzQg.Mq1.arg_ok_vf) [[@gw_eq_arg_ok__3; @gw_eq_arg_ok__2; @gw_eq_arg_ok]; [@gw_eq_gfile_cells__3; @gw_eq_gfile_cells__2; @gw_eq_gfile_cells]; [@gw_eq_towrite_g_stmt__3; @gw_eq_towrite_g_stmt__2; @gw_eq_towrite_g_stmt]] '([232]%Z : list Z) 'gwt_X).
Proof. ltac2:(GwEq.gw_rw [[@gw_eq_arg_ok__3; @gw_eq_arg_ok__2; @gw_eq_arg_ok]]); first [GwApply.gw_by_name GwI.segs (@QzQg.Mq1.arg_ok_vf) | autorewrite with gw_eqs; GwApply.gw_by_name GwI.segs (@QzQg.Mq1.arg_ok_vf)]. Qed.
Lemma args_ok_vf : ltac2:(Q6nq.ty1 'GwI.segs '(@QzQg.Mq1.args_ok_vf) [[@gw_eq_args_ok__3; @gw_eq_args_ok__2; @gw_eq_args_ok]; [@gw_eq_gfile_cells__3; @gw_eq_gfile_cells__2; @gw_eq_gfile_cells]; [@gw_eq_towrite_g_stmt__3; @gw_eq_towrite_g_stmt__2; @gw_eq_towrite_g_stmt]] '([232]%Z : list Z) 'gwt_X).
Proof. ltac2:(GwEq.gw_rw [[@gw_eq_args_ok__3; @gw_eq_args_ok__2; @gw_eq_args_ok]]); first [GwApply.gw_by_name GwI.segs (@QzQg.Mq1.args_ok_vf) | autorewrite with gw_eqs; GwApply.gw_by_name GwI.segs (@QzQg.Mq1.args_ok_vf)]. Qed.

Lemma rw_cells_unmerge : ltac2:(Q6nq.ty1 'GwI.segs '(@QzQg.Mq1.rw_cells_unmerge) [[@gw_eq_gfile_cells__3; @gw_eq_gfile_cells__2; @gw_eq_gfile_cells]; [@gw_eq_towrite_g_stmt__3; @gw_eq_towrite_g_stmt__2; @gw_eq_towrite_g_stmt]] '(@nil Z) 'gwt_X).
Proof. first [GwApply.gw_by_name GwI.segs (@QzQg.Mq1.rw_cells_unmerge) | autorewrite with gw_eqs; GwApply.gw_by_name GwI.segs (@QzQg.Mq1.rw_cells_unmerge)]. Qed.

Lemma rwc_eq : forall m A A' cs, rw_cells rsegs m A cs -> A = A' -> rw_cells rsegs m A' cs.
Proof. first [GwApply.gw_by_name GwI.segs (@QzQg.Mq1.rwc_eq) | autorewrite with gw_eqs; GwApply.gw_by_name GwI.segs (@QzQg.Mq1.rwc_eq)]. Qed.
Ltac piece H := eapply rwc_eq; [exact H | cbn [cells_size csize Nat.add app]; lia].

Lemma rw_cells_CB0 : forall m B, 0 <= B -> B <= 2^64 -> rw_cells rsegs m B [CB 0 []].
Proof. first [GwApply.gw_by_name GwI.segs (@QzQg.Mq1.rw_cells_CB0) | autorewrite with gw_eqs; GwApply.gw_by_name GwI.segs (@QzQg.Mq1.rw_cells_CB0)]. Qed.

Definition snfile_head (wend wpos wbase buf bufsize : Z) (mode : word) : list cell :=
gfile_cells (Z_to_bv 64 0) 0 0 0 wend wpos wbase 0x59f78 0 buf bufsize 0 mode (Z_to_bv 64 0xffffffff) 0xffffffff.
Lemma gw_eq_snfile_head : @snfile_head = ltac:(GwInst.gw_term (@QzQg.Mq1.snfile_head 0x59f78%Z) (@snfile_head)). Proof. unfold snfile_head, QzQg.Mq1.snfile_head; rewrite ?gw_eq_gfile_cells; first [reflexivity | autorewrite with gw_eqs; reflexivity]. Qed.
#[export] Hint Rewrite gw_eq_snfile_head : gw_eqs.
Definition snfile_rest (CK : Z) : list cell :=
[C4 z64; C8 (Z_to_bv 64 CK); C8 z64; C8 z64; C8 z64; C8 z64; C8 z64; C8 z64; C8 z64; C8 z64; C8 z64].
Lemma gw_eq_snfile_rest : @snfile_rest = ltac:(GwInst.gw_term (@QzQg.Mq1.snfile_rest) (@snfile_rest)). Proof. unfold snfile_rest, QzQg.Mq1.snfile_rest; first [reflexivity | autorewrite with gw_eqs; reflexivity]. Qed.
#[export] Hint Rewrite gw_eq_snfile_rest : gw_eqs.

Definition VF_FRAME : Z := 368.
Lemma gw_eq_VF_FRAME : @VF_FRAME = ltac:(GwInst.gw_term (@QzQg.Mq1.VF_FRAME) (@VF_FRAME)). Proof. unfold VF_FRAME, QzQg.Mq1.VF_FRAME; first [reflexivity | autorewrite with gw_eqs; reflexivity]. Qed.
#[export] Hint Rewrite gw_eq_VF_FRAME : gw_eqs.

Definition vfprintf_sn_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word)
(Fp CK D n : Z) (dn : nat) (junkd : list byte) (r : Z) (o : list Z) (lo : Z) (canary : word) (m : mem) : machine_state -> Prop :=
fun ms' => exists (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (Ft : bvmap 5 word) (fc' : bv 32) (fjunk : list byte) (m' : mem),
ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 r) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
Ft (ret_pc ra) fc' None m' (seg_rom rsegs)
/\ munch [(lo, bv_unsigned sp); (Fp, Fp + 232); (CK, CK + 16); (D, D + Z.of_nat dn)] m m' /\ wmono rsegs m m' /\ mem_inv rsegs m'
/\ frm0 fc'
/\ (forall k : reg, bv_unsigned k <> 10 -> reg_get Ft k = reg_get F k)
/\ stk rsegs m' lo (bv_unsigned sp)
/\ ssp_cells m' canary
/\ rw_cells rsegs m' D [CB dn (zb o ++ Z_to_bv 8 0 :: skipn (S (length o)) junkd)]
/\ rw_cells rsegs m' CK [C8 (Z_to_bv 64 (D + zlength o)); C8 (Z_to_bv 64 (n - zlength o))]
/\ rw_cells rsegs m' Fp [CB 232 fjunk].
Lemma gw_eq_vfprintf_sn_post : @vfprintf_sn_post = ltac:(GwInst.gw_term (@QzQg.Mq1.vfprintf_sn_post rsegs got_ssp ssp_guard) (@vfprintf_sn_post)). Proof. unfold vfprintf_sn_post, QzQg.Mq1.vfprintf_sn_post; ltac2:(GwEq.gw_rw [[@gw_eq_ssp_cells__3; @gw_eq_ssp_cells__2; @gw_eq_ssp_cells]; [@gw_eq_zb__3; @gw_eq_zb__2; @gw_eq_zb]]); first [reflexivity | autorewrite with gw_eqs; reflexivity]. Qed.
#[export] Hint Rewrite gw_eq_vfprintf_sn_post : gw_eqs.

Definition vfprintf_sn_stmt : Prop :=
forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : mem)
(Fp CK D n bufp A VA : Z) (dn : nat) (junkd : list byte) (fmt : list Z) (slots : list word) (args : list parg)
(lo : Z) (canary : word) (r : Z) (o : list Z),
let q := bv_unsigned sp in
a0 = Z_to_bv 64 Fp -> a1 = Z_to_bv 64 A -> a2 = Z_to_bv 64 VA ->
rw_cells rsegs m Fp (snfile_head 0 0 0 bufp 0 (Z_to_bv 64 0)) -> rw_cells rsegs m (Fp + 148) (snfile_rest CK) ->
rw_cells rsegs m CK [C8 (Z_to_bv 64 D); C8 (Z_to_bv 64 n)] ->
rw_cells rsegs m D [CB dn junkd] ->
bytes_at rsegs m A (zb fmt) -> Forall (fun c => 0 <= c < 256) fmt -> pass1_ok fmt = true ->
va_area m VA slots -> args_ok Fp (q - 352) 80 m lo q (q - VF_FRAME) slots args ->
printf_model OUT_sn OUTFP_sn fmt args [] = QlEo.Mq0.Ret (Ok (r, o)) ->
Forall (fun c => let '(y, w, p, fl, t) := c in fmt_fp_facts y fl p t) (fp_calls (length fmt) fmt args) ->
(length o < dn)%nat -> (zlength o <= n < 2^63) -> (0 < bufp < 2^64) ->
stk rsegs m lo q -> (lo <= q - VF_FRAME - PC_DEPTH) -> (GLOBALS_TOP <= lo) -> (q < 2^63) ->
ssp_cells m canary -> mem_inv rsegs m -> frm0 fc ->
(65536 <= A) -> (A + zlength fmt <= STATIC_SPLIT) ->
(q <= Fp) -> (Fp + 232 <= VA) -> (VA + 8 * zlength slots <= 2^64) ->
(q <= CK) -> (CK + 16 <= Fp \/ Fp + 232 <= CK) -> (CK + 16 < 2^64) ->
(D + Z.of_nat dn <= lo \/ q <= D) -> (D + Z.of_nat dn <= Fp \/ Fp + 232 <= D) -> (D + Z.of_nat dn <= CK \/ CK + 16 <= D) -> (D + Z.of_nat dn <= 65536 \/ GLOBALS_TOP <= D \/ (STATIC_SPLIT <= D /\ D + Z.of_nat dn <= got_ssp) \/ (got_ssp + 8 <= D /\ D + Z.of_nat dn <= ssp_guard) \/ (ssp_guard + 8 <= D /\ D + Z.of_nat dn <= GLOBALS_TOP)) ->
evt rsegs (vfprintf_sn_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F Fp CK D n dn junkd r o lo canary m)
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0x55474) fc None m (seg_rom rsegs)).
Lemma gw_eq_vfprintf_sn_stmt : @vfprintf_sn_stmt = ltac:(GwInst.gw_term (@QzQg.Mq1.vfprintf_sn_stmt rsegs 0x55474 got_ssp GLOBALS_TOP STATIC_SPLIT ssp_guard 0x59f78%Z) (@vfprintf_sn_stmt)). Proof. unfold vfprintf_sn_stmt, QzQg.Mq1.vfprintf_sn_stmt; rewrite ?gw_eq_snfile_head, ?gw_eq_snfile_rest, ?gw_eq_VF_FRAME, ?gw_eq_vfprintf_sn_post; ltac2:(GwEq.gw_rw [[@gw_eq_OUTFP_sn__3; @gw_eq_OUTFP_sn__2; @gw_eq_OUTFP_sn]; [@gw_eq_OUT_sn__3; @gw_eq_OUT_sn__2; @gw_eq_OUT_sn]; [@gw_eq_PC_DEPTH__3; @gw_eq_PC_DEPTH__2; @gw_eq_PC_DEPTH]; [@gw_eq_args_ok__3; @gw_eq_args_ok__2; @gw_eq_args_ok]; [@gw_eq_fmt_fp_facts__3; @gw_eq_fmt_fp_facts__2; @gw_eq_fmt_fp_facts]; [@gw_eq_fp_calls__3; @gw_eq_fp_calls__2; @gw_eq_fp_calls]; [@gw_eq_pass1_ok__3; @gw_eq_pass1_ok__2; @gw_eq_pass1_ok]; [@gw_eq_printf_model__3; @gw_eq_printf_model__2; @gw_eq_printf_model]; [@gw_eq_ssp_cells__3; @gw_eq_ssp_cells__2; @gw_eq_ssp_cells]; [@gw_eq_va_area__3; @gw_eq_va_area__2; @gw_eq_va_area]; [@gw_eq_zb__3; @gw_eq_zb__2; @gw_eq_zb]]); first [reflexivity | autorewrite with gw_eqs; reflexivity]. Qed.
#[export] Hint Rewrite gw_eq_vfprintf_sn_stmt : gw_eqs.

Theorem vfprintf_sn_proof : vfprintf_sn_stmt.
Proof. rewrite ?gw_eq_vfprintf_sn_stmt; first [GwApply.gw_by_name GwI.segs (@QzQg.Mq1.vfprintf_sn_proof) | autorewrite with gw_eqs; GwApply.gw_by_name GwI.segs (@QzQg.Mq1.vfprintf_sn_proof)]. Qed.
