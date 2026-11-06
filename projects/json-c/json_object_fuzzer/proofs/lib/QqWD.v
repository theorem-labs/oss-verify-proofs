(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)


From OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib Require CodeAt StepGen GwInst GwApply GwApply2. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q6nq.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q0Hd.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QheR.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QC8c.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QCcH.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q0Ek.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q6hv.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QT7b.

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QXup.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QXup. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q5Rg.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q5Rg.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qazd.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qazd.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Lib.GwApply.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QCcH.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QCcH. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q0Ek.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q0Ek.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QC8c.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QC8c.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qsw7.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qsw7. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QJjn.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QJjn. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QRUw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QRUw. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q8tj.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q8tj.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QgoP.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QgoP.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qwmw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qwmw.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QSL3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QSL3.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QXZq.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QXZq. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q22i.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q22i. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q6hv.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q6hv. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QT7b.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QT7b.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QnCn.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QnCn.
Import ListNotations. Unset Keyed Unification. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr.
Open Scope Z_scope.

Module GwI.
Definition segs := usegs.
Definition base := 0x287fc%Z.
Definition e_blk_1a328 := 0x28b80%Z.
Lemma CODE : CodeAt.code_at usegs 0x287fc QheR.ulhlookup_code.  Proof. StepGen.code_at_vm. Qed.
Lemma BASE4 : (0x287fc mod 4 = 0)%Z.  Proof. reflexivity. Qed.
Lemma BASER : (0 <= 0x287fc /\ 0x287fc + 316 <= 2^40)%Z.  Proof. vm_compute. split; discriminate. Qed.

Local Notation gw_RC := Q6q3.RunConsts (only parsing).
Local Ltac gw_lay t := let v := eval cbv beta iota delta [QC8c.U4L QCcH.hl_malloc QCcH.hl_free QCcH.hl_calloc QCcH.hl_realloc QCcH.hl_malloc2 QCcH.hl_free2 QCcH.hl_tp QCcH.hl_got_guard QCcH.hl_guard QCcH.hl_auxv QCcH.hl_libc QCcH.hl_img_lo QCcH.hl_img_hi QCcH.hl_consts] in t in lazymatch v with (fun _ => ?n) => exact n end.
Local Ltac gw_hex k := let v := eval cbv beta iota delta [QC8c.U4L QCcH.hl_consts] in (fun RC__ : gw_RC => @QCcH.hl_consts RC__ (@QC8c.U4L RC__)) in
lazymatch v with (fun _ => cons (pair ?a (?f1 (?f2 ?b))) (cons (pair _ (?f3 (?f4 ?c))) nil)) => lazymatch k with 0%nat => exact a | 1%nat => exact b | _ => exact c end end.
Definition e_malloc : Z := ltac:(gw_lay (fun RC__ : gw_RC => @QCcH.hl_malloc RC__ (@QC8c.U4L RC__))).
Definition e_free : Z := ltac:(gw_lay (fun RC__ : gw_RC => @QCcH.hl_free RC__ (@QC8c.U4L RC__))).
Definition e_calloc : Z := ltac:(gw_lay (fun RC__ : gw_RC => @QCcH.hl_calloc RC__ (@QC8c.U4L RC__))).
Definition e_realloc : Z := ltac:(gw_lay (fun RC__ : gw_RC => @QCcH.hl_realloc RC__ (@QC8c.U4L RC__))).
Definition e_malloc2 : Z := ltac:(gw_lay (fun RC__ : gw_RC => @QCcH.hl_malloc2 RC__ (@QC8c.U4L RC__))).
Definition e_free2 : Z := ltac:(gw_lay (fun RC__ : gw_RC => @QCcH.hl_free2 RC__ (@QC8c.U4L RC__))).
Definition gTP : Z := ltac:(gw_lay (fun RC__ : gw_RC => @QCcH.hl_tp RC__ (@QC8c.U4L RC__))).
Definition gGOTG : Z := ltac:(gw_lay (fun RC__ : gw_RC => @QCcH.hl_got_guard RC__ (@QC8c.U4L RC__))).
Definition gGUARD : Z := ltac:(gw_lay (fun RC__ : gw_RC => @QCcH.hl_guard RC__ (@QC8c.U4L RC__))).
Definition gAUXV : Z := ltac:(gw_lay (fun RC__ : gw_RC => @QCcH.hl_auxv RC__ (@QC8c.U4L RC__))).
Definition gLIBC : Z := ltac:(gw_lay (fun RC__ : gw_RC => @QCcH.hl_libc RC__ (@QC8c.U4L RC__))).
Definition gIMG_LO : Z := ltac:(gw_lay (fun RC__ : gw_RC => @QCcH.hl_img_lo RC__ (@QC8c.U4L RC__))).
Definition gIMG_HI : Z := ltac:(gw_lay (fun RC__ : gw_RC => @QCcH.hl_img_hi RC__ (@QC8c.U4L RC__))).
Definition gHEXGOT : Z := ltac:(gw_hex 0%nat).  Definition gHEXPTR : Z := ltac:(gw_hex 1%nat).  Definition gHEXCHARS : Z := ltac:(gw_hex 2%nat).
Definition gVOL := QC8c.u4_volatile.  Definition gCS := QC8c.u4_client_static.
Definition gH1 := fun RC__ : gw_RC => @QCcH.hl_static_in_img RC__ (@QC8c.U4L RC__).
Definition gH2 := fun RC__ : gw_RC => @QCcH.hl_img_range RC__ (@QC8c.U4L RC__).
Definition gH3 := fun RC__ : gw_RC => @QCcH.hl_scratch_in_img RC__ (@QC8c.U4L RC__).
Definition gH4 := fun RC__ : gw_RC => @QCcH.hl_scratch_not_static RC__ (@QC8c.U4L RC__).
Definition gH5 := fun RC__ : gw_RC => @QCcH.hl_consts_ok RC__ (@QC8c.U4L RC__).
Definition e_fn_obj_to_json_string := Eval cbv beta iota delta [Q0Ek.fn_obj_to_json_string QC8c.U4F] in (Q0Ek.fn_obj_to_json_string QC8c.U4F).
Definition e_fn_arr_to_json_string := Eval cbv beta iota delta [Q0Ek.fn_arr_to_json_string QC8c.U4F] in (Q0Ek.fn_arr_to_json_string QC8c.U4F).
Definition e_fn_bool_to_json_string := Eval cbv beta iota delta [Q0Ek.fn_bool_to_json_string QC8c.U4F] in (Q0Ek.fn_bool_to_json_string QC8c.U4F).
Definition e_fn_dbl_to_json_string := Eval cbv beta iota delta [Q0Ek.fn_dbl_to_json_string QC8c.U4F] in (Q0Ek.fn_dbl_to_json_string QC8c.U4F).
Definition e_fn_int_to_json_string := Eval cbv beta iota delta [Q0Ek.fn_int_to_json_string QC8c.U4F] in (Q0Ek.fn_int_to_json_string QC8c.U4F).
Definition e_fn_str_to_json_string := Eval cbv beta iota delta [Q0Ek.fn_str_to_json_string QC8c.U4F] in (Q0Ek.fn_str_to_json_string QC8c.U4F).
Definition e_fn_ud_to_json_string := Eval cbv beta iota delta [Q0Ek.fn_ud_to_json_string QC8c.U4F] in (Q0Ek.fn_ud_to_json_string QC8c.U4F).
Definition e_fn_free_userdata := Eval cbv beta iota delta [Q0Ek.fn_free_userdata QC8c.U4F] in (Q0Ek.fn_free_userdata QC8c.U4F).
Definition e_fn_lh_entry_free := Eval cbv beta iota delta [Q0Ek.fn_lh_entry_free QC8c.U4F] in (Q0Ek.fn_lh_entry_free QC8c.U4F).
Definition e_fn_lh_char_hash := Eval cbv beta iota delta [Q0Ek.fn_lh_char_hash QC8c.U4F] in (Q0Ek.fn_lh_char_hash QC8c.U4F).
Definition e_fn_lh_char_equal := Eval cbv beta iota delta [Q0Ek.fn_lh_char_equal QC8c.U4F] in (Q0Ek.fn_lh_char_equal QC8c.U4F).
Definition e_fn_arr_entry_free := Eval cbv beta iota delta [Q0Ek.fn_arr_entry_free QC8c.U4F] in (Q0Ek.fn_arr_entry_free QC8c.U4F).
Definition u_lh_char_equal_spec := @Q6hv.u_lh_char_equal_spec.
Definition ent_addr_mod8 := @QT7b.ent_addr_mod8.
Definition pS4L := Eval cbv beta delta [Q0Hd.gl segs e_malloc e_free e_calloc e_realloc e_malloc2 e_free2 gTP gGOTG gGUARD gAUXV gLIBC gVOL gCS gHEXGOT gHEXPTR gHEXCHARS gIMG_LO gIMG_HI] in
(fun RC__ : gw_RC => @Q0Hd.gl RC__ segs e_malloc e_free e_calloc e_realloc e_malloc2 e_free2 gTP gGOTG gGUARD gAUXV gLIBC gVOL gCS gHEXGOT gHEXPTR gHEXCHARS gIMG_LO gIMG_HI (gH1 RC__) (gH2 RC__) (gH3 RC__) (gH4 RC__) (gH5 RC__)).
Definition pS4F := Eval cbv beta delta [Q0Hd.gf e_fn_obj_to_json_string e_fn_arr_to_json_string e_fn_bool_to_json_string e_fn_dbl_to_json_string e_fn_int_to_json_string e_fn_str_to_json_string e_fn_ud_to_json_string e_fn_free_userdata e_fn_lh_entry_free e_fn_lh_char_hash e_fn_lh_char_equal e_fn_arr_entry_free] in
(Q0Hd.gf e_fn_obj_to_json_string e_fn_arr_to_json_string e_fn_bool_to_json_string e_fn_dbl_to_json_string e_fn_int_to_json_string e_fn_str_to_json_string e_fn_ud_to_json_string e_fn_free_userdata e_fn_lh_entry_free e_fn_lh_char_hash e_fn_lh_char_equal e_fn_arr_entry_free).
End GwI.

Definition u_lh_lookup_entry : Z := 0x287fc.

Local Definition gwt_X : unit := (Q6nq.gwt_def (@QRGY.Mq0.u_lh_char_equal_post) (@Q6hv.u_lh_char_equal_post) (Q6nq.gwt_def (@QheR.u_lh_char_equal_post) (@Q6hv.u_lh_char_equal_post) (Q6nq.gwt_def (@Q9Mh.Mq3.next_ix) (@Q22i.next_ix) (Q6nq.gwt_pat GwI.pS4L (@QC8c.U4L) (Q6nq.gwt_pat GwI.pS4F QC8c.U4F Q6nq.gwt_nil))))).
Lemma mul40_chk : ltac2:(Q6nq.tyx '(@QheR.mul40_chk) [] '(@nil Z) '(Q6nq.gwt_def (@QheR.u_lh_lookup_entry) (@u_lh_lookup_entry) gwt_X)).
Proof. first [GwInst.gw_exact (@QheR.mul40_chk) | autorewrite with gw_eqs; GwInst.gw_exact (@QheR.mul40_chk)]. Qed.

Section ULhLookup.
Variables (ra sp gp tp : word) (s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32).
Variables (t tbl size kp lo : Z) (es : list lent) (svs : list slotv) (ps : list byte).

Definition u_lookup_res (r : Z) : Prop :=
r = 0 \/ exists j e, nth_error es j = Some e /\ r = ent_addr tbl (le_ix e) /\ le_ks e = ps.

Definition u_lh_lookup_post (m : word -> option byte) : machine_state -> Prop :=
fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 (r : Z) m',
ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 r) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc ra) fc None m' (seg_rom usegs)
/\ munch [(bv_unsigned sp - 96, bv_unsigned sp)] m m' /\ wmono usegs m m' /\ mem_inv usegs m'
/\ stk usegs m' lo (bv_unsigned sp)
/\ lh_open usegs U4F m' t tbl size es svs
/\ bytes_at usegs m' kp (ps ++ [b0])
/\ u_lookup_res r.

Definition ulk_frame (m : word -> option byte) (junk8 : list byte) : Prop :=
rw_cells usegs m (bv_unsigned sp + -80) [CB 8 junk8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].

#[using="Type"] Lemma u_lh_lookup_next : ltac2:(Q6nq.ty2 'GwI.segs '(@QheR.u_lh_lookup_next) [] '([(-80); 165984; 166016; 166148]%Z : list Z) '(Q6nq.gwt_def (@QheR.ulk_frame) (@ulk_frame) (Q6nq.gwt_def (@QheR.u_lh_lookup_post) (@u_lh_lookup_post) (Q6nq.gwt_def (@QheR.u_lookup_res) (@u_lookup_res) (Q6nq.gwt_def (@QheR.u_lh_lookup_entry) (@u_lh_lookup_entry) gwt_X))))).
Proof. first [GwApply2.gw_by_name2 GwI.segs (@QheR.u_lh_lookup_next) | autorewrite with gw_eqs; GwApply2.gw_by_name2 GwI.segs (@QheR.u_lh_lookup_next)]. Qed.

#[using="Type"] Lemma u_lh_lookup_exit0 : ltac2:(Q6nq.ty2 'GwI.segs '(@QheR.u_lh_lookup_exit0) [] '([(-96); (-80); 166148]%Z : list Z) '(Q6nq.gwt_def (@QheR.ulk_frame) (@ulk_frame) (Q6nq.gwt_def (@QheR.u_lh_lookup_post) (@u_lh_lookup_post) (Q6nq.gwt_def (@QheR.u_lookup_res) (@u_lookup_res) (Q6nq.gwt_def (@QheR.u_lh_lookup_entry) (@u_lh_lookup_entry) gwt_X))))).
Proof. first [GwApply2.gw_by_name2 GwI.segs (@QheR.u_lh_lookup_exit0) | autorewrite with gw_eqs; GwApply2.gw_by_name2 GwI.segs (@QheR.u_lh_lookup_exit0)]. Qed.

#[using="Type"] Lemma u_lh_lookup_exit1 : ltac2:(Q6nq.ty2 'GwI.segs '(@QheR.u_lh_lookup_exit1) [] '([(-96); (-80); 166104]%Z : list Z) '(Q6nq.gwt_def (@QheR.ulk_frame) (@ulk_frame) (Q6nq.gwt_def (@QheR.u_lh_lookup_post) (@u_lh_lookup_post) (Q6nq.gwt_def (@QheR.u_lookup_res) (@u_lookup_res) (Q6nq.gwt_def (@QheR.u_lh_lookup_entry) (@u_lh_lookup_entry) gwt_X))))).
Proof. first [GwApply2.gw_by_name2 GwI.segs (@QheR.u_lh_lookup_exit1) | autorewrite with gw_eqs; GwApply2.gw_by_name2 GwI.segs (@QheR.u_lh_lookup_exit1)]. Qed.

#[using="Type"] Lemma u_lh_lookup_loop : ltac2:(Q6nq.ty2 'GwI.segs '(@QheR.u_lh_lookup_loop) [] '([(-96); (-80); 166016]%Z : list Z) '(Q6nq.gwt_def (@QheR.ulk_frame) (@ulk_frame) (Q6nq.gwt_def (@QheR.u_lh_lookup_post) (@u_lh_lookup_post) (Q6nq.gwt_def (@QheR.u_lookup_res) (@u_lookup_res) (Q6nq.gwt_def (@QheR.u_lh_lookup_entry) (@u_lh_lookup_entry) gwt_X))))).
Proof. first [GwApply2.gw_by_name2 GwI.segs (@QheR.u_lh_lookup_loop) | autorewrite with gw_eqs; GwApply2.gw_by_name2 GwI.segs (@QheR.u_lh_lookup_loop)]. Qed.

#[using="Type"] Lemma u_lh_lookup_spec : ltac2:(Q6nq.ty2 'GwI.segs '(@QheR.u_lh_lookup_spec) [] '([(-96)]%Z : list Z) '(Q6nq.gwt_zc u_lh_lookup_entry (Q6nq.gwt_def (@QheR.ulk_frame) (@ulk_frame) (Q6nq.gwt_def (@QheR.u_lh_lookup_post) (@u_lh_lookup_post) (Q6nq.gwt_def (@QheR.u_lookup_res) (@u_lookup_res) (Q6nq.gwt_def (@QheR.u_lh_lookup_entry) (@u_lh_lookup_entry) gwt_X)))))).
Proof. first [GwApply2.gw_by_name2 GwI.segs (@QheR.u_lh_lookup_spec) | autorewrite with gw_eqs; GwApply2.gw_by_name2 GwI.segs (@QheR.u_lh_lookup_spec)]. Qed.
End ULhLookup.
