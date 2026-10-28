(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)


From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib Require CodeAt StepGen GwInst GwApply GwApply2. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Q6nq.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Q0Hd.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Q7mx.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UC8c.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QCcH.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Q0Ek.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require Uihm.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UlCE.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QAyu.

From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QXup.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QXup.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UEQM.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UEQM.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Lib.GwApply.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QRjH.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QRjH.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QHnV.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QHnV. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QCcH.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QCcH. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QfLs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QfLs. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Q0Ek.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q0Ek. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Qtgi.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qtgi. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QjDH.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QjDH.Mq0.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UC8c.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UC8c.Mq0.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Qsw7.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qsw7. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QJjn.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QJjn.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require Uihm.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Uihm. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UPZI.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UPZI.Mq4. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UlCE.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UlCE.Mq1. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UhHQ.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UhHQ.
Import ListNotations. Unset Keyed Unification. Local Ltac Qfw3.Mq3.model_reg_tac n X mexpr ::= Qfw3.Mq3.mkr__model_reg_tac_1 n X mexpr.
Open Scope Z_scope.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Q6q3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q6q3.

Module GwI.
Definition segs := rsegs.
Definition base := 0x216b0%Z.
Definition w_19 := 0x765010ef%Z.
Definition w_24 := 0x41d2e0ef%Z.
Definition w_34 := 0x6dd010ef%Z.
Definition w_36 := 0x3ed2e0ef%Z.
Definition w_44 := 0x3cd2e06f%Z.
Definition joff_19 := (Z_to_bv 21 8036).
Definition joff_24 := (Z_to_bv 21 191516).
Definition joff_34 := (Z_to_bv 21 7900).
Definition joff_36 := (Z_to_bv 21 191468).
Definition joff_44 := (Z_to_bv 21 191436).
Definition e_pbfree := 0x23614%Z.
Definition e_blk_16158 := 0x23660%Z.

Local Notation gw_RC := Q6q3.RunConsts (only parsing).
Local Ltac gw_lay t := let v := eval cbv beta iota delta [UC8c.Mq0.S4L QCcH.hl_malloc QCcH.hl_free QCcH.hl_calloc QCcH.hl_realloc QCcH.hl_malloc2 QCcH.hl_free2 QCcH.hl_tp QCcH.hl_got_guard QCcH.hl_guard QCcH.hl_auxv QCcH.hl_libc QCcH.hl_img_lo QCcH.hl_img_hi QCcH.hl_consts] in t in lazymatch v with (fun _ => ?n) => exact n end.
Local Ltac gw_hex k := let v := eval cbv beta iota delta [UC8c.Mq0.S4L QCcH.hl_consts] in (fun RC__ : gw_RC => @QCcH.hl_consts RC__ (@UC8c.Mq0.S4L RC__)) in
lazymatch v with (fun _ => cons (pair ?a (?f1 (?f2 ?b))) (cons (pair _ (?f3 (?f4 ?c))) nil)) => lazymatch k with 0%nat => exact a | 1%nat => exact b | _ => exact c end end.
Definition e_malloc : Z := ltac:(gw_lay (fun RC__ : gw_RC => @QCcH.hl_malloc RC__ (@UC8c.Mq0.S4L RC__))).
Definition e_free : Z := ltac:(gw_lay (fun RC__ : gw_RC => @QCcH.hl_free RC__ (@UC8c.Mq0.S4L RC__))).
Definition e_calloc : Z := ltac:(gw_lay (fun RC__ : gw_RC => @QCcH.hl_calloc RC__ (@UC8c.Mq0.S4L RC__))).
Definition e_realloc : Z := ltac:(gw_lay (fun RC__ : gw_RC => @QCcH.hl_realloc RC__ (@UC8c.Mq0.S4L RC__))).
Definition e_malloc2 : Z := ltac:(gw_lay (fun RC__ : gw_RC => @QCcH.hl_malloc2 RC__ (@UC8c.Mq0.S4L RC__))).
Definition e_free2 : Z := ltac:(gw_lay (fun RC__ : gw_RC => @QCcH.hl_free2 RC__ (@UC8c.Mq0.S4L RC__))).
Definition gTP : Z := ltac:(gw_lay (fun RC__ : gw_RC => @QCcH.hl_tp RC__ (@UC8c.Mq0.S4L RC__))).
Definition gGOTG : Z := ltac:(gw_lay (fun RC__ : gw_RC => @QCcH.hl_got_guard RC__ (@UC8c.Mq0.S4L RC__))).
Definition gGUARD : Z := ltac:(gw_lay (fun RC__ : gw_RC => @QCcH.hl_guard RC__ (@UC8c.Mq0.S4L RC__))).
Definition gAUXV : Z := ltac:(gw_lay (fun RC__ : gw_RC => @QCcH.hl_auxv RC__ (@UC8c.Mq0.S4L RC__))).
Definition gLIBC : Z := ltac:(gw_lay (fun RC__ : gw_RC => @QCcH.hl_libc RC__ (@UC8c.Mq0.S4L RC__))).
Definition gIMG_LO : Z := ltac:(gw_lay (fun RC__ : gw_RC => @QCcH.hl_img_lo RC__ (@UC8c.Mq0.S4L RC__))).
Definition gIMG_HI : Z := ltac:(gw_lay (fun RC__ : gw_RC => @QCcH.hl_img_hi RC__ (@UC8c.Mq0.S4L RC__))).
Definition gHEXGOT : Z := ltac:(gw_hex 0%nat).  Definition gHEXPTR : Z := ltac:(gw_hex 1%nat).  Definition gHEXCHARS : Z := ltac:(gw_hex 2%nat).
Definition gVOL := UC8c.Mq0.s4_volatile.  Definition gCS := UC8c.Mq0.s4_client_static.
Definition gH1 := fun RC__ : gw_RC => @QCcH.hl_static_in_img RC__ (@UC8c.Mq0.S4L RC__).
Definition gH2 := fun RC__ : gw_RC => @QCcH.hl_img_range RC__ (@UC8c.Mq0.S4L RC__).
Definition gH3 := fun RC__ : gw_RC => @QCcH.hl_scratch_in_img RC__ (@UC8c.Mq0.S4L RC__).
Definition gH4 := fun RC__ : gw_RC => @QCcH.hl_scratch_not_static RC__ (@UC8c.Mq0.S4L RC__).
Definition gH5 := fun RC__ : gw_RC => @QCcH.hl_consts_ok RC__ (@UC8c.Mq0.S4L RC__).
Definition e_fn_obj_to_json_string := Eval cbv beta iota delta [Q0Ek.fn_obj_to_json_string UC8c.Mq0.S4F] in (Q0Ek.fn_obj_to_json_string UC8c.Mq0.S4F).
Definition e_fn_arr_to_json_string := Eval cbv beta iota delta [Q0Ek.fn_arr_to_json_string UC8c.Mq0.S4F] in (Q0Ek.fn_arr_to_json_string UC8c.Mq0.S4F).
Definition e_fn_bool_to_json_string := Eval cbv beta iota delta [Q0Ek.fn_bool_to_json_string UC8c.Mq0.S4F] in (Q0Ek.fn_bool_to_json_string UC8c.Mq0.S4F).
Definition e_fn_dbl_to_json_string := Eval cbv beta iota delta [Q0Ek.fn_dbl_to_json_string UC8c.Mq0.S4F] in (Q0Ek.fn_dbl_to_json_string UC8c.Mq0.S4F).
Definition e_fn_int_to_json_string := Eval cbv beta iota delta [Q0Ek.fn_int_to_json_string UC8c.Mq0.S4F] in (Q0Ek.fn_int_to_json_string UC8c.Mq0.S4F).
Definition e_fn_str_to_json_string := Eval cbv beta iota delta [Q0Ek.fn_str_to_json_string UC8c.Mq0.S4F] in (Q0Ek.fn_str_to_json_string UC8c.Mq0.S4F).
Definition e_fn_ud_to_json_string := Eval cbv beta iota delta [Q0Ek.fn_ud_to_json_string UC8c.Mq0.S4F] in (Q0Ek.fn_ud_to_json_string UC8c.Mq0.S4F).
Definition e_fn_free_userdata := Eval cbv beta iota delta [Q0Ek.fn_free_userdata UC8c.Mq0.S4F] in (Q0Ek.fn_free_userdata UC8c.Mq0.S4F).
Definition e_fn_lh_entry_free := Eval cbv beta iota delta [Q0Ek.fn_lh_entry_free UC8c.Mq0.S4F] in (Q0Ek.fn_lh_entry_free UC8c.Mq0.S4F).
Definition e_fn_lh_char_hash := Eval cbv beta iota delta [Q0Ek.fn_lh_char_hash UC8c.Mq0.S4F] in (Q0Ek.fn_lh_char_hash UC8c.Mq0.S4F).
Definition e_fn_lh_char_equal := Eval cbv beta iota delta [Q0Ek.fn_lh_char_equal UC8c.Mq0.S4F] in (Q0Ek.fn_lh_char_equal UC8c.Mq0.S4F).
Definition e_fn_arr_entry_free := Eval cbv beta iota delta [Q0Ek.fn_arr_entry_free UC8c.Mq0.S4F] in (Q0Ek.fn_arr_entry_free UC8c.Mq0.S4F).
Definition printbuf_free_cps := @Uihm.printbuf_free_cps.
Definition lb_remove_zero := @UlCE.Mq1.lb_remove_zero.
Definition pS4L := Eval cbv beta delta [Q0Hd.gl segs e_malloc e_free e_calloc e_realloc e_malloc2 e_free2 gTP gGOTG gGUARD gAUXV gLIBC gVOL gCS gHEXGOT gHEXPTR gHEXCHARS gIMG_LO gIMG_HI] in
(fun RC__ : gw_RC => @Q0Hd.gl RC__ segs e_malloc e_free e_calloc e_realloc e_malloc2 e_free2 gTP gGOTG gGUARD gAUXV gLIBC gVOL gCS gHEXGOT gHEXPTR gHEXCHARS gIMG_LO gIMG_HI (gH1 RC__) (gH2 RC__) (gH3 RC__) (gH4 RC__) (gH5 RC__)).
Definition pS4F := Eval cbv beta delta [Q0Hd.gf e_fn_obj_to_json_string e_fn_arr_to_json_string e_fn_bool_to_json_string e_fn_dbl_to_json_string e_fn_int_to_json_string e_fn_str_to_json_string e_fn_ud_to_json_string e_fn_free_userdata e_fn_lh_entry_free e_fn_lh_char_hash e_fn_lh_char_equal e_fn_arr_entry_free] in
(Q0Hd.gf e_fn_obj_to_json_string e_fn_arr_to_json_string e_fn_bool_to_json_string e_fn_dbl_to_json_string e_fn_int_to_json_string e_fn_str_to_json_string e_fn_ud_to_json_string e_fn_free_userdata e_fn_lh_entry_free e_fn_lh_char_hash e_fn_lh_char_equal e_fn_arr_entry_free).
End GwI.

Section RC__1. Context {RC__ : Q6q3.RunConsts}.

#[using="Type"] Lemma firstn_lupd_ge : forall {A} (l : list A) n i x, (n <= i)%nat -> firstn n (lupd l i x) = firstn n l.
Proof. first [GwApply2.gw_by_name2 GwI.segs (@Q7mx.Mq2.firstn_lupd_ge) | autorewrite with gw_eqs; GwApply2.gw_by_name2 GwI.segs (@Q7mx.Mq2.firstn_lupd_ge)]. Qed.

#[using="Type"] Lemma lvblocks_lupd_ge : forall levels n i x, (n <= i)%nat -> lvblocks (lupd levels i x) n = lvblocks levels n.
Proof. first [GwApply2.gw_by_name2 GwI.segs (@Q7mx.Mq2.lvblocks_lupd_ge) | autorewrite with gw_eqs; GwApply2.gw_by_name2 GwI.segs (@Q7mx.Mq2.lvblocks_lupd_ge)]. Qed.

Local Definition gwt_X : unit := (Q6nq.gwt_def (@Q7mx.Mq2.tokfree_loop_pc) (@UhHQ.tokfree_loop_pc) (Q6nq.gwt_def (@QAyu.Mq6.tokfree_loop_pc) (@UhHQ.tokfree_loop_pc) (Q6nq.gwt_def (@Q7mx.Mq2.tf_frame) (@UhHQ.tf_frame) (Q6nq.gwt_def (@QAyu.Mq6.tf_frame) (@UhHQ.tf_frame) (Q6nq.gwt_def (@Q7mx.Mq2.put_stk_P) (@UPZI.Mq4.put_stk_P) (Q6nq.gwt_def (@Q7mx.Mq2.lvblocks) (@UhHQ.lvblocks) (Q6nq.gwt_def (@QAyu.Mq6.lvblocks) (@UhHQ.lvblocks) (Q6nq.gwt_pat GwI.pS4L (@UC8c.Mq0.S4L) (Q6nq.gwt_pat GwI.pS4F UC8c.Mq0.S4F Q6nq.gwt_nil))))))))).
#[using="Type"] Lemma lvl_ok_agree : ltac2:(Q6nq.ty2 'GwI.segs '(@Q7mx.Mq2.lvl_ok_agree) [] '(@nil Z) 'gwt_X).
Proof. first [GwApply2.gw_by_name2 GwI.segs (@Q7mx.Mq2.lvl_ok_agree) | autorewrite with gw_eqs; GwApply2.gw_by_name2 GwI.segs (@Q7mx.Mq2.lvl_ok_agree)]. Qed.

#[using="Type"] Lemma lvblocks_incl : ltac2:(Q6nq.ty2 'GwI.segs '(@Q7mx.Mq2.lvblocks_incl) [] '(@nil Z) 'gwt_X).
Proof. first [GwApply2.gw_by_name2 GwI.segs (@Q7mx.Mq2.lvblocks_incl) | autorewrite with gw_eqs; GwApply2.gw_by_name2 GwI.segs (@Q7mx.Mq2.lvblocks_incl)]. Qed.

Section TokFree2.
Variable HIx : heap_iface S4L.
Notation HEAPx := (HEAP S4L HIx).
Hypothesis PUT : put_stmt_P HIx.

Definition tf_loop_post (x2 gp tp s0 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
(md : Model) (BASE LB0 PBS : list blk) (SP : Z) (me mpre : word -> option byte) (lo : Z) (errv : word)
(q r pb depth : Z) (x : tscal) (levels : list tlevel) (i : nat) (junk : list byte) (s3v s2v s1v s0v rav : word)
(ms' : machine_state) (md' : Model) : Prop :=
exists m' (A' : AS S4L HIx) F' fc' levels' x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 s1',
ms' = MS (mkR x1 x2 gp tp t0 t1 t2 s0 s1' a0 a1 a2 a3 a4 a5 a6 a7
s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F' (Z_to_bv 64 0x21bf0) fc' None m' (seg_rom rsegs) /\
fsaved F F' /\ (frm0 fc -> frm0 fc') /\
model_vm_only md md' /\
HEAPx A' BASE m' md' /\
length levels' = 32%nat /\
(forall j, (j <= i)%nat -> nth_error levels' j = Some lvl_reset) /\
(forall j, (i < j)%nat -> nth_error levels' j = nth_error levels j) /\
tstack rsegs m' q levels' /\
rw_cells rsegs m' r (tok_cells pb depth q x) /\
tf_frame m' SP junk s3v s2v s1v s0v rav /\
stk rsegs m' lo (SP - 48) /\
heap_pres S4L LB0 SP me m' /\
rw_cells rsegs m' (0x77c00 - 164) [C4 errv] /\
agree_on rsegs PBS mpre m'.


#[using="Type"] Lemma Permutation_concat : forall {A} (L L' : list (list A)), Permutation L L' -> Permutation (concat L) (concat L').
Proof. first [GwApply2.gw_by_name2 GwI.segs (@Q7mx.Mq2.Permutation_concat) | autorewrite with gw_eqs; GwApply2.gw_by_name2 GwI.segs (@Q7mx.Mq2.Permutation_concat)]. Qed.

#[using="Type"] Lemma lvblocks_all : ltac2:(Q6nq.ty2 'GwI.segs '(@Q7mx.Mq2.lvblocks_all) [] '(@nil Z) '(Q6nq.gwt_def (@Q7mx.Mq2.tf_loop_post) (@tf_loop_post) gwt_X)).
Proof. first [GwApply2.gw_by_name2 GwI.segs (@Q7mx.Mq2.lvblocks_all) | autorewrite with gw_eqs; GwApply2.gw_by_name2 GwI.segs (@Q7mx.Mq2.lvblocks_all)]. Qed.

#[using="Type"] Lemma lvblocks_trunc : ltac2:(Q6nq.ty2 'GwI.segs '(@Q7mx.Mq2.lvblocks_trunc) [] '(@nil Z) '(Q6nq.gwt_def (@Q7mx.Mq2.tf_loop_post) (@tf_loop_post) gwt_X)).
Proof. first [GwApply2.gw_by_name2 GwI.segs (@Q7mx.Mq2.lvblocks_trunc) | autorewrite with gw_eqs; GwApply2.gw_by_name2 GwI.segs (@Q7mx.Mq2.lvblocks_trunc)]. Qed.

Definition json_tokener_free_entry2 : Z := 0x216b0.

Definition tokfree_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
(m : word -> option byte) (md : Model) (LB : list blk) (lo : Z) (errv : word)
(ms' : machine_state) (md' : Model) : Prop :=
exists m' (A' : AS S4L HIx) (rv : word),
ret_statew S4L ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc rv m' ms' /\
model_vm_only md md' /\
stk rsegs m' lo (bv_unsigned sp) /\
heap_pres S4L LB (bv_unsigned sp) m m' /\
rw_cells rsegs m' (0x77c00 - 164) [C4 errv] /\
HEAPx A' LB m' md'.

End TokFree2.

End RC__1.
