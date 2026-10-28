(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)


From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib Require CodeAt StepGen GwInst GwApply GwApply2. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Q6nq.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Q0Hd.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QAyu.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UC8c.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QCcH.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Q0Ek.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UlCE.

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
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UlCE.Mq1.
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
Definition lb_remove_zero := @UlCE.Mq1.lb_remove_zero.
Definition pS4L := Eval cbv beta delta [Q0Hd.gl segs e_malloc e_free e_calloc e_realloc e_malloc2 e_free2 gTP gGOTG gGUARD gAUXV gLIBC gVOL gCS gHEXGOT gHEXPTR gHEXCHARS gIMG_LO gIMG_HI] in
(fun RC__ : gw_RC => @Q0Hd.gl RC__ segs e_malloc e_free e_calloc e_realloc e_malloc2 e_free2 gTP gGOTG gGUARD gAUXV gLIBC gVOL gCS gHEXGOT gHEXPTR gHEXCHARS gIMG_LO gIMG_HI (gH1 RC__) (gH2 RC__) (gH3 RC__) (gH4 RC__) (gH5 RC__)).
Definition pS4F := Eval cbv beta delta [Q0Hd.gf e_fn_obj_to_json_string e_fn_arr_to_json_string e_fn_bool_to_json_string e_fn_dbl_to_json_string e_fn_int_to_json_string e_fn_str_to_json_string e_fn_ud_to_json_string e_fn_free_userdata e_fn_lh_entry_free e_fn_lh_char_hash e_fn_lh_char_equal e_fn_arr_entry_free] in
(Q0Hd.gf e_fn_obj_to_json_string e_fn_arr_to_json_string e_fn_bool_to_json_string e_fn_dbl_to_json_string e_fn_int_to_json_string e_fn_str_to_json_string e_fn_ud_to_json_string e_fn_free_userdata e_fn_lh_entry_free e_fn_lh_char_hash e_fn_lh_char_equal e_fn_arr_entry_free).
End GwI.

Section RC__1. Context {RC__ : Q6q3.RunConsts}.

Definition lvblocks (levels : list tlevel) (i : nat) : list blk :=
concat (map lvl_blocks (rev (firstn i levels))).

#[using="Type"] Lemma firstn_S_nth : forall {A} (l : list A) i x, nth_error l i = Some x -> firstn (S i) l = firstn i l ++ [x].
Proof. first [GwApply2.gw_by_name2 GwI.segs (@QAyu.Mq6.firstn_S_nth) | autorewrite with gw_eqs; GwApply2.gw_by_name2 GwI.segs (@QAyu.Mq6.firstn_S_nth)]. Qed.

Local Definition gwt_X : unit := (Q6nq.gwt_def (@QAyu.Mq6.put_stk_P) (@UPZI.Mq4.put_stk_P) (Q6nq.gwt_pat GwI.pS4L (@UC8c.Mq0.S4L) (Q6nq.gwt_pat GwI.pS4F UC8c.Mq0.S4F Q6nq.gwt_nil))).
#[using="Type"] Lemma lvblocks_S : ltac2:(Q6nq.ty2 'GwI.segs '(@QAyu.Mq6.lvblocks_S) [] '(@nil Z) '(Q6nq.gwt_def (@QAyu.Mq6.lvblocks) (@lvblocks) gwt_X)).
Proof. first [GwApply2.gw_by_name2 GwI.segs (@QAyu.Mq6.lvblocks_S) | autorewrite with gw_eqs; GwApply2.gw_by_name2 GwI.segs (@QAyu.Mq6.lvblocks_S)]. Qed.

#[using="Type"] Lemma lvblocks_0 : forall levels, lvblocks levels 0 = [].
Proof. first [GwApply2.gw_by_name2 GwI.segs (@QAyu.Mq6.lvblocks_0) | autorewrite with gw_eqs; GwApply2.gw_by_name2 GwI.segs (@QAyu.Mq6.lvblocks_0)]. Qed.

#[using="Type"] Lemma lvblocks_clean : ltac2:(Q6nq.ty2 'GwI.segs '(@QAyu.Mq6.lvblocks_clean) [] '(@nil Z) '(Q6nq.gwt_def (@QAyu.Mq6.lvblocks) (@lvblocks) gwt_X)).
Proof. first [GwApply2.gw_by_name2 GwI.segs (@QAyu.Mq6.lvblocks_clean) | autorewrite with gw_eqs; GwApply2.gw_by_name2 GwI.segs (@QAyu.Mq6.lvblocks_clean)]. Qed.

#[using="Type"] Lemma tstack_pres : ltac2:(Q6nq.ty2 'GwI.segs '(@QAyu.Mq6.tstack_pres) [] '([1024]%Z : list Z) '(Q6nq.gwt_def (@QAyu.Mq6.lvblocks) (@lvblocks) gwt_X)).
Proof. first [GwApply2.gw_by_name2 GwI.segs (@QAyu.Mq6.tstack_pres) | autorewrite with gw_eqs; GwApply2.gw_by_name2 GwI.segs (@QAyu.Mq6.tstack_pres)]. Qed.

Definition srec_cells8 (stss : list byte) (cur name : Z) : list cell :=
[CB 8 stss; C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 cur); C8 (Z_to_bv 64 name)].

#[using="Type"] Lemma srec_to8 : ltac2:(Q6nq.ty2 'GwI.segs '(@QAyu.Mq6.srec_to8) [] '(@nil Z) '(Q6nq.gwt_def (@QAyu.Mq6.srec_cells8) (@srec_cells8) (Q6nq.gwt_def (@QAyu.Mq6.lvblocks) (@lvblocks) gwt_X))).
Proof. first [GwApply2.gw_by_name2 GwI.segs (@QAyu.Mq6.srec_to8) | autorewrite with gw_eqs; GwApply2.gw_by_name2 GwI.segs (@QAyu.Mq6.srec_to8)]. Qed.

#[using="Type"] Lemma srec_reset_of8 : ltac2:(Q6nq.ty2 'GwI.segs '(@QAyu.Mq6.srec_reset_of8) [] '([4294967296]%Z : list Z) '(Q6nq.gwt_def (@QAyu.Mq6.srec_cells8) (@srec_cells8) (Q6nq.gwt_def (@QAyu.Mq6.lvblocks) (@lvblocks) gwt_X))).
Proof. first [GwApply2.gw_by_name2 GwI.segs (@QAyu.Mq6.srec_reset_of8) | autorewrite with gw_eqs; GwApply2.gw_by_name2 GwI.segs (@QAyu.Mq6.srec_reset_of8)]. Qed.

#[using="Type"] Lemma lupd_lupd : forall {A} (l : list A) i (x y : A), lupd (lupd l i x) i y = lupd l i y.
Proof. first [GwApply2.gw_by_name2 GwI.segs (@QAyu.Mq6.lupd_lupd) | autorewrite with gw_eqs; GwApply2.gw_by_name2 GwI.segs (@QAyu.Mq6.lupd_lupd)]. Qed.

#[using="Type"] Lemma lvl_blocks_TL : forall st ss cur cs cbs name nbs, lvl_blocks (TL st ss cur cs cbs name nbs) = cbs ++ nbs.
Proof. first [GwApply2.gw_by_name2 GwI.segs (@QAyu.Mq6.lvl_blocks_TL) | autorewrite with gw_eqs; GwApply2.gw_by_name2 GwI.segs (@QAyu.Mq6.lvl_blocks_TL)]. Qed.

#[using="Type"] Lemma nodup_mid_notin : ltac2:(Q6nq.ty2 'GwI.segs '(@QAyu.Mq6.nodup_mid_notin) [] '(@nil Z) '(Q6nq.gwt_def (@QAyu.Mq6.srec_cells8) (@srec_cells8) (Q6nq.gwt_def (@QAyu.Mq6.lvblocks) (@lvblocks) gwt_X))).
Proof. first [GwApply2.gw_by_name2 GwI.segs (@QAyu.Mq6.nodup_mid_notin) | autorewrite with gw_eqs; GwApply2.gw_by_name2 GwI.segs (@QAyu.Mq6.nodup_mid_notin)]. Qed.

#[using="Type"] Lemma nodup_mid_notin_r : ltac2:(Q6nq.ty2 'GwI.segs '(@QAyu.Mq6.nodup_mid_notin_r) [] '(@nil Z) '(Q6nq.gwt_def (@QAyu.Mq6.srec_cells8) (@srec_cells8) (Q6nq.gwt_def (@QAyu.Mq6.lvblocks) (@lvblocks) gwt_X))).
Proof. first [GwApply2.gw_by_name2 GwI.segs (@QAyu.Mq6.nodup_mid_notin_r) | autorewrite with gw_eqs; GwApply2.gw_by_name2 GwI.segs (@QAyu.Mq6.nodup_mid_notin_r)]. Qed.

#[using="Type"] Lemma nodup_P_notq : ltac2:(Q6nq.ty2 'GwI.segs '(@QAyu.Mq6.nodup_P_notq) [] '(@nil Z) '(Q6nq.gwt_def (@QAyu.Mq6.srec_cells8) (@srec_cells8) (Q6nq.gwt_def (@QAyu.Mq6.lvblocks) (@lvblocks) gwt_X))).
Proof. first [GwApply2.gw_by_name2 GwI.segs (@QAyu.Mq6.nodup_P_notq) | autorewrite with gw_eqs; GwApply2.gw_by_name2 GwI.segs (@QAyu.Mq6.nodup_P_notq)]. Qed.

Section TokFree.
Variable HIx : heap_iface S4L.
Notation HEAPx := (HEAP S4L HIx).
Hypothesis PUT : put_stmt_P HIx.

Definition json_tokener_free_entry : Z := 0x216b0.
Definition tokfree_loop_pc : Z := 0x216f0.

Definition tf_frame (m : word -> option byte) (sp : Z) (junk : list byte) (s3v s2v s1v s0v rav : word) : Prop :=
rw_cells rsegs m (sp - 48) [CB 8 junk; C8 s3v; C8 s2v; C8 s1v; C8 s0v; C8 rav].

Definition tf_body_post (x2 gp tp s0 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 a0v : word) (F : bvmap 5 word) (fc : bv 32)
(md : Model) (REST LB0 P : list blk) (SP : Z) (me mpre : word -> option byte) (lo : Z) (errv : word)
(q r pb depth : Z) (x : tscal) (levels : list tlevel) (i : nat) (junk : list byte) (s3v s2v s1v s0v rav : word)
(ms' : machine_state) (md' : Model) : Prop :=
exists m' (A' : AS S4L HIx) F' fc' x1 t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6,
ms' = MS (mkR x1 x2 gp tp t0 t1 t2 s0 (Z_to_bv 64 (32 * Z.of_nat i + 16 - 32)) a0v a1 a2 a3 a4 a5 a6 a7
s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F' (Z_to_bv 64 0x21bec) fc' None m' (seg_rom rsegs) /\
fsaved F F' /\ (frm0 fc -> frm0 fc') /\
model_vm_only md md' /\
HEAPx A' REST m' md' /\
tstack rsegs m' q (lupd levels i lvl_reset) /\
rw_cells rsegs m' r (tok_cells pb depth q x) /\
tf_frame m' SP junk s3v s2v s1v s0v rav /\
stk rsegs m' lo (SP - 48) /\
heap_pres S4L LB0 SP me m' /\
rw_cells rsegs m' (0x77c00 - 164) [C4 errv] /\
agree_on rsegs P mpre m'.

End TokFree.

End RC__1.
