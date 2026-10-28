(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)


From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib Require CodeAt StepGen GwInst GwApply GwApply2. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Q6nq.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Q0Hd.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require U9Mh. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QRGY QT7b.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UC8c.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QCcH.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Q0Ek.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UXZq.

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QXup.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QXup. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Q5Rg.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q5Rg.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UEQM.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UEQM.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QCcH.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QCcH. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Q0Ek.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q0Ek.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UC8c.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UC8c.Mq0.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Qsw7.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qsw7. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QJjn.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QJjn. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QRUw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QRUw. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Q8tj.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q8tj.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QgoP.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QgoP.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UxXo.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UxXo.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QSL3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QSL3.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UXZq.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UXZq.
Import ListNotations. Unset Keyed Unification. Local Ltac Qfw3.Mq3.model_reg_tac n X mexpr ::= Qfw3.Mq3.mkr__model_reg_tac_1 n X mexpr.
Open Scope Z_scope.

Module GwI.
Definition segs := rsegs.
Definition base := 0x287fc%Z.
Definition e_blk_18a54 := 0x28b80%Z.
Lemma CODE : CodeAt.code_at rsegs 0x287fc U9Mh.Mq3.lhlookup_code.  Proof. StepGen.code_at_vm. Qed.
Lemma BASE4 : (0x287fc mod 4 = 0)%Z.  Proof. reflexivity. Qed.
Lemma BASER : (0 <= 0x287fc /\ 0x287fc + 316 <= 2^40)%Z.  Proof. vm_compute. split; discriminate. Qed.

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
Definition lh_char_equal_spec := @UXZq.lh_char_equal_spec.
Definition ent_addr_mod8 := @QT7b.ent_addr_mod8.
Definition pS4L := Eval cbv beta delta [Q0Hd.gl segs e_malloc e_free e_calloc e_realloc e_malloc2 e_free2 gTP gGOTG gGUARD gAUXV gLIBC gVOL gCS gHEXGOT gHEXPTR gHEXCHARS gIMG_LO gIMG_HI] in
(fun RC__ : gw_RC => @Q0Hd.gl RC__ segs e_malloc e_free e_calloc e_realloc e_malloc2 e_free2 gTP gGOTG gGUARD gAUXV gLIBC gVOL gCS gHEXGOT gHEXPTR gHEXCHARS gIMG_LO gIMG_HI (gH1 RC__) (gH2 RC__) (gH3 RC__) (gH4 RC__) (gH5 RC__)).
Definition pS4F := Eval cbv beta delta [Q0Hd.gf e_fn_obj_to_json_string e_fn_arr_to_json_string e_fn_bool_to_json_string e_fn_dbl_to_json_string e_fn_int_to_json_string e_fn_str_to_json_string e_fn_ud_to_json_string e_fn_free_userdata e_fn_lh_entry_free e_fn_lh_char_hash e_fn_lh_char_equal e_fn_arr_entry_free] in
(Q0Hd.gf e_fn_obj_to_json_string e_fn_arr_to_json_string e_fn_bool_to_json_string e_fn_dbl_to_json_string e_fn_int_to_json_string e_fn_str_to_json_string e_fn_ud_to_json_string e_fn_free_userdata e_fn_lh_entry_free e_fn_lh_char_hash e_fn_lh_char_equal e_fn_arr_entry_free).
End GwI.

Definition lh_lookup_entry := 0x287fc.

Definition next_ix (size n : Z) : Z := if n + 1 =? size then 0 else n + 1.

Lemma land_ones64_l : forall x, 0 <= x < 2^64 -> Z.land 18446744073709551615 x = x.
Proof. first [GwInst.gw_exact (@U9Mh.Mq3.land_ones64_l) | autorewrite with gw_eqs; GwInst.gw_exact (@U9Mh.Mq3.land_ones64_l)]. Qed.

Local Definition gwt_X : unit := (Q6nq.gwt_def (@QRGY.Mq0.u_lh_char_equal_post) (@UXZq.lh_char_equal_post) (Q6nq.gwt_def (@U9Mh.Mq3.lh_char_equal_post) (@UXZq.lh_char_equal_post) (Q6nq.gwt_def (@U9Mh.Mq3.next_ix) (@next_ix) (Q6nq.gwt_pat GwI.pS4L (@UC8c.Mq0.S4L) (Q6nq.gwt_pat GwI.pS4F UC8c.Mq0.S4F Q6nq.gwt_nil))))).
Lemma remu_lit : ltac2:(Q6nq.tyx '(@U9Mh.Mq3.remu_lit) [] '(@nil Z) '(Q6nq.gwt_def (@U9Mh.Mq3.lh_lookup_entry) (@lh_lookup_entry) gwt_X)).
Proof. first [GwInst.gw_exact (@U9Mh.Mq3.remu_lit) | autorewrite with gw_eqs; GwInst.gw_exact (@U9Mh.Mq3.remu_lit)]. Qed.
Lemma mul40_chk : ltac2:(Q6nq.tyx '(@U9Mh.Mq3.mul40_chk) [] '(@nil Z) '(Q6nq.gwt_def (@U9Mh.Mq3.lh_lookup_entry) (@lh_lookup_entry) gwt_X)).
Proof. first [GwInst.gw_exact (@U9Mh.Mq3.mul40_chk) | autorewrite with gw_eqs; GwInst.gw_exact (@U9Mh.Mq3.mul40_chk)]. Qed.

Section LhLookup.
Variables (ra sp gp tp : word) (s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32).
Variables (t tbl size kp lo : Z) (es : list lent) (svs : list slotv) (ps : list byte).

Definition lookup_res (r : Z) : Prop :=
r = 0 \/ exists j e, nth_error es j = Some e /\ r = ent_addr tbl (le_ix e) /\ le_ks e = ps.

Definition lh_lookup_post (m : word -> option byte) : machine_state -> Prop :=
fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 (r : Z) m',
ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 r) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc ra) fc None m' (seg_rom rsegs)
/\ munch [(bv_unsigned sp - 96, bv_unsigned sp)] m m' /\ wmono rsegs m m' /\ mem_inv rsegs m'
/\ stk rsegs m' lo (bv_unsigned sp)
/\ lh_open rsegs S4F m' t tbl size es svs
/\ bytes_at rsegs m' kp (ps ++ [b0])
/\ lookup_res r.

Definition lk_frame (m : word -> option byte) (junk8 : list byte) : Prop :=
rw_cells rsegs m (bv_unsigned sp + -80) [CB 8 junk8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].


#[using="Type"] Lemma lh_lookup_next : ltac2:(Q6nq.ty2 'GwI.segs '(@U9Mh.Mq3.lh_lookup_next) [] '([(-80); 165984; 166016; 166148]%Z : list Z) '(Q6nq.gwt_def (@U9Mh.Mq3.lk_frame) (@lk_frame) (Q6nq.gwt_def (@U9Mh.Mq3.lh_lookup_post) (@lh_lookup_post) (Q6nq.gwt_def (@U9Mh.Mq3.lookup_res) (@lookup_res) (Q6nq.gwt_def (@U9Mh.Mq3.lh_lookup_entry) (@lh_lookup_entry) gwt_X))))).
Proof. first [GwApply2.gw_by_name2 GwI.segs (@U9Mh.Mq3.lh_lookup_next) | autorewrite with gw_eqs; GwApply2.gw_by_name2 GwI.segs (@U9Mh.Mq3.lh_lookup_next)]. Qed.

#[using="Type"] Lemma lh_lookup_exit0 : ltac2:(Q6nq.ty2 'GwI.segs '(@U9Mh.Mq3.lh_lookup_exit0) [] '([(-96); (-80); 166148]%Z : list Z) '(Q6nq.gwt_def (@U9Mh.Mq3.lk_frame) (@lk_frame) (Q6nq.gwt_def (@U9Mh.Mq3.lh_lookup_post) (@lh_lookup_post) (Q6nq.gwt_def (@U9Mh.Mq3.lookup_res) (@lookup_res) (Q6nq.gwt_def (@U9Mh.Mq3.lh_lookup_entry) (@lh_lookup_entry) gwt_X))))).
Proof. first [GwApply2.gw_by_name2 GwI.segs (@U9Mh.Mq3.lh_lookup_exit0) | autorewrite with gw_eqs; GwApply2.gw_by_name2 GwI.segs (@U9Mh.Mq3.lh_lookup_exit0)]. Qed.

#[using="Type"] Lemma lh_lookup_exit1 : ltac2:(Q6nq.ty2 'GwI.segs '(@U9Mh.Mq3.lh_lookup_exit1) [] '([(-96); (-80); 166104]%Z : list Z) '(Q6nq.gwt_def (@U9Mh.Mq3.lk_frame) (@lk_frame) (Q6nq.gwt_def (@U9Mh.Mq3.lh_lookup_post) (@lh_lookup_post) (Q6nq.gwt_def (@U9Mh.Mq3.lookup_res) (@lookup_res) (Q6nq.gwt_def (@U9Mh.Mq3.lh_lookup_entry) (@lh_lookup_entry) gwt_X))))).
Proof. first [GwApply2.gw_by_name2 GwI.segs (@U9Mh.Mq3.lh_lookup_exit1) | autorewrite with gw_eqs; GwApply2.gw_by_name2 GwI.segs (@U9Mh.Mq3.lh_lookup_exit1)]. Qed.

#[using="Type"] Lemma lh_lookup_loop : ltac2:(Q6nq.ty2 'GwI.segs '(@U9Mh.Mq3.lh_lookup_loop) [] '([(-96); (-80); 166016]%Z : list Z) '(Q6nq.gwt_def (@U9Mh.Mq3.lk_frame) (@lk_frame) (Q6nq.gwt_def (@U9Mh.Mq3.lh_lookup_post) (@lh_lookup_post) (Q6nq.gwt_def (@U9Mh.Mq3.lookup_res) (@lookup_res) (Q6nq.gwt_def (@U9Mh.Mq3.lh_lookup_entry) (@lh_lookup_entry) gwt_X))))).
Proof. first [GwApply2.gw_by_name2 GwI.segs (@U9Mh.Mq3.lh_lookup_loop) | autorewrite with gw_eqs; GwApply2.gw_by_name2 GwI.segs (@U9Mh.Mq3.lh_lookup_loop)]. Qed.

#[using="Type"] Lemma lh_lookup_spec : ltac2:(Q6nq.ty2 'GwI.segs '(@U9Mh.Mq3.lh_lookup_spec) [] '([(-96)]%Z : list Z) '(Q6nq.gwt_zc lh_lookup_entry (Q6nq.gwt_def (@U9Mh.Mq3.lk_frame) (@lk_frame) (Q6nq.gwt_def (@U9Mh.Mq3.lh_lookup_post) (@lh_lookup_post) (Q6nq.gwt_def (@U9Mh.Mq3.lookup_res) (@lookup_res) (Q6nq.gwt_def (@U9Mh.Mq3.lh_lookup_entry) (@lh_lookup_entry) gwt_X)))))).
Proof. first [GwApply2.gw_by_name2 GwI.segs (@U9Mh.Mq3.lh_lookup_spec) | autorewrite with gw_eqs; GwApply2.gw_by_name2 GwI.segs (@U9Mh.Mq3.lh_lookup_spec)]. Qed.
End LhLookup.
