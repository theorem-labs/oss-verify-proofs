(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)


From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib Require CodeAt StepGen GwInst GwApply GwApply2. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Q6nq.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Q0Hd.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QXOI.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UC8c.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QCcH.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Q0Ek.

From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QXup.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QXup. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Q5Rg.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q5Rg.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UEQM.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UEQM.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QRjH.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QRjH.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QHnV.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QHnV. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QCcH.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QCcH. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QfLs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QfLs. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Q0Ek.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q0Ek.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UC8c.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UC8c.Mq0.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Qsw7.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qsw7. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QJjn.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QJjn. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Q8tj.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q8tj.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QSL3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QSL3.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QRUw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QRUw. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QnCn.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QnCn.
Import ListNotations. Unset Keyed Unification. Local Ltac Qfw3.Mq3.model_reg_tac n X mexpr ::= Qfw3.Mq3.mkr__model_reg_tac_1 n X mexpr.
Open Scope Z_scope.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Q6q3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q6q3.

Module GwI.
Definition segs := rsegs.
Definition base := 0x2878c%Z.
Definition w_21 := 0x0d5290ef%Z.
Definition w_27 := 0x0bd2906f%Z.
Definition joff_21 := (Z_to_bv 21 170196).
Definition joff_27 := (Z_to_bv 21 170172).
Definition e_16ed0 := 0x24654%Z.
Lemma CODE : CodeAt.code_at rsegs 0x2878c (QXOI.ulhfree_code 0x0d5290ef%Z 0x0bd2906f%Z).  Proof. StepGen.code_at_vm. Qed.
Lemma BASE4 : (0x2878c mod 4 = 0)%Z.  Proof. reflexivity. Qed.
Lemma BASER : (0 <= 0x2878c /\ 0x2878c + 112 <= 2^40)%Z.  Proof. vm_compute. split; discriminate. Qed.

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
Definition wb17dac_14 := 0x9acff06f%Z.
Definition wb17dac_16 := 0x4052c0ef%Z.
Definition joffb17dac_14 := (Z_to_bv 21 2093484).
Definition joffb17dac_16 := (Z_to_bv 21 183300).
Lemma CODE_e_fn_lh_entry_free : CodeAt.code_at rsegs e_fn_lh_entry_free (QXOI.blk_17dac_code 0x9acff06f%Z 0x4052c0ef%Z).  Proof. StepGen.code_at_vm. Qed.
Definition pS4L := Eval cbv beta delta [Q0Hd.gl segs e_malloc e_free e_calloc e_realloc e_malloc2 e_free2 gTP gGOTG gGUARD gAUXV gLIBC gVOL gCS gHEXGOT gHEXPTR gHEXCHARS gIMG_LO gIMG_HI] in
(fun RC__ : gw_RC => @Q0Hd.gl RC__ segs e_malloc e_free e_calloc e_realloc e_malloc2 e_free2 gTP gGOTG gGUARD gAUXV gLIBC gVOL gCS gHEXGOT gHEXPTR gHEXCHARS gIMG_LO gIMG_HI (gH1 RC__) (gH2 RC__) (gH3 RC__) (gH4 RC__) (gH5 RC__)).
Definition pS4F := Eval cbv beta delta [Q0Hd.gf e_fn_obj_to_json_string e_fn_arr_to_json_string e_fn_bool_to_json_string e_fn_dbl_to_json_string e_fn_int_to_json_string e_fn_str_to_json_string e_fn_ud_to_json_string e_fn_free_userdata e_fn_lh_entry_free e_fn_lh_char_hash e_fn_lh_char_equal e_fn_arr_entry_free] in
(Q0Hd.gf e_fn_obj_to_json_string e_fn_arr_to_json_string e_fn_bool_to_json_string e_fn_dbl_to_json_string e_fn_int_to_json_string e_fn_str_to_json_string e_fn_ud_to_json_string e_fn_free_userdata e_fn_lh_entry_free e_fn_lh_char_hash e_fn_lh_char_equal e_fn_arr_entry_free).
End GwI.

Section RC__1. Context {RC__ : Q6q3.RunConsts}.

#[using="Type"] Lemma ent_addr_mod8 : forall tbl i, tbl mod 16 = 0 -> (tbl + 40 * Z.of_nat i) mod 8 = 0.
Proof. first [GwApply2.gw_by_name2 GwI.segs (@QXOI.ent_addr_mod8) | autorewrite with gw_eqs; GwApply2.gw_by_name2 GwI.segs (@QXOI.ent_addr_mod8)]. Qed.

Section LhFree.
Variable HIx : heap_iface S4L.
Notation HEAPx := (HEAP S4L HIx).

Definition lh_entry_free_entry : Z := 0x25470.
Definition lh_table_free_entry : Z := 0x2878c.

Definition lh_entry_free_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
(m : word -> option byte) (md : Model) (LB : list blk) (lo : Z) (errv : word)
(ms' : machine_state) (md' : Model) : Prop :=
exists m' (A' : AS S4L HIx) (r : word),
ret_state S4L ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc r m' ms' /\
model_vm_only md md' /\
stk rsegs m' lo (bv_unsigned sp) /\
heap_pres S4L LB (bv_unsigned sp) m m' /\
rw_cells rsegs m' (0x77c00 - 164) [C4 errv] /\
HEAPx A' LB m' md'.

Local Definition gwt_X : unit := (Q6nq.gwt_pat GwI.pS4L (@UC8c.Mq0.S4L) (Q6nq.gwt_pat GwI.pS4F UC8c.Mq0.S4F Q6nq.gwt_nil)).
#[using="Type"] Lemma lh_entry_free_cps : ltac2:(Q6nq.ty2 'GwI.segs '(@QXOI.u_lh_entry_free_cps) [] '([(-8256); (-164); 65536; 490496; 626688]%Z : list Z) '(Q6nq.gwt_zc lh_entry_free_entry (Q6nq.gwt_def (@QXOI.u_lh_entry_free_post) (@lh_entry_free_post) (Q6nq.gwt_def (@QXOI.u_lh_table_free_entry) (@lh_table_free_entry) (Q6nq.gwt_def (@QXOI.u_lh_entry_free_entry) (@lh_entry_free_entry) gwt_X))))).
Proof. first [GwApply2.gw_by_name2 GwI.segs (@QXOI.u_lh_entry_free_cps) | autorewrite with gw_eqs; GwApply2.gw_by_name2 GwI.segs (@QXOI.u_lh_entry_free_cps)]. Qed.

Variables (sp gp : word) (s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32).
Variables (m0 : word -> option byte) (md0 : Model) (LB : list blk) (lo t tbl size : Z) (es : list lent) (svs : list slotv) (T : TSet).
Variables (s0c s1c rac : word).

Definition free_frame (m : word -> option byte) (junk8 : list byte) : Prop :=
rw_cells rsegs m (bv_unsigned sp + -32) [CB 8 junk8; C8 s1c; C8 s0c; C8 rac].

Definition free_exit (errv : word) (K0 : machine_state -> Model -> Prop) : Prop :=
forall (x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m : word -> option byte) (md : Model) (A : AS S4L HIx) (junk8 : list byte)
(hsz hcnt hhd htl : Z),
HEAPx A ((t, 56) :: (tbl, 40 * size) :: LB) m md ->
rw_cells rsegs m t [C4 (Z_to_bv 64 hsz); C4 (Z_to_bv 64 hcnt); C8 (Z_to_bv 64 hhd); C8 (Z_to_bv 64 htl); C8 (Z_to_bv 64 tbl);
C8 (Z_to_bv 64 (fn_lh_entry_free S4F)); C8 (Z_to_bv 64 (fn_lh_char_hash S4F)); C8 (Z_to_bv 64 (fn_lh_char_equal S4F))] ->
stk rsegs m lo (bv_unsigned sp + -32) ->
free_frame m junk8 ->
rw_cells rsegs m (0x77c00 - 164) [C4 errv] ->
model_vm_only md0 md -> heap_pres S4L LB (bv_unsigned sp) m0 m ->
K0 (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -32)) gp (Z_to_bv 64 0x77c00) t0 t1 t2 (Z_to_bv 64 t) (Z_to_bv 64 0) a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0x287dc) fc None m (seg_rom rsegs)) md.

#[using="Type"] Lemma ent_addr_pos : forall i, 0 < tbl -> 0 < ent_addr tbl i.
Proof. first [GwApply2.gw_by_name2 GwI.segs (@QXOI.u_ent_addr_pos) | autorewrite with gw_eqs; GwApply2.gw_by_name2 GwI.segs (@QXOI.u_ent_addr_pos)]. Qed.

#[using="Type"] Lemma lh_free_loop : ltac2:(Q6nq.ty2 'GwI.segs '(@QXOI.u_lh_free_loop) [] '([(-8256); (-164); 165820; 490496]%Z : list Z) '(Q6nq.gwt_def (@QXOI.u_free_exit) (@free_exit) (Q6nq.gwt_def (@QXOI.u_free_frame) (@free_frame) (Q6nq.gwt_def (@QXOI.u_lh_entry_free_post) (@lh_entry_free_post) (Q6nq.gwt_def (@QXOI.u_lh_table_free_entry) (@lh_table_free_entry) (Q6nq.gwt_def (@QXOI.u_lh_entry_free_entry) (@lh_entry_free_entry) gwt_X)))))).
Proof. first [GwApply2.gw_by_name2 GwI.segs (@QXOI.u_lh_free_loop) | autorewrite with gw_eqs; GwApply2.gw_by_name2 GwI.segs (@QXOI.u_lh_free_loop)]. Qed.

Definition lh_table_free_post (errv : word) (ms' : machine_state) (md' : Model) : Prop :=
exists m' (A' : AS S4L HIx) (r : word),
ret_statew S4L rac sp gp (Z_to_bv 64 0x77c00) s0c s1c s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc r m' ms' /\
model_vm_only md0 md' /\
stk rsegs m' lo (bv_unsigned sp) /\
heap_pres S4L LB (bv_unsigned sp) m0 m' /\
rw_cells rsegs m' (0x77c00 - 164) [C4 errv] /\
HEAPx A' LB m' md'.

#[using="Type"] Lemma lh_free_exit_ok : ltac2:(Q6nq.ty2 'GwI.segs '(@QXOI.u_lh_u_free_exit_ok) [] '([(-8256)]%Z : list Z) '(Q6nq.gwt_def (@QXOI.u_lh_table_free_post) (@lh_table_free_post) (Q6nq.gwt_def (@QXOI.u_free_exit) (@free_exit) (Q6nq.gwt_def (@QXOI.u_free_frame) (@free_frame) (Q6nq.gwt_def (@QXOI.u_lh_entry_free_post) (@lh_entry_free_post) (Q6nq.gwt_def (@QXOI.u_lh_table_free_entry) (@lh_table_free_entry) (Q6nq.gwt_def (@QXOI.u_lh_entry_free_entry) (@lh_entry_free_entry) gwt_X))))))).
Proof. first [GwApply2.gw_by_name2 GwI.segs (@QXOI.u_lh_u_free_exit_ok) | autorewrite with gw_eqs; GwApply2.gw_by_name2 GwI.segs (@QXOI.u_lh_u_free_exit_ok)]. Qed.

#[using="Type"] Lemma lh_table_free_cps : ltac2:(Q6nq.ty2 'GwI.segs '(@QXOI.u_lh_table_free_cps) [] '([(-8256); (-164); 490496]%Z : list Z) '(Q6nq.gwt_zc lh_table_free_entry (Q6nq.gwt_def (@QXOI.u_lh_table_free_post) (@lh_table_free_post) (Q6nq.gwt_def (@QXOI.u_free_exit) (@free_exit) (Q6nq.gwt_def (@QXOI.u_free_frame) (@free_frame) (Q6nq.gwt_def (@QXOI.u_lh_entry_free_post) (@lh_entry_free_post) (Q6nq.gwt_def (@QXOI.u_lh_table_free_entry) (@lh_table_free_entry) (Q6nq.gwt_def (@QXOI.u_lh_entry_free_entry) (@lh_entry_free_entry) gwt_X)))))))).
Proof. first [GwApply2.gw_by_name2 GwI.segs (@QXOI.u_lh_table_free_cps) | autorewrite with gw_eqs; GwApply2.gw_by_name2 GwI.segs (@QXOI.u_lh_table_free_cps)]. Qed.
End LhFree.

End RC__1.
