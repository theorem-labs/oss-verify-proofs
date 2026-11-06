(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)


From OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib Require CodeAt StepGen GwInst GwApply GwApply2. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q6nq.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q0Hd.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QxiR.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QC8c.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QCcH.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q0Ek.
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
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QSL3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QSL3.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q22i.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q22i. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q6us.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q6us. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QT7b.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QT7b. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QqWD.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QqWD.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QnCn.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QnCn.
Import ListNotations. Unset Keyed Unification. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr.
Open Scope Z_scope.

Module GwI.
Definition segs := usegs.
Definition base := 0x285a8%Z.
Definition w_12 := 0xfffeb897%Z.
Definition w_13 := 0xe288b787%Z.
Definition hi_12 := (Z_to_bv 20 1048555).
Definition lo_13 := (Z_to_bv 12 3624).
Definition G_10760 := 0x13400%Z.
Lemma CODE : CodeAt.code_at usegs 0x285a8 (QxiR.ulhprobe_code 0xfffeb897%Z 0xe288b787%Z).  Proof. StepGen.code_at_vm. Qed.
Lemma BASE4 : (0x285a8 mod 4 = 0)%Z.  Proof. reflexivity. Qed.
Lemma BASER : (0 <= 0x285a8 /\ 0x285a8 + 484 <= 2^40)%Z.  Proof. vm_compute. split; discriminate. Qed.

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
Definition ent_addr_mod8 := @QT7b.ent_addr_mod8.
Definition pS4L := Eval cbv beta delta [Q0Hd.gl segs e_malloc e_free e_calloc e_realloc e_malloc2 e_free2 gTP gGOTG gGUARD gAUXV gLIBC gVOL gCS gHEXGOT gHEXPTR gHEXCHARS gIMG_LO gIMG_HI] in
(fun RC__ : gw_RC => @Q0Hd.gl RC__ segs e_malloc e_free e_calloc e_realloc e_malloc2 e_free2 gTP gGOTG gGUARD gAUXV gLIBC gVOL gCS gHEXGOT gHEXPTR gHEXCHARS gIMG_LO gIMG_HI (gH1 RC__) (gH2 RC__) (gH3 RC__) (gH4 RC__) (gH5 RC__)).
Definition pS4F := Eval cbv beta delta [Q0Hd.gf e_fn_obj_to_json_string e_fn_arr_to_json_string e_fn_bool_to_json_string e_fn_dbl_to_json_string e_fn_int_to_json_string e_fn_str_to_json_string e_fn_ud_to_json_string e_fn_free_userdata e_fn_lh_entry_free e_fn_lh_char_hash e_fn_lh_char_equal e_fn_arr_entry_free] in
(Q0Hd.gf e_fn_obj_to_json_string e_fn_arr_to_json_string e_fn_bool_to_json_string e_fn_dbl_to_json_string e_fn_int_to_json_string e_fn_str_to_json_string e_fn_ud_to_json_string e_fn_free_userdata e_fn_lh_entry_free e_fn_lh_char_hash e_fn_lh_char_equal e_fn_arr_entry_free).
End GwI.

Section UProbe.
Variables (sp gp tp : word) (s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32).
Variables (t tbl size k v opts : Z) (svs : list slotv).

Definition u_ins_regs (x1 x7 x8 x9 : word) (n : Z) (x17 x18 x19 x20 x28 x29 x30 x31 : word) :=
mkR x1 (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp (Z_to_bv 64 40) (Z_to_bv 64 (-3)) x7 x8 x9
(Z_to_bv 64 t) (Z_to_bv 64 k) (Z_to_bv 64 v) (Z_to_bv 64 n) (Z_to_bv 64 opts) (Z_to_bv 64 tbl) (Z_to_bv 64 size) x17
x18 x19 x20 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31.

Local Definition gwt_X : unit := (Q6nq.gwt_def (@QAyu.Mq3.is_free) (@Q6us.is_free) (Q6nq.gwt_pat GwI.pS4L (@QC8c.U4L) (Q6nq.gwt_pat GwI.pS4F QC8c.U4F Q6nq.gwt_nil))).
#[using="Type"] Lemma u_lh_probe_loop : ltac2:(Q6nq.ty2 'GwI.segs '(@QxiR.u_lh_probe_loop) [] '([165540; 165636]%Z : list Z) '(Q6nq.gwt_zc LH_FREEDv (Q6nq.gwt_def (@QxiR.u_ins_regs) (@u_ins_regs) gwt_X))).
Proof. first [GwApply2.gw_by_name2 GwI.segs (@QxiR.u_lh_probe_loop) | autorewrite with gw_eqs; GwApply2.gw_by_name2 GwI.segs (@QxiR.u_lh_probe_loop)]. Qed.
End UProbe.
