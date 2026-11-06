(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)


From OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib Require CodeAt StepGen GwInst GwApply GwApply2. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q6nq.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q0Hd.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QH1t.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QC8c.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QCcH.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q0Ek.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QeL5.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q7mx.

From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QXup.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QXup.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QEQM.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QEQM.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Lib.GwApply.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q5Rg.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q5Rg.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QRjH.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QRjH.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QHnV.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QHnV. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QCcH.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QCcH. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QfLs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QfLs. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q0Ek.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q0Ek. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QjDH.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QjDH.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QmZZ.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QmZZ.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QC8c.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QC8c.Mq0.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qsw7.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qsw7. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QJjn.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QJjn. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QKQo.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QKQo. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q8tj.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q8tj.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q6WR.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q6WR. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q6WR.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q6WR.Mq0.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QeuE.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QeuE. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qxk8.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qxk8. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QNPb.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QNPb.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q6q3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q6q3.
Import ListNotations. Unset Keyed Unification. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr.
Open Scope Z_scope.

Module GwI.
Definition segs := rsegs.
Definition base := 0x23660%Z.
Definition w_24 := 0x011020ef%Z.
Definition w_26 := 0xf4dff0ef%Z.
Definition w_28 := 0x45d2c0ef%Z.
Definition w_34 := 0x7d4030ef%Z.
Definition w_39 := 0x21d020ef%Z.
Definition w_57 := 0x009020ef%Z.
Definition w_63 := 0x0c9020ef%Z.
Definition w_89 := 0x49c030ef%Z.
Definition w_97 := 0x5b8030ef%Z.
Definition w_101 := 0x12d020ef%Z.
Definition w_106 := 0x3252c0ef%Z.
Definition joff_24 := (Z_to_bv 21 10256).
Definition joff_26 := (Z_to_bv 21 2096972).
Definition joff_28 := (Z_to_bv 21 183388).
Definition joff_34 := (Z_to_bv 21 14292).
Definition joff_39 := (Z_to_bv 21 10780).
Definition joff_57 := (Z_to_bv 21 10248).
Definition joff_63 := (Z_to_bv 21 10440).
Definition joff_89 := (Z_to_bv 21 13468).
Definition joff_97 := (Z_to_bv 21 13752).
Definition joff_101 := (Z_to_bv 21 10540).
Definition joff_106 := (Z_to_bv 21 183076).
Definition e_pbfree := 0x23614%Z.
Definition e_alfree := 0x25ed0%Z.
Definition e_alread := 0x25f4c%Z.
Definition e_17bbc := 0x26024%Z.
Definition e_17cb0 := 0x26118%Z.
Definition e_17cb8 := 0x26120%Z.
Definition e_lhfree := 0x26c60%Z.
Definition e_18934 := 0x26d9c%Z.
Definition e_18a54 := 0x26ebc%Z.
Lemma CODE : CodeAt.code_at rsegs 0x23660 (Q7mx.Mq1.putloop1_code 0x011020ef%Z 0xf4dff0ef%Z 0x45d2c0ef%Z 0x7d4030ef%Z 0x21d020ef%Z 0x009020ef%Z 0x0c9020ef%Z 0x49c030ef%Z 0x5b8030ef%Z 0x12d020ef%Z 0x3252c0ef%Z).  Proof. StepGen.code_at_vm. Qed.
Lemma BASE4 : (0x23660 mod 4 = 0)%Z.  Proof. reflexivity. Qed.
Lemma BASER : (0 <= 0x23660 /\ 0x23660 + 488 <= 2^40)%Z.  Proof. vm_compute. split; discriminate. Qed.

Local Notation gw_RC := Q6q3.RunConsts (only parsing).
Local Ltac gw_lay t := let v := eval cbv beta iota delta [QC8c.Mq0.S4L QCcH.hl_malloc QCcH.hl_free QCcH.hl_calloc QCcH.hl_realloc QCcH.hl_malloc2 QCcH.hl_free2 QCcH.hl_tp QCcH.hl_got_guard QCcH.hl_guard QCcH.hl_auxv QCcH.hl_libc QCcH.hl_img_lo QCcH.hl_img_hi QCcH.hl_consts] in t in lazymatch v with (fun _ => ?n) => exact n end.
Local Ltac gw_hex k := let v := eval cbv beta iota delta [QC8c.Mq0.S4L QCcH.hl_consts] in (fun RC__ : gw_RC => @QCcH.hl_consts RC__ (@QC8c.Mq0.S4L RC__)) in
lazymatch v with (fun _ => cons (pair ?a (?f1 (?f2 ?b))) (cons (pair _ (?f3 (?f4 ?c))) nil)) => lazymatch k with 0%nat => exact a | 1%nat => exact b | _ => exact c end end.
Definition e_malloc : Z := ltac:(gw_lay (fun RC__ : gw_RC => @QCcH.hl_malloc RC__ (@QC8c.Mq0.S4L RC__))).
Definition e_free : Z := ltac:(gw_lay (fun RC__ : gw_RC => @QCcH.hl_free RC__ (@QC8c.Mq0.S4L RC__))).
Definition e_calloc : Z := ltac:(gw_lay (fun RC__ : gw_RC => @QCcH.hl_calloc RC__ (@QC8c.Mq0.S4L RC__))).
Definition e_realloc : Z := ltac:(gw_lay (fun RC__ : gw_RC => @QCcH.hl_realloc RC__ (@QC8c.Mq0.S4L RC__))).
Definition e_malloc2 : Z := ltac:(gw_lay (fun RC__ : gw_RC => @QCcH.hl_malloc2 RC__ (@QC8c.Mq0.S4L RC__))).
Definition e_free2 : Z := ltac:(gw_lay (fun RC__ : gw_RC => @QCcH.hl_free2 RC__ (@QC8c.Mq0.S4L RC__))).
Definition gTP : Z := ltac:(gw_lay (fun RC__ : gw_RC => @QCcH.hl_tp RC__ (@QC8c.Mq0.S4L RC__))).
Definition gGOTG : Z := ltac:(gw_lay (fun RC__ : gw_RC => @QCcH.hl_got_guard RC__ (@QC8c.Mq0.S4L RC__))).
Definition gGUARD : Z := ltac:(gw_lay (fun RC__ : gw_RC => @QCcH.hl_guard RC__ (@QC8c.Mq0.S4L RC__))).
Definition gAUXV : Z := ltac:(gw_lay (fun RC__ : gw_RC => @QCcH.hl_auxv RC__ (@QC8c.Mq0.S4L RC__))).
Definition gLIBC : Z := ltac:(gw_lay (fun RC__ : gw_RC => @QCcH.hl_libc RC__ (@QC8c.Mq0.S4L RC__))).
Definition gIMG_LO : Z := ltac:(gw_lay (fun RC__ : gw_RC => @QCcH.hl_img_lo RC__ (@QC8c.Mq0.S4L RC__))).
Definition gIMG_HI : Z := ltac:(gw_lay (fun RC__ : gw_RC => @QCcH.hl_img_hi RC__ (@QC8c.Mq0.S4L RC__))).
Definition gHEXGOT : Z := ltac:(gw_hex 0%nat).  Definition gHEXPTR : Z := ltac:(gw_hex 1%nat).  Definition gHEXCHARS : Z := ltac:(gw_hex 2%nat).
Definition gVOL := QC8c.Mq0.s4_volatile.  Definition gCS := QC8c.Mq0.s4_client_static.
Definition gH1 := fun RC__ : gw_RC => @QCcH.hl_static_in_img RC__ (@QC8c.Mq0.S4L RC__).
Definition gH2 := fun RC__ : gw_RC => @QCcH.hl_img_range RC__ (@QC8c.Mq0.S4L RC__).
Definition gH3 := fun RC__ : gw_RC => @QCcH.hl_scratch_in_img RC__ (@QC8c.Mq0.S4L RC__).
Definition gH4 := fun RC__ : gw_RC => @QCcH.hl_scratch_not_static RC__ (@QC8c.Mq0.S4L RC__).
Definition gH5 := fun RC__ : gw_RC => @QCcH.hl_consts_ok RC__ (@QC8c.Mq0.S4L RC__).
Definition e_fn_obj_to_json_string := Eval cbv beta iota delta [Q0Ek.fn_obj_to_json_string QC8c.Mq0.S4F] in (Q0Ek.fn_obj_to_json_string QC8c.Mq0.S4F).
Definition e_fn_arr_to_json_string := Eval cbv beta iota delta [Q0Ek.fn_arr_to_json_string QC8c.Mq0.S4F] in (Q0Ek.fn_arr_to_json_string QC8c.Mq0.S4F).
Definition e_fn_bool_to_json_string := Eval cbv beta iota delta [Q0Ek.fn_bool_to_json_string QC8c.Mq0.S4F] in (Q0Ek.fn_bool_to_json_string QC8c.Mq0.S4F).
Definition e_fn_dbl_to_json_string := Eval cbv beta iota delta [Q0Ek.fn_dbl_to_json_string QC8c.Mq0.S4F] in (Q0Ek.fn_dbl_to_json_string QC8c.Mq0.S4F).
Definition e_fn_int_to_json_string := Eval cbv beta iota delta [Q0Ek.fn_int_to_json_string QC8c.Mq0.S4F] in (Q0Ek.fn_int_to_json_string QC8c.Mq0.S4F).
Definition e_fn_str_to_json_string := Eval cbv beta iota delta [Q0Ek.fn_str_to_json_string QC8c.Mq0.S4F] in (Q0Ek.fn_str_to_json_string QC8c.Mq0.S4F).
Definition e_fn_ud_to_json_string := Eval cbv beta iota delta [Q0Ek.fn_ud_to_json_string QC8c.Mq0.S4F] in (Q0Ek.fn_ud_to_json_string QC8c.Mq0.S4F).
Definition e_fn_free_userdata := Eval cbv beta iota delta [Q0Ek.fn_free_userdata QC8c.Mq0.S4F] in (Q0Ek.fn_free_userdata QC8c.Mq0.S4F).
Definition e_fn_lh_entry_free := Eval cbv beta iota delta [Q0Ek.fn_lh_entry_free QC8c.Mq0.S4F] in (Q0Ek.fn_lh_entry_free QC8c.Mq0.S4F).
Definition e_fn_lh_char_hash := Eval cbv beta iota delta [Q0Ek.fn_lh_char_hash QC8c.Mq0.S4F] in (Q0Ek.fn_lh_char_hash QC8c.Mq0.S4F).
Definition e_fn_lh_char_equal := Eval cbv beta iota delta [Q0Ek.fn_lh_char_equal QC8c.Mq0.S4F] in (Q0Ek.fn_lh_char_equal QC8c.Mq0.S4F).
Definition e_fn_arr_entry_free := Eval cbv beta iota delta [Q0Ek.fn_arr_entry_free QC8c.Mq0.S4F] in (Q0Ek.fn_arr_entry_free QC8c.Mq0.S4F).
Lemma CODE_e_18a54 : CodeAt.code_at rsegs e_18a54 QH1t.Mq1.blk_18a54_code.  Proof. StepGen.code_at_vm. Qed.
Lemma CODE_e_17cb0 : CodeAt.code_at rsegs e_17cb0 QH1t.Mq1.blk_17cb0_code.  Proof. StepGen.code_at_vm. Qed.
Lemma CODE_e_17bbc : CodeAt.code_at rsegs e_17bbc QH1t.Mq1.blk_17bbc_code.  Proof. StepGen.code_at_vm. Qed.
Lemma CODE_e_18934 : CodeAt.code_at rsegs e_18934 QH1t.Mq1.blk_18934_code.  Proof. StepGen.code_at_vm. Qed.
Lemma CODE_e_17cb8 : CodeAt.code_at rsegs e_17cb8 QH1t.Mq1.blk_17cb8_code.  Proof. StepGen.code_at_vm. Qed.
Definition lh_table_free_cps := @QeL5.lh_table_free_cps.
Definition pS4L := Eval cbv beta delta [Q0Hd.gl segs e_malloc e_free e_calloc e_realloc e_malloc2 e_free2 gTP gGOTG gGUARD gAUXV gLIBC gVOL gCS gHEXGOT gHEXPTR gHEXCHARS gIMG_LO gIMG_HI] in
(fun RC__ : gw_RC => @Q0Hd.gl RC__ segs e_malloc e_free e_calloc e_realloc e_malloc2 e_free2 gTP gGOTG gGUARD gAUXV gLIBC gVOL gCS gHEXGOT gHEXPTR gHEXCHARS gIMG_LO gIMG_HI (gH1 RC__) (gH2 RC__) (gH3 RC__) (gH4 RC__) (gH5 RC__)).
Definition pS4F := Eval cbv beta delta [Q0Hd.gf e_fn_obj_to_json_string e_fn_arr_to_json_string e_fn_bool_to_json_string e_fn_dbl_to_json_string e_fn_int_to_json_string e_fn_str_to_json_string e_fn_ud_to_json_string e_fn_free_userdata e_fn_lh_entry_free e_fn_lh_char_hash e_fn_lh_char_equal e_fn_arr_entry_free] in
(Q0Hd.gf e_fn_obj_to_json_string e_fn_arr_to_json_string e_fn_bool_to_json_string e_fn_dbl_to_json_string e_fn_int_to_json_string e_fn_str_to_json_string e_fn_ud_to_json_string e_fn_free_userdata e_fn_lh_entry_free e_fn_lh_char_hash e_fn_lh_char_equal e_fn_arr_entry_free).
End GwI.

Section RC__1. Context {RC__ : Q6q3.RunConsts}.

Section Loop2.
Variable HIx : heap_iface S4L.
Notation HEAPx := (HEAP S4L HIx).
Variables (sp gp s10 s11 : word) (lo : Z) (errv : word).

Notation SPR := (Z_to_bv 64 (bv_unsigned sp + -96)).
Notation TP := (Z_to_bv 64 0x75e70).
Notation CM1 := (Z_to_bv 64 18446744073709551615).
Notation NEXT := (next_post HIx sp gp s10 s11 lo errv).

Definition tyof (isobj : bool) : Z := if isobj then 4 else 5.

Definition zhead (isobj : bool) (m : word -> option byte) (x q : Z) (kids : list (option jshape)) (XBS : list blk) : Prop :=
if isobj then zobjc rsegs S4F m x q kids XBS else zarrc rsegs S4F m x q kids XBS.

Definition head_stmt (isobj : bool) (kids : list (option jshape)) : Prop :=
forall (x1 t0 t1 t2 x9 a0 a1 a2 a3 a4 a5 a6 a7 x18 x19 x20 t3 t4 t5 t6 : word) (F1 : bvmap 5 word) (fc1 : bv 32)
(m : word -> option byte) (md : Model) (A : AS S4L HIx) (LB XBS : list blk) (x q : Z) (T : TSet),
HEAPx A (XBS ++ LB) m md ->
zhead isobj m x q kids XBS ->
stk rsegs m lo (bv_unsigned sp + -96) -> rw_cells rsegs m (0x75e70 - 164) [C4 errv] ->
(forall ms' md', NEXT q F1 fc1 m md LB ms' md' -> realizes rsegs (mkCfg ms' md') T) ->
realizes rsegs (mkCfg (MS (mkR x1 SPR gp TP t0 t1 t2 (Z_to_bv 64 x) x9 a0 a1 a2 a3 a4 a5 a6 a7 x18 x19 x20
(Z_to_bv 64 2) (Z_to_bv 64 4) (Z_to_bv 64 6) (Z_to_bv 64 5) CM1 s10 s11 t3 t4 t5 t6)
F1 (Z_to_bv 64 0x236dc) fc1 None m (seg_rom rsegs)) md) T.

Definition desc_stmt (c : jshape) : Prop :=
match c with Sobj kids => head_stmt true kids | Sarr kids => head_stmt false kids | _ => True end.
Definition desc_opt (k : option jshape) : Prop := match k with Some c => desc_stmt c | None => True end.
Definition kids_desc (kids : list (option jshape)) : Prop := forall k, In k kids -> desc_opt k.

Definition zcont (isobj : bool) (m : word -> option byte) (x q : Z) (kids : list (option jshape)) (nz : nat) (cur : Z) (XBS : list blk) : Prop :=
if isobj then exists t tbl size es svs, zobj rsegs S4F m x q kids nz t tbl size es svs XBS /\
(forall kids1 kl, kids = kids1 ++ [kl] -> exists e, nth_error es (length kids1) = Some e /\ cur = ent_addr tbl (le_ix e))
else exists a arr size, zarr rsegs S4F m x q kids nz a arr size XBS.

Definition cont_stmt (isobj : bool) (kids : list (option jshape)) : Prop :=
forall (x1 t0 t1 t2 x9 a0 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (F1 : bvmap 5 word) (fc1 : bv 32)
(m : word -> option byte) (md : Model) (A : AS S4L HIx) (LB XBS : list blk) (x q : Z) (T : TSet) (nz : nat) (cur : Z),
HEAPx A (XBS ++ LB) m md ->
zcont isobj m x q kids nz cur XBS ->
stk rsegs m lo (bv_unsigned sp + -96) -> rw_cells rsegs m (0x75e70 - 164) [C4 errv] ->
(forall ms' md', NEXT q F1 fc1 m md LB ms' md' -> realizes rsegs (mkCfg ms' md') T) ->
realizes rsegs (mkCfg (MS (mkR x1 SPR gp TP t0 t1 t2 (Z_to_bv 64 x) x9 a0 (Z_to_bv 64 (tyof isobj)) a2 a3 a4 a5 a6 a7
(Z_to_bv 64 cur) (Z_to_bv 64 (Z.of_nat (length kids))) (Z_to_bv 64 (Z.of_nat nz))
(Z_to_bv 64 2) (Z_to_bv 64 4) (Z_to_bv 64 6) (Z_to_bv 64 5) CM1 s10 s11 t3 t4 t5 t6)
F1 (Z_to_bv 64 0x23718) fc1 None m (seg_rom rsegs)) md) T.

Definition zbodyp (isobj : bool) (m : word -> option byte) (x q : Z) (kids : list (option jshape)) (k : option jshape) (nz : nat) (cur : Z) (XBS : list blk) : Prop :=
if isobj then exists t tbl size es svs e, zobj rsegs S4F m x q (kids ++ [k]) nz t tbl size es svs XBS /\
nth_error es (length kids) = Some e /\ cur = ent_addr tbl (le_ix e)
else exists a arr size, zarr rsegs S4F m x q (kids ++ [k]) nz a arr size XBS.

Definition body_stmt (isobj : bool) (kids : list (option jshape)) (k : option jshape) : Prop :=
forall (x1 t0 t1 t2 x9 a0 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (F1 : bvmap 5 word) (fc1 : bv 32)
(m : word -> option byte) (md : Model) (A : AS S4L HIx) (LB XBS : list blk) (x q : Z) (T : TSet) (nz : nat) (cur : Z),
HEAPx A (XBS ++ LB) m md ->
zbodyp isobj m x q kids k nz cur XBS ->
stk rsegs m lo (bv_unsigned sp + -96) -> rw_cells rsegs m (0x75e70 - 164) [C4 errv] ->
(forall ms' md', NEXT q F1 fc1 m md LB ms' md' -> realizes rsegs (mkCfg ms' md') T) ->
realizes rsegs (mkCfg (MS (mkR x1 SPR gp TP t0 t1 t2 (Z_to_bv 64 x) x9 a0 (Z_to_bv 64 (tyof isobj)) a2 a3 a4 a5 a6 a7
(Z_to_bv 64 cur) (Z_to_bv 64 (Z.of_nat (length kids))) (Z_to_bv 64 (Z.of_nat nz + 1))
(Z_to_bv 64 2) (Z_to_bv 64 4) (Z_to_bv 64 6) (Z_to_bv 64 5) CM1 s10 s11 t3 t4 t5 t6)
F1 (Z_to_bv 64 0x23724) fc1 None m (seg_rom rsegs)) md) T.

Definition tojs_of (isobj : bool) : Z := if isobj then fn_obj_to_json_string S4F else fn_arr_to_json_string S4F.

Local Definition gwt_X : unit := (Q6nq.gwt_def (@QH1t.Mq1.next_post) (@QNPb.next_post) (Q6nq.gwt_def (@Q7mx.Mq1.next_post) (@QNPb.next_post) (Q6nq.gwt_pat GwI.pS4L (@QC8c.Mq0.S4L) (Q6nq.gwt_pat GwI.pS4F QC8c.Mq0.S4F Q6nq.gwt_nil)))).
#[using="Type"] Lemma zhead_hdr : ltac2:(Q6nq.ty2 'GwI.segs '(@QH1t.Mq1.zhead_hdr) [] '(@nil Z) '(Q6nq.gwt_def (@QH1t.Mq1.tojs_of) (@tojs_of) (Q6nq.gwt_def (@QH1t.Mq1.body_stmt) (@body_stmt) (Q6nq.gwt_def (@QH1t.Mq1.zbodyp) (@zbodyp) (Q6nq.gwt_def (@QH1t.Mq1.cont_stmt) (@cont_stmt) (Q6nq.gwt_def (@QH1t.Mq1.zcont) (@zcont) (Q6nq.gwt_def (@QH1t.Mq1.kids_desc) (@kids_desc) (Q6nq.gwt_def (@QH1t.Mq1.desc_opt) (@desc_opt) (Q6nq.gwt_def (@QH1t.Mq1.desc_stmt) (@desc_stmt) (Q6nq.gwt_def (@QH1t.Mq1.head_stmt) (@head_stmt) (Q6nq.gwt_def (@QH1t.Mq1.zhead) (@zhead) (Q6nq.gwt_def (@QH1t.Mq1.tyof) (@tyof) gwt_X)))))))))))).
Proof. first [GwApply2.gw_by_name2 GwI.segs (@QH1t.Mq1.zhead_hdr) | autorewrite with gw_eqs; GwApply2.gw_by_name2 GwI.segs (@QH1t.Mq1.zhead_hdr)]. Qed.

#[using="Type"] Lemma zhead_agree : ltac2:(Q6nq.ty2 'GwI.segs '(@QH1t.Mq1.zhead_agree) [] '(@nil Z) '(Q6nq.gwt_def (@QH1t.Mq1.tojs_of) (@tojs_of) (Q6nq.gwt_def (@QH1t.Mq1.body_stmt) (@body_stmt) (Q6nq.gwt_def (@QH1t.Mq1.zbodyp) (@zbodyp) (Q6nq.gwt_def (@QH1t.Mq1.cont_stmt) (@cont_stmt) (Q6nq.gwt_def (@QH1t.Mq1.zcont) (@zcont) (Q6nq.gwt_def (@QH1t.Mq1.kids_desc) (@kids_desc) (Q6nq.gwt_def (@QH1t.Mq1.desc_opt) (@desc_opt) (Q6nq.gwt_def (@QH1t.Mq1.desc_stmt) (@desc_stmt) (Q6nq.gwt_def (@QH1t.Mq1.head_stmt) (@head_stmt) (Q6nq.gwt_def (@QH1t.Mq1.zhead) (@zhead) (Q6nq.gwt_def (@QH1t.Mq1.tyof) (@tyof) gwt_X)))))))))))).
Proof. first [GwApply2.gw_by_name2 GwI.segs (@QH1t.Mq1.zhead_agree) | autorewrite with gw_eqs; GwApply2.gw_by_name2 GwI.segs (@QH1t.Mq1.zhead_agree)]. Qed.

#[using="Type"] Lemma zomb_zhead : ltac2:(Q6nq.ty2 'GwI.segs '(@QH1t.Mq1.zomb_zhead) [] '(@nil Z) '(Q6nq.gwt_def (@QH1t.Mq1.tojs_of) (@tojs_of) (Q6nq.gwt_def (@QH1t.Mq1.body_stmt) (@body_stmt) (Q6nq.gwt_def (@QH1t.Mq1.zbodyp) (@zbodyp) (Q6nq.gwt_def (@QH1t.Mq1.cont_stmt) (@cont_stmt) (Q6nq.gwt_def (@QH1t.Mq1.zcont) (@zcont) (Q6nq.gwt_def (@QH1t.Mq1.kids_desc) (@kids_desc) (Q6nq.gwt_def (@QH1t.Mq1.desc_opt) (@desc_opt) (Q6nq.gwt_def (@QH1t.Mq1.desc_stmt) (@desc_stmt) (Q6nq.gwt_def (@QH1t.Mq1.head_stmt) (@head_stmt) (Q6nq.gwt_def (@QH1t.Mq1.zhead) (@zhead) (Q6nq.gwt_def (@QH1t.Mq1.tyof) (@tyof) gwt_X)))))))))))).
Proof. first [GwApply2.gw_by_name2 GwI.segs (@QH1t.Mq1.zomb_zhead) | autorewrite with gw_eqs; GwApply2.gw_by_name2 GwI.segs (@QH1t.Mq1.zomb_zhead)]. Qed.

#[using="Type"] Lemma next_post_w : forall q F1 fc1 F2 fc2 m1 m2 md1 md2 LB ms md,
fsaved F1 F2 -> (frm0 fc1 -> frm0 fc2) -> model_vm_only md1 md2 ->
heap_pres S4L LB (bv_unsigned sp + -96) m1 m2 ->
NEXT q F2 fc2 m2 md2 LB ms md -> NEXT q F1 fc1 m1 md1 LB ms md.
Proof. first [GwApply2.gw_by_name2 GwI.segs (@QH1t.Mq1.next_post_w) | autorewrite with gw_eqs; GwApply2.gw_by_name2 GwI.segs (@QH1t.Mq1.next_post_w)]. Qed.
End Loop2.

End RC__1.
