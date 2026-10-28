(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)


From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib Require CodeAt StepGen GwInst GwApply GwApply2. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Q6nq.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Q0Hd.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QPIU.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UC8c.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QCcH.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Q0Ek.

From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QXup.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QXup.
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
Import ListNotations. Unset Keyed Unification. Local Ltac OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.zs_idioms ::= OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.mkr__zs_idioms_3. Local Ltac OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.zs_idioms_in H ::= OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.mkr__zs_idioms_in_4 H. Local Ltac OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.zs_wrap e ::= OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.mkr__zs_wrap_1 e. Local Ltac OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.zs_wrap_in e H ::= OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.mkr__zs_wrap_in_2 e H.
Open Scope Z_scope.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Q6q3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q6q3.

Module GwI.
Definition segs := rsegs.
Definition base := 0x50b60%Z.
Definition e_1a694 := 0x521f0%Z.
Definition e_198e4 := 0x51308%Z.
Definition e_2607c := 0x60550%Z.
Definition e_24f50 := 0x5f408%Z.
Definition e_26304 := 0x607d8%Z.
Definition e_197bc := 0x51024%Z.
Lemma CODE : CodeAt.code_at rsegs 0x50b60 QPIU.Mqc.localestmt_code.  Proof. StepGen.code_at_vm. Qed.
Lemma BASE4 : (0x50b60 mod 4 = 0)%Z.  Proof. reflexivity. Qed.
Lemma BASER : (0 <= 0x50b60 /\ 0x50b60 + 12 <= 2^40)%Z.  Proof. vm_compute. split; discriminate. Qed.

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
Definition CNAME := (0x1239a)%Z.
Definition GLOBLOC := (0x97ec8)%Z.
Definition LOCALE_LOCK := (0x97f68)%Z.
Definition e_blk_1983c := 0x51254%Z.
Definition wb1983c_5 := 0x789000ef%Z.
Definition wb1983c_9 := 0x00047597%Z.
Definition wb1983c_10 := 0xc5058413%Z.
Definition joffb1983c_5 := (Z_to_bv 21 3976).
Lemma CODE_e_blk_1983c : CodeAt.code_at rsegs e_blk_1983c (QPIU.Mqc.blk_1983c_code 0x789000ef%Z 0x00047597%Z 0xc5058413%Z).  Proof. StepGen.code_at_vm. Qed.
Definition e_blk_198a8 := 0x512c0%Z.
Definition wb198a8_4 := 0x038000ef%Z.
Definition wb198a8_10 := 0x1f00106f%Z.
Definition joffb198a8_4 := (Z_to_bv 21 56).
Definition joffb198a8_10 := (Z_to_bv 21 4592).
Lemma CODE_e_blk_198a8 : CodeAt.code_at rsegs e_blk_198a8 (QPIU.Mqc.blk_198a8_code 0x038000ef%Z 0x1f00106f%Z).  Proof. StepGen.code_at_vm. Qed.
Definition e_blk_1993c := 0x51360%Z.
Definition wb1993c_10 := 0x00014517%Z.
Definition wb1993c_11 := 0x64853983%Z.
Definition wb1993c_14 := 0x00047517%Z.
Definition wb1993c_15 := 0xbd050513%Z.
Definition wb1993c_16 := 0x1b00f0ef%Z.
Definition wb1993c_25 := 0xfffc0517%Z.
Definition wb1993c_26 := 0x97d50593%Z.
Definition wb1993c_40 := 0xfffc0517%Z.
Definition wb1993c_41 := 0x94150593%Z.
Definition wb1993c_55 := 0xfffc0517%Z.
Definition wb1993c_56 := 0x90550593%Z.
Definition wb1993c_70 := 0xfffc0517%Z.
Definition wb1993c_71 := 0x8c950593%Z.
Definition wb1993c_85 := 0xfffc0517%Z.
Definition wb1993c_86 := 0x88d50593%Z.
Definition wb1993c_98 := 0xfffc0517%Z.
Definition wb1993c_99 := 0x85950493%Z.
Definition wb1993c_106 := 0x00047517%Z.
Definition wb1993c_107 := 0x9f850a13%Z.
Definition wb1993c_109 := 0xfffc5517%Z.
Definition wb1993c_110 := 0xf7450913%Z.
Definition wb1993c_114 := 0x00014517%Z.
Definition wb1993c_115 := 0x30050513%Z.
Definition wb1993c_136 := 0x6890d0ef%Z.
Definition wb1993c_138 := 0x00014597%Z.
Definition wb1993c_140 := 0x2a058913%Z.
Definition wb1993c_143 := 0x66d0d0ef%Z.
Definition wb1993c_147 := 0xfffbf517%Z.
Definition wb1993c_148 := 0x79550413%Z.
Definition wb1993c_181 := 0x5d50d0ef%Z.
Definition wb1993c_186 := 0x5c10d0ef%Z.
Definition wb1993c_190 := 0x399000ef%Z.
Definition wb1993c_194 := 0x00047517%Z.
Definition wb1993c_195 := 0x90050513%Z.
Definition wb1993c_196 := 0x1680f0ef%Z.
Definition wb1993c_209 := 0x981ff0ef%Z.
Definition joffb1993c_16 := (Z_to_bv 21 61872).
Definition joffb1993c_136 := (Z_to_bv 21 56968).
Definition joffb1993c_143 := (Z_to_bv 21 56940).
Definition joffb1993c_181 := (Z_to_bv 21 56788).
Definition joffb1993c_186 := (Z_to_bv 21 56768).
Definition joffb1993c_196 := (Z_to_bv 21 61800).
Definition joffb1993c_209 := (Z_to_bv 21 2095488).
Lemma CODE_e_blk_1993c : CodeAt.code_at rsegs e_blk_1993c (QPIU.Mqc.blk_1993c_code 0x00014517%Z 0x64853983%Z 0x00047517%Z 0xbd050513%Z 0x1b00f0ef%Z 0xfffc0517%Z 0x97d50593%Z 0xfffc0517%Z 0x94150593%Z 0xfffc0517%Z 0x90550593%Z 0xfffc0517%Z 0x8c950593%Z 0xfffc0517%Z 0x88d50593%Z 0xfffc0517%Z 0x85950493%Z 0x00047517%Z 0x9f850a13%Z 0xfffc5517%Z 0xf7450913%Z 0x00014517%Z 0x30050513%Z 0x6890d0ef%Z 0x00014597%Z 0x2a058913%Z 0x66d0d0ef%Z 0xfffbf517%Z 0x79550413%Z 0x5d50d0ef%Z 0x5c10d0ef%Z 0x399000ef%Z 0x00047517%Z 0x90050513%Z 0x1680f0ef%Z 0x981ff0ef%Z).  Proof. StepGen.code_at_vm. Qed.
Definition e_blk_1a51c := 0x51f40%Z.
Definition wb1a51c_2 := 0x00046697%Z.
Definition wb1a51c_3 := 0xf4868693%Z.
Lemma CODE_e_blk_1a51c : CodeAt.code_at rsegs e_blk_1a51c (QPIU.Mqc.blk_1a51c_code 0x00046697%Z 0xf4868693%Z).  Proof. StepGen.code_at_vm. Qed.
Definition pS4L := Eval cbv beta delta [Q0Hd.gl segs e_malloc e_free e_calloc e_realloc e_malloc2 e_free2 gTP gGOTG gGUARD gAUXV gLIBC gVOL gCS gHEXGOT gHEXPTR gHEXCHARS gIMG_LO gIMG_HI] in
(fun RC__ : gw_RC => @Q0Hd.gl RC__ segs e_malloc e_free e_calloc e_realloc e_malloc2 e_free2 gTP gGOTG gGUARD gAUXV gLIBC gVOL gCS gHEXGOT gHEXPTR gHEXCHARS gIMG_LO gIMG_HI (gH1 RC__) (gH2 RC__) (gH3 RC__) (gH4 RC__) (gH5 RC__)).
Definition pS4F := Eval cbv beta delta [Q0Hd.gf e_fn_obj_to_json_string e_fn_arr_to_json_string e_fn_bool_to_json_string e_fn_dbl_to_json_string e_fn_int_to_json_string e_fn_str_to_json_string e_fn_ud_to_json_string e_fn_free_userdata e_fn_lh_entry_free e_fn_lh_char_hash e_fn_lh_char_equal e_fn_arr_entry_free] in
(Q0Hd.gf e_fn_obj_to_json_string e_fn_arr_to_json_string e_fn_bool_to_json_string e_fn_dbl_to_json_string e_fn_int_to_json_string e_fn_str_to_json_string e_fn_ud_to_json_string e_fn_free_userdata e_fn_lh_entry_free e_fn_lh_char_hash e_fn_lh_char_equal e_fn_arr_entry_free).
End GwI.

Section RC__1. Context {RC__ : Q6q3.RunConsts}.

Definition LOCCELL : Z := 0x77c00 - 48.
Definition GLOBLOC : Z := 0x97ec8.
Definition LC_GLOBAL : Z := 2^64 - 1.
Definition LOCALE_LOCK : Z := 0x97f68.
Definition CNAME : Z := 0x1239a.

Definition usl_new (cur nw : Z) : Z := if nw =? 0 then cur else if nw =? LC_GLOBAL then GLOBLOC else nw.
Definition usl_ret (cur : Z) : Z := if cur =? GLOBLOC then LC_GLOBAL else cur.

Section LocaleStmt.
Variable HIx : heap_iface S4L.
Notation HEAPx := (HEAP S4L HIx).

Definition uselocale_stmt : Prop :=
forall (ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (cur nw : Z),
rw_cells rsegs m LOCCELL [C8 (Z_to_bv 64 cur)] -> 0 <= cur < 2^64 -> 0 <= nw < 2^64 ->
tp = Z_to_bv 64 0x77c00 -> mem_inv rsegs m ->
evt rsegs (fun ms' => exists m' a1' a2' a3' a4',
ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (usl_ret cur)) a1' a2' a3' a4' a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc ra) fc None m' (seg_rom rsegs)
/\ munch [(LOCCELL, LOCCELL + 8)] m m' /\ wmono rsegs m m' /\ mem_inv rsegs m'
/\ rw_cells rsegs m' LOCCELL [C8 (Z_to_bv 64 (usl_new cur nw))])
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 nw) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0x51f40) fc None m (seg_rom rsegs)).

Definition errno_location_stmt : Prop :=
forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : word -> option byte),
tp = Z_to_bv 64 0x77c00 ->
evt rsegs (fun ms' => ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (0x77c00 - 164)) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc ra) fc None m (seg_rom rsegs))
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0x50b60) fc None m (seg_rom rsegs)).

Definition duplocale_stmt : Prop :=
forall (ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (md : Model) (T : TSet)
(A : AS S4L HIx) (LB : list blk) (lo : Z) (errv : word),
HEAPx A LB m md ->
stk rsegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - 16 - hl_stack S4L ->
bv_unsigned sp mod 16 = 0 -> bv_unsigned sp <= hi_top S4L HIx ->
rw_cells rsegs m (0x77c00 - 164) [C4 errv] ->
tp = Z_to_bv 64 0x77c00 -> bv_unsigned ra mod 2 = 0 ->
(forall ms' m' md' A' (r : Z) (errv' : word),
ret_state S4L ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (Z_to_bv 64 r) m' ms' ->
model_vm_only md md' ->
stk rsegs m' lo (bv_unsigned sp) ->
heap_pres S4L LB (bv_unsigned sp) m m' ->
rw_cells rsegs m' (0x77c00 - 164) [C4 errv'] ->
( (r = 0 /\ errv' = Z_to_bv 64 ENOMEMv /\ HEAPx A' LB m' md')
\/ (r <> 0 /\ (exists junk, rw_cells rsegs m' r [CB 48 junk]) /\ HEAPx A' ((r, 48) :: LB) m' md') ) ->
realizes rsegs (mkCfg ms' md') T) ->
realizes rsegs (mkCfg (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 LC_GLOBAL) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0x51254) fc None m (seg_rom rsegs)) md) T.

Definition newlocale_stmt : Prop :=
forall (ra sp gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (md : Model) (T : TSet)
(A : AS S4L HIx) (LB : list blk) (lo d : Z) (junk : list byte) (errv : word),
HEAPx A LB m md -> In (d, 48) LB -> rw_cells rsegs m d [CB 48 junk] ->
rw_cells rsegs m LOCALE_LOCK [C4 (Z_to_bv 64 0)] ->
stk rsegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - 496 ->
bv_unsigned sp mod 16 = 0 -> bv_unsigned sp <= hi_top S4L HIx ->
rw_cells rsegs m (0x77c00 - 164) [C4 errv] ->
tp = Z_to_bv 64 0x77c00 -> bv_unsigned ra mod 2 = 0 ->
(forall ms' m' (r : Z) (junk' : list byte),
ret_state S4L ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (Z_to_bv 64 r) m' ms' ->
stk rsegs m' lo (bv_unsigned sp) ->
heap_pres S4L (lb_remove d LB) (bv_unsigned sp) m m' ->
rw_cells rsegs m' d [CB 48 junk'] ->
rw_cells rsegs m' LOCALE_LOCK [C4 (Z_to_bv 64 0)] ->
rw_cells rsegs m' (0x77c00 - 164) [C4 errv] ->
HEAPx A LB m' md ->
(r = d \/ r = 0) ->
realizes rsegs (mkCfg ms' md) T) ->
realizes rsegs (mkCfg (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 2) (Z_to_bv 64 CNAME) (Z_to_bv 64 d) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0x51360) fc None m (seg_rom rsegs)) md) T.

Definition freelocale_stmt : Prop :=
forall (ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (md : Model) (T : TSet)
(A : AS S4L HIx) (LB : list blk) (lo d n : Z) (errv : word),
HEAPx A LB m md -> In (d, n) LB ->
stk rsegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - 16 - hl_stack S4L ->
bv_unsigned sp mod 16 = 0 -> bv_unsigned sp <= hi_top S4L HIx ->
rw_cells rsegs m (0x77c00 - 164) [C4 errv] ->
tp = Z_to_bv 64 0x77c00 -> bv_unsigned ra mod 2 = 0 ->
(forall ms' m' md' A' (r : word),
ret_state S4L ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc r m' ms' ->
model_vm_only md md' ->
stk rsegs m' lo (bv_unsigned sp) ->
heap_pres S4L (lb_remove d LB) (bv_unsigned sp) m m' ->
rw_cells rsegs m' (0x77c00 - 164) [C4 errv] ->
HEAPx A' (lb_remove d LB) m' md' ->
realizes rsegs (mkCfg ms' md') T) ->
realizes rsegs (mkCfg (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 d) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 0x512c0) fc None m (seg_rom rsegs)) md) T.
End LocaleStmt.

End RC__1.
