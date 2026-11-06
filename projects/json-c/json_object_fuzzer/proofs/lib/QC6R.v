(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)


From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QXup.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QXup.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QRjH.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QRjH.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QHnV.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QHnV. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QCcH.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QCcH. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QfLs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QfLs. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q0Ek.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q0Ek.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QYIF.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QYIF.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QbFI.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QbFI. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qhd4.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qhd4. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qwm6.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qwm6.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qwm6.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qwm6.Mq4. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QsKa.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QsKa.Mqe. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QsKa.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QsKa.Mqd. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QlKV.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QlKV.Mqf. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q9O6.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q9O6.Mq4. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qekr.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qekr. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QJZd.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QJZd.Mq9.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QupI.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QupI.
Import ListNotations. Unset Keyed Unification. Local Ltac Stdlib.micromega.Lia.lia ::= QsRG.Mq0.mkr__lia_0. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0.
Open Scope Z_scope.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q6q3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q6q3.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

Definition GA_jo : (word -> option byte) -> Prop := fun m => lh_globA m /\ jhex_A m /\ utf8rep_A m.

Definition TGT_STACK_A_jo : Z := 2^20.
Definition TGT_BB_A_jo : Z := 1047680.
Definition TGT_BD_A_jo : Z := 2^28.
Lemma jo_envelope_ok : 0 <= TGT_STACK_A_jo <= 2^21 /\ 0 <= TGT_BB_A_jo <= 1047680 /\ 0 <= TGT_BD_A_jo <= 2^28.
Proof. unfold TGT_STACK_A_jo, TGT_BB_A_jo, TGT_BD_A_jo. lia. Qed.

Definition OBL_TARGET_jo (HIx : heap_iface_A A4L) : Prop := target_A_stmt HIx GA_jo TGT_STACK_A_jo TGT_BB_A_jo TGT_BD_A_jo.

Definition JO_GET_BOOLEAN_A : Z := 0x9d978.   Definition JO_GET_DOUBLE_A : Z := 0x9f8e4.    Definition JO_GET_INT_A : Z := 0x9dd50.
Definition JO_GET_INT64_A : Z := 0x9e4a0.     Definition JO_GET_UINT64_A : Z := 0x9e8d8.    Definition JO_GET_STRING_A : Z := 0xa0250.
Definition JO_GET_STRING_LEN_A : Z := 0xa03f4. Definition JO_GET_OBJECT_A : Z := 0x9d5e8.   Definition JO_GET_ARRAY_A : Z := 0xa08b4.
Definition JO_GET_TYPE_A : Z := 0x9c4b8.      Definition JO_VISIT_A : Z := 0xa65d4.
Definition JO_SET_INT_A : Z := 0x9e1d0.       Definition JO_SET_INT64_A : Z := 0x9e27c.     Definition JO_SET_UINT64_A : Z := 0x9ed0c.
Definition JO_SET_BOOLEAN_A : Z := 0x9db50.   Definition JO_SET_DOUBLE_A : Z := 0x9fedc.
Definition JO_SET_STRING_A : Z := 0xa0484.
Definition JO_SET_STRING_LEN_A : Z := 0xa0748.
Definition JO_TOKPARSE_A : Z := 0x93680.      Definition JO_DEEP_COPY_A : Z := 0xa14d8.     Definition JO_SHALLOW_COPY_A : Z := 0xa0a78.

Definition JO_GETNUM_STK_A : Z := 96 + 128 + 512 + 4096.
Definition JO_GETDBL_STK_A : Z := 128 + 8928 + 4096.
Definition JO_GETDBL_COSTB_A : Z := 512.  Definition JO_GETDBL_COSTD_A : Z := 0.
Definition JO_EMIT_A : Z := 0x92a2c.
Definition JO_VISIT_STK0_A : Z := 16 + 176 + 4096.  Definition JO_VISIT_STK1_A : Z := 176.
Definition JO_SETDBL_STK_A : Z := 64 + 4096.   Definition JO_SETDBL_COSTB_A : Z := 512.   Definition JO_SETDBL_COSTD_A : Z := 1.
Definition JO_SETSTR_STK_A : Z := 80 + 4096.  Definition JO_SETSTR_COSTD_A : Z := 2.
Definition jo_setstr_costB (n : Z) : Z := 16 * (n + 1) + 1024.
Definition JO_TOKPARSE_STK_A : Z := 96 + 80 + 432 + 12288 + 4096.
Definition JO_TOKPARSE_URA_A : Z := 0x932fc.
Definition JO_DEEP_STK0_A : Z := 32 + 192 + 8784.  Definition JO_DEEP_STK1_A : Z := 192.
Definition JO_GETSTR_STK0_A : Z := 48.
Definition JO_PUTX_COSTB_A : Z := 2048.   Definition JO_PUTX_COSTD_A : Z := 2.

Section Callees.
Variable HIx : heap_iface_A A4L.

Variables (tokparse_costB tokparse_costD : Z -> Z) (deep_costB deep_costD : Z -> Z) (getstr_stk : jshape -> Z) (getstr_costB : Z -> Z).

Record jo_callees_A : Prop := JoCalleesA {
ca_GETB    : jo_get_pure_A_stmt HIx JO_GET_BOOLEAN_A;
ca_GETD    : jo_get_double_A_stmt HIx JO_GET_DOUBLE_A JO_GETDBL_STK_A JO_GETDBL_COSTB_A JO_GETDBL_COSTD_A;
ca_GETI    : jo_get_num_A_stmt HIx JO_GET_INT_A JO_GETNUM_STK_A;
ca_GETI64  : jo_get_num_A_stmt HIx JO_GET_INT64_A JO_GETNUM_STK_A;
ca_GETU64  : jo_get_num_A_stmt HIx JO_GET_UINT64_A JO_GETNUM_STK_A;
ca_GETS    : jo_get_string_A_stmt HIx JO_GET_STRING_A getstr_stk getstr_costB;
ca_GETS0   : jo_get_string_null_A_stmt HIx JO_GET_STRING_A JO_GETSTR_STK0_A;
ca_GETSL   : jo_get_pure_A_stmt HIx JO_GET_STRING_LEN_A;
ca_GETO    : jo_get_pure_A_stmt HIx JO_GET_OBJECT_A;
ca_GETA    : jo_get_pure_A_stmt HIx JO_GET_ARRAY_A;
ca_GETT    : jo_get_pure_A_stmt HIx JO_GET_TYPE_A;
ca_VISIT   : jo_visit_A_stmt HIx JO_VISIT_A JO_EMIT_A JO_VISIT_STK0_A JO_VISIT_STK1_A;
ca_SETI    : jo_set_scalar_A_stmt HIx JO_SET_INT_A;
ca_SETI64  : jo_set_scalar_A_stmt HIx JO_SET_INT64_A;
ca_SETU64  : jo_set_scalar_A_stmt HIx JO_SET_UINT64_A;
ca_SETB    : jo_set_scalar_A_stmt HIx JO_SET_BOOLEAN_A;
ca_SETD    : jo_set_double_A_stmt HIx JO_SET_DOUBLE_A JO_SETDBL_STK_A JO_SETDBL_COSTB_A JO_SETDBL_COSTD_A;
ca_SETS    : jo_set_string_A_stmt HIx JO_SET_STRING_A JO_SETSTR_STK_A JO_SETSTR_COSTD_A jo_setstr_costB;
ca_SETSL   : jo_set_string_len_A_stmt HIx JO_SET_STRING_LEN_A JO_SETSTR_STK_A JO_SETSTR_COSTD_A jo_setstr_costB;
ca_TOKPARSE : jo_tokparse_A_stmt HIx JO_TOKPARSE_A JO_TOKPARSE_STK_A JO_TOKPARSE_URA_A tokparse_costB tokparse_costD;
ca_DEEP    : jo_deep_copy_A_stmt HIx JO_DEEP_COPY_A JO_SHALLOW_COPY_A JO_DEEP_STK0_A JO_DEEP_STK1_A deep_costB deep_costD;
ca_PUT     : put_stmt_A HIx;
ca_PUTX    : jo_put_xleaf_A_stmt HIx put_entry_A put_stk_A JO_PUTX_COSTB_A JO_PUTX_COSTD_A
}.
End Callees.

End RC__1.
