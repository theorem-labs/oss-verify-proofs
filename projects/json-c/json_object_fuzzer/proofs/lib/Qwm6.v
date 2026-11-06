(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)

From Stdlib Require ZArith List Lia.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QXup QCcH Q0Ek Q7UD Qhd4 QGcC Q6q3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq0.

Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import QXup.
Import QCcH Q0Ek.
Import Q7UD Qhd4 QGcC.Mq0.
Import Q6q3.
Import ListNotations. Local Ltac OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.zs_idioms ::= OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.mkr__zs_idioms_3. Local Ltac OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.zs_idioms_in H ::= OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.mkr__zs_idioms_in_4 H. Local Ltac OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.zs_wrap e ::= OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.mkr__zs_wrap_1 e. Local Ltac OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.zs_wrap_in e H ::= OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.mkr__zs_wrap_in_2 e H.
Open Scope Z_scope.

Definition asegs_wx : True := I.

Section RC__1. Context {RC__ : Q6q3.RunConsts}.

Definition A_TP : Z := 0x622e60.
Definition A_ERRNO : Z := 0x622e60 - 164.
Definition A_SB : Z := 0x7fff8000.

Definition A_HMB : Z := 0x10007fff8000.
Definition app_mem (s n : Z) : Prop := 0 <= s /\ ((s + n + 8 <= A_SB) \/ (A_HMB <= s /\ s + n + 8 <= 2^47)).
Definition A_GOT_SB : Z := 0xe5db8.
Definition A_SB_CELL : Z := 0xefaf8.

Definition a4_client_static (a : Z) : Prop :=
(0xea500 <= a < 0xec420)
\/ (0xec448 <= a < 0xec498)
\/ (0x181998 <= a < 0x1819a8)
\/ (0x612140 <= a < 0x622d90)
\/ (0x622d90 <= a < 0x644280
/\ ~ (0x622dbc <= a < 0x622dc0)
/\ ~ (0x622e50 <= a < 0x622e58)
/\ ~ (0x622e08 <= a < 0x622e10)
/\ ~ (0x622e58 <= a < 0x622e98)
/\ ~ (0x642ea0 <= a < 0x642ea8)
/\ ~ (0x6430f0 <= a < 0x643158)
/\ ~ (0x6431e0 <= a < 0x643588)).

Definition a4_volatile (a : Z) : Prop := (0xea560 <= a < 0xea564) \/ (0xea940 <= a < 0xea948).

Definition A4H : heap_layout :=
{| hl_segs := asegs;
hl_malloc := 0x632c8; hl_free := 0x632c4; hl_calloc := 0x632cc; hl_realloc := 0x632d0;
hl_malloc2 := 0xce630; hl_free2 := 0xcdca4;
hl_tp := A_TP;
hl_got_guard := 0xe6b80; hl_guard := 0x642ea0; hl_auxv := 0x6430f8; hl_libc := 0x6430f0; hl_volatile := a4_volatile;
hl_stack := 8256;
hl_client_static := a4_client_static;
hl_scratch := fun a => A_TP - 164 <= a < A_TP - 160;
hl_consts := [];
hl_img_lo := 0x10000; hl_img_hi := 0x645000;
hl_static_in_img := ltac:(unfold a4_client_static; cbn; intros; lia);
hl_img_range := ltac:(unfold alloc_ceiling, sp_window_lo, stack_max_size; lia);
hl_scratch_in_img := ltac:(unfold A_TP; cbn; intros; lia);
hl_scratch_not_static := ltac:(unfold a4_client_static, A_TP; cbn; intros; lia);
hl_consts_ok := ltac:(cbn; intros c a []) |}.

Definition a4_rt_consts : list (Z * list byte) :=
[ (0xe6928, le8 (Z_to_bv 64 0xf07d9));
(0xf07d9, [Z_to_bv 8 1]);
(0xf07d8, [Z_to_bv 8 1]);
(0xe7db0, le8 (Z_to_bv 64 0xdb750));
(0xe7da8, le8 (Z_to_bv 64 0xdb34c));
(0xe5da8, le8 (Z_to_bv 64 0x181628));
(0xe7c08, le8 (Z_to_bv 64 0xdb9b0));
(0x181723, [Z_to_bv 8 1]);

(0xe5dc0, le8 (Z_to_bv 64 0xf07e8));
(0xf07e8, le8 (Z_to_bv 64 0));
(0xe5dc8, le8 (Z_to_bv 64 0xf07f0));
(0xf07f0, le8 (Z_to_bv 64 0));
(0xe5dd0, le8 (Z_to_bv 64 0xf07e0));
(0xf07e0, le8 (Z_to_bv 64 0x7fffffffffff));
(0xe7c80, le8 (Z_to_bv 64 0xd385c));
(0xe7c88, le8 (Z_to_bv 64 0xd9004));
(0x18167c, [Z_to_bv 8 1]);
(0x6446f8, le4 (Z_to_bv 64 0));

(0x18171d, [Z_to_bv 8 0]);
(0x181722, [Z_to_bv 8 1]);
(0xe5db0, le8 (Z_to_bv 64 0xed2f8));
(0xed315, [Z_to_bv 8 1]);
(0xe7d80, le8 (Z_to_bv 64 0xda7e8));
(0xe7d30, le8 (Z_to_bv 64 0xccddc));

(0xe6a98, le8 (Z_to_bv 64 0xa1d2c));
(0xec440, le8 (Z_to_bv 64 1));
(0xed3b0, le8 (Z_to_bv 64 0));
(0xed310, le4 (Z_to_bv 64 1));
(0xef35c, [Z_to_bv 8 1]);
(0x1816a0, le8 (Z_to_bv 64 0xffffffffffffffff));

(0xe6a20, le8 (Z_to_bv 64 0xe5cb0));
(0xe5cb0, le8 (Z_to_bv 64 0xea660));
(0xe6a28, le8 (Z_to_bv 64 0x0));
(0xe7c58, le8 (Z_to_bv 64 0xe1270));
(0xe6bb0, le8 (Z_to_bv 64 0xe2400) ++ le8 (Z_to_bv 64 0xe23f0));
(0xe23f0, le8 (Z_to_bv 64 0x99f88) ++ le8 (Z_to_bv 64 0x3dee0));
(0xe5d88, le8 (Z_to_bv 64 0xcc594) ++ le8 (Z_to_bv 64 0x0));
(0xe7c00, le8 (Z_to_bv 64 0xe7c00));
(0xe5d98, le8 (Z_to_bv 64 0x17f5a0) ++ le8 (Z_to_bv 64 0xe7de8) ++ le8 (Z_to_bv 64 0x181628) ++ le8 (Z_to_bv 64 0xed2f8) ++ le8 (Z_to_bv 64 0xefaf8) ++ le8 (Z_to_bv 64 0xf07e8) ++ le8 (Z_to_bv 64 0xf07f0) ++ le8 (Z_to_bv 64 0xf07e0) ++ le8 (Z_to_bv 64 0xe7db0));
(0xe6ab0, le8 (Z_to_bv 64 0xea960) ++ le8 (Z_to_bv 64 0xec420));

(0xe6a50, le8 (Z_to_bv 64 0x9dd64));
(0xe6a78, le8 (Z_to_bv 64 0x930e8));

(0x181725, [Z_to_bv 8 1]);
(0xe7c30, le8 (Z_to_bv 64 0xdb85c));
(0xe6a38, le8 (Z_to_bv 64 0x9c460));
(0xe6a40, le8 (Z_to_bv 64 0x9cb08));
(0xe6a48, le8 (Z_to_bv 64 0x9cf10));
(0xe6a60, le8 (Z_to_bv 64 0x9dde4));
(0xe6a88, le8 (Z_to_bv 64 0xa39f8));
(0xe6a90, le8 (Z_to_bv 64 0xa3c68));
(0xe6aa0, le8 (Z_to_bv 64 0xa2d9c));
(0xe6a58, le8 (Z_to_bv 64 0x9dd6c));
(0xe6a68, le8 (Z_to_bv 64 0x9edbc));
(0xe6a70, le8 (Z_to_bv 64 0xea520));

(0xe5c50, le8 (Z_to_bv 64 0x1485d));
(0xe2808, le8 (Z_to_bv 64 0x9ae48));
(0xe2810, le8 (Z_to_bv 64 0x9af30));
(0xe2818, le8 (Z_to_bv 64 0x9af3c));
(0xe2820, le8 (Z_to_bv 64 0x9b1a4));
(0xe2828, le8 (Z_to_bv 64 0x9b600));
(0xe2830, le8 (Z_to_bv 64 0x9ba30)) ].

Definition a4_straces : list (Z * Z * option Z) :=
[ (0x632cc, 0x99fe0, None); (0x632c8, 0x9a024, None); (0x632c4, 0x9a05c, None); (0x632cc, 0xa1d8c, None); (0x632cc, 0xa1dcc, None); (0x632c4, 0xa1e78, None); (0x632cc, 0xa1f74, None); (0x632cc, 0xa1fb4, None); (0x632c4, 0xa214c, None); (0x632c4, 0xa2250, None); (0x632c4, 0xa2258, None); (0x632cc, 0x92b10, None); (0x632cc, 0x92b24, None); (0x632c4, 0x92c3c, None); (0x632c4, 0x92ccc, None); (0x632c4, 0x92cd4, None);
(0x632c8, 0x9164c, None);
(0x632c8, 0x916a0, None);
(0x632c4, 0x916c4, None);
(0x632c4, 0x917f4, None);
(0x632c8, 0x9192c, None);
(0x632c4, 0x919c0, None);
(0x632cc, 0x857c4, None);
(0x632cc, 0x857d8, None);
(0x632c4, 0x858d4, None);
(0x632c4, 0x8591c, None);
(0x632c4, 0x85924, None);
(0x632c4, 0x92eb0, None);
(0x632c4, 0x92f64, None);
(0x632c4, 0x92f4c, None);
(0x632c4, 0x85708, None);
(0x632c4, 0x937ac, (Some 0x93080));
(0x632c4, 0x938f8, (Some 0x93080));
(0x632c4, 0x93d38, (Some 0x93080));
(0x632c4, 0x94360, (Some 0x93080));
(0x4fa00, 0x95f88, (Some 0x93080));
(0x632c4, 0x98280, (Some 0x93080));
(0x632c8, 0x9bbfc, (Some 0x93080));
(0x632c8, 0x9d9cc, (Some 0x93080));
(0x632c8, 0x9daec, (Some 0x93080));
(0x632c8, 0x9e570, (Some 0x93080));
(0x632c8, 0x9eb50, (Some 0x93080));
(0x632c8, 0x9c004, None);
(0x632c4, 0x9bcb4, None);
(0x4fa00, 0x9db7c, None);
(0x632c4, 0x9dc20, None);
(0x632c4, 0x9dc28, None);
(0x632c4, 0x9ebec, None);
(0x4fa00, 0x9bf60, None);
(0x632cc, 0x8cb68, None);
(0x632c8, 0x8cb94, None);
(0x632c4, 0x8cbcc, None);
(0x632d0, 0x9a1ec, None);
(0x632d0, 0x9a4d4, None);
(0x632c4, 0x9a70c, None);
(0x632c4, 0x9aab0, None);
(0x632c4, 0x9ad3c, None);
(0x632c4, 0x9bcac, None);
(0x632c4, 0x9aa94, None);
(0x632c4, 0x9aab8, None);
(0x632c4, 0x9a9f8, None);
(0x632c4, 0x9aa64, None);
(0x632c4, 0x9ac64, None);
(0x632c4, 0x9acc0, None);
(0x632c4, 0x9ace4, None);
(0x632c4, 0x9ad20, None);
(0x632c4, 0x9ad44, None);
(0x632c4, 0x9bdbc, None);
(0x632c8, 0xa03c8, None);
(0x632c8, 0xa0424, None);
(0x632c4, 0xa044c, None);
(0x632c4, 0xa0564, None);
(0x632d0, 0xa0730, None);
(0x632d0, 0xa08fc, None);
(0x632cc, 0x91e3c, None);
(0x632cc, 0x91e64, None);
(0x632c4, 0x91f10, None);
(0x632cc, 0x91ffc, None);
(0x632cc, 0x92024, None);
(0x632c4, 0x921a4, None);
(0x632c4, 0x922a8, None);
(0x632c4, 0x922b0, None);
(0x632c4, 0xa27ac, None) ].

Definition A4L : heap_layout_A :=
{| hla_base := A4H;
hl_sb := A_SB; hl_sb_cell := A_SB_CELL; hl_got_sb := A_GOT_SB;
hl_uar_cell := 0xefb00; hl_got_uar := 0xe5e10;
hl_stack_malloc := fun k => if Z.eqb k 0 then 0x4a790 else if Z.eqb k 1 then 0x4a904 else if Z.eqb k 2 then 0x4aa94 else 0;
hl_strdup := 0x4fa00;
hl_stack_A := 4096;
hl_gp := 0x10800;
hl_pristine := [(0xe23d0, 0xe6b80); (0xe6b88, 0xe6c00); (0xe7c00, 0xe7df0)];
hl_globals := [];
hl_reg_globals := tokA_reg_globals;
hl_straces := a4_straces;
hl_rt_consts := a4_rt_consts;
hl_sb_range := ltac:(unfold A_SB; lia) |}.

Definition A4F : fnaddrs :=
{| fn_obj_to_json_string := 0x9b1a4;
fn_arr_to_json_string := 0x9b600;
fn_bool_to_json_string := 0x9ae48;
fn_dbl_to_json_string := 0x9af30;
fn_int_to_json_string := 0x9af3c;
fn_str_to_json_string := 0x9ba30;
fn_ud_to_json_string := 0x9dcec;
fn_free_userdata := 0x9dd64;
fn_lh_entry_free := 0x9bd40;
fn_lh_char_hash := 0xa0bb8;
fn_lh_char_equal := 0xa1d2c;
fn_arr_entry_free := 0x9ec38 |}.

End RC__1.

Ltac a4l :=
cbn [hl_segs hl_stack hl_stack_A hl_tp hl_calloc hl_malloc hl_free hl_realloc hl_malloc2 hl_free2 hl_straces hl_strdup hl_stack_malloc
hl_sb hl_sb_cell hl_got_sb hl_uar_cell hl_got_uar hl_img_lo hl_img_hi hl_got_guard hl_guard hl_rt_consts hl_reg_globals hla_base A4L A4H] in *;
unfold a4_straces, a4_rt_consts, A_TP, A_ERRNO, A_SB, A_SB_CELL, A_GOT_SB in *.
Ltac a4l_goal :=
cbn [hl_segs hl_stack hl_stack_A hl_tp hl_calloc hl_malloc hl_free hl_realloc hl_malloc2 hl_free2 hl_straces hl_strdup hl_stack_malloc
hl_sb hl_sb_cell hl_got_sb hl_uar_cell hl_got_uar hl_img_lo hl_img_hi hl_got_guard hl_guard hl_rt_consts hl_reg_globals hla_base A4L A4H];
unfold a4_straces, a4_rt_consts, A_TP, A_ERRNO, A_SB, A_SB_CELL, A_GOT_SB.
End Mq0.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QWxq_c1 QsjA Lib.GwApply QHnV Qsw7.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq1.

Import Stdlib.ZArith.ZArith Stdlib.Lists.List.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import QXup QWxq_c1 QsjA OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.
Import QHnV Qsw7. Local Ltac Stdlib.micromega.Lia.lia ::= QsRG.Mq0.mkr__lia_0. Local Ltac Stdlib.micromega.Lia.nia ::= QsRG.Mq0.mkr__nia_1.

Ltac fold_mkR :=
lazymatch goal with
| |- context [MS (TNode (TNode (TNode (TNode (TNode (TNode TEmpty (Some ?x31) TEmpty) (Some ?x15) TEmpty) (Some ?x7) (TNode TEmpty (Some ?x23) TEmpty)) (Some ?x3) (TNode (TNode TEmpty (Some ?x19) TEmpty) (Some ?x11) (TNode TEmpty (Some ?x27) TEmpty))) (Some ?x1) (TNode (TNode (TNode TEmpty (Some ?x17) TEmpty) (Some ?x9) (TNode TEmpty (Some ?x25) TEmpty)) (Some ?x5) (TNode (TNode TEmpty (Some ?x21) TEmpty) (Some ?x13) (TNode TEmpty (Some ?x29) TEmpty)))) None (TNode (TNode (TNode (TNode TEmpty (Some ?x16) TEmpty) (Some ?x8) (TNode TEmpty (Some ?x24) TEmpty)) (Some ?x4) (TNode (TNode TEmpty (Some ?x20) TEmpty) (Some ?x12) (TNode TEmpty (Some ?x28) TEmpty))) (Some ?x2) (TNode (TNode (TNode TEmpty (Some ?x18) TEmpty) (Some ?x10) (TNode TEmpty (Some ?x26) TEmpty)) (Some ?x6) (TNode (TNode TEmpty (Some ?x22) TEmpty) (Some ?x14) (TNode TEmpty (Some ?x30) TEmpty))))) ?F ?pc ?fc ?rv ?m ?ro] =>
change (TNode (TNode (TNode (TNode (TNode (TNode TEmpty (Some x31) TEmpty) (Some x15) TEmpty) (Some x7) (TNode TEmpty (Some x23) TEmpty)) (Some x3) (TNode (TNode TEmpty (Some x19) TEmpty) (Some x11) (TNode TEmpty (Some x27) TEmpty))) (Some x1) (TNode (TNode (TNode TEmpty (Some x17) TEmpty) (Some x9) (TNode TEmpty (Some x25) TEmpty)) (Some x5) (TNode (TNode TEmpty (Some x21) TEmpty) (Some x13) (TNode TEmpty (Some x29) TEmpty)))) None (TNode (TNode (TNode (TNode TEmpty (Some x16) TEmpty) (Some x8) (TNode TEmpty (Some x24) TEmpty)) (Some x4) (TNode (TNode TEmpty (Some x20) TEmpty) (Some x12) (TNode TEmpty (Some x28) TEmpty))) (Some x2) (TNode (TNode (TNode TEmpty (Some x18) TEmpty) (Some x10) (TNode TEmpty (Some x26) TEmpty)) (Some x6) (TNode (TNode TEmpty (Some x22) TEmpty) (Some x14) (TNode TEmpty (Some x30) TEmpty)))))
with (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
| |- _ => idtac
end.

Ltac if_lit :=
lazymatch goal with
| |- evt ?segs ?Q (MS ?R ?F (if ?c then ?a else ?b) ?fc ?rv ?m ?ro) =>
let v := eval vm_compute in c in change (if c then a else b) with (if v then a else b); cbv iota
end. Ltac mkr__if_lit_0 := lazymatch goal with
| |- evt ?segs ?Q (MS ?R ?F (if ?c then ?a else ?b) ?fc ?rv ?m ?ro) =>
let v := eval vm_compute in c in change (if c then a else b) with (if v then a else b); cbv iota
end.

Ltac jt_eval :=
match goal with |- context [sext 64 (bv_extract 0 32 (le_bytes_to_word ?bs))] =>
let v := eval vm_compute in (bv_unsigned (sext 64 (bv_extract 0 32 (le_bytes_to_word bs)))) in
replace (sext 64 (bv_extract 0 32 (le_bytes_to_word bs))) with (Z_to_bv 64 v) by (apply bv_eq; vm_compute; reflexivity) end.
End Mq1.
From Stdlib Require NArith Bool Permutation.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Lib.CodeAt QZDE QEpW QRjH.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq2.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool Stdlib.Sorting.Permutation.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import QXup QWxq_c1 OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.CodeAt QZDE QEpW.
Import QRjH.
Import QHnV QCcH.
Import Qhd4.
Import ListNotations. Local Ltac Stdlib.micromega.Lia.lia ::= QsRG.Mq0.mkr__lia_0. Local Ltac Stdlib.micromega.Lia.nia ::= QsRG.Mq0.mkr__nia_1. Local Ltac OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.zs_idioms ::= OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.mkr__zs_idioms_3. Local Ltac OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.zs_idioms_in H ::= OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.mkr__zs_idioms_in_4 H. Local Ltac OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.zs_wrap e ::= OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.mkr__zs_wrap_1 e. Local Ltac OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.zs_wrap_in e H ::= OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.mkr__zs_wrap_in_2 e H.
Open Scope Z_scope.
Import Q6q3.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

Section Stmts.
Variable L : heap_layout_A.
Variable HIx : heap_iface_A L.
Notation segs := (hl_segs L).
Notation errno_a := (hl_tp L - 164).
Notation fr_ivs := (QZsi.fr_ivs L).
Notation uw_pre := (QZsi.uw_pre L).
Notation uw_ok := (QZsi.uw_ok L).

Definition malloc_nf_stmt : Prop :=
forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (c : config) (T : TSet)
(A : ASA L HIx) (LB LM : list blk) (FR : list frame) (B : bud) (n lo : Z) (errv : word) (u : uwd),
HEAPA L HIx A LB LM FR B m c ->
stk segs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - hl_stack_A L ->
bv_unsigned sp mod 16 = 0 -> bv_unsigned sp < hiA_top L HIx + 64 ->
rw_cells segs m errno_a [C4 errv] ->
tp = Z_to_bv 64 (hl_tp L) ->
a0 = Z_to_bv 64 n -> 1 <= n < 2^40 ->
uw_pre (hiA_top L HIx) m (bv_unsigned sp) (bv_unsigned s0) u -> uw_ok (hl_malloc L) ra u ->
16 * n + 512 <= bB B -> uw_cost u <= bD B ->
(forall ms' m' c' A' (r : Z) (errv' : word),
ret_state (hla_base L) ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (Z_to_bv 64 r) m' ms' ->
model_vm_only (cfg_model c) (cfg_model c') ->
stk segs m' lo (bv_unsigned sp) ->
heap_pres (hla_base L) (LB ++ LM ++ fr_ivs FR) (bv_unsigned sp) m m' ->
rw_cells segs m' errno_a [C4 errv'] ->
r <> 0 -> (exists junk, rw_cells segs m' r [CB (Z.to_nat n) junk]) ->
HEAPA L HIx A' ((r, n) :: LB) LM FR (charge B (16 * n + 512) (uw_cost u)) m' c' ->
AJ5of L (hiA_J L HIx) A' T c' ms') ->
AJ5of L (hiA_J L HIx) A T c
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 (hl_malloc L)) fc None m (seg_rom segs)).

Definition calloc_nf_stmt : Prop :=
forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (c : config) (T : TSet)
(A : ASA L HIx) (LB LM : list blk) (FR : list frame) (B : bud) (cnt sz lo : Z) (errv : word) (u : uwd),
HEAPA L HIx A LB LM FR B m c ->
stk segs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - hl_stack_A L ->
bv_unsigned sp mod 16 = 0 -> bv_unsigned sp < hiA_top L HIx + 64 ->
rw_cells segs m errno_a [C4 errv] ->
tp = Z_to_bv 64 (hl_tp L) ->
a0 = Z_to_bv 64 cnt -> a1 = Z_to_bv 64 sz -> 0 <= cnt < 2^64 -> 0 <= sz < 2^64 -> 1 <= cnt * sz < 2^40 ->
uw_pre (hiA_top L HIx) m (bv_unsigned sp) (bv_unsigned s0) u -> uw_ok (hl_calloc L) ra u ->
16 * (cnt * sz) + 512 <= bB B -> uw_cost u <= bD B ->
(forall ms' m' c' A' (r : Z) (errv' : word),
ret_state (hla_base L) ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (Z_to_bv 64 r) m' ms' ->
model_vm_only (cfg_model c) (cfg_model c') ->
stk segs m' lo (bv_unsigned sp) ->
heap_pres (hla_base L) (LB ++ LM ++ fr_ivs FR) (bv_unsigned sp) m m' ->
rw_cells segs m' errno_a [C4 errv'] ->
r <> 0 -> rw_cells segs m' r [CB (Z.to_nat (cnt * sz)) (repeat (Z_to_bv 8 0) (Z.to_nat (cnt * sz)))] ->
HEAPA L HIx A' ((r, cnt * sz) :: LB) LM FR (charge B (16 * (cnt * sz) + 512) (uw_cost u)) m' c' ->
AJ5of L (hiA_J L HIx) A' T c' ms') ->
AJ5of L (hiA_J L HIx) A T c
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 (hl_calloc L)) fc None m (seg_rom segs)).

Definition strdup_nf_stmt : Prop :=
forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (c : config) (T : TSet)
(A : ASA L HIx) (LB LM : list blk) (FR : list frame) (B : bud) (src ab nb lo : Z) (str : list byte) (errv : word) (u : uwd),
HEAPA L HIx A LB LM FR B m c ->
In (ab, nb) LB -> ab <= src -> src + Z.of_nat (length str) + 1 <= ab + nb ->
bytes_at segs m src (str ++ [Z_to_bv 8 0]) -> ~ In (Z_to_bv 8 0) str -> Z.of_nat (length str) + 1 < 2^32 ->
stk segs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - hl_stack_A L ->
bv_unsigned sp mod 16 = 0 -> bv_unsigned sp < hiA_top L HIx + 64 ->
rw_cells segs m errno_a [C4 errv] ->
tp = Z_to_bv 64 (hl_tp L) ->
a0 = Z_to_bv 64 src ->
uw_pre (hiA_top L HIx) m (bv_unsigned sp) (bv_unsigned s0) u -> uw_ok (hl_strdup L) ra u ->
16 * (Z.of_nat (length str) + 1) + 512 <= bB B -> uw_cost u <= bD B ->
(forall ms' m' c' A' (r : Z) (errv' : word),
ret_state (hla_base L) ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (Z_to_bv 64 r) m' ms' ->
model_vm_only (cfg_model c) (cfg_model c') ->
stk segs m' lo (bv_unsigned sp) ->
heap_pres (hla_base L) (LB ++ LM ++ fr_ivs FR) (bv_unsigned sp) m m' ->
rw_cells segs m' errno_a [C4 errv'] ->
r <> 0 -> bytes_at segs m' r (str ++ [Z_to_bv 8 0]) ->
HEAPA L HIx A' ((r, Z.of_nat (length str) + 1) :: LB) LM FR (charge B (16 * (Z.of_nat (length str) + 1) + 512) (uw_cost u)) m' c' ->
AJ5of L (hiA_J L HIx) A' T c' ms') ->
AJ5of L (hiA_J L HIx) A T c
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 (hl_strdup L)) fc None m (seg_rom segs)).
End Stmts.

Section Inst.
Variable L : heap_layout_A.
Variable H6 : QZsi.heap_iface_A L.

Local Ltac close_link HP' uu :=
apply (heapa5_enter L H6 _ _ _ _ _ _ _ _ HP');
unfold blink, charge, QZsi.charge, QZsi.chargeQ in *; cbn [bB bD QZsi.bB QZsi.bD QZsi.bN bM QZsi.bM QZsi.bQ] in *;
pose proof (uw_cost_nonneg5 uu); lia.

Lemma malloc_nf_v6 : malloc_nf_stmt L (hi5_of_v6 L H6).
Proof.
unfold malloc_nf_stmt. intros until u. intros HP ST LO LOS SPA HT ERR TP A0 N UW UWK BB BD K HGP.
destruct (heapa5_exit L H6 _ _ _ _ _ _ _ HP) as (B6 & HP6 & LK). pose proof LK as LK'. unfold blink in LK'.
assert (GP : gp = Z_to_bv 64 (hl_gp L)) by exact HGP.
pose proof (acost_le5 n ltac:(lia)) as AC.
eapply (QZsi.hiA_malloc L H6) with (B := B6) (n := n) (u := u) (errv := errv) (lo := lo);
[ exact HP6 | exact ST | exact LO | exact LOS | exact SPA | exact HT | exact ERR | exact TP | exact GP | exact A0
| lia | exact UW | exact UWK | lia | lia | lia | first [lia | nia] | ].
intros ms' m' c' A' r errv' RS VM ST' HPR ERR' Hr BLK HP'.
eapply (K ms' m' c' A' r errv' RS VM ST' HPR ERR' Hr BLK).
- close_link HP' u.
- destruct RS as (?&?&?&?&?&?&?&?&?&?&?&?&?&?&->); exact HGP.
Qed.

Lemma strdup_nf_v6 : strdup_nf_stmt L (hi5_of_v6 L H6).
Proof.
unfold strdup_nf_stmt. intros until u. intros HP HIN LE1 LE2 BYTES NOZ LEN ST LO LOS SPA HT ERR TP A0 UW UWK BB BD K HGP.
destruct (heapa5_exit L H6 _ _ _ _ _ _ _ HP) as (B6 & HP6 & LK). pose proof LK as LK'. unfold blink in LK'.
assert (GP : gp = Z_to_bv 64 (hl_gp L)) by exact HGP.
pose proof (acost_le5 (Z.of_nat (length str) + 1) ltac:(lia)) as AC.
eapply (QZsi.hiA_strdup L H6) with (B := B6) (src := src) (ab := ab) (nb := nb) (str := str) (u := u) (errv := errv) (lo := lo);
[ exact HP6 | exact HIN | exact LE1 | exact LE2 | exact BYTES | exact NOZ | lia | exact ST | exact LO | exact LOS | exact SPA | exact HT | exact ERR
| exact TP | exact GP | exact A0 | exact UW | exact UWK | lia | lia | lia | first [lia | nia] | ].
intros ms' m' c' A' r errv' RS VM ST' HPR ERR' Hr BYTES' HP'.
eapply (K ms' m' c' A' r errv' RS VM ST' HPR ERR' Hr BYTES').
- close_link HP' u.
- destruct RS as (?&?&?&?&?&?&?&?&?&?&?&?&?&?&->); exact HGP.
Qed.
End Inst.
End RC__1.
End Mq2.
From LinuxProcessSemantics.LinuxProcessSem Require Fs Monad Specs.
From LinuxProcessSemantics.LinuxProcessSem.Sys Require Uapi.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QsRG Q9ox Qnhz QSpR QZsi.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq3.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.LinuxProcessSem.Sys.Uapi.
Import QsRG.Mq0 Q9ox.Mq0 QRjH.

Import QCcH.
Import QZsi Qhd4.Mq1.
Import ListNotations. Local Ltac OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.zs_idioms ::= OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.mkr__zs_idioms_3. Local Ltac OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.zs_idioms_in H ::= OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.mkr__zs_idioms_in_4 H. Local Ltac OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.zs_wrap e ::= OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.mkr__zs_wrap_1 e. Local Ltac OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.zs_wrap_in e H ::= OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.mkr__zs_wrap_in_2 e H.
Open Scope Z_scope.

Module LMg := QZDE.

Section GetrandomT.
Context {fF : FPF} {fC : FPC}.
Variable segs : list Segment.
Variable J : aj_base segs.
Variable wit : TSet -> Prop.

Definition aj_getrandom_tagged_stmt : Prop :=
forall regs (pc : word) mem rom c buf len (X : TSet) (Kf : machine_state -> TSet),
CK J c -> getr regs 17 = Z_to_bv 64 278 -> getr regs 10 = Z_to_bv 64 buf -> getr regs 11 = Z_to_bv 64 len ->
(getr regs 12 = Z_to_bv 64 0 \/ getr regs 12 = Z_to_bv 64 GRND_NONBLOCK) ->
1 <= len <= 256 -> buf + len <= TASK_SIZE -> LMg.wr_at segs mem buf len ->
(wit X -> exists bs, Z.of_nat (length bs) = len /\
wit (Kf (advance_past_svc (apply_effect (epend regs pc mem rom (getr regs 17))
(mkEffect (len_word bs) [(Z_to_bv 64 buf, bs)] []))))) ->
(forall bs c', Z.of_nat (length bs) = len -> CNEXT J c c' ->
model_vm_only (cfg_model c) (cfg_model c') ->
AJ J (Kf (advance_past_svc (apply_effect (epend regs pc mem rom (getr regs 17)) (mkEffect (len_word bs) [(Z_to_bv 64 buf, bs)] []))))
c' (advance_past_svc (apply_effect (epend regs pc mem rom (getr regs 17)) (mkEffect (len_word bs) [(Z_to_bv 64 buf, bs)] [])))) ->
AJ J X c (epend regs pc mem rom (getr regs 17)).

Lemma aj_getrandom_tagged_w : aj_getrandom_tagged_stmt -> forall regs (pc : word) mem rom c buf len (X : TSet) (Kf : machine_state -> TSet),
CK J c -> getr regs 17 = Z_to_bv 64 278 -> getr regs 10 = Z_to_bv 64 buf -> getr regs 11 = Z_to_bv 64 len ->
(getr regs 12 = Z_to_bv 64 0 \/ getr regs 12 = Z_to_bv 64 GRND_NONBLOCK) ->
1 <= len <= 256 -> buf + len <= TASK_SIZE -> LMg.wr_at segs mem buf len ->
(wit X -> exists bs, Z.of_nat (length bs) = len /\
wit (Kf (mkst (regupd regs 10 (len_word bs)) (v_addi pc 4) (Qnhz.Mq0.wbytes mem (Z_to_bv 64 buf) bs) rom))) ->
(forall bs c', Z.of_nat (length bs) = len -> CNEXT J c c' ->
model_vm_only (cfg_model c) (cfg_model c') ->
AJ J (Kf (mkst (regupd regs 10 (len_word bs)) (v_addi pc 4) (Qnhz.Mq0.wbytes mem (Z_to_bv 64 buf) bs) rom))
c' (mkst (regupd regs 10 (len_word bs)) (v_addi pc 4) (Qnhz.Mq0.wbytes mem (Z_to_bv 64 buf) bs) rom)) ->
AJ J X c (epend regs pc mem rom (getr regs 17)).
Proof.
intros SYS regs pc mem rom c buf len X Kf HCK H17 H10 H11 H12 Hlen Htop Hwr HW HK.
apply (SYS regs pc mem rom c buf len X Kf HCK H17 H10 H11 H12 Hlen Htop Hwr).
- intros HX. destruct (HW HX) as (bs & Hbs & Hw). exists bs. split; [exact Hbs|]. rewrite QSpR.Mq2.adv_write1_epend. exact Hw.
- intros bs c' Hbs HN VM. rewrite QSpR.Mq2.adv_write1_epend. exact (HK bs c' Hbs HN VM).
Qed.

End GetrandomT.
End Mq3.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QbFI.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq4.

Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import QXup.
Import QCcH Q0Ek.
Import Qhd4.
Import QbFI QGcC.
Import Q6q3.
Import ListNotations. Local Ltac OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.zs_idioms ::= OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.mkr__zs_idioms_3. Local Ltac OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.zs_idioms_in H ::= OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.mkr__zs_idioms_in_4 H. Local Ltac OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.zs_wrap e ::= OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.mkr__zs_wrap_1 e. Local Ltac OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.zs_wrap_in e H ::= OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.mkr__zs_wrap_in_2 e H.
Open Scope Z_scope.

Definition asegs_wx : True := I.

Section RC__1. Context {RC__ : Q6q3.RunConsts}.

Definition A_TP : Z := 0x625520.
Definition A_ERRNO : Z := 0x625520 - 164.
Definition A_SB : Z := 0x7fff8000.

Definition A_HMB : Z := 0x10007fff8000.
Definition app_mem (s n : Z) : Prop := 0 <= s /\ ((s + n + 8 <= A_SB) \/ (A_HMB <= s /\ s + n + 8 <= 2^47)).
Definition A_GOT_SB : Z := 0xe81b8.
Definition A_SB_CELL : Z := 0xf21b8.

Definition a4_client_static (a : Z) : Prop :=
(0xec920 <= a < 0xeeb00)
\/ (0xeeb08 <= a < 0xeeb58)
\/ (0x184058 <= a < 0x184068)
\/ (0x614800 <= a < 0x625450)
\/ (0x625450 <= a < 0x646940
/\ ~ (0x62547c <= a < 0x625480)
/\ ~ (0x625510 <= a < 0x625518)
/\ ~ (0x6254c8 <= a < 0x6254d0)
/\ ~ (0x625518 <= a < 0x625558)
/\ ~ (0x645560 <= a < 0x645568)
/\ ~ (0x6457b0 <= a < 0x645818)
/\ ~ (0x6458a0 <= a < 0x645c48)).

Definition a4_volatile (a : Z) : Prop := (0xec980 <= a < 0xec984) \/ (0xed020 <= a < 0xed028).

Definition A4H : heap_layout :=
{| hl_segs := asegs;
hl_malloc := 0x636a0; hl_free := 0x6369c; hl_calloc := 0x636a4; hl_realloc := 0x636a8;
hl_malloc2 := 0xd0cf4; hl_free2 := 0xd0368;
hl_tp := A_TP;
hl_got_guard := 0xe8f90; hl_guard := 0x645560; hl_auxv := 0x6457b8; hl_libc := 0x6457b0; hl_volatile := a4_volatile;
hl_stack := 8256;
hl_client_static := a4_client_static;
hl_scratch := fun a => A_TP - 164 <= a < A_TP - 160;
hl_consts := [];
hl_img_lo := 0x10000; hl_img_hi := 0x647000;
hl_static_in_img := ltac:(unfold a4_client_static; cbn; intros; lia);
hl_img_range := ltac:(unfold alloc_ceiling, sp_window_lo, stack_max_size; lia);
hl_scratch_in_img := ltac:(unfold A_TP; cbn; intros; lia);
hl_scratch_not_static := ltac:(unfold a4_client_static, A_TP; cbn; intros; lia);
hl_consts_ok := ltac:(cbn; intros c a []) |}.

Definition a4_rt_consts : list (Z * list byte) :=
[ (0xe8d28, le8 (Z_to_bv 64 0xf2e99));
(0xf2e99, [Z_to_bv 8 1]);
(0xf2e98, [Z_to_bv 8 1]);
(0xea1d0, le8 (Z_to_bv 64 0xdde14));
(0xea1c8, le8 (Z_to_bv 64 0xdda10));
(0xe81a8, le8 (Z_to_bv 64 0x183ce8));
(0xea028, le8 (Z_to_bv 64 0xde074));
(0x183de3, [Z_to_bv 8 1]);

(0xe81c0, le8 (Z_to_bv 64 0xf2ea8));
(0xf2ea8, le8 (Z_to_bv 64 0));
(0xe81c8, le8 (Z_to_bv 64 0xf2eb0));
(0xf2eb0, le8 (Z_to_bv 64 0));
(0xe81d0, le8 (Z_to_bv 64 0xf2ea0));
(0xf2ea0, le8 (Z_to_bv 64 0x7fffffffffff));
(0xea0a0, le8 (Z_to_bv 64 0xd5f20));
(0xea0a8, le8 (Z_to_bv 64 0xdb6c8));
(0x183d3c, [Z_to_bv 8 1]);
(0x646db8, le4 (Z_to_bv 64 0));

(0x183ddd, [Z_to_bv 8 0]);
(0x183de2, [Z_to_bv 8 1]);
(0xe81b0, le8 (Z_to_bv 64 0xef9b8));
(0xef9d5, [Z_to_bv 8 1]);
(0xea1a0, le8 (Z_to_bv 64 0xdceac));
(0xea150, le8 (Z_to_bv 64 0xcf4a0));

(0xe8ea8, le8 (Z_to_bv 64 0xa4110));
(0xeeb00, le8 (Z_to_bv 64 1));
(0xefa70, le8 (Z_to_bv 64 0));
(0xef9d0, le4 (Z_to_bv 64 1));
(0xf1a1c, [Z_to_bv 8 1]);
(0x183d60, le8 (Z_to_bv 64 0xffffffffffffffff));

(0xe8e20, le8 (Z_to_bv 64 0xe80b0));
(0xe80b0, le8 (Z_to_bv 64 0xecd40));
(0xe8e28, le8 (Z_to_bv 64 0x0));
(0xea078, le8 (Z_to_bv 64 0xe3934));
(0xe8fc0, le8 (Z_to_bv 64 0xe4ac8) ++ le8 (Z_to_bv 64 0xe4ab8));
(0xe4ab8, le8 (Z_to_bv 64 0x9b3cc) ++ le8 (Z_to_bv 64 0x3e10c));
(0xe8188, le8 (Z_to_bv 64 0xcec58) ++ le8 (Z_to_bv 64 0x0));
(0xea020, le8 (Z_to_bv 64 0xea020));
(0xe8198, le8 (Z_to_bv 64 0x181c60) ++ le8 (Z_to_bv 64 0xea208) ++ le8 (Z_to_bv 64 0x183ce8) ++ le8 (Z_to_bv 64 0xef9b8) ++ le8 (Z_to_bv 64 0xf21b8) ++ le8 (Z_to_bv 64 0xf2ea8) ++ le8 (Z_to_bv 64 0xf2eb0) ++ le8 (Z_to_bv 64 0xf2ea0) ++ le8 (Z_to_bv 64 0xea1d0));
(0xe8ec0, le8 (Z_to_bv 64 0xed040) ++ le8 (Z_to_bv 64 0xeeb00));

(0xe8e58, le8 (Z_to_bv 64 0x9f854));
(0xe8e88, le8 (Z_to_bv 64 0x93a24));

(0x183de5, [Z_to_bv 8 1]);
(0xea050, le8 (Z_to_bv 64 0xddf20));
(0xe8e38, le8 (Z_to_bv 64 0x9dd50));
(0xe8e40, le8 (Z_to_bv 64 0x9e4a0));
(0xe8e48, le8 (Z_to_bv 64 0x9e8d8));
(0xe8e68, le8 (Z_to_bv 64 0x9f8e4));
(0xe8e98, le8 (Z_to_bv 64 0xa6060));
(0xe8ea0, le8 (Z_to_bv 64 0xa62ec));
(0xe8eb0, le8 (Z_to_bv 64 0xa53f4));
(0xe8e60, le8 (Z_to_bv 64 0x9f85c));
(0xe8e70, le8 (Z_to_bv 64 0xa0a78));
(0xe8e78, le8 (Z_to_bv 64 0xec940));

(0xe8050, le8 (Z_to_bv 64 0x1499c));
(0xe4ec8, le8 (Z_to_bv 64 0x9c508));
(0xe4ed0, le8 (Z_to_bv 64 0x9c600));
(0xe4ed8, le8 (Z_to_bv 64 0x9c60c));
(0xe4ee0, le8 (Z_to_bv 64 0x9c878));
(0xe4ee8, le8 (Z_to_bv 64 0x9cd50));
(0xe4ef0, le8 (Z_to_bv 64 0x9d200));

(0xe8e50, le8 (Z_to_bv 64 0x9edbc));
(0xe81d8, le8 (Z_to_bv 64 0xea1d0));
(0xe8e80, le8 (Z_to_bv 64 0x93680)) ].

Definition a4_straces : list (Z * Z * option Z) :=
[ (0x636a4, 0x9b424, None);  (0x636a0, 0x9b470, None);  (0x6369c, 0x9b4a8, None);  (0x636a4, 0xa4170, None);
(0x636a4, 0xa41b8, None);  (0x6369c, 0xa4274, None);  (0x636a4, 0xa4380, None);  (0x636a4, 0xa43c8, None);
(0x6369c, 0xa4570, None);  (0x6369c, 0xa466c, None);  (0x6369c, 0xa4674, None);  (0x636a4, 0x932fc, None);
(0x636a4, 0x93310, None);  (0x636a0, 0x91a24, None);  (0x636a0, 0x91a78, None);  (0x6369c, 0x91a9c, None);
(0x6369c, 0x91bcc, None);  (0x636a0, 0x91d04, None);  (0x6369c, 0x91d98, None);  (0x6369c, 0x94e48, (Some 0x9385c));
(0x636a0, 0x9d38c, (Some 0x9385c));  (0x636a0, 0x9f3fc, (Some 0x9385c));  (0x636a0, 0x9f57c, (Some 0x9385c));  (0x636a0, 0xa00d4, (Some 0x9385c));
(0x636a0, 0xa0770, (Some 0x9385c));  (0x636a0, 0x9d850, None);  (0x6369c, 0x9d47c, None);  (0x4fdd8, 0x9f654, None);
(0x6369c, 0x9f6d0, None);  (0x6369c, 0x9f6d8, None);  (0x6369c, 0xa0850, None);  (0x4fdd8, 0x9d770, None);
(0x636a8, 0x9b690, None);  (0x636a8, 0x9ba84, None);  (0x6369c, 0x9bd30, None);  (0x6369c, 0x9c11c, None);
(0x6369c, 0x9c3d4, None);  (0x6369c, 0x9d474, None);  (0x6369c, 0x9c100, None);  (0x6369c, 0x9c124, None);
(0x6369c, 0x9c05c, None);  (0x6369c, 0x9c0d0, None);  (0x6369c, 0x9c2e8, None);  (0x6369c, 0x9c358, None);
(0x6369c, 0x9c37c, None);  (0x6369c, 0x9c3b8, None);  (0x6369c, 0x9c3dc, None);  (0x6369c, 0x9d5b0, None);
(0x636a0, 0xa22a4, None);  (0x636a0, 0xa2308, None);  (0x6369c, 0xa2330, None);  (0x6369c, 0xa2478, None);
(0x636a8, 0xa2694, None);  (0x636a8, 0xa28b0, None);  (0x6369c, 0xa4c58, None);  (0x6369c, 0x935bc, None);
(0x4fdd8, 0x975cc, (Some 0x9385c));  (0x6369c, 0x933d8, None);  (0x6369c, 0x933e0, None);  (0x6369c, 0x93938, None);
(0x6369c, 0x93940, None);  (0x636a0, 0x9f3fc, None);  (0x636a0, 0xa00d4, None) ].

Definition A4L : heap_layout_A :=
{| hla_base := A4H;
hl_sb := A_SB; hl_sb_cell := A_SB_CELL; hl_got_sb := A_GOT_SB;
hl_uar_cell := 0xf21c0; hl_got_uar := 0xe8210;
hl_stack_malloc := fun k => if Z.eqb k 0 then 0x4a9bc else if Z.eqb k 1 then 0x4ab30 else if Z.eqb k 2 then 0x4acc0 else if Z.eqb k 3 then 0x4ae5c else 0;
hl_strdup := 0x4fdd8;
hl_stack_A := 4096;
hl_gp := 0x10800;
hl_pristine := [(0xe4a98, 0xe8f90); (0xe8f98, 0xe9010); (0xea020, 0xea210)];
hl_globals := [];
hl_reg_globals := tokA_reg_globals;
hl_straces := a4_straces;
hl_rt_consts := a4_rt_consts;
hl_sb_range := ltac:(unfold A_SB; lia) |}.

Definition A4F : fnaddrs :=
{| fn_obj_to_json_string := 0x9c878;
fn_arr_to_json_string := 0x9cd50;
fn_bool_to_json_string := 0x9c508;
fn_dbl_to_json_string := 0x9c600;
fn_int_to_json_string := 0x9c60c;
fn_str_to_json_string := 0x9d200;
fn_ud_to_json_string := 0x9f7cc;
fn_free_userdata := 0x9f854;
fn_lh_entry_free := 0x9d528;
fn_lh_char_hash := 0xa2c54;
fn_lh_char_equal := 0xa4110;
fn_arr_entry_free := 0xa08a8 |}.

End RC__1.

Ltac a4l :=
cbn [hl_segs hl_stack hl_stack_A hl_tp hl_calloc hl_malloc hl_free hl_realloc hl_malloc2 hl_free2 hl_straces hl_strdup hl_stack_malloc
hl_sb hl_sb_cell hl_got_sb hl_uar_cell hl_got_uar hl_img_lo hl_img_hi hl_got_guard hl_guard hl_rt_consts hl_reg_globals hla_base A4L A4H] in *;
unfold a4_straces, a4_rt_consts, A_TP, A_ERRNO, A_SB, A_SB_CELL, A_GOT_SB in *.
Ltac a4l_goal :=
cbn [hl_segs hl_stack hl_stack_A hl_tp hl_calloc hl_malloc hl_free hl_realloc hl_malloc2 hl_free2 hl_straces hl_strdup hl_stack_malloc
hl_sb hl_sb_cell hl_got_sb hl_uar_cell hl_got_uar hl_img_lo hl_img_hi hl_got_guard hl_guard hl_rt_consts hl_reg_globals hla_base A4L A4H];
unfold a4_straces, a4_rt_consts, A_TP, A_ERRNO, A_SB, A_SB_CELL, A_GOT_SB.
End Mq4.

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QXup.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QXup. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QWxq_c1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QWxq_c1. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib Require Import CodeAt. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QZDE.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QZDE. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QEpW.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QEpW. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QbrW.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QbrW. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Lib.GwApply.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qhd4.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qhd4.
Import ListNotations. Local Ltac Stdlib.micromega.Lia.lia ::= QsRG.Mq0.mkr__lia_0. Local Ltac Stdlib.micromega.Lia.nia ::= QsRG.Mq0.mkr__nia_1. Local Ltac OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.zs_idioms ::= OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.mkr__zs_idioms_3. Local Ltac OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.zs_idioms_in H ::= OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.mkr__zs_idioms_in_4 H. Local Ltac OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.zs_wrap e ::= OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.mkr__zs_wrap_1 e. Local Ltac OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.zs_wrap_in e H ::= OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.mkr__zs_wrap_in_2 e H.
Open Scope Z_scope.

Definition shadow_cells (n : Z) : list cell := map C1 (shadow_bytes n).

Lemma cells_bytes_map_C1 : forall bs, cells_bytes (map C1 bs) = bs.
Proof. induction bs as [|b bs IH]; cbn; [reflexivity | now rewrite IH]. Qed.

Lemma cells_wf_map_C1 : forall bs, cells_wf (map C1 bs).
Proof. induction bs as [|b bs IH]; cbn; [exact I | split; [exact I | exact IH]]. Qed.

Section WithSegs.
Variable segs : list Segment.

Lemma shadow_ro_cells : forall m A n,
bytes_at segs m A (shadow_bytes n) -> ro_cells segs m A (shadow_cells n).
Proof.
intros m A n Hb. split; [apply cells_wf_map_C1|]. unfold shadow_cells. rewrite cells_bytes_map_C1. exact Hb.
Qed.

Lemma Zdiv8_sub : forall n k, (n - 8 * k) / 8 = n / 8 - k.
Proof.
intros n k. replace (n - 8 * k) with (n + (- k) * 8) by lia.
rewrite Z.div_add by lia. lia.
Qed.

Lemma Zmod8_sub : forall n k, (n - 8 * k) mod 8 = n mod 8.
Proof.
intros n k. replace (n - 8 * k) with (n + (- k) * 8) by lia.
rewrite Z.mod_add by lia. reflexivity.
Qed.

Lemma shadow_bytes_split : forall n k, 0 <= k -> 8 * k <= n ->
shadow_bytes n = repeat (Z_to_bv 8 0) (Z.to_nat k) ++ shadow_bytes (n - 8 * k).
Proof.
intros n k Hk Hkn. unfold shadow_bytes. rewrite Zdiv8_sub, Zmod8_sub.
rewrite app_assoc. f_equal.
rewrite <- repeat_app. f_equal.
assert (k <= n / 8) by (apply Z.div_le_lower_bound; lia). lia.
Qed.

Lemma shadow_skip : forall m A n k, 0 <= k -> 8 * k <= n ->
bytes_at segs m A (shadow_bytes n) ->
bytes_at segs m (A + k) (shadow_bytes (n - 8 * k)).
Proof.
intros m A n k Hk Hkn Hb.
rewrite (shadow_bytes_split n k Hk Hkn) in Hb.
apply bytes_at_app in Hb. destruct Hb as [_ Hb].
rewrite repeat_length, Z2Nat.id in Hb by lia. exact Hb.
Qed.

Lemma shadow_head0 : forall m A n, 8 <= n ->
bytes_at segs m A (shadow_bytes n) -> ro_cells segs m A [C1 (Z_to_bv 8 0)].
Proof.
intros m A n Hn Hb.
rewrite (shadow_bytes_split n 1) in Hb by lia. cbn [Z.to_nat Pos.to_nat repeat app] in Hb.
change (Z_to_bv 8 0 :: shadow_bytes (n - 8 * 1)) with ([Z_to_bv 8 0] ++ shadow_bytes (n - 8 * 1)) in Hb.
apply bytes_at_app in Hb. destruct Hb as [Hb _].
split; [cbn; split; exact I | cbn [cells_bytes cbytes app]; exact Hb].
Qed.

Lemma shadow_tail : forall m A n, 0 <= n -> n mod 8 <> 0 ->
bytes_at segs m A (shadow_bytes n) -> ro_cells segs m (A + n / 8) [C1 (Z_to_bv 8 (n mod 8))].
Proof.
intros m A n Hn Hm Hb.
pose proof (shadow_skip m A n (n / 8) ltac:(apply Z.div_pos; lia) ltac:(apply Z.mul_div_le; lia) Hb) as Hb'.
unfold shadow_bytes in Hb'. rewrite Zdiv8_sub, Zmod8_sub, Z.sub_diag in Hb'. cbn [Z.to_nat repeat app] in Hb'.
destruct (Z.eqb (n mod 8) 0) eqn:E; [apply Z.eqb_eq in E; lia|].
split; [cbn; split; exact I | cbn [cells_bytes cbytes app]; exact Hb'].
Qed.

Lemma shadow_at0 : forall m S n i, 0 <= i -> 8 * (i / 8) + 8 <= n ->
bytes_at segs m S (shadow_bytes n) -> ro_cells segs m (S + i / 8) [C1 (Z_to_bv 8 0)].
Proof.
intros m S n i Hi Hn Hb.
apply (shadow_head0 m (S + i / 8) (n - 8 * (i / 8))); [lia|].
apply shadow_skip; [apply Z.div_pos; lia | lia | exact Hb].
Qed.

End WithSegs.

Ltac sh_norm :=
repeat match goal with
| |- context [Z.shiftr (bv_unsigned (Z_to_bv 64 ?a)) 3] =>
rewrite (unsigned_lit a) by lia
| |- context [Z.shiftr ?a 3] =>
rewrite (Z.shiftr_div_pow2 a 3) by lia; change (2 ^ 3) with 8
end.

Lemma sxb_zero : sxb (Z_to_bv 8 0) = Z_to_bv 64 0.
Proof. apply bv_eq; vm_compute; reflexivity. Qed.
Lemma zxb_zero : zxb (Z_to_bv 8 0) = Z_to_bv 64 0.
Proof. apply bv_eq; vm_compute; reflexivity. Qed.

Ltac asan_chk0 :=
step;
step;
sh_norm;
step;
step;
first [ if_false | if_true ];
rewrite ?sxb_zero, ?zxb_zero.
