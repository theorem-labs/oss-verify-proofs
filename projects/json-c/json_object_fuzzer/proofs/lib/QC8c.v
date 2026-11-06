(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)

From Stdlib Require ZArith List Lia.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QXup QEQM QCcH Q0Ek Q6q3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq0.

Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import QXup.
Import QEQM.
Import QCcH Q0Ek.
Import Q6q3.
Open Scope Z_scope.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

Definition s4_client_static (a : Z) : Prop :=
0x60000 <= a < 0x97000
/\ ~ (0x96100 <= a < 0x96168)
/\ ~ (0x961e8 <= a < 0x96590)
/\ ~ (0x63e88 <= a < 0x63e90)
/\ ~ (0x63d90 <= a < 0x63d98)
/\ ~ (0x64ee8 <= a < 0x64ef0)
/\ ~ (0x960e0 <= a < 0x960e8)
/\ ~ (0x75e60 <= a < 0x75e68)
/\ ~ (0x75dcc <= a < 0x75dd0).

Definition s4_volatile (a : Z) : Prop := (0x64ef8 <= a < 0x64efc) \/ (0x65198 <= a < 0x651a0)
\/ (0x7522c <= a < 0x7532c).

Definition S4L : heap_layout :=
{| hl_segs := rsegs;
hl_malloc := 0x5046c; hl_free := 0x5032c; hl_calloc := 0x501f4; hl_realloc := 0x51fb8; hl_malloc2 := 0x510dc; hl_free2 := 0x50750;
hl_tp := 0x75e70;
hl_got_guard := 0x63e88; hl_guard := 0x960e0; hl_auxv := 0x96108; hl_libc := 0x96100; hl_volatile := s4_volatile;
hl_stack := 8256;
hl_client_static := s4_client_static;
hl_scratch := fun a => 0x75e70 - 164 <= a < 0x75e70 - 160;
hl_consts := [(0x63d90, le8 (Z_to_bv 64 0x64ee8)); (0x64ee8, le8 (Z_to_bv 64 0x12b1b))];
hl_img_lo := 0x10000; hl_img_hi := 0x97000;
hl_static_in_img := ltac:(unfold s4_client_static; cbn; intros; lia);
hl_img_range := ltac:(unfold alloc_ceiling, sp_window_lo, stack_max_size; lia);
hl_scratch_in_img := ltac:(cbn; intros; lia);
hl_scratch_not_static := ltac:(unfold s4_client_static; cbn; intros; lia);
hl_consts_ok := ltac:(unfold s4_client_static; cbn; intros c a [<-|[<-|[]]]; cbn; rewrite ?length_le8; cbn; intros; lia) |}.

Definition S4F : fnaddrs :=
{| fn_obj_to_json_string := 0x23a5c;
fn_arr_to_json_string := 0x23e00;
fn_bool_to_json_string := 0x23940;
fn_dbl_to_json_string := 0x239ec;
fn_int_to_json_string := 0x239f8;
fn_str_to_json_string := 0x2417c;
fn_ud_to_json_string := 0x24e64;
fn_free_userdata := 0x24eb8;
fn_lh_entry_free := 0x24330;
fn_lh_char_hash := 0x261f4;
fn_lh_char_equal := 0x268a4;
fn_arr_entry_free := 0x254e4 |}.

End RC__1.
End Mq0.

From Stdlib Require Import ZArith List Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QXup.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QXup.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qazd.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qazd.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QCcH.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QCcH. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q0Ek.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q0Ek.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q6q3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q6q3.
Open Scope Z_scope.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

Definition u4_client_static (a : Z) : Prop :=
0x62000 <= a < 0x99000
/\ ~ (0x97e90 <= a < 0x97ef8)
/\ ~ (0x97f78 <= a < 0x98320)
/\ ~ (0x659d0 <= a < 0x659d8)
/\ ~ (0x658d8 <= a < 0x658e0)
/\ ~ (0x66a30 <= a < 0x66a38)
/\ ~ (0x97e70 <= a < 0x97e78)
/\ ~ (0x77bf0 <= a < 0x77bf8)
/\ ~ (0x77b5c <= a < 0x77b60).

Definition u4_volatile (a : Z) : Prop := (0x66a40 <= a < 0x66a44) \/ (0x66f20 <= a < 0x66f28)
\/ (0x76fbc <= a < 0x770bc).

Definition U4L : heap_layout :=
{| hl_segs := usegs;
hl_malloc := 0x521f4; hl_free := 0x520b4; hl_calloc := 0x51f7c; hl_realloc := 0x53d40; hl_malloc2 := 0x52e64; hl_free2 := 0x524d8;
hl_tp := 0x77c00;
hl_got_guard := 0x659d0; hl_guard := 0x97e70; hl_auxv := 0x97e98; hl_libc := 0x97e90; hl_volatile := u4_volatile;
hl_stack := 8256;
hl_client_static := u4_client_static;
hl_scratch := fun a => 0x77c00 - 164 <= a < 0x77c00 - 160;
hl_consts := [(0x658d8, le8 (Z_to_bv 64 0x66a30)); (0x66a30, le8 (Z_to_bv 64 0x12b12))];
hl_img_lo := 0x10000; hl_img_hi := 0x99000;
hl_static_in_img := ltac:(unfold u4_client_static; cbn; intros; lia);
hl_img_range := ltac:(unfold alloc_ceiling, sp_window_lo, stack_max_size; lia);
hl_scratch_in_img := ltac:(cbn; intros; lia);
hl_scratch_not_static := ltac:(unfold u4_client_static; cbn; intros; lia);
hl_consts_ok := ltac:(unfold u4_client_static; cbn; intros c a [<-|[<-|[]]]; cbn; rewrite ?length_le8; cbn; intros; lia) |}.

Definition U4F : fnaddrs :=
{| fn_obj_to_json_string := 0x24ac0;
fn_arr_to_json_string := 0x24ed4;
fn_bool_to_json_string := 0x24984;
fn_dbl_to_json_string := 0x24a40;
fn_int_to_json_string := 0x24a4c;
fn_str_to_json_string := 0x252c4;
fn_ud_to_json_string := 0x26150;
fn_free_userdata := 0x261b4;
fn_lh_entry_free := 0x25470;
fn_lh_char_hash := 0x27844;
fn_lh_char_equal := 0x28314;
fn_arr_entry_free := 0x268b8 |}.

End RC__1.
