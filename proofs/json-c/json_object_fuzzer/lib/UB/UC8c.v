(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)

From Stdlib Require ZArith List Lia.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType State Run.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QXup.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UEQM.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QCcH Q0Ek Q6q3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq0.

Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import QXup.
Import UEQM.
Import QCcH Q0Ek.
Import Q6q3.
Open Scope Z_scope.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

Definition s4_client_static (a : Z) : Prop :=
0x62000 <= a < 0x99000
/\ ~ (0x97e90 <= a < 0x97ef8)
/\ ~ (0x97f78 <= a < 0x98320)
/\ ~ (0x659d0 <= a < 0x659d8)
/\ ~ (0x658d8 <= a < 0x658e0)
/\ ~ (0x66a30 <= a < 0x66a38)
/\ ~ (0x97e70 <= a < 0x97e78)
/\ ~ (0x77bf0 <= a < 0x77bf8)
/\ ~ (0x77b5c <= a < 0x77b60).

Definition s4_volatile (a : Z) : Prop := (0x66a40 <= a < 0x66a44) \/ (0x66f20 <= a < 0x66f28)
\/ (0x76fbc <= a < 0x770bc).

Definition S4L : heap_layout :=
{| hl_segs := rsegs;
hl_malloc := 0x521f4; hl_free := 0x520b4; hl_calloc := 0x51f7c; hl_realloc := 0x53d40; hl_malloc2 := 0x52e64; hl_free2 := 0x524d8;
hl_tp := 0x77c00;
hl_got_guard := 0x659d0; hl_guard := 0x97e70; hl_auxv := 0x97e98; hl_libc := 0x97e90; hl_volatile := s4_volatile;
hl_stack := 8256;
hl_client_static := s4_client_static;
hl_scratch := fun a => 0x77c00 - 164 <= a < 0x77c00 - 160;
hl_consts := [(0x658d8, le8 (Z_to_bv 64 0x66a30)); (0x66a30, le8 (Z_to_bv 64 0x12b12))];
hl_img_lo := 0x10000; hl_img_hi := 0x99000;
hl_static_in_img := ltac:(unfold s4_client_static; cbn; intros; lia);
hl_img_range := ltac:(unfold alloc_ceiling, sp_window_lo, stack_max_size; lia);
hl_scratch_in_img := ltac:(cbn; intros; lia);
hl_scratch_not_static := ltac:(unfold s4_client_static; cbn; intros; lia);
hl_consts_ok := ltac:(unfold s4_client_static; cbn; intros c a [<-|[<-|[]]]; cbn; rewrite ?length_le8; cbn; intros; lia) |}.

Definition S4F : fnaddrs :=
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
End Mq0.
