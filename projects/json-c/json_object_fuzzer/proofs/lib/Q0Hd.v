(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)

From Stdlib Require Import ZArith List Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QXup.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QXup.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QCcH.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QCcH. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q0Ek.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q0Ek.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q6q3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q6q3.
Import ListNotations.
Open Scope Z_scope.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

Definition gl (segs : list Segment) (e_malloc e_free e_calloc e_realloc e_malloc2 e_free2 TP GOTG GUARD AUXV LIBC : Z)
(VOL CS : Z -> Prop) (HEXGOT HEXPTR HEXCHARS IMG_LO IMG_HI : Z)
(H1 : forall a, CS a -> IMG_LO <= a < IMG_HI)
(H2 : 0 <= IMG_LO /\ IMG_HI <= alloc_ceiling)
(H3 : forall a, (TP - 164 <= a < TP - 160) -> IMG_LO <= a < IMG_HI)
(H4 : forall a, (TP - 164 <= a < TP - 160) -> ~ CS a)
(H5 : forall c a, In c [(HEXGOT, le8 (Z_to_bv 64 HEXPTR)); (HEXPTR, le8 (Z_to_bv 64 HEXCHARS))] -> fst c <= a < fst c + Z.of_nat (length (snd c)) ->
~ CS a /\ ~ (TP - 164 <= a < TP - 160) /\ IMG_LO <= a < IMG_HI) : heap_layout :=
{| hl_segs := segs;
hl_malloc := e_malloc; hl_free := e_free; hl_calloc := e_calloc; hl_realloc := e_realloc; hl_malloc2 := e_malloc2; hl_free2 := e_free2;
hl_tp := TP;
hl_got_guard := GOTG; hl_guard := GUARD; hl_auxv := AUXV; hl_libc := LIBC; hl_volatile := VOL;
hl_stack := 8256;
hl_client_static := CS;
hl_scratch := fun a => TP - 164 <= a < TP - 160;
hl_consts := [(HEXGOT, le8 (Z_to_bv 64 HEXPTR)); (HEXPTR, le8 (Z_to_bv 64 HEXCHARS))];
hl_img_lo := IMG_LO; hl_img_hi := IMG_HI;
hl_static_in_img := H1; hl_img_range := H2; hl_scratch_in_img := H3; hl_scratch_not_static := H4; hl_consts_ok := H5 |}.

Definition gl_range_ok (lo hi : Z) : Prop := (0 <= lo /\ hi <= alloc_ceiling)%Z.

Definition gf (e_fn_obj_to_json_string e_fn_arr_to_json_string e_fn_bool_to_json_string e_fn_dbl_to_json_string e_fn_int_to_json_string
e_fn_str_to_json_string e_fn_ud_to_json_string e_fn_free_userdata e_fn_lh_entry_free e_fn_lh_char_hash e_fn_lh_char_equal
e_fn_arr_entry_free : Z) : fnaddrs :=
{| fn_obj_to_json_string := e_fn_obj_to_json_string; fn_arr_to_json_string := e_fn_arr_to_json_string;
fn_bool_to_json_string := e_fn_bool_to_json_string; fn_dbl_to_json_string := e_fn_dbl_to_json_string;
fn_int_to_json_string := e_fn_int_to_json_string; fn_str_to_json_string := e_fn_str_to_json_string;
fn_ud_to_json_string := e_fn_ud_to_json_string; fn_free_userdata := e_fn_free_userdata; fn_lh_entry_free := e_fn_lh_entry_free;
fn_lh_char_hash := e_fn_lh_char_hash; fn_lh_char_equal := e_fn_lh_char_equal; fn_arr_entry_free := e_fn_arr_entry_free |}.
End RC__1.
