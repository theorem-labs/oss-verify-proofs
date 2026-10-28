(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout State Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.simdjson.fuzz_print_json.lib.Lib Require Import Tac Arr Bytes ITree Nodes Decode SysStep RegsEquiv Image.
From OssFuzzTheorems.Proofs.simdjson.fuzz_print_json.lib.U Require Export Layout.
From OssFuzzTheorems.Proofs.simdjson.fuzz_print_json.lib.P Require Import Str_tac Startup_glue.
From OssFuzzTheorems.Proofs.simdjson.fuzz_print_json.lib.U Require Import Pj_steps Pj_loc_defs Pj_loc_kit Pj_loc_get Pj_os_defs Pj_os_kit.
From OssFuzzTheorems.simdjson.fuzz_print_json.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.simdjson.fuzz_print_json.lib.Lib Require Import StoreFast.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.
Import ListNotations.
Open Scope bv_scope.

Theorem ios_dtor_proof : ios_dtor_stmt.
Proof.
  unfold ios_dtor_stmt. intros until j284. intros ST LO LOLO IOSF RO RO2 MI.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  assert (LO0 : (0 <= lo)%Z) by (destruct ST as [? _]; assumption).
  pose proof (munch_refl [(bv_unsigned sp - 48, bv_unsigned sp); (OS + 136, OS + 144)]%Z m) as MU.
  pose proof (wmono_refl usegs m) as WM.
  unfold ios_dtor_post.
  remember (OS + 136)%Z as IOS eqn:EIOS.
  replace (OS + 144)%Z with (IOS + 8)%Z in * by lia.
  unfold ios_cells in IOSF |- *.
  lstep.
  carve_frame 48%nat ST.
  do 12 lstep.
  if_false.
  do 2 lstep.
  if_true.
  lstep.
  lstep.
  takeZ IOSF 8%nat (IOS + 48)%Z P0. takeZ IOSF 1%nat (IOS + 56)%Z LOCM.
  eapply evt_cut.
  { eapply (locale_dtor_spec _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (IOS + 48)%Z); [exact LOCM | lia | assumption]. }
  intros ms' (a0' & a1' & ->).
  replace (ret_pc (Z_to_bv 64 0x812cc)) with (Z_to_bv 64 0x812cc) by (apply bv_eq; vm_compute; reflexivity).
  glueZ LOCM IOSF. glueZ P0 LOCM. rename P0 into IOSF.
  lstep.
  lstep.
  do 2 lstep. if_true. lstep.
  lstep.
  lstep.
  do 2 lstep. if_true. lstep.
  lstep.
  lstep.
  do 2 lstep. if_true. lstep.
  do 7 lstep.
  release_frame FR ST (bv_unsigned sp).
  do 3 lstep.
  if_true.
  lstep.
  sys_finish.
Qed.
