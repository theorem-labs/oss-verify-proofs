(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout State Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.simdjson.fuzz_print_json.lib.Lib Require Import Tac Arr Bytes ITree Nodes Decode SysStep RegsEquiv Image.
From OssFuzzTheorems.Proofs.simdjson.fuzz_print_json.lib.U Require Export Layout.
From OssFuzzTheorems.Proofs.simdjson.fuzz_print_json.lib.P Require Import Str_tac Startup_glue.
From OssFuzzTheorems.Proofs.simdjson.fuzz_print_json.lib.U Require Import F_memset Pj_steps Pj_loc_defs Pj_loc_kit Pj_loc_get Pj_loc_get0 Pj_os_defs Pj_os_kit.
From OssFuzzTheorems.simdjson.fuzz_print_json.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.simdjson.fuzz_print_json.lib.Lib Require Import StoreFast.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.
Import ListNotations.
Open Scope bv_scope.

Theorem os_ctor_proof : os_ctor_stmt.
Proof.
  unfold os_ctor_stmt. intros until junk. intros ST LO LOLO HI PL OSR RO RO2 GOTV GOT CAN NL LK MI.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  assert (LO0 : (0 <= lo)%Z) by (destruct ST as [? _]; assumption).
  pose proof (munch_refl [(bv_unsigned sp - 672, bv_unsigned sp); (OS, OS + 288); (0xed228, 0xee0d8)]%Z m) as MU.
  pose proof (wmono_refl usegs m) as WM.
  pose proof (munch_refl [(bv_unsigned sp - 672, bv_unsigned sp); (OS, OS + 288)]%Z m) as MUF.
  pose proof (wmono_refl usegs m) as WMF.
  apply (rw_cells_split_CB usegs _ _ [] 288 junk [] [8; 8; 48; 64; 8; 8; 4; 4; 8; 8; 4; 4; 8; 8; 80; 8; 4; 4]%nat) in OSR; [|reflexivity].
  cbn [mk_CB_cells app] in OSR. forget_junk OSR.
  carve_frame 64%nat ST.
  do 21 lstep.
  lstep.
  lazymatch type of MUF with munch ?W ?m0 ?m1 =>
    assert (PL1 : pj_locale m1) by (apply (pj_locale_transport W m0 m1 PL MUF WMF); cbv [disjoint_from fst snd]; repeat split; lia) end.
  clear MUF WMF PL.
  takeZ OSR 1%nat (OS + 8)%Z P0. takeZ OSR 1%nat (OS + 16)%Z LOCC.
  call_sp (locale_ctor_spec _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (OS + 8)%Z);
    [exact ST | lia | lia | lia | exact PL1 | exact LOCC | lia | exact GOT | exact CAN | exact NL | exact LK | assumption |].
  rename PC into ST. rename PC0 into LOCC. rename POST into LB.
  glueZ LOCC OSR. glueZ P0 LOCC. rename P0 into OSR.
  lazymatch type of OSR with rw_cells _ ?m1 _ _ =>
    pose proof (munch_refl [(bv_unsigned sp - 672, bv_unsigned sp); (OS, OS + 288)]%Z m1) as MUF; pose proof (wmono_refl usegs m1) as WMF end.
  do 3 lstep.
  lstep.
  takeZ OSR 2%nat (OS + 16)%Z P0. takeZ OSR 1%nat (OS + 64)%Z MS1.
  call_sp (memset_callZ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc _ (OS + 16) 0 48 _)%Z; [exact MS1 | assumption | lia | lia | lia | lia |].
  rename POST into MS1. change (Z.to_nat 48) with 48%nat in MS1. change (0 mod 256)%Z with 0%Z in MS1.
  retype MS1 [C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)].
  glueZ MS1 OSR. glueZ P0 MS1. rename P0 into OSR.
  do 13 lstep.
  carve_frame 16%nat ST.
  do 18 lstep.
  lstep.
  takeZ OSR 19%nat (OS + 192)%Z P0. takeZ OSR 1%nat (OS + 272)%Z MS2.
  call_sp (memset_callZ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc _ (OS + 192) 0 80 _)%Z; [exact MS2 | assumption | lia | lia | lia | lia |].
  rename POST into MS2. change (Z.to_nat 80) with 80%nat in MS2. change (0 mod 256)%Z with 0%Z in MS2.
  retype MS2 [C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0);
              C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)].
  glueZ MS2 OSR. glueZ P0 MS2. rename P0 into OSR.
  do 4 lstep.
  release_frame FR0 ST (bv_unsigned sp + -64)%Z.
  lstep.
  takeZ OSR 18%nat (OS + 184)%Z P0. takeZ OSR 1%nat (OS + 192)%Z LOC2. merge_at LOC2 0%nat 1%nat.
  lazymatch type of MUF with munch ?W ?m0 ?m1 =>
    assert (LB2 : LOCB m1) by (apply (LOCB_transport W m0 m1 LB MUF WMF); cbv [disjoint_from fst snd]; repeat split; lia) end.
  clear LB.
  call_sp (locale_ctor_specB _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (OS + 184)%Z);
    [exact ST | lia | lia | exact LB2 | exact LOC2 | lia | assumption |].
  rename PC into ST. rename PC0 into LOC2. rename POST into LB.
  glueZ LOC2 OSR. glueZ P0 LOC2. rename P0 into OSR.
  lazymatch type of OSR with rw_cells _ ?m1 _ _ =>
    clear MUF WMF; pose proof (munch_refl [(bv_unsigned sp - 672, bv_unsigned sp); (OS, OS + 288)]%Z m1) as MUF; pose proof (wmono_refl usegs m1) as WMF end.
  do 17 lstep.
  release_frame FR ST (bv_unsigned sp).
  replace (OS <? 1)%Z with false in OSR by (symmetry; apply Z.ltb_ge; lia). cbn [Z.b2z] in OSR.
  retype_at OSR 30%nat 1%nat [C4 (Z_to_bv 64 0xffffffff)].
  lazymatch type of MUF with munch ?W ?m0 ?m1 =>
    assert (LBF : LOCB m1) by (apply (LOCB_transport W m0 m1 LB MUF WMF); cbv [disjoint_from fst snd]; repeat split; lia) end.
  clear MUF WMF.
  assert (OSF : OSFRESH m0 OS) by (unfold OSFRESH, os_cells, sb_cells, ios_cells; cbn [app]; do 3 eexists; exact OSR).
  unfold os_ctor_post. sys_finish.
Qed.
