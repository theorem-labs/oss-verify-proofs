(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout State Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Lib Require Import Tac Arr Bytes ITree Nodes Decode SysStep RegsEquiv Image.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.U Require Export Layout.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.P Require Import Str_tac Startup_glue.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.U Require Import Pj_steps Pj_loc_kit Pj_loc_imp Pj_loc_get.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.U Require Import Pj_loc_defs.
From OssFuzzTheorems.simdjson.fuzz_element.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Lib Require Import StoreFast.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.
Import ListNotations.
Open Scope bv_scope.

Definition classic_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word)
    (F : bvmap 5 word) (fc : bv 32) (lo : Z) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 ja1 ja2 ja3 jb1 jb2 jb3 jb4 jb5 jb6 jb6b jb6c jb7 jb8 jb9 jb10 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 0xedfa0) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom usegs)
    /\ munch [(bv_unsigned sp - 576, bv_unsigned sp); (0xeddc8, 0xedfaa); (0xedfc0, 0xeec78)]%Z m m'
    /\ wmono usegs m m' /\ mem_inv usegs m'
    /\ stk usegs m' lo (bv_unsigned sp)
    /\ rw_cells usegs m' 0xeddc8 (impb_A ja1 ja2 ja3)
    /\ rw_cells usegs m' 0xedfa0 [C8 (Z_to_bv 64 0xee3c8); C1 (Z_to_bv 8 1); C1 (Z_to_bv 8 1)]
    /\ rw_cells usegs m' 0xedfc0 (impb_B jb1 jb2 jb3 jb4 jb5 jb6 jb6b jb6c jb7 jb8 jb9 jb10).

Lemma classic_spec : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (lo : Z) (canary : word),
  stk usegs m lo (bv_unsigned sp) -> (lo <= bv_unsigned sp - 576)%Z -> (0x111000 <= lo)%Z -> (bv_unsigned sp < 2^62)%Z ->
  rw_cells usegs m 0xeddc8 imp0_A ->
  rw_cells usegs m 0xedfa0 [C8 (Z_to_bv 64 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)] ->
  rw_cells usegs m 0xedfc0 imp0_B ->
  rw_cells usegs m 0xdc448 [C8 (Z_to_bv 64 0x10f7f8)] -> rw_cells usegs m 0x10f7f8 [C8 canary] ->
  rw_cells usegs m 0x10f81b [C1 (Z_to_bv 8 0)] -> rw_cells usegs m 0x10f8f0 [C4 (Z_to_bv 64 0)] -> mem_inv usegs m ->
  evt usegs (classic_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo m)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0xa0f9c) fc None m (seg_rom usegs)).
Proof.
  intros until canary. intros ST LO LOLO HI RA CLS RB GOT CAN NL LK MI.
  unfold imp0_A in RA. unfold imp0_B in RB.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  pose proof (munch_refl [(bv_unsigned sp - 576, bv_unsigned sp); (0xeddc8, 0xedfaa); (0xedfc0, 0xeec78)]%Z m) as MU.
  pose proof (wmono_refl usegs m) as WM.
  carve_frame 32%nat ST.
  do 10 lstep.
  if_true.
  do 6 lstep.
  if_true.
  do 3 lstep.
  if_false.
  do 2 lstep.
  if_false.
  do 7 lstep.
  if_false.
  do 3 lstep.
  lstep.
  call_sp imp_ctor_spec; [exact ST | lia | lia | lia | exact RA | exact RB | exact GOT | exact CAN | exact NL | exact LK | assumption |].
  rename PC into ST. rename PC0 into RA. rename POST into RB. unfold impb_A in RA.
  do 16 lstep.
  release_frame FR ST (bv_unsigned sp).
  unfold classic_post. sys_finish; eassumption.
Qed.

Lemma locale_ctor_spec0 : forall ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (lo D : Z) (j : list byte) (canary : word),
  stk usegs m lo (bv_unsigned sp) -> (lo <= bv_unsigned sp - 608)%Z -> (0x111000 <= lo)%Z -> (bv_unsigned sp < 2^62)%Z ->
  LOC0 m -> rw_cells usegs m D [CB 8 j] -> (bv_unsigned sp <= D < 2^63)%Z ->
  rw_cells usegs m 0xdc448 [C8 (Z_to_bv 64 0x10f7f8)] -> rw_cells usegs m 0x10f7f8 [C8 canary] ->
  rw_cells usegs m 0x10f81b [C1 (Z_to_bv 8 0)] -> rw_cells usegs m 0x10f8f0 [C4 (Z_to_bv 64 0)] -> mem_inv usegs m ->
  evt usegs (locale_ctor_post ra sp gp tp t0 t1 t2 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo D 608 [(0xeddc8, 0xeec78)%Z] m)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 D) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0xa6db0) fc None m (seg_rom usegs)).
Proof.
  intros until canary. intros ST LO LOLO HI L0 DST RD GOT CAN NL LK MI.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  pose proof (munch_refl [(bv_unsigned sp - 608, bv_unsigned sp); (D, D + 8); (0xeddc8, 0xeec78)]%Z m) as MU.
  pose proof (wmono_refl usegs m) as WM.
  unfold LOC0, loc0_cells in L0.
  retype L0 [CB 472 (repeat (Z_to_bv 8 0) 472);
             C8 (Z_to_bv 64 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); CB 6 (repeat (Z_to_bv 8 0) 6);
             C8 (Z_to_bv 64 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); CB 6 (repeat (Z_to_bv 8 0) 6);
             CB 3256 (repeat (Z_to_bv 8 0) 3256)].
  take L0 1%nat 0xedfa0%Z RA. take L0 3%nat 0xedfaa%Z CLS. take L0 1%nat 0xedfb0%Z P1.
  take L0 3%nat 0xedfba%Z GLB. take L0 1%nat 0xedfc0%Z P2. rename L0 into RB.
  carve_frame 32%nat ST.
  do 11 lstep.
  if_true.
  do 6 lstep.
  if_true.
  do 3 lstep.
  if_false.
  do 2 lstep.
  if_false.
  do 7 lstep.
  if_false.
  lstep.
  call_sp classic_spec; [exact ST | lia | lia | lia | exact RA | exact CLS | exact RB | exact GOT | exact CAN | exact NL | exact LK | assumption |].
  rename PC into ST. rename PC0 into RA. rename PC1 into CLS. rename POST into RB. unfold impb_A in RA. unfold impb_B in RB.
  do 4 lstep.
  if_true.
  do 12 lstep.
  if_true.
  do 6 lstep.
  release_frame FR ST (bv_unsigned sp).

  glue RA CLS. glue RA P1. glue RA GLB. glue RA P2. glue RA RB.
  merge_at RA 14%nat 3%nat. merge_at RA 7%nat 5%nat.
  unfold locale_ctor_post. sys_finish.
  unfold LOCB, locb_cells. do 15 eexists. eassumption.
Qed.

Theorem locale_ctor_spec : forall ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (lo D : Z) (j : list byte) (canary : word),
  stk usegs m lo (bv_unsigned sp) -> (lo <= bv_unsigned sp - 608)%Z -> (0x111000 <= lo)%Z -> (bv_unsigned sp < 2^62)%Z ->
  pj_locale m -> rw_cells usegs m D [CB 8 j] -> (bv_unsigned sp <= D < 2^63)%Z ->
  rw_cells usegs m 0xdc448 [C8 (Z_to_bv 64 0x10f7f8)] -> rw_cells usegs m 0x10f7f8 [C8 canary] ->
  rw_cells usegs m 0x10f81b [C1 (Z_to_bv 8 0)] -> rw_cells usegs m 0x10f8f0 [C4 (Z_to_bv 64 0)] -> mem_inv usegs m ->
  evt usegs (locale_ctor_post ra sp gp tp t0 t1 t2 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo D 608 [(0xeddc8, 0xeec78)%Z] m)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 D) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0xa6db0) fc None m (seg_rom usegs)).
Proof.
  intros until canary. intros ST LO LOLO HI [L0|LB] DST RD GOT CAN NL LK MI.
  - eapply locale_ctor_spec0; eassumption.
  - eapply evt_mono; [ eapply locale_ctor_specB; [exact ST | lia | lia | exact LB | exact DST | lia | exact MI] | ].
    intros ms' (t0' & t1' & t2' & a0' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' & E & MU & WM & MI' & ST' & D' & LB').
    exists t0', t1', t2', a0', a1', a2', a3', a4', a5', a6', a7', t3', t4', t5', t6', m'.
    split; [exact E|]. split; [|auto].
    eapply munch_weaken; [|exact MU]. unfold sub_fp. cbn [outside]. intros x. lia.
Qed.
