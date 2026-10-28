(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout State Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.simdjson.fuzz_print_json.lib.Lib Require Import Tac Arr Bytes ITree Nodes Decode SysStep RegsEquiv Image.
From OssFuzzTheorems.Proofs.simdjson.fuzz_print_json.lib.U Require Export Layout.
From OssFuzzTheorems.Proofs.simdjson.fuzz_print_json.lib.P Require Import Str_tac Startup_glue.
From OssFuzzTheorems.Proofs.simdjson.fuzz_print_json.lib.U Require Import Pj_steps Pj_once Pj_loc_kit Pj_loc_newloc.
From OssFuzzTheorems.Proofs.simdjson.fuzz_print_json.lib.U Require Import F_memset Pj_loc_defs.
From OssFuzzTheorems.Proofs.simdjson.fuzz_print_json.lib.U Require Import Pj_loc_i00 Pj_loc_i01 Pj_loc_i02 Pj_loc_i03 Pj_loc_i04 Pj_loc_i05 Pj_loc_i06 Pj_loc_i07 Pj_loc_i08 Pj_loc_i09 Pj_loc_i10 Pj_loc_i11 Pj_loc_i12 Pj_loc_i13 Pj_loc_i14 Pj_loc_i15 Pj_loc_i16 Pj_loc_i17 Pj_loc_i18 Pj_loc_i19 Pj_loc_i20 Pj_loc_i21 Pj_loc_i22 Pj_loc_i23 Pj_loc_i24 Pj_loc_i25 Pj_loc_i26 Pj_loc_i27 Pj_loc_i28 Pj_loc_i29.
From OssFuzzTheorems.simdjson.fuzz_print_json.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.simdjson.fuzz_print_json.lib.Lib Require Import StoreFast.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.
Import ListNotations.
Open Scope bv_scope.

Definition imp0_A : list cell := [CB 472 (repeat (Z_to_bv 8 0) 472)].
Definition imp0_B : list cell := [CB 3256 (repeat (Z_to_bv 8 0) 3256)].
Definition impb_B (j2 j3 j4 j5 j6 : list byte) : list cell :=
  [CB 192 j2;
   C8 (Z_to_bv 64 18446744073709551615);
   C4 (Z_to_bv 64 3);
   CB 604 j3;
   C8 (Z_to_bv 64 0xd9608);
   CB 232 j4;
   C8 (Z_to_bv 64 0xed850);
   C8 (Z_to_bv 64 0xed940);
   CB 24 j5;
   C8 (Z_to_bv 64 0xed748);
   CB 2160 j6].

Definition imp_ctor_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word)
    (F : bvmap 5 word) (fc : bv 32) (lo : Z) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 j1 j2 j3 j4 j5 j6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom usegs)
    /\ munch [(bv_unsigned sp - 544, bv_unsigned sp); (0xed228, 0xed400); (0xed420, 0xee0d8)]%Z m m'
    /\ wmono usegs m m' /\ mem_inv usegs m'
    /\ stk usegs m' lo (bv_unsigned sp)
    /\ rw_cells usegs m' 0xed228 [CB 472 j1]
    /\ rw_cells usegs m' 0xed420 (impb_B j2 j3 j4 j5 j6).

Lemma imp_ctor_spec : forall ra sp gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (lo : Z) (canary : word),
  stk usegs m lo (bv_unsigned sp) -> (lo <= bv_unsigned sp - 544)%Z -> (0x110000 <= lo)%Z -> (bv_unsigned sp < 2^62)%Z ->
  rw_cells usegs m 0xed228 imp0_A -> rw_cells usegs m 0xed420 imp0_B ->
  rw_cells usegs m 0xdb8b0 [C8 (Z_to_bv 64 0x10ec58)] -> rw_cells usegs m 0x10ec58 [C8 canary] ->
  rw_cells usegs m 0x10ec7b [C1 (Z_to_bv 8 0)] -> rw_cells usegs m 0x10ed50 [C4 (Z_to_bv 64 0)] -> mem_inv usegs m ->
  evt usegs (imp_ctor_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo m)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 0xed828) (Z_to_bv 64 1) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x9d34c) fc None m (seg_rom usegs)).
Proof.
  intros until canary. intros ST LO LOLO HI RA RB GOT CAN NL LK MI.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  pose proof (munch_refl [(bv_unsigned sp - 544, bv_unsigned sp); (0xed228, 0xed400); (0xed420, 0xee0d8)]%Z m) as MU.
  pose proof (wmono_refl usegs m) as WM.
  unfold imp0_A in RA. unfold imp0_B in RB.
  retype RA [C8 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); CB 4 (repeat (Z_to_bv 8 0) 4); C8 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); CB 4 (repeat (Z_to_bv 8 0) 4); C8 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); CB 4 (repeat (Z_to_bv 8 0) 4); C8 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); CB 4 (repeat (Z_to_bv 8 0) 4); C8 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); CB 4 (repeat (Z_to_bv 8 0) 4); C8 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); CB 4 (repeat (Z_to_bv 8 0) 4); C8 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); CB 4 (repeat (Z_to_bv 8 0) 4); C8 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); CB 4 (repeat (Z_to_bv 8 0) 4); C8 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); CB 4 (repeat (Z_to_bv 8 0) 4); C8 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); CB 4 (repeat (Z_to_bv 8 0) 4); C8 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); CB 4 (repeat (Z_to_bv 8 0) 4); C8 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); CB 4 (repeat (Z_to_bv 8 0) 4); C8 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); CB 4 (repeat (Z_to_bv 8 0) 4); C8 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); CB 4 (repeat (Z_to_bv 8 0) 4); C8 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); CB 4 (repeat (Z_to_bv 8 0) 4); C8 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); CB 4 (repeat (Z_to_bv 8 0) 4); C8 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); CB 4 (repeat (Z_to_bv 8 0) 4); C8 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); CB 4 (repeat (Z_to_bv 8 0) 4); C8 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); CB 4 (repeat (Z_to_bv 8 0) 4); C8 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); CB 4 (repeat (Z_to_bv 8 0) 4); C4 (Z_to_bv 64 0); CB 4 (repeat (Z_to_bv 8 0) 4); C8 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); CB 4 (repeat (Z_to_bv 8 0) 4); C8 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); CB 4 (repeat (Z_to_bv 8 0) 4); C8 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); CB 4 (repeat (Z_to_bv 8 0) 4); C8 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); CB 4 (repeat (Z_to_bv 8 0) 4); C8 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); CB 4 (repeat (Z_to_bv 8 0) 4); C8 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); CB 4 (repeat (Z_to_bv 8 0) 4); CB 32 (repeat (Z_to_bv 8 0) 32); C8 (Z_to_bv 64 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); CB 6 (repeat (Z_to_bv 8 0) 6)].
  retype RB [CB 176 (repeat (Z_to_bv 8 0) 176); C8 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); CB 4 (repeat (Z_to_bv 8 0) 4); C8 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); CB 4 (repeat (Z_to_bv 8 0) 4); C8 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); CB 4 (repeat (Z_to_bv 8 0) 4); C8 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); CB 4 (repeat (Z_to_bv 8 0) 4); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); CB 96 (repeat (Z_to_bv 8 0) 96); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C1 (Z_to_bv 8 0); CB 103 (repeat (Z_to_bv 8 0) 103); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C2 (Z_to_bv 64 0); CB 6 (repeat (Z_to_bv 8 0) 6); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); CB 240 (repeat (Z_to_bv 8 0) 240); C8 (Z_to_bv 64 0); C2 (Z_to_bv 64 0); C1 (Z_to_bv 8 0); CB 1845 (repeat (Z_to_bv 8 0) 1845); CB 4 (repeat (Z_to_bv 8 0) 4); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); CB 28 (repeat (Z_to_bv 8 0) 28); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); CB 16 (repeat (Z_to_bv 8 0) 16); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)].

  take RA 2%nat 0xed234%Z ge1f68.
  take RA 58%nat 0xed368%Z a_0.
  take RA 1%nat 0xed36c%Z ge20a8.
  take RB 13%nat 0xed510%Z b_0.
  take RB 1%nat 0xed518%Z ge2250.
  take RB 1%nat 0xed520%Z ge2258.
  take RB 76%nat 0xed828%Z b_1.
  take RB 2%nat 0xed838%Z ge2568.
  take RB 3%nat 0xed850%Z ge2578.
  take RB 1%nat 0xed940%Z ge2590.
  take RB 3%nat 0xed94b%Z ge2680.
  take RB 1%nat 0xee080%Z b_2.
  take RB 3%nat 0xee08c%Z ge2dc0.
  take RB 1%nat 0xee0a8%Z b_3.
  take RB 6%nat 0xee0d8%Z ge2de8.
  callc seg_spec_0 clearing (clear ST ge1f68 ge20a8 ge2250 ge2258 ge2568 ge2578 ge2590 ge2680 ge2dc0 ge2de8); [exact ST | lia | lia | lia | exact ge1f68 | exact ge20a8 | exact ge2250 | exact ge2258 | exact ge2568 | exact ge2578 | exact ge2590 | exact ge2680 | exact ge2dc0 | exact GOT | exact CAN | exact ge2de8 | assumption |].
  rename PC into ST. rename PC0 into FR. rename PC1 into ge1f68. rename PC2 into ge20a8. rename PC3 into ge2250. rename PC4 into ge2258. rename PC5 into ge2568. rename PC6 into ge2578. rename PC7 into ge2590. rename PC8 into ge2598. rename PC9 into ge2680. rename PC10 into ge2dc0. rename POST into ge2de8.
  retype ge2598 [CB 8 (repeat (Z_to_bv 8 0) 8); CB 8 (repeat (Z_to_bv 8 0) 8); CB 8 (repeat (Z_to_bv 8 0) 8); CB 8 (repeat (Z_to_bv 8 0) 8); CB 8 (repeat (Z_to_bv 8 0) 8); CB 8 (repeat (Z_to_bv 8 0) 8); CB 8 (repeat (Z_to_bv 8 0) 8); CB 8 (repeat (Z_to_bv 8 0) 8); CB 8 (repeat (Z_to_bv 8 0) 8); CB 8 (repeat (Z_to_bv 8 0) 8); CB 8 (repeat (Z_to_bv 8 0) 8); CB 8 (repeat (Z_to_bv 8 0) 8); CB 8 (repeat (Z_to_bv 8 0) 8); CB 8 (repeat (Z_to_bv 8 0) 8); CB 8 (repeat (Z_to_bv 8 0) 8); CB 8 (repeat (Z_to_bv 8 0) 8); CB 8 (repeat (Z_to_bv 8 0) 8); CB 8 (repeat (Z_to_bv 8 0) 8); CB 8 (repeat (Z_to_bv 8 0) 8); CB 8 (repeat (Z_to_bv 8 0) 8); CB 8 (repeat (Z_to_bv 8 0) 8); CB 8 (repeat (Z_to_bv 8 0) 8); CB 8 (repeat (Z_to_bv 8 0) 8); CB 8 (repeat (Z_to_bv 8 0) 8); CB 8 (repeat (Z_to_bv 8 0) 8); CB 8 (repeat (Z_to_bv 8 0) 8); CB 8 (repeat (Z_to_bv 8 0) 8); CB 8 (repeat (Z_to_bv 8 0) 8); CB 8 (repeat (Z_to_bv 8 0) 8)].
  glue ge1f68 a_0.
  glue ge1f68 ge20a8.
  glue ge1f68 RA.
  rename ge1f68 into RA.
  glue b_0 ge2250.
  glue b_0 ge2258.
  glue b_0 b_1.
  glue b_0 ge2568.
  glue b_0 ge2578.
  glue b_0 ge2590.
  glue b_0 ge2598.
  glue b_0 ge2680.
  glue b_0 b_2.
  glue b_0 ge2dc0.
  glue b_0 b_3.
  glue b_0 ge2de8.
  glue b_0 RB.
  rename b_0 into RB.

  name_sp sp (-48)%Z. rewrite <- Hsp in ST.

  lazymatch type of FR with rw_cells _ ?m1 _ _ =>
    pose proof (munch_refl [(bv_unsigned sp - 544, bv_unsigned sp + -48); (0xed228, 0xed400); (0xed420, 0xee0d8)]%Z m1) as MUF;
    pose proof (wmono_refl usegs m1) as WMF end.
  pj_hide FR.

  take RA 3%nat 0xed238%Z a_0.
  take RA 2%nat 0xed244%Z ge1f78.
  take RA 55%nat 0xed368%Z a_1.
  take RA 1%nat 0xed36c%Z ge20a8.
  take RB 15%nat 0xed520%Z b_0.
  take RB 1%nat 0xed528%Z ge2260.
  take RB 1%nat 0xed530%Z ge2268.
  take RB 76%nat 0xed838%Z b_1.
  take RB 3%nat 0xed850%Z ge2578.
  take RB 1%nat 0xed858%Z b_2.
  take RB 1%nat 0xed860%Z ge2598.
  take RB 32%nat 0xee080%Z b_3.
  take RB 3%nat 0xee08c%Z ge2dc0.
  take RB 1%nat 0xee0a8%Z b_4.
  take RB 6%nat 0xee0d8%Z ge2de8.
  callc seg_spec_1 clearing (clear ST ge1f78 ge20a8 ge2260 ge2268 ge2578 ge2598 ge2dc0 ge2de8); [exact ST | lia | lia | lia | exact ge1f78 | exact ge20a8 | exact ge2260 | exact ge2268 | exact ge2578 | exact ge2598 | exact ge2dc0 | exact GOT | exact CAN | exact ge2de8 | assumption |].
  rename PC into ST. rename PC0 into ge1f78. rename PC1 into ge20a8. rename PC2 into ge2260. rename PC3 into ge2268. rename PC4 into ge2578. rename PC5 into ge2598. rename PC6 into ge2dc0. rename POST into ge2de8.
  glue a_0 ge1f78.
  glue a_0 a_1.
  glue a_0 ge20a8.
  glue a_0 RA.
  rename a_0 into RA.
  glue b_0 ge2260.
  glue b_0 ge2268.
  glue b_0 b_1.
  glue b_0 ge2578.
  glue b_0 b_2.
  glue b_0 ge2598.
  glue b_0 b_3.
  glue b_0 ge2dc0.
  glue b_0 b_4.
  glue b_0 ge2de8.
  glue b_0 RB.
  rename b_0 into RB.

  take RA 60%nat 0xed368%Z a_0.
  take RA 1%nat 0xed36c%Z ge20a8.
  take RB 4%nat 0xed4e0%Z b_0.
  take RB 2%nat 0xed4ec%Z ge2220.
  take RB 67%nat 0xed748%Z b_1.
  take RB 1%nat 0xed750%Z ge2488.
  take RB 1%nat 0xed758%Z ge2490.
  take RB 1%nat 0xed760%Z ge2498.
  take RB 1%nat 0xed761%Z ge24a0.
  take RB 16%nat 0xed838%Z b_2.
  take RB 3%nat 0xed850%Z ge2578.
  take RB 2%nat 0xed860%Z b_3.
  take RB 1%nat 0xed868%Z ge25a0.
  take RB 31%nat 0xee080%Z b_4.
  take RB 3%nat 0xee08c%Z ge2dc0.
  take RB 1%nat 0xee0a8%Z b_5.
  take RB 6%nat 0xee0d8%Z ge2de8.
  callc seg_spec_2 clearing (clear ST ge2220 ge20a8 ge2488 ge2490 ge2498 ge24a0 ge2578 ge25a0 ge2dc0 ge2de8); [exact ST | lia | lia | lia | exact ge2220 | exact ge20a8 | exact ge2488 | exact ge2490 | exact ge2498 | exact ge24a0 | exact ge2578 | exact ge25a0 | exact ge2dc0 | exact GOT | exact CAN | exact ge2de8 | assumption |].
  rename PC into ST. rename PC0 into ge2220. rename PC1 into ge20a8. rename PC2 into ge2488. rename PC3 into ge2490. rename PC4 into ge2498. rename PC5 into ge24a0. rename PC6 into ge2578. rename PC7 into ge25a0. rename PC8 into ge2dc0. rename POST into ge2de8.
  glue a_0 ge20a8.
  glue a_0 RA.
  rename a_0 into RA.
  glue b_0 ge2220.
  glue b_0 b_1.
  glue b_0 ge2488.
  glue b_0 ge2490.
  glue b_0 ge2498.
  glue b_0 ge24a0.
  glue b_0 b_2.
  glue b_0 ge2578.
  glue b_0 b_3.
  glue b_0 ge25a0.
  glue b_0 b_4.
  glue b_0 ge2dc0.
  glue b_0 b_5.
  glue b_0 ge2de8.
  glue b_0 RB.
  rename b_0 into RB.

  take RA 60%nat 0xed368%Z a_0.
  take RA 1%nat 0xed36c%Z ge20a8.
  take RB 1%nat 0xed4d0%Z b_0.
  take RB 2%nat 0xed4dc%Z ge2210.
  take RB 14%nat 0xed530%Z b_1.
  take RB 1%nat 0xed538%Z ge2270.
  take RB 1%nat 0xed540%Z ge2278.
  take RB 74%nat 0xed838%Z b_2.
  take RB 3%nat 0xed850%Z ge2578.
  take RB 3%nat 0xed868%Z b_3.
  take RB 1%nat 0xed870%Z ge25a8.
  take RB 30%nat 0xee080%Z b_4.
  take RB 3%nat 0xee08c%Z ge2dc0.
  take RB 1%nat 0xee0a8%Z b_5.
  take RB 6%nat 0xee0d8%Z ge2de8.
  callc seg_spec_3 clearing (clear ST ge2210 ge20a8 ge2270 ge2278 ge2578 ge25a8 ge2dc0 ge2de8); [exact ST | lia | lia | lia | exact ge2210 | exact ge20a8 | exact ge2270 | exact ge2278 | exact ge2578 | exact ge25a8 | exact ge2dc0 | exact GOT | exact CAN | exact ge2de8 | assumption |].
  rename PC into ST. rename PC0 into ge2210. rename PC1 into ge20a8. rename PC2 into ge2270. rename PC3 into ge2278. rename PC4 into ge2578. rename PC5 into ge25a8. rename PC6 into ge2dc0. rename POST into ge2de8.
  glue a_0 ge20a8.
  glue a_0 RA.
  rename a_0 into RA.
  glue b_0 ge2210.
  glue b_0 b_1.
  glue b_0 ge2270.
  glue b_0 ge2278.
  glue b_0 b_2.
  glue b_0 ge2578.
  glue b_0 b_3.
  glue b_0 ge25a8.
  glue b_0 b_4.
  glue b_0 ge2dc0.
  glue b_0 b_5.
  glue b_0 ge2de8.
  glue b_0 RB.
  rename b_0 into RB.

  take RA 60%nat 0xed368%Z a_0.
  take RA 1%nat 0xed36c%Z ge20a8.
  take RA 1%nat 0xed370%Z a_1.
  take RA 2%nat 0xed37c%Z ge20b0.
  take RB 19%nat 0xed540%Z b_0.
  take RB 1%nat 0xed548%Z ge2280.
  take RB 1%nat 0xed550%Z ge2288.
  take RB 72%nat 0xed838%Z b_1.
  take RB 3%nat 0xed850%Z ge2578.
  take RB 4%nat 0xed870%Z b_2.
  take RB 1%nat 0xed878%Z ge25b0.
  take RB 29%nat 0xee080%Z b_3.
  take RB 3%nat 0xee08c%Z ge2dc0.
  take RB 1%nat 0xee0a8%Z b_4.
  take RB 6%nat 0xee0d8%Z ge2de8.
  callc seg_spec_4 clearing (clear ST ge20b0 ge20a8 ge2280 ge2288 ge2578 ge25b0 ge2dc0 ge2de8); [exact ST | lia | lia | lia | exact ge20b0 | exact ge20a8 | exact ge2280 | exact ge2288 | exact ge2578 | exact ge25b0 | exact ge2dc0 | exact GOT | exact CAN | exact ge2de8 | assumption |].
  rename PC into ST. rename PC0 into ge20b0. rename PC1 into ge20a8. rename PC2 into ge2280. rename PC3 into ge2288. rename PC4 into ge2578. rename PC5 into ge25b0. rename PC6 into ge2dc0. rename POST into ge2de8.
  glue a_0 ge20a8.
  glue a_0 a_1.
  glue a_0 ge20b0.
  glue a_0 RA.
  rename a_0 into RA.
  glue b_0 ge2280.
  glue b_0 ge2288.
  glue b_0 b_1.
  glue b_0 ge2578.
  glue b_0 b_2.
  glue b_0 ge25b0.
  glue b_0 b_3.
  glue b_0 ge2dc0.
  glue b_0 b_4.
  glue b_0 ge2de8.
  glue b_0 RB.
  rename b_0 into RB.

  take RA 60%nat 0xed368%Z a_0.
  take RA 1%nat 0xed36c%Z ge20a8.
  take RA 4%nat 0xed380%Z a_1.
  take RA 2%nat 0xed38c%Z ge20c0.
  take RA 14%nat 0xed3f0%Z a_2.
  take RA 1%nat 0xed3f8%Z ge2130.
  take RA 2%nat 0xed3fa%Z ge2138.
  take RB 58%nat 0xed6d0%Z b_0.
  take RB 1%nat 0xed6d8%Z ge2410.
  take RB 1%nat 0xed6e0%Z ge2418.
  take RB 1%nat 0xed6e8%Z ge2420.
  take RB 32%nat 0xed838%Z b_1.
  take RB 3%nat 0xed850%Z ge2578.
  take RB 5%nat 0xed878%Z b_2.
  take RB 1%nat 0xed880%Z ge25b8.
  take RB 28%nat 0xee080%Z b_3.
  take RB 3%nat 0xee08c%Z ge2dc0.
  take RB 1%nat 0xee0a8%Z b_4.
  take RB 6%nat 0xee0d8%Z ge2de8.
  callc seg_spec_5 clearing (clear ST ge20c0 ge20a8 ge2130 ge2138 ge2410 ge2418 ge2420 ge2578 ge25b8 ge2dc0 ge2de8); [exact ST | lia | lia | lia | exact ge20c0 | exact ge20a8 | exact ge2130 | exact ge2138 | exact ge2410 | exact ge2418 | exact ge2420 | exact ge2578 | exact ge25b8 | exact ge2dc0 | exact GOT | exact CAN | exact NL | exact LK | exact ge2de8 | assumption |].
  rename PC into ST. rename PC0 into ge20c0. rename PC1 into ge20a8. rename PC2 into ge2130. rename PC3 into ge2138. rename PC4 into ge2410. rename PC5 into ge2418. rename PC6 into ge2420. rename PC7 into ge2578. rename PC8 into ge25b8. rename PC9 into ge2dc0. rename POST into ge2de8.
  glue a_0 ge20a8.
  glue a_0 a_1.
  glue a_0 ge20c0.
  glue a_0 a_2.
  glue a_0 ge2130.
  glue a_0 ge2138.
  glue a_0 RA.
  rename a_0 into RA.
  glue b_0 ge2410.
  glue b_0 ge2418.
  glue b_0 ge2420.
  glue b_0 b_1.
  glue b_0 ge2578.
  glue b_0 b_2.
  glue b_0 ge25b8.
  glue b_0 b_3.
  glue b_0 ge2dc0.
  glue b_0 b_4.
  glue b_0 ge2de8.
  glue b_0 RB.
  rename b_0 into RB.

  take RA 60%nat 0xed368%Z a_0.
  take RA 1%nat 0xed36c%Z ge20a8.
  take RA 7%nat 0xed390%Z a_1.
  take RA 2%nat 0xed39c%Z ge20d0.
  take RB 21%nat 0xed550%Z b_0.
  take RB 1%nat 0xed558%Z ge2290.
  take RB 1%nat 0xed560%Z ge2298.
  take RB 70%nat 0xed838%Z b_1.
  take RB 3%nat 0xed850%Z ge2578.
  take RB 6%nat 0xed880%Z b_2.
  take RB 1%nat 0xed888%Z ge25c0.
  take RB 27%nat 0xee080%Z b_3.
  take RB 3%nat 0xee08c%Z ge2dc0.
  take RB 1%nat 0xee0a8%Z b_4.
  take RB 6%nat 0xee0d8%Z ge2de8.
  callc seg_spec_6 clearing (clear ST ge20d0 ge20a8 ge2290 ge2298 ge2578 ge25c0 ge2dc0 ge2de8); [exact ST | lia | lia | lia | exact ge20d0 | exact ge20a8 | exact ge2290 | exact ge2298 | exact ge2578 | exact ge25c0 | exact ge2dc0 | exact GOT | exact CAN | exact ge2de8 | assumption |].
  rename PC into ST. rename PC0 into ge20d0. rename PC1 into ge20a8. rename PC2 into ge2290. rename PC3 into ge2298. rename PC4 into ge2578. rename PC5 into ge25c0. rename PC6 into ge2dc0. rename POST into ge2de8.
  glue a_0 ge20a8.
  glue a_0 a_1.
  glue a_0 ge20d0.
  glue a_0 RA.
  rename a_0 into RA.
  glue b_0 ge2290.
  glue b_0 ge2298.
  glue b_0 b_1.
  glue b_0 ge2578.
  glue b_0 b_2.
  glue b_0 ge25c0.
  glue b_0 b_3.
  glue b_0 ge2dc0.
  glue b_0 b_4.
  glue b_0 ge2de8.
  glue b_0 RB.
  rename b_0 into RB.

  take RA 60%nat 0xed368%Z a_0.
  take RA 1%nat 0xed36c%Z ge20a8.
  take RA 13%nat 0xed3b0%Z a_1.
  take RA 2%nat 0xed3bc%Z ge20f0.
  take RB 23%nat 0xed560%Z b_0.
  take RB 1%nat 0xed568%Z ge22a0.
  take RB 1%nat 0xed570%Z ge22a8.
  take RB 68%nat 0xed838%Z b_1.
  take RB 3%nat 0xed850%Z ge2578.
  take RB 7%nat 0xed888%Z b_2.
  take RB 1%nat 0xed890%Z ge25c8.
  take RB 26%nat 0xee080%Z b_3.
  take RB 3%nat 0xee08c%Z ge2dc0.
  take RB 1%nat 0xee0a8%Z b_4.
  take RB 6%nat 0xee0d8%Z ge2de8.
  callc seg_spec_7 clearing (clear ST ge20f0 ge20a8 ge22a0 ge22a8 ge2578 ge25c8 ge2dc0 ge2de8); [exact ST | lia | lia | lia | exact ge20f0 | exact ge20a8 | exact ge22a0 | exact ge22a8 | exact ge2578 | exact ge25c8 | exact ge2dc0 | exact GOT | exact CAN | exact ge2de8 | assumption |].
  rename PC into ST. rename PC0 into ge20f0. rename PC1 into ge20a8. rename PC2 into ge22a0. rename PC3 into ge22a8. rename PC4 into ge2578. rename PC5 into ge25c8. rename PC6 into ge2dc0. rename POST into ge2de8.
  glue a_0 ge20a8.
  glue a_0 a_1.
  glue a_0 ge20f0.
  glue a_0 RA.
  rename a_0 into RA.
  glue b_0 ge22a0.
  glue b_0 ge22a8.
  glue b_0 b_1.
  glue b_0 ge2578.
  glue b_0 b_2.
  glue b_0 ge25c8.
  glue b_0 b_3.
  glue b_0 ge2dc0.
  glue b_0 b_4.
  glue b_0 ge2de8.
  glue b_0 RB.
  rename b_0 into RB.

  take RA 60%nat 0xed368%Z a_0.
  take RA 1%nat 0xed36c%Z ge20a8.
  take RA 10%nat 0xed3a0%Z a_1.
  take RA 2%nat 0xed3ac%Z ge20e0.
  take RB 25%nat 0xed570%Z b_0.
  take RB 1%nat 0xed578%Z ge22b0.
  take RB 1%nat 0xed580%Z ge22b8.
  take RB 66%nat 0xed838%Z b_1.
  take RB 3%nat 0xed850%Z ge2578.
  take RB 8%nat 0xed890%Z b_2.
  take RB 1%nat 0xed898%Z ge25d0.
  take RB 25%nat 0xee080%Z b_3.
  take RB 3%nat 0xee08c%Z ge2dc0.
  take RB 1%nat 0xee0a8%Z b_4.
  take RB 6%nat 0xee0d8%Z ge2de8.
  callc seg_spec_8 clearing (clear ST ge20e0 ge20a8 ge22b0 ge22b8 ge2578 ge25d0 ge2dc0 ge2de8); [exact ST | lia | lia | lia | exact ge20e0 | exact ge20a8 | exact ge22b0 | exact ge22b8 | exact ge2578 | exact ge25d0 | exact ge2dc0 | exact GOT | exact CAN | exact ge2de8 | assumption |].
  rename PC into ST. rename PC0 into ge20e0. rename PC1 into ge20a8. rename PC2 into ge22b0. rename PC3 into ge22b8. rename PC4 into ge2578. rename PC5 into ge25d0. rename PC6 into ge2dc0. rename POST into ge2de8.
  glue a_0 ge20a8.
  glue a_0 a_1.
  glue a_0 ge20e0.
  glue a_0 RA.
  rename a_0 into RA.
  glue b_0 ge22b0.
  glue b_0 ge22b8.
  glue b_0 b_1.
  glue b_0 ge2578.
  glue b_0 b_2.
  glue b_0 ge25d0.
  glue b_0 b_3.
  glue b_0 ge2dc0.
  glue b_0 b_4.
  glue b_0 ge2de8.
  glue b_0 RB.
  rename b_0 into RB.

  take RA 60%nat 0xed368%Z a_0.
  take RA 1%nat 0xed36c%Z ge20a8.
  take RA 16%nat 0xed3c0%Z a_1.
  take RA 2%nat 0xed3cc%Z ge2100.
  take RB 27%nat 0xed580%Z b_0.
  take RB 1%nat 0xed588%Z ge22c0.
  take RB 1%nat 0xed590%Z ge22c8.
  take RB 64%nat 0xed838%Z b_1.
  take RB 3%nat 0xed850%Z ge2578.
  take RB 9%nat 0xed898%Z b_2.
  take RB 1%nat 0xed8a0%Z ge25d8.
  take RB 24%nat 0xee080%Z b_3.
  take RB 3%nat 0xee08c%Z ge2dc0.
  take RB 1%nat 0xee0a8%Z b_4.
  take RB 6%nat 0xee0d8%Z ge2de8.
  callc seg_spec_9 clearing (clear ST ge2100 ge20a8 ge22c0 ge22c8 ge2578 ge25d8 ge2dc0 ge2de8); [exact ST | lia | lia | lia | exact ge2100 | exact ge20a8 | exact ge22c0 | exact ge22c8 | exact ge2578 | exact ge25d8 | exact ge2dc0 | exact GOT | exact CAN | exact ge2de8 | assumption |].
  rename PC into ST. rename PC0 into ge2100. rename PC1 into ge20a8. rename PC2 into ge22c0. rename PC3 into ge22c8. rename PC4 into ge2578. rename PC5 into ge25d8. rename PC6 into ge2dc0. rename POST into ge2de8.
  glue a_0 ge20a8.
  glue a_0 a_1.
  glue a_0 ge2100.
  glue a_0 RA.
  rename a_0 into RA.
  glue b_0 ge22c0.
  glue b_0 ge22c8.
  glue b_0 b_1.
  glue b_0 ge2578.
  glue b_0 b_2.
  glue b_0 ge25d8.
  glue b_0 b_3.
  glue b_0 ge2dc0.
  glue b_0 b_4.
  glue b_0 ge2de8.
  glue b_0 RB.
  rename b_0 into RB.

  take RA 60%nat 0xed368%Z a_0.
  take RA 1%nat 0xed36c%Z ge20a8.
  take RB 7%nat 0xed4f0%Z b_0.
  take RB 2%nat 0xed4fc%Z ge2230.
  take RB 69%nat 0xed7c8%Z b_1.
  take RB 1%nat 0xed7d0%Z ge2508.
  take RB 1%nat 0xed7d8%Z ge2510.
  take RB 1%nat 0xed7da%Z ge2518.
  take RB 1%nat 0xed7e0%Z b_2.
  take RB 1%nat 0xed7e8%Z ge2520.
  take RB 1%nat 0xed7f0%Z ge2528.
  take RB 1%nat 0xed7f8%Z ge2530.
  take RB 8%nat 0xed838%Z b_3.
  take RB 3%nat 0xed850%Z ge2578.
  take RB 10%nat 0xed8a0%Z b_4.
  take RB 1%nat 0xed8a8%Z ge25e0.
  take RB 23%nat 0xee080%Z b_5.
  take RB 3%nat 0xee08c%Z ge2dc0.
  take RB 1%nat 0xee0a8%Z b_6.
  take RB 6%nat 0xee0d8%Z ge2de8.
  callc seg_spec_10 clearing (clear ST ge2230 ge20a8 ge2508 ge2510 ge2518 ge2520 ge2528 ge2530 ge2578 ge25e0 ge2dc0 ge2de8); [exact ST | lia | lia | lia | exact ge2230 | exact ge20a8 | exact ge2508 | exact ge2510 | exact ge2518 | exact ge2520 | exact ge2528 | exact ge2530 | exact ge2578 | exact ge25e0 | exact ge2dc0 | exact GOT | exact CAN | exact ge2de8 | assumption |].
  rename PC into ST. rename PC0 into ge2230. rename PC1 into ge20a8. rename PC2 into ge2508. rename PC3 into ge2510. rename PC4 into ge2518. rename PC5 into ge2520. rename PC6 into ge2528. rename PC7 into ge2530. rename PC8 into ge2578. rename PC9 into ge25e0. rename PC10 into ge2dc0. rename POST into ge2de8.
  glue a_0 ge20a8.
  glue a_0 RA.
  rename a_0 into RA.
  glue b_0 ge2230.
  glue b_0 b_1.
  glue b_0 ge2508.
  glue b_0 ge2510.
  glue b_0 ge2518.
  glue b_0 b_2.
  glue b_0 ge2520.
  glue b_0 ge2528.
  glue b_0 ge2530.
  glue b_0 b_3.
  glue b_0 ge2578.
  glue b_0 b_4.
  glue b_0 ge25e0.
  glue b_0 b_5.
  glue b_0 ge2dc0.
  glue b_0 b_6.
  glue b_0 ge2de8.
  glue b_0 RB.
  rename b_0 into RB.

  take RA 60%nat 0xed368%Z a_0.
  take RA 1%nat 0xed36c%Z ge20a8.
  take RB 10%nat 0xed500%Z b_0.
  take RB 2%nat 0xed50c%Z ge2240.
  take RB 73%nat 0xed7f8%Z b_1.
  take RB 1%nat 0xed800%Z ge2538.
  take RB 1%nat 0xed808%Z ge2540.
  take RB 1%nat 0xed810%Z ge2548.
  take RB 1%nat 0xed818%Z ge2550.
  take RB 1%nat 0xed820%Z ge2558.
  take RB 1%nat 0xed828%Z ge2560.
  take RB 2%nat 0xed838%Z b_2.
  take RB 3%nat 0xed850%Z ge2578.
  take RB 11%nat 0xed8a8%Z b_3.
  take RB 1%nat 0xed8b0%Z ge25e8.
  take RB 22%nat 0xee080%Z b_4.
  take RB 3%nat 0xee08c%Z ge2dc0.
  take RB 1%nat 0xee0a8%Z b_5.
  take RB 6%nat 0xee0d8%Z ge2de8.
  callc seg_spec_11 clearing (clear ST ge2240 ge20a8 ge2538 ge2540 ge2548 ge2550 ge2558 ge2560 ge2578 ge25e8 ge2dc0 ge2de8); [exact ST | lia | lia | lia | exact ge2240 | exact ge20a8 | exact ge2538 | exact ge2540 | exact ge2548 | exact ge2550 | exact ge2558 | exact ge2560 | exact ge2578 | exact ge25e8 | exact ge2dc0 | exact GOT | exact CAN | exact ge2de8 | assumption |].
  rename PC into ST. rename PC0 into ge2240. rename PC1 into ge20a8. rename PC2 into ge2538. rename PC3 into ge2540. rename PC4 into ge2548. rename PC5 into ge2550. rename PC6 into ge2558. rename PC7 into ge2560. rename PC8 into ge2578. rename PC9 into ge25e8. rename PC10 into ge2dc0. rename POST into ge2de8.
  glue a_0 ge20a8.
  glue a_0 RA.
  rename a_0 into RA.
  glue b_0 ge2240.
  glue b_0 b_1.
  glue b_0 ge2538.
  glue b_0 ge2540.
  glue b_0 ge2548.
  glue b_0 ge2550.
  glue b_0 ge2558.
  glue b_0 ge2560.
  glue b_0 b_2.
  glue b_0 ge2578.
  glue b_0 b_3.
  glue b_0 ge25e8.
  glue b_0 b_4.
  glue b_0 ge2dc0.
  glue b_0 b_5.
  glue b_0 ge2de8.
  glue b_0 RB.
  rename b_0 into RB.

  take RA 6%nat 0xed248%Z a_0.
  take RA 2%nat 0xed254%Z ge1f88.
  take RA 52%nat 0xed368%Z a_1.
  take RA 1%nat 0xed36c%Z ge20a8.
  take RB 29%nat 0xed590%Z b_0.
  take RB 1%nat 0xed598%Z ge22d0.
  take RB 1%nat 0xed5a0%Z ge22d8.
  take RB 62%nat 0xed838%Z b_1.
  take RB 3%nat 0xed850%Z ge2578.
  take RB 12%nat 0xed8b0%Z b_2.
  take RB 1%nat 0xed8b8%Z ge25f0.
  take RB 21%nat 0xee080%Z b_3.
  take RB 3%nat 0xee08c%Z ge2dc0.
  take RB 1%nat 0xee0a8%Z b_4.
  take RB 6%nat 0xee0d8%Z ge2de8.
  callc seg_spec_12 clearing (clear ST ge1f88 ge20a8 ge22d0 ge22d8 ge2578 ge25f0 ge2dc0 ge2de8); [exact ST | lia | lia | lia | exact ge1f88 | exact ge20a8 | exact ge22d0 | exact ge22d8 | exact ge2578 | exact ge25f0 | exact ge2dc0 | exact GOT | exact CAN | exact ge2de8 | assumption |].
  rename PC into ST. rename PC0 into ge1f88. rename PC1 into ge20a8. rename PC2 into ge22d0. rename PC3 into ge22d8. rename PC4 into ge2578. rename PC5 into ge25f0. rename PC6 into ge2dc0. rename POST into ge2de8.
  glue a_0 ge1f88.
  glue a_0 a_1.
  glue a_0 ge20a8.
  glue a_0 RA.
  rename a_0 into RA.
  glue b_0 ge22d0.
  glue b_0 ge22d8.
  glue b_0 b_1.
  glue b_0 ge2578.
  glue b_0 b_2.
  glue b_0 ge25f0.
  glue b_0 b_3.
  glue b_0 ge2dc0.
  glue b_0 b_4.
  glue b_0 ge2de8.
  glue b_0 RB.
  rename b_0 into RB.

  take RA 9%nat 0xed258%Z a_0.
  take RA 2%nat 0xed264%Z ge1f98.
  take RA 49%nat 0xed368%Z a_1.
  take RA 1%nat 0xed36c%Z ge20a8.
  take RB 31%nat 0xed5a0%Z b_0.
  take RB 1%nat 0xed5a8%Z ge22e0.
  take RB 1%nat 0xed5b0%Z ge22e8.
  take RB 60%nat 0xed838%Z b_1.
  take RB 3%nat 0xed850%Z ge2578.
  take RB 13%nat 0xed8b8%Z b_2.
  take RB 1%nat 0xed8c0%Z ge25f8.
  take RB 20%nat 0xee080%Z b_3.
  take RB 3%nat 0xee08c%Z ge2dc0.
  take RB 1%nat 0xee0a8%Z b_4.
  take RB 6%nat 0xee0d8%Z ge2de8.
  callc seg_spec_13 clearing (clear ST ge1f98 ge20a8 ge22e0 ge22e8 ge2578 ge25f8 ge2dc0 ge2de8); [exact ST | lia | lia | lia | exact ge1f98 | exact ge20a8 | exact ge22e0 | exact ge22e8 | exact ge2578 | exact ge25f8 | exact ge2dc0 | exact GOT | exact CAN | exact ge2de8 | assumption |].
  rename PC into ST. rename PC0 into ge1f98. rename PC1 into ge20a8. rename PC2 into ge22e0. rename PC3 into ge22e8. rename PC4 into ge2578. rename PC5 into ge25f8. rename PC6 into ge2dc0. rename POST into ge2de8.
  glue a_0 ge1f98.
  glue a_0 a_1.
  glue a_0 ge20a8.
  glue a_0 RA.
  rename a_0 into RA.
  glue b_0 ge22e0.
  glue b_0 ge22e8.
  glue b_0 b_1.
  glue b_0 ge2578.
  glue b_0 b_2.
  glue b_0 ge25f8.
  glue b_0 b_3.
  glue b_0 ge2dc0.
  glue b_0 b_4.
  glue b_0 ge2de8.
  glue b_0 RB.
  rename b_0 into RB.

  take RA 12%nat 0xed268%Z a_0.
  take RA 2%nat 0xed274%Z ge1fa8.
  take RA 46%nat 0xed368%Z a_1.
  take RA 1%nat 0xed36c%Z ge20a8.
  take RB 33%nat 0xed5b0%Z b_0.
  take RB 1%nat 0xed5b8%Z ge22f0.
  take RB 1%nat 0xed5c0%Z ge22f8.
  take RB 58%nat 0xed838%Z b_1.
  take RB 3%nat 0xed850%Z ge2578.
  take RB 14%nat 0xed8c0%Z b_2.
  take RB 1%nat 0xed8c8%Z ge2600.
  take RB 19%nat 0xee080%Z b_3.
  take RB 3%nat 0xee08c%Z ge2dc0.
  take RB 1%nat 0xee0a8%Z b_4.
  take RB 6%nat 0xee0d8%Z ge2de8.
  callc seg_spec_14 clearing (clear ST ge1fa8 ge20a8 ge22f0 ge22f8 ge2578 ge2600 ge2dc0 ge2de8); [exact ST | lia | lia | lia | exact ge1fa8 | exact ge20a8 | exact ge22f0 | exact ge22f8 | exact ge2578 | exact ge2600 | exact ge2dc0 | exact GOT | exact CAN | exact ge2de8 | assumption |].
  rename PC into ST. rename PC0 into ge1fa8. rename PC1 into ge20a8. rename PC2 into ge22f0. rename PC3 into ge22f8. rename PC4 into ge2578. rename PC5 into ge2600. rename PC6 into ge2dc0. rename POST into ge2de8.
  glue a_0 ge1fa8.
  glue a_0 a_1.
  glue a_0 ge20a8.
  glue a_0 RA.
  rename a_0 into RA.
  glue b_0 ge22f0.
  glue b_0 ge22f8.
  glue b_0 b_1.
  glue b_0 ge2578.
  glue b_0 b_2.
  glue b_0 ge2600.
  glue b_0 b_3.
  glue b_0 ge2dc0.
  glue b_0 b_4.
  glue b_0 ge2de8.
  glue b_0 RB.
  rename b_0 into RB.

  take RA 15%nat 0xed278%Z a_0.
  take RA 2%nat 0xed284%Z ge1fb8.
  take RA 43%nat 0xed368%Z a_1.
  take RA 1%nat 0xed36c%Z ge20a8.
  take RB 35%nat 0xed5c0%Z b_0.
  take RB 1%nat 0xed5c8%Z ge2300.
  take RB 1%nat 0xed5d0%Z ge2308.
  take RB 56%nat 0xed838%Z b_1.
  take RB 3%nat 0xed850%Z ge2578.
  take RB 15%nat 0xed8c8%Z b_2.
  take RB 1%nat 0xed8d0%Z ge2608.
  take RB 18%nat 0xee080%Z b_3.
  take RB 3%nat 0xee08c%Z ge2dc0.
  take RB 1%nat 0xee0a8%Z b_4.
  take RB 6%nat 0xee0d8%Z ge2de8.
  callc seg_spec_15 clearing (clear ST ge1fb8 ge20a8 ge2300 ge2308 ge2578 ge2608 ge2dc0 ge2de8); [exact ST | lia | lia | lia | exact ge1fb8 | exact ge20a8 | exact ge2300 | exact ge2308 | exact ge2578 | exact ge2608 | exact ge2dc0 | exact GOT | exact CAN | exact ge2de8 | assumption |].
  rename PC into ST. rename PC0 into ge1fb8. rename PC1 into ge20a8. rename PC2 into ge2300. rename PC3 into ge2308. rename PC4 into ge2578. rename PC5 into ge2608. rename PC6 into ge2dc0. rename POST into ge2de8.
  glue a_0 ge1fb8.
  glue a_0 a_1.
  glue a_0 ge20a8.
  glue a_0 RA.
  rename a_0 into RA.
  glue b_0 ge2300.
  glue b_0 ge2308.
  glue b_0 b_1.
  glue b_0 ge2578.
  glue b_0 b_2.
  glue b_0 ge2608.
  glue b_0 b_3.
  glue b_0 ge2dc0.
  glue b_0 b_4.
  glue b_0 ge2de8.
  glue b_0 RB.
  rename b_0 into RB.

  take RA 30%nat 0xed2c8%Z a_0.
  take RA 2%nat 0xed2d4%Z ge2008.
  take RA 28%nat 0xed368%Z a_1.
  take RA 1%nat 0xed36c%Z ge20a8.
  take RB 37%nat 0xed5d0%Z b_0.
  take RB 1%nat 0xed5d8%Z ge2310.
  take RB 1%nat 0xed5e0%Z ge2318.
  take RB 54%nat 0xed838%Z b_1.
  take RB 3%nat 0xed850%Z ge2578.
  take RB 16%nat 0xed8d0%Z b_2.
  take RB 1%nat 0xed8d8%Z ge2610.
  take RB 17%nat 0xee080%Z b_3.
  take RB 3%nat 0xee08c%Z ge2dc0.
  take RB 1%nat 0xee0a8%Z b_4.
  take RB 6%nat 0xee0d8%Z ge2de8.
  callc seg_spec_16 clearing (clear ST ge2008 ge20a8 ge2310 ge2318 ge2578 ge2610 ge2dc0 ge2de8); [exact ST | lia | lia | lia | exact ge2008 | exact ge20a8 | exact ge2310 | exact ge2318 | exact ge2578 | exact ge2610 | exact ge2dc0 | exact GOT | exact CAN | exact ge2de8 | assumption |].
  rename PC into ST. rename PC0 into ge2008. rename PC1 into ge20a8. rename PC2 into ge2310. rename PC3 into ge2318. rename PC4 into ge2578. rename PC5 into ge2610. rename PC6 into ge2dc0. rename POST into ge2de8.
  glue a_0 ge2008.
  glue a_0 a_1.
  glue a_0 ge20a8.
  glue a_0 RA.
  rename a_0 into RA.
  glue b_0 ge2310.
  glue b_0 ge2318.
  glue b_0 b_1.
  glue b_0 ge2578.
  glue b_0 b_2.
  glue b_0 ge2610.
  glue b_0 b_3.
  glue b_0 ge2dc0.
  glue b_0 b_4.
  glue b_0 ge2de8.
  glue b_0 RB.
  rename b_0 into RB.

  take RA 33%nat 0xed2d8%Z a_0.
  take RA 2%nat 0xed2e4%Z ge2018.
  take RA 25%nat 0xed368%Z a_1.
  take RA 1%nat 0xed36c%Z ge20a8.
  take RB 39%nat 0xed5e0%Z b_0.
  take RB 1%nat 0xed5e8%Z ge2320.
  take RB 1%nat 0xed5f0%Z ge2328.
  take RB 52%nat 0xed838%Z b_1.
  take RB 3%nat 0xed850%Z ge2578.
  take RB 17%nat 0xed8d8%Z b_2.
  take RB 1%nat 0xed8e0%Z ge2618.
  take RB 16%nat 0xee080%Z b_3.
  take RB 3%nat 0xee08c%Z ge2dc0.
  take RB 1%nat 0xee0a8%Z b_4.
  take RB 6%nat 0xee0d8%Z ge2de8.
  callc seg_spec_17 clearing (clear ST ge2018 ge20a8 ge2320 ge2328 ge2578 ge2618 ge2dc0 ge2de8); [exact ST | lia | lia | lia | exact ge2018 | exact ge20a8 | exact ge2320 | exact ge2328 | exact ge2578 | exact ge2618 | exact ge2dc0 | exact GOT | exact CAN | exact ge2de8 | assumption |].
  rename PC into ST. rename PC0 into ge2018. rename PC1 into ge20a8. rename PC2 into ge2320. rename PC3 into ge2328. rename PC4 into ge2578. rename PC5 into ge2618. rename PC6 into ge2dc0. rename POST into ge2de8.
  glue a_0 ge2018.
  glue a_0 a_1.
  glue a_0 ge20a8.
  glue a_0 RA.
  rename a_0 into RA.
  glue b_0 ge2320.
  glue b_0 ge2328.
  glue b_0 b_1.
  glue b_0 ge2578.
  glue b_0 b_2.
  glue b_0 ge2618.
  glue b_0 b_3.
  glue b_0 ge2dc0.
  glue b_0 b_4.
  glue b_0 ge2de8.
  glue b_0 RB.
  rename b_0 into RB.

  take RA 36%nat 0xed2e8%Z a_0.
  take RA 2%nat 0xed2f4%Z ge2028.
  take RA 22%nat 0xed368%Z a_1.
  take RA 1%nat 0xed36c%Z ge20a8.
  take RB 41%nat 0xed5f0%Z b_0.
  take RB 1%nat 0xed5f8%Z ge2330.
  take RB 1%nat 0xed600%Z ge2338.
  take RB 50%nat 0xed838%Z b_1.
  take RB 3%nat 0xed850%Z ge2578.
  take RB 18%nat 0xed8e0%Z b_2.
  take RB 1%nat 0xed8e8%Z ge2620.
  take RB 15%nat 0xee080%Z b_3.
  take RB 3%nat 0xee08c%Z ge2dc0.
  take RB 1%nat 0xee0a8%Z b_4.
  take RB 6%nat 0xee0d8%Z ge2de8.
  callc seg_spec_18 clearing (clear ST ge2028 ge20a8 ge2330 ge2338 ge2578 ge2620 ge2dc0 ge2de8); [exact ST | lia | lia | lia | exact ge2028 | exact ge20a8 | exact ge2330 | exact ge2338 | exact ge2578 | exact ge2620 | exact ge2dc0 | exact GOT | exact CAN | exact ge2de8 | assumption |].
  rename PC into ST. rename PC0 into ge2028. rename PC1 into ge20a8. rename PC2 into ge2330. rename PC3 into ge2338. rename PC4 into ge2578. rename PC5 into ge2620. rename PC6 into ge2dc0. rename POST into ge2de8.
  glue a_0 ge2028.
  glue a_0 a_1.
  glue a_0 ge20a8.
  glue a_0 RA.
  rename a_0 into RA.
  glue b_0 ge2330.
  glue b_0 ge2338.
  glue b_0 b_1.
  glue b_0 ge2578.
  glue b_0 b_2.
  glue b_0 ge2620.
  glue b_0 b_3.
  glue b_0 ge2dc0.
  glue b_0 b_4.
  glue b_0 ge2de8.
  glue b_0 RB.
  rename b_0 into RB.

  take RA 39%nat 0xed2f8%Z a_0.
  take RA 2%nat 0xed304%Z ge2038.
  take RA 19%nat 0xed368%Z a_1.
  take RA 1%nat 0xed36c%Z ge20a8.
  take RB 43%nat 0xed600%Z b_0.
  take RB 1%nat 0xed608%Z ge2340.
  take RB 1%nat 0xed610%Z ge2348.
  take RB 48%nat 0xed838%Z b_1.
  take RB 3%nat 0xed850%Z ge2578.
  take RB 19%nat 0xed8e8%Z b_2.
  take RB 1%nat 0xed8f0%Z ge2628.
  take RB 14%nat 0xee080%Z b_3.
  take RB 3%nat 0xee08c%Z ge2dc0.
  take RB 1%nat 0xee0a8%Z b_4.
  take RB 6%nat 0xee0d8%Z ge2de8.
  callc seg_spec_19 clearing (clear ST ge2038 ge20a8 ge2340 ge2348 ge2578 ge2628 ge2dc0 ge2de8); [exact ST | lia | lia | lia | exact ge2038 | exact ge20a8 | exact ge2340 | exact ge2348 | exact ge2578 | exact ge2628 | exact ge2dc0 | exact GOT | exact CAN | exact ge2de8 | assumption |].
  rename PC into ST. rename PC0 into ge2038. rename PC1 into ge20a8. rename PC2 into ge2340. rename PC3 into ge2348. rename PC4 into ge2578. rename PC5 into ge2628. rename PC6 into ge2dc0. rename POST into ge2de8.
  glue a_0 ge2038.
  glue a_0 a_1.
  glue a_0 ge20a8.
  glue a_0 RA.
  rename a_0 into RA.
  glue b_0 ge2340.
  glue b_0 ge2348.
  glue b_0 b_1.
  glue b_0 ge2578.
  glue b_0 b_2.
  glue b_0 ge2628.
  glue b_0 b_3.
  glue b_0 ge2dc0.
  glue b_0 b_4.
  glue b_0 ge2de8.
  glue b_0 RB.
  rename b_0 into RB.

  take RA 42%nat 0xed308%Z a_0.
  take RA 2%nat 0xed314%Z ge2048.
  take RA 16%nat 0xed368%Z a_1.
  take RA 1%nat 0xed36c%Z ge20a8.
  take RB 45%nat 0xed610%Z b_0.
  take RB 1%nat 0xed618%Z ge2350.
  take RB 1%nat 0xed620%Z ge2358.
  take RB 46%nat 0xed838%Z b_1.
  take RB 3%nat 0xed850%Z ge2578.
  take RB 20%nat 0xed8f0%Z b_2.
  take RB 1%nat 0xed8f8%Z ge2630.
  take RB 13%nat 0xee080%Z b_3.
  take RB 3%nat 0xee08c%Z ge2dc0.
  take RB 1%nat 0xee0a8%Z b_4.
  take RB 6%nat 0xee0d8%Z ge2de8.
  callc seg_spec_20 clearing (clear ST ge2048 ge20a8 ge2350 ge2358 ge2578 ge2630 ge2dc0 ge2de8); [exact ST | lia | lia | lia | exact ge2048 | exact ge20a8 | exact ge2350 | exact ge2358 | exact ge2578 | exact ge2630 | exact ge2dc0 | exact GOT | exact CAN | exact ge2de8 | assumption |].
  rename PC into ST. rename PC0 into ge2048. rename PC1 into ge20a8. rename PC2 into ge2350. rename PC3 into ge2358. rename PC4 into ge2578. rename PC5 into ge2630. rename PC6 into ge2dc0. rename POST into ge2de8.
  glue a_0 ge2048.
  glue a_0 a_1.
  glue a_0 ge20a8.
  glue a_0 RA.
  rename a_0 into RA.
  glue b_0 ge2350.
  glue b_0 ge2358.
  glue b_0 b_1.
  glue b_0 ge2578.
  glue b_0 b_2.
  glue b_0 ge2630.
  glue b_0 b_3.
  glue b_0 ge2dc0.
  glue b_0 b_4.
  glue b_0 ge2de8.
  glue b_0 RB.
  rename b_0 into RB.

  take RA 45%nat 0xed318%Z a_0.
  take RA 2%nat 0xed324%Z ge2058.
  take RA 13%nat 0xed368%Z a_1.
  take RA 1%nat 0xed36c%Z ge20a8.
  take RB 47%nat 0xed620%Z b_0.
  take RB 1%nat 0xed628%Z ge2360.
  take RB 1%nat 0xed630%Z ge2368.
  take RB 44%nat 0xed838%Z b_1.
  take RB 3%nat 0xed850%Z ge2578.
  take RB 21%nat 0xed8f8%Z b_2.
  take RB 1%nat 0xed900%Z ge2638.
  take RB 12%nat 0xee080%Z b_3.
  take RB 3%nat 0xee08c%Z ge2dc0.
  take RB 1%nat 0xee0a8%Z b_4.
  take RB 6%nat 0xee0d8%Z ge2de8.
  callc seg_spec_21 clearing (clear ST ge2058 ge20a8 ge2360 ge2368 ge2578 ge2638 ge2dc0 ge2de8); [exact ST | lia | lia | lia | exact ge2058 | exact ge20a8 | exact ge2360 | exact ge2368 | exact ge2578 | exact ge2638 | exact ge2dc0 | exact GOT | exact CAN | exact ge2de8 | assumption |].
  rename PC into ST. rename PC0 into ge2058. rename PC1 into ge20a8. rename PC2 into ge2360. rename PC3 into ge2368. rename PC4 into ge2578. rename PC5 into ge2638. rename PC6 into ge2dc0. rename POST into ge2de8.
  glue a_0 ge2058.
  glue a_0 a_1.
  glue a_0 ge20a8.
  glue a_0 RA.
  rename a_0 into RA.
  glue b_0 ge2360.
  glue b_0 ge2368.
  glue b_0 b_1.
  glue b_0 ge2578.
  glue b_0 b_2.
  glue b_0 ge2638.
  glue b_0 b_3.
  glue b_0 ge2dc0.
  glue b_0 b_4.
  glue b_0 ge2de8.
  glue b_0 RB.
  rename b_0 into RB.

  take RA 48%nat 0xed328%Z a_0.
  take RA 2%nat 0xed334%Z ge2068.
  take RA 10%nat 0xed368%Z a_1.
  take RA 1%nat 0xed36c%Z ge20a8.
  take RB 49%nat 0xed630%Z b_0.
  take RB 1%nat 0xed638%Z ge2370.
  take RB 1%nat 0xed640%Z ge2378.
  take RB 42%nat 0xed838%Z b_1.
  take RB 3%nat 0xed850%Z ge2578.
  take RB 22%nat 0xed900%Z b_2.
  take RB 1%nat 0xed908%Z ge2640.
  take RB 11%nat 0xee080%Z b_3.
  take RB 3%nat 0xee08c%Z ge2dc0.
  take RB 1%nat 0xee0a8%Z b_4.
  take RB 6%nat 0xee0d8%Z ge2de8.
  callc seg_spec_22 clearing (clear ST ge2068 ge20a8 ge2370 ge2378 ge2578 ge2640 ge2dc0 ge2de8); [exact ST | lia | lia | lia | exact ge2068 | exact ge20a8 | exact ge2370 | exact ge2378 | exact ge2578 | exact ge2640 | exact ge2dc0 | exact GOT | exact CAN | exact ge2de8 | assumption |].
  rename PC into ST. rename PC0 into ge2068. rename PC1 into ge20a8. rename PC2 into ge2370. rename PC3 into ge2378. rename PC4 into ge2578. rename PC5 into ge2640. rename PC6 into ge2dc0. rename POST into ge2de8.
  glue a_0 ge2068.
  glue a_0 a_1.
  glue a_0 ge20a8.
  glue a_0 RA.
  rename a_0 into RA.
  glue b_0 ge2370.
  glue b_0 ge2378.
  glue b_0 b_1.
  glue b_0 ge2578.
  glue b_0 b_2.
  glue b_0 ge2640.
  glue b_0 b_3.
  glue b_0 ge2dc0.
  glue b_0 b_4.
  glue b_0 ge2de8.
  glue b_0 RB.
  rename b_0 into RB.

  take RA 51%nat 0xed338%Z a_0.
  take RA 2%nat 0xed344%Z ge2078.
  take RA 7%nat 0xed368%Z a_1.
  take RA 1%nat 0xed36c%Z ge20a8.
  take RB 51%nat 0xed640%Z b_0.
  take RB 1%nat 0xed648%Z ge2380.
  take RB 1%nat 0xed650%Z ge2388.
  take RB 40%nat 0xed838%Z b_1.
  take RB 3%nat 0xed850%Z ge2578.
  take RB 23%nat 0xed908%Z b_2.
  take RB 1%nat 0xed910%Z ge2648.
  take RB 10%nat 0xee080%Z b_3.
  take RB 3%nat 0xee08c%Z ge2dc0.
  take RB 1%nat 0xee0a8%Z b_4.
  take RB 6%nat 0xee0d8%Z ge2de8.
  callc seg_spec_23 clearing (clear ST ge2078 ge20a8 ge2380 ge2388 ge2578 ge2648 ge2dc0 ge2de8); [exact ST | lia | lia | lia | exact ge2078 | exact ge20a8 | exact ge2380 | exact ge2388 | exact ge2578 | exact ge2648 | exact ge2dc0 | exact GOT | exact CAN | exact ge2de8 | assumption |].
  rename PC into ST. rename PC0 into ge2078. rename PC1 into ge20a8. rename PC2 into ge2380. rename PC3 into ge2388. rename PC4 into ge2578. rename PC5 into ge2648. rename PC6 into ge2dc0. rename POST into ge2de8.
  glue a_0 ge2078.
  glue a_0 a_1.
  glue a_0 ge20a8.
  glue a_0 RA.
  rename a_0 into RA.
  glue b_0 ge2380.
  glue b_0 ge2388.
  glue b_0 b_1.
  glue b_0 ge2578.
  glue b_0 b_2.
  glue b_0 ge2648.
  glue b_0 b_3.
  glue b_0 ge2dc0.
  glue b_0 b_4.
  glue b_0 ge2de8.
  glue b_0 RB.
  rename b_0 into RB.

  take RA 18%nat 0xed288%Z a_0.
  take RA 2%nat 0xed294%Z ge1fc8.
  take RA 40%nat 0xed368%Z a_1.
  take RA 1%nat 0xed36c%Z ge20a8.
  take RB 61%nat 0xed6e8%Z b_0.
  take RB 1%nat 0xed6f0%Z ge2428.
  take RB 1%nat 0xed6f8%Z ge2430.
  take RB 1%nat 0xed700%Z ge2438.
  take RB 29%nat 0xed838%Z b_1.
  take RB 3%nat 0xed850%Z ge2578.
  take RB 24%nat 0xed910%Z b_2.
  take RB 1%nat 0xed918%Z ge2650.
  take RB 9%nat 0xee080%Z b_3.
  take RB 3%nat 0xee08c%Z ge2dc0.
  take RB 1%nat 0xee0a8%Z b_4.
  take RB 6%nat 0xee0d8%Z ge2de8.
  callc seg_spec_24 clearing (clear ST ge1fc8 ge20a8 ge2428 ge2430 ge2438 ge2578 ge2650 ge2dc0 ge2de8); [exact ST | lia | lia | lia | exact ge1fc8 | exact ge20a8 | exact ge2428 | exact ge2430 | exact ge2438 | exact ge2578 | exact ge2650 | exact ge2dc0 | exact GOT | exact CAN | exact ge2de8 | assumption |].
  rename PC into ST. rename PC0 into ge1fc8. rename PC1 into ge20a8. rename PC2 into ge2428. rename PC3 into ge2430. rename PC4 into ge2438. rename PC5 into ge2578. rename PC6 into ge2650. rename PC7 into ge2dc0. rename POST into ge2de8.
  glue a_0 ge1fc8.
  glue a_0 a_1.
  glue a_0 ge20a8.
  glue a_0 RA.
  rename a_0 into RA.
  glue b_0 ge2428.
  glue b_0 ge2430.
  glue b_0 ge2438.
  glue b_0 b_1.
  glue b_0 ge2578.
  glue b_0 b_2.
  glue b_0 ge2650.
  glue b_0 b_3.
  glue b_0 ge2dc0.
  glue b_0 b_4.
  glue b_0 ge2de8.
  glue b_0 RB.
  rename b_0 into RB.

  take RA 21%nat 0xed298%Z a_0.
  take RA 2%nat 0xed2a4%Z ge1fd8.
  take RA 37%nat 0xed368%Z a_1.
  take RA 1%nat 0xed36c%Z ge20a8.
  take RB 64%nat 0xed700%Z b_0.
  take RB 1%nat 0xed708%Z ge2440.
  take RB 1%nat 0xed710%Z ge2448.
  take RB 1%nat 0xed718%Z ge2450.
  take RB 26%nat 0xed838%Z b_1.
  take RB 3%nat 0xed850%Z ge2578.
  take RB 25%nat 0xed918%Z b_2.
  take RB 1%nat 0xed920%Z ge2658.
  take RB 8%nat 0xee080%Z b_3.
  take RB 3%nat 0xee08c%Z ge2dc0.
  take RB 1%nat 0xee0a8%Z b_4.
  take RB 6%nat 0xee0d8%Z ge2de8.
  callc seg_spec_25 clearing (clear ST ge1fd8 ge20a8 ge2440 ge2448 ge2450 ge2578 ge2658 ge2dc0 ge2de8); [exact ST | lia | lia | lia | exact ge1fd8 | exact ge20a8 | exact ge2440 | exact ge2448 | exact ge2450 | exact ge2578 | exact ge2658 | exact ge2dc0 | exact GOT | exact CAN | exact ge2de8 | assumption |].
  rename PC into ST. rename PC0 into ge1fd8. rename PC1 into ge20a8. rename PC2 into ge2440. rename PC3 into ge2448. rename PC4 into ge2450. rename PC5 into ge2578. rename PC6 into ge2658. rename PC7 into ge2dc0. rename POST into ge2de8.
  glue a_0 ge1fd8.
  glue a_0 a_1.
  glue a_0 ge20a8.
  glue a_0 RA.
  rename a_0 into RA.
  glue b_0 ge2440.
  glue b_0 ge2448.
  glue b_0 ge2450.
  glue b_0 b_1.
  glue b_0 ge2578.
  glue b_0 b_2.
  glue b_0 ge2658.
  glue b_0 b_3.
  glue b_0 ge2dc0.
  glue b_0 b_4.
  glue b_0 ge2de8.
  glue b_0 RB.
  rename b_0 into RB.

  take RA 24%nat 0xed2a8%Z a_0.
  take RA 2%nat 0xed2b4%Z ge1fe8.
  take RA 34%nat 0xed368%Z a_1.
  take RA 1%nat 0xed36c%Z ge20a8.
  take RA 20%nat 0xed3f0%Z a_2.
  take RA 1%nat 0xed3f8%Z ge2130.
  take RA 1%nat 0xed3f9%Z ge2138.
  take RB 67%nat 0xed718%Z b_0.
  take RB 1%nat 0xed720%Z ge2458.
  take RB 1%nat 0xed728%Z ge2460.
  take RB 1%nat 0xed730%Z ge2468.
  take RB 23%nat 0xed838%Z b_1.
  take RB 3%nat 0xed850%Z ge2578.
  take RB 26%nat 0xed920%Z b_2.
  take RB 1%nat 0xed928%Z ge2660.
  take RB 7%nat 0xee080%Z b_3.
  take RB 3%nat 0xee08c%Z ge2dc0.
  take RB 1%nat 0xee0a8%Z b_4.
  take RB 6%nat 0xee0d8%Z ge2de8.
  callc seg_spec_26 clearing (clear ST ge1fe8 ge20a8 ge2458 ge2460 ge2468 ge2578 ge2660 ge2dc0 ge2de8); [exact ST | lia | lia | lia | exact ge1fe8 | exact ge20a8 | exact ge2458 | exact ge2460 | exact ge2468 | exact ge2578 | exact ge2660 | exact ge2dc0 | exact ge2130 | exact ge2138 | exact GOT | exact CAN | exact ge2de8 | assumption |].
  rename PC into ST. rename PC0 into ge1fe8. rename PC1 into ge20a8. rename PC2 into ge2458. rename PC3 into ge2460. rename PC4 into ge2468. rename PC5 into ge2578. rename PC6 into ge2660. rename PC7 into ge2dc0. rename POST into ge2de8.
  glue a_0 ge1fe8.
  glue a_0 a_1.
  glue a_0 ge20a8.
  glue a_0 a_2.
  glue a_0 ge2130.
  glue a_0 ge2138.
  glue a_0 RA.
  rename a_0 into RA.
  glue b_0 ge2458.
  glue b_0 ge2460.
  glue b_0 ge2468.
  glue b_0 b_1.
  glue b_0 ge2578.
  glue b_0 b_2.
  glue b_0 ge2660.
  glue b_0 b_3.
  glue b_0 ge2dc0.
  glue b_0 b_4.
  glue b_0 ge2de8.
  glue b_0 RB.
  rename b_0 into RB.

  take RA 27%nat 0xed2b8%Z a_0.
  take RA 2%nat 0xed2c4%Z ge1ff8.
  take RA 31%nat 0xed368%Z a_1.
  take RA 1%nat 0xed36c%Z ge20a8.
  take RA 20%nat 0xed3f0%Z a_2.
  take RA 1%nat 0xed3f8%Z ge2130.
  take RA 1%nat 0xed3f9%Z ge2138.
  take RB 70%nat 0xed730%Z b_0.
  take RB 1%nat 0xed738%Z ge2470.
  take RB 1%nat 0xed740%Z ge2478.
  take RB 1%nat 0xed748%Z ge2480.
  take RB 20%nat 0xed838%Z b_1.
  take RB 3%nat 0xed850%Z ge2578.
  take RB 27%nat 0xed928%Z b_2.
  take RB 1%nat 0xed930%Z ge2668.
  take RB 6%nat 0xee080%Z b_3.
  take RB 3%nat 0xee08c%Z ge2dc0.
  take RB 1%nat 0xee0a8%Z b_4.
  take RB 6%nat 0xee0d8%Z ge2de8.
  callc seg_spec_27 clearing (clear ST ge1ff8 ge20a8 ge2470 ge2478 ge2480 ge2578 ge2668 ge2dc0 ge2de8); [exact ST | lia | lia | lia | exact ge1ff8 | exact ge20a8 | exact ge2470 | exact ge2478 | exact ge2480 | exact ge2578 | exact ge2668 | exact ge2dc0 | exact ge2130 | exact ge2138 | exact GOT | exact CAN | exact ge2de8 | assumption |].
  rename PC into ST. rename PC0 into ge1ff8. rename PC1 into ge20a8. rename PC2 into ge2470. rename PC3 into ge2478. rename PC4 into ge2480. rename PC5 into ge2578. rename PC6 into ge2668. rename PC7 into ge2dc0. rename POST into ge2de8.
  glue a_0 ge1ff8.
  glue a_0 a_1.
  glue a_0 ge20a8.
  glue a_0 a_2.
  glue a_0 ge2130.
  glue a_0 ge2138.
  glue a_0 RA.
  rename a_0 into RA.
  glue b_0 ge2470.
  glue b_0 ge2478.
  glue b_0 ge2480.
  glue b_0 b_1.
  glue b_0 ge2578.
  glue b_0 b_2.
  glue b_0 ge2668.
  glue b_0 b_3.
  glue b_0 ge2dc0.
  glue b_0 b_4.
  glue b_0 ge2de8.
  glue b_0 RB.
  rename b_0 into RB.

  take RA 54%nat 0xed348%Z a_0.
  take RA 2%nat 0xed354%Z ge2088.
  take RA 4%nat 0xed368%Z a_1.
  take RA 1%nat 0xed36c%Z ge20a8.
  take RB 53%nat 0xed650%Z b_0.
  take RB 1%nat 0xed658%Z ge2390.
  take RB 1%nat 0xed660%Z ge2398.
  take RB 38%nat 0xed838%Z b_1.
  take RB 3%nat 0xed850%Z ge2578.
  take RB 28%nat 0xed930%Z b_2.
  take RB 1%nat 0xed938%Z ge2670.
  take RB 5%nat 0xee080%Z b_3.
  take RB 3%nat 0xee08c%Z ge2dc0.
  take RB 1%nat 0xee0a8%Z b_4.
  take RB 6%nat 0xee0d8%Z ge2de8.
  callc seg_spec_28 clearing (clear ST ge2088 ge20a8 ge2390 ge2398 ge2578 ge2670 ge2dc0 ge2de8); [exact ST | lia | lia | lia | exact ge2088 | exact ge20a8 | exact ge2390 | exact ge2398 | exact ge2578 | exact ge2670 | exact ge2dc0 | exact GOT | exact CAN | exact ge2de8 | assumption |].
  rename PC into ST. rename PC0 into ge2088. rename PC1 into ge20a8. rename PC2 into ge2390. rename PC3 into ge2398. rename PC4 into ge2578. rename PC5 into ge2670. rename PC6 into ge2dc0. rename POST into ge2de8.
  glue a_0 ge2088.
  glue a_0 a_1.
  glue a_0 ge20a8.
  glue a_0 RA.
  rename a_0 into RA.
  glue b_0 ge2390.
  glue b_0 ge2398.
  glue b_0 b_1.
  glue b_0 ge2578.
  glue b_0 b_2.
  glue b_0 ge2670.
  glue b_0 b_3.
  glue b_0 ge2dc0.
  glue b_0 b_4.
  glue b_0 ge2de8.
  glue b_0 RB.
  rename b_0 into RB.

  take RA 57%nat 0xed358%Z a_0.
  take RA 2%nat 0xed364%Z ge2098.
  take RA 1%nat 0xed368%Z a_1.
  take RA 1%nat 0xed36c%Z ge20a8.
  take RB 55%nat 0xed660%Z b_0.
  take RB 1%nat 0xed668%Z ge23a0.
  take RB 1%nat 0xed670%Z ge23a8.
  take RB 36%nat 0xed838%Z b_1.
  take RB 3%nat 0xed850%Z ge2578.
  take RB 29%nat 0xed938%Z b_2.
  take RB 1%nat 0xed940%Z ge2678.
  take RB 4%nat 0xee080%Z b_3.
  take RB 3%nat 0xee08c%Z ge2dc0.
  take RB 1%nat 0xee0a8%Z b_4.
  take RB 6%nat 0xee0d8%Z ge2de8.
  callc seg_spec_29 clearing (clear ST ge2098 ge20a8 ge23a0 ge23a8 ge2578 ge2678 ge2dc0 ge2de8); [exact ST | lia | lia | lia | exact ge2098 | exact ge20a8 | exact ge23a0 | exact ge23a8 | exact ge2578 | exact ge2678 | exact ge2dc0 | exact GOT | exact CAN | exact ge2de8 | assumption |].
  rename PC into ST. rename PC0 into ge2098. rename PC1 into ge20a8. rename PC2 into ge23a0. rename PC3 into ge23a8. rename PC4 into ge2578. rename PC5 into ge2678. rename PC6 into ge2dc0. rename POST into ge2de8.
  glue a_0 ge2098.
  glue a_0 a_1.
  glue a_0 ge20a8.
  glue a_0 RA.
  rename a_0 into RA.
  glue b_0 ge23a0.
  glue b_0 ge23a8.
  glue b_0 b_1.
  glue b_0 ge2578.
  glue b_0 b_2.
  glue b_0 ge2678.
  glue b_0 b_3.
  glue b_0 ge2dc0.
  glue b_0 b_4.
  glue b_0 ge2de8.
  glue b_0 RB.
  rename b_0 into RB.
  rewrite Hsp in ST. subst sp0.
  pj_carry FR MUF WMF. clear MUF WMF.

  do 7 lstep.
  release_frame FR ST (bv_unsigned sp).

  merge_at RB 99%nat 41%nat.
  merge_at RB 95%nat 3%nat.
  merge_at RB 74%nat 19%nat.
  merge_at RB 6%nat 67%nat.
  merge_at RB 0%nat 4%nat.
  merge_at RA 0%nat 85%nat.
  unfold imp_ctor_post, impb_B. sys_finish; eassumption.
Qed.
