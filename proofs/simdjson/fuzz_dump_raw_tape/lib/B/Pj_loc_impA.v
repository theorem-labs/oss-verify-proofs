(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump_raw_tape.lib.AS Require Import ShapeAlg AsanAcct.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump_raw_tape.lib.Lib Require Import Tac Arr Bytes ITree Nodes Decode SysStep RegsEquiv ImageA RzCPS StoreFast FP.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump_raw_tape.lib.Spec Require Import Prelim StrFun.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump_raw_tape.lib.P Require Import Str_tac Startup_glue Pj_steps Pj_loc_kit.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump_raw_tape.lib.A Require Import Shadow IcptSpec.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump_raw_tape.lib.B Require Import Layout RT_iface RT_iface2 D_defs D_kit D_clx D_rlkit D_libiface Sj_rtf Sj_akit Sj_acps Sj_hkit Sj_new Sj_num_akit Sj_num_amem Pj_mciA Pj_loc_akitA Pj_onceA Pj_loc_newlocA Pj_loc_i00A Pj_loc_i01A Pj_loc_i02A Pj_loc_i03A Pj_loc_i04A Pj_loc_i05A Pj_loc_i06A Pj_loc_i07A Pj_loc_i08A Pj_loc_i09A Pj_loc_i10A Pj_loc_i11A Pj_loc_i12A Pj_loc_i13A Pj_loc_i14A Pj_loc_i15A Pj_loc_i16A Pj_loc_i17A Pj_loc_i18A Pj_loc_i19A Pj_loc_i20A Pj_loc_i21A Pj_loc_i22A Pj_loc_i23A Pj_loc_i24A Pj_loc_i25A Pj_loc_i26A Pj_loc_i27A Pj_loc_i28A Pj_loc_i29A.
From OssFuzzTheorems.simdjson.fuzz_dump_raw_tape.images Require Import AsanUbsan.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump_raw_tape.lib.B Require Import Layout.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump_raw_tape.lib.Lib Require Import StoreFast.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.
Import ListNotations.
Open Scope bv_scope.

Definition imp0_A : list cell := [CB 472 (repeat (Z_to_bv 8 0) 472)].
Definition imp0_B : list cell := [CB 3256 (repeat (Z_to_bv 8 0) 3256)].
Definition impb_A (ja1 ja2 ja3 : list byte) : list cell :=
  [CB 64 ja1;
   C8 (Z_to_bv 64 18446744073709551615);
   C4 (Z_to_bv 64 15);
   CB 380 ja2;
   C8 (Z_to_bv 64 0x33380);
   C1 (Z_to_bv 8 1); C1 (Z_to_bv 8 1);
   CB 6 ja3].
Definition impb_B (jb1 jb2 jb3 jb4 jb5 jb6 jb6b jb6c jb7 jb8 jb9 jb10 : list byte) : list cell :=
  [CB 192 jb1;
   C8 (Z_to_bv 64 18446744073709551615);
   C4 (Z_to_bv 64 3);
   CB 4 jb2;
   C8 (Z_to_bv 64 18446744073709551615);
   C4 (Z_to_bv 64 11);
   CB 180 jb3;
   C8 (Z_to_bv 64 0x16d120);
   CB 400 jb4;
   C8 (Z_to_bv 64 0x16c558);
   CB 120 jb5;
   C8 (Z_to_bv 64 0x16c710);
   CB 8 jb6;
   C2 (Z_to_bv 64 11310);
   CB 6 jb6b;
   C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0);
   CB 64 jb6c;
   C8 (Z_to_bv 64 0x6aac50);
   C8 (Z_to_bv 64 0x6aad40);
   CB 24 jb7;
   C8 (Z_to_bv 64 0x6aab48);
   CB 56 jb8;
   C8 (Z_to_bv 64 0x6aabc8);
   CB 24 jb9;
   C8 (Z_to_bv 64 0x6aa9b0);
   CB 2064 jb10].

Section AevtPieces.
Variable RT : rt_sig.
Hypothesis AF : art_facts RT.
Hypothesis RTC : rt_contracts RT.
Hypothesis MCI : memcmp_inner_icontract RT.
Variable PMc : Model -> Prop.
Hypothesis FDO : fdfs_only PMc.
Hypothesis MST : mat_stable PMc.

Definition imp_ctor_postA (Σ : rts RT) (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word)
    (fc : bv 32) (lo : Z) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists (t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (F : bvmap 5 word) ja1 ja2 ja3 jb1 jb2 jb3 jb4 jb5 jb6 jb6b jb6c jb7 jb8 jb9 jb10 (m' : mem),
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom bsegs)
    /\ rt_pres_fp (rt_live RT Σ) (rt_frames RT Σ) (bv_unsigned sp) [(0x6aa628, 0x6aa800); (0x6aa820, 0x6ab4d8)]%Z m m'
    /\ wmono bsegs m m' /\ mem_inv bsegs m' /\ ART RT Σ m'
    /\ (stk bsegs m' lo (bv_unsigned sp)
    /\ rw_cells bsegs m' 0x6aa628 (impb_A ja1 ja2 ja3)
    /\ rw_cells bsegs m' 0x6aa820 (impb_B jb1 jb2 jb3 jb4 jb5 jb6 jb6b jb6c jb7 jb8 jb9 jb10)).

Lemma imp_ctor_aevt : forall Σ K ra sp gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (lo : Z) (canary : word),
  stk bsegs m lo (bv_unsigned sp) -> (lo + 544 + RT_STACK <= bv_unsigned sp)%Z -> (rt_sp0 RT Σ - STACK_WIN <= lo)%Z ->
  (bv_unsigned sp + 16 <= USTACK_TOP)%Z -> (bv_unsigned sp mod 16 = 0)%Z -> (bv_unsigned sp < 2^62)%Z ->
  rw_cells bsegs m 0x6aa628 imp0_A -> rw_cells bsegs m 0x6aa820 imp0_B ->
  ro_cells bsegs m 0x16f508 [C8 (Z_to_bv 64 0x6cbe28)] -> ro_cells bsegs m 0x6cbe28 [C8 canary] ->
  ro_cells bsegs m 0x6cc07b [C1 (Z_to_bv 8 0)] -> rw_cells bsegs m 0x6cc158 [C4 (Z_to_bv 64 0)] -> mem_inv bsegs m -> ART RT Σ m ->
  (forall ms', imp_ctor_postA Σ ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 fc lo m ms' -> aevt RT PMc Σ K ms') ->
  aevt RT PMc Σ K (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 0x6aac28) (Z_to_bv 64 1) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x12d0f0) fc None m (seg_rom bsegs)).
Proof using AF RTC MCI FDO MST.
  intros until canary. intros ST LO LOR SPT SPA HI RA RB GOT CAN NL LK MI ART0 HK.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  pose proof (munch_refl [(bv_unsigned sp - 544, bv_unsigned sp); (0x6aa628, 0x6aa800); (0x6aa820, 0x6ab4d8)]%Z m) as MU.
  pose proof (wmono_refl bsegs m) as WM.
  astart (bv_unsigned sp) [(0x6aa628, 0x6aa800); (0x6aa820, 0x6ab4d8)]%Z.
  apply (aevt_evt RT AF PMc MST).
  unfold imp0_A in RA. unfold imp0_B in RB.
  retype RA [C8 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); CB 4 (repeat (Z_to_bv 8 0) 4); C8 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); CB 4 (repeat (Z_to_bv 8 0) 4); C8 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); CB 4 (repeat (Z_to_bv 8 0) 4); C8 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); CB 4 (repeat (Z_to_bv 8 0) 4); C8 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); CB 4 (repeat (Z_to_bv 8 0) 4); C8 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); CB 4 (repeat (Z_to_bv 8 0) 4); C8 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); CB 4 (repeat (Z_to_bv 8 0) 4); C8 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); CB 4 (repeat (Z_to_bv 8 0) 4); C8 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); CB 4 (repeat (Z_to_bv 8 0) 4); C8 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); CB 4 (repeat (Z_to_bv 8 0) 4); C8 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); CB 4 (repeat (Z_to_bv 8 0) 4); C8 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); CB 4 (repeat (Z_to_bv 8 0) 4); C8 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); CB 4 (repeat (Z_to_bv 8 0) 4); C8 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); CB 4 (repeat (Z_to_bv 8 0) 4); C8 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); CB 4 (repeat (Z_to_bv 8 0) 4); C8 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); CB 4 (repeat (Z_to_bv 8 0) 4); C8 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); CB 4 (repeat (Z_to_bv 8 0) 4); C8 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); CB 4 (repeat (Z_to_bv 8 0) 4); C8 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); CB 4 (repeat (Z_to_bv 8 0) 4); C8 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); CB 4 (repeat (Z_to_bv 8 0) 4); C4 (Z_to_bv 64 0); CB 4 (repeat (Z_to_bv 8 0) 4); C8 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); CB 4 (repeat (Z_to_bv 8 0) 4); C8 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); CB 4 (repeat (Z_to_bv 8 0) 4); C8 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); CB 4 (repeat (Z_to_bv 8 0) 4); C8 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); CB 4 (repeat (Z_to_bv 8 0) 4); C8 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); CB 4 (repeat (Z_to_bv 8 0) 4); C8 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); CB 4 (repeat (Z_to_bv 8 0) 4); CB 32 (repeat (Z_to_bv 8 0) 32); C8 (Z_to_bv 64 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); CB 6 (repeat (Z_to_bv 8 0) 6)].
  retype RB [CB 176 (repeat (Z_to_bv 8 0) 176); C8 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); CB 4 (repeat (Z_to_bv 8 0) 4); C8 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); CB 4 (repeat (Z_to_bv 8 0) 4); C8 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); CB 4 (repeat (Z_to_bv 8 0) 4); C8 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); CB 4 (repeat (Z_to_bv 8 0) 4); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); CB 96 (repeat (Z_to_bv 8 0) 96); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C1 (Z_to_bv 8 0); CB 103 (repeat (Z_to_bv 8 0) 103); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C2 (Z_to_bv 64 0); CB 6 (repeat (Z_to_bv 8 0) 6); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); CB 240 (repeat (Z_to_bv 8 0) 240); C8 (Z_to_bv 64 0); C2 (Z_to_bv 64 0); C1 (Z_to_bv 8 0); CB 1845 (repeat (Z_to_bv 8 0) 1845); CB 4 (repeat (Z_to_bv 8 0) 4); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); CB 28 (repeat (Z_to_bv 8 0) 28); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); CB 16 (repeat (Z_to_bv 8 0) 16); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)].

  take RA 2%nat 0x6aa634%Z ge1f68.
  take RA 58%nat 0x6aa768%Z a_0.
  take RA 1%nat 0x6aa76c%Z ge20a8.
  take RB 13%nat 0x6aa910%Z b_0.
  take RB 1%nat 0x6aa918%Z ge2250.
  take RB 1%nat 0x6aa920%Z ge2258.
  take RB 76%nat 0x6aac28%Z b_1.
  take RB 2%nat 0x6aac38%Z ge2568.
  take RB 3%nat 0x6aac50%Z ge2578.
  take RB 1%nat 0x6aad40%Z ge2590.
  take RB 3%nat 0x6aad4b%Z ge2680.
  take RB 1%nat 0x6ab480%Z b_2.
  take RB 3%nat 0x6ab48c%Z ge2dc0.
  take RB 1%nat 0x6ab4a8%Z b_3.
  take RB 6%nat 0x6ab4d8%Z ge2de8.
  acall (seg_aevt_0 RT AF RTC MCI PMc FDO MST Σ); [exact ST | a_ul | exact LOR | a_ul | a_mod16 | lia | exact ge1f68 | exact ge20a8 | exact ge2250 | exact ge2258 | exact ge2568 | exact ge2578 | exact ge2590 | exact ge2680 | exact ge2dc0 | exact GOT | exact CAN | exact ge2de8 | assumption | exact ARTX | clear ST ge1f68 ge20a8 ge2250 ge2258 ge2568 ge2578 ge2590 ge2680 ge2dc0 ge2de8; apost_call].
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

  take RA 3%nat 0x6aa638%Z a_0.
  take RA 2%nat 0x6aa644%Z ge1f78.
  take RA 55%nat 0x6aa768%Z a_1.
  take RA 1%nat 0x6aa76c%Z ge20a8.
  take RB 15%nat 0x6aa920%Z b_0.
  take RB 1%nat 0x6aa928%Z ge2260.
  take RB 1%nat 0x6aa930%Z ge2268.
  take RB 76%nat 0x6aac38%Z b_1.
  take RB 3%nat 0x6aac50%Z ge2578.
  take RB 1%nat 0x6aac58%Z b_2.
  take RB 1%nat 0x6aac60%Z ge2598.
  take RB 32%nat 0x6ab480%Z b_3.
  take RB 3%nat 0x6ab48c%Z ge2dc0.
  take RB 1%nat 0x6ab4a8%Z b_4.
  take RB 6%nat 0x6ab4d8%Z ge2de8.
  acall (seg_aevt_1 RT AF RTC MCI PMc FDO MST Σ); [exact ST | a_ul | exact LOR | a_ul | a_mod16 | lia | exact ge1f78 | exact ge20a8 | exact ge2260 | exact ge2268 | exact ge2578 | exact ge2598 | exact ge2dc0 | exact GOT | exact CAN | exact ge2de8 | assumption | exact ARTX | clear ST ge1f78 ge20a8 ge2260 ge2268 ge2578 ge2598 ge2dc0 ge2de8; apost_call].
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

  take RA 60%nat 0x6aa768%Z a_0.
  take RA 1%nat 0x6aa76c%Z ge20a8.
  take RB 4%nat 0x6aa8e0%Z b_0.
  take RB 2%nat 0x6aa8ec%Z ge2220.
  take RB 67%nat 0x6aab48%Z b_1.
  take RB 1%nat 0x6aab50%Z ge2488.
  take RB 1%nat 0x6aab58%Z ge2490.
  take RB 1%nat 0x6aab60%Z ge2498.
  take RB 1%nat 0x6aab61%Z ge24a0.
  take RB 16%nat 0x6aac38%Z b_2.
  take RB 3%nat 0x6aac50%Z ge2578.
  take RB 2%nat 0x6aac60%Z b_3.
  take RB 1%nat 0x6aac68%Z ge25a0.
  take RB 31%nat 0x6ab480%Z b_4.
  take RB 3%nat 0x6ab48c%Z ge2dc0.
  take RB 1%nat 0x6ab4a8%Z b_5.
  take RB 6%nat 0x6ab4d8%Z ge2de8.
  acall (seg_aevt_2 RT AF RTC MCI PMc FDO MST Σ); [exact ST | a_ul | exact LOR | a_ul | a_mod16 | lia | exact ge2220 | exact ge20a8 | exact ge2488 | exact ge2490 | exact ge2498 | exact ge24a0 | exact ge2578 | exact ge25a0 | exact ge2dc0 | exact GOT | exact CAN | exact ge2de8 | assumption | exact ARTX | clear ST ge2220 ge20a8 ge2488 ge2490 ge2498 ge24a0 ge2578 ge25a0 ge2dc0 ge2de8; apost_call].
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

  take RA 60%nat 0x6aa768%Z a_0.
  take RA 1%nat 0x6aa76c%Z ge20a8.
  take RB 1%nat 0x6aa8d0%Z b_0.
  take RB 2%nat 0x6aa8dc%Z ge2210.
  take RB 14%nat 0x6aa930%Z b_1.
  take RB 1%nat 0x6aa938%Z ge2270.
  take RB 1%nat 0x6aa940%Z ge2278.
  take RB 74%nat 0x6aac38%Z b_2.
  take RB 3%nat 0x6aac50%Z ge2578.
  take RB 3%nat 0x6aac68%Z b_3.
  take RB 1%nat 0x6aac70%Z ge25a8.
  take RB 30%nat 0x6ab480%Z b_4.
  take RB 3%nat 0x6ab48c%Z ge2dc0.
  take RB 1%nat 0x6ab4a8%Z b_5.
  take RB 6%nat 0x6ab4d8%Z ge2de8.
  acall (seg_aevt_3 RT AF RTC MCI PMc FDO MST Σ); [exact ST | a_ul | exact LOR | a_ul | a_mod16 | lia | exact ge2210 | exact ge20a8 | exact ge2270 | exact ge2278 | exact ge2578 | exact ge25a8 | exact ge2dc0 | exact GOT | exact CAN | exact ge2de8 | assumption | exact ARTX | clear ST ge2210 ge20a8 ge2270 ge2278 ge2578 ge25a8 ge2dc0 ge2de8; apost_call].
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

  take RA 60%nat 0x6aa768%Z a_0.
  take RA 1%nat 0x6aa76c%Z ge20a8.
  take RA 1%nat 0x6aa770%Z a_1.
  take RA 2%nat 0x6aa77c%Z ge20b0.
  take RB 19%nat 0x6aa940%Z b_0.
  take RB 1%nat 0x6aa948%Z ge2280.
  take RB 1%nat 0x6aa950%Z ge2288.
  take RB 72%nat 0x6aac38%Z b_1.
  take RB 3%nat 0x6aac50%Z ge2578.
  take RB 4%nat 0x6aac70%Z b_2.
  take RB 1%nat 0x6aac78%Z ge25b0.
  take RB 29%nat 0x6ab480%Z b_3.
  take RB 3%nat 0x6ab48c%Z ge2dc0.
  take RB 1%nat 0x6ab4a8%Z b_4.
  take RB 6%nat 0x6ab4d8%Z ge2de8.
  acall (seg_aevt_4 RT AF RTC MCI PMc FDO MST Σ); [exact ST | a_ul | exact LOR | a_ul | a_mod16 | lia | exact ge20b0 | exact ge20a8 | exact ge2280 | exact ge2288 | exact ge2578 | exact ge25b0 | exact ge2dc0 | exact GOT | exact CAN | exact ge2de8 | assumption | exact ARTX | clear ST ge20b0 ge20a8 ge2280 ge2288 ge2578 ge25b0 ge2dc0 ge2de8; apost_call].
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

  take RA 60%nat 0x6aa768%Z a_0.
  take RA 1%nat 0x6aa76c%Z ge20a8.
  take RA 4%nat 0x6aa780%Z a_1.
  take RA 2%nat 0x6aa78c%Z ge20c0.
  take RA 14%nat 0x6aa7f0%Z a_2.
  take RA 1%nat 0x6aa7f8%Z ge2130.
  take RA 2%nat 0x6aa7fa%Z ge2138.
  take RB 58%nat 0x6aaad0%Z b_0.
  take RB 1%nat 0x6aaad8%Z ge2410.
  take RB 1%nat 0x6aaae0%Z ge2418.
  take RB 1%nat 0x6aaae8%Z ge2420.
  take RB 32%nat 0x6aac38%Z b_1.
  take RB 3%nat 0x6aac50%Z ge2578.
  take RB 5%nat 0x6aac78%Z b_2.
  take RB 1%nat 0x6aac80%Z ge25b8.
  take RB 28%nat 0x6ab480%Z b_3.
  take RB 3%nat 0x6ab48c%Z ge2dc0.
  take RB 1%nat 0x6ab4a8%Z b_4.
  take RB 6%nat 0x6ab4d8%Z ge2de8.
  acall (seg_aevt_5 RT AF RTC MCI PMc FDO MST Σ); [exact ST | a_ul | exact LOR | a_ul | a_mod16 | lia | exact ge20c0 | exact ge20a8 | exact ge2130 | exact ge2138 | exact ge2410 | exact ge2418 | exact ge2420 | exact ge2578 | exact ge25b8 | exact ge2dc0 | exact GOT | exact CAN | exact NL | exact LK | exact ge2de8 | assumption | exact ARTX | clear ST ge20c0 ge20a8 ge2130 ge2138 ge2410 ge2418 ge2420 ge2578 ge25b8 ge2dc0 ge2de8; apost_call].
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

  take RA 60%nat 0x6aa768%Z a_0.
  take RA 1%nat 0x6aa76c%Z ge20a8.
  take RA 7%nat 0x6aa790%Z a_1.
  take RA 2%nat 0x6aa79c%Z ge20d0.
  take RB 21%nat 0x6aa950%Z b_0.
  take RB 1%nat 0x6aa958%Z ge2290.
  take RB 1%nat 0x6aa960%Z ge2298.
  take RB 70%nat 0x6aac38%Z b_1.
  take RB 3%nat 0x6aac50%Z ge2578.
  take RB 6%nat 0x6aac80%Z b_2.
  take RB 1%nat 0x6aac88%Z ge25c0.
  take RB 27%nat 0x6ab480%Z b_3.
  take RB 3%nat 0x6ab48c%Z ge2dc0.
  take RB 1%nat 0x6ab4a8%Z b_4.
  take RB 6%nat 0x6ab4d8%Z ge2de8.
  acall (seg_aevt_6 RT AF RTC MCI PMc FDO MST Σ); [exact ST | a_ul | exact LOR | a_ul | a_mod16 | lia | exact ge20d0 | exact ge20a8 | exact ge2290 | exact ge2298 | exact ge2578 | exact ge25c0 | exact ge2dc0 | exact GOT | exact CAN | exact ge2de8 | assumption | exact ARTX | clear ST ge20d0 ge20a8 ge2290 ge2298 ge2578 ge25c0 ge2dc0 ge2de8; apost_call].
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

  take RA 60%nat 0x6aa768%Z a_0.
  take RA 1%nat 0x6aa76c%Z ge20a8.
  take RA 13%nat 0x6aa7b0%Z a_1.
  take RA 2%nat 0x6aa7bc%Z ge20f0.
  take RB 23%nat 0x6aa960%Z b_0.
  take RB 1%nat 0x6aa968%Z ge22a0.
  take RB 1%nat 0x6aa970%Z ge22a8.
  take RB 68%nat 0x6aac38%Z b_1.
  take RB 3%nat 0x6aac50%Z ge2578.
  take RB 7%nat 0x6aac88%Z b_2.
  take RB 1%nat 0x6aac90%Z ge25c8.
  take RB 26%nat 0x6ab480%Z b_3.
  take RB 3%nat 0x6ab48c%Z ge2dc0.
  take RB 1%nat 0x6ab4a8%Z b_4.
  take RB 6%nat 0x6ab4d8%Z ge2de8.
  acall (seg_aevt_7 RT AF RTC MCI PMc FDO MST Σ); [exact ST | a_ul | exact LOR | a_ul | a_mod16 | lia | exact ge20f0 | exact ge20a8 | exact ge22a0 | exact ge22a8 | exact ge2578 | exact ge25c8 | exact ge2dc0 | exact GOT | exact CAN | exact ge2de8 | assumption | exact ARTX | clear ST ge20f0 ge20a8 ge22a0 ge22a8 ge2578 ge25c8 ge2dc0 ge2de8; apost_call].
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

  take RA 60%nat 0x6aa768%Z a_0.
  take RA 1%nat 0x6aa76c%Z ge20a8.
  take RA 10%nat 0x6aa7a0%Z a_1.
  take RA 2%nat 0x6aa7ac%Z ge20e0.
  take RB 25%nat 0x6aa970%Z b_0.
  take RB 1%nat 0x6aa978%Z ge22b0.
  take RB 1%nat 0x6aa980%Z ge22b8.
  take RB 66%nat 0x6aac38%Z b_1.
  take RB 3%nat 0x6aac50%Z ge2578.
  take RB 8%nat 0x6aac90%Z b_2.
  take RB 1%nat 0x6aac98%Z ge25d0.
  take RB 25%nat 0x6ab480%Z b_3.
  take RB 3%nat 0x6ab48c%Z ge2dc0.
  take RB 1%nat 0x6ab4a8%Z b_4.
  take RB 6%nat 0x6ab4d8%Z ge2de8.
  acall (seg_aevt_8 RT AF RTC MCI PMc FDO MST Σ); [exact ST | a_ul | exact LOR | a_ul | a_mod16 | lia | exact ge20e0 | exact ge20a8 | exact ge22b0 | exact ge22b8 | exact ge2578 | exact ge25d0 | exact ge2dc0 | exact GOT | exact CAN | exact ge2de8 | assumption | exact ARTX | clear ST ge20e0 ge20a8 ge22b0 ge22b8 ge2578 ge25d0 ge2dc0 ge2de8; apost_call].
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

  take RA 60%nat 0x6aa768%Z a_0.
  take RA 1%nat 0x6aa76c%Z ge20a8.
  take RA 16%nat 0x6aa7c0%Z a_1.
  take RA 2%nat 0x6aa7cc%Z ge2100.
  take RB 27%nat 0x6aa980%Z b_0.
  take RB 1%nat 0x6aa988%Z ge22c0.
  take RB 1%nat 0x6aa990%Z ge22c8.
  take RB 64%nat 0x6aac38%Z b_1.
  take RB 3%nat 0x6aac50%Z ge2578.
  take RB 9%nat 0x6aac98%Z b_2.
  take RB 1%nat 0x6aaca0%Z ge25d8.
  take RB 24%nat 0x6ab480%Z b_3.
  take RB 3%nat 0x6ab48c%Z ge2dc0.
  take RB 1%nat 0x6ab4a8%Z b_4.
  take RB 6%nat 0x6ab4d8%Z ge2de8.
  acall (seg_aevt_9 RT AF RTC MCI PMc FDO MST Σ); [exact ST | a_ul | exact LOR | a_ul | a_mod16 | lia | exact ge2100 | exact ge20a8 | exact ge22c0 | exact ge22c8 | exact ge2578 | exact ge25d8 | exact ge2dc0 | exact GOT | exact CAN | exact ge2de8 | assumption | exact ARTX | clear ST ge2100 ge20a8 ge22c0 ge22c8 ge2578 ge25d8 ge2dc0 ge2de8; apost_call].
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

  take RA 60%nat 0x6aa768%Z a_0.
  take RA 1%nat 0x6aa76c%Z ge20a8.
  take RB 7%nat 0x6aa8f0%Z b_0.
  take RB 2%nat 0x6aa8fc%Z ge2230.
  take RB 69%nat 0x6aabc8%Z b_1.
  take RB 1%nat 0x6aabd0%Z ge2508.
  take RB 1%nat 0x6aabd8%Z ge2510.
  take RB 1%nat 0x6aabda%Z ge2518.
  take RB 1%nat 0x6aabe0%Z b_2.
  take RB 1%nat 0x6aabe8%Z ge2520.
  take RB 1%nat 0x6aabf0%Z ge2528.
  take RB 1%nat 0x6aabf8%Z ge2530.
  take RB 8%nat 0x6aac38%Z b_3.
  take RB 3%nat 0x6aac50%Z ge2578.
  take RB 10%nat 0x6aaca0%Z b_4.
  take RB 1%nat 0x6aaca8%Z ge25e0.
  take RB 23%nat 0x6ab480%Z b_5.
  take RB 3%nat 0x6ab48c%Z ge2dc0.
  take RB 1%nat 0x6ab4a8%Z b_6.
  take RB 6%nat 0x6ab4d8%Z ge2de8.
  acall (seg_aevt_10 RT AF RTC MCI PMc FDO MST Σ); [exact ST | a_ul | exact LOR | a_ul | a_mod16 | lia | exact ge2230 | exact ge20a8 | exact ge2508 | exact ge2510 | exact ge2518 | exact ge2520 | exact ge2528 | exact ge2530 | exact ge2578 | exact ge25e0 | exact ge2dc0 | exact GOT | exact CAN | exact ge2de8 | assumption | exact ARTX | clear ST ge2230 ge20a8 ge2508 ge2510 ge2518 ge2520 ge2528 ge2530 ge2578 ge25e0 ge2dc0 ge2de8; apost_call].
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

  take RA 60%nat 0x6aa768%Z a_0.
  take RA 1%nat 0x6aa76c%Z ge20a8.
  take RB 10%nat 0x6aa900%Z b_0.
  take RB 2%nat 0x6aa90c%Z ge2240.
  take RB 73%nat 0x6aabf8%Z b_1.
  take RB 1%nat 0x6aac00%Z ge2538.
  take RB 1%nat 0x6aac08%Z ge2540.
  take RB 1%nat 0x6aac10%Z ge2548.
  take RB 1%nat 0x6aac18%Z ge2550.
  take RB 1%nat 0x6aac20%Z ge2558.
  take RB 1%nat 0x6aac28%Z ge2560.
  take RB 2%nat 0x6aac38%Z b_2.
  take RB 3%nat 0x6aac50%Z ge2578.
  take RB 11%nat 0x6aaca8%Z b_3.
  take RB 1%nat 0x6aacb0%Z ge25e8.
  take RB 22%nat 0x6ab480%Z b_4.
  take RB 3%nat 0x6ab48c%Z ge2dc0.
  take RB 1%nat 0x6ab4a8%Z b_5.
  take RB 6%nat 0x6ab4d8%Z ge2de8.
  acall (seg_aevt_11 RT AF RTC MCI PMc FDO MST Σ); [exact ST | a_ul | exact LOR | a_ul | a_mod16 | lia | exact ge2240 | exact ge20a8 | exact ge2538 | exact ge2540 | exact ge2548 | exact ge2550 | exact ge2558 | exact ge2560 | exact ge2578 | exact ge25e8 | exact ge2dc0 | exact GOT | exact CAN | exact ge2de8 | assumption | exact ARTX | clear ST ge2240 ge20a8 ge2538 ge2540 ge2548 ge2550 ge2558 ge2560 ge2578 ge25e8 ge2dc0 ge2de8; apost_call].
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

  take RA 6%nat 0x6aa648%Z a_0.
  take RA 2%nat 0x6aa654%Z ge1f88.
  take RA 52%nat 0x6aa768%Z a_1.
  take RA 1%nat 0x6aa76c%Z ge20a8.
  take RB 29%nat 0x6aa990%Z b_0.
  take RB 1%nat 0x6aa998%Z ge22d0.
  take RB 1%nat 0x6aa9a0%Z ge22d8.
  take RB 62%nat 0x6aac38%Z b_1.
  take RB 3%nat 0x6aac50%Z ge2578.
  take RB 12%nat 0x6aacb0%Z b_2.
  take RB 1%nat 0x6aacb8%Z ge25f0.
  take RB 21%nat 0x6ab480%Z b_3.
  take RB 3%nat 0x6ab48c%Z ge2dc0.
  take RB 1%nat 0x6ab4a8%Z b_4.
  take RB 6%nat 0x6ab4d8%Z ge2de8.
  acall (seg_aevt_12 RT AF RTC MCI PMc FDO MST Σ); [exact ST | a_ul | exact LOR | a_ul | a_mod16 | lia | exact ge1f88 | exact ge20a8 | exact ge22d0 | exact ge22d8 | exact ge2578 | exact ge25f0 | exact ge2dc0 | exact GOT | exact CAN | exact ge2de8 | assumption | exact ARTX | clear ST ge1f88 ge20a8 ge22d0 ge22d8 ge2578 ge25f0 ge2dc0 ge2de8; apost_call].
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

  take RA 9%nat 0x6aa658%Z a_0.
  take RA 2%nat 0x6aa664%Z ge1f98.
  take RA 49%nat 0x6aa768%Z a_1.
  take RA 1%nat 0x6aa76c%Z ge20a8.
  take RB 31%nat 0x6aa9a0%Z b_0.
  take RB 1%nat 0x6aa9a8%Z ge22e0.
  take RB 1%nat 0x6aa9b0%Z ge22e8.
  take RB 60%nat 0x6aac38%Z b_1.
  take RB 3%nat 0x6aac50%Z ge2578.
  take RB 13%nat 0x6aacb8%Z b_2.
  take RB 1%nat 0x6aacc0%Z ge25f8.
  take RB 20%nat 0x6ab480%Z b_3.
  take RB 3%nat 0x6ab48c%Z ge2dc0.
  take RB 1%nat 0x6ab4a8%Z b_4.
  take RB 6%nat 0x6ab4d8%Z ge2de8.
  acall (seg_aevt_13 RT AF RTC MCI PMc FDO MST Σ); [exact ST | a_ul | exact LOR | a_ul | a_mod16 | lia | exact ge1f98 | exact ge20a8 | exact ge22e0 | exact ge22e8 | exact ge2578 | exact ge25f8 | exact ge2dc0 | exact GOT | exact CAN | exact ge2de8 | assumption | exact ARTX | clear ST ge1f98 ge20a8 ge22e0 ge22e8 ge2578 ge25f8 ge2dc0 ge2de8; apost_call].
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

  take RA 12%nat 0x6aa668%Z a_0.
  take RA 2%nat 0x6aa674%Z ge1fa8.
  take RA 46%nat 0x6aa768%Z a_1.
  take RA 1%nat 0x6aa76c%Z ge20a8.
  take RB 33%nat 0x6aa9b0%Z b_0.
  take RB 1%nat 0x6aa9b8%Z ge22f0.
  take RB 1%nat 0x6aa9c0%Z ge22f8.
  take RB 58%nat 0x6aac38%Z b_1.
  take RB 3%nat 0x6aac50%Z ge2578.
  take RB 14%nat 0x6aacc0%Z b_2.
  take RB 1%nat 0x6aacc8%Z ge2600.
  take RB 19%nat 0x6ab480%Z b_3.
  take RB 3%nat 0x6ab48c%Z ge2dc0.
  take RB 1%nat 0x6ab4a8%Z b_4.
  take RB 6%nat 0x6ab4d8%Z ge2de8.
  acall (seg_aevt_14 RT AF RTC MCI PMc FDO MST Σ); [exact ST | a_ul | exact LOR | a_ul | a_mod16 | lia | exact ge1fa8 | exact ge20a8 | exact ge22f0 | exact ge22f8 | exact ge2578 | exact ge2600 | exact ge2dc0 | exact GOT | exact CAN | exact ge2de8 | assumption | exact ARTX | clear ST ge1fa8 ge20a8 ge22f0 ge22f8 ge2578 ge2600 ge2dc0 ge2de8; apost_call].
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

  take RA 15%nat 0x6aa678%Z a_0.
  take RA 2%nat 0x6aa684%Z ge1fb8.
  take RA 43%nat 0x6aa768%Z a_1.
  take RA 1%nat 0x6aa76c%Z ge20a8.
  take RB 35%nat 0x6aa9c0%Z b_0.
  take RB 1%nat 0x6aa9c8%Z ge2300.
  take RB 1%nat 0x6aa9d0%Z ge2308.
  take RB 56%nat 0x6aac38%Z b_1.
  take RB 3%nat 0x6aac50%Z ge2578.
  take RB 15%nat 0x6aacc8%Z b_2.
  take RB 1%nat 0x6aacd0%Z ge2608.
  take RB 18%nat 0x6ab480%Z b_3.
  take RB 3%nat 0x6ab48c%Z ge2dc0.
  take RB 1%nat 0x6ab4a8%Z b_4.
  take RB 6%nat 0x6ab4d8%Z ge2de8.
  acall (seg_aevt_15 RT AF RTC MCI PMc FDO MST Σ); [exact ST | a_ul | exact LOR | a_ul | a_mod16 | lia | exact ge1fb8 | exact ge20a8 | exact ge2300 | exact ge2308 | exact ge2578 | exact ge2608 | exact ge2dc0 | exact GOT | exact CAN | exact ge2de8 | assumption | exact ARTX | clear ST ge1fb8 ge20a8 ge2300 ge2308 ge2578 ge2608 ge2dc0 ge2de8; apost_call].
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

  take RA 30%nat 0x6aa6c8%Z a_0.
  take RA 2%nat 0x6aa6d4%Z ge2008.
  take RA 28%nat 0x6aa768%Z a_1.
  take RA 1%nat 0x6aa76c%Z ge20a8.
  take RB 37%nat 0x6aa9d0%Z b_0.
  take RB 1%nat 0x6aa9d8%Z ge2310.
  take RB 1%nat 0x6aa9e0%Z ge2318.
  take RB 54%nat 0x6aac38%Z b_1.
  take RB 3%nat 0x6aac50%Z ge2578.
  take RB 16%nat 0x6aacd0%Z b_2.
  take RB 1%nat 0x6aacd8%Z ge2610.
  take RB 17%nat 0x6ab480%Z b_3.
  take RB 3%nat 0x6ab48c%Z ge2dc0.
  take RB 1%nat 0x6ab4a8%Z b_4.
  take RB 6%nat 0x6ab4d8%Z ge2de8.
  acall (seg_aevt_16 RT AF RTC MCI PMc FDO MST Σ); [exact ST | a_ul | exact LOR | a_ul | a_mod16 | lia | exact ge2008 | exact ge20a8 | exact ge2310 | exact ge2318 | exact ge2578 | exact ge2610 | exact ge2dc0 | exact GOT | exact CAN | exact ge2de8 | assumption | exact ARTX | clear ST ge2008 ge20a8 ge2310 ge2318 ge2578 ge2610 ge2dc0 ge2de8; apost_call].
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

  take RA 33%nat 0x6aa6d8%Z a_0.
  take RA 2%nat 0x6aa6e4%Z ge2018.
  take RA 25%nat 0x6aa768%Z a_1.
  take RA 1%nat 0x6aa76c%Z ge20a8.
  take RB 39%nat 0x6aa9e0%Z b_0.
  take RB 1%nat 0x6aa9e8%Z ge2320.
  take RB 1%nat 0x6aa9f0%Z ge2328.
  take RB 52%nat 0x6aac38%Z b_1.
  take RB 3%nat 0x6aac50%Z ge2578.
  take RB 17%nat 0x6aacd8%Z b_2.
  take RB 1%nat 0x6aace0%Z ge2618.
  take RB 16%nat 0x6ab480%Z b_3.
  take RB 3%nat 0x6ab48c%Z ge2dc0.
  take RB 1%nat 0x6ab4a8%Z b_4.
  take RB 6%nat 0x6ab4d8%Z ge2de8.
  acall (seg_aevt_17 RT AF RTC MCI PMc FDO MST Σ); [exact ST | a_ul | exact LOR | a_ul | a_mod16 | lia | exact ge2018 | exact ge20a8 | exact ge2320 | exact ge2328 | exact ge2578 | exact ge2618 | exact ge2dc0 | exact GOT | exact CAN | exact ge2de8 | assumption | exact ARTX | clear ST ge2018 ge20a8 ge2320 ge2328 ge2578 ge2618 ge2dc0 ge2de8; apost_call].
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

  take RA 36%nat 0x6aa6e8%Z a_0.
  take RA 2%nat 0x6aa6f4%Z ge2028.
  take RA 22%nat 0x6aa768%Z a_1.
  take RA 1%nat 0x6aa76c%Z ge20a8.
  take RB 41%nat 0x6aa9f0%Z b_0.
  take RB 1%nat 0x6aa9f8%Z ge2330.
  take RB 1%nat 0x6aaa00%Z ge2338.
  take RB 50%nat 0x6aac38%Z b_1.
  take RB 3%nat 0x6aac50%Z ge2578.
  take RB 18%nat 0x6aace0%Z b_2.
  take RB 1%nat 0x6aace8%Z ge2620.
  take RB 15%nat 0x6ab480%Z b_3.
  take RB 3%nat 0x6ab48c%Z ge2dc0.
  take RB 1%nat 0x6ab4a8%Z b_4.
  take RB 6%nat 0x6ab4d8%Z ge2de8.
  acall (seg_aevt_18 RT AF RTC MCI PMc FDO MST Σ); [exact ST | a_ul | exact LOR | a_ul | a_mod16 | lia | exact ge2028 | exact ge20a8 | exact ge2330 | exact ge2338 | exact ge2578 | exact ge2620 | exact ge2dc0 | exact GOT | exact CAN | exact ge2de8 | assumption | exact ARTX | clear ST ge2028 ge20a8 ge2330 ge2338 ge2578 ge2620 ge2dc0 ge2de8; apost_call].
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

  take RA 39%nat 0x6aa6f8%Z a_0.
  take RA 2%nat 0x6aa704%Z ge2038.
  take RA 19%nat 0x6aa768%Z a_1.
  take RA 1%nat 0x6aa76c%Z ge20a8.
  take RB 43%nat 0x6aaa00%Z b_0.
  take RB 1%nat 0x6aaa08%Z ge2340.
  take RB 1%nat 0x6aaa10%Z ge2348.
  take RB 48%nat 0x6aac38%Z b_1.
  take RB 3%nat 0x6aac50%Z ge2578.
  take RB 19%nat 0x6aace8%Z b_2.
  take RB 1%nat 0x6aacf0%Z ge2628.
  take RB 14%nat 0x6ab480%Z b_3.
  take RB 3%nat 0x6ab48c%Z ge2dc0.
  take RB 1%nat 0x6ab4a8%Z b_4.
  take RB 6%nat 0x6ab4d8%Z ge2de8.
  acall (seg_aevt_19 RT AF RTC MCI PMc FDO MST Σ); [exact ST | a_ul | exact LOR | a_ul | a_mod16 | lia | exact ge2038 | exact ge20a8 | exact ge2340 | exact ge2348 | exact ge2578 | exact ge2628 | exact ge2dc0 | exact GOT | exact CAN | exact ge2de8 | assumption | exact ARTX | clear ST ge2038 ge20a8 ge2340 ge2348 ge2578 ge2628 ge2dc0 ge2de8; apost_call].
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

  take RA 42%nat 0x6aa708%Z a_0.
  take RA 2%nat 0x6aa714%Z ge2048.
  take RA 16%nat 0x6aa768%Z a_1.
  take RA 1%nat 0x6aa76c%Z ge20a8.
  take RB 45%nat 0x6aaa10%Z b_0.
  take RB 1%nat 0x6aaa18%Z ge2350.
  take RB 1%nat 0x6aaa20%Z ge2358.
  take RB 46%nat 0x6aac38%Z b_1.
  take RB 3%nat 0x6aac50%Z ge2578.
  take RB 20%nat 0x6aacf0%Z b_2.
  take RB 1%nat 0x6aacf8%Z ge2630.
  take RB 13%nat 0x6ab480%Z b_3.
  take RB 3%nat 0x6ab48c%Z ge2dc0.
  take RB 1%nat 0x6ab4a8%Z b_4.
  take RB 6%nat 0x6ab4d8%Z ge2de8.
  acall (seg_aevt_20 RT AF RTC MCI PMc FDO MST Σ); [exact ST | a_ul | exact LOR | a_ul | a_mod16 | lia | exact ge2048 | exact ge20a8 | exact ge2350 | exact ge2358 | exact ge2578 | exact ge2630 | exact ge2dc0 | exact GOT | exact CAN | exact ge2de8 | assumption | exact ARTX | clear ST ge2048 ge20a8 ge2350 ge2358 ge2578 ge2630 ge2dc0 ge2de8; apost_call].
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

  take RA 45%nat 0x6aa718%Z a_0.
  take RA 2%nat 0x6aa724%Z ge2058.
  take RA 13%nat 0x6aa768%Z a_1.
  take RA 1%nat 0x6aa76c%Z ge20a8.
  take RB 47%nat 0x6aaa20%Z b_0.
  take RB 1%nat 0x6aaa28%Z ge2360.
  take RB 1%nat 0x6aaa30%Z ge2368.
  take RB 44%nat 0x6aac38%Z b_1.
  take RB 3%nat 0x6aac50%Z ge2578.
  take RB 21%nat 0x6aacf8%Z b_2.
  take RB 1%nat 0x6aad00%Z ge2638.
  take RB 12%nat 0x6ab480%Z b_3.
  take RB 3%nat 0x6ab48c%Z ge2dc0.
  take RB 1%nat 0x6ab4a8%Z b_4.
  take RB 6%nat 0x6ab4d8%Z ge2de8.
  acall (seg_aevt_21 RT AF RTC MCI PMc FDO MST Σ); [exact ST | a_ul | exact LOR | a_ul | a_mod16 | lia | exact ge2058 | exact ge20a8 | exact ge2360 | exact ge2368 | exact ge2578 | exact ge2638 | exact ge2dc0 | exact GOT | exact CAN | exact ge2de8 | assumption | exact ARTX | clear ST ge2058 ge20a8 ge2360 ge2368 ge2578 ge2638 ge2dc0 ge2de8; apost_call].
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

  take RA 48%nat 0x6aa728%Z a_0.
  take RA 2%nat 0x6aa734%Z ge2068.
  take RA 10%nat 0x6aa768%Z a_1.
  take RA 1%nat 0x6aa76c%Z ge20a8.
  take RB 49%nat 0x6aaa30%Z b_0.
  take RB 1%nat 0x6aaa38%Z ge2370.
  take RB 1%nat 0x6aaa40%Z ge2378.
  take RB 42%nat 0x6aac38%Z b_1.
  take RB 3%nat 0x6aac50%Z ge2578.
  take RB 22%nat 0x6aad00%Z b_2.
  take RB 1%nat 0x6aad08%Z ge2640.
  take RB 11%nat 0x6ab480%Z b_3.
  take RB 3%nat 0x6ab48c%Z ge2dc0.
  take RB 1%nat 0x6ab4a8%Z b_4.
  take RB 6%nat 0x6ab4d8%Z ge2de8.
  acall (seg_aevt_22 RT AF RTC MCI PMc FDO MST Σ); [exact ST | a_ul | exact LOR | a_ul | a_mod16 | lia | exact ge2068 | exact ge20a8 | exact ge2370 | exact ge2378 | exact ge2578 | exact ge2640 | exact ge2dc0 | exact GOT | exact CAN | exact ge2de8 | assumption | exact ARTX | clear ST ge2068 ge20a8 ge2370 ge2378 ge2578 ge2640 ge2dc0 ge2de8; apost_call].
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

  take RA 51%nat 0x6aa738%Z a_0.
  take RA 2%nat 0x6aa744%Z ge2078.
  take RA 7%nat 0x6aa768%Z a_1.
  take RA 1%nat 0x6aa76c%Z ge20a8.
  take RB 51%nat 0x6aaa40%Z b_0.
  take RB 1%nat 0x6aaa48%Z ge2380.
  take RB 1%nat 0x6aaa50%Z ge2388.
  take RB 40%nat 0x6aac38%Z b_1.
  take RB 3%nat 0x6aac50%Z ge2578.
  take RB 23%nat 0x6aad08%Z b_2.
  take RB 1%nat 0x6aad10%Z ge2648.
  take RB 10%nat 0x6ab480%Z b_3.
  take RB 3%nat 0x6ab48c%Z ge2dc0.
  take RB 1%nat 0x6ab4a8%Z b_4.
  take RB 6%nat 0x6ab4d8%Z ge2de8.
  acall (seg_aevt_23 RT AF RTC MCI PMc FDO MST Σ); [exact ST | a_ul | exact LOR | a_ul | a_mod16 | lia | exact ge2078 | exact ge20a8 | exact ge2380 | exact ge2388 | exact ge2578 | exact ge2648 | exact ge2dc0 | exact GOT | exact CAN | exact ge2de8 | assumption | exact ARTX | clear ST ge2078 ge20a8 ge2380 ge2388 ge2578 ge2648 ge2dc0 ge2de8; apost_call].
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

  take RA 18%nat 0x6aa688%Z a_0.
  take RA 2%nat 0x6aa694%Z ge1fc8.
  take RA 40%nat 0x6aa768%Z a_1.
  take RA 1%nat 0x6aa76c%Z ge20a8.
  take RB 61%nat 0x6aaae8%Z b_0.
  take RB 1%nat 0x6aaaf0%Z ge2428.
  take RB 1%nat 0x6aaaf8%Z ge2430.
  take RB 1%nat 0x6aab00%Z ge2438.
  take RB 29%nat 0x6aac38%Z b_1.
  take RB 3%nat 0x6aac50%Z ge2578.
  take RB 24%nat 0x6aad10%Z b_2.
  take RB 1%nat 0x6aad18%Z ge2650.
  take RB 9%nat 0x6ab480%Z b_3.
  take RB 3%nat 0x6ab48c%Z ge2dc0.
  take RB 1%nat 0x6ab4a8%Z b_4.
  take RB 6%nat 0x6ab4d8%Z ge2de8.
  acall (seg_aevt_24 RT AF RTC MCI PMc FDO MST Σ); [exact ST | a_ul | exact LOR | a_ul | a_mod16 | lia | exact ge1fc8 | exact ge20a8 | exact ge2428 | exact ge2430 | exact ge2438 | exact ge2578 | exact ge2650 | exact ge2dc0 | exact GOT | exact CAN | exact ge2de8 | assumption | exact ARTX | clear ST ge1fc8 ge20a8 ge2428 ge2430 ge2438 ge2578 ge2650 ge2dc0 ge2de8; apost_call].
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

  take RA 21%nat 0x6aa698%Z a_0.
  take RA 2%nat 0x6aa6a4%Z ge1fd8.
  take RA 37%nat 0x6aa768%Z a_1.
  take RA 1%nat 0x6aa76c%Z ge20a8.
  take RB 64%nat 0x6aab00%Z b_0.
  take RB 1%nat 0x6aab08%Z ge2440.
  take RB 1%nat 0x6aab10%Z ge2448.
  take RB 1%nat 0x6aab18%Z ge2450.
  take RB 26%nat 0x6aac38%Z b_1.
  take RB 3%nat 0x6aac50%Z ge2578.
  take RB 25%nat 0x6aad18%Z b_2.
  take RB 1%nat 0x6aad20%Z ge2658.
  take RB 8%nat 0x6ab480%Z b_3.
  take RB 3%nat 0x6ab48c%Z ge2dc0.
  take RB 1%nat 0x6ab4a8%Z b_4.
  take RB 6%nat 0x6ab4d8%Z ge2de8.
  acall (seg_aevt_25 RT AF RTC MCI PMc FDO MST Σ); [exact ST | a_ul | exact LOR | a_ul | a_mod16 | lia | exact ge1fd8 | exact ge20a8 | exact ge2440 | exact ge2448 | exact ge2450 | exact ge2578 | exact ge2658 | exact ge2dc0 | exact GOT | exact CAN | exact ge2de8 | assumption | exact ARTX | clear ST ge1fd8 ge20a8 ge2440 ge2448 ge2450 ge2578 ge2658 ge2dc0 ge2de8; apost_call].
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

  take RA 24%nat 0x6aa6a8%Z a_0.
  take RA 2%nat 0x6aa6b4%Z ge1fe8.
  take RA 34%nat 0x6aa768%Z a_1.
  take RA 1%nat 0x6aa76c%Z ge20a8.
  take RA 20%nat 0x6aa7f0%Z a_2.
  take RA 1%nat 0x6aa7f8%Z ge2130.
  take RA 1%nat 0x6aa7f9%Z ge2138.
  take RB 67%nat 0x6aab18%Z b_0.
  take RB 1%nat 0x6aab20%Z ge2458.
  take RB 1%nat 0x6aab28%Z ge2460.
  take RB 1%nat 0x6aab30%Z ge2468.
  take RB 23%nat 0x6aac38%Z b_1.
  take RB 3%nat 0x6aac50%Z ge2578.
  take RB 26%nat 0x6aad20%Z b_2.
  take RB 1%nat 0x6aad28%Z ge2660.
  take RB 7%nat 0x6ab480%Z b_3.
  take RB 3%nat 0x6ab48c%Z ge2dc0.
  take RB 1%nat 0x6ab4a8%Z b_4.
  take RB 6%nat 0x6ab4d8%Z ge2de8.
  acall (seg_aevt_26 RT AF RTC MCI PMc FDO MST Σ); [exact ST | a_ul | exact LOR | a_ul | a_mod16 | lia | exact ge1fe8 | exact ge20a8 | exact ge2458 | exact ge2460 | exact ge2468 | exact ge2578 | exact ge2660 | exact ge2dc0 | exact ge2130 | exact ge2138 | exact GOT | exact CAN | exact ge2de8 | assumption | exact ARTX | clear ST ge1fe8 ge20a8 ge2458 ge2460 ge2468 ge2578 ge2660 ge2dc0 ge2de8; apost_call].
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

  take RA 27%nat 0x6aa6b8%Z a_0.
  take RA 2%nat 0x6aa6c4%Z ge1ff8.
  take RA 31%nat 0x6aa768%Z a_1.
  take RA 1%nat 0x6aa76c%Z ge20a8.
  take RA 20%nat 0x6aa7f0%Z a_2.
  take RA 1%nat 0x6aa7f8%Z ge2130.
  take RA 1%nat 0x6aa7f9%Z ge2138.
  take RB 70%nat 0x6aab30%Z b_0.
  take RB 1%nat 0x6aab38%Z ge2470.
  take RB 1%nat 0x6aab40%Z ge2478.
  take RB 1%nat 0x6aab48%Z ge2480.
  take RB 20%nat 0x6aac38%Z b_1.
  take RB 3%nat 0x6aac50%Z ge2578.
  take RB 27%nat 0x6aad28%Z b_2.
  take RB 1%nat 0x6aad30%Z ge2668.
  take RB 6%nat 0x6ab480%Z b_3.
  take RB 3%nat 0x6ab48c%Z ge2dc0.
  take RB 1%nat 0x6ab4a8%Z b_4.
  take RB 6%nat 0x6ab4d8%Z ge2de8.
  acall (seg_aevt_27 RT AF RTC MCI PMc FDO MST Σ); [exact ST | a_ul | exact LOR | a_ul | a_mod16 | lia | exact ge1ff8 | exact ge20a8 | exact ge2470 | exact ge2478 | exact ge2480 | exact ge2578 | exact ge2668 | exact ge2dc0 | exact ge2130 | exact ge2138 | exact GOT | exact CAN | exact ge2de8 | assumption | exact ARTX | clear ST ge1ff8 ge20a8 ge2470 ge2478 ge2480 ge2578 ge2668 ge2dc0 ge2de8; apost_call].
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

  take RA 54%nat 0x6aa748%Z a_0.
  take RA 2%nat 0x6aa754%Z ge2088.
  take RA 4%nat 0x6aa768%Z a_1.
  take RA 1%nat 0x6aa76c%Z ge20a8.
  take RB 53%nat 0x6aaa50%Z b_0.
  take RB 1%nat 0x6aaa58%Z ge2390.
  take RB 1%nat 0x6aaa60%Z ge2398.
  take RB 38%nat 0x6aac38%Z b_1.
  take RB 3%nat 0x6aac50%Z ge2578.
  take RB 28%nat 0x6aad30%Z b_2.
  take RB 1%nat 0x6aad38%Z ge2670.
  take RB 5%nat 0x6ab480%Z b_3.
  take RB 3%nat 0x6ab48c%Z ge2dc0.
  take RB 1%nat 0x6ab4a8%Z b_4.
  take RB 6%nat 0x6ab4d8%Z ge2de8.
  acall (seg_aevt_28 RT AF RTC MCI PMc FDO MST Σ); [exact ST | a_ul | exact LOR | a_ul | a_mod16 | lia | exact ge2088 | exact ge20a8 | exact ge2390 | exact ge2398 | exact ge2578 | exact ge2670 | exact ge2dc0 | exact GOT | exact CAN | exact ge2de8 | assumption | exact ARTX | clear ST ge2088 ge20a8 ge2390 ge2398 ge2578 ge2670 ge2dc0 ge2de8; apost_call].
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

  take RA 57%nat 0x6aa758%Z a_0.
  take RA 2%nat 0x6aa764%Z ge2098.
  take RA 1%nat 0x6aa768%Z a_1.
  take RA 1%nat 0x6aa76c%Z ge20a8.
  take RB 55%nat 0x6aaa60%Z b_0.
  take RB 1%nat 0x6aaa68%Z ge23a0.
  take RB 1%nat 0x6aaa70%Z ge23a8.
  take RB 36%nat 0x6aac38%Z b_1.
  take RB 3%nat 0x6aac50%Z ge2578.
  take RB 29%nat 0x6aad38%Z b_2.
  take RB 1%nat 0x6aad40%Z ge2678.
  take RB 4%nat 0x6ab480%Z b_3.
  take RB 3%nat 0x6ab48c%Z ge2dc0.
  take RB 1%nat 0x6ab4a8%Z b_4.
  take RB 6%nat 0x6ab4d8%Z ge2de8.
  acall (seg_aevt_29 RT AF RTC MCI PMc FDO MST Σ); [exact ST | a_ul | exact LOR | a_ul | a_mod16 | lia | exact ge2098 | exact ge20a8 | exact ge23a0 | exact ge23a8 | exact ge2578 | exact ge2678 | exact ge2dc0 | exact GOT | exact CAN | exact ge2de8 | assumption | exact ARTX | clear ST ge2098 ge20a8 ge23a0 ge23a8 ge2578 ge2678 ge2dc0 ge2de8; apost_call].
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

  do 7 lstep.
  release_frame FR ST (bv_unsigned sp).

  merge_at RB 111%nat 29%nat.
  merge_at RB 107%nat 3%nat.
  merge_at RB 99%nat 7%nat.
  merge_at RB 95%nat 3%nat.
  merge_at RB 85%nat 8%nat.
  merge_at RB 79%nat 1%nat.
  merge_at RB 74%nat 4%nat.
  merge_at RB 34%nat 39%nat.
  merge_at RB 9%nat 24%nat.
  merge_at RB 0%nat 4%nat.
  merge_at RA 14%nat 67%nat.
  merge_at RA 0%nat 12%nat.
  afinish_with ltac:(unfold impb_A, impb_B).
Qed.

End AevtPieces.
