(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.simdjson.fuzz_dump_raw_tape.lib.AS Require Import ShapeAlg AsanAcct.
From OSSVerify.Proofs.simdjson.fuzz_dump_raw_tape.lib.Lib Require Import Tac Arr Bytes ITree Nodes Decode SysStep RegsEquiv ImageA RzCPS StoreFast FP.
From OSSVerify.Proofs.simdjson.fuzz_dump_raw_tape.lib.Spec Require Import Prelim StrFun.
From OSSVerify.Proofs.simdjson.fuzz_dump_raw_tape.lib.P Require Import Str_tac Startup_glue Pj_steps Pj_loc_kit.
From OSSVerify.Proofs.simdjson.fuzz_dump_raw_tape.lib.A Require Import Shadow IcptSpec.
From OSSVerify.Proofs.simdjson.fuzz_dump_raw_tape.lib.B Require Import Layout RT_iface RT_iface2 D_defs D_kit D_clx D_rlkit D_libiface Sj_rtf Sj_akit Sj_acps Sj_hkit Sj_new Sj_num_akit Sj_num_amem Pj_mciA Pj_loc_akitA Pj_onceA Pj_loc_newlocA Pj_loc_i00A Pj_loc_i01A Pj_loc_i02A Pj_loc_i03A Pj_loc_i04A Pj_loc_i05A Pj_loc_i06A Pj_loc_i07A Pj_loc_i08A Pj_loc_i09A Pj_loc_i10A Pj_loc_i11A Pj_loc_i12A Pj_loc_i13A Pj_loc_i14A Pj_loc_i15A Pj_loc_i16A Pj_loc_i17A Pj_loc_i18A Pj_loc_i19A Pj_loc_i20A Pj_loc_i21A Pj_loc_i22A Pj_loc_i23A Pj_loc_i24A Pj_loc_i25A Pj_loc_i26A Pj_loc_i27A Pj_loc_i28A Pj_loc_i29A.
From OSSVerify.simdjson.fuzz_dump_raw_tape.images Require Import AsanUbsan.
From OSSVerify.Proofs.simdjson.fuzz_dump_raw_tape.lib.B Require Import Layout.
From OSSVerify.Proofs.simdjson.fuzz_dump_raw_tape.lib.Lib Require Import StoreFast.
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
   C8 (Z_to_bv 64 18446744073709551615); C4 (Z_to_bv 64 3);
   CB 4 jb2;
   C8 (Z_to_bv 64 18446744073709551615); C4 (Z_to_bv 64 11);
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
   C8 (Z_to_bv 64 0x6aac50); C8 (Z_to_bv 64 0x6aad40);
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

Definition imp_ctor_postA (Σ : rts RT) (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (fc : bv 32) (lo : Z) (m : mem)
    : machine_state -> Prop :=
  fun done => exists (x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 : word) (Fr : bvmap 5 word) (mr : mem)
                     (ja1 ja2 ja3 jb1 jb2 jb3 jb4 jb5 jb6 jb6b jb6c jb7 jb8 jb9 jb10 : list byte),
    done = MS (mkR ra sp gp tp x5 x6 x7 s0 s1 x10 x11 x12 x13 x14 x15 x16 x17 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
              Fr (ret_pc ra) fc None mr (seg_rom bsegs)
    /\ rt_pres_fp (rt_live RT Σ) (rt_frames RT Σ) (bv_unsigned sp) [(0x6aa628, 0x6aa800); (0x6aa820, 0x6ab4d8)]%Z m mr
    /\ wmono bsegs m mr
    /\ mem_inv bsegs mr
    /\ ART RT Σ mr
    /\ stk bsegs mr lo (bv_unsigned sp)
    /\ rw_cells bsegs mr 0x6aa628 (impb_A ja1 ja2 ja3)
    /\ rw_cells bsegs mr 0x6aa820 (impb_B jb1 jb2 jb3 jb4 jb5 jb6 jb6b jb6c jb7 jb8 jb9 jb10).

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
  intros Σ K ra sp gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo canary
    Frame RoomLo WinLo SpTop SpAl SpLow BlkA BlkB GotSsp Guard NlFlag LkWord MInv Art0 Then.
  unfold imp0_A in BlkA. unfold imp0_B in BlkB.
  retype BlkA [C8 z64; C4 z64; CB 4 (repeat (Z_to_bv 8 0) 4); C8 z64; C4 z64; CB 4 (repeat (Z_to_bv 8 0) 4); C8 z64; C4 z64; CB 4 (repeat (Z_to_bv 8 0) 4); C8 z64; C4 z64; CB 4 (repeat (Z_to_bv 8 0) 4); C8 z64; C4 z64; CB 4 (repeat (Z_to_bv 8 0) 4); C8 z64; C4 z64; CB 4 (repeat (Z_to_bv 8 0) 4); C8 z64; C4 z64; CB 4 (repeat (Z_to_bv 8 0) 4); C8 z64; C4 z64; CB 4 (repeat (Z_to_bv 8 0) 4); C8 z64; C4 z64; CB 4 (repeat (Z_to_bv 8 0) 4); C8 z64; C4 z64; CB 4 (repeat (Z_to_bv 8 0) 4); C8 z64; C4 z64; CB 4 (repeat (Z_to_bv 8 0) 4); C8 z64; C4 z64; CB 4 (repeat (Z_to_bv 8 0) 4); C8 z64; C4 z64; CB 4 (repeat (Z_to_bv 8 0) 4); C8 z64; C4 z64; CB 4 (repeat (Z_to_bv 8 0) 4); C8 z64; C4 z64; CB 4 (repeat (Z_to_bv 8 0) 4); C8 z64; C4 z64; CB 4 (repeat (Z_to_bv 8 0) 4); C8 z64; C4 z64; CB 4 (repeat (Z_to_bv 8 0) 4); C8 z64; C4 z64; CB 4 (repeat (Z_to_bv 8 0) 4); C8 z64; C4 z64; CB 4 (repeat (Z_to_bv 8 0) 4); C8 z64; C4 z64; CB 4 (repeat (Z_to_bv 8 0) 4); C4 z64; CB 4 (repeat (Z_to_bv 8 0) 4); C8 z64; C4 z64; CB 4 (repeat (Z_to_bv 8 0) 4); C8 z64; C4 z64; CB 4 (repeat (Z_to_bv 8 0) 4); C8 z64; C4 z64; CB 4 (repeat (Z_to_bv 8 0) 4); C8 z64; C4 z64; CB 4 (repeat (Z_to_bv 8 0) 4); C8 z64; C4 z64; CB 4 (repeat (Z_to_bv 8 0) 4); C8 z64; C4 z64; CB 36 (repeat (Z_to_bv 8 0) 36); C8 z64; C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); CB 6 (repeat (Z_to_bv 8 0) 6)].
  take BlkA 2%nat 6989364%Z IdZ00. take BlkA 1%nat 6989368%Z Gap6aa634. take BlkA 2%nat 6989380%Z IdZ01. take BlkA 1%nat 6989384%Z Gap6aa644. take BlkA 2%nat 6989396%Z IdZ12. take BlkA 1%nat 6989400%Z Gap6aa654. take BlkA 2%nat 6989412%Z IdZ13. take BlkA 1%nat 6989416%Z Gap6aa664. take BlkA 2%nat 6989428%Z IdZ14. take BlkA 1%nat 6989432%Z Gap6aa674. take BlkA 2%nat 6989444%Z IdZ15. take BlkA 1%nat 6989448%Z Gap6aa684. take BlkA 2%nat 6989460%Z IdZ24. take BlkA 1%nat 6989464%Z Gap6aa694. take BlkA 2%nat 6989476%Z IdZ25. take BlkA 1%nat 6989480%Z Gap6aa6a4. take BlkA 2%nat 6989492%Z IdZ26. take BlkA 1%nat 6989496%Z Gap6aa6b4. take BlkA 2%nat 6989508%Z IdZ27. take BlkA 1%nat 6989512%Z Gap6aa6c4. take BlkA 2%nat 6989524%Z IdZ16. take BlkA 1%nat 6989528%Z Gap6aa6d4. take BlkA 2%nat 6989540%Z IdZ17. take BlkA 1%nat 6989544%Z Gap6aa6e4. take BlkA 2%nat 6989556%Z IdZ18. take BlkA 1%nat 6989560%Z Gap6aa6f4. take BlkA 2%nat 6989572%Z IdZ19. take BlkA 1%nat 6989576%Z Gap6aa704. take BlkA 2%nat 6989588%Z IdZ20. take BlkA 1%nat 6989592%Z Gap6aa714. take BlkA 2%nat 6989604%Z IdZ21. take BlkA 1%nat 6989608%Z Gap6aa724. take BlkA 2%nat 6989620%Z IdZ22. take BlkA 1%nat 6989624%Z Gap6aa734. take BlkA 2%nat 6989636%Z IdZ23. take BlkA 1%nat 6989640%Z Gap6aa744. take BlkA 2%nat 6989652%Z IdZ28. take BlkA 1%nat 6989656%Z Gap6aa754. take BlkA 2%nat 6989668%Z IdZ29. take BlkA 1%nat 6989672%Z Gap6aa764. take BlkA 1%nat 6989676%Z NextId. take BlkA 1%nat 6989680%Z Gap6aa76c. take BlkA 2%nat 6989692%Z IdZ04. take BlkA 1%nat 6989696%Z Gap6aa77c. take BlkA 2%nat 6989708%Z IdZ05. take BlkA 1%nat 6989712%Z Gap6aa78c. take BlkA 2%nat 6989724%Z IdZ06. take BlkA 1%nat 6989728%Z Gap6aa79c. take BlkA 2%nat 6989740%Z IdZ08. take BlkA 1%nat 6989744%Z Gap6aa7ac. take BlkA 2%nat 6989756%Z IdZ07. take BlkA 1%nat 6989760%Z Gap6aa7bc. take BlkA 2%nat 6989772%Z IdZ09. take BlkA 1%nat 6989808%Z Gap6aa7cc. take BlkA 1%nat 6989816%Z ClocP. take BlkA 2%nat 6989818%Z ClocG. take BlkA 1%nat 6989824%Z Gap6aa7fa.
  clear BlkA.
  retype BlkB [CB 176 (repeat (Z_to_bv 8 0) 176); C8 z64; C4 z64; CB 4 (repeat (Z_to_bv 8 0) 4); C8 z64; C4 z64; CB 4 (repeat (Z_to_bv 8 0) 4); C8 z64; C4 z64; CB 4 (repeat (Z_to_bv 8 0) 4); C8 z64; C4 z64; CB 4 (repeat (Z_to_bv 8 0) 4); C8 z64; C8 z64; C8 z64; C8 z64; C8 z64; C8 z64; C8 z64; C8 z64; C8 z64; C8 z64; C8 z64; C8 z64; C8 z64; C8 z64; C8 z64; C8 z64; C8 z64; C8 z64; C8 z64; C8 z64; C8 z64; C8 z64; C8 z64; C8 z64; C8 z64; C8 z64; C8 z64; C8 z64; C8 z64; C8 z64; C8 z64; C8 z64; C8 z64; C8 z64; C8 z64; C8 z64; C8 z64; C8 z64; C8 z64; C8 z64; C8 z64; C8 z64; C8 z64; C8 z64; CB 96 (repeat (Z_to_bv 8 0) 96); C8 z64; C8 z64; C8 z64; C8 z64; C8 z64; C8 z64; C8 z64; C8 z64; C8 z64; C8 z64; C8 z64; C8 z64; C8 z64; C8 z64; C8 z64; C8 z64; C8 z64; C8 z64; C1 (Z_to_bv 8 0); CB 103 (repeat (Z_to_bv 8 0) 103); C8 z64; C8 z64; C2 z64; CB 6 (repeat (Z_to_bv 8 0) 6); C8 z64; C8 z64; C8 z64; C8 z64; C8 z64; C8 z64; C8 z64; C8 z64; C8 z64; C8 z64; C8 z64; C8 z64; C8 z64; C8 z64; CB 240 (repeat (Z_to_bv 8 0) 240); C8 z64; C2 z64; C1 (Z_to_bv 8 0); CB 1845 (repeat (Z_to_bv 8 0) 1845); CB 4 (repeat (Z_to_bv 8 0) 4); C4 z64; C4 z64; CB 28 (repeat (Z_to_bv 8 0) 28); C8 z64; C8 z64; CB 16 (repeat (Z_to_bv 8 0) 16); C4 z64; C4 z64; C8 z64].
  take BlkB 1%nat 6990032%Z Gap6aa820. take BlkB 2%nat 6990044%Z IdZ03. take BlkB 1%nat 6990048%Z Gap6aa8dc. take BlkB 2%nat 6990060%Z IdZ02. take BlkB 1%nat 6990064%Z Gap6aa8ec. take BlkB 2%nat 6990076%Z IdZ10. take BlkB 1%nat 6990080%Z Gap6aa8fc. take BlkB 2%nat 6990092%Z IdZ11. take BlkB 1%nat 6990096%Z Gap6aa90c. take BlkB 1%nat 6990104%Z ObZ00a. take BlkB 1%nat 6990112%Z ObZ00b. take BlkB 1%nat 6990120%Z ObZ01a. take BlkB 1%nat 6990128%Z ObZ01b. take BlkB 1%nat 6990136%Z ObZ03a. take BlkB 1%nat 6990144%Z ObZ03b. take BlkB 1%nat 6990152%Z ObZ04a. take BlkB 1%nat 6990160%Z ObZ04b. take BlkB 1%nat 6990168%Z ObZ06a. take BlkB 1%nat 6990176%Z ObZ06b. take BlkB 1%nat 6990184%Z ObZ07a. take BlkB 1%nat 6990192%Z ObZ07b. take BlkB 1%nat 6990200%Z ObZ08a. take BlkB 1%nat 6990208%Z ObZ08b. take BlkB 1%nat 6990216%Z ObZ09a. take BlkB 1%nat 6990224%Z ObZ09b. take BlkB 1%nat 6990232%Z ObZ12a. take BlkB 1%nat 6990240%Z ObZ12b. take BlkB 1%nat 6990248%Z ObZ13a. take BlkB 1%nat 6990256%Z ObZ13b. take BlkB 1%nat 6990264%Z ObZ14a. take BlkB 1%nat 6990272%Z ObZ14b. take BlkB 1%nat 6990280%Z ObZ15a. take BlkB 1%nat 6990288%Z ObZ15b. take BlkB 1%nat 6990296%Z ObZ16a. take BlkB 1%nat 6990304%Z ObZ16b. take BlkB 1%nat 6990312%Z ObZ17a. take BlkB 1%nat 6990320%Z ObZ17b. take BlkB 1%nat 6990328%Z ObZ18a. take BlkB 1%nat 6990336%Z ObZ18b. take BlkB 1%nat 6990344%Z ObZ19a. take BlkB 1%nat 6990352%Z ObZ19b. take BlkB 1%nat 6990360%Z ObZ20a. take BlkB 1%nat 6990368%Z ObZ20b. take BlkB 1%nat 6990376%Z ObZ21a. take BlkB 1%nat 6990384%Z ObZ21b. take BlkB 1%nat 6990392%Z ObZ22a. take BlkB 1%nat 6990400%Z ObZ22b. take BlkB 1%nat 6990408%Z ObZ23a. take BlkB 1%nat 6990416%Z ObZ23b. take BlkB 1%nat 6990424%Z ObZ28a. take BlkB 1%nat 6990432%Z ObZ28b. take BlkB 1%nat 6990440%Z ObZ29a. take BlkB 1%nat 6990448%Z ObZ29b. take BlkB 1%nat 6990544%Z Gap6aaa70. take BlkB 1%nat 6990552%Z ObZ05a. take BlkB 1%nat 6990560%Z ObZ05b. take BlkB 1%nat 6990568%Z ObZ05c. take BlkB 1%nat 6990576%Z ObZ24a. take BlkB 1%nat 6990584%Z ObZ24b. take BlkB 1%nat 6990592%Z ObZ24c. take BlkB 1%nat 6990600%Z ObZ25a. take BlkB 1%nat 6990608%Z ObZ25b. take BlkB 1%nat 6990616%Z ObZ25c. take BlkB 1%nat 6990624%Z ObZ26a. take BlkB 1%nat 6990632%Z ObZ26b. take BlkB 1%nat 6990640%Z ObZ26c. take BlkB 1%nat 6990648%Z ObZ27a. take BlkB 1%nat 6990656%Z ObZ27b. take BlkB 1%nat 6990664%Z ObZ27c. take BlkB 1%nat 6990672%Z ObZ02a. take BlkB 1%nat 6990680%Z ObZ02b. take BlkB 1%nat 6990688%Z ObZ02c. take BlkB 1%nat 6990689%Z ObZ02d. take BlkB 1%nat 6990792%Z Gap6aab61. take BlkB 1%nat 6990800%Z ObZ10a. take BlkB 1%nat 6990808%Z ObZ10b. take BlkB 1%nat 6990810%Z ObZ10c. take BlkB 1%nat 6990816%Z Gap6aabda. take BlkB 1%nat 6990824%Z ObZ10d. take BlkB 1%nat 6990832%Z ObZ10e. take BlkB 1%nat 6990840%Z ObZ10f. take BlkB 1%nat 6990848%Z ObZ11a. take BlkB 1%nat 6990856%Z ObZ11b. take BlkB 1%nat 6990864%Z ObZ11c. take BlkB 1%nat 6990872%Z ObZ11d. take BlkB 1%nat 6990880%Z ObZ11e. take BlkB 1%nat 6990888%Z ObZ11f. take BlkB 2%nat 6990904%Z ImpHd. take BlkB 3%nat 6990928%Z ImpVec. take BlkB 1%nat 6991168%Z ImpBuf. take BlkB 3%nat 6991179%Z ImpTl. take BlkB 1%nat 6993024%Z Gap6aad4b. take BlkB 3%nat 6993036%Z OnceMx. take BlkB 1%nat 6993064%Z Gap6ab48c. take BlkB 6%nat 6993112%Z OnceCv.
  clear BlkB.
  pose proof (wmono_refl bsegs m) as Grow.
  astart (bv_unsigned sp) [(0x6aa628, 0x6aa800); (0x6aa820, 0x6ab4d8)]%Z.
  pose proof (munch_refl [(lo, bv_unsigned sp)]%Z m) as Wr.
  apply (aevt_evt RT AF PMc MST).
  acallc (seg_aevt_0 RT AF RTC MCI PMc FDO MST) clearing idtac by (first [ eassumption | a_ul | a_mod16 ]).
  remember (Z_to_bv 64 (bv_unsigned sp + -48)) as sq eqn:SqDef.
  assert (SqVal : bv_unsigned sq = (bv_unsigned sp + -48)%Z) by (rewrite SqDef; apply unsigned_lit; a_ul).
  lazymatch goal with Low : stk bsegs _ lo (bv_unsigned sp + -48) |- _ => rewrite <- SqVal in Low; rename Low into Stk1 end.
  lazymatch goal with Regs : rw_cells bsegs _ (bv_unsigned sp + -48) _ |- _ => rewrite <- SqVal in Regs; rename Regs into Saved end.
  lazymatch goal with Rest : rw_cells bsegs _ 6990936 [CB 232 _] |- _ => rename Rest into Slots end.
  retype Slots [CB 8 (repeat (Z_to_bv 8 0) 8); CB 8 (repeat (Z_to_bv 8 0) 8); CB 8 (repeat (Z_to_bv 8 0) 8); CB 8 (repeat (Z_to_bv 8 0) 8); CB 8 (repeat (Z_to_bv 8 0) 8); CB 8 (repeat (Z_to_bv 8 0) 8); CB 8 (repeat (Z_to_bv 8 0) 8); CB 8 (repeat (Z_to_bv 8 0) 8); CB 8 (repeat (Z_to_bv 8 0) 8); CB 8 (repeat (Z_to_bv 8 0) 8); CB 8 (repeat (Z_to_bv 8 0) 8); CB 8 (repeat (Z_to_bv 8 0) 8); CB 8 (repeat (Z_to_bv 8 0) 8); CB 8 (repeat (Z_to_bv 8 0) 8); CB 8 (repeat (Z_to_bv 8 0) 8); CB 8 (repeat (Z_to_bv 8 0) 8); CB 8 (repeat (Z_to_bv 8 0) 8); CB 8 (repeat (Z_to_bv 8 0) 8); CB 8 (repeat (Z_to_bv 8 0) 8); CB 8 (repeat (Z_to_bv 8 0) 8); CB 8 (repeat (Z_to_bv 8 0) 8); CB 8 (repeat (Z_to_bv 8 0) 8); CB 8 (repeat (Z_to_bv 8 0) 8); CB 8 (repeat (Z_to_bv 8 0) 8); CB 8 (repeat (Z_to_bv 8 0) 8); CB 8 (repeat (Z_to_bv 8 0) 8); CB 8 (repeat (Z_to_bv 8 0) 8); CB 8 (repeat (Z_to_bv 8 0) 8); CB 8 (repeat (Z_to_bv 8 0) 8)].
  take Slots 1%nat 6990944%Z SlZ01. take Slots 1%nat 6990952%Z SlZ02. take Slots 1%nat 6990960%Z SlZ03. take Slots 1%nat 6990968%Z SlZ04. take Slots 1%nat 6990976%Z SlZ05. take Slots 1%nat 6990984%Z SlZ06. take Slots 1%nat 6990992%Z SlZ07. take Slots 1%nat 6991000%Z SlZ08. take Slots 1%nat 6991008%Z SlZ09. take Slots 1%nat 6991016%Z SlZ10. take Slots 1%nat 6991024%Z SlZ11. take Slots 1%nat 6991032%Z SlZ12. take Slots 1%nat 6991040%Z SlZ13. take Slots 1%nat 6991048%Z SlZ14. take Slots 1%nat 6991056%Z SlZ15. take Slots 1%nat 6991064%Z SlZ16. take Slots 1%nat 6991072%Z SlZ17. take Slots 1%nat 6991080%Z SlZ18. take Slots 1%nat 6991088%Z SlZ19. take Slots 1%nat 6991096%Z SlZ20. take Slots 1%nat 6991104%Z SlZ21. take Slots 1%nat 6991112%Z SlZ22. take Slots 1%nat 6991120%Z SlZ23. take Slots 1%nat 6991128%Z SlZ24. take Slots 1%nat 6991136%Z SlZ25. take Slots 1%nat 6991144%Z SlZ26. take Slots 1%nat 6991152%Z SlZ27. take Slots 1%nat 6991160%Z SlZ28. take Slots 1%nat 6991168%Z SlZ29.
  clear Slots.
  acallc (seg_aevt_1 RT AF RTC MCI PMc FDO MST) clearing idtac by (first [ eassumption | a_ul | a_mod16 ]).
  acallc (seg_aevt_2 RT AF RTC MCI PMc FDO MST) clearing idtac by (first [ eassumption | a_ul | a_mod16 ]).
  acallc (seg_aevt_3 RT AF RTC MCI PMc FDO MST) clearing idtac by (first [ eassumption | a_ul | a_mod16 ]).
  acallc (seg_aevt_4 RT AF RTC MCI PMc FDO MST) clearing idtac by (first [ eassumption | a_ul | a_mod16 ]).
  acallc (seg_aevt_5 RT AF RTC MCI PMc FDO MST) clearing idtac by (first [ eassumption | a_ul | a_mod16 ]).
  acallc (seg_aevt_6 RT AF RTC MCI PMc FDO MST) clearing idtac by (first [ eassumption | a_ul | a_mod16 ]).
  acallc (seg_aevt_7 RT AF RTC MCI PMc FDO MST) clearing idtac by (first [ eassumption | a_ul | a_mod16 ]).
  acallc (seg_aevt_8 RT AF RTC MCI PMc FDO MST) clearing idtac by (first [ eassumption | a_ul | a_mod16 ]).
  acallc (seg_aevt_9 RT AF RTC MCI PMc FDO MST) clearing idtac by (first [ eassumption | a_ul | a_mod16 ]).
  acallc (seg_aevt_10 RT AF RTC MCI PMc FDO MST) clearing idtac by (first [ eassumption | a_ul | a_mod16 ]).
  acallc (seg_aevt_11 RT AF RTC MCI PMc FDO MST) clearing idtac by (first [ eassumption | a_ul | a_mod16 ]).
  acallc (seg_aevt_12 RT AF RTC MCI PMc FDO MST) clearing idtac by (first [ eassumption | a_ul | a_mod16 ]).
  acallc (seg_aevt_13 RT AF RTC MCI PMc FDO MST) clearing idtac by (first [ eassumption | a_ul | a_mod16 ]).
  acallc (seg_aevt_14 RT AF RTC MCI PMc FDO MST) clearing idtac by (first [ eassumption | a_ul | a_mod16 ]).
  acallc (seg_aevt_15 RT AF RTC MCI PMc FDO MST) clearing idtac by (first [ eassumption | a_ul | a_mod16 ]).
  acallc (seg_aevt_16 RT AF RTC MCI PMc FDO MST) clearing idtac by (first [ eassumption | a_ul | a_mod16 ]).
  acallc (seg_aevt_17 RT AF RTC MCI PMc FDO MST) clearing idtac by (first [ eassumption | a_ul | a_mod16 ]).
  acallc (seg_aevt_18 RT AF RTC MCI PMc FDO MST) clearing idtac by (first [ eassumption | a_ul | a_mod16 ]).
  acallc (seg_aevt_19 RT AF RTC MCI PMc FDO MST) clearing idtac by (first [ eassumption | a_ul | a_mod16 ]).
  acallc (seg_aevt_20 RT AF RTC MCI PMc FDO MST) clearing idtac by (first [ eassumption | a_ul | a_mod16 ]).
  acallc (seg_aevt_21 RT AF RTC MCI PMc FDO MST) clearing idtac by (first [ eassumption | a_ul | a_mod16 ]).
  acallc (seg_aevt_22 RT AF RTC MCI PMc FDO MST) clearing idtac by (first [ eassumption | a_ul | a_mod16 ]).
  acallc (seg_aevt_23 RT AF RTC MCI PMc FDO MST) clearing idtac by (first [ eassumption | a_ul | a_mod16 ]).
  acallc (seg_aevt_24 RT AF RTC MCI PMc FDO MST) clearing idtac by (first [ eassumption | a_ul | a_mod16 ]).
  acallc (seg_aevt_25 RT AF RTC MCI PMc FDO MST) clearing idtac by (first [ eassumption | a_ul | a_mod16 ]).
  lazymatch goal with Guards : rw_cells bsegs _ 6989816 [C1 _; C1 _] |- _ => take Guards 1%nat 6989817%Z ClocG0 end.
  acallc (seg_aevt_26 RT AF RTC MCI PMc FDO MST) clearing idtac by (first [ eassumption | a_ul | a_mod16 ]).
  acallc (seg_aevt_27 RT AF RTC MCI PMc FDO MST) clearing idtac by (first [ eassumption | a_ul | a_mod16 ]).
  acallc (seg_aevt_28 RT AF RTC MCI PMc FDO MST) clearing idtac by (first [ eassumption | a_ul | a_mod16 ]).
  acallc (seg_aevt_29 RT AF RTC MCI PMc FDO MST) clearing idtac by (first [ eassumption | a_ul | a_mod16 ]).
  lazymatch goal with Vec : rw_cells bsegs _ 6990904 [_; _; _] |- _ => take Vec 2%nat 6990920%Z VecLive end.
  lazymatch goal with Piece : rw_cells bsegs _ 6989352 _ |- _ => rename Piece into ImpA0 end.
  lazymatch goal with Piece : rw_cells bsegs _ 6989364 _ |- _ => glue ImpA0 Piece end.
  lazymatch goal with Piece : rw_cells bsegs _ 6989368 _ |- _ => glue ImpA0 Piece end.
  lazymatch goal with Piece : rw_cells bsegs _ 6989380 _ |- _ => glue ImpA0 Piece end.
  lazymatch goal with Piece : rw_cells bsegs _ 6989384 _ |- _ => glue ImpA0 Piece end.
  lazymatch goal with Piece : rw_cells bsegs _ 6989396 _ |- _ => glue ImpA0 Piece end.
  lazymatch goal with Piece : rw_cells bsegs _ 6989400 _ |- _ => glue ImpA0 Piece end.
  lazymatch goal with Piece : rw_cells bsegs _ 6989412 _ |- _ => glue ImpA0 Piece end.
  lazymatch type of ImpA0 with rw_cells _ _ _ ?cs => let n := eval cbn [length] in (length cs) in merge_at ImpA0 0%nat n end.
  lazymatch goal with Piece : rw_cells bsegs _ 6989416 _ |- _ => rename Piece into ImpA1 end.
  lazymatch goal with Piece : rw_cells bsegs _ 6989428 _ |- _ => rename Piece into ImpA2 end.
  lazymatch goal with Piece : rw_cells bsegs _ 6989432 _ |- _ => glue ImpA2 Piece end.
  lazymatch goal with Piece : rw_cells bsegs _ 6989444 _ |- _ => glue ImpA2 Piece end.
  lazymatch goal with Piece : rw_cells bsegs _ 6989448 _ |- _ => glue ImpA2 Piece end.
  lazymatch goal with Piece : rw_cells bsegs _ 6989460 _ |- _ => glue ImpA2 Piece end.
  lazymatch goal with Piece : rw_cells bsegs _ 6989464 _ |- _ => glue ImpA2 Piece end.
  lazymatch goal with Piece : rw_cells bsegs _ 6989476 _ |- _ => glue ImpA2 Piece end.
  lazymatch goal with Piece : rw_cells bsegs _ 6989480 _ |- _ => glue ImpA2 Piece end.
  lazymatch goal with Piece : rw_cells bsegs _ 6989492 _ |- _ => glue ImpA2 Piece end.
  lazymatch goal with Piece : rw_cells bsegs _ 6989496 _ |- _ => glue ImpA2 Piece end.
  lazymatch goal with Piece : rw_cells bsegs _ 6989508 _ |- _ => glue ImpA2 Piece end.
  lazymatch goal with Piece : rw_cells bsegs _ 6989512 _ |- _ => glue ImpA2 Piece end.
  lazymatch goal with Piece : rw_cells bsegs _ 6989524 _ |- _ => glue ImpA2 Piece end.
  lazymatch goal with Piece : rw_cells bsegs _ 6989528 _ |- _ => glue ImpA2 Piece end.
  lazymatch goal with Piece : rw_cells bsegs _ 6989540 _ |- _ => glue ImpA2 Piece end.
  lazymatch goal with Piece : rw_cells bsegs _ 6989544 _ |- _ => glue ImpA2 Piece end.
  lazymatch goal with Piece : rw_cells bsegs _ 6989556 _ |- _ => glue ImpA2 Piece end.
  lazymatch goal with Piece : rw_cells bsegs _ 6989560 _ |- _ => glue ImpA2 Piece end.
  lazymatch goal with Piece : rw_cells bsegs _ 6989572 _ |- _ => glue ImpA2 Piece end.
  lazymatch goal with Piece : rw_cells bsegs _ 6989576 _ |- _ => glue ImpA2 Piece end.
  lazymatch goal with Piece : rw_cells bsegs _ 6989588 _ |- _ => glue ImpA2 Piece end.
  lazymatch goal with Piece : rw_cells bsegs _ 6989592 _ |- _ => glue ImpA2 Piece end.
  lazymatch goal with Piece : rw_cells bsegs _ 6989604 _ |- _ => glue ImpA2 Piece end.
  lazymatch goal with Piece : rw_cells bsegs _ 6989608 _ |- _ => glue ImpA2 Piece end.
  lazymatch goal with Piece : rw_cells bsegs _ 6989620 _ |- _ => glue ImpA2 Piece end.
  lazymatch goal with Piece : rw_cells bsegs _ 6989624 _ |- _ => glue ImpA2 Piece end.
  lazymatch goal with Piece : rw_cells bsegs _ 6989636 _ |- _ => glue ImpA2 Piece end.
  lazymatch goal with Piece : rw_cells bsegs _ 6989640 _ |- _ => glue ImpA2 Piece end.
  lazymatch goal with Piece : rw_cells bsegs _ 6989652 _ |- _ => glue ImpA2 Piece end.
  lazymatch goal with Piece : rw_cells bsegs _ 6989656 _ |- _ => glue ImpA2 Piece end.
  lazymatch goal with Piece : rw_cells bsegs _ 6989668 _ |- _ => glue ImpA2 Piece end.
  lazymatch goal with Piece : rw_cells bsegs _ 6989672 _ |- _ => glue ImpA2 Piece end.
  lazymatch goal with Piece : rw_cells bsegs _ 6989676 _ |- _ => glue ImpA2 Piece end.
  lazymatch goal with Piece : rw_cells bsegs _ 6989680 _ |- _ => glue ImpA2 Piece end.
  lazymatch goal with Piece : rw_cells bsegs _ 6989692 _ |- _ => glue ImpA2 Piece end.
  lazymatch goal with Piece : rw_cells bsegs _ 6989696 _ |- _ => glue ImpA2 Piece end.
  lazymatch goal with Piece : rw_cells bsegs _ 6989708 _ |- _ => glue ImpA2 Piece end.
  lazymatch goal with Piece : rw_cells bsegs _ 6989712 _ |- _ => glue ImpA2 Piece end.
  lazymatch goal with Piece : rw_cells bsegs _ 6989724 _ |- _ => glue ImpA2 Piece end.
  lazymatch goal with Piece : rw_cells bsegs _ 6989728 _ |- _ => glue ImpA2 Piece end.
  lazymatch goal with Piece : rw_cells bsegs _ 6989740 _ |- _ => glue ImpA2 Piece end.
  lazymatch goal with Piece : rw_cells bsegs _ 6989744 _ |- _ => glue ImpA2 Piece end.
  lazymatch goal with Piece : rw_cells bsegs _ 6989756 _ |- _ => glue ImpA2 Piece end.
  lazymatch goal with Piece : rw_cells bsegs _ 6989760 _ |- _ => glue ImpA2 Piece end.
  lazymatch goal with Piece : rw_cells bsegs _ 6989772 _ |- _ => glue ImpA2 Piece end.
  lazymatch type of ImpA2 with rw_cells _ _ _ ?cs => let n := eval cbn [length] in (length cs) in merge_at ImpA2 0%nat n end.
  lazymatch goal with Piece : rw_cells bsegs _ 6989808 _ |- _ => rename Piece into ImpA3 end.
  lazymatch goal with Piece : rw_cells bsegs _ 6989816 _ |- _ => glue ImpA3 Piece end.
  lazymatch goal with Piece : rw_cells bsegs _ 6989817 _ |- _ => glue ImpA3 Piece end.
  lazymatch goal with Piece : rw_cells bsegs _ 6989818 _ |- _ => rename Piece into ImpA4 end.
  lazymatch type of ImpA4 with rw_cells _ _ _ ?cs => let n := eval cbn [length] in (length cs) in merge_at ImpA4 0%nat n end.
  glue ImpA0 ImpA1.
  glue ImpA0 ImpA2.
  glue ImpA0 ImpA3.
  glue ImpA0 ImpA4.
  rename ImpA0 into ImpA.
  lazymatch goal with Piece : rw_cells bsegs _ 6989856 _ |- _ => rename Piece into ImpB0 end.
  lazymatch goal with Piece : rw_cells bsegs _ 6990032 _ |- _ => glue ImpB0 Piece end.
  lazymatch goal with Piece : rw_cells bsegs _ 6990044 _ |- _ => glue ImpB0 Piece end.
  lazymatch type of ImpB0 with rw_cells _ _ _ ?cs => let n := eval cbn [length] in (length cs) in merge_at ImpB0 0%nat n end.
  lazymatch goal with Piece : rw_cells bsegs _ 6990048 _ |- _ => rename Piece into ImpB1 end.
  lazymatch goal with Piece : rw_cells bsegs _ 6990060 _ |- _ => rename Piece into ImpB2 end.
  lazymatch type of ImpB2 with rw_cells _ _ _ ?cs => let n := eval cbn [length] in (length cs) in merge_at ImpB2 0%nat n end.
  lazymatch goal with Piece : rw_cells bsegs _ 6990064 _ |- _ => rename Piece into ImpB3 end.
  lazymatch goal with Piece : rw_cells bsegs _ 6990076 _ |- _ => rename Piece into ImpB4 end.
  lazymatch goal with Piece : rw_cells bsegs _ 6990080 _ |- _ => glue ImpB4 Piece end.
  lazymatch goal with Piece : rw_cells bsegs _ 6990092 _ |- _ => glue ImpB4 Piece end.
  lazymatch goal with Piece : rw_cells bsegs _ 6990096 _ |- _ => glue ImpB4 Piece end.
  lazymatch goal with Piece : rw_cells bsegs _ 6990104 _ |- _ => glue ImpB4 Piece end.
  lazymatch goal with Piece : rw_cells bsegs _ 6990112 _ |- _ => glue ImpB4 Piece end.
  lazymatch goal with Piece : rw_cells bsegs _ 6990120 _ |- _ => glue ImpB4 Piece end.
  lazymatch goal with Piece : rw_cells bsegs _ 6990128 _ |- _ => glue ImpB4 Piece end.
  lazymatch goal with Piece : rw_cells bsegs _ 6990136 _ |- _ => glue ImpB4 Piece end.
  lazymatch goal with Piece : rw_cells bsegs _ 6990144 _ |- _ => glue ImpB4 Piece end.
  lazymatch goal with Piece : rw_cells bsegs _ 6990152 _ |- _ => glue ImpB4 Piece end.
  lazymatch goal with Piece : rw_cells bsegs _ 6990160 _ |- _ => glue ImpB4 Piece end.
  lazymatch goal with Piece : rw_cells bsegs _ 6990168 _ |- _ => glue ImpB4 Piece end.
  lazymatch goal with Piece : rw_cells bsegs _ 6990176 _ |- _ => glue ImpB4 Piece end.
  lazymatch goal with Piece : rw_cells bsegs _ 6990184 _ |- _ => glue ImpB4 Piece end.
  lazymatch goal with Piece : rw_cells bsegs _ 6990192 _ |- _ => glue ImpB4 Piece end.
  lazymatch goal with Piece : rw_cells bsegs _ 6990200 _ |- _ => glue ImpB4 Piece end.
  lazymatch goal with Piece : rw_cells bsegs _ 6990208 _ |- _ => glue ImpB4 Piece end.
  lazymatch goal with Piece : rw_cells bsegs _ 6990216 _ |- _ => glue ImpB4 Piece end.
  lazymatch goal with Piece : rw_cells bsegs _ 6990224 _ |- _ => glue ImpB4 Piece end.
  lazymatch goal with Piece : rw_cells bsegs _ 6990232 _ |- _ => glue ImpB4 Piece end.
  lazymatch goal with Piece : rw_cells bsegs _ 6990240 _ |- _ => glue ImpB4 Piece end.
  lazymatch goal with Piece : rw_cells bsegs _ 6990248 _ |- _ => glue ImpB4 Piece end.
  lazymatch type of ImpB4 with rw_cells _ _ _ ?cs => let n := eval cbn [length] in (length cs) in merge_at ImpB4 0%nat n end.
  lazymatch goal with Piece : rw_cells bsegs _ 6990256 _ |- _ => rename Piece into ImpB5 end.
  lazymatch goal with Piece : rw_cells bsegs _ 6990264 _ |- _ => rename Piece into ImpB6 end.
  lazymatch goal with Piece : rw_cells bsegs _ 6990272 _ |- _ => glue ImpB6 Piece end.
  lazymatch goal with Piece : rw_cells bsegs _ 6990280 _ |- _ => glue ImpB6 Piece end.
  lazymatch goal with Piece : rw_cells bsegs _ 6990288 _ |- _ => glue ImpB6 Piece end.
  lazymatch goal with Piece : rw_cells bsegs _ 6990296 _ |- _ => glue ImpB6 Piece end.
  lazymatch goal with Piece : rw_cells bsegs _ 6990304 _ |- _ => glue ImpB6 Piece end.
  lazymatch goal with Piece : rw_cells bsegs _ 6990312 _ |- _ => glue ImpB6 Piece end.
  lazymatch goal with Piece : rw_cells bsegs _ 6990320 _ |- _ => glue ImpB6 Piece end.
  lazymatch goal with Piece : rw_cells bsegs _ 6990328 _ |- _ => glue ImpB6 Piece end.
  lazymatch goal with Piece : rw_cells bsegs _ 6990336 _ |- _ => glue ImpB6 Piece end.
  lazymatch goal with Piece : rw_cells bsegs _ 6990344 _ |- _ => glue ImpB6 Piece end.
  lazymatch goal with Piece : rw_cells bsegs _ 6990352 _ |- _ => glue ImpB6 Piece end.
  lazymatch goal with Piece : rw_cells bsegs _ 6990360 _ |- _ => glue ImpB6 Piece end.
  lazymatch goal with Piece : rw_cells bsegs _ 6990368 _ |- _ => glue ImpB6 Piece end.
  lazymatch goal with Piece : rw_cells bsegs _ 6990376 _ |- _ => glue ImpB6 Piece end.
  lazymatch goal with Piece : rw_cells bsegs _ 6990384 _ |- _ => glue ImpB6 Piece end.
  lazymatch goal with Piece : rw_cells bsegs _ 6990392 _ |- _ => glue ImpB6 Piece end.
  lazymatch goal with Piece : rw_cells bsegs _ 6990400 _ |- _ => glue ImpB6 Piece end.
  lazymatch goal with Piece : rw_cells bsegs _ 6990408 _ |- _ => glue ImpB6 Piece end.
  lazymatch goal with Piece : rw_cells bsegs _ 6990416 _ |- _ => glue ImpB6 Piece end.
  lazymatch goal with Piece : rw_cells bsegs _ 6990424 _ |- _ => glue ImpB6 Piece end.
  lazymatch goal with Piece : rw_cells bsegs _ 6990432 _ |- _ => glue ImpB6 Piece end.
  lazymatch goal with Piece : rw_cells bsegs _ 6990440 _ |- _ => glue ImpB6 Piece end.
  lazymatch goal with Piece : rw_cells bsegs _ 6990448 _ |- _ => glue ImpB6 Piece end.
  lazymatch goal with Piece : rw_cells bsegs _ 6990544 _ |- _ => glue ImpB6 Piece end.
  lazymatch goal with Piece : rw_cells bsegs _ 6990552 _ |- _ => glue ImpB6 Piece end.
  lazymatch goal with Piece : rw_cells bsegs _ 6990560 _ |- _ => glue ImpB6 Piece end.
  lazymatch goal with Piece : rw_cells bsegs _ 6990568 _ |- _ => glue ImpB6 Piece end.
  lazymatch goal with Piece : rw_cells bsegs _ 6990576 _ |- _ => glue ImpB6 Piece end.
  lazymatch goal with Piece : rw_cells bsegs _ 6990584 _ |- _ => glue ImpB6 Piece end.
  lazymatch goal with Piece : rw_cells bsegs _ 6990592 _ |- _ => glue ImpB6 Piece end.
  lazymatch goal with Piece : rw_cells bsegs _ 6990600 _ |- _ => glue ImpB6 Piece end.
  lazymatch goal with Piece : rw_cells bsegs _ 6990608 _ |- _ => glue ImpB6 Piece end.
  lazymatch goal with Piece : rw_cells bsegs _ 6990616 _ |- _ => glue ImpB6 Piece end.
  lazymatch goal with Piece : rw_cells bsegs _ 6990624 _ |- _ => glue ImpB6 Piece end.
  lazymatch goal with Piece : rw_cells bsegs _ 6990632 _ |- _ => glue ImpB6 Piece end.
  lazymatch goal with Piece : rw_cells bsegs _ 6990640 _ |- _ => glue ImpB6 Piece end.
  lazymatch goal with Piece : rw_cells bsegs _ 6990648 _ |- _ => glue ImpB6 Piece end.
  lazymatch goal with Piece : rw_cells bsegs _ 6990656 _ |- _ => glue ImpB6 Piece end.
  lazymatch type of ImpB6 with rw_cells _ _ _ ?cs => let n := eval cbn [length] in (length cs) in merge_at ImpB6 0%nat n end.
  lazymatch goal with Piece : rw_cells bsegs _ 6990664 _ |- _ => rename Piece into ImpB7 end.
  lazymatch goal with Piece : rw_cells bsegs _ 6990672 _ |- _ => rename Piece into ImpB8 end.
  lazymatch goal with Piece : rw_cells bsegs _ 6990680 _ |- _ => glue ImpB8 Piece end.
  lazymatch goal with Piece : rw_cells bsegs _ 6990688 _ |- _ => glue ImpB8 Piece end.
  lazymatch goal with Piece : rw_cells bsegs _ 6990689 _ |- _ => glue ImpB8 Piece end.
  lazymatch type of ImpB8 with rw_cells _ _ _ ?cs => let n := eval cbn [length] in (length cs) in merge_at ImpB8 0%nat n end.
  lazymatch goal with Piece : rw_cells bsegs _ 6990792 _ |- _ => rename Piece into ImpB9 end.
  lazymatch goal with Piece : rw_cells bsegs _ 6990800 _ |- _ => rename Piece into ImpB10 end.
  lazymatch type of ImpB10 with rw_cells _ _ _ ?cs => let n := eval cbn [length] in (length cs) in merge_at ImpB10 0%nat n end.
  lazymatch goal with Piece : rw_cells bsegs _ 6990808 _ |- _ => rename Piece into ImpB11 end.
  lazymatch goal with Piece : rw_cells bsegs _ 6990810 _ |- _ => rename Piece into ImpB12 end.
  lazymatch type of ImpB12 with rw_cells _ _ _ ?cs => let n := eval cbn [length] in (length cs) in merge_at ImpB12 0%nat n end.
  lazymatch goal with Piece : rw_cells bsegs _ 6990816 _ |- _ => rename Piece into ImpB13 end.
  lazymatch goal with Piece : rw_cells bsegs _ 6990824 _ |- _ => glue ImpB13 Piece end.
  lazymatch goal with Piece : rw_cells bsegs _ 6990832 _ |- _ => glue ImpB13 Piece end.
  lazymatch goal with Piece : rw_cells bsegs _ 6990840 _ |- _ => rename Piece into ImpB14 end.
  lazymatch goal with Piece : rw_cells bsegs _ 6990848 _ |- _ => glue ImpB14 Piece end.
  lazymatch goal with Piece : rw_cells bsegs _ 6990856 _ |- _ => glue ImpB14 Piece end.
  lazymatch goal with Piece : rw_cells bsegs _ 6990864 _ |- _ => glue ImpB14 Piece end.
  lazymatch goal with Piece : rw_cells bsegs _ 6990872 _ |- _ => glue ImpB14 Piece end.
  lazymatch goal with Piece : rw_cells bsegs _ 6990880 _ |- _ => glue ImpB14 Piece end.
  lazymatch goal with Piece : rw_cells bsegs _ 6990888 _ |- _ => glue ImpB14 Piece end.
  lazymatch type of ImpB14 with rw_cells _ _ _ ?cs => let n := eval cbn [length] in (length cs) in merge_at ImpB14 0%nat n end.
  lazymatch goal with Piece : rw_cells bsegs _ 6990904 _ |- _ => rename Piece into ImpB15 end.
  lazymatch goal with Piece : rw_cells bsegs _ 6990920 _ |- _ => rename Piece into ImpB16 end.
  lazymatch goal with Piece : rw_cells bsegs _ 6990928 _ |- _ => glue ImpB16 Piece end.
  lazymatch goal with Piece : rw_cells bsegs _ 6990936 _ |- _ => glue ImpB16 Piece end.
  lazymatch type of ImpB16 with rw_cells _ _ _ ?cs => let n := eval cbn [length] in (length cs) in merge_at ImpB16 0%nat n end.
  lazymatch goal with Piece : rw_cells bsegs _ 6990944 _ |- _ => rename Piece into ImpB17 end.
  lazymatch goal with Piece : rw_cells bsegs _ 6990952 _ |- _ => rename Piece into ImpB18 end.
  lazymatch goal with Piece : rw_cells bsegs _ 6990960 _ |- _ => glue ImpB18 Piece end.
  lazymatch goal with Piece : rw_cells bsegs _ 6990968 _ |- _ => glue ImpB18 Piece end.
  lazymatch goal with Piece : rw_cells bsegs _ 6990976 _ |- _ => glue ImpB18 Piece end.
  lazymatch goal with Piece : rw_cells bsegs _ 6990984 _ |- _ => glue ImpB18 Piece end.
  lazymatch goal with Piece : rw_cells bsegs _ 6990992 _ |- _ => glue ImpB18 Piece end.
  lazymatch goal with Piece : rw_cells bsegs _ 6991000 _ |- _ => glue ImpB18 Piece end.
  lazymatch type of ImpB18 with rw_cells _ _ _ ?cs => let n := eval cbn [length] in (length cs) in merge_at ImpB18 0%nat n end.
  lazymatch goal with Piece : rw_cells bsegs _ 6991008 _ |- _ => rename Piece into ImpB19 end.
  lazymatch goal with Piece : rw_cells bsegs _ 6991016 _ |- _ => rename Piece into ImpB20 end.
  lazymatch goal with Piece : rw_cells bsegs _ 6991024 _ |- _ => glue ImpB20 Piece end.
  lazymatch goal with Piece : rw_cells bsegs _ 6991032 _ |- _ => glue ImpB20 Piece end.
  lazymatch type of ImpB20 with rw_cells _ _ _ ?cs => let n := eval cbn [length] in (length cs) in merge_at ImpB20 0%nat n end.
  lazymatch goal with Piece : rw_cells bsegs _ 6991040 _ |- _ => rename Piece into ImpB21 end.
  lazymatch goal with Piece : rw_cells bsegs _ 6991048 _ |- _ => rename Piece into ImpB22 end.
  lazymatch goal with Piece : rw_cells bsegs _ 6991056 _ |- _ => glue ImpB22 Piece end.
  lazymatch goal with Piece : rw_cells bsegs _ 6991064 _ |- _ => glue ImpB22 Piece end.
  lazymatch goal with Piece : rw_cells bsegs _ 6991072 _ |- _ => glue ImpB22 Piece end.
  lazymatch goal with Piece : rw_cells bsegs _ 6991080 _ |- _ => glue ImpB22 Piece end.
  lazymatch goal with Piece : rw_cells bsegs _ 6991088 _ |- _ => glue ImpB22 Piece end.
  lazymatch goal with Piece : rw_cells bsegs _ 6991096 _ |- _ => glue ImpB22 Piece end.
  lazymatch goal with Piece : rw_cells bsegs _ 6991104 _ |- _ => glue ImpB22 Piece end.
  lazymatch goal with Piece : rw_cells bsegs _ 6991112 _ |- _ => glue ImpB22 Piece end.
  lazymatch goal with Piece : rw_cells bsegs _ 6991120 _ |- _ => glue ImpB22 Piece end.
  lazymatch goal with Piece : rw_cells bsegs _ 6991128 _ |- _ => glue ImpB22 Piece end.
  lazymatch goal with Piece : rw_cells bsegs _ 6991136 _ |- _ => glue ImpB22 Piece end.
  lazymatch goal with Piece : rw_cells bsegs _ 6991144 _ |- _ => glue ImpB22 Piece end.
  lazymatch goal with Piece : rw_cells bsegs _ 6991152 _ |- _ => glue ImpB22 Piece end.
  lazymatch goal with Piece : rw_cells bsegs _ 6991160 _ |- _ => glue ImpB22 Piece end.
  lazymatch goal with Piece : rw_cells bsegs _ 6991168 _ |- _ => glue ImpB22 Piece end.
  lazymatch goal with Piece : rw_cells bsegs _ 6991179 _ |- _ => glue ImpB22 Piece end.
  lazymatch goal with Piece : rw_cells bsegs _ 6993024 _ |- _ => glue ImpB22 Piece end.
  lazymatch goal with Piece : rw_cells bsegs _ 6993036 _ |- _ => glue ImpB22 Piece end.
  lazymatch goal with Piece : rw_cells bsegs _ 6993064 _ |- _ => glue ImpB22 Piece end.
  lazymatch type of ImpB22 with rw_cells _ _ _ ?cs => let n := eval cbn [length] in (length cs) in merge_at ImpB22 0%nat n end.
  glue ImpB0 ImpB1.
  glue ImpB0 ImpB2.
  glue ImpB0 ImpB3.
  glue ImpB0 ImpB4.
  glue ImpB0 ImpB5.
  glue ImpB0 ImpB6.
  glue ImpB0 ImpB7.
  glue ImpB0 ImpB8.
  glue ImpB0 ImpB9.
  glue ImpB0 ImpB10.
  glue ImpB0 ImpB11.
  glue ImpB0 ImpB12.
  glue ImpB0 ImpB13.
  glue ImpB0 ImpB14.
  glue ImpB0 ImpB15.
  glue ImpB0 ImpB16.
  glue ImpB0 ImpB17.
  glue ImpB0 ImpB18.
  glue ImpB0 ImpB19.
  glue ImpB0 ImpB20.
  glue ImpB0 ImpB21.
  glue ImpB0 ImpB22.
  rename ImpB0 into ImpB.
  unname_sp.
  repeat lstep.
  lazymatch goal with Low : stk bsegs _ lo (bv_unsigned sp + -48) |- _ => release_frame Saved Low (bv_unsigned sp) end.
  afinish.
Qed.

End AevtPieces.
