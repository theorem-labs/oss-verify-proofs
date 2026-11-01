(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump_raw_tape.lib.AS Require Import ShapeAlg AsanAcct.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump_raw_tape.lib.Lib Require Import Tac Arr Bytes ITree Nodes Decode SysStep RegsEquiv ImageA RzCPS StoreFast FP.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump_raw_tape.lib.Spec Require Import Prelim StrFun.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump_raw_tape.lib.P Require Import Str_tac Startup_glue Pj_steps.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump_raw_tape.lib.A Require Import Shadow IcptSpec.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump_raw_tape.lib.B Require Import Layout RT_iface RT_iface2 D_defs D_kit D_clx D_rlkit D_libiface Sj_rtf Sj_akit Sj_acps Sj_hkit Sj_new Sj_num_akit Sj_num_amem Pj_mciA Pj_loc_akitA Pj_onceA.
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

Definition call_once_post_11 (ra sp gp tp t0 t1 t2 s0 s1 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (lo k : Z) (canary : word) (pad1 j8 : list byte) (pad2 : word) (m : mem)
    : machine_state -> Prop :=
  fun st => exists (r0 r1 r2 r3 r4 r5 : word) (mx : mem),
    st = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 r0 r1 r2 r3 r4 r5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (ret_pc ra) fc None mx (seg_rom bsegs)
    /\ munch [(bv_unsigned sp - 160, bv_unsigned sp - 64); (bv_unsigned sp - 56, bv_unsigned sp); (6989672, 6989676); (6990080, 6990092);
              (6993028, 6993032); (6993072, 6993080); (6993096, 6993100); (6993104, 6993112)]%Z m mx
    /\ wmono bsegs m mx /\ mem_inv bsegs mx
    /\ stk bsegs mx lo (bv_unsigned sp)
    /\ rw_cells bsegs mx (bv_unsigned sp)
         [CB 8 j8; C8 (Z_to_bv 64 6990080); C8 (Z_to_bv 64 (bv_unsigned sp + 24)); C8 (Z_to_bv 64 (bv_unsigned sp + 8))]
    /\ rw_cells bsegs mx 6990080 [C8 (Z_to_bv 64 (-1)); C4 (Z_to_bv 64 (k + 1))]
    /\ rw_cells bsegs mx 6989672 [C4 (Z_to_bv 64 (k + 1))]
    /\ rw_cells bsegs mx 6993024 [CB 4 (repeat (Z_to_bv 8 0) 4); C4 z64; C4 z64]
    /\ ro_cells bsegs mx 7126568 [C8 canary]
    /\ rw_cells bsegs mx 6993064 [C8 z64; C8 z64; CB 16 pad1; C4 z64; C4 pad2; C8 z64].

Lemma call_once_spec_11 : forall ra sp gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (lo k : Z) (canary tl idv : word) (pad1 j8 : list byte) (pad2 : word),
  stk bsegs m lo (bv_unsigned sp) -> (lo <= bv_unsigned sp - 160)%Z -> (0x6ce000 <= lo)%Z -> (bv_unsigned sp + 32 < 2^63)%Z ->
  rw_cells bsegs m (bv_unsigned sp) [CB 8 j8; C8 (Z_to_bv 64 0x6aa900); C8 (Z_to_bv 64 (bv_unsigned sp + 24)); C8 (Z_to_bv 64 (bv_unsigned sp + 8))] ->
  rw_cells bsegs m 0x6aa900 [C8 (Z_to_bv 64 0); C4 idv] ->
  rw_cells bsegs m 0x6aa768 [C4 (Z_to_bv 64 k)] -> (0 <= k < 30)%Z ->
  rw_cells bsegs m 0x6ab480 [CB 4 (repeat (Z_to_bv 8 0) 4); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0)] ->
  ro_cells bsegs m 0x16f508 [C8 (Z_to_bv 64 0x6cbe28)] -> ro_cells bsegs m 0x6cbe28 [C8 canary] ->
  rw_cells bsegs m 0x6ab4a8 [C8 (Z_to_bv 64 0); C8 tl; CB 16 pad1; C4 (Z_to_bv 64 0); C4 pad2; C8 (Z_to_bv 64 0)] ->
  length pad1 = 16%nat -> mem_inv bsegs m ->
  evt bsegs (call_once_post_11 ra sp gp tp t0 t1 t2 s0 s1 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc lo k canary pad1 j8 pad2 m)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 0x6aa900) (Z_to_bv 64 (bv_unsigned sp + 16)) (Z_to_bv 64 0x14637c) a3 a4 a5 a6 a7
               s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x147b40) fc None m (seg_rom bsegs)).
Proof.
  intros until pad2. intros STK LOW FLOOR TOP ARGS IDC NXT KRNG MTX GOTE CAN CNDV PADL MINV.
  assert (SPR : (0 <= bv_unsigned sp < 2^64)%Z) by apply bv_unsigned_in_range.
  pose proof (munch_refl [(bv_unsigned sp - 160, bv_unsigned sp - 64); (bv_unsigned sp - 56, bv_unsigned sp); (6989672, 6989676); (6990080, 6990092);
                          (6993028, 6993032); (6993072, 6993080); (6993096, 6993100); (6993104, 6993112)]%Z m) as MU.
  pose proof (wmono_refl bsegs m) as WM.
  carve_frame 64%nat STK.
  do 15 lstep.
  call_sp mutex_lock_spec; [exact MTX | assumption | ].
  rename POST into MTX, MI into MINV.
  do 3 lstep. if_true.
  do 2 lstep. if_true.
  do 5 lstep.
  call_sp mutex_unlock_spec; [exact STK | lia | lia | exact MTX | assumption | ].
  rename PC into STK, POST into MTX, MI into MINV.
  do 8 lstep.
  amo_step. amo32_fix_lit.
  replace (sx32 (Z_to_bv 64 k)) with (Z_to_bv 64 k)
    by (unfold sx32; f_equal; rewrite unsigned_lit by lia; symmetry; apply swrap32_small; lia).
  do 6 lstep.
  call_sp mutex_lock_spec; [exact MTX | assumption | ].
  rename POST into MTX, MI into MINV.
  do 7 lstep.
  call_sp mutex_unlock_spec; [exact STK | lia | lia | exact MTX | assumption | ].
  rename PC into STK, POST into MTX, MI into MINV.
  do 2 lstep.
  call_sp cond_broadcast_spec; [exact STK | lia | lia | exact GOTE | exact CAN | exact CNDV | exact PADL | assumption | ].
  rename PC into STK, POST into CNDV, MI into MINV.
  do 9 lstep.
  release_frame FR STK (bv_unsigned sp).
  unfold call_once_post_11. sys_finish.
Qed.

Section AevtPieces.
Variable RT : rt_sig.
Hypothesis AF : art_facts RT.
Hypothesis RTC : rt_contracts RT.
Hypothesis MCI : memcmp_inner_icontract RT.
Variable PMc : Model -> Prop.
Hypothesis FDO : fdfs_only PMc.
Hypothesis MST : mat_stable PMc.

Definition append_postA_11 (Σ : rts RT) (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (fc : bv 32) (lo : Z) (m : mem)
    : machine_state -> Prop :=
  fun st => exists (t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (F' : bvmap 5 word) (mx : mem),
    st = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F' (ret_pc ra) fc None mx (seg_rom bsegs)
    /\ rt_pres_fp (rt_live RT Σ) (rt_frames RT Σ) (bv_unsigned sp) [(6990912, 6990920); (6991016, 6991024)]%Z m mx
    /\ wmono bsegs m mx /\ mem_inv bsegs mx /\ ART RT Σ mx
    /\ stk bsegs mx lo (bv_unsigned sp)
    /\ rw_cells bsegs mx 6990904 [C8 (Z_to_bv 64 6990928); C8 (Z_to_bv 64 6991024); C8 (Z_to_bv 64 6991168)]
    /\ rw_cells bsegs mx 6991016 [CB 8 (repeat (Z_to_bv 8 0) 8)].

Lemma append_aevt_11 : forall Σ K ra sp gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (lo : Z) (junk8 : list byte),
  stk bsegs m lo (bv_unsigned sp) -> (lo + 80 + RT_STACK <= bv_unsigned sp)%Z -> (rt_sp0 RT Σ - STACK_WIN <= lo)%Z ->
  (bv_unsigned sp + 16 <= USTACK_TOP)%Z -> (bv_unsigned sp mod 16 = 0)%Z ->
  rw_cells bsegs m 0x6aac38 [C8 (Z_to_bv 64 0x6aac50); C8 (Z_to_bv 64 0x6aaca8); C8 (Z_to_bv 64 0x6aad40)] ->
  rw_cells bsegs m 0x6aaca8 [CB 8 junk8] -> mem_inv bsegs m -> ART RT Σ m ->
  (forall ms', append_postA_11 Σ ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 fc lo m ms' -> aevt RT PMc Σ K ms') ->
  aevt RT PMc Σ K (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 0x6aac38) (Z_to_bv 64 1) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x14502c) fc None m (seg_rom bsegs)).
Proof using AF RTC MCI FDO MST.
  intros Σ K ra sp gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo junk8.
  intros STK ROOM WIN TOP ALGN VEC SLOT MINV ARTIN CONT.
  pose proof (wmono_refl bsegs m) as WM.
  astart (bv_unsigned sp) [(6990912, 6990920); (6991016, 6991024)]%Z.
  assert (SPR : (0 <= bv_unsigned sp < 2^64)%Z) by apply bv_unsigned_in_range.
  pose proof (munch_refl [(bv_unsigned sp - 80, bv_unsigned sp); (6990912, 6990920)]%Z m) as MU.
  apply (aevt_evt RT AF PMc MST).
  carve_frame 80%nat STK.
  do 17 lstep. if_true.
  lstep. if_false.
  do 5 lstep.
  acall_sp (memsetA_spec RT RTC PMc FDO MST); [exact SLOT | lia | lia | lia | lia | a_chk | a_cl | exact ARTX | assumption | a_call_ok | ].
  apost_call.
  rename PC into STK, POST into SLOT, MI into MINV.
  change (Z.to_nat 8) with 8%nat in SLOT. change (0 mod 256)%Z with 0%Z in SLOT.
  do 15 lstep.
  release_frame FR STK (bv_unsigned sp).
  afinish.
Qed.

Definition install_postA_11 (Σ : rts RT) (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (fc : bv 32)
    (lo v : Z) (canary : word) (pad1 : list byte) (pad2 : word) (m : mem) : machine_state -> Prop :=
  fun st => exists (t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (F' : bvmap 5 word) (mx : mem),
    st = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F' (ret_pc ra) fc None mx (seg_rom bsegs)
    /\ rt_pres_fp (rt_live RT Σ) (rt_frames RT Σ) (bv_unsigned sp)
         [(6989672, 6989676); (6990080, 6990092); (6990848, 6990856); (6990912, 6990920); (6991016, 6991024);
          (6993028, 6993032); (6993072, 6993080); (6993096, 6993100); (6993104, 6993112)]%Z m mx
    /\ wmono bsegs m mx /\ mem_inv bsegs mx /\ ART RT Σ mx
    /\ stk bsegs mx lo (bv_unsigned sp)
    /\ rw_cells bsegs mx 6990080 [C8 (Z_to_bv 64 (-1)); C4 (Z_to_bv 64 12)]
    /\ rw_cells bsegs mx 6989672 [C4 (Z_to_bv 64 12)]
    /\ rw_cells bsegs mx 6990848 [C8 (Z_to_bv 64 (v + 1))]
    /\ rw_cells bsegs mx 6990904 [C8 (Z_to_bv 64 6990928); C8 (Z_to_bv 64 6991024); C8 (Z_to_bv 64 6991168)]
    /\ rw_cells bsegs mx 6991016 [C8 (Z_to_bv 64 6990840)]
    /\ rw_cells bsegs mx 6993024 [CB 4 (repeat (Z_to_bv 8 0) 4); C4 z64; C4 z64]
    /\ ro_cells bsegs mx 7126568 [C8 canary]
    /\ rw_cells bsegs mx 6993064 [C8 z64; C8 z64; CB 16 pad1; C4 z64; C4 pad2; C8 z64].

Lemma install_aevt_11 : forall Σ K ra sp gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (lo v : Z) (canary tl idv : word) (pad1 junk8 : list byte) (pad2 : word),
  stk bsegs m lo (bv_unsigned sp) -> (lo + 240 + RT_STACK <= bv_unsigned sp)%Z -> (rt_sp0 RT Σ - STACK_WIN <= lo)%Z ->
  (bv_unsigned sp + 16 <= USTACK_TOP)%Z -> (bv_unsigned sp mod 16 = 0)%Z -> (bv_unsigned sp < 2^62)%Z ->
  rw_cells bsegs m 0x6aa900 [C8 (Z_to_bv 64 0); C4 idv] ->
  rw_cells bsegs m 0x6aa768 [C4 (Z_to_bv 64 11)] ->
  rw_cells bsegs m 0x6aac00 [C8 (Z_to_bv 64 v)] -> (0 <= v < 2^62)%Z ->
  rw_cells bsegs m 0x6aac38 [C8 (Z_to_bv 64 0x6aac50); C8 (Z_to_bv 64 0x6aaca8); C8 (Z_to_bv 64 0x6aad40)] ->
  rw_cells bsegs m 0x6aaca8 [CB 8 junk8] ->
  rw_cells bsegs m 0x6ab480 [CB 4 (repeat (Z_to_bv 8 0) 4); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0)] ->
  ro_cells bsegs m 0x16f508 [C8 (Z_to_bv 64 0x6cbe28)] -> ro_cells bsegs m 0x6cbe28 [C8 canary] ->
  rw_cells bsegs m 0x6ab4a8 [C8 (Z_to_bv 64 0); C8 tl; CB 16 pad1; C4 (Z_to_bv 64 0); C4 pad2; C8 (Z_to_bv 64 0)] ->
  length pad1 = 16%nat -> mem_inv bsegs m -> ART RT Σ m ->
  (forall ms', install_postA_11 Σ ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 fc lo v canary pad1 pad2 m ms' -> aevt RT PMc Σ K ms') ->
  aevt RT PMc Σ K (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 0x6aac28) (Z_to_bv 64 0x6aabf8) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x12e548) fc None m (seg_rom bsegs)).
Proof using AF RTC MCI FDO MST.
  intros Σ K ra sp gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo v canary tl idv pad1 junk8 pad2.
  intros STK ROOM WIN TOP ALGN SPHI IDC NXT REFC VRNG VEC SLOT MTX GOTE CAN CNDV PADL MINV ARTIN CONT.
  pose proof (wmono_refl bsegs m) as WM.
  astart (bv_unsigned sp) [(6989672, 6989676); (6990080, 6990092); (6990848, 6990856); (6990912, 6990920); (6991016, 6991024);
          (6993028, 6993032); (6993072, 6993080); (6993096, 6993100); (6993104, 6993112)]%Z.
  assert (SPR : (0 <= bv_unsigned sp < 2^64)%Z) by apply bv_unsigned_in_range.
  pose proof (munch_refl [(bv_unsigned sp - 240, bv_unsigned sp); (6989672, 6989676); (6990080, 6990092); (6990848, 6990856);
          (6991016, 6991024); (6993028, 6993032); (6993072, 6993080); (6993096, 6993100); (6993104, 6993112)]%Z m) as MU.
  apply (aevt_evt RT AF PMc MST).
  carve_frame 80%nat STK.
  do 17 lstep. if_false.
  do 8 lstep.
  pose proof (proj1 (proj1 (rw_cells_app bsegs _ (bv_unsigned sp + -80) [CB 8 _; C8 _; C8 _; C8 _] [C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]) FR))
    as ARGS.
  replace (bv_unsigned sp + -56)%Z with (bv_unsigned sp + -80 + 24)%Z in ARGS by lia.
  replace (bv_unsigned sp + -72)%Z with (bv_unsigned sp + -80 + 8)%Z in ARGS by lia.
  name_sp sp (-80)%Z.
  replace (Z_to_bv 64 (bv_unsigned sp + -64)) with (Z_to_bv 64 (bv_unsigned sp0 + 16)) by (rewrite Hsp; f_equal; lia).
  call call_once_spec_11; unname_sp;
    [exact STK | lia | exact LOLO | lia | exact ARGS | exact IDC | exact NXT | lia | exact MTX | exact GOTE | exact CAN | exact CNDV
    | exact PADL | exact MINV | ].
  clear ARGS PC0 PC4.
  rename PC into STK, PC1 into IDC, PC2 into NXT, PC3 into MTX, POST into CNDV, MI into MINV.
  do 3 lstep.
  amo_step.
  assert (BUMP : amo_val AMO_ADD (Z_to_bv 64 v) (Z_to_bv 64 1) = Z_to_bv 64 (v + 1)) by exact (lit_add_lit v 1).
  rewrite BUMP in REFC. clear BUMP.
  change (sx32 (Z_to_bv 64 12)) with (Z_to_bv 64 12).
  do 7 lstep. if_false.
  do 2 lstep. if_false.
  do 3 lstep.
  acall_sp append_aevt_11; [exact STK | a_ul | exact WIN | a_ul | a_mod16 | exact VEC | exact SLOT | assumption | exact ARTX | ].
  apost_call.
  rename PC into STK, PC0 into VEC, POST into SLOT, MI into MINV.
  do 6 lstep. if_true.
  do 3 lstep.
  do 8 lstep.
  release_frame FR STK (bv_unsigned sp).
  afinish.
Qed.

Definition seg_postA_11 (Σ : rts RT) (sp gp tp s1 s2 s4 s5 s6 s7 s8 s9 s10 s11 : word) (fc : bv 32) (lo : Z) (m : mem)
    : machine_state -> Prop :=
  fun st => exists (t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (F' : bvmap 5 word) (mx : mem),
    st = MS (mkR (Z_to_bv 64 1233676) sp gp tp t0 t1 t2 (Z_to_bv 64 6990888) s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 (Z_to_bv 64 6989808)
                 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F' (Z_to_bv 64 1233676) fc None mx (seg_rom bsegs)
    /\ rt_pres_fp (rt_live RT Σ) (rt_frames RT Σ) (bv_unsigned sp)
         [(6989672, 6989676); (6990080, 6990092); (6990840, 6990888); (6990912, 6990920); (6991016, 6991024);
          (6993028, 6993032); (6993072, 6993080); (6993096, 6993100); (6993104, 6993112)]%Z m mx
    /\ wmono bsegs m mx /\ mem_inv bsegs mx /\ ART RT Σ mx
    /\ stk bsegs mx lo (bv_unsigned sp)
    /\ rw_cells bsegs mx 6990080 [C8 (Z_to_bv 64 (-1)); C4 (Z_to_bv 64 12)]
    /\ rw_cells bsegs mx 6989672 [C4 (Z_to_bv 64 12)]
    /\ rw_cells bsegs mx 6990840 [C8 (Z_to_bv 64 1492832)]
    /\ rw_cells bsegs mx 6990848 [C8 (Z_to_bv 64 1)]
    /\ rw_cells bsegs mx 6990856 [C8 (Z_to_bv 64 188978561070)]
    /\ rw_cells bsegs mx 6990864 [C8 z64]
    /\ rw_cells bsegs mx 6990872 [C8 z64]
    /\ rw_cells bsegs mx 6990880 [C8 z64]
    /\ rw_cells bsegs mx 6990904 [C8 (Z_to_bv 64 6990928); C8 (Z_to_bv 64 6991024); C8 (Z_to_bv 64 6991168)]
    /\ rw_cells bsegs mx 6991016 [C8 (Z_to_bv 64 6990840)]
    /\ rw_cells bsegs mx 6993024 [CB 4 (repeat (Z_to_bv 8 0) 4); C4 z64; C4 z64]
    /\ rw_cells bsegs mx 6993064 [C8 z64; C8 z64; CB 16 (repeat (Z_to_bv 8 0) 16); C4 z64; C4 z64; C8 z64].

Lemma seg_aevt_11 : forall Σ K ra sp gp tp t0 t1 t2 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (lo : Z) (canary : word),
  stk bsegs m lo (bv_unsigned sp) -> (lo + 240 + RT_STACK <= bv_unsigned sp)%Z -> (rt_sp0 RT Σ - STACK_WIN <= lo)%Z ->
  (bv_unsigned sp + 16 <= USTACK_TOP)%Z -> (bv_unsigned sp mod 16 = 0)%Z -> (bv_unsigned sp < 2^62)%Z ->
  rw_cells bsegs m 0x6aa900 [C8 (Z_to_bv 64 0); C4 (Z_to_bv 64 0)] ->
  rw_cells bsegs m 0x6aa768 [C4 (Z_to_bv 64 0xb)] ->
  rw_cells bsegs m 0x6aabf8 [C8 (Z_to_bv 64 0)] ->
  rw_cells bsegs m 0x6aac00 [C8 (Z_to_bv 64 0)] ->
  rw_cells bsegs m 0x6aac08 [C8 (Z_to_bv 64 0)] ->
  rw_cells bsegs m 0x6aac10 [C8 (Z_to_bv 64 0)] ->
  rw_cells bsegs m 0x6aac18 [C8 (Z_to_bv 64 0)] ->
  rw_cells bsegs m 0x6aac20 [C8 (Z_to_bv 64 0)] ->
  rw_cells bsegs m 0x6aac38 [C8 (Z_to_bv 64 0x6aac50); C8 (Z_to_bv 64 0x6aaca8); C8 (Z_to_bv 64 0x6aad40)] ->
  rw_cells bsegs m 0x6aaca8 [CB 8 (repeat (Z_to_bv 8 0) 8)] ->
  rw_cells bsegs m 0x6ab480 [CB 4 (repeat (Z_to_bv 8 0) 4); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0)] ->
  ro_cells bsegs m 0x16f508 [C8 (Z_to_bv 64 0x6cbe28)] -> ro_cells bsegs m 0x6cbe28 [C8 canary] ->
  rw_cells bsegs m 0x6ab4a8 [C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); CB 16 (repeat (Z_to_bv 8 0) 16); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)] ->
  mem_inv bsegs m -> ART RT Σ m ->
  (forall ms', seg_postA_11 Σ sp gp tp s1 s2 s4 s5 s6 s7 s8 s9 s10 s11 fc lo m ms' -> aevt RT PMc Σ K ms') ->
  aevt RT PMc Σ K (MS (mkR ra sp gp tp t0 t1 t2 (Z_to_bv 64 0x6aac28) s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 (Z_to_bv 64 0x6aa7f0) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x12d2d4) fc None m (seg_rom bsegs)).
Proof using AF RTC MCI FDO MST.
  intros Σ K ra sp gp tp t0 t1 t2 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo canary.
  intros STK ROOM WIN TOP ALGN SPHI IDC NXT VPTR REFC PUNCT GRP0 GRP1 GRP2 VEC SLOT MTX GOTE CAN CNDV MINV ARTIN CONT.
  pose proof (wmono_refl bsegs m) as WM.
  astart (bv_unsigned sp) [(6989672, 6989676); (6990080, 6990092); (6990840, 6990888); (6990912, 6990920); (6991016, 6991024);
          (6993028, 6993032); (6993072, 6993080); (6993096, 6993100); (6993104, 6993112)]%Z.
  pose proof (munch_refl [(lo, bv_unsigned sp); (6990840, 6990888)]%Z m) as MU.
  apply (aevt_evt RT AF PMc MST).
  do 14 lstep.
  acall install_aevt_11;
    [exact STK | a_ul | exact WIN | exact TOP | exact ALGN | exact SPHI | exact IDC | exact NXT | exact REFC | lia | exact VEC | exact SLOT
    | exact MTX | exact GOTE | exact CAN | exact CNDV | apply repeat_length | assumption | exact ARTX | ].
  apost_call.
  afinish.
Qed.

End AevtPieces.
