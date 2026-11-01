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

Definition call_once_post_10 (ra sp gp tp t0 t1 t2 s0 s1 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (lo k : Z) (canary : word) (pad1 j8 : list byte) (pad2 : word) (m : mem)
    : machine_state -> Prop :=
  fun ms' => exists (a1 a2 a3 a4 a5 : word) (m' : mem),
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 z64 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom bsegs)
    /\ munch [(6989672, 6989676); (6990064, 6990076); (6993028, 6993032); (6993072, 6993080); (6993096, 6993100);
              (6993104, 6993112); (bv_unsigned sp - 160, bv_unsigned sp)]%Z m m'
    /\ wmono bsegs m m'
    /\ mem_inv bsegs m'
    /\ stk bsegs m' lo (bv_unsigned sp)
    /\ rw_cells bsegs m' (bv_unsigned sp)
         [CB 8 j8; C8 (Z_to_bv 64 6990064); C8 (Z_to_bv 64 (bv_unsigned sp + 24)); C8 (Z_to_bv 64 (bv_unsigned sp + 8))]
    /\ rw_cells bsegs m' 6990064 [C8 (Z_to_bv 64 18446744073709551615); C4 (Z_to_bv 64 (k + 1))]
    /\ rw_cells bsegs m' 6989672 [C4 (Z_to_bv 64 (k + 1))]
    /\ rw_cells bsegs m' 6993024 [CB 4 (repeat (Z_to_bv 8 0) 4); C4 z64; C4 z64]
    /\ ro_cells bsegs m' 7126568 [C8 canary]
    /\ rw_cells bsegs m' 6993064 [C8 z64; C8 z64; CB 16 pad1; C4 z64; C4 pad2; C8 z64].

Lemma call_once_spec_10 : forall ra sp gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (lo k : Z) (canary tl idv : word) (pad1 j8 : list byte) (pad2 : word),
  stk bsegs m lo (bv_unsigned sp) -> (lo <= bv_unsigned sp - 160)%Z -> (0x6ce000 <= lo)%Z -> (bv_unsigned sp + 32 < 2^63)%Z ->
  rw_cells bsegs m (bv_unsigned sp) [CB 8 j8; C8 (Z_to_bv 64 0x6aa8f0); C8 (Z_to_bv 64 (bv_unsigned sp + 24)); C8 (Z_to_bv 64 (bv_unsigned sp + 8))] ->
  rw_cells bsegs m 0x6aa8f0 [C8 (Z_to_bv 64 0); C4 idv] ->
  rw_cells bsegs m 0x6aa768 [C4 (Z_to_bv 64 k)] -> (0 <= k < 30)%Z ->
  rw_cells bsegs m 0x6ab480 [CB 4 (repeat (Z_to_bv 8 0) 4); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0)] ->
  ro_cells bsegs m 0x16f508 [C8 (Z_to_bv 64 0x6cbe28)] -> ro_cells bsegs m 0x6cbe28 [C8 canary] ->
  rw_cells bsegs m 0x6ab4a8 [C8 (Z_to_bv 64 0); C8 tl; CB 16 pad1; C4 (Z_to_bv 64 0); C4 pad2; C8 (Z_to_bv 64 0)] ->
  length pad1 = 16%nat -> mem_inv bsegs m ->
  evt bsegs (call_once_post_10 ra sp gp tp t0 t1 t2 s0 s1 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc lo k canary pad1 j8 pad2 m)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 0x6aa8f0) (Z_to_bv 64 (bv_unsigned sp + 16)) (Z_to_bv 64 0x14637c) a3 a4 a5 a6 a7
               s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x147b40) fc None m (seg_rom bsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo k canary tl idv pad1 j8 pad2
    Stk Room Floor SpHi Slots IdC Ctr Kr Mtx Got Can Cv PadL Inv.
  pose proof (bv_unsigned_in_range 64 sp) as SpR. unfold bv_modulus in SpR. cbn in SpR.
  pose proof (munch_refl [(6989672, 6989676); (6990064, 6990076); (6993028, 6993032); (6993072, 6993080); (6993096, 6993100);
                          (6993104, 6993112); (bv_unsigned sp - 160, bv_unsigned sp)]%Z m) as Fp.
  pose proof (wmono_refl bsegs m) as Grow.
  carve_frame 64%nat Stk.
  do 15 lstep.
  call_sp mutex_lock_spec; [exact Mtx | exact Inv |].
  steps_to 1458824%Z.
  call_sp mutex_unlock_spec; [exact Stk | lia | lia | exact POST | exact MI |].
  steps_to 1336212%Z.
  amo_step. amo32_fix_lit.
  assert (Sx : sx32 (Z_to_bv 64 k) = Z_to_bv 64 k).
  { unfold sx32. rewrite unsigned_lit by lia. rewrite swrap32_small by lia. reflexivity. }
  rewrite Sx; clear Sx.
  steps_to 1457564%Z.
  call_sp mutex_lock_spec; [exact POST0 | exact MI0 |].
  steps_to 1458824%Z.
  call_sp mutex_unlock_spec; [exact PC | lia | lia | exact POST | exact MI |].
  steps_to 1450036%Z.
  call_sp cond_broadcast_spec; [exact PC | lia | lia | exact Got | exact Can | exact Cv | exact PadL | exact MI0 |].
  do 9 lstep.
  release_frame FR PC (bv_unsigned sp).
  unfold call_once_post_10. sys_finish.
Qed.

Section AevtPieces.
Variable RT : rt_sig.
Hypothesis AF : art_facts RT.
Hypothesis RTC : rt_contracts RT.
Hypothesis MCI : memcmp_inner_icontract RT.
Variable PMc : Model -> Prop.
Hypothesis FDO : fdfs_only PMc.
Hypothesis MST : mat_stable PMc.

Definition append_postA_10 (Σ : rts RT) (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (fc : bv 32) (lo : Z)
    (m : mem) : machine_state -> Prop :=
  fun ms' => exists (t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (F' : bvmap 5 word) (m' : mem),
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F' (ret_pc ra) fc None m' (seg_rom bsegs)
    /\ rt_pres_fp (rt_live RT Σ) (rt_frames RT Σ) (bv_unsigned sp) [(6990912, 6990920); (6991008, 6991016)]%Z m m'
    /\ wmono bsegs m m'
    /\ mem_inv bsegs m'
    /\ ART RT Σ m'
    /\ stk bsegs m' lo (bv_unsigned sp)
    /\ rw_cells bsegs m' 6990904 [C8 (Z_to_bv 64 6990928); C8 (Z_to_bv 64 6991016); C8 (Z_to_bv 64 6991168)]
    /\ rw_cells bsegs m' 6991008 [CB 8 (repeat (Z_to_bv 8 0) 8)].

Lemma append_aevt_10 : forall Σ K ra sp gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (lo : Z) (junk8 : list byte),
  stk bsegs m lo (bv_unsigned sp) -> (lo + 80 + RT_STACK <= bv_unsigned sp)%Z -> (rt_sp0 RT Σ - STACK_WIN <= lo)%Z ->
  (bv_unsigned sp + 16 <= USTACK_TOP)%Z -> (bv_unsigned sp mod 16 = 0)%Z ->
  rw_cells bsegs m 0x6aac38 [C8 (Z_to_bv 64 0x6aac50); C8 (Z_to_bv 64 0x6aaca0); C8 (Z_to_bv 64 0x6aad40)] ->
  rw_cells bsegs m 0x6aaca0 [CB 8 junk8] -> mem_inv bsegs m -> ART RT Σ m ->
  (forall ms', append_postA_10 Σ ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 fc lo m ms' -> aevt RT PMc Σ K ms') ->
  aevt RT PMc Σ K (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 0x6aac38) (Z_to_bv 64 1) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x14502c) fc None m (seg_rom bsegs)).
Proof using AF RTC MCI FDO MST.
  intros Σ K ra sp gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo junk8
    Stk Room Floor Top Align Vec Tail Inv Art0 Cont.
  pose proof (bv_unsigned_in_range 64 sp) as SpR. unfold bv_modulus in SpR. cbn in SpR.
  pose proof (wmono_refl bsegs m) as Grow.
  astart (bv_unsigned sp) [(6990912, 6990920); (6991008, 6991016)]%Z.
  pose proof (munch_refl [(bv_unsigned sp - 80, bv_unsigned sp); (6990912, 6990920)]%Z m) as Fp.
  apply (aevt_evt RT AF PMc MST).
  carve_frame 80%nat Stk.
  steps_to 519824%Z.
  acallc (memsetA_spec RT RTC PMc FDO MST) clearing (clear Tail)
    by (first [ eassumption | a_call_ok | a_chk | a_cl | a_ul ]).
  change (Z.to_nat 8) with 8%nat in POST. change (0 mod 256)%Z with 0%Z in POST.
  do 15 lstep.
  release_frame FR PC (bv_unsigned sp).
  afinish.
Qed.

Definition install_postA_10 (Σ : rts RT) (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (fc : bv 32)
    (lo v : Z) (canary : word) (pad1 : list byte) (pad2 : word) (m : mem) : machine_state -> Prop :=
  fun ms' => exists (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (F' : bvmap 5 word) (m' : mem),
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 6991008) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
                  t3 t4 t5 t6)
             F' (ret_pc ra) fc None m' (seg_rom bsegs)
    /\ rt_pres_fp (rt_live RT Σ) (rt_frames RT Σ) (bv_unsigned sp)
         [(6989672, 6989676); (6990064, 6990076); (6990800, 6990808); (6990912, 6990920); (6991008, 6991016);
          (6993028, 6993032); (6993072, 6993080); (6993096, 6993100); (6993104, 6993112)]%Z m m'
    /\ wmono bsegs m m'
    /\ mem_inv bsegs m'
    /\ ART RT Σ m'
    /\ stk bsegs m' lo (bv_unsigned sp)
    /\ rw_cells bsegs m' 6990064 [C8 (Z_to_bv 64 18446744073709551615); C4 (Z_to_bv 64 11)]
    /\ rw_cells bsegs m' 6989672 [C4 (Z_to_bv 64 11)]
    /\ rw_cells bsegs m' 6990800 [C8 (Z_to_bv 64 (v + 1))]
    /\ rw_cells bsegs m' 6990904 [C8 (Z_to_bv 64 6990928); C8 (Z_to_bv 64 6991016); C8 (Z_to_bv 64 6991168)]
    /\ rw_cells bsegs m' 6991008 [C8 (Z_to_bv 64 6990792)]
    /\ rw_cells bsegs m' 6993024 [CB 4 (repeat (Z_to_bv 8 0) 4); C4 z64; C4 z64]
    /\ ro_cells bsegs m' 7126568 [C8 canary]
    /\ rw_cells bsegs m' 6993064 [C8 z64; C8 z64; CB 16 pad1; C4 z64; C4 pad2; C8 z64].

Lemma install_aevt_10 : forall Σ K ra sp gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (lo v : Z) (canary tl idv : word) (pad1 junk8 : list byte) (pad2 : word),
  stk bsegs m lo (bv_unsigned sp) -> (lo + 240 + RT_STACK <= bv_unsigned sp)%Z -> (rt_sp0 RT Σ - STACK_WIN <= lo)%Z ->
  (bv_unsigned sp + 16 <= USTACK_TOP)%Z -> (bv_unsigned sp mod 16 = 0)%Z -> (bv_unsigned sp < 2^62)%Z ->
  rw_cells bsegs m 0x6aa8f0 [C8 (Z_to_bv 64 0); C4 idv] ->
  rw_cells bsegs m 0x6aa768 [C4 (Z_to_bv 64 10)] ->
  rw_cells bsegs m 0x6aabd0 [C8 (Z_to_bv 64 v)] -> (0 <= v < 2^62)%Z ->
  rw_cells bsegs m 0x6aac38 [C8 (Z_to_bv 64 0x6aac50); C8 (Z_to_bv 64 0x6aaca0); C8 (Z_to_bv 64 0x6aad40)] ->
  rw_cells bsegs m 0x6aaca0 [CB 8 junk8] ->
  rw_cells bsegs m 0x6ab480 [CB 4 (repeat (Z_to_bv 8 0) 4); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0)] ->
  ro_cells bsegs m 0x16f508 [C8 (Z_to_bv 64 0x6cbe28)] -> ro_cells bsegs m 0x6cbe28 [C8 canary] ->
  rw_cells bsegs m 0x6ab4a8 [C8 (Z_to_bv 64 0); C8 tl; CB 16 pad1; C4 (Z_to_bv 64 0); C4 pad2; C8 (Z_to_bv 64 0)] ->
  length pad1 = 16%nat -> mem_inv bsegs m -> ART RT Σ m ->
  (forall ms', install_postA_10 Σ ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 fc lo v canary pad1 pad2 m ms' -> aevt RT PMc Σ K ms') ->
  aevt RT PMc Σ K (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 0x6aac28) (Z_to_bv 64 0x6aabc8) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x12e408) fc None m (seg_rom bsegs)).
Proof using AF RTC MCI FDO MST.
  intros Σ K ra sp gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo v canary tl idv
    pad1 junk8 pad2 Stk Room Floor Top Align SpHi IdC Ctr Cnt Vr Vec Tail Mtx Got Can Cv PadL Inv Art0 Cont.
  pose proof (bv_unsigned_in_range 64 sp) as SpR. unfold bv_modulus in SpR. cbn in SpR.
  pose proof (wmono_refl bsegs m) as Grow.
  astart (bv_unsigned sp)
    [(6989672, 6989676); (6990064, 6990076); (6990800, 6990808); (6990912, 6990920); (6991008, 6991016);
     (6993028, 6993032); (6993072, 6993080); (6993096, 6993100); (6993104, 6993112)]%Z.
  pose proof (munch_refl [(lo, bv_unsigned sp); (6989672, 6989676); (6990064, 6990076); (6990800, 6990808);
                          (6991008, 6991016); (6993028, 6993032); (6993072, 6993080); (6993096, 6993100);
                          (6993104, 6993112)]%Z m) as Fp.
  apply (aevt_evt RT AF PMc MST).
  carve_frame 80%nat Stk.
  steps_to 1342272%Z.
  pose proof FR as Slots.
  apply (rw_cells_app bsegs _ _ [_; _; _; _] _) in Slots. destruct Slots as [Slots _].
  name_sp sp (-80)%Z.
  replace (Z_to_bv 64 (bv_unsigned sp + -64)) with (Z_to_bv 64 (bv_unsigned sp0 + 16))
    by (rewrite Hsp; f_equal; lia).
  eapply evt_cut.
  { eapply call_once_spec_10; rewrite ?Hsp.
    - exact Stk.
    - lia.
    - lia.
    - lia.
    - replace (bv_unsigned sp + -80 + 24)%Z with (bv_unsigned sp + -56)%Z by lia.
      replace (bv_unsigned sp + -80 + 8)%Z with (bv_unsigned sp + -72)%Z by lia.
      exact Slots.
    - exact IdC.
    - exact Ctr.
    - lia.
    - exact Mtx.
    - exact Got.
    - exact Can.
    - exact Cv.
    - exact PadL.
    - exact Inv. }
  post_call bsegs m0.
  unname_sp.
  clear Slots PC0 Can.
  change (10 + 1)%Z with 11%Z in PC1, PC2.
  do 3 lstep.
  amo_step.
  cbn [amo_val] in Cnt. rewrite lit_add_lit in Cnt.
  replace (sx32 (Z_to_bv 64 11)) with (Z_to_bv 64 11) by (vm_compute; reflexivity).
  steps_to 1331244%Z.
  acallc append_aevt_10 clearing (clear Tail Vec)
    by (try a_unz; first [ eassumption | a_mod16 | a_ul ]).
  steps_to 1238296%Z.
  lstep.
  release_frame FR PC (bv_unsigned sp).
  afinish.
Qed.

Definition seg_postA_10 (Σ : rts RT) (sp gp tp s1 s2 s4 s5 s6 s7 s8 s9 s10 s11 : word) (fc : bv 32) (lo : Z) (m : mem)
    : machine_state -> Prop :=
  fun ms' => exists (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (F' : bvmap 5 word) (m' : mem),
    ms' = MS (mkR (Z_to_bv 64 1233620) sp gp tp t0 t1 t2 (Z_to_bv 64 6990888) s1 (Z_to_bv 64 6991008) a1 a2 a3 a4 a5 a6 a7
                  s2 (Z_to_bv 64 6989808) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F' (Z_to_bv 64 1233620) fc None m' (seg_rom bsegs)
    /\ rt_pres_fp (rt_live RT Σ) (rt_frames RT Σ) (bv_unsigned sp)
         [(6989672, 6989676); (6990064, 6990076); (6990792, 6990810); (6990816, 6990840); (6990912, 6990920);
          (6991008, 6991016); (6993028, 6993032); (6993072, 6993080); (6993096, 6993100); (6993104, 6993112)]%Z m m'
    /\ wmono bsegs m m'
    /\ mem_inv bsegs m'
    /\ ART RT Σ m'
    /\ stk bsegs m' lo (bv_unsigned sp)
    /\ rw_cells bsegs m' 6990064 [C8 (Z_to_bv 64 18446744073709551615); C4 (Z_to_bv 64 11)]
    /\ rw_cells bsegs m' 6989672 [C4 (Z_to_bv 64 11)]
    /\ rw_cells bsegs m' 6990792 [C8 (Z_to_bv 64 1492752)]
    /\ rw_cells bsegs m' 6990800 [C8 (Z_to_bv 64 1)]
    /\ rw_cells bsegs m' 6990808 [C2 (Z_to_bv 64 11310)]
    /\ rw_cells bsegs m' 6990816 [C8 z64]
    /\ rw_cells bsegs m' 6990824 [C8 z64]
    /\ rw_cells bsegs m' 6990832 [C8 z64]
    /\ rw_cells bsegs m' 6990904 [C8 (Z_to_bv 64 6990928); C8 (Z_to_bv 64 6991016); C8 (Z_to_bv 64 6991168)]
    /\ rw_cells bsegs m' 6991008 [C8 (Z_to_bv 64 6990792)]
    /\ rw_cells bsegs m' 6993024 [CB 4 (repeat (Z_to_bv 8 0) 4); C4 z64; C4 z64]
    /\ rw_cells bsegs m' 6993064 [C8 z64; C8 z64; CB 16 (repeat (Z_to_bv 8 0) 16); C4 z64; C4 z64; C8 z64].

Lemma seg_aevt_10 : forall Σ K ra sp gp tp t0 t1 t2 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (lo : Z) (canary : word),
  stk bsegs m lo (bv_unsigned sp) -> (lo + 240 + RT_STACK <= bv_unsigned sp)%Z -> (rt_sp0 RT Σ - STACK_WIN <= lo)%Z ->
  (bv_unsigned sp + 16 <= USTACK_TOP)%Z -> (bv_unsigned sp mod 16 = 0)%Z -> (bv_unsigned sp < 2^62)%Z ->
  rw_cells bsegs m 0x6aa8f0 [C8 (Z_to_bv 64 0); C4 (Z_to_bv 64 0)] ->
  rw_cells bsegs m 0x6aa768 [C4 (Z_to_bv 64 0xa)] ->
  rw_cells bsegs m 0x6aabc8 [C8 (Z_to_bv 64 0)] ->
  rw_cells bsegs m 0x6aabd0 [C8 (Z_to_bv 64 0)] ->
  rw_cells bsegs m 0x6aabd8 [C2 (Z_to_bv 64 0)] ->
  rw_cells bsegs m 0x6aabe0 [C8 (Z_to_bv 64 0)] ->
  rw_cells bsegs m 0x6aabe8 [C8 (Z_to_bv 64 0)] ->
  rw_cells bsegs m 0x6aabf0 [C8 (Z_to_bv 64 0)] ->
  rw_cells bsegs m 0x6aac38 [C8 (Z_to_bv 64 0x6aac50); C8 (Z_to_bv 64 0x6aaca0); C8 (Z_to_bv 64 0x6aad40)] ->
  rw_cells bsegs m 0x6aaca0 [CB 8 (repeat (Z_to_bv 8 0) 8)] ->
  rw_cells bsegs m 0x6ab480 [CB 4 (repeat (Z_to_bv 8 0) 4); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0)] ->
  ro_cells bsegs m 0x16f508 [C8 (Z_to_bv 64 0x6cbe28)] -> ro_cells bsegs m 0x6cbe28 [C8 canary] ->
  rw_cells bsegs m 0x6ab4a8 [C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); CB 16 (repeat (Z_to_bv 8 0) 16); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)] ->
  mem_inv bsegs m -> ART RT Σ m ->
  (forall ms', seg_postA_10 Σ sp gp tp s1 s2 s4 s5 s6 s7 s8 s9 s10 s11 fc lo m ms' -> aevt RT PMc Σ K ms') ->
  aevt RT PMc Σ K (MS (mkR ra sp gp tp t0 t1 t2 (Z_to_bv 64 0x6aac28) s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 (Z_to_bv 64 0x6aa7f0) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x12d2a0) fc None m (seg_rom bsegs)).
Proof using AF RTC MCI FDO MST.
  intros Σ K ra sp gp tp t0 t1 t2 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo canary
    Stk Room Floor Top Align SpHi IdC Ctr Vt Cnt Tag Z1 Z2 Z3 Vec Tail Mtx Got Can Cv Inv Art0 Cont.
  pose proof (wmono_refl bsegs m) as Grow.
  astart (bv_unsigned sp)
    [(6989672, 6989676); (6990064, 6990076); (6990792, 6990810); (6990816, 6990840); (6990912, 6990920);
     (6991008, 6991016); (6993028, 6993032); (6993072, 6993080); (6993096, 6993100); (6993104, 6993112)]%Z.
  pose proof (munch_refl [(lo, bv_unsigned sp); (6990792, 6990810); (6990816, 6990840)]%Z m) as Fp.
  apply (aevt_evt RT AF PMc MST).
  steps_to 1238024%Z.
  acallc install_aevt_10 clearing (clear IdC Ctr Cnt Vec Tail Mtx Can Cv)
    by (first [ eassumption | reflexivity | a_ul ]).
  afinish.
Qed.

End AevtPieces.
