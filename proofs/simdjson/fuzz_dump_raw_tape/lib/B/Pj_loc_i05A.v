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
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump_raw_tape.lib.B Require Import Layout RT_iface RT_iface2 D_defs D_kit D_clx D_rlkit D_libiface Sj_rtf Sj_akit Sj_acps Sj_hkit Sj_new Sj_num_akit Sj_num_amem Pj_mciA Pj_loc_akitA Pj_onceA Pj_loc_newlocA.
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

Definition call_once_post_5 (ra sp gp tp t0 t1 t2 s0 s1 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (lo k : Z) (canary : word) (pad1 j8 : list byte) (pad2 : word) (m : mem)
    : machine_state -> Prop :=
  fun st => exists (r0 r1 r2 r3 r4 r5 : word) (mf : mem),
    st = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 r0 r1 r2 r3 r4 r5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (ret_pc ra) fc None mf (seg_rom bsegs)
    /\ munch [((bv_unsigned sp - 160)%Z, bv_unsigned sp); (6989672%Z, 6989676%Z); (6989696%Z, 6989708%Z);
              (6993028%Z, 6993032%Z); (6993072%Z, 6993080%Z); (6993096%Z, 6993100%Z); (6993104%Z, 6993112%Z)] m mf
    /\ wmono bsegs m mf
    /\ mem_inv bsegs mf
    /\ stk bsegs mf lo (bv_unsigned sp)
    /\ rw_cells bsegs mf (bv_unsigned sp)
         [CB 8 j8; C8 (Z_to_bv 64 6989696); C8 (Z_to_bv 64 (bv_unsigned sp + 24)); C8 (Z_to_bv 64 (bv_unsigned sp + 8))]
    /\ rw_cells bsegs mf 6989696 [C8 (Z_to_bv 64 18446744073709551615); C4 (Z_to_bv 64 (k + 1))]
    /\ rw_cells bsegs mf 6989672 [C4 (Z_to_bv 64 (k + 1))]
    /\ rw_cells bsegs mf 6993024 [CB 4 (repeat (Z_to_bv 8 0) 4); C4 z64; C4 z64]
    /\ ro_cells bsegs mf 7126568 [C8 canary]
    /\ rw_cells bsegs mf 6993064 [C8 z64; C8 z64; CB 16 pad1; C4 z64; C4 pad2; C8 z64].

Lemma call_once_spec_5 : forall ra sp gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (lo k : Z) (canary tl idv : word) (pad1 j8 : list byte) (pad2 : word),
  stk bsegs m lo (bv_unsigned sp) -> (lo <= bv_unsigned sp - 160)%Z -> (0x6ce000 <= lo)%Z -> (bv_unsigned sp + 32 < 2^63)%Z ->
  rw_cells bsegs m (bv_unsigned sp) [CB 8 j8; C8 (Z_to_bv 64 0x6aa780); C8 (Z_to_bv 64 (bv_unsigned sp + 24)); C8 (Z_to_bv 64 (bv_unsigned sp + 8))] ->
  rw_cells bsegs m 0x6aa780 [C8 (Z_to_bv 64 0); C4 idv] ->
  rw_cells bsegs m 0x6aa768 [C4 (Z_to_bv 64 k)] -> (0 <= k < 30)%Z ->
  rw_cells bsegs m 0x6ab480 [CB 4 (repeat (Z_to_bv 8 0) 4); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0)] ->
  ro_cells bsegs m 0x16f508 [C8 (Z_to_bv 64 0x6cbe28)] -> ro_cells bsegs m 0x6cbe28 [C8 canary] ->
  rw_cells bsegs m 0x6ab4a8 [C8 (Z_to_bv 64 0); C8 tl; CB 16 pad1; C4 (Z_to_bv 64 0); C4 pad2; C8 (Z_to_bv 64 0)] ->
  length pad1 = 16%nat -> mem_inv bsegs m ->
  evt bsegs (call_once_post_5 ra sp gp tp t0 t1 t2 s0 s1 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc lo k canary pad1 j8 pad2 m)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 0x6aa780) (Z_to_bv 64 (bv_unsigned sp + 16)) (Z_to_bv 64 0x14637c) a3 a4 a5 a6 a7
               s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x147b40) fc None m (seg_rom bsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo k canary tl idv pad1 j8 pad2
    STACK ROOM FLOOR SPHI ARGS IDCELL CTR KRANGE MUTEX GOTC CANC CONDV PADLEN MEMOK.
  pose proof (munch_refl [((bv_unsigned sp - 160)%Z, bv_unsigned sp); (6989672%Z, 6989676%Z); (6989696%Z, 6989708%Z);
              (6993028%Z, 6993032%Z); (6993072%Z, 6993080%Z); (6993096%Z, 6993100%Z); (6993104%Z, 6993112%Z)] m) as FOOT.
  pose proof (wmono_refl bsegs m) as GROW.
  carve_frame 64%nat STACK.
  steps_to 1457564%Z.
  call mutex_lock_spec; [exact MUTEX | exact MEMOK |].
  steps_to 1458824%Z.
  call_sp mutex_unlock_spec; [exact STACK | lia | lia | assumption | assumption |].
  steps_to 1336212%Z.
  amo_step.
  amo32_fix_lit.
  assert (SXK : sx32 (Z_to_bv 64 k) = Z_to_bv 64 k)
    by (unfold sx32; rewrite unsigned_lit by lia; rewrite swrap32_small by lia; reflexivity).
  rewrite SXK.
  steps_to 1457564%Z.
  call mutex_lock_spec; [assumption | assumption |].
  steps_to 1458824%Z.
  call_sp mutex_unlock_spec; [eassumption | lia | lia | assumption | assumption |].
  steps_to 1450036%Z.
  call_sp cond_broadcast_spec; [eassumption | lia | lia | eassumption | eassumption | eassumption | eassumption | assumption |].
  steps_to 1342528%Z.
  lstep.
  lazymatch goal with S : stk bsegs _ lo _ |- _ => release_frame FR S (bv_unsigned sp) end.
  finish.
Qed.

Section AevtPieces.
Variable RT : rt_sig.
Hypothesis AF : art_facts RT.
Hypothesis RTC : rt_contracts RT.
Hypothesis MCI : memcmp_inner_icontract RT.
Variable PMc : Model -> Prop.
Hypothesis FDO : fdfs_only PMc.
Hypothesis MST : mat_stable PMc.

Definition append_postA_5 (Σ : rts RT) (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (fc : bv 32) (lo : Z) (m : mem)
    : machine_state -> Prop :=
  fun st => exists (u0 u1 u2 r0 r1 r2 r3 r4 r5 r6 r7 u3 u4 u5 u6 : word) (G : bvmap 5 word) (mf : mem),
    st = MS (mkR ra sp gp tp u0 u1 u2 s0 s1 r0 r1 r2 r3 r4 r5 r6 r7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 u3 u4 u5 u6)
            G (ret_pc ra) fc None mf (seg_rom bsegs)
    /\ rt_pres_fp (rt_live RT Σ) (rt_frames RT Σ) (bv_unsigned sp) [(6990912%Z, 6990920%Z); (6990968%Z, 6990976%Z)] m mf
    /\ wmono bsegs m mf
    /\ mem_inv bsegs mf
    /\ ART RT Σ mf
    /\ stk bsegs mf lo (bv_unsigned sp)
    /\ rw_cells bsegs mf 6990904 [C8 (Z_to_bv 64 6990928); C8 (Z_to_bv 64 6990976); C8 (Z_to_bv 64 6991168)]
    /\ rw_cells bsegs mf 6990968 [C8 z64].

Lemma append_aevt_5 : forall Σ K ra sp gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (lo : Z) (junk8 : list byte),
  stk bsegs m lo (bv_unsigned sp) -> (lo + 80 + RT_STACK <= bv_unsigned sp)%Z -> (rt_sp0 RT Σ - STACK_WIN <= lo)%Z ->
  (bv_unsigned sp + 16 <= USTACK_TOP)%Z -> (bv_unsigned sp mod 16 = 0)%Z ->
  rw_cells bsegs m 0x6aac38 [C8 (Z_to_bv 64 0x6aac50); C8 (Z_to_bv 64 0x6aac78); C8 (Z_to_bv 64 0x6aad40)] ->
  rw_cells bsegs m 0x6aac78 [CB 8 junk8] -> mem_inv bsegs m -> ART RT Σ m ->
  (forall ms', append_postA_5 Σ ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 fc lo m ms' -> aevt RT PMc Σ K ms') ->
  aevt RT PMc Σ K (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 0x6aac38) (Z_to_bv 64 1) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x14502c) fc None m (seg_rom bsegs)).
Proof using AF RTC MCI FDO MST.
  intros Σ K ra sp gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo junk8
    STK ROOM WIN TOP ALIGN VEC SLOT MEMOK ART0 KONT.
  pose proof (wmono_refl bsegs m) as GROW.
  astart (bv_unsigned sp) [(6990912%Z, 6990920%Z); (6990968%Z, 6990976%Z)].
  pose proof (munch_refl [((bv_unsigned sp - 80)%Z, bv_unsigned sp); (6990912%Z, 6990920%Z)] m) as MU.
  apply (aevt_evt RT AF PMc MST).
  carve_frame 80%nat STK.
  steps_to 519824%Z.
  acallc (memsetA_spec RT RTC PMc FDO MST) clearing idtac by (first [ eassumption | a_ul | a_chk | a_cl | a_call_ok ]).
  lazymatch goal with
  | ZERO8 : rw_cells bsegs _ 6990968 [CB _ _] |- _ =>
      change (Z.to_nat 8) with 8%nat in ZERO8;
      apply (Sj_num_kit.num_cb8_c8 bsegs _ 6990968 [] []) in ZERO8; cbn [app] in ZERO8;
      replace (le_bytes_to_word (repeat (Z_to_bv 8 (0 mod 256)) 8)) with z64 in ZERO8
        by (apply bv_eq; vm_compute; reflexivity)
  end.
  steps_to 1331692%Z.
  lstep.
  lazymatch goal with S : stk bsegs _ lo _ |- _ => release_frame FR S (bv_unsigned sp) end.
  afinish.
Qed.

Definition install_postA_5 (Σ : rts RT) (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (fc : bv 32)
    (lo v : Z) (canary : word) (pad1 : list byte) (pad2 : word) (m : mem) : machine_state -> Prop :=
  fun st => exists (u0 u1 u2 r0 r1 r2 r3 r4 r5 r6 r7 u3 u4 u5 u6 : word) (G : bvmap 5 word) (mf : mem),
    st = MS (mkR ra sp gp tp u0 u1 u2 s0 s1 r0 r1 r2 r3 r4 r5 r6 r7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 u3 u4 u5 u6)
            G (ret_pc ra) fc None mf (seg_rom bsegs)
    /\ rt_pres_fp (rt_live RT Σ) (rt_frames RT Σ) (bv_unsigned sp)
         [(6989672%Z, 6989676%Z); (6989696%Z, 6989708%Z); (6990552%Z, 6990560%Z); (6990912%Z, 6990920%Z);
          (6990968%Z, 6990976%Z); (6993028%Z, 6993032%Z); (6993072%Z, 6993080%Z); (6993096%Z, 6993100%Z);
          (6993104%Z, 6993112%Z)] m mf
    /\ wmono bsegs m mf
    /\ mem_inv bsegs mf
    /\ ART RT Σ mf
    /\ stk bsegs mf lo (bv_unsigned sp)
    /\ rw_cells bsegs mf 6989696 [C8 (Z_to_bv 64 18446744073709551615); C4 (Z_to_bv 64 6)]
    /\ rw_cells bsegs mf 6989672 [C4 (Z_to_bv 64 6)]
    /\ rw_cells bsegs mf 6990552 [C8 (Z_to_bv 64 (v + 1))]
    /\ rw_cells bsegs mf 6990904 [C8 (Z_to_bv 64 6990928); C8 (Z_to_bv 64 6990976); C8 (Z_to_bv 64 6991168)]
    /\ rw_cells bsegs mf 6990968 [C8 (Z_to_bv 64 6990544)]
    /\ rw_cells bsegs mf 6993024 [CB 4 (repeat (Z_to_bv 8 0) 4); C4 z64; C4 z64]
    /\ ro_cells bsegs mf 7126568 [C8 canary]
    /\ rw_cells bsegs mf 6993064 [C8 z64; C8 z64; CB 16 pad1; C4 z64; C4 pad2; C8 z64].

Lemma install_aevt_5 : forall Σ K ra sp gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (lo v : Z) (canary tl idv : word) (pad1 junk8 : list byte) (pad2 : word),
  stk bsegs m lo (bv_unsigned sp) -> (lo + 240 + RT_STACK <= bv_unsigned sp)%Z -> (rt_sp0 RT Σ - STACK_WIN <= lo)%Z ->
  (bv_unsigned sp + 16 <= USTACK_TOP)%Z -> (bv_unsigned sp mod 16 = 0)%Z -> (bv_unsigned sp < 2^62)%Z ->
  rw_cells bsegs m 0x6aa780 [C8 (Z_to_bv 64 0); C4 idv] ->
  rw_cells bsegs m 0x6aa768 [C4 (Z_to_bv 64 5)] ->
  rw_cells bsegs m 0x6aaad8 [C8 (Z_to_bv 64 v)] -> (0 <= v < 2^62)%Z ->
  rw_cells bsegs m 0x6aac38 [C8 (Z_to_bv 64 0x6aac50); C8 (Z_to_bv 64 0x6aac78); C8 (Z_to_bv 64 0x6aad40)] ->
  rw_cells bsegs m 0x6aac78 [CB 8 junk8] ->
  rw_cells bsegs m 0x6ab480 [CB 4 (repeat (Z_to_bv 8 0) 4); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0)] ->
  ro_cells bsegs m 0x16f508 [C8 (Z_to_bv 64 0x6cbe28)] -> ro_cells bsegs m 0x6cbe28 [C8 canary] ->
  rw_cells bsegs m 0x6ab4a8 [C8 (Z_to_bv 64 0); C8 tl; CB 16 pad1; C4 (Z_to_bv 64 0); C4 pad2; C8 (Z_to_bv 64 0)] ->
  length pad1 = 16%nat -> mem_inv bsegs m -> ART RT Σ m ->
  (forall ms', install_postA_5 Σ ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 fc lo v canary pad1 pad2 m ms' -> aevt RT PMc Σ K ms') ->
  aevt RT PMc Σ K (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 0x6aac28) (Z_to_bv 64 0x6aaad0) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x12ddb4) fc None m (seg_rom bsegs)).
Proof using AF RTC MCI FDO MST.
  intros Σ K ra sp gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo v
    canary tl idv pad1 junk8 pad2
    STK ROOM WIN TOP ALIGN SMALL IDC CTR REFC VRANGE VEC SLOT MUTEX GOTC CANC CONDV PADLEN MEMOK ART0 KONT.
  pose proof (wmono_refl bsegs m) as GROW.
  astart (bv_unsigned sp)
    [(6989672%Z, 6989676%Z); (6989696%Z, 6989708%Z); (6990552%Z, 6990560%Z); (6990912%Z, 6990920%Z);
     (6990968%Z, 6990976%Z); (6993028%Z, 6993032%Z); (6993072%Z, 6993080%Z); (6993096%Z, 6993100%Z);
     (6993104%Z, 6993112%Z)].
  pose proof (munch_refl
    [((bv_unsigned sp - 240)%Z, bv_unsigned sp); (6989672%Z, 6989676%Z); (6989696%Z, 6989708%Z);
     (6990552%Z, 6990560%Z); (6990968%Z, 6990976%Z); (6993028%Z, 6993032%Z); (6993072%Z, 6993080%Z);
     (6993096%Z, 6993100%Z); (6993104%Z, 6993112%Z)] m) as MU.
  apply (aevt_evt RT AF PMc MST).
  carve_frame 80%nat STK.
  steps_to 1342272%Z.
  lazymatch type of FR with rw_cells _ _ _ (?c0 :: ?c1 :: ?c2 :: ?c3 :: ?rest) =>
    destruct (proj1 (rw_cells_app bsegs _ _ [c0; c1; c2; c3] rest) FR) as [ARGS FRHI]; clear FR end.
  cbn [cells_size csize Nat.add] in FRHI.
  replace (bv_unsigned sp + -80 + Z.of_nat 32)%Z with (bv_unsigned sp + -48)%Z in FRHI by lia.
  replace (Z_to_bv 64 (bv_unsigned sp + -64)) with (Z_to_bv 64 (bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -80)) + 16))
    by (rewrite unsigned_lit by lia; f_equal; lia).
  call_sp call_once_spec_5;
    [ exact STK | lia | lia | lia
    | replace (bv_unsigned sp + -80 + 24)%Z with (bv_unsigned sp + -56)%Z by lia;
      replace (bv_unsigned sp + -80 + 8)%Z with (bv_unsigned sp + -72)%Z by lia; exact ARGS
    | eassumption | eassumption | lia | eassumption | eassumption | eassumption | eassumption | eassumption
    | assumption | ].
  steps_to 1236520%Z.
  change (Z_to_bv 64 (5 + 1)) with (Z_to_bv 64 6) in *.
  replace (sx32 (Z_to_bv 64 6)) with (Z_to_bv 64 6) by (apply bv_eq; vm_compute; reflexivity).
  amo_step.
  cbn [amo_val] in REFC. rewrite lit_add_lit in REFC.
  steps_to 1331244%Z.
  acall_sp append_aevt_5;
    [ eassumption | a_ul | a_ul | a_ul | a_mod16 | eassumption | eassumption | eassumption | eassumption | apost_call ].
  steps_to 1236680%Z.
  lstep.
  lazymatch goal with
  | S : stk bsegs _ lo (bv_unsigned sp + -80)%Z, LOW : rw_cells bsegs _ (bv_unsigned sp + -80)%Z _ |- _ =>
      release_frame LOW S (bv_unsigned sp + -48)%Z
  end.
  lazymatch goal with S : stk bsegs _ lo (bv_unsigned sp + -48)%Z |- _ => release_frame FRHI S (bv_unsigned sp) end.
  afinish.
Qed.

Definition seg_postA_5 (Σ : rts RT) (sp gp tp s1 s4 s5 s6 s7 s8 s9 s10 s11 : word) (fc : bv 32) (lo : Z) (m : mem)
    : machine_state -> Prop :=
  fun st => exists (u0 u1 u2 r0 r1 r2 r3 r4 r5 r6 r7 u3 u4 u5 u6 : word) (G : bvmap 5 word) (mf : mem),
    st = MS (mkR (Z_to_bv 64 1233456) sp gp tp u0 u1 u2 (Z_to_bv 64 6990888) s1 r0 r1 r2 r3 r4 r5 r6 r7
                 (Z_to_bv 64 6989816) (Z_to_bv 64 6989808) s4 s5 s6 s7 s8 s9 s10 s11 u3 u4 u5 u6)
            G (Z_to_bv 64 1233456) fc None mf (seg_rom bsegs)
    /\ rt_pres_fp (rt_live RT Σ) (rt_frames RT Σ) (bv_unsigned sp)
         [(6989672%Z, 6989676%Z); (6989696%Z, 6989708%Z); (6989808%Z, 6989818%Z); (6990544%Z, 6990568%Z);
          (6990912%Z, 6990920%Z); (6990968%Z, 6990976%Z); (6993028%Z, 6993032%Z); (6993072%Z, 6993080%Z);
          (6993096%Z, 6993100%Z); (6993104%Z, 6993112%Z)] m mf
    /\ wmono bsegs m mf
    /\ mem_inv bsegs mf
    /\ ART RT Σ mf
    /\ stk bsegs mf lo (bv_unsigned sp)
    /\ rw_cells bsegs mf 6989696 [C8 (Z_to_bv 64 18446744073709551615); C4 (Z_to_bv 64 6)]
    /\ rw_cells bsegs mf 6989672 [C4 (Z_to_bv 64 6)]
    /\ rw_cells bsegs mf 6989808 [C8 (Z_to_bv 64 209792)]
    /\ rw_cells bsegs mf 6989816 [C1 (Z_to_bv 8 1); C1 (Z_to_bv 8 1)]
    /\ rw_cells bsegs mf 6990544 [C8 (Z_to_bv 64 1492656)]
    /\ rw_cells bsegs mf 6990552 [C8 (Z_to_bv 64 1)]
    /\ rw_cells bsegs mf 6990560 [C8 (Z_to_bv 64 209792)]
    /\ rw_cells bsegs mf 6990904 [C8 (Z_to_bv 64 6990928); C8 (Z_to_bv 64 6990976); C8 (Z_to_bv 64 6991168)]
    /\ rw_cells bsegs mf 6990968 [C8 (Z_to_bv 64 6990544)]
    /\ rw_cells bsegs mf 6993024 [CB 4 (repeat (Z_to_bv 8 0) 4); C4 z64; C4 z64]
    /\ ro_cells bsegs mf 7127163 [C1 (Z_to_bv 8 0)]
    /\ rw_cells bsegs mf 7127384 [C4 z64]
    /\ rw_cells bsegs mf 6993064 [C8 z64; C8 z64; CB 16 (repeat (Z_to_bv 8 0) 16); C4 z64; C4 z64; C8 z64].

Lemma seg_aevt_5 : forall Σ K ra sp gp tp t0 t1 t2 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (lo : Z) (canary : word),
  stk bsegs m lo (bv_unsigned sp) -> (lo + 496 + RT_STACK <= bv_unsigned sp)%Z -> (rt_sp0 RT Σ - STACK_WIN <= lo)%Z ->
  (bv_unsigned sp + 16 <= USTACK_TOP)%Z -> (bv_unsigned sp mod 16 = 0)%Z -> (bv_unsigned sp < 2^62)%Z ->
  rw_cells bsegs m 0x6aa780 [C8 (Z_to_bv 64 0); C4 (Z_to_bv 64 0)] ->
  rw_cells bsegs m 0x6aa768 [C4 (Z_to_bv 64 5)] ->
  rw_cells bsegs m 0x6aa7f0 [C8 (Z_to_bv 64 0)] ->
  rw_cells bsegs m 0x6aa7f8 [C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)] ->
  rw_cells bsegs m 0x6aaad0 [C8 (Z_to_bv 64 0)] ->
  rw_cells bsegs m 0x6aaad8 [C8 (Z_to_bv 64 0)] ->
  rw_cells bsegs m 0x6aaae0 [C8 (Z_to_bv 64 0)] ->
  rw_cells bsegs m 0x6aac38 [C8 (Z_to_bv 64 0x6aac50); C8 (Z_to_bv 64 0x6aac78); C8 (Z_to_bv 64 0x6aad40)] ->
  rw_cells bsegs m 0x6aac78 [CB 8 (repeat (Z_to_bv 8 0) 8)] ->
  rw_cells bsegs m 0x6ab480 [CB 4 (repeat (Z_to_bv 8 0) 4); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0)] ->
  ro_cells bsegs m 0x16f508 [C8 (Z_to_bv 64 0x6cbe28)] -> ro_cells bsegs m 0x6cbe28 [C8 canary] ->
  ro_cells bsegs m 0x6cc07b [C1 (Z_to_bv 8 0)] -> rw_cells bsegs m 0x6cc158 [C4 (Z_to_bv 64 0)] ->
  rw_cells bsegs m 0x6ab4a8 [C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); CB 16 (repeat (Z_to_bv 8 0) 16); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)] ->
  mem_inv bsegs m -> ART RT Σ m ->
  (forall ms', seg_postA_5 Σ sp gp tp s1 s4 s5 s6 s7 s8 s9 s10 s11 fc lo m ms' -> aevt RT PMc Σ K ms') ->
  aevt RT PMc Σ K (MS (mkR ra sp gp tp t0 t1 t2 (Z_to_bv 64 0x6aac28) s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 (Z_to_bv 64 0x6aa7f0) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x12d200) fc None m (seg_rom bsegs)).
Proof using AF RTC MCI FDO MST.
  intros Σ K ra sp gp tp t0 t1 t2 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo canary
    STK ROOM WIN TOP ALIGN SMALL IDC CTR CLOC GUARD VPTR REFC TAB VEC SLOT MUTEX GOTC CANC NLB NLW CONDV MEMOK ART0 KONT.
  pose proof (wmono_refl bsegs m) as GROW.
  astart (bv_unsigned sp)
    [(6989672%Z, 6989676%Z); (6989696%Z, 6989708%Z); (6989808%Z, 6989818%Z); (6990544%Z, 6990568%Z);
     (6990912%Z, 6990920%Z); (6990968%Z, 6990976%Z); (6993028%Z, 6993032%Z); (6993072%Z, 6993080%Z);
     (6993096%Z, 6993100%Z); (6993104%Z, 6993112%Z)].
  pose proof (munch_refl [((bv_unsigned sp - 496)%Z, bv_unsigned sp); (6989808%Z, 6989818%Z); (6990544%Z, 6990568%Z)] m)
    as MU.
  apply (aevt_evt RT AF PMc MST).
  steps_to 1379708%Z.
  acallc (newlocale_aevt RT AF RTC MCI PMc FDO MST) clearing idtac by (first [ eassumption | a_ul ]).
  steps_to 1236404%Z.
  acallc install_aevt_5 clearing idtac by (first [ eassumption | a_ul | reflexivity ]).
  change (Z_to_bv 64 (0 + 1)) with (Z_to_bv 64 1) in *.
  afinish.
Qed.

End AevtPieces.
