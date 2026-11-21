(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_halts_any_exit.Lib Require Import Arr InitMem.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_halts_any_exit.Spec Require Import AsanCtrl AsanEmbed.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_halts_any_exit.BothW Require Import BImg ABase AQConst ABytes.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_halts_any_exit.LibA Require Import StepF.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_halts_any_exit.BothW Require Import AKit AKit2 AKitQ F_aintal.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_halts_any_exit.Common Require Import RunDraw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Section CANSEC1. Context {rc : runConstT}.
Definition ficptA_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (p lo : Z) (m : amem) : machine_state -> Prop :=
  fun ms' => exists (t0 t1 t2 a6 a7 t3 t4 t5 t6 : word) m' (junk1 junk2 : list byte),
    ms' = MS (mkR (Z_to_bv 64 0x5e870) (Z_to_bv 64 (bv_unsigned sp + -2128)) gp tp t0 t1 t2
                  sp (Z_to_bv 64 p)
                  (Z_to_bv 64 (bv_unsigned sp + -2128)) (Z_to_bv 64 0x5e85c) sp (Z_to_bv 64 0) (Z_to_bv 64 1) (Z_to_bv 64 30) a6 a7
                  (Z_to_bv 64 0x5e85c) (Z_to_bv 64 1) (Z_to_bv 64 (bv_unsigned sp + -2128)) (Z_to_bv 64 (bv_unsigned sp + -81))
                  s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (Z_to_bv 64 0x5e8b4) fc None m' (seg_rom bsegs)
    /\ munch [(bv_unsigned sp - 2176, bv_unsigned sp); (0xdad40, 0xdad40 + 0x81030); (0x1695c8, 0x1695c8 + 4)]%Z m m'
    /\ wmono bsegs m m' /\ mem_inv bsegs m'
    /\ stk bsegs m' lo (bv_unsigned sp + -2128)
    /\ rw_cells bsegs m' (bv_unsigned sp + -2128) [C8 (Z_to_bv 64 (bv_unsigned sp + -2112)); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0)]
    /\ rw_cells bsegs m' (bv_unsigned sp + -2112) [CB 2040 junk1]
    /\ rw_cells bsegs m' (bv_unsigned sp + -72) [C8 sp; CB 8 junk2; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]
    /\ rw_cells bsegs m' 0x1695c8 [C1 (Z_to_bv 8 1); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)]
    /\ stk bsegs m' 0xdad40 (0xdad40 + 0x81030)
    /\ (forall j, 0 <= j < 32768 -> bytes_at bsegs m' (0xdad48 + 8 * j) (le8 (Z_to_bv 64 0))).

Lemma ficptA_spec : forall (p : Z) (ia : bool) RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : amem) (lo : Z),
  stk bsegs m lo (bv_unsigned sp) -> ATOP <= lo -> lo <= bv_unsigned sp - 2176 ->
  mem_inv bsegs m ->
  a0 = Z_to_bv 64 p -> 0 <= p < 2^47 ->
  rw_cells bsegs m 0xda83c [C4 (Z_to_bv 64 30)] ->
  rw_cells bsegs m 0xd1320 [C8 (Z_to_bv 64 0x16b668); C8 (Z_to_bv 64 0xd7338); C8 (Z_to_bv 64 0xd9b38);
                             C8 (Z_to_bv 64 0xda828); C8 (Z_to_bv 64 0xda830); C8 (Z_to_bv 64 0xda820)] ->
  rw_cells bsegs m 0x16b68a [C1 (Z_to_bv 8 1)] ->
  rw_cells bsegs m 0xd1310 [C8 (Z_to_bv 64 0x1695e0)] -> rw_cells bsegs m 0x1695e0 [C8 (Z_to_bv 64 4096)] ->
  rw_cells bsegs m AIA_FLAG [C1 (Z_to_bv 8 (if ia then 1 else 0)); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)] ->
  stk bsegs m AIA_BASE (AIA_BASE + AIA_SIZE) ->
  (ia = true -> forall j, 0 <= j < 32768 -> bytes_at bsegs m (AIA_MAP1 + 8 * j) (le8 (Z_to_bv 64 0))) ->
  rng_aimg RNG -> rng RNG lo (bv_unsigned sp - lo) ->
  evtF bsegs RNG (ficptA_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc p lo m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 AFREE_SYM) fc None m (seg_rom bsegs)).
Proof.
  intros until lo. intros ST CEIL LO MI -> PR MCS GOT CF34 PG1 PG2 FL IA Z2 RIMG RSTK.
  unfold AFREE_SYM, AFREE_PC, AIA_BASE, AIA_SIZE, AIA_FLAG, AIA_MAP1, AIA_MAP1_LEN in *.
  word_range sp SPR.
  pose proof (munch_refl [(bv_unsigned sp - 2176, bv_unsigned sp); (0xdad40, 0xdad40 + 0x81030); (0x1695c8, 0x1695c8 + 4)]%Z m) as MU.
  pose proof (wmono_refl bsegs m) as WM.
  pose proof (munch_refl [(bv_unsigned sp - 2176, bv_unsigned sp)]%Z m) as MU0.
  step.
  carve_frame 2128%nat ST.
  cb_split3 FR 16%nat 2040%nat 72%nat. rw_split FR 1%nat FRa FR'. rw_split FR' 1%nat FRt FRs.
  do 8 step.
  zstep. zstep. step. step.
  lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) =>
    assert (Z2' : ia = true -> forall j, 0 <= j < 32768 -> bytes_at bsegs mm (896328 + 8 * j) (le8 (Z_to_bv 64 0)))
      by (intros Hia j Hj; eapply bytes_at_agree; [exact (Z2 Hia j Hj)|];
          intros i Hi; apply MU0; cbn [outside]; rewrite length_le8 in Hi; rewrite wa_unsigned by lia; lia) end.
  clear Z2 MU0.
  step. call_sp internal_allocator_spec;
    [exact ST| exact CEIL| lia| exact MI| exact FL| exact IA| exact Z2'| exact PG1| exact PG2| solve_rng|].
  try rename MI0 into MI. clear Z2'.
  match goal with H : stk bsegs ?mm lo _ |- _ => rename H into ST end.
  match goal with H : stk bsegs ?mm 896320 _ |- _ => rename H into IA' end.
  match goal with H : rw_cells bsegs ?mm 1480136 _ |- _ => rename H into FL' end.
  match goal with H : forall j, _ -> bytes_at bsegs _ _ _ |- _ => rename H into MAP end.
  snapshot [(bv_unsigned sp - 2176, bv_unsigned sp)]%Z MU1 WM1.
  zstep. setreg 11%Z (Z_to_bv 64 0) ltac:(f_equal; rewrite Z.shiftr_div_pow2 by lia; symmetry; apply Z.div_small; lia).
  step. if_lit.
  zstep.
  remember (Z.shiftr p 32) as j eqn:Hj.
  assert (JR : 0 <= j < 32768) by (subst j; rewrite Z.shiftr_div_pow2 by lia; Z.div_mod_to_equations; lia).
  zstep. rewrite (Z.shiftl_mul_pow2 j 3) by lia. change (2^3) with 8. zstep.
  pose proof (bytes_at_read8 _ _ _ (MAP j JR)) as RD.
  replace (896328 + 8 * j) with (896320 + j * 8 + 8) in RD by lia.
  step. clear RD.
  step. step. if_lit.
  clear Hj JR.
  zstep. zstep. zstep. zstep. zstep.
  step. sstep. step.
  step. step. lstep. step. step.
  step. step. if_lit.
  step. step. step.
  step. step. lstep. step.
  step. step. lstep. step. step.
  step. zstep. zstep. zstep. step.
  change ((Z.b2z (30 <? 1) + -1) mod 18446744073709551616) with 18446744073709551615. rewrite land_ones_l by lia.
  sstep.
  step. if_lit.
  zstep. zstep. step. step. step. step.
  rw_split FRa 1%nat FRa1 FRa2. apply rw_cells_C8_to_C4C4_zero in FRa2. rw_join FRa1 FRa2 FRA.
  apply evtF_done. unfold ficptA_post. do 10 eexists. exists (firstn 2040 (skipn 16 junk)). eexists.
  split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [assumption|]. split; [exact ST|].
  split; [exact FRA|]. split; [exact FRt|]. split; [exact FRs|]. split; [exact FL'|]. split; [exact IA'|].
  intros j0 Hj0. eapply bytes_at_agree; [exact (MAP j0 Hj0)|].
  intros i Hi. apply MU1. cbn [outside]. rewrite length_le8 in Hi. rewrite wa_unsigned by lia. lia.
Qed.

Lemma ficptD_spec : forall RNG sp gp tp t0 t1 t2 s0x s1x a0 a1 a2 a3 a4 a5 a6 a7 s2x s3x s4x s5x s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (rav s0v s1v s2v s3v s4v s5v spv : word) (F : bvmap 5 word) fc (m : amem) (lo : Z) (junk2 : list byte),
  stk bsegs m lo (bv_unsigned sp + -2128) -> ATOP <= lo -> lo <= bv_unsigned sp - 2128 ->
  mem_inv bsegs m ->
  (exists csA, rw_cells bsegs m (bv_unsigned sp + -2128) csA /\ cells_size csA = 16%nat) ->
  (exists csT, rw_cells bsegs m (bv_unsigned sp + -2112) csT /\ cells_size csT = 2040%nat) ->
  rw_cells bsegs m (bv_unsigned sp + -72) [C8 spv; CB 8 junk2; C8 s5v; C8 s4v; C8 s3v; C8 s2v; C8 s1v; C8 s0v; C8 rav] ->
  rng_aimg RNG -> rng RNG lo (bv_unsigned sp - lo) ->
  evtF bsegs RNG (fun ms' =>
      ms' = MS (mkR rav sp gp tp t0 t1 t2 s0v s1v a0 a1 a2 a3 a4 a5 a6 a7 s2v s3v s4v s5v s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (ret_pc rav) fc None m (seg_rom bsegs)
      /\ stk bsegs m lo (bv_unsigned sp))
    (MS (mkR (Z_to_bv 64 0x5e8cc) (Z_to_bv 64 (bv_unsigned sp + -2128)) gp tp t0 t1 t2 s0x s1x a0 a1 a2 a3 a4 a5 a6 a7
              s2x s3x s4x s5x s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x5e8cc) fc None m (seg_rom bsegs)).
Proof.
  intros until junk2. intros ST CEIL LO MI [csA [FRA SZA]] [csT [FRT SZT]] FRS RIMG RSTK. atop_facts.
  word_range sp SPR.
  pose proof (munch_refl (@nil (Z * Z)) m) as MU. pose proof (wmono_refl bsegs m) as WM.
  zstep. do 7 step. zstep. step.
  pose proof (rw_cells_forget bsegs _ _ _ FRA) as [jA FRA']. rewrite SZA in FRA'. clear FRA.
  release_frame FRA' ST (bv_unsigned sp + -2112).
  pose proof (rw_cells_forget bsegs _ _ _ FRT) as [jT FRT']. rewrite SZT in FRT'. clear FRT.
  release_frame FRT' ST (bv_unsigned sp + -72).
  release_frame FRS ST (bv_unsigned sp).
  apply evtF_done. split; [|exact ST].
  reflexivity.
Qed.
End CANSEC1.
