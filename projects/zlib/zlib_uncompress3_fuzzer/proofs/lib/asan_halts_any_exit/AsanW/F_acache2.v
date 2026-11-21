(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_halts_any_exit.Lib Require Import ITree Nodes Decode Arr.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_halts_any_exit.Spec Require Import STree AsanCtrl.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_halts_any_exit.AsanW Require Import AImg AProto ABase.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_halts_any_exit.LibA Require Import StepF.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_halts_any_exit.AsanW Require Import AKit F_acache.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_halts_any_exit.Common Require Import RunDraw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Ltac band_lin :=
  repeat match goal with H : iclr ?a ?n |- _ => unfold iclr, AIMG_LO, AIMG_HI in H end.
Local Ltac with_band H tac :=
  let H' := fresh H in pose proof H as H'; unfold sclr, iclr, ablk, KLS, AIMG_LO, AIMG_HI in H'; tac; try clear H'.


Notation acache_rec t c := (t + 208 + c * 80) (only parsing).
Notation acache_stats t := (t + 2784) (only parsing).

Section CANSEC1. Context {rc : runConstT}.
Definition calloc_pre_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (t c lo : Z) (m : amem) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR (Z_to_bv 64 0x41b9c) (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp t0 t1 t2
                  (Z_to_bv 64 c) (Z_to_bv 64 (acache_rec t c))
                  (Z_to_bv 64 (t + 208)) (Z_to_bv 64 (acache_rec t c)) (Z_to_bv 64 AINSTANCE) (Z_to_bv 64 c) a4 a5 a6 a7
                  (Z_to_bv 64 8) (Z_to_bv 64 (t + 208)) (Z_to_bv 64 AINSTANCE) s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (Z_to_bv 64 0x4203c) fc None m' (seg_rom asegs)
    /\ munch [(bv_unsigned sp - 48, bv_unsigned sp)]%Z m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ stk asegs m' lo (bv_unsigned sp - 48)
    /\ rw_cells asegs m' (bv_unsigned sp + -48) [C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].

Lemma calloc_pre_spec : forall RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : amem) (t size c lo : Z) (maxc csz : word),
  stk asegs m lo (bv_unsigned sp) -> ATOP <= lo -> lo <= bv_unsigned sp - 48 ->
  mem_inv asegs m ->
  a0 = Z_to_bv 64 AINSTANCE -> a1 = Z_to_bv 64 (t + 208) -> a2 = Z_to_bv 64 size -> a3 = Z_to_bv 64 8 ->
  16 <= size <= 512 -> Z.shiftr (size + 31) 5 = c ->
  rw_cells asegs m (acache_rec t c) [C4 (Z_to_bv 64 0); C4 maxc; C8 csz] ->
  iclr t 4096 -> t + 4096 <= ATOP ->
  rng_aimg RNG -> rng RNG lo (bv_unsigned sp - lo) -> rng RNG t 4096 ->
  evtF asegs RNG (calloc_pre_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc t c lo m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x418ec) fc None m (seg_rom asegs)).
Proof.
  intros until csz. intros ST CEIL LO MI -> -> -> -> SZ HC CR T0 T1 RIMG RSTK RT. band_lin.
  unfold AIMG_HI, AINSTANCE in *.
  assert (C1 : 1 <= c <= 16) by (rewrite <- HC; rewrite Z.shiftr_div_pow2 by lia; Z.div_mod_to_equations; lia).
  word_range sp SPR.
  pose proof (munch_refl [(bv_unsigned sp - 48, bv_unsigned sp)]%Z m) as MU.
  pose proof (wmono_refl asegs m) as WM.
  carve_frame 48%nat ST.
  do 7 step.
  do 3 zstep.
  replace (size <? 1) with false by (symmetry; apply Z.ltb_ge; lia). cbn [Z.b2z]. rewrite Z.add_0_r.
  rewrite (Z.mod_small size) by lia. rewrite zb_lxor_ones by lia.
  step. if_cases K0; zify_cond K0; [| exfalso; lia].
  do 2 step. step. if_lit.
  step. step. if_lit.
  step. if_cases K1; zify_cond K1. { exfalso. lia. }
  step. step. if_cases K2; zify_cond K2. { exfalso. lia. }
  do 2 zstep. rewrite HC.
  step.
  step. if_cases K3; zify_cond K3. { exfalso. lia. }
  step. step. if_cases K4; zify_cond K4. { exfalso. lia. }
  step. zstep. zstep.
  assert (RB : t + 208 + 80 <= t + 208 + c * 80 /\ t + 208 + c * 80 + 80 <= t + 1568) by lia.
  remember (t + 208 + c * 80) as R eqn:HR.
  lstep.
  step. if_cases K5; zify_cond K5. 2: { exfalso. apply K5. reflexivity. }
  do 7 step.
  step.
  subst R. finish.
Qed.

Lemma calloc_popj_spec : forall RNG sp gp tp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (rav s0v s1v s2v s3v s4v rv : word)
    (F : bvmap 5 word) fc (m : amem) (t c cnt spacebeg lo : Z) (maxc csz stj : word) (chunks : list word) (idxw : word),
  stk asegs m lo (bv_unsigned sp - 48) -> ATOP <= lo -> lo <= bv_unsigned sp - 48 ->
  mem_inv asegs m ->
  bv_unsigned rv <> 0 ->
  1 <= c <= 16 ->
  rw_cells asegs m (bv_unsigned sp + -48) [C8 s4v; C8 s3v; C8 s2v; C8 s1v; C8 s0v; C8 rav] ->
  rw_cells asegs m 0xd5338 [C8 (Z_to_bv 64 spacebeg)] ->
  rw_cells asegs m (acache_rec t c) [C4 (Z_to_bv 64 cnt); C4 maxc; C8 csz] ->
  u32arr asegs m (acache_rec t c + 16) chunks -> length chunks = 16%nat ->
  0 < cnt <= 16 -> nth_error chunks (Z.to_nat (cnt - 1)) = Some idxw -> bv_unsigned idxw < 2^32 ->
  rw_cells asegs m (acache_stats t) [C8 stj] ->
  iclr t 4096 -> t + 4096 <= ATOP -> t mod 4096 = 0 -> 0 <= spacebeg < 2^47 ->
  rng_aimg RNG -> rng RNG lo (bv_unsigned sp - lo) -> rng RNG t 4096 ->
  evtF asegs RNG (cache_hit_post rav sp gp tp s0v s1v s2v s3v s4v s5 s6 s7 s8 s9 s10 s11 F fc t c cnt (bv_unsigned idxw) spacebeg lo maxc csz m)
    (MS (mkR (Z_to_bv 64 0x41b9c) (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp t0 t1 t2
             (Z_to_bv 64 c) (Z_to_bv 64 (acache_rec t c))
             rv a1 a2 a3 a4 a5 a6 a7
             (Z_to_bv 64 8) (Z_to_bv 64 (t + 208)) (Z_to_bv 64 AINSTANCE) s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x41b9c) fc None m (seg_rom asegs)).
Proof.
  intros until idxw. intros ST CEIL LO MI RV C1 FR SB CR CH LCH CNT NTH IXS STS T0 T1 TAL SBR RIMG RSTK RT. band_lin.
  unfold AIMG_HI, AINSTANCE in *.
  word_range sp SPR. word_range idxw IXR. word_range rv RVR.
  pose proof (munch_refl [(bv_unsigned sp - 48, bv_unsigned sp); (t + 208 + c * 80, t + 208 + c * 80 + 4); (t + 2784, t + 2784 + 8)]%Z m) as MU.
  pose proof (wmono_refl asegs m) as WM.
  assert (RB : t + 208 + 80 <= t + 208 + c * 80 /\ t + 208 + c * 80 + 80 <= t + 1568) by lia.
  remember (t + 208 + c * 80) as R eqn:HR.
  step. if_cases K0; zify_cond K0. { exfalso. apply RV. exact K0. }
  lstep.
  do 3 step.
  step.
  do 3 zstep.
  step.
  zstep. step. zstep. zstep.
  replace (Z.shiftr (Z.shiftl (cnt + -1) 32 mod 18446744073709551616) 30) with (4 * (cnt + -1))
    by (rewrite Z.shiftl_mul_pow2, Z.shiftr_div_pow2 by lia; rewrite Z.mod_small by lia; change (2^32) with (4 * 2^30); rewrite Z.mul_assoc, Z.div_mul by lia; lia).
  pose proof (u32arr_read asegs _ _ chunks (cnt + -1) idxw (wa (R + 16 + 4 * (cnt + -1))) CH ltac:(replace (cnt + -1) with (cnt - 1) by lia; exact NTH) ltac:(lia) ltac:(f_equal; lia)) as RD.
  step. clear RD. rewrite (zx32_small idxw) by lia.
  assert (AMO : amo_aligned AD (Z_to_bv 64 (t + 2784)) = true) by (apply amo_alignedD_intro; [lia| Z.div_mod_to_equations; lia]).
  amo_stepA AMO.
  step.
  do 4 zstep.
  step. step. if_lit.
  do 8 step.
  release_frame FR ST (bv_unsigned sp). subst R.
  setreg 10 (Z_to_bv 64 (spacebeg + c * 2^32 + 16 * bv_unsigned idxw))
    ltac:(apply Z_to_bv_eqm; rewrite ?Z.shiftl_mul_pow2 by lia; zeq).
  finish. eexists. exact STS.
Qed.
End CANSEC1.
