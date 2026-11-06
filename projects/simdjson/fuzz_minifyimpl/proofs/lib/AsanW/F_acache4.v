(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.Lib Require Import ITree Nodes Decode Arr.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.Spec Require Import STree AsanCtrl.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.AsanW Require Import AImg AProto ABase.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.LibA Require Import StepF.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.AsanW Require Import AKit AModelFacts APrimFacts F_acache F_acache2 F_acache3.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.Common Require Import RunDraw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
(* [comment removed for export] *)
Local Ltac band_lin :=      (* [comment removed for export] *)
  repeat match goal with H : iclr ?a ?n |- _ => unfold iclr, AIMG_LO, AIMG_HI in H end.
Local Ltac with_band H tac :=
  let H' := fresh H in pose proof H as H'; unfold sclr, iclr, ablk, KLS, AIMG_LO, AIMG_HI in H'; tac; try clear H'.


Notation acache_rec t c := (t + 208 + c * 80) (only parsing).
Notation acache_stats t := (t + 2784) (only parsing).

Section CANSEC1. Context {rc : runConstT}.
Lemma calloc_hit_gen : forall RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : amem) (t size c cnt spacebeg lo : Z) (maxc csz stj : word) (chunks : list word) (idxw : word),
  stk asegs m lo (bv_unsigned sp) -> ATOP <= lo -> lo <= bv_unsigned sp - 48 ->
  mem_inv asegs m ->
  a0 = Z_to_bv 64 AINSTANCE -> a1 = Z_to_bv 64 (t + 208) -> a2 = Z_to_bv 64 size -> a3 = Z_to_bv 64 8 ->
  16 <= size <= 65536 -> size mod 8 = 0 -> class_id size = c ->
  rw_cells asegs m 0x16cd78 [C8 (Z_to_bv 64 spacebeg)] ->      (* [comment removed for export] *)
  rw_cells asegs m (acache_rec t c) [C4 (Z_to_bv 64 cnt); C4 maxc; C8 csz] ->
  u32arr asegs m (acache_rec t c + 16) chunks -> length chunks = 16%nat ->
  0 < cnt <= 16 -> nth_error chunks (Z.to_nat (cnt - 1)) = Some idxw -> bv_unsigned idxw < 2^32 ->
  rw_cells asegs m (acache_stats t) [C8 stj] ->
  iclr t 4096 -> t + 4096 <= ATOP -> t mod 4096 = 0 -> 0 <= spacebeg < 2^47 ->
  rng_aimg RNG -> rng RNG lo (bv_unsigned sp - lo) -> rng RNG t 4096 ->
  evtF asegs RNG (cache_hit_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc t c cnt (bv_unsigned idxw) spacebeg lo maxc csz m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x5fb98) fc None m (seg_rom asegs)).
Proof.
  intros until idxw. intros ST CEIL LO MI -> -> -> -> SZ M8 HC SB CR CH LCH CNT NTH IXS STS T0 T1 TAL SBR RIMG RSTK RT. band_lin.   (* [comment removed for export] *)
  unfold AIMG_HI, AINSTANCE in *.
  pose proof (class_facts size ltac:(lia)) as CF. cbv zeta in CF. rewrite HC in CF. destruct CF as (C1 & CS1 & CS2 & CS3 & CSM & CBG).
  word_range sp SPR. word_range idxw IXR.
  pose proof (munch_refl [(bv_unsigned sp - 48, bv_unsigned sp); (t + 208 + c * 80, t + 208 + c * 80 + 4); (t + 2784, t + 2784 + 8)]%Z m) as MU.
  pose proof (wmono_refl asegs m) as WM.
  carve_frame 48%nat ST.
  do 7 step.                                        (* [comment removed for export] *)
  do 3 zstep.                                       (* [comment removed for export] *)
  replace (size <? 1) with false by (symmetry; apply Z.ltb_ge; lia). cbn [Z.b2z]. rewrite Z.add_0_r.
  rewrite (Z.mod_small size) by lia. rewrite zb_lxor_ones by lia.
  step. if_cases K0; zify_cond K0; [| exfalso; lia].  (* [comment removed for export] *)
  do 2 step. step. if_lit.                          (* [comment removed for export] *)
  step. step. if_lit.                               (* [comment removed for export] *)
  step. if_cases K1; zify_cond K1. { exfalso. lia. }   (* [comment removed for export] *)
  step. step. if_cases K2; zify_cond K2.            (* [comment removed for export] *)
  (* [comment removed for export] *)
  1: eapply evtF_cut; [eapply (classblock_spec RNG); [lia | assumption | exact RIMG] |].
  1: cbv beta; intros msB PB; destruct PB as (a2b & a4b & a5b & a6b & a7b & t0b & t1b & ->); rewrite HC.
  2: do 2 zstep; rewrite <- (CSM ltac:(lia)); step.
  (* [comment removed for export] *)
  all: step.
  all: if_cases K3; zify_cond K3; [exfalso; lia|].
  all: step.
  all: step.
  all: if_cases K4; zify_cond K4; [exfalso; lia|].
  all: step.
  all: zstep.
  all: zstep.
  all: assert (RB : t + 208 + 80 <= t + 208 + c * 80 /\ t + 208 + c * 80 + 80 <= t + 2688) by lia.
  all: remember (t + 208 + c * 80) as R eqn:HR.
  all: lstep.
  all: step.
  all: if_cases K5; zify_cond K5; [exfalso; lia|].
  all: do 3 zstep.
  all: step.
  all: zstep.
  all: step.
  all: zstep.
  all: zstep.
  all: replace (Z.shiftr (Z.shiftl (cnt + -1) 32 mod 18446744073709551616) 30) with (4 * (cnt + -1))
    by (rewrite Z.shiftl_mul_pow2, Z.shiftr_div_pow2 by lia; rewrite Z.mod_small by lia; change (2^32) with (4 * 2^30); rewrite Z.mul_assoc, Z.div_mul by lia; lia).
  all: pose proof (u32arr_read asegs _ _ chunks (cnt + -1) idxw (wa (R + 16 + 4 * (cnt + -1))) CH ltac:(replace (cnt + -1) with (cnt - 1) by lia; exact NTH) ltac:(lia) ltac:(f_equal; lia)) as RD.
  all: step.
  all: clear RD.
  all: rewrite (zx32_small idxw) by lia.
  all: assert (AMO : amo_aligned AD (Z_to_bv 64 (t + 2784)) = true) by (apply amo_alignedD_intro; [lia| Z.div_mod_to_equations; lia]).
  all: amo_stepA AMO.
  all: step.
  all: do 4 zstep.
  all: step.
  all: step.
  all: if_lit.
  all: do 8 step.
  all: release_frame FR ST (bv_unsigned sp).
  all: subst R.
  all: setreg 10 (Z_to_bv 64 (spacebeg + c * 2^32 + 16 * bv_unsigned idxw))
    ltac:(apply Z_to_bv_eqm; rewrite ?Z.shiftl_mul_pow2 by lia; zeq).
  all: finish.
  all: eexists.
  all: exact STS.
Qed.

Lemma calloc_pre_gen : forall RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : amem) (t size c lo : Z) (maxc csz : word),
  stk asegs m lo (bv_unsigned sp) -> ATOP <= lo -> lo <= bv_unsigned sp - 48 ->
  mem_inv asegs m ->
  a0 = Z_to_bv 64 AINSTANCE -> a1 = Z_to_bv 64 (t + 208) -> a2 = Z_to_bv 64 size -> a3 = Z_to_bv 64 8 ->
  16 <= size <= 65536 -> size mod 8 = 0 -> class_id size = c ->
  rw_cells asegs m (acache_rec t c) [C4 (Z_to_bv 64 0); C4 maxc; C8 csz] ->
  iclr t 4096 -> t + 4096 <= ATOP ->
  rng_aimg RNG -> rng RNG lo (bv_unsigned sp - lo) -> rng RNG t 4096 ->
  evtF asegs RNG (calloc_pre_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc t c lo m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x5fb98) fc None m (seg_rom asegs)).
Proof.
  intros until csz. intros ST CEIL LO MI -> -> -> -> SZ M8 HC CR T0 T1 RIMG RSTK RT. band_lin.   (* [comment removed for export] *)
  unfold AIMG_HI, AINSTANCE in *.
  pose proof (class_facts size ltac:(lia)) as CF. cbv zeta in CF. rewrite HC in CF. destruct CF as (C1 & CS1 & CS2 & CS3 & CSM & CBG).
  word_range sp SPR.
  pose proof (munch_refl [(bv_unsigned sp - 48, bv_unsigned sp)]%Z m) as MU.
  pose proof (wmono_refl asegs m) as WM.
  carve_frame 48%nat ST.
  do 7 step.                                        (* [comment removed for export] *)
  do 3 zstep.                                       (* [comment removed for export] *)
  replace (size <? 1) with false by (symmetry; apply Z.ltb_ge; lia). cbn [Z.b2z]. rewrite Z.add_0_r.
  rewrite (Z.mod_small size) by lia. rewrite zb_lxor_ones by lia.
  step. if_cases K0; zify_cond K0; [| exfalso; lia].  (* [comment removed for export] *)
  do 2 step. step. if_lit.                          (* [comment removed for export] *)
  step. step. if_lit.                               (* [comment removed for export] *)
  step. if_cases K1; zify_cond K1. { exfalso. lia. }   (* [comment removed for export] *)
  step. step. if_cases K2; zify_cond K2.            (* [comment removed for export] *)
  (* [comment removed for export] *)
  1: eapply evtF_cut; [eapply (classblock_spec RNG); [lia | assumption | exact RIMG] |].
  1: cbv beta; intros msB PB; destruct PB as (a2b & a4b & a5b & a6b & a7b & t0b & t1b & ->); rewrite HC.
  2: do 2 zstep; rewrite <- (CSM ltac:(lia)); step.
  (* [comment removed for export] *)
  all: step.
  all: if_cases K3; zify_cond K3; [exfalso; lia|].
  all: step.
  all: step.
  all: if_cases K4; zify_cond K4; [exfalso; lia|].
  all: step.
  all: zstep.
  all: zstep.
  all: assert (RB : t + 208 + 80 <= t + 208 + c * 80 /\ t + 208 + c * 80 + 80 <= t + 2688) by lia.
  all: remember (t + 208 + c * 80) as R eqn:HR.
  all: lstep.
  all: step.
  all: if_cases K5; zify_cond K5; [| exfalso; apply K5; reflexivity].
  all: do 7 step.
  all: step.
  all: subst R.
  all: finish.
Qed.

Lemma calloc_popj_gen : forall RNG sp gp tp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (rav s0v s1v s2v s3v s4v rv : word)
    (F : bvmap 5 word) fc (m : amem) (t c cnt spacebeg lo : Z) (maxc csz stj : word) (chunks : list word) (idxw : word),
  stk asegs m lo (bv_unsigned sp - 48) -> ATOP <= lo -> lo <= bv_unsigned sp - 48 ->
  mem_inv asegs m ->
  bv_unsigned rv <> 0 ->
  1 <= c <= 30 ->
  rw_cells asegs m (bv_unsigned sp + -48) [C8 s4v; C8 s3v; C8 s2v; C8 s1v; C8 s0v; C8 rav] ->
  rw_cells asegs m 0x16cd78 [C8 (Z_to_bv 64 spacebeg)] ->      (* [comment removed for export] *)
  rw_cells asegs m (acache_rec t c) [C4 (Z_to_bv 64 cnt); C4 maxc; C8 csz] ->
  u32arr asegs m (acache_rec t c + 16) chunks -> length chunks = 16%nat ->
  0 < cnt <= 16 -> nth_error chunks (Z.to_nat (cnt - 1)) = Some idxw -> bv_unsigned idxw < 2^32 ->
  rw_cells asegs m (acache_stats t) [C8 stj] ->
  iclr t 4096 -> t + 4096 <= ATOP -> t mod 4096 = 0 -> 0 <= spacebeg < 2^47 ->
  rng_aimg RNG -> rng RNG lo (bv_unsigned sp - lo) -> rng RNG t 4096 ->
  evtF asegs RNG (cache_hit_post rav sp gp tp s0v s1v s2v s3v s4v s5 s6 s7 s8 s9 s10 s11 F fc t c cnt (bv_unsigned idxw) spacebeg lo maxc csz m)
    (MS (mkR (Z_to_bv 64 0x5fe48) (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp t0 t1 t2
             (Z_to_bv 64 c) (Z_to_bv 64 (acache_rec t c))
             rv a1 a2 a3 a4 a5 a6 a7
             (Z_to_bv 64 8) (Z_to_bv 64 (t + 208)) (Z_to_bv 64 AINSTANCE) s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x5fe48) fc None m (seg_rom asegs)).
Proof.
  intros until idxw. intros ST CEIL LO MI RV C1 FR SB CR CH LCH CNT NTH IXS STS T0 T1 TAL SBR RIMG RSTK RT. band_lin.   (* [comment removed for export] *)
  unfold AIMG_HI, AINSTANCE in *.
  word_range sp SPR. word_range idxw IXR. word_range rv RVR.
  pose proof (munch_refl [(bv_unsigned sp - 48, bv_unsigned sp); (t + 208 + c * 80, t + 208 + c * 80 + 4); (t + 2784, t + 2784 + 8)]%Z m) as MU.
  pose proof (wmono_refl asegs m) as WM.
  assert (RB : t + 208 + 80 <= t + 208 + c * 80 /\ t + 208 + c * 80 + 80 <= t + 2688) by lia.
  remember (t + 208 + c * 80) as R eqn:HR.
  step. if_cases K0; zify_cond K0. { exfalso. apply RV. exact K0. }   (* [comment removed for export] *)
  lstep.                                            (* [comment removed for export] *)
  do 3 step.                                        (* [comment removed for export] *)
  step.                                             (* [comment removed for export] *)
  do 3 zstep.                                       (* [comment removed for export] *)
  step.                                             (* [comment removed for export] *)
  zstep. step. zstep. zstep.                        (* [comment removed for export] *)
  replace (Z.shiftr (Z.shiftl (cnt + -1) 32 mod 18446744073709551616) 30) with (4 * (cnt + -1))
    by (rewrite Z.shiftl_mul_pow2, Z.shiftr_div_pow2 by lia; rewrite Z.mod_small by lia; change (2^32) with (4 * 2^30); rewrite Z.mul_assoc, Z.div_mul by lia; lia).
  pose proof (u32arr_read asegs _ _ chunks (cnt + -1) idxw (wa (R + 16 + 4 * (cnt + -1))) CH ltac:(replace (cnt + -1) with (cnt - 1) by lia; exact NTH) ltac:(lia) ltac:(f_equal; lia)) as RD.
  step. clear RD. rewrite (zx32_small idxw) by lia.  (* [comment removed for export] *)
  assert (AMO : amo_aligned AD (Z_to_bv 64 (t + 2784)) = true) by (apply amo_alignedD_intro; [lia| Z.div_mod_to_equations; lia]).
  amo_stepA AMO.                                   (* [comment removed for export] *)
  step.                                             (* [comment removed for export] *)
  do 4 zstep.                                       (* [comment removed for export] *)
  step. step. if_lit.                               (* [comment removed for export] *)
  do 8 step.                                        (* [comment removed for export] *)
  release_frame FR ST (bv_unsigned sp). subst R.
  setreg 10 (Z_to_bv 64 (spacebeg + c * 2^32 + 16 * bv_unsigned idxw))
    ltac:(apply Z_to_bv_eqm; rewrite ?Z.shiftl_mul_pow2 by lia; zeq).
  finish. eexists. exact STS.
Qed.
End CANSEC1.
