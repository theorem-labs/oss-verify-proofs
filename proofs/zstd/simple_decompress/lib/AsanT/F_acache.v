(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Lib Require Import ITree Nodes Decode Arr.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Spec Require Import STree AsanCtrl.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.AsanT Require Import BImg AProto ABase.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.LibA Require Import StepF.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.AsanT Require Import AKit.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import RunDraw.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
(* [comment removed for export] *)
Local Ltac band_lin :=      (* [comment removed for export] *)
  repeat match goal with H : iclr ?a ?n |- _ => unfold iclr, AIMG_LO, AIMG_HI in H end.
Local Ltac with_band H tac :=
  let H' := fresh H in pose proof H as H'; unfold sclr, iclr, ablk, KLS, AIMG_LO, AIMG_HI in H'; tac; try clear H'.


Section CANSEC1. Context {rc : runConstT}.
Definition combined_alloc_entry := 0x37f9c%Z.

(* [comment removed for export] *)
(* [comment removed for export] *)
End CANSEC1.
Notation acache_rec t c := (t + 208 + c * 80) (only parsing).
Notation acache_stats t := (t + 2784) (only parsing).     (* [comment removed for export] *)

Section CANSEC2. Context {rc : runConstT}.
Definition cache_hit_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (t c cnt idx spacebeg lo : Z) (maxc csz : word) (m : amem) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (spacebeg + c * 2^32 + 16 * idx)) a1 a2 a3 a4 a5 a6 a7
                  s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom bsegs)
    /\ munch [(bv_unsigned sp - 48, bv_unsigned sp); (acache_rec t c, acache_rec t c + 4); (acache_stats t, acache_stats t + 8)]%Z m m'
    /\ wmono bsegs m m' /\ mem_inv bsegs m'
    /\ stk bsegs m' lo (bv_unsigned sp)
    /\ rw_cells bsegs m' (acache_rec t c) [C4 (Z_to_bv 64 (cnt - 1)); C4 maxc; C8 csz]
    /\ (exists stj' : word, rw_cells bsegs m' (acache_stats t) [C8 stj']).

Lemma combined_alloc_hit_spec : forall RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : amem) (t size c cnt spacebeg lo : Z) (maxc csz stj : word) (chunks : list word) (idxw : word),
  stk bsegs m lo (bv_unsigned sp) -> ATOP <= lo -> lo <= bv_unsigned sp - 48 ->
  mem_inv bsegs m ->
  a0 = Z_to_bv 64 AINSTANCE -> a1 = Z_to_bv 64 (t + 208) -> a2 = Z_to_bv 64 size -> a3 = Z_to_bv 64 8 ->
  16 <= size <= 512 -> Z.shiftr (size + 31) 5 = c ->
  rw_cells bsegs m 0xcc6b8 [C8 (Z_to_bv 64 spacebeg)] ->      (* [comment removed for export] *)
  rw_cells bsegs m (acache_rec t c) [C4 (Z_to_bv 64 cnt); C4 maxc; C8 csz] ->
  u32arr bsegs m (acache_rec t c + 16) chunks -> length chunks = 16%nat ->
  0 < cnt <= 16 -> nth_error chunks (Z.to_nat (cnt - 1)) = Some idxw -> bv_unsigned idxw < 2^32 ->
  rw_cells bsegs m (acache_stats t) [C8 stj] ->
  iclr t 4096 -> t + 4096 <= ATOP -> t mod 4096 = 0 -> 0 <= spacebeg < 2^47 ->
  rng_aimg RNG -> rng RNG lo (bv_unsigned sp - lo) -> rng RNG t 4096 ->
  evtF bsegs RNG (cache_hit_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc t c cnt (bv_unsigned idxw) spacebeg lo maxc csz m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x37f9c) fc None m (seg_rom bsegs)).
Proof.
  intros until idxw. intros ST CEIL LO MI -> -> -> -> SZ HC SB CR CH LCH CNT NTH IXS STS T0 T1 TAL SBR RIMG RSTK RT. band_lin.   (* [comment removed for export] *)
  unfold AIMG_HI, AINSTANCE in *.
  assert (C1 : 1 <= c <= 16) by (rewrite <- HC; rewrite Z.shiftr_div_pow2 by lia; Z.div_mod_to_equations; lia).
  word_range sp SPR. word_range idxw IXR.
  pose proof (munch_refl [(bv_unsigned sp - 48, bv_unsigned sp); (t + 208 + c * 80, t + 208 + c * 80 + 4); (t + 2784, t + 2784 + 8)]%Z m) as MU.
  pose proof (wmono_refl bsegs m) as WM.
  carve_frame 48%nat ST.
  do 7 step.                                        (* [comment removed for export] *)
  do 3 zstep.                                       (* [comment removed for export] *)
  replace (size <? 1) with false by (symmetry; apply Z.ltb_ge; lia). cbn [Z.b2z]. rewrite Z.add_0_r.
  rewrite (Z.mod_small size) by lia. rewrite zb_lxor_ones by lia.
  step. if_cases K0; zify_cond K0; [| exfalso; lia].  (* [comment removed for export] *)
  do 2 step. step. if_lit.                          (* [comment removed for export] *)
  step. step. if_lit.                               (* [comment removed for export] *)
  step. if_cases K1; zify_cond K1. { exfalso. lia. }   (* [comment removed for export] *)
  step. step. if_cases K2; zify_cond K2. { exfalso. lia. }   (* [comment removed for export] *)
  do 2 zstep. rewrite HC.                           (* [comment removed for export] *)
  step.                                             (* [comment removed for export] *)
  step. if_cases K3; zify_cond K3. { exfalso. lia. }   (* [comment removed for export] *)
  step. step. if_cases K4; zify_cond K4. { exfalso. lia. }   (* [comment removed for export] *)
  step. zstep. zstep.                               (* [comment removed for export] *)
  (* [comment removed for export] *)
  assert (RB : t + 208 + 80 <= t + 208 + c * 80 /\ t + 208 + c * 80 + 80 <= t + 1568) by lia.
  remember (t + 208 + c * 80) as R eqn:HR.
  lstep.                                            (* [comment removed for export] *)
  step. if_cases K5; zify_cond K5. { exfalso. lia. }   (* [comment removed for export] *)
  do 3 zstep.                                       (* [comment removed for export] *)
  step.                                             (* [comment removed for export] *)
  zstep. step. zstep. zstep.                        (* [comment removed for export] *)
  replace (Z.shiftr (Z.shiftl (cnt + -1) 32 mod 18446744073709551616) 30) with (4 * (cnt + -1))
    by (rewrite Z.shiftl_mul_pow2, Z.shiftr_div_pow2 by lia; rewrite Z.mod_small by lia; change (2^32) with (4 * 2^30); rewrite Z.mul_assoc, Z.div_mul by lia; lia).
  pose proof (u32arr_read bsegs _ _ chunks (cnt + -1) idxw (wa (R + 16 + 4 * (cnt + -1))) CH ltac:(replace (cnt + -1) with (cnt - 1) by lia; exact NTH) ltac:(lia) ltac:(f_equal; lia)) as RD.
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
End CANSEC2.
