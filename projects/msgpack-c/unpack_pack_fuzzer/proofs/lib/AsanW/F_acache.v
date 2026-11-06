(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib Require ITree Nodes Decode Arr.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec Require STree AsanCtrl.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW Require AImg AProto ABase.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALibA Require StepF.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW Require AKit.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Common Require RunDraw.
Module F_acache.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase. Import LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics. Import LinuxProcessSemantics.LinuxProcessSem.MemImageType. Import LinuxProcessSemantics.LinuxProcessSem.State. Import LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude. Import LinuxProcessSemantics.Riscv.Instr. Import LinuxProcessSemantics.Riscv.Decode. Import LinuxProcessSemantics.Riscv.DecodeC. Import LinuxProcessSemantics.Riscv.Sem. Import LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.ITree. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Nodes. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Decode. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Arr.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec.STree. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec.AsanCtrl.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AImg. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AProto. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.ABase.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALibA.StepF.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AKit.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Common.RunDraw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Local Ltac band_lin :=
  repeat match goal with H : iclr ?a ?n |- _ => unfold iclr, AIMG_LO, AIMG_HI in H end.
Local Ltac with_band H tac :=
  let H' := fresh H in pose proof H as H'; unfold sclr, iclr, ablk, KLS, AIMG_LO, AIMG_HI in H'; tac; try clear H'.

Section CANSEC1. Context {rc : runConstT}.
Definition combined_alloc_entry := 0x41420%Z.

End CANSEC1.
Notation acache_rec t c := (t + 208 + c * 80) (only parsing).
Notation acache_stats t := (t + 2784) (only parsing).

Section CANSEC2. Context {rc : runConstT}.
Definition cache_hit_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (t c cnt idx spacebeg lo : Z) (maxc csz : word) (m : amem) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (spacebeg + c * 2^32 + 16 * idx)) a1 a2 a3 a4 a5 a6 a7
                  s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom asegs)
    /\ munch [(bv_unsigned sp - 48, bv_unsigned sp); (acache_rec t c, acache_rec t c + 4); (acache_stats t, acache_stats t + 8)]%Z m m'
    /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ stk asegs m' lo (bv_unsigned sp)
    /\ rw_cells asegs m' (acache_rec t c) [C4 (Z_to_bv 64 (cnt - 1)); C4 maxc; C8 csz]
    /\ (exists stj' : word, rw_cells asegs m' (acache_stats t) [C8 stj']).

Lemma combined_alloc_hit_spec : forall RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : amem) (t size c cnt spacebeg lo : Z) (maxc csz stj : word) (chunks : list word) (idxw : word),
  stk asegs m lo (bv_unsigned sp) -> ATOP <= lo -> lo <= bv_unsigned sp - 48 ->
  mem_inv asegs m ->
  a0 = Z_to_bv 64 AINSTANCE -> a1 = Z_to_bv 64 (t + 208) -> a2 = Z_to_bv 64 size -> a3 = Z_to_bv 64 8 ->
  16 <= size <= 512 -> Z.shiftr (size + 31) 5 = c ->
  rw_cells asegs m 0xd6478 [C8 (Z_to_bv 64 spacebeg)] ->
  rw_cells asegs m (acache_rec t c) [C4 (Z_to_bv 64 cnt); C4 maxc; C8 csz] ->
  u32arr asegs m (acache_rec t c + 16) chunks -> length chunks = 16%nat ->
  0 < cnt <= 16 -> nth_error chunks (Z.to_nat (cnt - 1)) = Some idxw -> bv_unsigned idxw < 2^32 ->
  rw_cells asegs m (acache_stats t) [C8 stj] ->
  iclr t 4096 -> t + 4096 <= ATOP -> t mod 4096 = 0 -> 0 <= spacebeg < 2^47 ->
  rng_aimg RNG -> rng RNG lo (bv_unsigned sp - lo) -> rng RNG t 4096 ->
  evtF asegs RNG (cache_hit_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc t c cnt (bv_unsigned idxw) spacebeg lo maxc csz m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x41420) fc None m (seg_rom asegs)).
Proof.
  intros until idxw. intros ST CEIL LO MI -> -> -> -> SZ HC SB CR CH LCH CNT NTH IXS STS T0 T1 TAL SBR RIMG RSTK RT. band_lin.
  unfold AIMG_HI, AINSTANCE in *.
  assert (C1 : 1 <= c <= 16) by (rewrite <- HC; rewrite Z.shiftr_div_pow2 by lia; Z.div_mod_to_equations; lia).
  word_range sp SPR. word_range idxw IXR.
  pose proof (munch_refl [(bv_unsigned sp - 48, bv_unsigned sp); (t + 208 + c * 80, t + 208 + c * 80 + 4); (t + 2784, t + 2784 + 8)]%Z m) as MU.
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
  step. if_cases K5; zify_cond K5. { exfalso. lia. }
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
End CANSEC2.
End F_acache.

Module F_acache2.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase. Import LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics. Import LinuxProcessSemantics.LinuxProcessSem.MemImageType. Import LinuxProcessSemantics.LinuxProcessSem.State. Import LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude. Import LinuxProcessSemantics.Riscv.Instr. Import LinuxProcessSemantics.Riscv.Decode. Import LinuxProcessSemantics.Riscv.DecodeC. Import LinuxProcessSemantics.Riscv.Sem. Import LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.ITree. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Nodes. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Decode. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Arr.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec.STree. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec.AsanCtrl.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AImg. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AProto. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.ABase.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALibA.StepF.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AKit. Import F_acache.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Common.RunDraw.
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
    ms' = MS (mkR (Z_to_bv 64 0x416d0) (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp t0 t1 t2
                  (Z_to_bv 64 c) (Z_to_bv 64 (acache_rec t c))
                  (Z_to_bv 64 (t + 208)) (Z_to_bv 64 (acache_rec t c)) (Z_to_bv 64 AINSTANCE) (Z_to_bv 64 c) a4 a5 a6 a7
                  (Z_to_bv 64 8) (Z_to_bv 64 (t + 208)) (Z_to_bv 64 AINSTANCE) s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (Z_to_bv 64 0x41b70) fc None m' (seg_rom asegs)
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
        F (Z_to_bv 64 0x41420) fc None m (seg_rom asegs)).
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
  rw_cells asegs m 0xd6478 [C8 (Z_to_bv 64 spacebeg)] ->
  rw_cells asegs m (acache_rec t c) [C4 (Z_to_bv 64 cnt); C4 maxc; C8 csz] ->
  u32arr asegs m (acache_rec t c + 16) chunks -> length chunks = 16%nat ->
  0 < cnt <= 16 -> nth_error chunks (Z.to_nat (cnt - 1)) = Some idxw -> bv_unsigned idxw < 2^32 ->
  rw_cells asegs m (acache_stats t) [C8 stj] ->
  iclr t 4096 -> t + 4096 <= ATOP -> t mod 4096 = 0 -> 0 <= spacebeg < 2^47 ->
  rng_aimg RNG -> rng RNG lo (bv_unsigned sp - lo) -> rng RNG t 4096 ->
  evtF asegs RNG (cache_hit_post rav sp gp tp s0v s1v s2v s3v s4v s5 s6 s7 s8 s9 s10 s11 F fc t c cnt (bv_unsigned idxw) spacebeg lo maxc csz m)
    (MS (mkR (Z_to_bv 64 0x416d0) (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp t0 t1 t2
             (Z_to_bv 64 c) (Z_to_bv 64 (acache_rec t c))
             rv a1 a2 a3 a4 a5 a6 a7
             (Z_to_bv 64 8) (Z_to_bv 64 (t + 208)) (Z_to_bv 64 AINSTANCE) s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x416d0) fc None m (seg_rom asegs)).
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
End F_acache2.

From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW Require AModelFacts APrimFacts.
Module F_acache3.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase. Import LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics. Import LinuxProcessSemantics.LinuxProcessSem.MemImageType. Import LinuxProcessSemantics.LinuxProcessSem.State. Import LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude. Import LinuxProcessSemantics.Riscv.Instr. Import LinuxProcessSemantics.Riscv.Decode. Import LinuxProcessSemantics.Riscv.DecodeC. Import LinuxProcessSemantics.Riscv.Sem. Import LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.ITree. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Nodes. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Decode. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Arr.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec.STree. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec.AsanCtrl.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AImg. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AProto. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.ABase.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALibA.StepF.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AKit. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AModelFacts. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.APrimFacts. Import F_acache. Import F_acache2.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Common.RunDraw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Notation acache_rec t c := (t + 208 + c * 80) (only parsing).
Notation acache_stats t := (t + 2784) (only parsing).

Section CANSEC1. Context {rc : runConstT}.
Definition cb_sm (s : Z) : Z :=
  let x1 := Z.lor s (Z.shiftr s 1) in let x2 := Z.lor x1 (Z.shiftr x1 2) in let x3 := Z.lor x2 (Z.shiftr x2 4) in
  let x4 := Z.lor x3 (Z.shiftr x3 8) in let x5 := Z.lor x4 (Z.shiftr x4 16) in let x6 := Z.lor x5 (Z.shiftr x5 32) in
  Z.lxor x6 18446744073709551615.
End CANSEC1.
Arguments cb_sm : simpl never.
Section CANSEC2. Context {rc : runConstT}.
Definition cb_clz (y : Z) : Z :=
  let a := (y - Z.land (Z.shiftr y 1) 6148914691236517205) mod 18446744073709551616 in
  let b := Z.land a 3689348814741910323 + Z.land (Z.shiftr a 2) 3689348814741910323 in
  Z.shiftr ((Z.land ((b + Z.shiftr (b mod 18446744073709551616) 4) mod 18446744073709551616) 1085102592571150095
             * 72340172838076673) mod 18446744073709551616) 56.
End CANSEC2.
Arguments cb_clz : simpl never.
Section CANSEC3. Context {rc : runConstT}.
Definition cb_fin (s : Z) : Z :=
  let k := cb_clz (cb_sm s) in let sh := (bv_swrap 32 (62 - k)) mod 18446744073709551616 in
  Z.lor (Z.lxor ((Z.shiftl k 1) mod 18446744073709551616) 126) (Z.land (Z.shiftr s (sh mod 64)) 1)
  + Z.b2z (0 <? Z.land s (Z.lxor ((bv_swrap 32 (Z.shiftl 18446744073709551615 (sh mod 32))) mod 18446744073709551616) 18446744073709551615))
  + -2.
End CANSEC3.
Arguments cb_fin : simpl never.
Section CANSEC4. Context {rc : runConstT}.

Definition Rw (s x w : Z) : Prop :=
  forall n, 0 <= n -> (Z.testbit x n = true <-> exists i, 0 <= i < w /\ Z.testbit s (n + i) = true).

Lemma Rw_base : forall s, Rw s s 1.
Proof.
  intros s n Hn. split.
  - intros H. exists 0. split; [lia|]. rewrite Z.add_0_r. exact H.
  - intros (i & Hi & H). replace (n + i) with n in H by lia. exact H.
Qed.

Lemma Rw_step : forall s x w, 0 <= w -> Rw s x w -> Rw s (Z.lor x (Z.shiftr x w)) (2 * w).
Proof.
  intros s x w Hw R n Hn. rewrite Z.lor_spec, Z.shiftr_spec by lia. split.
  - intros H. apply Bool.orb_true_iff in H as [H|H].
    + apply (R n Hn) in H as (i & Hi & H). exists i. split; [lia| exact H].
    + apply (R (n + w) ltac:(lia)) in H as (i & Hi & H). exists (w + i). split; [lia|]. replace (n + (w + i)) with (n + w + i) by lia. exact H.
  - intros (i & Hi & H). apply Bool.orb_true_iff.
    destruct (Z_lt_le_dec i w) as [L|L].
    + left. apply (R n Hn). exists i. split; [lia| exact H].
    + right. apply (R (n + w) ltac:(lia)). exists (i - w). split; [lia|]. replace (n + w + (i - w)) with (n + i) by lia. exact H.
Qed.

Lemma cb_sm_bits : forall s, 0 < s < 2^64 -> cb_sm s = 2^64 - 2^(Z.log2 s + 1).
Proof.
  intros s Hs. set (p := Z.log2 s).
  assert (P0 : 0 <= p) by (subst p; apply Z.log2_nonneg).
  assert (P63 : p <= 63). { subst p. apply Z.lt_succ_r. change (Z.succ 63) with 64. apply Z.log2_lt_pow2; lia. }
  unfold cb_sm. cbv zeta.
  set (x1 := Z.lor s (Z.shiftr s 1)). set (x2 := Z.lor x1 (Z.shiftr x1 2)). set (x3 := Z.lor x2 (Z.shiftr x2 4)).
  set (x4 := Z.lor x3 (Z.shiftr x3 8)). set (x5 := Z.lor x4 (Z.shiftr x4 16)). set (x6 := Z.lor x5 (Z.shiftr x5 32)).
  assert (R6 : Rw s x6 64).
  { change 64 with (2 * 32). apply Rw_step; [lia|]. change 32 with (2 * 16). apply Rw_step; [lia|].
    change 16 with (2 * 8). apply Rw_step; [lia|]. change 8 with (2 * 4). apply Rw_step; [lia|].
    change 4 with (2 * 2). apply Rw_step; [lia|]. change 2 with (2 * 1). apply Rw_step; [lia|]. apply Rw_base. }
  assert (T : 2^64 - 2^(p + 1) = Z.shiftl (Z.ones (63 - p)) (p + 1)).
  { rewrite Z.shiftl_mul_pow2 by lia. unfold Z.ones. rewrite Z.shiftl_1_l, <- Z.sub_1_r.
    rewrite Z.mul_sub_distr_r, <- Z.pow_add_r by lia. replace (63 - p + (p + 1)) with 64 by lia. lia. }
  rewrite T. apply Z.bits_inj'. intros n Hn.
  rewrite Z.lxor_spec. change 18446744073709551615 with (Z.ones 64). rewrite Z.testbit_ones by lia.
  destruct (Z_lt_le_dec n (p + 1)) as [L|L].
  - rewrite Z.shiftl_spec_low by lia.
    assert (X : Z.testbit x6 n = true).
    { apply (R6 n Hn). exists (p - n). split; [lia|]. replace (n + (p - n)) with p by lia. subst p. apply Z.bit_log2. lia. }
    rewrite X. cbn [xorb]. apply Bool.negb_false_iff. apply Bool.andb_true_iff. split; [apply Z.leb_le; lia| apply Z.ltb_lt; lia].
  - rewrite Z.shiftl_spec_high by lia. rewrite Z.testbit_ones by lia.
    assert (X : Z.testbit x6 n = false).
    { destruct (Z.testbit x6 n) eqn:E; [|reflexivity]. exfalso. apply (R6 n Hn) in E as (i & Hi & E).
      rewrite Z.bits_above_log2 in E; [discriminate E| lia| subst p; lia]. }
    rewrite X. cbn [xorb].
    destruct (Z.ltb_spec n 64); destruct (Z.leb_spec 0 (n - (p + 1))); destruct (Z.ltb_spec (n - (p + 1)) (63 - p)); cbn; try reflexivity; lia.
Qed.

Definition clz_okv (p : Z) : bool := cb_clz (2^64 - 2^(p + 1)) =? 63 - p.
Lemma clz_okv_all : forallb_range clz_okv 0 (Z.to_nat (63 - 0 + 1)) = true.
Proof. vm_compute. reflexivity. Qed.
Local Opaque cb_sm cb_clz.
Lemma clz_okv_sound : forall p, clz_okv p = true -> cb_clz (2^64 - 2^(p + 1)) = 63 - p.
Proof. intros p H. unfold clz_okv in H. apply Z.eqb_eq in H. exact H. Qed.
Lemma cb_clz_smear : forall p, 0 <= p <= 63 -> cb_clz (2^64 - 2^(p + 1)) = 63 - p.
Proof. exact (range_by_compute (fun p => cb_clz (2^64 - 2^(p + 1)) = 63 - p) clz_okv 0 63 clz_okv_sound clz_okv_all). Qed.

Lemma cb_clz_sm : forall s, 0 < s < 2^64 -> cb_sm s = 2^64 - 2^(Z.log2 s + 1) /\ cb_clz (cb_sm s) = 63 - Z.log2 s.
Proof.
  intros s Hs. pose proof (Z.log2_nonneg s) as P0.
  assert (P63 : Z.log2 s <= 63). { apply Z.lt_succ_r. change (Z.succ 63) with 64. apply Z.log2_lt_pow2; lia. }
  rewrite (cb_sm_bits s Hs). split; [reflexivity| exact (cb_clz_smear (Z.log2 s) ltac:(lia))].
Qed.
Lemma cb_sm_range : forall s, 513 <= s <= 65536 -> s mod 8 = 0 -> 0 <= cb_sm s < 2^64 /\ 47 <= cb_clz (cb_sm s) <= 54.
Proof.
  intros s Hs _. destruct (cb_clz_sm s ltac:(lia)) as [E1 E2]. rewrite E2, E1.
  assert (P9 : 9 <= Z.log2 s). { change 9 with (Z.log2 513). apply Z.log2_le_mono. lia. }
  assert (P16 : Z.log2 s <= 16). { apply Z.lt_succ_r. change (Z.succ 16) with 17. apply Z.log2_lt_pow2; lia. }
  assert (B : 2^10 <= 2^(Z.log2 s + 1) <= 2^17) by (split; apply Z.pow_le_mono_r; lia). lia.
Qed.
Local Transparent cb_sm cb_clz.

Definition cbf (l s : Z) : Z :=
  let k := 63 - l in let sh := (bv_swrap 32 (62 - k)) mod 18446744073709551616 in
  Z.lor (Z.lxor ((Z.shiftl k 1) mod 18446744073709551616) 126) (Z.land (Z.shiftr s (sh mod 64)) 1)
  + Z.b2z (0 <? Z.land s (Z.lxor ((bv_swrap 32 (Z.shiftl 18446744073709551615 (sh mod 32))) mod 18446744073709551616) 18446744073709551615))
  + -2.
Lemma cb_fin_cbf : forall s, 0 < s < 2^64 -> cb_fin s = cbf (Z.log2 s) s.
Proof. intros s Hs. unfold cb_fin, cbf. destruct (cb_clz_sm s Hs) as [_ ->]. replace (63 - (63 - Z.log2 s)) with (Z.log2 s) by lia. reflexivity. Qed.

Definition cbf_ok (l : Z) : bool :=
  let k := 63 - l in let sh := (bv_swrap 32 (62 - k)) mod 18446744073709551616 in
  (sh =? l - 1) && (Z.lxor ((Z.shiftl k 1) mod 18446744073709551616) 126 =? 2 * l)
  && (Z.lxor ((bv_swrap 32 (Z.shiftl 18446744073709551615 (l - 1))) mod 18446744073709551616) 18446744073709551615 =? 2^(l - 1) - 1).
Lemma cbf_ok_all : forallb_range cbf_ok 9 (Z.to_nat (16 - 9 + 1)) = true.
Proof. vm_compute. reflexivity. Qed.
Lemma cbf_ok_sound : forall l, cbf_ok l = true ->
  (bv_swrap 32 (62 - (63 - l))) mod 18446744073709551616 = l - 1
  /\ Z.lxor ((Z.shiftl (63 - l) 1) mod 18446744073709551616) 126 = 2 * l
  /\ Z.lxor ((bv_swrap 32 (Z.shiftl 18446744073709551615 (l - 1))) mod 18446744073709551616) 18446744073709551615 = 2^(l - 1) - 1.
Proof.
  intros l H. unfold cbf_ok in H. cbv zeta in H. apply andb_prop in H as [H E3]. apply andb_prop in H as [E1 E2].
  apply Z.eqb_eq in E1. apply Z.eqb_eq in E2. apply Z.eqb_eq in E3. repeat split; assumption.
Qed.
Lemma cbf_consts : forall l, 9 <= l <= 16 ->
  (bv_swrap 32 (62 - (63 - l))) mod 18446744073709551616 = l - 1
  /\ Z.lxor ((Z.shiftl (63 - l) 1) mod 18446744073709551616) 126 = 2 * l
  /\ Z.lxor ((bv_swrap 32 (Z.shiftl 18446744073709551615 (l - 1))) mod 18446744073709551616) 18446744073709551615 = 2^(l - 1) - 1.
Proof. exact (range_by_compute _ cbf_ok 9 16 cbf_ok_sound cbf_ok_all). Qed.
Lemma land_1 : forall x, Z.land x 1 = x mod 2.
Proof. intros x. exact (Z.land_ones x 1 ltac:(lia)). Qed.
Lemma cbf_class_id : forall l s, 9 <= l <= 16 -> 512 < s -> Z.log2 s = l -> cbf l s = class_id s.
Proof.
  intros l s Hl Hs HL. destruct (cbf_consts l Hl) as (E1 & E2 & E3).
  unfold cbf. cbv zeta. rewrite E1. rewrite (Z.mod_small (l - 1) 64) by lia. rewrite (Z.mod_small (l - 1) 32) by lia. rewrite E2, E3.
  unfold class_id. replace (s <=? 512) with false by (symmetry; apply Z.leb_gt; lia). cbv zeta. rewrite HL.
  rewrite Z.shiftl_1_l. rewrite (Z.shiftl_mul_pow2 (l - 9) 1) by lia.
  set (hb := Z.land (Z.shiftr s (l - 1)) 1). set (lb := Z.land s (2^(l - 1) - 1)).
  assert (HB : 0 <= hb <= 1).
  { subst hb. rewrite land_1. pose proof (Z.mod_pos_bound (Z.shiftr s (l - 1)) 2 ltac:(lia)). lia. }
  assert (LB : 0 <= lb) by (subst lb; apply Z.land_nonneg; left; lia).
  assert (LOR : Z.lor (2 * l) hb = 2 * l + hb).
  { assert (D : Z.land (2 * l) hb = 0).
    { assert (C : hb = 0 \/ hb = 1) by lia. destruct C as [-> | ->]; [apply Z.land_0_r|].
      rewrite land_1. rewrite Z.mul_comm. apply Z_mod_mult. }
    rewrite <- Z.lxor_lor by exact D. symmetry. apply Z.add_nocarry_lxor. exact D. }
  rewrite LOR. destruct (Z.eqb_spec lb 0) as [E|E]; destruct (Z.ltb_spec 0 lb); cbn [Z.b2z]; lia.
Qed.
Lemma cb_fin_class_id : forall z, 513 <= z <= 65536 -> z mod 8 = 0 -> Z_to_bv 64 (cb_fin z) = Z_to_bv 64 (class_id z).
Proof.
  intros z Hz _. f_equal. rewrite cb_fin_cbf by lia.
  assert (P9 : 9 <= Z.log2 z). { change 9 with (Z.log2 513). apply Z.log2_le_mono. lia. }
  assert (P16 : Z.log2 z <= 16). { apply Z.lt_succ_r. change (Z.succ 16) with 17. apply Z.log2_lt_pow2; lia. }
  apply cbf_class_id; lia.
Qed.

Lemma classblock_spec : forall RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : amem) (size : Z),
  513 <= size <= 65536 -> size mod 8 = 0 ->
  rng_aimg RNG ->
  evtF asegs RNG (fun ms' => exists a2' a4' a5' a6' a7' t0' t1',
      ms' = MS (mkR ra sp gp tp t0' t1' t2 (Z_to_bv 64 (class_id size)) s1 a0 a1 a2' a3 a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (Z_to_bv 64 0x415b4) fc None m (seg_rom asegs))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 (Z_to_bv 64 size) a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x414d8) fc None m (seg_rom asegs)).
Proof.
  intros until size. intros SZ M8 RIMG. pose proof (cb_sm_range size SZ M8) as [CBR CLZ].
  do 29 zstep. setreg 12 (Z_to_bv 64 (cb_sm size)) ltac:(reflexivity).
  do 14 zstep. setreg 12 (Z_to_bv 64 (cb_clz (cb_sm size))) ltac:(reflexivity).
  do 12 zstep. setreg 8 (Z_to_bv 64 (cb_fin size)) ltac:(reflexivity).
  setreg 8 (Z_to_bv 64 (class_id size))
    ltac:(symmetry; exact (cb_fin_class_id size SZ M8)).
  apply evtF_done. do 7 eexists. reflexivity.
Qed.
End CANSEC4.
End F_acache3.

Module F_acache4.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase. Import LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics. Import LinuxProcessSemantics.LinuxProcessSem.MemImageType. Import LinuxProcessSemantics.LinuxProcessSem.State. Import LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude. Import LinuxProcessSemantics.Riscv.Instr. Import LinuxProcessSemantics.Riscv.Decode. Import LinuxProcessSemantics.Riscv.DecodeC. Import LinuxProcessSemantics.Riscv.Sem. Import LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.ITree. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Nodes. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Decode. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Arr.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec.STree. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec.AsanCtrl.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AImg. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AProto. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.ABase.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALibA.StepF.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AKit. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AModelFacts. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.APrimFacts. Import F_acache. Import F_acache2. Import F_acache3.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Common.RunDraw.
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
Lemma calloc_hit_gen : forall RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : amem) (t size c cnt spacebeg lo : Z) (maxc csz stj : word) (chunks : list word) (idxw : word),
  stk asegs m lo (bv_unsigned sp) -> ATOP <= lo -> lo <= bv_unsigned sp - 48 ->
  mem_inv asegs m ->
  a0 = Z_to_bv 64 AINSTANCE -> a1 = Z_to_bv 64 (t + 208) -> a2 = Z_to_bv 64 size -> a3 = Z_to_bv 64 8 ->
  16 <= size <= 65536 -> size mod 8 = 0 -> class_id size = c ->
  rw_cells asegs m 0xd6478 [C8 (Z_to_bv 64 spacebeg)] ->
  rw_cells asegs m (acache_rec t c) [C4 (Z_to_bv 64 cnt); C4 maxc; C8 csz] ->
  u32arr asegs m (acache_rec t c + 16) chunks -> length chunks = 16%nat ->
  0 < cnt <= 16 -> nth_error chunks (Z.to_nat (cnt - 1)) = Some idxw -> bv_unsigned idxw < 2^32 ->
  rw_cells asegs m (acache_stats t) [C8 stj] ->
  iclr t 4096 -> t + 4096 <= ATOP -> t mod 4096 = 0 -> 0 <= spacebeg < 2^47 ->
  rng_aimg RNG -> rng RNG lo (bv_unsigned sp - lo) -> rng RNG t 4096 ->
  evtF asegs RNG (cache_hit_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc t c cnt (bv_unsigned idxw) spacebeg lo maxc csz m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x41420) fc None m (seg_rom asegs)).
Proof.
  intros until idxw. intros ST CEIL LO MI -> -> -> -> SZ M8 HC SB CR CH LCH CNT NTH IXS STS T0 T1 TAL SBR RIMG RSTK RT. band_lin.
  unfold AIMG_HI, AINSTANCE in *.
  pose proof (class_facts size ltac:(lia)) as CF. cbv zeta in CF. rewrite HC in CF. destruct CF as (C1 & CS1 & CS2 & CS3 & CSM & CBG).
  word_range sp SPR. word_range idxw IXR.
  pose proof (munch_refl [(bv_unsigned sp - 48, bv_unsigned sp); (t + 208 + c * 80, t + 208 + c * 80 + 4); (t + 2784, t + 2784 + 8)]%Z m) as MU.
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
  step. step. if_cases K2; zify_cond K2.

  1: eapply evtF_cut; [eapply (classblock_spec RNG); [lia | assumption | exact RIMG] |].
  1: cbv beta; intros msB PB; destruct PB as (a2b & a4b & a5b & a6b & a7b & t0b & t1b & ->); rewrite HC.
  2: do 2 zstep; rewrite <- (CSM ltac:(lia)); step.

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
        F (Z_to_bv 64 0x41420) fc None m (seg_rom asegs)).
Proof.
  intros until csz. intros ST CEIL LO MI -> -> -> -> SZ M8 HC CR T0 T1 RIMG RSTK RT. band_lin.
  unfold AIMG_HI, AINSTANCE in *.
  pose proof (class_facts size ltac:(lia)) as CF. cbv zeta in CF. rewrite HC in CF. destruct CF as (C1 & CS1 & CS2 & CS3 & CSM & CBG).
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
  step. step. if_cases K2; zify_cond K2.

  1: eapply evtF_cut; [eapply (classblock_spec RNG); [lia | assumption | exact RIMG] |].
  1: cbv beta; intros msB PB; destruct PB as (a2b & a4b & a5b & a6b & a7b & t0b & t1b & ->); rewrite HC.
  2: do 2 zstep; rewrite <- (CSM ltac:(lia)); step.

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
  rw_cells asegs m 0xd6478 [C8 (Z_to_bv 64 spacebeg)] ->
  rw_cells asegs m (acache_rec t c) [C4 (Z_to_bv 64 cnt); C4 maxc; C8 csz] ->
  u32arr asegs m (acache_rec t c + 16) chunks -> length chunks = 16%nat ->
  0 < cnt <= 16 -> nth_error chunks (Z.to_nat (cnt - 1)) = Some idxw -> bv_unsigned idxw < 2^32 ->
  rw_cells asegs m (acache_stats t) [C8 stj] ->
  iclr t 4096 -> t + 4096 <= ATOP -> t mod 4096 = 0 -> 0 <= spacebeg < 2^47 ->
  rng_aimg RNG -> rng RNG lo (bv_unsigned sp - lo) -> rng RNG t 4096 ->
  evtF asegs RNG (cache_hit_post rav sp gp tp s0v s1v s2v s3v s4v s5 s6 s7 s8 s9 s10 s11 F fc t c cnt (bv_unsigned idxw) spacebeg lo maxc csz m)
    (MS (mkR (Z_to_bv 64 0x416d0) (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp t0 t1 t2
             (Z_to_bv 64 c) (Z_to_bv 64 (acache_rec t c))
             rv a1 a2 a3 a4 a5 a6 a7
             (Z_to_bv 64 8) (Z_to_bv 64 (t + 208)) (Z_to_bv 64 AINSTANCE) s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x416d0) fc None m (seg_rom asegs)).
Proof.
  intros until idxw. intros ST CEIL LO MI RV C1 FR SB CR CH LCH CNT NTH IXS STS T0 T1 TAL SBR RIMG RSTK RT. band_lin.
  unfold AIMG_HI, AINSTANCE in *.
  word_range sp SPR. word_range idxw IXR. word_range rv RVR.
  pose proof (munch_refl [(bv_unsigned sp - 48, bv_unsigned sp); (t + 208 + c * 80, t + 208 + c * 80 + 4); (t + 2784, t + 2784 + 8)]%Z m) as MU.
  pose proof (wmono_refl asegs m) as WM.
  assert (RB : t + 208 + 80 <= t + 208 + c * 80 /\ t + 208 + c * 80 + 80 <= t + 2688) by lia.
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
End F_acache4.

From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.BothW Require BImg.
Module TwinB.

Module F_acache.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase. Import LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics. Import LinuxProcessSemantics.LinuxProcessSem.MemImageType. Import LinuxProcessSemantics.LinuxProcessSem.State. Import LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude. Import LinuxProcessSemantics.Riscv.Instr. Import LinuxProcessSemantics.Riscv.Decode. Import LinuxProcessSemantics.Riscv.DecodeC. Import LinuxProcessSemantics.Riscv.Sem. Import LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.ITree. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Nodes. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Decode. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Arr.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec.STree. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec.AsanCtrl.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.BothW.BImg. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AProto.TwinB. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.ABase.TwinB.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALibA.StepF.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AKit.TwinB.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Common.RunDraw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Local Ltac band_lin :=
  repeat match goal with H : iclr ?a ?n |- _ => unfold iclr, AIMG_LO, AIMG_HI in H end.
Local Ltac with_band H tac :=
  let H' := fresh H in pose proof H as H'; unfold sclr, iclr, ablk, KLS, AIMG_LO, AIMG_HI in H'; tac; try clear H'.

Section CANSEC1. Context {rc : runConstT}.
Definition combined_alloc_entry := 0x41db0%Z.

End CANSEC1.
Notation acache_rec t c := (t + 208 + c * 80) (only parsing).
Notation acache_stats t := (t + 2784) (only parsing).

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
  rw_cells bsegs m 0xd8638 [C8 (Z_to_bv 64 spacebeg)] ->
  rw_cells bsegs m (acache_rec t c) [C4 (Z_to_bv 64 cnt); C4 maxc; C8 csz] ->
  u32arr bsegs m (acache_rec t c + 16) chunks -> length chunks = 16%nat ->
  0 < cnt <= 16 -> nth_error chunks (Z.to_nat (cnt - 1)) = Some idxw -> bv_unsigned idxw < 2^32 ->
  rw_cells bsegs m (acache_stats t) [C8 stj] ->
  iclr t 4096 -> t + 4096 <= ATOP -> t mod 4096 = 0 -> 0 <= spacebeg < 2^47 ->
  rng_aimg RNG -> rng RNG lo (bv_unsigned sp - lo) -> rng RNG t 4096 ->
  evtF bsegs RNG (cache_hit_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc t c cnt (bv_unsigned idxw) spacebeg lo maxc csz m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x41db0) fc None m (seg_rom bsegs)).
Proof.
  intros until idxw. intros ST CEIL LO MI -> -> -> -> SZ HC SB CR CH LCH CNT NTH IXS STS T0 T1 TAL SBR RIMG RSTK RT. band_lin.
  unfold AIMG_HI, AINSTANCE in *.
  assert (C1 : 1 <= c <= 16) by (rewrite <- HC; rewrite Z.shiftr_div_pow2 by lia; Z.div_mod_to_equations; lia).
  word_range sp SPR. word_range idxw IXR.
  pose proof (munch_refl [(bv_unsigned sp - 48, bv_unsigned sp); (t + 208 + c * 80, t + 208 + c * 80 + 4); (t + 2784, t + 2784 + 8)]%Z m) as MU.
  pose proof (wmono_refl bsegs m) as WM.
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
  step. if_cases K5; zify_cond K5. { exfalso. lia. }
  do 3 zstep.
  step.
  zstep. step. zstep. zstep.
  replace (Z.shiftr (Z.shiftl (cnt + -1) 32 mod 18446744073709551616) 30) with (4 * (cnt + -1))
    by (rewrite Z.shiftl_mul_pow2, Z.shiftr_div_pow2 by lia; rewrite Z.mod_small by lia; change (2^32) with (4 * 2^30); rewrite Z.mul_assoc, Z.div_mul by lia; lia).
  pose proof (u32arr_read bsegs _ _ chunks (cnt + -1) idxw (wa (R + 16 + 4 * (cnt + -1))) CH ltac:(replace (cnt + -1) with (cnt - 1) by lia; exact NTH) ltac:(lia) ltac:(f_equal; lia)) as RD.
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
End CANSEC2.
End F_acache.

Module F_acache2.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase. Import LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics. Import LinuxProcessSemantics.LinuxProcessSem.MemImageType. Import LinuxProcessSemantics.LinuxProcessSem.State. Import LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude. Import LinuxProcessSemantics.Riscv.Instr. Import LinuxProcessSemantics.Riscv.Decode. Import LinuxProcessSemantics.Riscv.DecodeC. Import LinuxProcessSemantics.Riscv.Sem. Import LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.ITree. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Nodes. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Decode. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Arr.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec.STree. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec.AsanCtrl.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.BothW.BImg. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AProto.TwinB. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.ABase.TwinB.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALibA.StepF.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AKit.TwinB. Import F_acache.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Common.RunDraw.
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
    ms' = MS (mkR (Z_to_bv 64 0x42060) (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp t0 t1 t2
                  (Z_to_bv 64 c) (Z_to_bv 64 (acache_rec t c))
                  (Z_to_bv 64 (t + 208)) (Z_to_bv 64 (acache_rec t c)) (Z_to_bv 64 AINSTANCE) (Z_to_bv 64 c) a4 a5 a6 a7
                  (Z_to_bv 64 8) (Z_to_bv 64 (t + 208)) (Z_to_bv 64 AINSTANCE) s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (Z_to_bv 64 0x42500) fc None m' (seg_rom bsegs)
    /\ munch [(bv_unsigned sp - 48, bv_unsigned sp)]%Z m m' /\ wmono bsegs m m' /\ mem_inv bsegs m'
    /\ stk bsegs m' lo (bv_unsigned sp - 48)
    /\ rw_cells bsegs m' (bv_unsigned sp + -48) [C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].

Lemma calloc_pre_spec : forall RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : amem) (t size c lo : Z) (maxc csz : word),
  stk bsegs m lo (bv_unsigned sp) -> ATOP <= lo -> lo <= bv_unsigned sp - 48 ->
  mem_inv bsegs m ->
  a0 = Z_to_bv 64 AINSTANCE -> a1 = Z_to_bv 64 (t + 208) -> a2 = Z_to_bv 64 size -> a3 = Z_to_bv 64 8 ->
  16 <= size <= 512 -> Z.shiftr (size + 31) 5 = c ->
  rw_cells bsegs m (acache_rec t c) [C4 (Z_to_bv 64 0); C4 maxc; C8 csz] ->
  iclr t 4096 -> t + 4096 <= ATOP ->
  rng_aimg RNG -> rng RNG lo (bv_unsigned sp - lo) -> rng RNG t 4096 ->
  evtF bsegs RNG (calloc_pre_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc t c lo m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x41db0) fc None m (seg_rom bsegs)).
Proof.
  intros until csz. intros ST CEIL LO MI -> -> -> -> SZ HC CR T0 T1 RIMG RSTK RT. band_lin.
  unfold AIMG_HI, AINSTANCE in *.
  assert (C1 : 1 <= c <= 16) by (rewrite <- HC; rewrite Z.shiftr_div_pow2 by lia; Z.div_mod_to_equations; lia).
  word_range sp SPR.
  pose proof (munch_refl [(bv_unsigned sp - 48, bv_unsigned sp)]%Z m) as MU.
  pose proof (wmono_refl bsegs m) as WM.
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
  stk bsegs m lo (bv_unsigned sp - 48) -> ATOP <= lo -> lo <= bv_unsigned sp - 48 ->
  mem_inv bsegs m ->
  bv_unsigned rv <> 0 ->
  1 <= c <= 16 ->
  rw_cells bsegs m (bv_unsigned sp + -48) [C8 s4v; C8 s3v; C8 s2v; C8 s1v; C8 s0v; C8 rav] ->
  rw_cells bsegs m 0xd8638 [C8 (Z_to_bv 64 spacebeg)] ->
  rw_cells bsegs m (acache_rec t c) [C4 (Z_to_bv 64 cnt); C4 maxc; C8 csz] ->
  u32arr bsegs m (acache_rec t c + 16) chunks -> length chunks = 16%nat ->
  0 < cnt <= 16 -> nth_error chunks (Z.to_nat (cnt - 1)) = Some idxw -> bv_unsigned idxw < 2^32 ->
  rw_cells bsegs m (acache_stats t) [C8 stj] ->
  iclr t 4096 -> t + 4096 <= ATOP -> t mod 4096 = 0 -> 0 <= spacebeg < 2^47 ->
  rng_aimg RNG -> rng RNG lo (bv_unsigned sp - lo) -> rng RNG t 4096 ->
  evtF bsegs RNG (cache_hit_post rav sp gp tp s0v s1v s2v s3v s4v s5 s6 s7 s8 s9 s10 s11 F fc t c cnt (bv_unsigned idxw) spacebeg lo maxc csz m)
    (MS (mkR (Z_to_bv 64 0x42060) (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp t0 t1 t2
             (Z_to_bv 64 c) (Z_to_bv 64 (acache_rec t c))
             rv a1 a2 a3 a4 a5 a6 a7
             (Z_to_bv 64 8) (Z_to_bv 64 (t + 208)) (Z_to_bv 64 AINSTANCE) s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x42060) fc None m (seg_rom bsegs)).
Proof.
  intros until idxw. intros ST CEIL LO MI RV C1 FR SB CR CH LCH CNT NTH IXS STS T0 T1 TAL SBR RIMG RSTK RT. band_lin.
  unfold AIMG_HI, AINSTANCE in *.
  word_range sp SPR. word_range idxw IXR. word_range rv RVR.
  pose proof (munch_refl [(bv_unsigned sp - 48, bv_unsigned sp); (t + 208 + c * 80, t + 208 + c * 80 + 4); (t + 2784, t + 2784 + 8)]%Z m) as MU.
  pose proof (wmono_refl bsegs m) as WM.
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
  pose proof (u32arr_read bsegs _ _ chunks (cnt + -1) idxw (wa (R + 16 + 4 * (cnt + -1))) CH ltac:(replace (cnt + -1) with (cnt - 1) by lia; exact NTH) ltac:(lia) ltac:(f_equal; lia)) as RD.
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
End F_acache2.

Module F_acache3.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase. Import LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics. Import LinuxProcessSemantics.LinuxProcessSem.MemImageType. Import LinuxProcessSemantics.LinuxProcessSem.State. Import LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude. Import LinuxProcessSemantics.Riscv.Instr. Import LinuxProcessSemantics.Riscv.Decode. Import LinuxProcessSemantics.Riscv.DecodeC. Import LinuxProcessSemantics.Riscv.Sem. Import LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.ITree. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Nodes. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Decode. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Arr.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec.STree. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec.AsanCtrl.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.BothW.BImg. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AProto.TwinB. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.ABase.TwinB.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALibA.StepF.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AKit.TwinB. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AModelFacts.TwinB. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.APrimFacts.TwinB. Import F_acache. Import F_acache2.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Common.RunDraw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Notation acache_rec t c := (t + 208 + c * 80) (only parsing).
Notation acache_stats t := (t + 2784) (only parsing).

Section CANSEC1. Context {rc : runConstT}.
Definition cb_sm (s : Z) : Z :=
  let x1 := Z.lor s (Z.shiftr s 1) in let x2 := Z.lor x1 (Z.shiftr x1 2) in let x3 := Z.lor x2 (Z.shiftr x2 4) in
  let x4 := Z.lor x3 (Z.shiftr x3 8) in let x5 := Z.lor x4 (Z.shiftr x4 16) in let x6 := Z.lor x5 (Z.shiftr x5 32) in
  Z.lxor x6 18446744073709551615.
End CANSEC1.
Arguments cb_sm : simpl never.
Section CANSEC2. Context {rc : runConstT}.
Definition cb_clz (y : Z) : Z :=
  let a := (y - Z.land (Z.shiftr y 1) 6148914691236517205) mod 18446744073709551616 in
  let b := Z.land a 3689348814741910323 + Z.land (Z.shiftr a 2) 3689348814741910323 in
  Z.shiftr ((Z.land ((b + Z.shiftr (b mod 18446744073709551616) 4) mod 18446744073709551616) 1085102592571150095
             * 72340172838076673) mod 18446744073709551616) 56.
End CANSEC2.
Arguments cb_clz : simpl never.
Section CANSEC3. Context {rc : runConstT}.
Definition cb_fin (s : Z) : Z :=
  let k := cb_clz (cb_sm s) in let sh := (bv_swrap 32 (62 - k)) mod 18446744073709551616 in
  Z.lor (Z.lxor ((Z.shiftl k 1) mod 18446744073709551616) 126) (Z.land (Z.shiftr s (sh mod 64)) 1)
  + Z.b2z (0 <? Z.land s (Z.lxor ((bv_swrap 32 (Z.shiftl 18446744073709551615 (sh mod 32))) mod 18446744073709551616) 18446744073709551615))
  + -2.
End CANSEC3.
Arguments cb_fin : simpl never.
Section CANSEC4. Context {rc : runConstT}.

Definition Rw (s x w : Z) : Prop :=
  forall n, 0 <= n -> (Z.testbit x n = true <-> exists i, 0 <= i < w /\ Z.testbit s (n + i) = true).

Lemma Rw_base : forall s, Rw s s 1.
Proof.
  intros s n Hn. split.
  - intros H. exists 0. split; [lia|]. rewrite Z.add_0_r. exact H.
  - intros (i & Hi & H). replace (n + i) with n in H by lia. exact H.
Qed.

Lemma Rw_step : forall s x w, 0 <= w -> Rw s x w -> Rw s (Z.lor x (Z.shiftr x w)) (2 * w).
Proof.
  intros s x w Hw R n Hn. rewrite Z.lor_spec, Z.shiftr_spec by lia. split.
  - intros H. apply Bool.orb_true_iff in H as [H|H].
    + apply (R n Hn) in H as (i & Hi & H). exists i. split; [lia| exact H].
    + apply (R (n + w) ltac:(lia)) in H as (i & Hi & H). exists (w + i). split; [lia|]. replace (n + (w + i)) with (n + w + i) by lia. exact H.
  - intros (i & Hi & H). apply Bool.orb_true_iff.
    destruct (Z_lt_le_dec i w) as [L|L].
    + left. apply (R n Hn). exists i. split; [lia| exact H].
    + right. apply (R (n + w) ltac:(lia)). exists (i - w). split; [lia|]. replace (n + w + (i - w)) with (n + i) by lia. exact H.
Qed.

Lemma cb_sm_bits : forall s, 0 < s < 2^64 -> cb_sm s = 2^64 - 2^(Z.log2 s + 1).
Proof.
  intros s Hs. set (p := Z.log2 s).
  assert (P0 : 0 <= p) by (subst p; apply Z.log2_nonneg).
  assert (P63 : p <= 63). { subst p. apply Z.lt_succ_r. change (Z.succ 63) with 64. apply Z.log2_lt_pow2; lia. }
  unfold cb_sm. cbv zeta.
  set (x1 := Z.lor s (Z.shiftr s 1)). set (x2 := Z.lor x1 (Z.shiftr x1 2)). set (x3 := Z.lor x2 (Z.shiftr x2 4)).
  set (x4 := Z.lor x3 (Z.shiftr x3 8)). set (x5 := Z.lor x4 (Z.shiftr x4 16)). set (x6 := Z.lor x5 (Z.shiftr x5 32)).
  assert (R6 : Rw s x6 64).
  { change 64 with (2 * 32). apply Rw_step; [lia|]. change 32 with (2 * 16). apply Rw_step; [lia|].
    change 16 with (2 * 8). apply Rw_step; [lia|]. change 8 with (2 * 4). apply Rw_step; [lia|].
    change 4 with (2 * 2). apply Rw_step; [lia|]. change 2 with (2 * 1). apply Rw_step; [lia|]. apply Rw_base. }
  assert (T : 2^64 - 2^(p + 1) = Z.shiftl (Z.ones (63 - p)) (p + 1)).
  { rewrite Z.shiftl_mul_pow2 by lia. unfold Z.ones. rewrite Z.shiftl_1_l, <- Z.sub_1_r.
    rewrite Z.mul_sub_distr_r, <- Z.pow_add_r by lia. replace (63 - p + (p + 1)) with 64 by lia. lia. }
  rewrite T. apply Z.bits_inj'. intros n Hn.
  rewrite Z.lxor_spec. change 18446744073709551615 with (Z.ones 64). rewrite Z.testbit_ones by lia.
  destruct (Z_lt_le_dec n (p + 1)) as [L|L].
  - rewrite Z.shiftl_spec_low by lia.
    assert (X : Z.testbit x6 n = true).
    { apply (R6 n Hn). exists (p - n). split; [lia|]. replace (n + (p - n)) with p by lia. subst p. apply Z.bit_log2. lia. }
    rewrite X. cbn [xorb]. apply Bool.negb_false_iff. apply Bool.andb_true_iff. split; [apply Z.leb_le; lia| apply Z.ltb_lt; lia].
  - rewrite Z.shiftl_spec_high by lia. rewrite Z.testbit_ones by lia.
    assert (X : Z.testbit x6 n = false).
    { destruct (Z.testbit x6 n) eqn:E; [|reflexivity]. exfalso. apply (R6 n Hn) in E as (i & Hi & E).
      rewrite Z.bits_above_log2 in E; [discriminate E| lia| subst p; lia]. }
    rewrite X. cbn [xorb].
    destruct (Z.ltb_spec n 64); destruct (Z.leb_spec 0 (n - (p + 1))); destruct (Z.ltb_spec (n - (p + 1)) (63 - p)); cbn; try reflexivity; lia.
Qed.

Definition clz_okv (p : Z) : bool := cb_clz (2^64 - 2^(p + 1)) =? 63 - p.
Lemma clz_okv_all : forallb_range clz_okv 0 (Z.to_nat (63 - 0 + 1)) = true.
Proof. vm_compute. reflexivity. Qed.
Local Opaque cb_sm cb_clz.
Lemma clz_okv_sound : forall p, clz_okv p = true -> cb_clz (2^64 - 2^(p + 1)) = 63 - p.
Proof. intros p H. unfold clz_okv in H. apply Z.eqb_eq in H. exact H. Qed.
Lemma cb_clz_smear : forall p, 0 <= p <= 63 -> cb_clz (2^64 - 2^(p + 1)) = 63 - p.
Proof. exact (range_by_compute (fun p => cb_clz (2^64 - 2^(p + 1)) = 63 - p) clz_okv 0 63 clz_okv_sound clz_okv_all). Qed.

Lemma cb_clz_sm : forall s, 0 < s < 2^64 -> cb_sm s = 2^64 - 2^(Z.log2 s + 1) /\ cb_clz (cb_sm s) = 63 - Z.log2 s.
Proof.
  intros s Hs. pose proof (Z.log2_nonneg s) as P0.
  assert (P63 : Z.log2 s <= 63). { apply Z.lt_succ_r. change (Z.succ 63) with 64. apply Z.log2_lt_pow2; lia. }
  rewrite (cb_sm_bits s Hs). split; [reflexivity| exact (cb_clz_smear (Z.log2 s) ltac:(lia))].
Qed.
Lemma cb_sm_range : forall s, 513 <= s <= 65536 -> s mod 8 = 0 -> 0 <= cb_sm s < 2^64 /\ 47 <= cb_clz (cb_sm s) <= 54.
Proof.
  intros s Hs _. destruct (cb_clz_sm s ltac:(lia)) as [E1 E2]. rewrite E2, E1.
  assert (P9 : 9 <= Z.log2 s). { change 9 with (Z.log2 513). apply Z.log2_le_mono. lia. }
  assert (P16 : Z.log2 s <= 16). { apply Z.lt_succ_r. change (Z.succ 16) with 17. apply Z.log2_lt_pow2; lia. }
  assert (B : 2^10 <= 2^(Z.log2 s + 1) <= 2^17) by (split; apply Z.pow_le_mono_r; lia). lia.
Qed.
Local Transparent cb_sm cb_clz.

Definition cbf (l s : Z) : Z :=
  let k := 63 - l in let sh := (bv_swrap 32 (62 - k)) mod 18446744073709551616 in
  Z.lor (Z.lxor ((Z.shiftl k 1) mod 18446744073709551616) 126) (Z.land (Z.shiftr s (sh mod 64)) 1)
  + Z.b2z (0 <? Z.land s (Z.lxor ((bv_swrap 32 (Z.shiftl 18446744073709551615 (sh mod 32))) mod 18446744073709551616) 18446744073709551615))
  + -2.
Lemma cb_fin_cbf : forall s, 0 < s < 2^64 -> cb_fin s = cbf (Z.log2 s) s.
Proof. intros s Hs. unfold cb_fin, cbf. destruct (cb_clz_sm s Hs) as [_ ->]. replace (63 - (63 - Z.log2 s)) with (Z.log2 s) by lia. reflexivity. Qed.

Definition cbf_ok (l : Z) : bool :=
  let k := 63 - l in let sh := (bv_swrap 32 (62 - k)) mod 18446744073709551616 in
  (sh =? l - 1) && (Z.lxor ((Z.shiftl k 1) mod 18446744073709551616) 126 =? 2 * l)
  && (Z.lxor ((bv_swrap 32 (Z.shiftl 18446744073709551615 (l - 1))) mod 18446744073709551616) 18446744073709551615 =? 2^(l - 1) - 1).
Lemma cbf_ok_all : forallb_range cbf_ok 9 (Z.to_nat (16 - 9 + 1)) = true.
Proof. vm_compute. reflexivity. Qed.
Lemma cbf_ok_sound : forall l, cbf_ok l = true ->
  (bv_swrap 32 (62 - (63 - l))) mod 18446744073709551616 = l - 1
  /\ Z.lxor ((Z.shiftl (63 - l) 1) mod 18446744073709551616) 126 = 2 * l
  /\ Z.lxor ((bv_swrap 32 (Z.shiftl 18446744073709551615 (l - 1))) mod 18446744073709551616) 18446744073709551615 = 2^(l - 1) - 1.
Proof.
  intros l H. unfold cbf_ok in H. cbv zeta in H. apply andb_prop in H as [H E3]. apply andb_prop in H as [E1 E2].
  apply Z.eqb_eq in E1. apply Z.eqb_eq in E2. apply Z.eqb_eq in E3. repeat split; assumption.
Qed.
Lemma cbf_consts : forall l, 9 <= l <= 16 ->
  (bv_swrap 32 (62 - (63 - l))) mod 18446744073709551616 = l - 1
  /\ Z.lxor ((Z.shiftl (63 - l) 1) mod 18446744073709551616) 126 = 2 * l
  /\ Z.lxor ((bv_swrap 32 (Z.shiftl 18446744073709551615 (l - 1))) mod 18446744073709551616) 18446744073709551615 = 2^(l - 1) - 1.
Proof. exact (range_by_compute _ cbf_ok 9 16 cbf_ok_sound cbf_ok_all). Qed.
Lemma land_1 : forall x, Z.land x 1 = x mod 2.
Proof. intros x. exact (Z.land_ones x 1 ltac:(lia)). Qed.
Lemma cbf_class_id : forall l s, 9 <= l <= 16 -> 512 < s -> Z.log2 s = l -> cbf l s = class_id s.
Proof.
  intros l s Hl Hs HL. destruct (cbf_consts l Hl) as (E1 & E2 & E3).
  unfold cbf. cbv zeta. rewrite E1. rewrite (Z.mod_small (l - 1) 64) by lia. rewrite (Z.mod_small (l - 1) 32) by lia. rewrite E2, E3.
  unfold class_id. replace (s <=? 512) with false by (symmetry; apply Z.leb_gt; lia). cbv zeta. rewrite HL.
  rewrite Z.shiftl_1_l. rewrite (Z.shiftl_mul_pow2 (l - 9) 1) by lia.
  set (hb := Z.land (Z.shiftr s (l - 1)) 1). set (lb := Z.land s (2^(l - 1) - 1)).
  assert (HB : 0 <= hb <= 1).
  { subst hb. rewrite land_1. pose proof (Z.mod_pos_bound (Z.shiftr s (l - 1)) 2 ltac:(lia)). lia. }
  assert (LB : 0 <= lb) by (subst lb; apply Z.land_nonneg; left; lia).
  assert (LOR : Z.lor (2 * l) hb = 2 * l + hb).
  { assert (D : Z.land (2 * l) hb = 0).
    { assert (C : hb = 0 \/ hb = 1) by lia. destruct C as [-> | ->]; [apply Z.land_0_r|].
      rewrite land_1. rewrite Z.mul_comm. apply Z_mod_mult. }
    rewrite <- Z.lxor_lor by exact D. symmetry. apply Z.add_nocarry_lxor. exact D. }
  rewrite LOR. destruct (Z.eqb_spec lb 0) as [E|E]; destruct (Z.ltb_spec 0 lb); cbn [Z.b2z]; lia.
Qed.
Lemma cb_fin_class_id : forall z, 513 <= z <= 65536 -> z mod 8 = 0 -> Z_to_bv 64 (cb_fin z) = Z_to_bv 64 (class_id z).
Proof.
  intros z Hz _. f_equal. rewrite cb_fin_cbf by lia.
  assert (P9 : 9 <= Z.log2 z). { change 9 with (Z.log2 513). apply Z.log2_le_mono. lia. }
  assert (P16 : Z.log2 z <= 16). { apply Z.lt_succ_r. change (Z.succ 16) with 17. apply Z.log2_lt_pow2; lia. }
  apply cbf_class_id; lia.
Qed.

Lemma classblock_spec : forall RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : amem) (size : Z),
  513 <= size <= 65536 -> size mod 8 = 0 ->
  rng_aimg RNG ->
  evtF bsegs RNG (fun ms' => exists a2' a4' a5' a6' a7' t0' t1',
      ms' = MS (mkR ra sp gp tp t0' t1' t2 (Z_to_bv 64 (class_id size)) s1 a0 a1 a2' a3 a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (Z_to_bv 64 0x41f44) fc None m (seg_rom bsegs))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 (Z_to_bv 64 size) a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x41e68) fc None m (seg_rom bsegs)).
Proof.
  intros until size. intros SZ M8 RIMG. pose proof (cb_sm_range size SZ M8) as [CBR CLZ].
  do 29 zstep. setreg 12 (Z_to_bv 64 (cb_sm size)) ltac:(reflexivity).
  do 14 zstep. setreg 12 (Z_to_bv 64 (cb_clz (cb_sm size))) ltac:(reflexivity).
  do 12 zstep. setreg 8 (Z_to_bv 64 (cb_fin size)) ltac:(reflexivity).
  setreg 8 (Z_to_bv 64 (class_id size))
    ltac:(symmetry; exact (cb_fin_class_id size SZ M8)).
  apply evtF_done. do 7 eexists. reflexivity.
Qed.
End CANSEC4.
End F_acache3.

Module F_acache4.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase. Import LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics. Import LinuxProcessSemantics.LinuxProcessSem.MemImageType. Import LinuxProcessSemantics.LinuxProcessSem.State. Import LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude. Import LinuxProcessSemantics.Riscv.Instr. Import LinuxProcessSemantics.Riscv.Decode. Import LinuxProcessSemantics.Riscv.DecodeC. Import LinuxProcessSemantics.Riscv.Sem. Import LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.ITree. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Nodes. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Decode. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Arr.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec.STree. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec.AsanCtrl.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.BothW.BImg. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AProto.TwinB. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.ABase.TwinB.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALibA.StepF.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AKit.TwinB. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AModelFacts.TwinB. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.APrimFacts.TwinB. Import F_acache. Import F_acache2. Import F_acache3.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Common.RunDraw.
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
Lemma calloc_hit_gen : forall RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : amem) (t size c cnt spacebeg lo : Z) (maxc csz stj : word) (chunks : list word) (idxw : word),
  stk bsegs m lo (bv_unsigned sp) -> ATOP <= lo -> lo <= bv_unsigned sp - 48 ->
  mem_inv bsegs m ->
  a0 = Z_to_bv 64 AINSTANCE -> a1 = Z_to_bv 64 (t + 208) -> a2 = Z_to_bv 64 size -> a3 = Z_to_bv 64 8 ->
  16 <= size <= 65536 -> size mod 8 = 0 -> class_id size = c ->
  rw_cells bsegs m 0xd8638 [C8 (Z_to_bv 64 spacebeg)] ->
  rw_cells bsegs m (acache_rec t c) [C4 (Z_to_bv 64 cnt); C4 maxc; C8 csz] ->
  u32arr bsegs m (acache_rec t c + 16) chunks -> length chunks = 16%nat ->
  0 < cnt <= 16 -> nth_error chunks (Z.to_nat (cnt - 1)) = Some idxw -> bv_unsigned idxw < 2^32 ->
  rw_cells bsegs m (acache_stats t) [C8 stj] ->
  iclr t 4096 -> t + 4096 <= ATOP -> t mod 4096 = 0 -> 0 <= spacebeg < 2^47 ->
  rng_aimg RNG -> rng RNG lo (bv_unsigned sp - lo) -> rng RNG t 4096 ->
  evtF bsegs RNG (cache_hit_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc t c cnt (bv_unsigned idxw) spacebeg lo maxc csz m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x41db0) fc None m (seg_rom bsegs)).
Proof.
  intros until idxw. intros ST CEIL LO MI -> -> -> -> SZ M8 HC SB CR CH LCH CNT NTH IXS STS T0 T1 TAL SBR RIMG RSTK RT. band_lin.
  unfold AIMG_HI, AINSTANCE in *.
  pose proof (class_facts size ltac:(lia)) as CF. cbv zeta in CF. rewrite HC in CF. destruct CF as (C1 & CS1 & CS2 & CS3 & CSM & CBG).
  word_range sp SPR. word_range idxw IXR.
  pose proof (munch_refl [(bv_unsigned sp - 48, bv_unsigned sp); (t + 208 + c * 80, t + 208 + c * 80 + 4); (t + 2784, t + 2784 + 8)]%Z m) as MU.
  pose proof (wmono_refl bsegs m) as WM.
  carve_frame 48%nat ST.
  do 7 step.
  do 3 zstep.
  replace (size <? 1) with false by (symmetry; apply Z.ltb_ge; lia). cbn [Z.b2z]. rewrite Z.add_0_r.
  rewrite (Z.mod_small size) by lia. rewrite zb_lxor_ones by lia.
  step. if_cases K0; zify_cond K0; [| exfalso; lia].
  do 2 step. step. if_lit.
  step. step. if_lit.
  step. if_cases K1; zify_cond K1. { exfalso. lia. }
  step. step. if_cases K2; zify_cond K2.

  1: eapply evtF_cut; [eapply (classblock_spec RNG); [lia | assumption | exact RIMG] |].
  1: cbv beta; intros msB PB; destruct PB as (a2b & a4b & a5b & a6b & a7b & t0b & t1b & ->); rewrite HC.
  2: do 2 zstep; rewrite <- (CSM ltac:(lia)); step.

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
  all: pose proof (u32arr_read bsegs _ _ chunks (cnt + -1) idxw (wa (R + 16 + 4 * (cnt + -1))) CH ltac:(replace (cnt + -1) with (cnt - 1) by lia; exact NTH) ltac:(lia) ltac:(f_equal; lia)) as RD.
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
  stk bsegs m lo (bv_unsigned sp) -> ATOP <= lo -> lo <= bv_unsigned sp - 48 ->
  mem_inv bsegs m ->
  a0 = Z_to_bv 64 AINSTANCE -> a1 = Z_to_bv 64 (t + 208) -> a2 = Z_to_bv 64 size -> a3 = Z_to_bv 64 8 ->
  16 <= size <= 65536 -> size mod 8 = 0 -> class_id size = c ->
  rw_cells bsegs m (acache_rec t c) [C4 (Z_to_bv 64 0); C4 maxc; C8 csz] ->
  iclr t 4096 -> t + 4096 <= ATOP ->
  rng_aimg RNG -> rng RNG lo (bv_unsigned sp - lo) -> rng RNG t 4096 ->
  evtF bsegs RNG (calloc_pre_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc t c lo m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x41db0) fc None m (seg_rom bsegs)).
Proof.
  intros until csz. intros ST CEIL LO MI -> -> -> -> SZ M8 HC CR T0 T1 RIMG RSTK RT. band_lin.
  unfold AIMG_HI, AINSTANCE in *.
  pose proof (class_facts size ltac:(lia)) as CF. cbv zeta in CF. rewrite HC in CF. destruct CF as (C1 & CS1 & CS2 & CS3 & CSM & CBG).
  word_range sp SPR.
  pose proof (munch_refl [(bv_unsigned sp - 48, bv_unsigned sp)]%Z m) as MU.
  pose proof (wmono_refl bsegs m) as WM.
  carve_frame 48%nat ST.
  do 7 step.
  do 3 zstep.
  replace (size <? 1) with false by (symmetry; apply Z.ltb_ge; lia). cbn [Z.b2z]. rewrite Z.add_0_r.
  rewrite (Z.mod_small size) by lia. rewrite zb_lxor_ones by lia.
  step. if_cases K0; zify_cond K0; [| exfalso; lia].
  do 2 step. step. if_lit.
  step. step. if_lit.
  step. if_cases K1; zify_cond K1. { exfalso. lia. }
  step. step. if_cases K2; zify_cond K2.

  1: eapply evtF_cut; [eapply (classblock_spec RNG); [lia | assumption | exact RIMG] |].
  1: cbv beta; intros msB PB; destruct PB as (a2b & a4b & a5b & a6b & a7b & t0b & t1b & ->); rewrite HC.
  2: do 2 zstep; rewrite <- (CSM ltac:(lia)); step.

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
  stk bsegs m lo (bv_unsigned sp - 48) -> ATOP <= lo -> lo <= bv_unsigned sp - 48 ->
  mem_inv bsegs m ->
  bv_unsigned rv <> 0 ->
  1 <= c <= 30 ->
  rw_cells bsegs m (bv_unsigned sp + -48) [C8 s4v; C8 s3v; C8 s2v; C8 s1v; C8 s0v; C8 rav] ->
  rw_cells bsegs m 0xd8638 [C8 (Z_to_bv 64 spacebeg)] ->
  rw_cells bsegs m (acache_rec t c) [C4 (Z_to_bv 64 cnt); C4 maxc; C8 csz] ->
  u32arr bsegs m (acache_rec t c + 16) chunks -> length chunks = 16%nat ->
  0 < cnt <= 16 -> nth_error chunks (Z.to_nat (cnt - 1)) = Some idxw -> bv_unsigned idxw < 2^32 ->
  rw_cells bsegs m (acache_stats t) [C8 stj] ->
  iclr t 4096 -> t + 4096 <= ATOP -> t mod 4096 = 0 -> 0 <= spacebeg < 2^47 ->
  rng_aimg RNG -> rng RNG lo (bv_unsigned sp - lo) -> rng RNG t 4096 ->
  evtF bsegs RNG (cache_hit_post rav sp gp tp s0v s1v s2v s3v s4v s5 s6 s7 s8 s9 s10 s11 F fc t c cnt (bv_unsigned idxw) spacebeg lo maxc csz m)
    (MS (mkR (Z_to_bv 64 0x42060) (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp t0 t1 t2
             (Z_to_bv 64 c) (Z_to_bv 64 (acache_rec t c))
             rv a1 a2 a3 a4 a5 a6 a7
             (Z_to_bv 64 8) (Z_to_bv 64 (t + 208)) (Z_to_bv 64 AINSTANCE) s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x42060) fc None m (seg_rom bsegs)).
Proof.
  intros until idxw. intros ST CEIL LO MI RV C1 FR SB CR CH LCH CNT NTH IXS STS T0 T1 TAL SBR RIMG RSTK RT. band_lin.
  unfold AIMG_HI, AINSTANCE in *.
  word_range sp SPR. word_range idxw IXR. word_range rv RVR.
  pose proof (munch_refl [(bv_unsigned sp - 48, bv_unsigned sp); (t + 208 + c * 80, t + 208 + c * 80 + 4); (t + 2784, t + 2784 + 8)]%Z m) as MU.
  pose proof (wmono_refl bsegs m) as WM.
  assert (RB : t + 208 + 80 <= t + 208 + c * 80 /\ t + 208 + c * 80 + 80 <= t + 2688) by lia.
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
  pose proof (u32arr_read bsegs _ _ chunks (cnt + -1) idxw (wa (R + 16 + 4 * (cnt + -1))) CH ltac:(replace (cnt + -1) with (cnt - 1) by lia; exact NTH) ltac:(lia) ltac:(f_equal; lia)) as RD.
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
End F_acache4.
End TwinB.
