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
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.AsanT Require Import AKit AModelFacts F_aunwind F_aalloc_s F_acache.
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
Definition allocate_entry := 0x33b08%Z.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma rz_ladder_spec : forall RNG ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : amem) (n : Z),
  0 <= n < 2^40 ->
  rng_aimg RNG ->
  evtF bsegs RNG (fun ms' => exists a0',
      ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0' a1 a2 a3 a4 a5 a6 a7 s2 (Z_to_bv 64 (rz_log n)) s4 (Z_to_bv 64 n) s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (Z_to_bv 64 0x33c74) fc None m (seg_rom bsegs))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 49) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 (Z_to_bv 64 n) s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x33ba0) fc None m (seg_rom bsegs)).
Proof.
  intros until n. intros N RIMG. unfold rz_log.
  step. if_cases K0; zify_cond K0.
  2: { replace (n <=? 48) with true by (symmetry; apply Z.leb_le; lia). do 2 step. apply evtF_done. eexists. reflexivity. }
  replace (n <=? 48) with false by (symmetry; apply Z.leb_gt; lia).
  step. step. if_cases K1; zify_cond K1.
  2: { replace (n <=? 96) with true by (symmetry; apply Z.leb_le; lia). do 2 step. apply evtF_done. eexists. reflexivity. }
  replace (n <=? 96) with false by (symmetry; apply Z.leb_gt; lia).
  step. step. if_cases K2; zify_cond K2.
  2: { replace (n <=? 448) with true by (symmetry; apply Z.leb_le; lia). do 2 step. apply evtF_done. eexists. reflexivity. }
  replace (n <=? 448) with false by (symmetry; apply Z.leb_gt; lia).
  step. zstep. step. if_cases K3; zify_cond K3.
  2: { replace (n <=? 3968) with true by (symmetry; apply Z.leb_le; lia). do 2 step. apply evtF_done. eexists. reflexivity. }
  replace (n <=? 3968) with false by (symmetry; apply Z.leb_gt; lia).
  step. zstep. step. if_cases K4; zify_cond K4.
  2: { replace (n <=? 16128) with true by (symmetry; apply Z.leb_le; lia). do 2 step. apply evtF_done. eexists. reflexivity. }
  replace (n <=? 16128) with false by (symmetry; apply Z.leb_gt; lia).
  step. zstep. step. if_cases K5; zify_cond K5.
  2: { replace (n <=? 32256) with true by (symmetry; apply Z.leb_le; lia). do 2 step. apply evtF_done. eexists. reflexivity. }
  replace (n <=? 32256) with false by (symmetry; apply Z.leb_gt; lia).
  step. zstep. zstep. zstep.
  apply evtF_done. destruct (Z.leb_spec n 64512) as [K6|K6]; eexists.
  - replace (n <? 64513) with true by (symmetry; apply Z.ltb_lt; lia). reflexivity.
  - replace (n <? 64513) with false by (symmetry; apply Z.ltb_ge; lia). reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma rz_clamp_spec : forall RNG ra sp gp tp t0 t1 t2 s0 a1 a2 a3 a4 a5 a6 a7 s2 s4 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : amem) (n rz : Z),
  0 <= n < 2^40 -> 0 <= rz <= 7 ->
  rng_aimg RNG ->
  evtF bsegs RNG (fun ms' =>
      ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 (Z_to_bv 64 0) (Z_to_bv 64 (Z.max n 8)) (Z_to_bv 64 8) a2 a3 a4 a5 a6 a7 s2 (Z_to_bv 64 rz) s4 (Z_to_bv 64 n) s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (Z_to_bv 64 0x33cbc) fc None m (seg_rom bsegs))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 (Z_to_bv 64 0) (Z_to_bv 64 7) a1 a2 a3 a4 a5 a6 a7 s2 (Z_to_bv 64 rz) s4 (Z_to_bv 64 n) s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x33ca0) fc None m (seg_rom bsegs)).
Proof.
  intros until rz. intros N RZ RIMG.
  step. if_cases K0; zify_cond K0.
  - (* [comment removed for export] *)
    step. if_cases K1; zify_cond K1.
    + (* [comment removed for export] *) step. step. step. if_cases K2; zify_cond K2.
      * replace (Z.max n 8) with n by lia. apply evtF_done. reflexivity.
      * step. replace (Z.max n 8) with 8 by lia. apply evtF_done. reflexivity.
    + (* [comment removed for export] *) step. replace rz with 7 by lia. step. step. step. if_cases K2; zify_cond K2.
      * step. replace (Z.max n 8) with 8 by lia. apply evtF_done. reflexivity.
      * step. replace (Z.max n 8) with n by lia. apply evtF_done. reflexivity.
  - (* [comment removed for export] *) step. replace rz with 0 by lia. step. if_lit. step. step. step. if_cases K2; zify_cond K2.
    + replace (Z.max n 8) with n by lia. apply evtF_done. reflexivity.
    + step. replace (Z.max n 8) with 8 by lia. apply evtF_done. reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition allocA_cells (m : amem) (ctx t : Z) : Prop :=
     rw_cells bsegs m AINITED [C1 (Z_to_bv 8 1)]
  /\ rw_cells bsegs m ARSSLIM [C1 (Z_to_bv 8 0)]
  /\ rw_cells bsegs m 0xcd4b8 (* [comment removed for export] *) [C8 (Z_to_bv 64 (2^40)); C2 (Z_to_bv 64 16); C2 (Z_to_bv 64 2048)]
  /\ rw_cells bsegs m ATSDI [C1 (Z_to_bv 8 1)] /\ rw_cells bsegs m ATSDK [C4 (Z_to_bv 64 0)]
  /\ rw_cells bsegs m ATP88 [C8 (Z_to_bv 64 ATSD)] /\ rw_cells bsegs m ATSD [C8 (Z_to_bv 64 ctx)]
  /\ rw_cells bsegs m (ctx + 152) [C8 (Z_to_bv 64 t)].

Definition allocA_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (n S t c cnt spacebeg lo : Z) (idxw maxc csz : word) (m : amem) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR (Z_to_bv 64 0x33da8) (Z_to_bv 64 (bv_unsigned sp + -128)) gp tp t0 t1 t2
                  (Z_to_bv 64 1) (Z_to_bv 64 n)
                  (Z_to_bv 64 (spacebeg + c * 2^32 + 16 * bv_unsigned idxw)) a1 a2 a3 a4 a5 a6 a7
                  (Z_to_bv 64 8) (Z_to_bv 64 (needed_size n)) (Z_to_bv 64 (rz_size n)) (Z_to_bv 64 n)
                  (Z_to_bv 64 AINSTANCE) (Z_to_bv 64 S) (Z_to_bv 64 (-8)) (Z_to_bv 64 7) (Z_to_bv 64 t) (Z_to_bv 64 1)
                  t3 t4 t5 t6)
             F (Z_to_bv 64 0x33da8) fc None m' (seg_rom bsegs)
    /\ munch [(bv_unsigned sp - 176, bv_unsigned sp); (acache_rec t c, acache_rec t c + 4); (acache_stats t, acache_stats t + 8)]%Z m m'
    /\ wmono bsegs m m' /\ mem_inv bsegs m'
    /\ stk bsegs m' lo (bv_unsigned sp - 128)
    /\ (exists j0, rw_cells bsegs m' (bv_unsigned sp - 128)
         [CB 8 j0 (* [comment removed for export] *); C8 (Z_to_bv 64 1) (* [comment removed for export] *); C8 (Z_to_bv 64 16) (* [comment removed for export] *);
          C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra])
    /\ rw_cells bsegs m' (acache_rec t c) [C4 (Z_to_bv 64 (cnt - 1)); C4 maxc; C8 csz]
    /\ (exists stj' : word, rw_cells bsegs m' (acache_stats t) [C8 stj']).

Lemma allocA_spec : forall RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : amem) (n S ctx t c cnt spacebeg lo : Z) (maxc csz stj : word) (chunks : list word) (idxw : word),
  stk bsegs m lo (bv_unsigned sp) -> ATOP <= lo -> lo <= bv_unsigned sp - 176 ->
  mem_inv bsegs m ->
  tp = Z_to_bv 64 ATP ->
  a0 = Z_to_bv 64 AINSTANCE -> a1 = Z_to_bv 64 n -> a2 = Z_to_bv 64 8 -> a3 = Z_to_bv 64 S -> a4 = Z_to_bv 64 1 -> a5 = Z_to_bv 64 1 ->
  1 <= n <= 448 -> 0 < S < 2^64 ->
  allocA_cells m ctx t ->
  rw_cells bsegs m 0xcc6b8 [C8 (Z_to_bv 64 spacebeg)] ->
  Z.shiftr (needed_size n + 31) 5 = c ->
  rw_cells bsegs m (acache_rec t c) [C4 (Z_to_bv 64 cnt); C4 maxc; C8 csz] ->
  u32arr bsegs m (acache_rec t c + 16) chunks -> length chunks = 16%nat ->
  0 < cnt <= 16 -> nth_error chunks (Z.to_nat (cnt - 1)) = Some idxw -> bv_unsigned idxw < 2^32 ->
  rw_cells bsegs m (acache_stats t) [C8 stj] ->
  AIMG_HI <= ctx -> ctx + 4096 <= ATOP -> iclr t 4096 -> t + 4096 <= ATOP -> t mod 4096 = 0 ->
  (ctx + 4096 <= t \/ t + 4096 <= ctx) -> 0 <= spacebeg < 2^47 ->
  rng_aimg RNG -> rng RNG lo (bv_unsigned sp - lo) -> rng RNG ctx 4096 -> rng RNG t 4096 ->
  evtF bsegs RNG (allocA_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc n S t c cnt spacebeg lo idxw maxc csz m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 allocate_entry) fc None m (seg_rom bsegs)).
Proof.
  intros until idxw. intros ST CEIL LO MI TP -> -> -> -> -> -> N HS AC SB HC CR CH LCH CNT NTH IXS STS C0 C1 T0 T1 TAL CT2 SBR RIMG RSTK RCTX RT. band_lin.   (* [comment removed for export] *)
  destruct AC as (INI & RSS & IMAX & TI & TK & T88 & TSD & CT).
  unfold AIMG_HI, AINSTANCE, AINITED, ATSDI, ATSDK, ATP88, ATSD, ARSSLIM, allocate_entry in *.
  pose proof (small_facts n N) as (PRIM & NS & RZR & RZE & RSR & RSM & NSR).
  assert (C16 : 1 <= c <= 16) by (rewrite <- HC; rewrite Z.shiftr_div_pow2 by lia; Z.div_mod_to_equations; lia).
  pose proof (munch_refl [(bv_unsigned sp - 176, bv_unsigned sp); (acache_rec t c, acache_rec t c + 4); (acache_stats t, acache_stats t + 8)]%Z m) as MU.
  pose proof (wmono_refl bsegs m) as WM.
  word_range sp SPR.
  carve_frame 128%nat ST.
  do 14 step.                                       (* [comment removed for export] *)
  do 6 step.                                        (* [comment removed for export] *)
  step. callp asan_inited_spec; [exact INI|]. step. if_lit.     (* [comment removed for export] *)
  step. callp rss_spec; [exact RSS|]. step. if_lit.             (* [comment removed for export] *)
  step. if_cases KS; zify_cond KS. { exfalso. lia. }            (* [comment removed for export] *)
  step. step. if_lit.                                            (* [comment removed for export] *)
  step. step. step. if_lit.                                      (* [comment removed for export] *)
  zstep. zstep. step. if_lit.                                    (* [comment removed for export] *)
  step. step. zstep. zstep. zstep. step. zstep. zstep. zstep.    (* [comment removed for export] *)
  lstep. zstep. zstep. zstep.                               (* [comment removed for export] *)
  step. step. if_lit.                                            (* [comment removed for export] *)
  step. zstep. zstep. step. if_lit.                              (* [comment removed for export] *)
  step. zstep. step. step.                                       (* [comment removed for export] *)
  callp rz_ladder_spec; [lia|].                                  (* [comment removed for export] *)
  lstep. step. step. zstep. zstep.                        (* [comment removed for export] *)
  step. call_sp rz2log16_spec; try eassumption; try lia; try reflexivity; try solve_rng.
  rename POST into ST.
  step. lstep. step. zstep.                                      (* [comment removed for export] *)
  step. call_sp rz2log2048_spec; try eassumption; try lia; try reflexivity; try solve_rng.
  rename POST into ST.
  callp rz_clamp_spec; [lia| pose proof (rz_log_range_small n N); lia |].   (* [comment removed for export] *)
  zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep.        (* [comment removed for export] *)
  change ((Z.b2z (8 <? 9) + -1) mod 18446744073709551616) with 0. rewrite Z.land_0_l, Z.add_0_r.
  rewrite land_align8 by lia.
  setreg 10 (Z_to_bv 64 (rounded_size n)) ltac:(f_equal; rewrite rounded_size_align; lia).
  zstep. step. if_cases KA; zify_cond KA. { exfalso. apply KA. change 7 with (2^3 - 1). rewrite zb_land_mask by lia. change (2^3) with 8. exact RSM. }   (* [comment removed for export] *)
  step. zstep.                                                   (* [comment removed for export] *)
  replace (n <? 1) with false by (symmetry; apply Z.ltb_ge; lia). cbn [Z.b2z].
  zstep. zstep.                                                  (* [comment removed for export] *)
  pose proof (rz_log_range_small n N) as RLR. rewrite (sllw_rz n N).   (* [comment removed for export] *)
  step. zstep.                                                   (* [comment removed for export] *)
  zstep. replace (8 <? 65537) with true by reflexivity. cbn [Z.b2z].   (* [comment removed for export] *)
  zstep.                                                         (* [comment removed for export] *)
  rewrite <- NS.
  zstep. zstep. zstep. zstep. step. zstep.                       (* [comment removed for export] *)
  replace (needed_size n <? 65537) with true by (symmetry; apply Z.ltb_lt; lia). cbn [Z.b2z].
  change ((Z.land 1 1 + -1) mod 18446744073709551616) with 0. change (Z.land 1 1) with 1. rewrite Z.land_0_l, Z.add_0_l.
  step. if_cases KB; zify_cond KB. { exfalso. lia. }            (* [comment removed for export] *)
  step. if_cases KC; zify_cond KC. { exfalso. lia. }            (* [comment removed for export] *)
  step. step. if_cases KD; zify_cond KD. 2: { exfalso. lia. }   (* [comment removed for export] *)
  box RT.
  step. call_sp get_current_thread_spec; try eassumption; try lia; try reflexivity; try solve_rng.
  unbox RT. rename POST into ST.
  step. step. if_cases KE; zify_cond KE. { exfalso. lia. }      (* [comment removed for export] *)
  zstep. step. step. step.                                       (* [comment removed for export] *)
  box RCTX.
  step. call_sp (combined_alloc_hit_spec _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ t (needed_size n) c cnt spacebeg lo maxc csz stj chunks idxw).
  all: try lazymatch goal with
       | |- evtF _ _ _ _ => idtac
       | |- iclr _ _ => assumption | |- sclr _ _ => assumption | |- ablk _ _ => assumption   (* [comment removed for export] *)
       | |- rng _ _ _ => solve_rng
       | |- stk _ _ _ _ => exact ST
       | |- mem_inv _ _ => assumption
       | |- @eq word _ _ => reflexivity
       | |- Z.shiftr _ _ = _ => exact HC
       | |- nth_error _ _ = _ => exact NTH
       | |- length _ = _ => exact LCH
       | |- _ mod _ = _ => exact TAL
       | |- u32arr _ _ _ _ => exact CH
       | |- rw_cells _ _ (_ + 208 + _ * 80) _ => exact CR
       | |- rw_cells _ _ (_ + 2784) _ => exact STS
       | |- rw_cells _ _ _ _ => exact SB
       | |- _ => unfold AIMG_HI; lia
       end.
  apply evtF_done. unfold allocA_post. do 15 eexists. split; [reflexivity|].
  repeat lazymatch goal with |- _ /\ _ => split end.
  all: try assumption. all: eexists; eassumption.
Qed.
End CANSEC1.
