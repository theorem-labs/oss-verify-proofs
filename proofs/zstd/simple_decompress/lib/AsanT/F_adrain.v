(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Lib Require Import Arr InitMem.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Spec Require Import AsanCtrl.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.AsanT Require Import BImg ABase AQConst ABytes.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.LibA Require Import StepF.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.AsanT Require Import AKit AKit2 AKitQ.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import RunDraw.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
(* [comment removed for export] *)
Local Ltac band_lin :=      (* [comment removed for export] *)
  repeat match goal with H : iclr ?a ?n |- _ => unfold iclr, AIMG_LO, AIMG_HI in H end.
Local Ltac with_band H tac :=
  let H' := fresh H in pose proof H as H'; unfold sclr, iclr, ablk, KLS, AIMG_LO, AIMG_HI in H'; tac; try clear H'.


(* [comment removed for export] *)
Section CANSEC1. Context {rc : runConstT}.
Definition drain_post (gfull : bool) (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (t nb fst lst qb gnb gfst glst gqb lo : Z) (m : amem) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom bsegs)
    /\ munch [(bv_unsigned sp - 48, bv_unsigned sp); (t + 80, t + 112); (0xcca08, 0xcca08 + 4); (0xcca10, 0xcca10 + 32); (glst, glst + 8)]%Z m m'
    /\ wmono bsegs m m' /\ mem_inv bsegs m'
    /\ stk bsegs m' lo (bv_unsigned sp)
    /\ rw_cells bsegs m' (t + 80) [C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)]
    /\ rw_cells bsegs m' 0xcca08 [C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)]
    /\ rw_cells bsegs m' 0xcca10 [C8 (Z_to_bv 64 (gnb + nb)); C8 (Z_to_bv 64 (if gfull then gfst else fst)); C8 (Z_to_bv 64 lst);
                                   C8 (Z_to_bv 64 (gqb + qb))]
    /\ (if gfull then rw_cells bsegs m' glst [C8 (Z_to_bv 64 fst)] else True).

Lemma drain_norecycle_spec : forall (gfull : bool) (t glst : Z) RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : amem) (nb fst lst qb gnb gfst gqb gnx lo : Z),
  stk bsegs m lo (bv_unsigned sp) -> ATOP <= lo -> lo <= bv_unsigned sp - 48 ->
  mem_inv bsegs m ->
  a0 = Z_to_bv 64 AQUAR_Q -> a1 = Z_to_bv 64 (t + 80) ->
  rw_cells bsegs m (t + 80) [C8 (Z_to_bv 64 nb); C8 (Z_to_bv 64 fst); C8 (Z_to_bv 64 lst); C8 (Z_to_bv 64 qb)] ->
  0 < nb < 2^63 -> 0 <= qb -> 0 <= fst < 2^64 -> 0 <= lst < 2^64 ->
  rw_cells bsegs m AQ_MUTEX [C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)] ->
  rw_cells bsegs m AQ_GCACHE [C8 (Z_to_bv 64 gnb); C8 (Z_to_bv 64 gfst); C8 (Z_to_bv 64 glst); C8 (Z_to_bv 64 gqb)] ->
  0 <= gnb < 2^62 -> 0 <= gqb -> gqb + qb <= Q_MAX -> 0 <= gfst < 2^64 -> 0 <= glst < 2^64 ->
  rw_cells bsegs m AQ_MAX [C8 (Z_to_bv 64 Q_MAX)] ->
  (if gfull then 0 < gnb /\ rw_cells bsegs m glst [C8 (Z_to_bv 64 gnx)] /\ AIMG_HI <= glst /\ glst + Q_BATCH_BYTES <= ATOP
                 /\ (t + 4096 <= glst \/ glst + Q_BATCH_BYTES <= t)
   else gnb = 0) ->
  iclr t 4096 -> t + 4096 <= ATOP ->
  rng_aimg RNG -> rng RNG lo (bv_unsigned sp - lo) -> rng RNG t 4096 -> (if gfull then rng RNG glst Q_BATCH_BYTES else True) ->
  evtF bsegs RNG (drain_post gfull ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc t nb fst lst qb gnb gfst glst gqb lo m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x35510) fc None m (seg_rom bsegs)).
Proof.
  intros until lo. intros ST CEIL LO MI -> -> QC NB QB FST LST MX GC GNB GQB GQ GFST GLST QM GFULL T0 T1 RIMG RSTK RT RGL. band_lin.   (* [comment removed for export] *)
  unfold AIMG_HI, Q_BATCH_BYTES, Q_MAX, AQUAR_Q, AQ_MUTEX, AQ_GCACHE, AQ_MAX, AINSTANCE in *.
  pose proof (munch_refl [(bv_unsigned sp - 48, bv_unsigned sp); (t + 80, t + 112); (0xcca08, 0xcca08 + 4);
                          (0xcca10, 0xcca10 + 32); (glst, glst + 8)]%Z m) as MU.
  pose proof (wmono_refl bsegs m) as WM.
  word_range sp SPR.
  carve_frame 48%nat ST.
  destruct gfull.
  - destruct GFULL as (GNB1 & GLB & GL0 & GL1 & DTG).
    do 6 step.                                 (* [comment removed for export] *)
    zstep. step. zstep. step.                  (* [comment removed for export] *)
    apply (rw_C1x4_to_C4 _ _ 0 0 ltac:(lia) ltac:(lia)) in MX. change (0 + 256 * 0) with 0 in MX.
    amo_step. lits.                            (* [comment removed for export] *)
    do 4 zstep.                                (* [comment removed for export] *)
    amo_step.                                  (* [comment removed for export] *)
    step. if_lit.                              (* [comment removed for export] *)
    zstep. step. if_lit.                       (* [comment removed for export] *)
    zstep. step. if_cases K0; zify_cond K0; [exfalso; lia|].   (* [comment removed for export] *)
    step. step. if_cases K1; zify_cond K1; [exfalso; lia|].    (* [comment removed for export] *)
    step. step. if_cases K2; zify_cond K2; [exfalso; lia|].    (* [comment removed for export] *)
    step. step. step. zstep.                   (* [comment removed for export] *)
    step. step. step. step.                    (* [comment removed for export] *)
    step. step. step.                          (* [comment removed for export] *)
    step. step. zstep. step. step.             (* [comment removed for export] *)
    step.                                      (* [comment removed for export] *)
    apply (rw_C4_to_C1x4 _ _ 1 0 ltac:(lia) ltac:(lia)) in MX.
    step.                                      (* [comment removed for export] *)
    step. step. step. if_cases K3; zify_cond K3; [|exfalso; lia].   (* [comment removed for export] *)
    do 7 step.                                 (* [comment removed for export] *)
    release_frame FR ST (bv_unsigned sp).
    unfold drain_post. finish.
  - pose proof GFULL as GNB0. clear GFULL.
    do 6 step.                                 (* [comment removed for export] *)
    zstep. step. zstep. step.                  (* [comment removed for export] *)
    apply (rw_C1x4_to_C4 _ _ 0 0 ltac:(lia) ltac:(lia)) in MX. change (0 + 256 * 0) with 0 in MX.
    amo_step. lits.                            (* [comment removed for export] *)
    do 4 zstep.                                (* [comment removed for export] *)
    amo_step.                                  (* [comment removed for export] *)
    step. if_lit.                              (* [comment removed for export] *)
    zstep. step. if_lit.                       (* [comment removed for export] *)
    zstep. step. if_cases K0; zify_cond K0; [exfalso; lia|].   (* [comment removed for export] *)
    step. step. if_cases K1; zify_cond K1; [exfalso; lia|].    (* [comment removed for export] *)
    step. step. if_cases K2; zify_cond K2; [|exfalso; lia].    (* [comment removed for export] *)
    step. step. step. step. step. step.        (* [comment removed for export] *)
    step. step. step.                          (* [comment removed for export] *)
    step. step. zstep. step. step.             (* [comment removed for export] *)
    step.                                      (* [comment removed for export] *)
    apply (rw_C4_to_C1x4 _ _ 1 0 ltac:(lia) ltac:(lia)) in MX.
    step.                                      (* [comment removed for export] *)
    step. step. step. if_cases K3; zify_cond K3; [|exfalso; lia].   (* [comment removed for export] *)
    do 7 step.                                 (* [comment removed for export] *)
    release_frame FR ST (bv_unsigned sp).
    unfold drain_post. finish.
    subst gnb. exact GC.
Qed.

End CANSEC1.
