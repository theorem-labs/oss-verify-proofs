(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Lib Require Import ITree Nodes Decode Arr.
From OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Spec Require Import STree AsanCtrl.
From OSSVerify.Proofs.simdjson.fuzz_utf8.lib.AsanW Require Import AImg AProto ABase.
From OSSVerify.Proofs.simdjson.fuzz_utf8.lib.LibA Require Import StepF.
From OSSVerify.Proofs.simdjson.fuzz_utf8.lib.AsanW Require Import AKit AModelFacts F_aunwind F_aalloc_s F_acache.
From OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common Require Import RunDraw.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
(* [comment removed for export] *)
Local Ltac band_lin :=      (* [comment removed for export] *)
  repeat match goal with H : iclr ?a ?n |- _ => unfold iclr, AIMG_LO, AIMG_HI in H end.
Local Ltac with_band H tac :=
  let H' := fresh H in pose proof H as H'; unfold sclr, iclr, ablk, KLS, AIMG_LO, AIMG_HI in H'; tac; try clear H'.


Section CANSEC1. Context {rc : runConstT}.
Definition allocate_entry := 0x5a33c%Z.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma rz_ladder_spec : forall RNG ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : amem) (n : Z),
  0 <= n < 2^40 ->
  rng_aimg RNG ->
  evtF asegs RNG (fun ms' => exists a0',
      ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0' a1 a2 a3 a4 a5 a6 a7 s2 (Z_to_bv 64 (rz_log n)) s4 (Z_to_bv 64 n) s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (Z_to_bv 64 0x5a4a8) fc None m (seg_rom asegs))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 49) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 (Z_to_bv 64 n) s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x5a3d4) fc None m (seg_rom asegs)).
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
  evtF asegs RNG (fun ms' =>
      ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 (Z_to_bv 64 0) (Z_to_bv 64 (Z.max n 8)) (Z_to_bv 64 8) a2 a3 a4 a5 a6 a7 s2 (Z_to_bv 64 rz) s4 (Z_to_bv 64 n) s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (Z_to_bv 64 0x5a4f0) fc None m (seg_rom asegs))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 (Z_to_bv 64 0) (Z_to_bv 64 7) a1 a2 a3 a4 a5 a6 a7 s2 (Z_to_bv 64 rz) s4 (Z_to_bv 64 n) s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x5a4d4) fc None m (seg_rom asegs)).
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
     rw_cells asegs m AINITED [C1 (Z_to_bv 8 1)]
  /\ rw_cells asegs m ARSSLIM [C1 (Z_to_bv 8 0)]
  /\ rw_cells asegs m 0x16c4b8 (* [comment removed for export] *) [C8 (Z_to_bv 64 (2^40)); C2 (Z_to_bv 64 16); C2 (Z_to_bv 64 2048)]
  /\ rw_cells asegs m ATSDI [C1 (Z_to_bv 8 1)] /\ rw_cells asegs m ATSDK [C4 (Z_to_bv 64 0)]
  /\ rw_cells asegs m ATP88 [C8 (Z_to_bv 64 ATSD)] /\ rw_cells asegs m ATSD [C8 (Z_to_bv 64 ctx)]
  /\ rw_cells asegs m (ctx + 152) [C8 (Z_to_bv 64 t)].

Definition allocA_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (n S t c cnt spacebeg lo : Z) (idxw maxc csz : word) (m : amem) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR (Z_to_bv 64 0x5a5dc) (Z_to_bv 64 (bv_unsigned sp + -128)) gp tp t0 t1 t2
                  (Z_to_bv 64 1) (Z_to_bv 64 n)
                  (Z_to_bv 64 (spacebeg + c * 2^32 + 16 * bv_unsigned idxw)) a1 a2 a3 a4 a5 a6 a7
                  (Z_to_bv 64 8) (Z_to_bv 64 (needed_size n)) (Z_to_bv 64 (rz_size n)) (Z_to_bv 64 n)
                  (Z_to_bv 64 AINSTANCE) (Z_to_bv 64 S) (Z_to_bv 64 (-8)) (Z_to_bv 64 7) (Z_to_bv 64 t) (Z_to_bv 64 1)
                  t3 t4 t5 t6)
             F (Z_to_bv 64 0x5a5dc) fc None m' (seg_rom asegs)
    /\ munch [(bv_unsigned sp - 176, bv_unsigned sp); (acache_rec t c, acache_rec t c + 4); (acache_stats t, acache_stats t + 8)]%Z m m'
    /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ stk asegs m' lo (bv_unsigned sp - 128)
    /\ (exists j0, rw_cells asegs m' (bv_unsigned sp - 128)
         [CB 8 j0 (* [comment removed for export] *); C8 (Z_to_bv 64 1) (* [comment removed for export] *); C8 (Z_to_bv 64 16) (* [comment removed for export] *);
          C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra])
    /\ rw_cells asegs m' (acache_rec t c) [C4 (Z_to_bv 64 (cnt - 1)); C4 maxc; C8 csz]
    /\ (exists stj' : word, rw_cells asegs m' (acache_stats t) [C8 stj']).

(* [comment removed for export] *)
End CANSEC1.
