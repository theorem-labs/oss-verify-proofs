(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Lib Require Import Arr Bytes ZBridge.
From OSSVerify.Proofs.simdjson.fuzz_utf8.lib.BothW Require Import BImg.
From OSSVerify.Proofs.simdjson.fuzz_utf8.lib.LibA Require Import Shadow.
From OSSVerify.Proofs.simdjson.fuzz_utf8.lib.LibA Require Import StepF.
From OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common Require Import RunDraw.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Ltac zify_lts K :=
  unfold bv_lts in K; rewrite ?land7_mod in K;
  rewrite !signed_lit_small64 in K by (Z.div_mod_to_equations; lia);
  zify_bool K.
Section CANSEC1. Context {rc : runConstT}.

Lemma ckb_b7a10 : forall ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 (F : bvmap 5 word) (fc : bv 32) (mm : word -> option byte) (RNG : footprint) (P : Z) (b : byte),
    0 <= P < 2^63 -> (sval b = 0 \/ (0 < sval b <= 7 /\ P mod 8 + 1 - 1 < sval b)) ->
    evtF bsegs RNG (fun ms' => exists y_a4, ms' = (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 P) a1 a2 (Z_to_bv 64 (sval b)) y_a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0xb7d70) fc None mm (seg_rom bsegs)))
         (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 P) a1 a2 (Z_to_bv 64 (sval b)) a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0xb7d6c) fc None mm (seg_rom bsegs)).
Proof.
  intros until b. intros PR CK. pose proof (sval_range b) as SR.
  zstep. if_cases K1; zify_cond K1.
  { zstep. zstep.  if_cases K2; zify_lts K2. 2:{ exfalso. Z.div_mod_to_equations. lia. }
    apply evtF_done. eexists; reflexivity. }
  apply evtF_done. eexists; reflexivity.
Qed.

Lemma ckb_b7a24 : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 (F : bvmap 5 word) (fc : bv 32) (mm : word -> option byte) (RNG : footprint) (P : Z) (b : byte),
    0 <= P < 2^63 -> (sval b = 0 \/ (0 < sval b <= 7 /\ P mod 8 + 1 - 1 < sval b)) ->
    evtF bsegs RNG (fun ms' => exists y_s4, ms' = (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 (Z_to_bv 64 P) (Z_to_bv 64 (sval b)) a5 a6 a7 s2 s3 y_s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0xb7d84) fc None mm (seg_rom bsegs)))
         (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 (Z_to_bv 64 P) (Z_to_bv 64 (sval b)) a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0xb7d80) fc None mm (seg_rom bsegs)).
Proof.
  intros until b. intros PR CK. pose proof (sval_range b) as SR.
  zstep. if_cases K1; zify_cond K1.
  { zstep. zstep.  if_cases K2; zify_lts K2. 2:{ exfalso. Z.div_mod_to_equations. lia. }
    apply evtF_done. eexists; reflexivity. }
  apply evtF_done. eexists; reflexivity.
Qed.

Lemma ckb_b7a58 : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 (F : bvmap 5 word) (fc : bv 32) (mm : word -> option byte) (RNG : footprint) (P : Z) (b : byte),
    0 <= P < 2^63 -> (sval b = 0 \/ (0 < sval b <= 7 /\ P mod 8 + 1 - 1 < sval b)) ->
    evtF bsegs RNG (fun ms' => exists y_ra, ms' = (MS (mkR y_ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 (Z_to_bv 64 P) (Z_to_bv 64 (sval b)) a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0xb7db8) fc None mm (seg_rom bsegs)))
         (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 (Z_to_bv 64 P) (Z_to_bv 64 (sval b)) a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0xb7db4) fc None mm (seg_rom bsegs)).
Proof.
  intros until b. intros PR CK. pose proof (sval_range b) as SR.
  zstep. if_cases K1; zify_cond K1.
  { zstep. zstep.  if_cases K2; zify_lts K2. 2:{ exfalso. Z.div_mod_to_equations. lia. }
    apply evtF_done. eexists; reflexivity. }
  apply evtF_done. eexists; reflexivity.
Qed.

Lemma ckb_b7a6c : forall sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t4 t5 t6 (F : bvmap 5 word) (fc : bv 32) (mm : word -> option byte) (RNG : footprint) (P : Z) (b : byte),
    0 <= P < 2^63 -> (sval b = 0 \/ (0 < sval b <= 7 /\ P mod 8 + 1 - 1 < sval b)) ->
    evtF bsegs RNG (fun ms' => exists y_a4, ms' = (MS (mkR (Z_to_bv 64 (sval b)) sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 y_a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 P) t4 t5 t6) F (Z_to_bv 64 0xb7dcc) fc None mm (seg_rom bsegs)))
         (MS (mkR (Z_to_bv 64 (sval b)) sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 P) t4 t5 t6) F (Z_to_bv 64 0xb7dc8) fc None mm (seg_rom bsegs)).
Proof.
  intros until b. intros PR CK. pose proof (sval_range b) as SR.
  zstep. if_cases K1; zify_cond K1.
  { zstep. zstep.  if_cases K2; zify_lts K2. 2:{ exfalso. Z.div_mod_to_equations. lia. }
    apply evtF_done. eexists; reflexivity. }
  apply evtF_done. eexists; reflexivity.
Qed.

Lemma ckb_b7b24 : forall ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 (F : bvmap 5 word) (fc : bv 32) (mm : word -> option byte) (RNG : footprint) (P : Z) (b : byte),
    0 <= P < 2^63 -> (sval b = 0 \/ (0 < sval b <= 7 /\ P mod 8 + 1 - 1 < sval b)) ->
    evtF bsegs RNG (fun ms' => exists y_a4, ms' = (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 P) a1 a2 (Z_to_bv 64 (sval b)) y_a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0xb7e84) fc None mm (seg_rom bsegs)))
         (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 P) a1 a2 (Z_to_bv 64 (sval b)) a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0xb7e80) fc None mm (seg_rom bsegs)).
Proof.
  intros until b. intros PR CK. pose proof (sval_range b) as SR.
  zstep. if_cases K1; zify_cond K1.
  { zstep. zstep.  if_cases K2; zify_lts K2. 2:{ exfalso. Z.div_mod_to_equations. lia. }
    apply evtF_done. eexists; reflexivity. }
  apply evtF_done. eexists; reflexivity.
Qed.

Lemma ckb_b7b5c : forall ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 (F : bvmap 5 word) (fc : bv 32) (mm : word -> option byte) (RNG : footprint) (P : Z) (b : byte),
    0 <= P < 2^63 -> (sval b = 0 \/ (0 < sval b <= 7 /\ P mod 8 + 1 - 1 < sval b)) ->
    evtF bsegs RNG (fun ms' => exists y_t3, ms' = (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (sval b)) a1 a2 (Z_to_bv 64 P) a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 y_t3 t4 t5 t6) F (Z_to_bv 64 0xb7ebc) fc None mm (seg_rom bsegs)))
         (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (sval b)) a1 a2 (Z_to_bv 64 P) a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0xb7eb8) fc None mm (seg_rom bsegs)).
Proof.
  intros until b. intros PR CK. pose proof (sval_range b) as SR.
  zstep. if_cases K1; zify_cond K1.
  { zstep. zstep.  if_cases K2; zify_lts K2. 2:{ exfalso. Z.div_mod_to_equations. lia. }
    apply evtF_done. eexists; reflexivity. }
  apply evtF_done. eexists; reflexivity.
Qed.

Lemma ckb_b7ba0 : forall ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 (F : bvmap 5 word) (fc : bv 32) (mm : word -> option byte) (RNG : footprint) (P : Z) (b : byte),
    0 <= P < 2^63 -> (sval b = 0 \/ (0 < sval b <= 7 /\ P mod 8 + 1 - 1 < sval b)) ->
    evtF bsegs RNG (fun ms' => exists y_t3, ms' = (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 P) a1 a2 (Z_to_bv 64 (sval b)) a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 y_t3 t4 t5 t6) F (Z_to_bv 64 0xb7f00) fc None mm (seg_rom bsegs)))
         (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 P) a1 a2 (Z_to_bv 64 (sval b)) a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0xb7efc) fc None mm (seg_rom bsegs)).
Proof.
  intros until b. intros PR CK. pose proof (sval_range b) as SR.
  zstep. if_cases K1; zify_cond K1.
  { zstep. zstep.  if_cases K2; zify_lts K2. 2:{ exfalso. Z.div_mod_to_equations. lia. }
    apply evtF_done. eexists; reflexivity. }
  apply evtF_done. eexists; reflexivity.
Qed.

Lemma ckb_b7bc8 : forall ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 (F : bvmap 5 word) (fc : bv 32) (mm : word -> option byte) (RNG : footprint) (P : Z) (b : byte),
    0 <= P < 2^63 -> (sval b = 0 \/ (0 < sval b <= 7 /\ P mod 8 + 1 - 1 < sval b)) ->
    evtF bsegs RNG (fun ms' => exists y_t3, ms' = (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 P) a1 a2 a3 a4 a5 a6 a7 s2 (Z_to_bv 64 (sval b)) s4 s5 s6 s7 s8 s9 s10 s11 y_t3 t4 t5 t6) F (Z_to_bv 64 0xb7f28) fc None mm (seg_rom bsegs)))
         (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 P) a1 a2 a3 a4 a5 a6 a7 s2 (Z_to_bv 64 (sval b)) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0xb7f24) fc None mm (seg_rom bsegs)).
Proof.
  intros until b. intros PR CK. pose proof (sval_range b) as SR.
  zstep. if_cases K1; zify_cond K1.
  { zstep. zstep.  if_cases K2; zify_lts K2. 2:{ exfalso. Z.div_mod_to_equations. lia. }
    apply evtF_done. eexists; reflexivity. }
  apply evtF_done. eexists; reflexivity.
Qed.

Lemma ckb_b7c2c : forall ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 (F : bvmap 5 word) (fc : bv 32) (mm : word -> option byte) (RNG : footprint) (P : Z) (b : byte),
    0 <= P < 2^63 -> (sval b = 0 \/ (0 < sval b <= 7 /\ P mod 8 + 1 - 1 < sval b)) ->
    evtF bsegs RNG (fun ms' => exists y_t3, ms' = (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 P) a1 a2 (Z_to_bv 64 (sval b)) a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 y_t3 t4 t5 t6) F (Z_to_bv 64 0xb7f8c) fc None mm (seg_rom bsegs)))
         (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 P) a1 a2 (Z_to_bv 64 (sval b)) a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0xb7f88) fc None mm (seg_rom bsegs)).
Proof.
  intros until b. intros PR CK. pose proof (sval_range b) as SR.
  zstep. if_cases K1; zify_cond K1.
  { zstep. zstep.  if_cases K2; zify_lts K2. 2:{ exfalso. Z.div_mod_to_equations. lia. }
    apply evtF_done. eexists; reflexivity. }
  apply evtF_done. eexists; reflexivity.
Qed.

Lemma ckb_b7c54 : forall ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 (F : bvmap 5 word) (fc : bv 32) (mm : word -> option byte) (RNG : footprint) (P : Z) (b : byte),
    0 <= P < 2^63 -> (sval b = 0 \/ (0 < sval b <= 7 /\ P mod 8 + 1 - 1 < sval b)) ->
    evtF bsegs RNG (fun ms' => exists y_t3, ms' = (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 P) a1 a2 a3 a4 a5 a6 a7 s2 s3 (Z_to_bv 64 (sval b)) s5 s6 s7 s8 s9 s10 s11 y_t3 t4 t5 t6) F (Z_to_bv 64 0xb7fb4) fc None mm (seg_rom bsegs)))
         (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 P) a1 a2 a3 a4 a5 a6 a7 s2 s3 (Z_to_bv 64 (sval b)) s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0xb7fb0) fc None mm (seg_rom bsegs)).
Proof.
  intros until b. intros PR CK. pose proof (sval_range b) as SR.
  zstep. if_cases K1; zify_cond K1.
  { zstep. zstep.  if_cases K2; zify_lts K2. 2:{ exfalso. Z.div_mod_to_equations. lia. }
    apply evtF_done. eexists; reflexivity. }
  apply evtF_done. eexists; reflexivity.
Qed.

Lemma ckb_b7c78 : forall ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 (F : bvmap 5 word) (fc : bv 32) (mm : word -> option byte) (RNG : footprint) (P : Z) (b : byte),
    0 <= P < 2^63 -> (sval b = 0 \/ (0 < sval b <= 7 /\ P mod 8 + 1 - 1 < sval b)) ->
    evtF bsegs RNG (fun ms' => exists y_t3, ms' = (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 P) a1 a2 a3 a4 a5 a6 a7 s2 (Z_to_bv 64 (sval b)) s4 s5 s6 s7 s8 s9 s10 s11 y_t3 t4 t5 t6) F (Z_to_bv 64 0xb7fd8) fc None mm (seg_rom bsegs)))
         (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 P) a1 a2 a3 a4 a5 a6 a7 s2 (Z_to_bv 64 (sval b)) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0xb7fd4) fc None mm (seg_rom bsegs)).
Proof.
  intros until b. intros PR CK. pose proof (sval_range b) as SR.
  zstep. if_cases K1; zify_cond K1.
  { zstep. zstep.  if_cases K2; zify_lts K2. 2:{ exfalso. Z.div_mod_to_equations. lia. }
    apply evtF_done. eexists; reflexivity. }
  apply evtF_done. eexists; reflexivity.
Qed.

End CANSEC1.
