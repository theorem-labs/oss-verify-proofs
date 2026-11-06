(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Lib Require Import Arr Bytes ZBridge.
From OSSVerify.Proofs.simdjson.fuzz_utf8.lib.AsanW Require Import AImg.
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

Lemma ckb_b66ac : forall ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 (F : bvmap 5 word) (fc : bv 32) (mm : word -> option byte) (RNG : footprint) (P : Z) (b : byte),
    0 <= P < 2^63 -> (sval b = 0 \/ (0 < sval b <= 7 /\ P mod 8 + 1 - 1 < sval b)) ->
    evtF asegs RNG (fun ms' => exists y_a4, ms' = (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 P) a1 a2 (Z_to_bv 64 (sval b)) y_a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0xb6a0c) fc None mm (seg_rom asegs)))
         (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 P) a1 a2 (Z_to_bv 64 (sval b)) a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0xb6a08) fc None mm (seg_rom asegs)).
Proof.
  intros until b. intros PR CK. pose proof (sval_range b) as SR.
  zstep. if_cases K1; zify_cond K1.
  { zstep. zstep.  if_cases K2; zify_lts K2. 2:{ exfalso. Z.div_mod_to_equations. lia. }
    apply evtF_done. eexists; reflexivity. }
  apply evtF_done. eexists; reflexivity.
Qed.

Lemma ckb_b66c0 : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 (F : bvmap 5 word) (fc : bv 32) (mm : word -> option byte) (RNG : footprint) (P : Z) (b : byte),
    0 <= P < 2^63 -> (sval b = 0 \/ (0 < sval b <= 7 /\ P mod 8 + 1 - 1 < sval b)) ->
    evtF asegs RNG (fun ms' => exists y_s2, ms' = (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 (Z_to_bv 64 P) (Z_to_bv 64 (sval b)) a5 a6 a7 y_s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0xb6a20) fc None mm (seg_rom asegs)))
         (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 (Z_to_bv 64 P) (Z_to_bv 64 (sval b)) a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0xb6a1c) fc None mm (seg_rom asegs)).
Proof.
  intros until b. intros PR CK. pose proof (sval_range b) as SR.
  zstep. if_cases K1; zify_cond K1.
  { zstep. zstep.  if_cases K2; zify_lts K2. 2:{ exfalso. Z.div_mod_to_equations. lia. }
    apply evtF_done. eexists; reflexivity. }
  apply evtF_done. eexists; reflexivity.
Qed.

Lemma ckb_b66f4 : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 (F : bvmap 5 word) (fc : bv 32) (mm : word -> option byte) (RNG : footprint) (P : Z) (b : byte),
    0 <= P < 2^63 -> (sval b = 0 \/ (0 < sval b <= 7 /\ P mod 8 + 1 - 1 < sval b)) ->
    evtF asegs RNG (fun ms' => exists y_s10, ms' = (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 (Z_to_bv 64 P) (Z_to_bv 64 (sval b)) a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 y_s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0xb6a54) fc None mm (seg_rom asegs)))
         (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 (Z_to_bv 64 P) (Z_to_bv 64 (sval b)) a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0xb6a50) fc None mm (seg_rom asegs)).
Proof.
  intros until b. intros PR CK. pose proof (sval_range b) as SR.
  zstep. if_cases K1; zify_cond K1.
  { zstep. zstep.  if_cases K2; zify_lts K2. 2:{ exfalso. Z.div_mod_to_equations. lia. }
    apply evtF_done. eexists; reflexivity. }
  apply evtF_done. eexists; reflexivity.
Qed.

Lemma ckb_b6708 : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s11 t3 t4 t5 t6 (F : bvmap 5 word) (fc : bv 32) (mm : word -> option byte) (RNG : footprint) (P : Z) (b : byte),
    0 <= P < 2^63 -> (sval b = 0 \/ (0 < sval b <= 7 /\ P mod 8 + 1 - 1 < sval b)) ->
    evtF asegs RNG (fun ms' => exists y_s11, ms' = (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 (Z_to_bv 64 P) a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 (Z_to_bv 64 (sval b)) y_s11 t3 t4 t5 t6) F (Z_to_bv 64 0xb6a68) fc None mm (seg_rom asegs)))
         (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 (Z_to_bv 64 P) a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 (Z_to_bv 64 (sval b)) s11 t3 t4 t5 t6) F (Z_to_bv 64 0xb6a64) fc None mm (seg_rom asegs)).
Proof.
  intros until b. intros PR CK. pose proof (sval_range b) as SR.
  zstep. if_cases K1; zify_cond K1.
  { zstep. zstep.  if_cases K2; zify_lts K2. 2:{ exfalso. Z.div_mod_to_equations. lia. }
    apply evtF_done. eexists; reflexivity. }
  apply evtF_done. eexists; reflexivity.
Qed.

Lemma ckb_b67bc : forall ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 (F : bvmap 5 word) (fc : bv 32) (mm : word -> option byte) (RNG : footprint) (P : Z) (b : byte),
    0 <= P < 2^63 -> (sval b = 0 \/ (0 < sval b <= 7 /\ P mod 8 + 1 - 1 < sval b)) ->
    evtF asegs RNG (fun ms' => exists y_a4, ms' = (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 P) a1 a2 (Z_to_bv 64 (sval b)) y_a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0xb6b1c) fc None mm (seg_rom asegs)))
         (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 P) a1 a2 (Z_to_bv 64 (sval b)) a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0xb6b18) fc None mm (seg_rom asegs)).
Proof.
  intros until b. intros PR CK. pose proof (sval_range b) as SR.
  zstep. if_cases K1; zify_cond K1.
  { zstep. zstep.  if_cases K2; zify_lts K2. 2:{ exfalso. Z.div_mod_to_equations. lia. }
    apply evtF_done. eexists; reflexivity. }
  apply evtF_done. eexists; reflexivity.
Qed.

Lemma ckb_b67ec : forall ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 (F : bvmap 5 word) (fc : bv 32) (mm : word -> option byte) (RNG : footprint) (P : Z) (b : byte),
    0 <= P < 2^63 -> (sval b = 0 \/ (0 < sval b <= 7 /\ P mod 8 + 1 - 1 < sval b)) ->
    evtF asegs RNG (fun ms' => exists y_s1, ms' = (MS (mkR ra sp gp tp t0 t1 t2 s0 y_s1 (Z_to_bv 64 (sval b)) a1 a2 (Z_to_bv 64 P) a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0xb6b4c) fc None mm (seg_rom asegs)))
         (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (sval b)) a1 a2 (Z_to_bv 64 P) a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0xb6b48) fc None mm (seg_rom asegs)).
Proof.
  intros until b. intros PR CK. pose proof (sval_range b) as SR.
  zstep. if_cases K1; zify_cond K1.
  { zstep. zstep.  if_cases K2; zify_lts K2. 2:{ exfalso. Z.div_mod_to_equations. lia. }
    apply evtF_done. eexists; reflexivity. }
  apply evtF_done. eexists; reflexivity.
Qed.

Lemma ckb_b6828 : forall ra sp gp tp t0 t1 t2 s0 a0 a1 a2 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 (F : bvmap 5 word) (fc : bv 32) (mm : word -> option byte) (RNG : footprint) (P : Z) (b : byte),
    0 <= P < 2^63 -> (sval b = 0 \/ (0 < sval b <= 7 /\ P mod 8 + 1 - 1 < sval b)) ->
    evtF asegs RNG (fun ms' => exists y_s2, ms' = (MS (mkR ra sp gp tp t0 t1 t2 s0 (Z_to_bv 64 (sval b)) a0 a1 a2 (Z_to_bv 64 P) a4 a5 a6 a7 y_s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0xb6b88) fc None mm (seg_rom asegs)))
         (MS (mkR ra sp gp tp t0 t1 t2 s0 (Z_to_bv 64 (sval b)) a0 a1 a2 (Z_to_bv 64 P) a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0xb6b84) fc None mm (seg_rom asegs)).
Proof.
  intros until b. intros PR CK. pose proof (sval_range b) as SR.
  zstep. if_cases K1; zify_cond K1.
  { zstep. zstep.  if_cases K2; zify_lts K2. 2:{ exfalso. Z.div_mod_to_equations. lia. }
    apply evtF_done. eexists; reflexivity. }
  apply evtF_done. eexists; reflexivity.
Qed.

Lemma ckb_b6848 : forall ra sp gp tp t0 t1 t2 s0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 (F : bvmap 5 word) (fc : bv 32) (mm : word -> option byte) (RNG : footprint) (P : Z) (b : byte),
    0 <= P < 2^63 -> (sval b = 0 \/ (0 < sval b <= 7 /\ P mod 8 + 1 - 1 < sval b)) ->
    evtF asegs RNG (fun ms' => exists y_s2, ms' = (MS (mkR ra sp gp tp t0 t1 t2 s0 (Z_to_bv 64 (sval b)) (Z_to_bv 64 P) a1 a2 a3 a4 a5 a6 a7 y_s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0xb6ba8) fc None mm (seg_rom asegs)))
         (MS (mkR ra sp gp tp t0 t1 t2 s0 (Z_to_bv 64 (sval b)) (Z_to_bv 64 P) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0xb6ba4) fc None mm (seg_rom asegs)).
Proof.
  intros until b. intros PR CK. pose proof (sval_range b) as SR.
  zstep. if_cases K1; zify_cond K1.
  { zstep. zstep.  if_cases K2; zify_lts K2. 2:{ exfalso. Z.div_mod_to_equations. lia. }
    apply evtF_done. eexists; reflexivity. }
  apply evtF_done. eexists; reflexivity.
Qed.

Lemma ckb_b68a0 : forall ra sp gp tp t0 t1 t2 s0 a0 a1 a2 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 (F : bvmap 5 word) (fc : bv 32) (mm : word -> option byte) (RNG : footprint) (P : Z) (b : byte),
    0 <= P < 2^63 -> (sval b = 0 \/ (0 < sval b <= 7 /\ P mod 8 + 1 - 1 < sval b)) ->
    evtF asegs RNG (fun ms' => exists y_s2, ms' = (MS (mkR ra sp gp tp t0 t1 t2 s0 (Z_to_bv 64 (sval b)) a0 a1 a2 (Z_to_bv 64 P) a4 a5 a6 a7 y_s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0xb6c00) fc None mm (seg_rom asegs)))
         (MS (mkR ra sp gp tp t0 t1 t2 s0 (Z_to_bv 64 (sval b)) a0 a1 a2 (Z_to_bv 64 P) a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0xb6bfc) fc None mm (seg_rom asegs)).
Proof.
  intros until b. intros PR CK. pose proof (sval_range b) as SR.
  zstep. if_cases K1; zify_cond K1.
  { zstep. zstep.  if_cases K2; zify_lts K2. 2:{ exfalso. Z.div_mod_to_equations. lia. }
    apply evtF_done. eexists; reflexivity. }
  apply evtF_done. eexists; reflexivity.
Qed.

Lemma ckb_b68c0 : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a4 a5 a6 a7 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 (F : bvmap 5 word) (fc : bv 32) (mm : word -> option byte) (RNG : footprint) (P : Z) (b : byte),
    0 <= P < 2^63 -> (sval b = 0 \/ (0 < sval b <= 7 /\ P mod 8 + 1 - 1 < sval b)) ->
    evtF asegs RNG (fun ms' => exists y_s3, ms' = (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 (Z_to_bv 64 P) a4 a5 a6 a7 (Z_to_bv 64 (sval b)) y_s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0xb6c20) fc None mm (seg_rom asegs)))
         (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 (Z_to_bv 64 P) a4 a5 a6 a7 (Z_to_bv 64 (sval b)) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0xb6c1c) fc None mm (seg_rom asegs)).
Proof.
  intros until b. intros PR CK. pose proof (sval_range b) as SR.
  zstep. if_cases K1; zify_cond K1.
  { zstep. zstep.  if_cases K2; zify_lts K2. 2:{ exfalso. Z.div_mod_to_equations. lia. }
    apply evtF_done. eexists; reflexivity. }
  apply evtF_done. eexists; reflexivity.
Qed.

Lemma ckb_b68dc : forall ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 (F : bvmap 5 word) (fc : bv 32) (mm : word -> option byte) (RNG : footprint) (P : Z) (b : byte),
    0 <= P < 2^63 -> (sval b = 0 \/ (0 < sval b <= 7 /\ P mod 8 + 1 - 1 < sval b)) ->
    evtF asegs RNG (fun ms' => exists y_s2, ms' = (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 P) a1 a2 (Z_to_bv 64 (sval b)) a4 a5 a6 a7 y_s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0xb6c3c) fc None mm (seg_rom asegs)))
         (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 P) a1 a2 (Z_to_bv 64 (sval b)) a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0xb6c38) fc None mm (seg_rom asegs)).
Proof.
  intros until b. intros PR CK. pose proof (sval_range b) as SR.
  zstep. if_cases K1; zify_cond K1.
  { zstep. zstep.  if_cases K2; zify_lts K2. 2:{ exfalso. Z.div_mod_to_equations. lia. }
    apply evtF_done. eexists; reflexivity. }
  apply evtF_done. eexists; reflexivity.
Qed.

End CANSEC1.
