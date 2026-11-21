(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.zlib_uncompress3_fuzzer_asan_ubsan.Lib Require Import Image Tac InitMem.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.zlib_uncompress3_fuzzer_asan_ubsan.BothW Require Import BImg ABase.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.zlib_uncompress3_fuzzer_asan_ubsan.LibA Require Import StepF.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.zlib_uncompress3_fuzzer_asan_ubsan.BothW Require Import AKit FsKit.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.zlib_uncompress3_fuzzer_asan_ubsan.Common Require Import RunDraw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Ltac solve_load ::= solve_load_g.
Local Ltac solve_store ::= solve_store_g.

Section CANSEC1. Context {rc : runConstT}.
Definition ASYSCONF : Z := 0xbd374.
Definition AGETPAGESIZE : Z := 0x71740.
Definition AGETMMAPGRAN : Z := 0x71ed4.

Definition sysconf30_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (t0 t1 t2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (lo : Z) (m : amem) : machine_state -> Prop :=
  fun ms' => exists a1 a2 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 4096) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom bsegs)
    /\ munch [(bv_unsigned sp - 544, bv_unsigned sp)] m m' /\ wmono bsegs m m' /\ mem_inv bsegs m'
    /\ stk bsegs m' lo (bv_unsigned sp).

Lemma sysconf30_spec : forall RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : amem) (lo : Z) (canary : word),
  mem_inv bsegs m ->
  stk bsegs m lo (bv_unsigned sp) -> ATOP <= lo -> lo <= bv_unsigned sp - 544 ->
  (forall i, ARELRO_LO <= i < ARELRO_HI -> m (wa i) = None) ->
  rw_cells bsegs m 0x67d0b8 [C8 canary] ->
  rw_cells bsegs m 0x67d338 [C8 (Z_to_bv 64 4096)] ->
  a0 = Z_to_bv 64 30 ->
  rng_aimg RNG -> rng RNG lo (bv_unsigned sp - lo) ->
  evtF bsegs RNG (sysconf30_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc t0 t1 t2 a3 a4 a5 a6 a7 t3 t4 t5 t6 lo m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 ASYSCONF) fc None m (seg_rom bsegs)).
Proof.
  intros until canary. intros MI ST CEIL LO RR CAN PGS -> RIMG RSTK.
  unfold ASYSCONF, ARELRO_LO, ARELRO_HI in *.
  pose proof (munch_refl [(bv_unsigned sp - 544, bv_unsigned sp)] m) as MU. pose proof (wmono_refl bsegs m) as WM.
  assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
  assert (GCAN : rw_cells bsegs m 0xd2388 [C8 (Z_to_bv 64 0x67d0b8)]).
  { eapply rw_cells_recast; [apply (rw_cells_image0 bsegs m 0xd2388 (le8 (Z_to_bv 64 0x67d0b8)));
      [ intros a Ha; rewrite <- (Z_to_bv_bv_unsigned a); apply RR; rewrite length_le8 in Ha; lia
      | vm_compute; reflexivity | lia | rewrite length_le8; lia ] | cbn; split; exact I | reflexivity | reflexivity]. }
  assert (ROV : ro_cells bsegs m 0x27514 [CB 2 [Z_to_bv 8 4; Z_to_bv 8 255]]).
  { apply (ro_cells_image bsegs m); [exact MI | vm_compute; reflexivity | lia | cbn; lia]. }
  assert (ROJ : ro_cells bsegs m 0x274b0 [CB 4 [Z_to_bv 8 216; Z_to_bv 8 96; Z_to_bv 8 9; Z_to_bv 8 0]]).
  { apply (ro_cells_image bsegs m); [exact MI | vm_compute; reflexivity | lia | cbn; lia]. }
  carve_frame 32%nat ST. carve_frame 512%nat ST.
  do 4 zstep.
  zstep.
  zstep. zstep.
  zstep.
  zstep.
  zstep.
  zstep. if_cases Ka; zify_cond Ka; [exfalso; clear - Ka; lia|].
  zstep. zstep. zstep. zstep.
  zstep.
  zstep. if_lit.
  zstep. zstep. if_lit.
  zstep. zstep. zstep. if_lit.
  zstep. zstep. if_lit.
  zstep. zstep. zstep. zstep. if_lit.
  zstep. zstep. zstep. zstep.
  zstep.
  zstep. zstep. zstep.
  zstep.
  zstep. zstep. zstep.
  zstep. zstep.
  zstep. if_cases Kc; [zify_cond Kc; exfalso; apply Kc; reflexivity|].
  zstep. zstep. zstep. zstep. zstep.
  release_frame FR0 ST (bv_unsigned sp + -32). release_frame FR ST (bv_unsigned sp). finish.
Qed.

Lemma getmmapgran_spec : forall RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : amem) (lo : Z) (canary : word),
  mem_inv bsegs m ->
  stk bsegs m lo (bv_unsigned sp) -> ATOP <= lo -> lo <= bv_unsigned sp - 544 ->
  (forall i, ARELRO_LO <= i < ARELRO_HI -> m (wa i) = None) ->
  rw_cells bsegs m 0x67d0b8 [C8 canary] ->
  rw_cells bsegs m 0x67d338 [C8 (Z_to_bv 64 4096)] ->
  rng_aimg RNG -> rng RNG lo (bv_unsigned sp - lo) ->
  evtF bsegs RNG (sysconf30_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc t0 t1 t2 a3 a4 a5 a6 a7 t3 t4 t5 t6 lo m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 AGETMMAPGRAN) fc None m (seg_rom bsegs)).
Proof.
  intros until canary. intros MI ST CEIL LO RR CAN PGS RIMG RSTK. unfold AGETMMAPGRAN.
  zstep. zstep.
  zstep.
  eapply sysconf30_spec; try eassumption; reflexivity.
Qed.
End CANSEC1.
