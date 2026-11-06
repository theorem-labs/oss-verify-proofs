(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib Require Import Arr InitMem.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Common Require Import StrFun.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec Require Import AsanCtrl AsanEmbed.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW Require Import AImg ABase AQConst ABytes.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALibA Require Import StepF.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW Require Import AKit AKit2 AKitQ.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Common Require Import RunDraw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Section CANSEC1. Context {rc : runConstT}.
Definition putA_post (sp gp tp s7 s8 s9 s10 s11 ra s0 s1 s2 s3 s4 s5 s6 a2 a3 : word) (F : bvmap 5 word) (fc : bv 32)
    (t hm n lo : Z) (m : amem) : machine_state -> Prop :=
  fun ms' => exists (t0 t1 t2 a4 a5 a6 a7 t3 t4 t5 t6 : word) m',
    ms' = MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -80)) gp tp t0 t1 t2
                  (Z_to_bv 64 0xd6730) (Z_to_bv 64 (t + 80))
                  (Z_to_bv 64 (hm + 16)) (Z_to_bv 64 (rup n 8)) (Z_to_bv 64 253) (Z_to_bv 64 0) a4 a5 a6 a7
                  (Z_to_bv 64 n) a3 a2 (Z_to_bv 64 hm) (Z_to_bv 64 0x100000) s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (Z_to_bv 64 0x41214) fc None m' (seg_rom asegs)
    /\ munch [(bv_unsigned sp - 80, bv_unsigned sp)]%Z m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ stk asegs m' lo (bv_unsigned sp + -80)
    /\ rw_cells asegs m' (bv_unsigned sp + -80) [C8 a2; C8 a3; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].

Lemma putA_spec : forall (t hm n : Z) RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : amem) (lo stb b1 ctx : Z),
  stk asegs m lo (bv_unsigned sp) -> ATOP <= lo -> lo <= bv_unsigned sp - 80 ->
  mem_inv asegs m ->
  a0 = Z_to_bv 64 AQUAR_Q -> a1 = Z_to_bv 64 (t + 80) -> a4 = Z_to_bv 64 hm -> a5 = Z_to_bv 64 n ->
  rw_cells asegs m AQ_MAX [C8 (Z_to_bv 64 Q_MAX); C8 (Z_to_bv 64 Q_MIN); C8 (Z_to_bv 64 Q_CACHE)] ->
  rw_cells asegs m 0xd1510 [C8 (Z_to_bv 64 AFLAGS)] ->
  rw_cells asegs m 0xd72e4 [C4 (Z_to_bv 64 0x1000); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0xbe)] ->
  rw_cells asegs m hm [C1 (Z_to_bv 8 stb); C1 (Z_to_bv 8 b1); C2 (Z_to_bv 64 0); C4 (Z_to_bv 64 n); C8 (Z_to_bv 64 ctx)] ->
  0 <= n <= Q_MAX -> AIMG_HI <= hm -> hm + 16 <= ATOP ->
  rng_aimg RNG -> rng RNG lo (bv_unsigned sp - lo) -> rng RNG hm 16 ->
  evtF asegs RNG (putA_post sp gp tp s7 s8 s9 s10 s11 ra s0 s1 s2 s3 s4 s5 s6 a2 a3 F fc t hm n lo m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x4108c) fc None m (seg_rom asegs)).
Proof.
  intros until ctx. intros ST CEIL LO MI -> -> -> -> QK GF FL HD N H0 H1 RIMG RSTK RH.
  unfold AIMG_HI, AQUAR_Q, AQ_MAX, AFLAGS, Q_MAX, Q_MIN, Q_CACHE in *.
  pose proof (munch_refl [(bv_unsigned sp - 80, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl asegs m) as WM.
  word_range sp SPR.
  carve_frame 80%nat ST.
  do 9 step.
  step. step. step.
  step. step. step. if_lit.
  step. step. if_cases K0; zify_cond K0; [|exfalso; lia].
  step. step. step.
  step. step. lstep. step. if_lit.
  lstep. lstep. zstep. zstep. zstep.
  rewrite Z.lor_0_l.
  zstep. zstep.
  change 18446744073709551608 with (2^64 - 2^3). rewrite land_align_down by lia.
  setreg 11%Z (Z_to_bv 64 (rup n 8)) ltac:(f_equal; unfold rup; Z.div_mod_to_equations; lia).
  step. step.
  unfold putA_post. finish.
Qed.
End CANSEC1.

From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.BothW Require Import BImg.
Module TwinB.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Arr OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.InitMem.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Common.StrFun.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec.AsanCtrl OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec.AsanEmbed.
Import ABase.TwinB AQConst.TwinB ABytes.TwinB.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALibA.StepF.
Import AKit.TwinB AKit2.TwinB AKitQ.TwinB.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Common.RunDraw.

Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Section CANSEC1. Context {rc : runConstT}.
Definition putA_post (sp gp tp s7 s8 s9 s10 s11 ra s0 s1 s2 s3 s4 s5 s6 a2 a3 : word) (F : bvmap 5 word) (fc : bv 32)
    (t hm n lo : Z) (m : amem) : machine_state -> Prop :=
  fun ms' => exists (t0 t1 t2 a4 a5 a6 a7 t3 t4 t5 t6 : word) m',
    ms' = MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -80)) gp tp t0 t1 t2
                  (Z_to_bv 64 0xd88f0) (Z_to_bv 64 (t + 80))
                  (Z_to_bv 64 (hm + 16)) (Z_to_bv 64 (rup n 8)) (Z_to_bv 64 253) (Z_to_bv 64 0) a4 a5 a6 a7
                  (Z_to_bv 64 n) a3 a2 (Z_to_bv 64 hm) (Z_to_bv 64 0x100000) s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (Z_to_bv 64 0x41ba4) fc None m' (seg_rom bsegs)
    /\ munch [(bv_unsigned sp - 80, bv_unsigned sp)]%Z m m' /\ wmono bsegs m m' /\ mem_inv bsegs m'
    /\ stk bsegs m' lo (bv_unsigned sp + -80)
    /\ rw_cells bsegs m' (bv_unsigned sp + -80) [C8 a2; C8 a3; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].

Lemma putA_spec : forall (t hm n : Z) RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : amem) (lo stb b1 ctx : Z),
  stk bsegs m lo (bv_unsigned sp) -> ATOP <= lo -> lo <= bv_unsigned sp - 80 ->
  mem_inv bsegs m ->
  a0 = Z_to_bv 64 AQUAR_Q -> a1 = Z_to_bv 64 (t + 80) -> a4 = Z_to_bv 64 hm -> a5 = Z_to_bv 64 n ->
  rw_cells bsegs m AQ_MAX [C8 (Z_to_bv 64 Q_MAX); C8 (Z_to_bv 64 Q_MIN); C8 (Z_to_bv 64 Q_CACHE)] ->
  rw_cells bsegs m 0xd3628 [C8 (Z_to_bv 64 AFLAGS)] ->
  rw_cells bsegs m 0xd94a4 [C4 (Z_to_bv 64 0x1000); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0xbe)] ->
  rw_cells bsegs m hm [C1 (Z_to_bv 8 stb); C1 (Z_to_bv 8 b1); C2 (Z_to_bv 64 0); C4 (Z_to_bv 64 n); C8 (Z_to_bv 64 ctx)] ->
  0 <= n <= Q_MAX -> AIMG_HI <= hm -> hm + 16 <= ATOP ->
  rng_aimg RNG -> rng RNG lo (bv_unsigned sp - lo) -> rng RNG hm 16 ->
  evtF bsegs RNG (putA_post sp gp tp s7 s8 s9 s10 s11 ra s0 s1 s2 s3 s4 s5 s6 a2 a3 F fc t hm n lo m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x41a1c) fc None m (seg_rom bsegs)).
Proof.
  intros until ctx. intros ST CEIL LO MI -> -> -> -> QK GF FL HD N H0 H1 RIMG RSTK RH.
  unfold AIMG_HI, AQUAR_Q, AQ_MAX, AFLAGS, Q_MAX, Q_MIN, Q_CACHE in *.
  pose proof (munch_refl [(bv_unsigned sp - 80, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl bsegs m) as WM.
  word_range sp SPR.
  carve_frame 80%nat ST.
  do 9 step.
  step. step. step.
  step. step. step. if_lit.
  step. step. if_cases K0; zify_cond K0; [|exfalso; lia].
  step. step. step.
  step. step. lstep. step. if_lit.
  lstep. lstep. zstep. zstep. zstep.
  rewrite Z.lor_0_l.
  zstep. zstep.
  change 18446744073709551608 with (2^64 - 2^3). rewrite land_align_down by lia.
  setreg 11%Z (Z_to_bv 64 (rup n 8)) ltac:(f_equal; unfold rup; Z.div_mod_to_equations; lia).
  step. step.
  unfold putA_post. finish.
Qed.
End CANSEC1.
End TwinB.
