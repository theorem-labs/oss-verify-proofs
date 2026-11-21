(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.asan_ca_sound.Lib Require Import Arr Bytes ZBridge.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.asan_ca_sound.cks Require Import CkTables CkModel CkMathAdler CkWalk.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.asan_ca_sound.CkA Require Import CkAImg CkATables CkAShadow CkAIface CkAKit AdlAGlue AdlACGlue.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.asan_ca_sound.LibA Require Import Shadow.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.asan_ca_sound.LibA Require Import StepF.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Theorem adler32_combine_proofA : adler32_combine_stmtA.
Proof.
  intros RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
         FR fc m ad1 ad2 len2 MI A0 A1 A2 R1 R2 RL RI.
  subst a0 a1 a2. unfold ACK_ADLCOMB.
  pose proof (c_lo1_range ad1) as L1. pose proof (c_lo2_range ad2) as L2.
  pose proof (c_hi1_range ad1) as H1. pose proof (c_hi2_range ad2) as H2.
  unfold c_lo1, c_lo2, c_hi1, c_hi2 in *.
  zstep. if_cases KN; zify_cond KN. { exfalso. lia. }
  do 7 zstep.
  rewrite !hi16_mach by lia.
  do 7 zstep.
  change (Z.land ad1 65535) with (lo16 ad1). change (Z.land ad2 65535) with (lo16 ad2).
  zstep.
  setreg 10 (Z_to_bv 64 (amag_t len2)) ltac:(f_equal; symmetry; apply amag_t_mach; lia).
  pose proof (amag_t_range len2 ltac:(lia)) as TR. pose proof (amag_v_range len2 ltac:(lia)) as VR.
  pose proof (amag_q_range len2 ltac:(lia)) as QR. unfold amag_q in QR.
  do 8 zstep.
  do 3 zstep.
  setreg 12 (Z_to_bv 64 (c_rem len2)) ltac:(unfold c_rem, amag_q; reflexivity).
  pose proof (c_rem_range len2 RL) as RR. pose proof (c_pr_range ad1 len2 RL) as PR.
  zstep.
  setreg 11 (Z_to_bv 64 (c_pr ad1 len2)) ltac:(f_equal; unfold c_pr, c_lo1; symmetry; apply Z.mod_small; unfold c_pr, c_lo1 in PR; lia).
  do 3 zstep.
  setreg 14 (Z_to_bv 64 (c_q2 ad1 len2)) ltac:(unfold c_q2; reflexivity).
  pose proof (c_q2_range ad1 len2 RL) as Q2R. pose proof (c_s2m_range ad1 len2 RL) as SMR.
  do 4 zstep.
  setreg 11 (Z_to_bv 64 (c_s2m ad1 len2)) ltac:(f_equal; unfold c_s2m; symmetry; apply zext_swrap32_small; unfold c_s2m in SMR; lia).
  do 3 zstep.
  set (S1 := lo16 ad1 + lo16 ad2 + 65520) in *.
  set (S2 := hi16 ad1 + hi16 ad2 + 65535 - c_rem len2 + c_s2m ad1 len2 + -14) in *.
  assert (S1R : 65520 <= S1 < 2^18) by (subst S1; lia).
  assert (S2R : 0 <= S2 < 2^18) by (subst S2; lia).
  assert (MODEL : forall c1, c1 = (if 65520 <? S1 then S1 - 65521 else S1) ->
            Z.lor (csub (if 131041 <? S2 then S2 - 131042 else S2) * 65536) (csub c1) = adler32_combine_model ad1 ad2 len2).
  { intros c1 ->. rewrite <- (adlc_val_model ad1 ad2 len2 RL). unfold adlc_val, c_f2, c_f1, c_c2, c_c1.
    rewrite !csub_if. unfold c_S1, c_S2, c_lo1, c_lo2, c_hi1, c_hi2. subst S1 S2.
    replace (hi16 ad1 + hi16 ad2 + 65535 - c_rem len2 + c_s2m ad1 len2 + -14)
       with (hi16 ad1 + hi16 ad2 + 65535 - c_rem len2 + c_s2m ad1 len2 - 14) by lia. reflexivity. }
  zstep.
  if_cases KS; zify_cond KS.
  -
    zstep.
    setreg 13 (Z_to_bv 64 (S1 - 65521)) ltac:(f_equal; lia).
    set (C1 := S1 - 65521) in *.
    assert (C1R : 0 <= C1 < 2^18) by (subst C1; lia).
    do 5 zstep.
    setreg 12 (Z_to_bv 64 (csub C1)) ltac:(symmetry; apply csub_mach; lia).
    pose proof (csub_le C1 ltac:(lia)) as CL1.
    do 8 zstep.
    setreg 11 (Z_to_bv 64 (if 131041 <? S2 then S2 - 131042 else S2))
      ltac:(symmetry; apply (csel_mach S2 131041 18446744073709420574 131042); lia).
    set (C2 := if 131041 <? S2 then S2 - 131042 else S2) in *.
    assert (C2R : 0 <= C2 < 2^18) by (subst C2; destruct (131041 <? S2) eqn:E; [apply Z.ltb_lt in E|]; lia).
    do 6 zstep.
    setreg 10 (Z_to_bv 64 (csub C2 * 2^16)) ltac:(symmetry; apply csub16_mach; lia).
    pose proof (csub_le C2 ltac:(lia)) as CL2.
    zstep.
    setreg 10 (Z_to_bv 64 (adler32_combine_model ad1 ad2 len2)) ltac:(f_equal; symmetry; apply MODEL; subst C1; destruct (Z.ltb_spec 65520 S1); [reflexivity| lia]).
    zstep.
    apply evtF_done. hnf. repeat eexists.
  -
    do 2 zstep.
    set (C1 := 65520) in *.
    assert (C1R : 0 <= C1 < 2^18) by (subst C1; lia).
    do 5 zstep.
    setreg 12 (Z_to_bv 64 (csub C1)) ltac:(symmetry; apply csub_mach; lia).
    pose proof (csub_le C1 ltac:(lia)) as CL1.
    do 8 zstep.
    setreg 11 (Z_to_bv 64 (if 131041 <? S2 then S2 - 131042 else S2))
      ltac:(symmetry; apply (csel_mach S2 131041 18446744073709420574 131042); lia).
    set (C2 := if 131041 <? S2 then S2 - 131042 else S2) in *.
    assert (C2R : 0 <= C2 < 2^18) by (subst C2; destruct (131041 <? S2) eqn:E; [apply Z.ltb_lt in E|]; lia).
    do 6 zstep.
    setreg 10 (Z_to_bv 64 (csub C2 * 2^16)) ltac:(symmetry; apply csub16_mach; lia).
    pose proof (csub_le C2 ltac:(lia)) as CL2.
    zstep.
    setreg 10 (Z_to_bv 64 (adler32_combine_model ad1 ad2 len2)) ltac:(f_equal; symmetry; apply MODEL; subst C1; destruct (Z.ltb_spec 65520 S1); lia).
    zstep.
    apply evtF_done. hnf. repeat eexists.
Qed.
