(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.jsoncons.fuzz_bigint.images Require Import Asan.
From LinuxProcessSemantics.LinuxProcessSem Require Import State Run.
From OSSVerify.Proofs.jsoncons.fuzz_bigint.lib Require Import PropExec CatExec CatSim SeqExec As0_code_92368_93368 As0_code_93368_94368.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Abbreviation RSEGS := Asan.M.loaded_segments.

Lemma u64_small : forall z, 0 <= z < 2 ^ 64 -> bv_unsigned (Z_to_bv 64 z) = z.
Proof. intros z Hz. rewrite Z_to_bv_unsigned. apply bv_wrap_small. unfold bv_modulus. lia. Qed.

Section Clz.
  Context {fx : PropExec.FPState}.
  Variable mem rom : word -> option byte.

  (* [comment removed for export] *)
  Lemma clz_iter : forall (R : bvmap 5 word) (y : Z) (k : Z),
    getr R (10%bv : reg) = Z_to_bv 64 y -> getr R (11%bv : reg) = Z_to_bv 64 k ->
    0 <= y < 2 ^ 63 -> 0 <= k < 1000 ->
    msteps RSEGS (@mkst fx R (0x93364%bv : word) mem rom)
                 (@mkst fx (regupd (regupd R 10%bv (Z_to_bv 64 (2 * y))) 11%bv (Z_to_bv 64 (k + 1)))
                           (if Z.ltb (2 * y) (2 ^ 63) then (0x93364%bv : word) else (0x93370%bv : word)) mem rom).
  Proof.
    intros R y k Ha0 Ha1 Hy Hk.
    assert (Hsll : v_slli (getr R 10%bv) (bv_unsigned (1%bv : bv 6)) = Z_to_bv 64 (2 * y)).
    { rewrite Ha0. unfold v_slli. apply bv_eq. rewrite !Z_to_bv_unsigned.
      change (bv_unsigned (1%bv : bv 6)) with 1. rewrite Z.shiftl_mul_pow2 by lia.
      rewrite (bv_wrap_small 64 y) by (unfold bv_modulus; lia). f_equal. lia. }
    eapply mst_step; [reflexivity | eapply (step_slli RSEGS R _ mem rom _ 10%bv 10%bv 1%bv F_93364 eq_refl D_93364) |].
    cbn [bv_eqb]. rewrite Hsll.
    set (R1 := regupd R 10%bv (Z_to_bv 64 (2 * y))).
    assert (Ha1' : getr R1 11%bv = Z_to_bv 64 k) by (subst R1; rewrite getr_other by (intro X; discriminate X); exact Ha1).
    assert (Haddiw : v_addiw (getr R1 11%bv) (bv_signed (1%bv : bv 12)) = Z_to_bv 64 (k + 1)).
    { rewrite Ha1'. change (bv_signed (1%bv : bv 12)) with 1. unfold v_addiw. f_equal.
      rewrite u64_small by lia. apply bv_swrap_small.
      change (bv_half_modulus 32) with (2 ^ 31). lia. }
    replace (v_addi (0x93364%bv : word) 4) with (0x93368%bv : word) by (apply bv_eq; reflexivity).
    eapply mst_step; [reflexivity | eapply (step_addiw RSEGS R1 _ mem rom _ 11%bv 11%bv 1%bv F_93368 eq_refl D_93368) |].
    cbn [bv_eqb]. rewrite Haddiw.
    set (R' := regupd R1 11%bv (Z_to_bv 64 (k + 1))).
    replace (v_addi (0x93368%bv : word) 4) with (0x9336c%bv : word) by (apply bv_eq; reflexivity).
    assert (Ha0' : getr R' 10%bv = Z_to_bv 64 (2 * y)).
    { subst R' R1. rewrite getr_other by (intro X; discriminate X). apply getr_same. intro X; discriminate X. }
    pose proof (getr_zero R') as Hx0.
    destruct (Z.ltb (2 * y) (2 ^ 63)) eqn:Hlt.
    - apply Z.ltb_lt in Hlt.
      eapply mst_step; [reflexivity | eapply (step_bge_tk RSEGS R' _ mem rom _ 10%bv 0%bv _ F_9336c eq_refl D_9336c) |].
      { rewrite Hx0. apply c_lts_pos_0. rewrite Ha0', u64_small; lia. }
      replace (btgt (0x9336c%bv : word) (bv_signed (8184%bv : bv 13))) with (0x93364%bv : word) by (apply bv_eq; vm_compute; reflexivity).
      apply mst_refl.
    - apply Z.ltb_ge in Hlt.
      eapply mst_step; [reflexivity | eapply (step_bge_ft RSEGS R' _ mem rom _ 10%bv 0%bv _ F_9336c eq_refl D_9336c) |].
      { rewrite Hx0. apply c_lts_neg_0. rewrite Ha0', u64_small; lia. }
      replace (v_addi (0x9336c%bv : word) 4) with (0x93370%bv : word) by (apply bv_eq; reflexivity).
      apply mst_refl.
  Qed.

  (* [comment removed for export] *)
  Lemma clz_run : forall (n : nat) (R : bvmap 5 word) (y k : Z),
    getr R (10%bv : reg) = Z_to_bv 64 y -> getr R (11%bv : reg) = Z_to_bv 64 k ->
    1 <= y < 2 ^ 63 -> 0 <= k -> k + Z.of_nat n <= 100 -> 2 ^ 63 <= y * 2 ^ (Z.of_nat n) ->
    exists (c : Z) (R' : bvmap 5 word),
      1 <= c <= Z.of_nat n /\ 2 ^ 63 <= y * 2 ^ c < 2 ^ 64
      /\ getr R' (10%bv : reg) = Z_to_bv 64 (y * 2 ^ c) /\ getr R' (11%bv : reg) = Z_to_bv 64 (k + c)
      /\ (forall r : reg, r <> 10%bv -> r <> 11%bv -> getr R' r = getr R r)
      /\ msteps RSEGS (@mkst fx R (0x93364%bv : word) mem rom) (@mkst fx R' (0x93370%bv : word) mem rom).
  Proof.
    induction n as [|n IH]; intros R y k Ha0 Ha1 Hy Hk Hkn Hn.
    - rewrite Z.pow_0_r in Hn. lia.
    - pose proof (clz_iter R y k Ha0 Ha1 ltac:(lia) ltac:(lia)) as STEP.
      set (R1 := regupd (regupd R 10%bv (Z_to_bv 64 (2 * y))) 11%bv (Z_to_bv 64 (k + 1))) in STEP.
      assert (G0 : getr R1 10%bv = Z_to_bv 64 (2 * y)).
      { subst R1. rewrite getr_other by (intro X; discriminate X). apply getr_same. intro X; discriminate X. }
      assert (G1 : getr R1 11%bv = Z_to_bv 64 (k + 1)) by (subst R1; apply getr_same; intro X; discriminate X).
      assert (GR : forall r : reg, r <> 10%bv -> r <> 11%bv -> getr R1 r = getr R r).
      { intros r H10 H11. subst R1. rewrite getr_other by exact H11. rewrite getr_other by exact H10. reflexivity. }
      destruct (Z.ltb (2 * y) (2 ^ 63)) eqn:Hlt.
      + apply Z.ltb_lt in Hlt.
        assert (Hn' : 2 ^ 63 <= 2 * y * 2 ^ Z.of_nat n).
        { rewrite Nat2Z.inj_succ, Z.pow_succ_r in Hn by lia. lia. }
        destruct (IH R1 (2 * y) (k + 1) G0 G1 ltac:(lia) ltac:(lia) ltac:(lia) Hn') as (c & R' & Hc & Hr & Q0 & Q1 & QR & MS).
        exists (c + 1), R'. split; [lia|]. split.
        { rewrite Z.pow_add_r, Z.pow_1_r by lia. lia. }
        split; [rewrite Q0; f_equal; rewrite Z.pow_add_r, Z.pow_1_r by lia; lia|].
        split; [rewrite Q1; f_equal; lia|].
        split; [intros r H10 H11; rewrite (QR r H10 H11); exact (GR r H10 H11)|].
        eapply msteps_trans; [exact STEP | exact MS].
      + apply Z.ltb_ge in Hlt. exists 1, R1. split; [lia|]. split; [rewrite Z.pow_1_r; lia|].
        split; [rewrite G0; f_equal; rewrite Z.pow_1_r; lia|]. split; [exact G1|]. split; [exact GR|]. exact STEP.
  Qed.

  (* [comment removed for export] *)
  Theorem clz_loop : forall (R : bvmap 5 word) (y k : Z),
    getr R (10%bv : reg) = Z_to_bv 64 y -> getr R (11%bv : reg) = Z_to_bv 64 k ->
    1 <= y < 2 ^ 63 -> 0 <= k <= 37 ->
    exists (c : Z) (R' : bvmap 5 word),
      1 <= c <= 63 /\ 2 ^ 63 <= y * 2 ^ c < 2 ^ 64
      /\ getr R' (10%bv : reg) = Z_to_bv 64 (y * 2 ^ c) /\ getr R' (11%bv : reg) = Z_to_bv 64 (k + c)
      /\ (forall r : reg, r <> 10%bv -> r <> 11%bv -> getr R' r = getr R r)
      /\ msteps RSEGS (@mkst fx R (0x93364%bv : word) mem rom) (@mkst fx R' (0x93370%bv : word) mem rom).
  Proof.
    intros R y k Ha0 Ha1 Hy Hk.
    destruct (clz_run 63 R y k Ha0 Ha1 Hy ltac:(lia) ltac:(cbn; lia)) as (c & R' & Hc & X).
    { change (Z.of_nat 63) with 63. assert (2 ^ 63 <= 2 ^ 63 * y) by (apply Z.le_mul_diag_r || idtac; nia). nia. }
    exists c, R'. split; [cbn in Hc; lia | exact X].
  Qed.
End Clz.
