(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.jsoncons.fuzz_bigint.images Require Import Ubsan.
From OSSVerify.Proofs.jsoncons.fuzz_bigint.lib Require Import PropExec CatExec CatSim SeqExec BigClz Ub0_code_221b0_23098.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Abbreviation RSEGS := Ubsan.M.loaded_segments.

Section Clz.
  Context {fx : PropExec.FPState}.
  Variable mem rom : word -> option byte.

  Ltac greg := repeat (first [ rewrite getr_same by (let X := fresh in intro X; discriminate X)
                             | rewrite getr_other by (let X := fresh in intro X; discriminate X) ]).

  (* [comment removed for export] *)
  Lemma clz_iter : forall (R : bvmap 5 word) (y : Z) (k : Z),
    getr R (10%bv : reg) = Z_to_bv 64 y -> getr R (11%bv : reg) = Z_to_bv 64 k ->
    0 <= y < 2 ^ 63 -> 0 <= k < 1000 ->
    msteps RSEGS (@mkst fx R (0x22d98%bv : word) mem rom)
                 (@mkst fx (regupd (regupd (regupd R 12%bv (Z_to_bv 64 k)) 11%bv (Z_to_bv 64 (k + 1))) 10%bv (Z_to_bv 64 (2 * y)))
                           (if Z.ltb (2 * y) (2 ^ 63) then (0x22d98%bv : word) else (0x22dac%bv : word)) mem rom).
  Proof.
    intros R y k Ha0 Ha1 Hy Hk.
    (* [comment removed for export] *)
    eapply mst_step; [reflexivity | eapply (step_addi RSEGS R _ mem rom _ 12%bv 11%bv 0%bv F_22d98 eq_refl D_22d98) |].
    cbn [bv_eqb].
    assert (E2 : v_addi (getr R 11%bv) (bv_signed (0%bv : bv 12)) = Z_to_bv 64 k).
    { rewrite Ha1. change (bv_signed (0%bv : bv 12)) with 0. unfold v_addi. rewrite u64_small, Z.add_0_r by lia. reflexivity. }
    rewrite E2. set (R1 := regupd R 12%bv (Z_to_bv 64 k)).
    replace (v_addi (0x22d98%bv : word) 4) with (0x22d9c%bv : word) by (apply bv_eq; reflexivity).
    (* [comment removed for export] *)
    eapply mst_step; [reflexivity | eapply (step_addiw RSEGS R1 _ mem rom _ 11%bv 11%bv 1%bv F_22d9c eq_refl D_22d9c) |].
    cbn [bv_eqb].
    assert (Haddiw : v_addiw (getr R1 11%bv) (bv_signed (1%bv : bv 12)) = Z_to_bv 64 (k + 1)).
    { subst R1. greg. rewrite Ha1. change (bv_signed (1%bv : bv 12)) with 1. unfold v_addiw. f_equal.
      rewrite u64_small by lia. apply bv_swrap_small. change (bv_half_modulus 32) with (2 ^ 31). lia. }
    rewrite Haddiw. set (R2 := regupd R1 11%bv (Z_to_bv 64 (k + 1))).
    replace (v_addi (0x22d9c%bv : word) 4) with (0x22da0%bv : word) by (apply bv_eq; reflexivity).
    (* [comment removed for export] *)
    eapply mst_step; [reflexivity | eapply (step_blt_ft RSEGS R2 _ mem rom _ 11%bv 12%bv _ F_22da0 eq_refl D_22da0) |].
    { subst R2 R1. greg. rewrite c_lts_small by (rewrite u64_small; lia). unfold bv_ltu. rewrite !u64_small by lia.
      apply Z.ltb_ge. lia. }
    replace (v_addi (0x22da0%bv : word) 4) with (0x22da4%bv : word) by (apply bv_eq; reflexivity).
    (* [comment removed for export] *)
    assert (Hsll : v_slli (getr R2 10%bv) (bv_unsigned (1%bv : bv 6)) = Z_to_bv 64 (2 * y)).
    { subst R2 R1. greg. rewrite Ha0. unfold v_slli. apply bv_eq. rewrite !Z_to_bv_unsigned.
      change (bv_unsigned (1%bv : bv 6)) with 1. rewrite Z.shiftl_mul_pow2 by lia.
      rewrite (bv_wrap_small 64 y) by (unfold bv_modulus; lia). f_equal. lia. }
    eapply mst_step; [reflexivity | eapply (step_slli RSEGS R2 _ mem rom _ 10%bv 10%bv 1%bv F_22da4 eq_refl D_22da4) |].
    cbn [bv_eqb]. rewrite Hsll.
    set (R' := regupd R2 10%bv (Z_to_bv 64 (2 * y))).
    replace (v_addi (0x22da4%bv : word) 4) with (0x22da8%bv : word) by (apply bv_eq; reflexivity).
    assert (Ha0' : getr R' 10%bv = Z_to_bv 64 (2 * y)) by (subst R'; apply getr_same; intro X; discriminate X).
    pose proof (getr_zero R') as Hx0.
    destruct (Z.ltb (2 * y) (2 ^ 63)) eqn:Hlt.
    - apply Z.ltb_lt in Hlt.
      eapply mst_step; [reflexivity | eapply (step_bge_tk RSEGS R' _ mem rom _ 10%bv 0%bv _ F_22da8 eq_refl D_22da8) |].
      { rewrite Hx0. apply c_lts_pos_0. rewrite Ha0', u64_small; lia. }
      replace (btgt (0x22da8%bv : word) (bv_signed (8176%bv : bv 13))) with (0x22d98%bv : word) by (apply bv_eq; vm_compute; reflexivity).
      subst R' R2 R1. apply mst_refl.
    - apply Z.ltb_ge in Hlt.
      eapply mst_step; [reflexivity | eapply (step_bge_ft RSEGS R' _ mem rom _ 10%bv 0%bv _ F_22da8 eq_refl D_22da8) |].
      { rewrite Hx0. apply c_lts_neg_0. rewrite Ha0', u64_small; lia. }
      replace (v_addi (0x22da8%bv : word) 4) with (0x22dac%bv : word) by (apply bv_eq; reflexivity).
      subst R' R2 R1. apply mst_refl.
  Qed.

  Lemma clz_run : forall (n : nat) (R : bvmap 5 word) (y k : Z),
    getr R (10%bv : reg) = Z_to_bv 64 y -> getr R (11%bv : reg) = Z_to_bv 64 k ->
    1 <= y < 2 ^ 63 -> 0 <= k -> k + Z.of_nat n <= 100 -> 2 ^ 63 <= y * 2 ^ (Z.of_nat n) ->
    exists (c : Z) (R' : bvmap 5 word),
      1 <= c <= Z.of_nat n /\ 2 ^ 63 <= y * 2 ^ c < 2 ^ 64
      /\ getr R' (10%bv : reg) = Z_to_bv 64 (y * 2 ^ c) /\ getr R' (11%bv : reg) = Z_to_bv 64 (k + c)
      /\ (forall r : reg, r <> 10%bv -> r <> 11%bv -> r <> 12%bv -> getr R' r = getr R r)
      /\ msteps RSEGS (@mkst fx R (0x22d98%bv : word) mem rom) (@mkst fx R' (0x22dac%bv : word) mem rom).
  Proof.
    induction n as [|n IH]; intros R y k Ha0 Ha1 Hy Hk Hkn Hn.
    - rewrite Z.pow_0_r in Hn. lia.
    - pose proof (clz_iter R y k Ha0 Ha1 ltac:(lia) ltac:(lia)) as STEP.
      set (R1 := regupd (regupd (regupd R 12%bv (Z_to_bv 64 k)) 11%bv (Z_to_bv 64 (k + 1))) 10%bv (Z_to_bv 64 (2 * y))) in STEP.
      assert (G0 : getr R1 10%bv = Z_to_bv 64 (2 * y)) by (subst R1; apply getr_same; intro X; discriminate X).
      assert (G1 : getr R1 11%bv = Z_to_bv 64 (k + 1)).
      { subst R1. rewrite getr_other by (intro X; discriminate X). apply getr_same. intro X; discriminate X. }
      assert (GR : forall r : reg, r <> 10%bv -> r <> 11%bv -> r <> 12%bv -> getr R1 r = getr R r).
      { intros r H10 H11 H12. subst R1. rewrite getr_other by exact H10. rewrite getr_other by exact H11. rewrite getr_other by exact H12. reflexivity. }
      destruct (Z.ltb (2 * y) (2 ^ 63)) eqn:Hlt.
      + apply Z.ltb_lt in Hlt.
        assert (Hn' : 2 ^ 63 <= 2 * y * 2 ^ Z.of_nat n).
        { rewrite Nat2Z.inj_succ, Z.pow_succ_r in Hn by lia. lia. }
        destruct (IH R1 (2 * y) (k + 1) G0 G1 ltac:(lia) ltac:(lia) ltac:(lia) Hn') as (c & R' & Hc & Hr & Q0 & Q1 & QR & MS).
        exists (c + 1), R'. split; [lia|]. split.
        { rewrite Z.pow_add_r, Z.pow_1_r by lia. lia. }
        split; [rewrite Q0; f_equal; rewrite Z.pow_add_r, Z.pow_1_r by lia; lia|].
        split; [rewrite Q1; f_equal; lia|].
        split; [intros r H10 H11 H12; rewrite (QR r H10 H11 H12); exact (GR r H10 H11 H12)|].
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
      /\ (forall r : reg, r <> 10%bv -> r <> 11%bv -> r <> 12%bv -> getr R' r = getr R r)
      /\ msteps RSEGS (@mkst fx R (0x22d98%bv : word) mem rom) (@mkst fx R' (0x22dac%bv : word) mem rom).
  Proof.
    intros R y k Ha0 Ha1 Hy Hk.
    destruct (clz_run 63 R y k Ha0 Ha1 Hy ltac:(lia) ltac:(cbn; lia)) as (c & R' & Hc & X).
    { change (Z.of_nat 63) with 63. assert (2 ^ 63 <= 2 ^ 63 * y) by (apply Z.le_mul_diag_r || idtac; nia). nia. }
    exists c, R'. split; [cbn in Hc; lia | exact X].
  Qed.
End Clz.
