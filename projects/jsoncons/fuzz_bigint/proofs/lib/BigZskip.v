(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.jsoncons.fuzz_bigint.images Require Import Plain.
From OSSVerify.Proofs.jsoncons.fuzz_bigint.lib Require Import PropExec CatExec CatSim SeqExec BigClz Src0_code_20088_210bc.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Abbreviation RSEGS := Plain.M.loaded_segments.

Section Zskip.
  Context {fx : PropExec.FPState}.
  Variable mem rom : word -> option byte.
  Variable p m : Z.
  Variable bs : list Z.        (* [comment removed for export] *)
  Hypothesis Hm : Z.of_nat (length bs) = m.
  Hypothesis Hp : 4096 <= p /\ p + m <= 2 ^ 63.
  Hypothesis Hrd : forall i : nat, (i < length bs)%nat -> rdn RSEGS mem (Z_to_bv 64 (p + Z.of_nat i)) 1 = Some [Z_to_bv 8 (nth i bs 0)].
  Hypothesis Hb : forall i : nat, (i < length bs)%nat -> 0 <= nth i bs 0 < 256.

  (* [comment removed for export] *)
  Lemma zskip_step : forall (R : bvmap 5 word) (i : nat),
    getr R (10%bv : reg) = Z_to_bv 64 (p + Z.of_nat i) -> getr R (8%bv : reg) = Z_to_bv 64 (p + m) -> getr R (11%bv : reg) = Z_to_bv 64 48 ->
    (S i < length bs)%nat -> nth i bs 0 = 48 ->
    msteps RSEGS (@mkst fx R (0x20bf4%bv : word) mem rom)
                 (@mkst fx (regupd (regupd R 12%bv (Z_to_bv 64 48)) 10%bv (Z_to_bv 64 (p + Z.of_nat (S i)))) (0x20bf4%bv : word) mem rom).
  Proof.
    intros R i Ha0 Hs0 Ha1 Hi Hz.
    eapply mst_step; [reflexivity | eapply (step_lbu RSEGS R _ mem rom _ 12%bv 10%bv 0%bv _ F_20bf4 eq_refl D_20bf4) |].
    { rewrite Ha0. change (bv_signed (0%bv : bv 12)) with 0. unfold v_addi. rewrite u64_small, Z.add_0_r by lia. apply Hrd. lia. }
    cbn [bv_eqb]. rewrite Hz. change (bv_unsigned (Z_to_bv 8 48)) with 48.
    replace (v_addi (0x20bf4%bv : word) 4) with (0x20bf8%bv : word) by (apply bv_eq; reflexivity).
    set (R1 := regupd R 12%bv (Z_to_bv 64 48)).
    eapply mst_step; [reflexivity | eapply (step_bne_ft RSEGS R1 _ mem rom _ 12%bv 11%bv _ F_20bf8 eq_refl D_20bf8) |].
    { subst R1. rewrite getr_same by (intro X; discriminate X). rewrite getr_other by (intro X; discriminate X). rewrite Ha1. apply c_eq_refl. }
    replace (v_addi (0x20bf8%bv : word) 4) with (0x20bfc%bv : word) by (apply bv_eq; reflexivity).
    eapply mst_step; [reflexivity | eapply (step_addi RSEGS R1 _ mem rom _ 10%bv 10%bv 1%bv F_20bfc eq_refl D_20bfc) |].
    cbn [bv_eqb].
    assert (Ha0' : v_addi (getr R1 10%bv) (bv_signed (1%bv : bv 12)) = Z_to_bv 64 (p + Z.of_nat (S i))).
    { subst R1. rewrite getr_other by (intro X; discriminate X). rewrite Ha0. change (bv_signed (1%bv : bv 12)) with 1.
      unfold v_addi. rewrite u64_small by lia. f_equal. lia. }
    rewrite Ha0'. set (R2 := regupd R1 10%bv (Z_to_bv 64 (p + Z.of_nat (S i)))).
    replace (v_addi (0x20bfc%bv : word) 4) with (0x20c00%bv : word) by (apply bv_eq; reflexivity).
    eapply mst_step; [reflexivity | eapply (step_bltu_tk RSEGS R2 _ mem rom _ 10%bv 8%bv _ F_20c00 eq_refl D_20c00) |].
    { subst R2 R1. rewrite getr_same by (intro X; discriminate X). rewrite !getr_other by (intro X; discriminate X). rewrite Hs0.
      unfold c_ltu, bv_ltu. rewrite !u64_small by lia. apply Z.ltb_lt. lia. }
    replace (btgt (0x20c00%bv : word) (bv_signed (8180%bv : bv 13))) with (0x20bf4%bv : word) by (apply bv_eq; vm_compute; reflexivity).
    apply mst_refl.
  Qed.

  (* [comment removed for export] *)
  Lemma zskip_last : forall (R : bvmap 5 word) (z : nat),
    getr R (10%bv : reg) = Z_to_bv 64 (p + Z.of_nat z) -> getr R (11%bv : reg) = Z_to_bv 64 48 ->
    (z < length bs)%nat -> nth z bs 0 <> 48 ->
    msteps RSEGS (@mkst fx R (0x20bf4%bv : word) mem rom)
                 (@mkst fx (regupd R 12%bv (Z_to_bv 64 (nth z bs 0))) (0x20c04%bv : word) mem rom).
  Proof.
    intros R z Ha0 Ha1 Hz Hnz.
    eapply mst_step; [reflexivity | eapply (step_lbu RSEGS R _ mem rom _ 12%bv 10%bv 0%bv _ F_20bf4 eq_refl D_20bf4) |].
    { rewrite Ha0. change (bv_signed (0%bv : bv 12)) with 0. unfold v_addi. rewrite u64_small, Z.add_0_r by lia. apply Hrd. lia. }
    cbn [bv_eqb]. pose proof (Hb z Hz) as Bz.
    rewrite (u64_small (nth z bs 0)) || rewrite BigClz.u64_small || idtac.
    all: cycle 1. all: try lia.
    replace (bv_unsigned (Z_to_bv 8 (nth z bs 0))) with (nth z bs 0).
    2:{ symmetry. rewrite Z_to_bv_unsigned. apply bv_wrap_small. unfold bv_modulus. lia. }
    replace (v_addi (0x20bf4%bv : word) 4) with (0x20bf8%bv : word) by (apply bv_eq; reflexivity).
    set (R1 := regupd R 12%bv (Z_to_bv 64 (nth z bs 0))).
    eapply mst_step; [reflexivity | eapply (step_bne_tk RSEGS R1 _ mem rom _ 12%bv 11%bv _ F_20bf8 eq_refl D_20bf8) |].
    { subst R1. rewrite getr_same by (intro X; discriminate X). rewrite getr_other by (intro X; discriminate X). rewrite Ha1.
      apply c_eq_neq. rewrite !u64_small; lia. }
    replace (btgt (0x20bf8%bv : word) (bv_signed (12%bv : bv 13))) with (0x20c04%bv : word) by (apply bv_eq; vm_compute; reflexivity).
    apply mst_refl.
  Qed.

  (* [comment removed for export] *)
  Lemma zskip_run : forall (k : nat) (R : bvmap 5 word) (i z : nat),
    (z = i + k)%nat ->
    getr R (10%bv : reg) = Z_to_bv 64 (p + Z.of_nat i) -> getr R (8%bv : reg) = Z_to_bv 64 (p + m) -> getr R (11%bv : reg) = Z_to_bv 64 48 ->
    (z < length bs)%nat -> (forall j : nat, (i <= j < z)%nat -> nth j bs 0 = 48) -> nth z bs 0 <> 48 ->
    exists R' : bvmap 5 word,
      msteps RSEGS (@mkst fx R (0x20bf4%bv : word) mem rom) (@mkst fx R' (0x20c04%bv : word) mem rom)
      /\ getr R' (10%bv : reg) = Z_to_bv 64 (p + Z.of_nat z) /\ getr R' (12%bv : reg) = Z_to_bv 64 (nth z bs 0)
      /\ (forall r : reg, r <> 10%bv -> r <> 12%bv -> getr R' r = getr R r).
  Proof.
    induction k as [|k IH]; intros R i z Hzk Ha0 Hs0 Ha1 Hz Hzero Hnz.
    - rewrite Nat.add_0_r in Hzk. subst z.
      exists (regupd R 12%bv (Z_to_bv 64 (nth i bs 0))). split; [exact (zskip_last R i Ha0 Ha1 Hz Hnz)|].
      split; [rewrite getr_other by (intro X; discriminate X); exact Ha0|].
      split; [apply getr_same; intro X; discriminate X|].
      intros r H10 H12. rewrite getr_other by exact H12. reflexivity.
    - pose proof (zskip_step R i Ha0 Hs0 Ha1 ltac:(lia) (Hzero i ltac:(lia))) as STEP.
      set (R1 := regupd (regupd R 12%bv (Z_to_bv 64 48)) 10%bv (Z_to_bv 64 (p + Z.of_nat (S i)))) in STEP.
      destruct (IH R1 (S i) z ltac:(lia)) as (R' & MS & Q10 & Q12 & QR).
      { subst R1. apply getr_same. intro X; discriminate X. }
      { subst R1. rewrite !getr_other by (intro X; discriminate X). exact Hs0. }
      { subst R1. rewrite !getr_other by (intro X; discriminate X). exact Ha1. }
      { exact Hz. } { intros j Hj. apply Hzero. lia. } { exact Hnz. }
      exists R'. split; [eapply msteps_trans; [exact STEP | exact MS]|]. split; [exact Q10|]. split; [exact Q12|].
      intros r H10 H12. rewrite (QR r H10 H12). subst R1. rewrite getr_other by exact H10. rewrite getr_other by exact H12. reflexivity.
  Qed.

  Theorem zskip_loop : forall (R : bvmap 5 word) (z : nat),
    getr R (10%bv : reg) = Z_to_bv 64 p -> getr R (8%bv : reg) = Z_to_bv 64 (p + m) -> getr R (11%bv : reg) = Z_to_bv 64 48 ->
    (z < length bs)%nat -> (forall j : nat, (j < z)%nat -> nth j bs 0 = 48) -> nth z bs 0 <> 48 ->
    exists R' : bvmap 5 word,
      msteps RSEGS (@mkst fx R (0x20bf4%bv : word) mem rom) (@mkst fx R' (0x20c04%bv : word) mem rom)
      /\ getr R' (10%bv : reg) = Z_to_bv 64 (p + Z.of_nat z) /\ getr R' (12%bv : reg) = Z_to_bv 64 (nth z bs 0)
      /\ (forall r : reg, r <> 10%bv -> r <> 12%bv -> getr R' r = getr R r).
  Proof.
    intros R z Ha0 Hs0 Ha1 Hz Hzero Hnz. apply (zskip_run z R 0%nat z eq_refl); try assumption.
    - rewrite Z.add_0_r. exact Ha0.
    - intros j Hj. apply Hzero. lia.
  Qed.
End Zskip.
