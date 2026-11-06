(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.jsoncons.fuzz_bigint.images Require Import Ubsan.
From OSSVerify.Proofs.jsoncons.fuzz_bigint.lib Require Import PropExec CatExec CatSim SeqExec BigClz BigZskipUb0 Ub0_code_201fc_21084.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_bigint.lib.L5FastLia. Local Ltac lia := L5FastLia.plia.   (* [comment removed for export] *)
Open Scope Z_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Abbreviation RSEGS := Ubsan.M.loaded_segments.

Section ZskipAll.
  Context {fx : PropExec.FPState}.
  Variable mem rom : word -> option byte.
  Variable p m : Z.
  Variable bs : list Z.
  Hypothesis Hm : Z.of_nat (length bs) = m.
  Hypothesis Hp : 4096 <= p /\ p + m <= 2 ^ 63.
  Hypothesis Hrd : forall i : nat, (i < length bs)%nat -> rdn RSEGS mem (Z_to_bv 64 (p + Z.of_nat i)) 1 = Some [Z_to_bv 8 (nth i bs 0)].
  Hypothesis Hb : forall i : nat, (i < length bs)%nat -> 0 <= nth i bs 0 < 256.
  Hypothesis Hz : forall i : nat, (i < length bs)%nat -> nth i bs 0 = 48.

  (* [comment removed for export] *)
  Lemma zskip_final : forall (R : bvmap 5 word) (i : nat),
    getr R (10%bv : reg) = Z_to_bv 64 (p + Z.of_nat i) -> getr R (8%bv : reg) = Z_to_bv 64 (p + m) -> getr R (11%bv : reg) = Z_to_bv 64 48 ->
    getr R (12%bv : reg) = Z_to_bv 64 (2 ^ 64 - 1) ->
    (S i = length bs)%nat ->
    msteps RSEGS (@mkst fx R (0x20f00%bv : word) mem rom)
                 (@mkst fx (regupd (regupd R 13%bv (Z_to_bv 64 48)) 10%bv (Z_to_bv 64 (p + m))) (0x20f14%bv : word) mem rom).
  Proof.
    intros R i Ha0 Hs0 Ha1 Ha2 Hi.
    eapply mst_step; [reflexivity | eapply (step_lbu RSEGS R _ mem rom _ 13%bv 10%bv 0%bv _ F_20f00 eq_refl D_20f00) |].
    { rewrite Ha0. change (bv_signed (0%bv : bv 12)) with 0. unfold v_addi. rewrite u64_small, Z.add_0_r by lia. apply Hrd. lia. }
    cbn [bv_eqb]. rewrite (Hz i) by lia. change (bv_unsigned (Z_to_bv 8 48)) with 48.
    replace (v_addi (0x20f00%bv : word) 4) with (0x20f04%bv : word) by (apply bv_eq; reflexivity).
    set (R1 := regupd R 13%bv (Z_to_bv 64 48)).
    eapply mst_step; [reflexivity | eapply (step_bne_ft RSEGS R1 _ mem rom _ 13%bv 11%bv _ F_20f04 eq_refl D_20f04) |].
    { subst R1. rewrite getr_same by (intro X; discriminate X). rewrite getr_other by (intro X; discriminate X). rewrite Ha1. apply c_eq_refl. }
    replace (v_addi (0x20f04%bv : word) 4) with (0x20f08%bv : word) by (apply bv_eq; reflexivity).
    (* [comment removed for export] *)
    eapply mst_step; [reflexivity | eapply (step_beq_ft RSEGS R1 _ mem rom _ 10%bv 12%bv _ F_20f08 eq_refl D_20f08) |].
    { subst R1. rewrite !getr_other by (intro X; discriminate X). rewrite Ha0, Ha2. apply c_eq_neq. rewrite !u64_small; lia. }
    replace (v_addi (0x20f08%bv : word) 4) with (0x20f0c%bv : word) by (apply bv_eq; reflexivity).
    eapply mst_step; [reflexivity | eapply (step_addi RSEGS R1 _ mem rom _ 10%bv 10%bv 1%bv F_20f0c eq_refl D_20f0c) |].
    cbn [bv_eqb].
    assert (Ha0' : v_addi (getr R1 10%bv) (bv_signed (1%bv : bv 12)) = Z_to_bv 64 (p + m)).
    { subst R1. rewrite getr_other by (intro X; discriminate X). rewrite Ha0. change (bv_signed (1%bv : bv 12)) with 1.
      unfold v_addi. rewrite u64_small by lia. f_equal. lia. }
    rewrite Ha0'. set (R2 := regupd R1 10%bv (Z_to_bv 64 (p + m))).
    replace (v_addi (0x20f0c%bv : word) 4) with (0x20f10%bv : word) by (apply bv_eq; reflexivity).
    eapply mst_step; [reflexivity | eapply (step_bltu_ft RSEGS R2 _ mem rom _ 10%bv 8%bv _ F_20f10 eq_refl D_20f10) |].
    { subst R2 R1. rewrite getr_same by (intro X; discriminate X). rewrite !getr_other by (intro X; discriminate X). rewrite Hs0.
      unfold c_ltu, bv_ltu. rewrite !u64_small by lia. apply Z.ltb_irrefl. }
    replace (v_addi (0x20f10%bv : word) 4) with (0x20f14%bv : word) by (apply bv_eq; reflexivity).
    apply mst_refl.
  Qed.

  Lemma zskip_all_run : forall (k : nat) (R : bvmap 5 word) (i : nat),
    (S (i + k) = length bs)%nat ->
    getr R (10%bv : reg) = Z_to_bv 64 (p + Z.of_nat i) -> getr R (8%bv : reg) = Z_to_bv 64 (p + m) -> getr R (11%bv : reg) = Z_to_bv 64 48 ->
    getr R (12%bv : reg) = Z_to_bv 64 (2 ^ 64 - 1) ->
    exists R' : bvmap 5 word,
      msteps RSEGS (@mkst fx R (0x20f00%bv : word) mem rom) (@mkst fx R' (0x20f14%bv : word) mem rom)
      /\ getr R' (10%bv : reg) = Z_to_bv 64 (p + m) /\ getr R' (13%bv : reg) = Z_to_bv 64 48
      /\ (forall r : reg, r <> 10%bv -> r <> 13%bv -> getr R' r = getr R r).
  Proof.
    induction k as [|k IH]; intros R i Hik Ha0 Hs0 Ha1 Ha2.
    - exists (regupd (regupd R 13%bv (Z_to_bv 64 48)) 10%bv (Z_to_bv 64 (p + m))). split. apply (zskip_final R i); auto. lia.
      split. apply getr_same. intro X; discriminate X.
      split. rewrite getr_other by (intro X; discriminate X). apply getr_same. intro X; discriminate X.
      intros r H10 H13. rewrite getr_other by exact H10. rewrite getr_other by exact H13. reflexivity.
    - pose proof (zskip_step mem rom p m bs Hm Hp Hrd R i Ha0 Hs0 Ha1 Ha2 ltac:(lia) (Hz i ltac:(lia))) as STEP.
      set (R1 := regupd (regupd R 13%bv (Z_to_bv 64 48)) 10%bv (Z_to_bv 64 (p + Z.of_nat (S i)))) in STEP.
      destruct (IH R1 (S i) ltac:(lia)) as (R' & MS & Q10 & Q13 & QR).
      { subst R1. apply getr_same. intro X; discriminate X. }
      { subst R1. rewrite !getr_other by (intro X; discriminate X). exact Hs0. }
      { subst R1. rewrite !getr_other by (intro X; discriminate X). exact Ha1. }
      { subst R1. rewrite !getr_other by (intro X; discriminate X). exact Ha2. }
      exists R'. split; [eapply msteps_trans; [exact STEP | exact MS]|]. split; [exact Q10|]. split; [exact Q13|].
      intros r H10 H13. rewrite (QR r H10 H13). subst R1. rewrite getr_other by exact H10. rewrite getr_other by exact H13. reflexivity.
  Qed.

  Theorem zskip_all : forall (R : bvmap 5 word),
    (1 <= length bs)%nat ->
    getr R (10%bv : reg) = Z_to_bv 64 p -> getr R (8%bv : reg) = Z_to_bv 64 (p + m) -> getr R (11%bv : reg) = Z_to_bv 64 48 ->
    getr R (12%bv : reg) = Z_to_bv 64 (2 ^ 64 - 1) ->
    exists R' : bvmap 5 word,
      msteps RSEGS (@mkst fx R (0x20f00%bv : word) mem rom) (@mkst fx R' (0x20f14%bv : word) mem rom)
      /\ getr R' (10%bv : reg) = Z_to_bv 64 (p + m) /\ getr R' (13%bv : reg) = Z_to_bv 64 48
      /\ (forall r : reg, r <> 10%bv -> r <> 13%bv -> getr R' r = getr R r).
  Proof.
    intros R Hlen Ha0 Hs0 Ha1 Ha2. apply (zskip_all_run (length bs - 1) R 0%nat ltac:(lia)); try assumption.
    rewrite Z.add_0_r. exact Ha0.
  Qed.
End ZskipAll.
