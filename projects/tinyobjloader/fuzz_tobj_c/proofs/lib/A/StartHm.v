(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Numbers.BinNums"; "Z"; "@Stdlib.ZArith.BinInt.Z"; "le"; "testbit"; "pow"; "lt"; "sub"; "add"; "max"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.A.StartHm"; "smear_step"; "smear_sv"; "smear"; "@Corelib.Init.Logic"; "eq"; "and"; "@Corelib.Init.Datatypes"; "bool"; "cons"; "false"; "true"; "list"; "nil"; "orb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "eval"; "sv"; "valuation"; "@stdpp.bitvector.definitions"; "bv_unsigned"; "Z_to_bv"; "bv"; "@Corelib.Lists.ListDef"; "Forall"; "@Stdlib.Lists.List"; "fold_left"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Sem.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymSoundA.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Definition smear_step (k : Z) (z : Z) : Z := Z.lor z (Z.shiftr z k).
Definition smear (x : Z) : Z := ltac2:(tb__ "0|0|
S8Z20S8Z10S8Z8S8Z4S8Z2S8Z1Vx;A2A2A2A2A2A2").

Lemma smear_step_nonneg : ltac2:(tb__ "0|2|
S0S0S1Z0M0R2A2M1G1S1G0S8R4R3A2A2F_;F_;Fz;Fk;").
Proof. intros k z Hk Hz. unfold smear_step. apply Z.lor_nonneg. split; [exact Hz | apply Z.shiftr_nonneg; exact Hz]. Qed.

Lemma testbit_smear_step : ltac2:(tb__ "0|1|
S0S0S0S1Z0R3A2M0G0G0SbSdS2S8R6R5A2R4A2S13S2R5R4A2S2R5S6R4R6A2A2A2A3F_;F_;F_;Fi;Fz;Fk;").
Proof.
  intros k z i Hk Hz Hi. unfold smear_step. rewrite Z.lor_spec, Z.shiftr_spec by lia. reflexivity.
Qed.

Lemma smear_step_low : ltac2:(tb__ "0|4|
S0S0S0S1Z0M0R3A2M1G1S1S5R3Z1A2S5Z2eM2R5A2A2S0ScS1R5R1A2S1R1G2A2M3A2SbSdS2R7R2A2S10A3F_;Fi;S0ScS1S7G0S5R6R8A2A2R1A2G3A2SbSdS2S8R9R8A2R2A2S10A3F_;Fi;F_;F_;F_;F_;Fa;Fz;Fk;").
Proof.
  intros k z a Hk Hz Hak H i Hi. rewrite testbit_smear_step by lia.
  destruct (Z_lt_le_dec i a) as [Hl|Hl].
  - rewrite (H (i + k)) by lia. apply orb_true_r.
  - rewrite (H i) by lia. reflexivity.
Qed.

Lemma smear_step_high : ltac2:(tb__ "0|2|
S0S0S1Z0R2A2M0G0S0S1Z2fR1A2M1SbSdS2R5R2A2SfA3F_;Fi;S0G1SbSdS2S8R7R6A2R2A2SfA3F_;Fi;F_;F_;F_;Fz;Fk;").
Proof. intros k z Hk Hz H i Hi. rewrite testbit_smear_step by lia. rewrite (H i), (H (i + k)) by lia. reflexivity. Qed.

Lemma testbit_high_false : ltac2:(tb__ "0|1|
S0S0ScS1Z0R2A2S4R2S3Z2Z2fM0A2A2A2S1G0R2A2SbSdS2R4R3A2SfA3F_;F_;Fi;Fx;").
Proof.
  intros x i Hx Hi. apply Z.testbit_false; [lia|].
  rewrite Z.div_small; [reflexivity|]. split; [lia|]. eapply Z.lt_le_trans; [apply (proj2 Hx)|]. apply Z.pow_le_mono_r; lia.
Qed.

Lemma testbit_46_true : ltac2:(tb__ "0|2|
S0ScS1S3Z2M0Z2eM1A2R1A2S4R1S3G0Z2fA2A2A2SbSdS2R2G1A2S10A3F_;Fx;").
Proof.
  intros x Hx. apply Z.testbit_true; [lia|].
  assert (2 ^ 47 = 2 * 2 ^ 46) by reflexivity.
  replace (x / 2 ^ 46) with 1; [reflexivity|].
  apply (Z.div_unique_pos x (2 ^ 46) 1 (x - 2 ^ 46)); lia.
Qed.

Theorem smear_47 : ltac2:(tb__ "0|2|
S0ScS1S3Z2M0Z2eA2R1A2S4R1S3G0Z2fA2M1A2A2SbS0SaR2A1S5G1Z1A2A3F_;Fx;").
Proof.
  intros x Hx.
  assert (Hx0 : 0 <= x) by lia.
  set (s1 := smear_step 1 x). set (s2 := smear_step 2 s1). set (s3 := smear_step 4 s2).
  set (s4 := smear_step 8 s3). set (s5 := smear_step 16 s4). set (s6 := smear_step 32 s5).
  assert (P1 : 0 <= s1) by (subst s1; apply smear_step_nonneg; lia).
  assert (P2 : 0 <= s2) by (subst s2; apply smear_step_nonneg; lia).
  assert (P3 : 0 <= s3) by (subst s3; apply smear_step_nonneg; lia).
  assert (P4 : 0 <= s4) by (subst s4; apply smear_step_nonneg; lia).
  assert (P5 : 0 <= s5) by (subst s5; apply smear_step_nonneg; lia).
  assert (P6 : 0 <= s6) by (subst s6; apply smear_step_nonneg; lia).

  assert (L0 : forall i, 46 <= i <= 46 -> Z.testbit x i = true) by (intros i Hi; replace i with 46 by lia; apply testbit_46_true; exact Hx).
  pose proof (smear_step_low 1 x 46 ltac:(lia) Hx0 ltac:(lia) L0) as L1. change (smear_step 1 x) with s1 in L1. cbn [Z.max Z.sub] in L1.
  assert (L1' : forall i, 45 <= i <= 46 -> Z.testbit s1 i = true) by (intros i Hi; apply L1; lia).
  pose proof (smear_step_low 2 s1 45 ltac:(lia) P1 ltac:(lia) L1') as L2. change (smear_step 2 s1) with s2 in L2.
  assert (L2' : forall i, 43 <= i <= 46 -> Z.testbit s2 i = true) by (intros i Hi; apply L2; lia).
  pose proof (smear_step_low 4 s2 43 ltac:(lia) P2 ltac:(lia) L2') as L3. change (smear_step 4 s2) with s3 in L3.
  assert (L3' : forall i, 39 <= i <= 46 -> Z.testbit s3 i = true) by (intros i Hi; apply L3; lia).
  pose proof (smear_step_low 8 s3 39 ltac:(lia) P3 ltac:(lia) L3') as L4. change (smear_step 8 s3) with s4 in L4.
  assert (L4' : forall i, 31 <= i <= 46 -> Z.testbit s4 i = true) by (intros i Hi; apply L4; lia).
  pose proof (smear_step_low 16 s4 31 ltac:(lia) P4 ltac:(lia) L4') as L5. change (smear_step 16 s4) with s5 in L5.
  assert (L5' : forall i, 15 <= i <= 46 -> Z.testbit s5 i = true) by (intros i Hi; apply L5; lia).
  pose proof (smear_step_low 32 s5 15 ltac:(lia) P5 ltac:(lia) L5') as L6. change (smear_step 32 s5) with s6 in L6.
  assert (L6' : forall i, 0 <= i <= 46 -> Z.testbit s6 i = true) by (intros i Hi; apply L6; lia).

  assert (H0 : forall i, 47 <= i -> Z.testbit x i = false) by (intros i Hi; apply testbit_high_false; lia).
  pose proof (smear_step_high 1 x ltac:(lia) Hx0 H0) as H1. change (smear_step 1 x) with s1 in H1.
  pose proof (smear_step_high 2 s1 ltac:(lia) P1 H1) as H2. change (smear_step 2 s1) with s2 in H2.
  pose proof (smear_step_high 4 s2 ltac:(lia) P2 H2) as H3. change (smear_step 4 s2) with s3 in H3.
  pose proof (smear_step_high 8 s3 ltac:(lia) P3 H3) as H4. change (smear_step 8 s3) with s4 in H4.
  pose proof (smear_step_high 16 s4 ltac:(lia) P4 H4) as H5. change (smear_step 16 s4) with s5 in H5.
  pose proof (smear_step_high 32 s5 ltac:(lia) P5 H5) as H6. change (smear_step 32 s5) with s6 in H6.

  change (smear x) with s6. replace (2 ^ 47 - 1) with (Z.ones 47) by reflexivity.
  apply Z.bits_inj'. intros i Hi.
  destruct (Z_lt_le_dec i 47) as [Hl|Hl].
  - rewrite (L6' i) by lia. symmetry. apply Z.ones_spec_low. lia.
  - rewrite (H6 i) by lia. symmetry. apply Z.ones_spec_high. lia.
Qed.

Example max_user_va_47 : Z.lnot (Z.shiftl (-1) (Z.land (- (64 - 47)) 63)) = 2 ^ 47 - 1.
Proof. reflexivity. Qed.

Fixpoint smear_sv (x : sv) (ks : list Z) : sv :=
  match ks with
  | [] => x
  | k :: ks' => smear_sv (SAlu ALU_OR x (SAlu ALU_SRL x (SLit k))) ks'
  end.

Lemma eval_smear_sv : ltac2:(tb__ "0|1|
S16S11S0A1S15S1aS0S0ScS1Z0R1A2S4R1Z40A2A2Lk;R2A3SbS0S17Q40M0S14R4S9R2R3A2A2A2S1bS0S0S0S0S8R1R2A2Lk;Lz;R3S17G0S14R4R2A2A2A5A3F_;Fx;Fks;Frho;").
Proof.
  intros rho ks. induction ks as [|k ks IH]; intros x Hks; [reflexivity|].
  inversion Hks as [|k' ks' Hk Hks']; subst. cbn [smear_sv fold_left]. rewrite (IH _ Hks'). f_equal.
  cbn [eval]. rewrite or_val_A, srl_val, (Z.mod_small k 64) by lia. reflexivity.
Qed.

Theorem eval_smear_sv_47 : ltac2:(tb__ "0|5|
S16S15ScS1S3Z2M0Z2eA2S17Q40M1S14R2R1A2A2M2A2S4G2S3G0Z2fA2M3A2A2SbS19G1A1S14R3S9R2SeS0Z1M4SeS0G0SeS0Z4SeS0Z8SeS0Z10SeS0Z20S12S0A1A3A3A3A3A3A3A2A2S18G1S5G3G4A2A2A3F_;Fx;Frho;").
Proof.
  intros rho x Hx. apply bv_eq. rewrite eval_smear_sv by (repeat constructor; lia).
  cbn [fold_left]. change (smear_step 32 (smear_step 16 (smear_step 8 (smear_step 4 (smear_step 2 (smear_step 1 (bv_unsigned (eval rho x))))))))
    with (smear (bv_unsigned (eval rho x))).
  rewrite (smear_47 _ Hx). reflexivity.
Qed.
