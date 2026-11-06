(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Sem.
From OSSVerify.jsoncons.fuzz_bigint.images Require Import Plain.
From OSSVerify.Proofs.jsoncons.fuzz_bigint.lib Require Import PropExec SeqExec StoreOk AxSymExec3 AxSymExec3B AxSymExec3Sound AxSymRun3 SegRun SegPlan Src0PlanKit BigLinkBase.
From OSSVerify.Proofs.jsoncons.fuzz_bigint.lib.seg Require Import SegHost_BigLinkMulAlg.
From OSSVerify.Proofs.jsoncons.fuzz_bigint.lib.seg Require LibSegZ_l1_mul10_iter.
From OSSVerify.Proofs.jsoncons.fuzz_bigint.lib Require BigModel BigFactsBase BigFactsDigits.
Import -(notations) BigModel BigFactsBase BigFactsDigits.
Import ListNotations. Import AX2. Import AX2B. Import AX2S.
Unset Lia Cache. Unset Nra Cache. Unset Nia Cache.
Open Scope Z_scope.

Module BMA.
Abbreviation RSEGS := Plain.M.loaded_segments.
Module MI := LibSegZ_l1_mul10_iter.
Module ML := LibSegZ_l1_mul10_IL.
Module MA := LibSegZ_l1_mul10_A.
Module MT := LibSegZ_l1_mul10_T.

(* [comment removed for export] *)
Definition mlo (X C : Z) : Z := W.add (snd (DDproduct X 10)) C.
Definition mcar (X C : Z) : Z := W.add (fst (DDproduct X 10)) (W.b2z (W.ltu (mlo X C) (snd (DDproduct X 10)))).

Definition reg (i : nat) : bv 5 := Z_to_bv 5 (Z.of_nat i).

(* [comment removed for export] *)
(* [comment removed for export] *)

Definition t_lo : expr := match MI.cells with [KWord _ _ e] => e | _ => ELit 0 end.   (* [comment removed for export] *)
Definition t_car : expr := nth 11 MI.regs_out (ELit 0).                              (* [comment removed for export] *)
Definition z_lo : BL.za := Eval vm_compute in (match BL.zcomp t_lo with Some t => t | None => BL.ZL 0 end).
Definition z_car : BL.za := Eval vm_compute in (match BL.zcomp t_car with Some t => t | None => BL.ZL 0 end).
Lemma z_lo_ok : BL.zcomp t_lo = Some z_lo. Proof. vm_compute. reflexivity. Qed.
Lemma z_car_ok : BL.zcomp t_car = Some z_car. Proof. vm_compute. reflexivity. Qed.

Lemma t_lo_IL : match ML.cells with [KWord _ _ e] => e | _ => ELit 0 end = t_lo. Proof. vm_compute. reflexivity. Qed.
Lemma t_car_IL : nth 11 ML.regs_out (ELit 0) = t_car. Proof. vm_compute. reflexivity. Qed.

Lemma mul10_closed X : BL.inrange X -> fst (DDproduct X 10) = (10 * X) / BL.MM /\ snd (DDproduct X 10) = (10 * X) mod BL.MM.
Proof. intros. rewrite (Z.mul_comm 10 X). apply BL.DDproduct_closed; auto. unfold BL.inrange, BL.MM; lia. Qed.

(* [comment removed for export] *)
Lemma lo32_identity X : BL.inrange X ->
  ((42949672960 * (X / 4294967296)) mod BL.MM + (10 * ((4294967296 * X) mod BL.MM / 4294967296)) mod BL.MM) mod BL.MM
  = (10 * X) mod BL.MM.
Proof.
  (* [comment removed for export] *)
  unfold BL.inrange. change BL.MM with 18446744073709551616. intros HX.
  pose proof (Z.div_mod X 4294967296 ltac:(lia)) as DX. pose proof (Z.mod_pos_bound X 4294967296 ltac:(lia)) as BX.
  set (Xh := X / 4294967296) in *. set (Xl := X mod 4294967296) in *. clearbody Xh Xl.
  assert (E1: (4294967296 * X) mod 18446744073709551616 = 4294967296 * Xl).
  { symmetry. apply Z.mod_unique with Xh; lia. }
  rewrite E1. rewrite (Z.mul_comm 4294967296 Xl), Z.div_mul by lia.
  rewrite <- Zplus_mod. f_equal. lia.
Qed.

Lemma t_lo_val V : BL.inrange (V 19%nat) -> BL.inrange (V 11%nat) -> BL.zden V z_lo = mlo (V 19%nat) (V 11%nat).
Proof.
  intros HX HC. cbn [BL.zden z_lo]. set (X := V 19%nat) in *. set (C := V 11%nat) in *. clearbody X C.
  rewrite lo32_identity by auto. unfold mlo. destruct (mul10_closed X HX) as [_ ->]. rewrite BL.W_add_eq. f_equal. lia.
Qed.

Lemma t_car_val V : BL.inrange (V 19%nat) -> BL.inrange (V 11%nat) -> BL.zden V z_car = mcar (V 19%nat) (V 11%nat).
Proof.
  intros HX HC. cbn [BL.zden z_car]. set (X := V 19%nat) in *. set (C := V 11%nat) in *. clearbody X C.
  rewrite !lo32_identity by auto.
  unfold mcar, mlo. destruct (mul10_closed X HX) as [-> ->]. rewrite !BL.W_add_eq, BL.W_b2z_ltu.
  change (if (C + (10 * X) mod BL.MM) mod BL.MM <? (10 * X) mod BL.MM then 1 else 0)
    with (BL.zb ((C + (10 * X) mod BL.MM) mod BL.MM <? (10 * X) mod BL.MM)).
  change (if (10 * X) mod BL.MM <? (42949672960 * (X / 4294967296)) mod BL.MM then 1 else 0)
    with (BL.zb ((10 * X) mod BL.MM <? (42949672960 * (X / 4294967296)) mod BL.MM)).
  change (if ((10 * X) mod BL.MM + C) mod BL.MM <? (10 * X) mod BL.MM then 1 else 0)
    with (BL.zb (((10 * X) mod BL.MM + C) mod BL.MM <? (10 * X) mod BL.MM)).
  set (lo := (10 * X) mod BL.MM) in *.
  assert (Hmid: BL.zb (lo <? (42949672960 * (X / 4294967296)) mod BL.MM)
                = ((42949672960 * (X / 4294967296)) mod BL.MM + (10 * ((4294967296 * X) mod BL.MM / 4294967296)) mod BL.MM) / BL.MM).
  { subst lo. rewrite <- (lo32_identity X HX). apply BL.carry_ltu_l; apply BL.mod_inrange. }
  rewrite Hmid. clear Hmid.
  rewrite (BL.carry_ltu_r C lo). 2: exact HC. 2: subst lo; apply BL.mod_inrange.
  rewrite (BL.carry_ltu_l lo C). 2: subst lo; apply BL.mod_inrange. 2: exact HC.
  (* [comment removed for export] *)
  unfold BL.inrange in *. change BL.MM with 18446744073709551616 in *.
  pose proof (Z.div_mod X 4294967296 ltac:(lia)) as DX. pose proof (Z.mod_pos_bound X 4294967296 ltac:(lia)) as BX.
  set (Xh := X / 4294967296) in *. set (Xl := X mod 4294967296) in *.
  assert (HXh: 0 <= Xh < 4294967296) by (subst Xh; split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]).
  clearbody Xh Xl.
  assert (E1: (4294967296 * X) mod 18446744073709551616 = 4294967296 * Xl).
  { symmetry. apply Z.mod_unique with Xh; lia. }
  rewrite E1. rewrite (Z.mul_comm 4294967296 Xl), Z.div_mul by lia.
  rewrite (Z.mod_small (10 * Xl)) by lia.
  rewrite (Z.mod_small (10 * Xh)) by lia.
  pose proof (Z.div_mod (10 * Xh) 4294967296 ltac:(lia)) as DA. pose proof (Z.mod_pos_bound (10 * Xh) 4294967296 ltac:(lia)) as BA.
  set (a := 10 * Xh / 4294967296) in *. set (b := (10 * Xh) mod 4294967296) in *. clearbody a b.
  assert (E4: (42949672960 * Xh) mod 18446744073709551616 = 4294967296 * b).
  { symmetry. apply Z.mod_unique with a; lia. }
  rewrite E4.
  assert (E5: 10 * X = 18446744073709551616 * a + (4294967296 * b + 10 * Xl)) by lia.
  assert (Elo: lo = (4294967296 * b + 10 * Xl) mod 18446744073709551616).
  { subst lo. rewrite E5. rewrite Z.add_comm, (Z.mul_comm 18446744073709551616 a), Z_mod_plus_full. reflexivity. }
  rewrite E5 at 1. rewrite (Z.add_comm (18446744073709551616 * a)), (Z.mul_comm 18446744073709551616 a), Z_div_plus_full by lia.
  rewrite Zplus_mod_idemp_r. f_equal. rewrite (Z.add_comm C lo). lia.
Qed.

End BMA.
