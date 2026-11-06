(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.jsoncons.fuzz_bigint.images Require Import Ubsan.
From OSSVerify.Proofs.jsoncons.fuzz_bigint.lib Require Import PropExec CatExec CatSim SeqExec StoreOk AxSymExec3 AxSymExec3B AxSymExec3Sound AxSymRun3 SegRun SegPlan Ub0PlanKit BigLinkBase BigLinkGlueUb0 BigLinkInlBaseU BigLinkMulAlg.
From OSSVerify.Proofs.jsoncons.fuzz_bigint.lib.seg Require Import SegHost_BigLinkMulU.
From OSSVerify.Proofs.jsoncons.fuzz_bigint.lib Require BigModel BigFactsBase BigFactsDigits.
Import -(notations) BigModel BigFactsBase BigFactsDigits.
Import ListNotations. Import AX2. Import AX2B. Import AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Module BMU.
Import BMA.   (* [comment removed for export] *)
Unset Lia Cache.
Abbreviation RSEGS := Ubsan.M.loaded_segments.
Module MI := LibSegZ_l1u_mul10_iter.
Module ML := LibSegZ_l1u_mul10_IL.

Notation reg i := (Z_to_bv 5 (Z.of_nat i)) (only parsing).

Lemma In_of_existsb_u (i : nat) (l : list nat) : existsb (Nat.eqb i) l = true -> In i l.
Proof. intros H. apply existsb_exists in H as (x & Hx & E). apply Nat.eqb_eq in E. subst. exact Hx. Qed.
Ltac inK := apply In_of_existsb_u; vm_compute; reflexivity.
Lemma nth_error_single {A} (x y : A) i : nth_error [x] i = Some y -> y = x.
Proof. destruct i; simpl. congruence. destruct i; discriminate. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)


Definition e8C : expr := EMd M_MUL (ELit 8) (EVar 34).
Definition z8C : BL.za := Eval vm_compute in (BL.zc e8C).
Lemma z8C_ok : BL.zcomp e8C = Some z8C. Proof. vm_compute. reflexivity. Qed.
Lemma z8C_val V C : V 34%nat = C -> 8 <= C <= 264 -> BL.zden V z8C = 8 * C.
Proof. intros HC RC. cbn [BL.zden z8C]. rewrite HC. unfold BL.MM. rewrite Z.mod_small; lia. Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition t_lo : expr := Eval vm_compute in (match MI.cells with [KWord _ _ e] => e | _ => ELit 0 end).
Definition t_car : expr := Eval vm_compute in (nth 22 MI.regs_out (ELit 0)).
Definition z_lo : BL.za := Eval vm_compute in (BL.zc t_lo).
Definition z_car : BL.za := Eval vm_compute in (BL.zc t_car).
Lemma z_lo_ok : BL.zcomp t_lo = Some z_lo. Proof. vm_compute. reflexivity. Qed.
Lemma z_car_ok : BL.zcomp t_car = Some z_car. Proof. vm_compute. reflexivity. Qed.
Definition ren (V : nat -> Z) : nat -> Z := fun n => match n with 11%nat => V 41%nat | 19%nat => V 32%nat | _ => V n end.
Lemma z_lo_ren V : BL.zden V z_lo = BL.zden (ren V) BMA.z_lo. Proof. reflexivity. Qed.
Lemma z_car_ren V : BL.zden V z_car = BL.zden (ren V) BMA.z_car. Proof. reflexivity. Qed.
Lemma t_lo_val V : BL.inrange (V 32%nat) -> BL.inrange (V 41%nat) -> BL.zden V z_lo = mlo (V 32%nat) (V 41%nat).
Proof. intros. rewrite z_lo_ren. rewrite BMA.t_lo_val; auto. Qed.
Lemma t_car_val V : BL.inrange (V 32%nat) -> BL.inrange (V 41%nat) -> BL.zden V z_car = mcar (V 32%nat) (V 41%nat).
Proof. intros. rewrite z_car_ren. rewrite BMA.t_car_val; auto. Qed.
Lemma t_lo_IL : match ML.cells with [KWord _ _ e] => e | _ => ELit 0 end = t_lo. Proof. vm_compute. reflexivity. Qed.
Lemma t_car_IL : nth 22 ML.regs_out (ELit 0) = t_car. Proof. vm_compute. reflexivity. Qed.
Lemma t_car_MI : nth 22 MI.regs_out (ELit 0) = t_car. Proof. vm_compute. reflexivity. Qed.
Lemma cells_MI : MI.cells = [KWord (SA (EAlu ALU_ADD (EVar 35) (EMd M_MUL (ELit 8) (EVar 40))) 0) 8 t_lo]. Proof. vm_compute. reflexivity. Qed.
Lemma cells_ML : ML.cells = [KWord (SA (EAlu ALU_ADD (EVar 35) (EMd M_MUL (ELit 8) (EVar 40))) 0) 8 t_lo]. Proof. vm_compute. reflexivity. Qed.

Definition e_qI : expr := EAlu ALU_ADD (EVar 35) (EMd M_MUL (ELit 8) (EVar 40)).   (* [comment removed for export] *)
Definition z_qI : BL.za := Eval vm_compute in (BL.zc e_qI).
Lemma z_qI_ok : BL.zcomp e_qI = Some z_qI. Proof. vm_compute. reflexivity. Qed.
Definition e_nI : expr := EAlu ALU_ADD (EVar 33) (EMd M_MUL (ELit (-1)) (EVar 40)).   (* [comment removed for export] *)
Definition z_nI : BL.za := Eval vm_compute in (BL.zc e_nI).
Lemma z_nI_ok : BL.zcomp e_nI = Some z_nI. Proof. vm_compute. reflexivity. Qed.
Definition e_Cn : expr := EAlu ALU_ADD (EMd M_MUL (ELit (-1)) (EVar 33)) (EVar 34).  (* [comment removed for export] *)
Definition z_Cn : BL.za := Eval vm_compute in (BL.zc e_Cn).
Lemma z_Cn_ok : BL.zcomp e_Cn = Some z_Cn. Proof. vm_compute. reflexivity. Qed.
Definition e_CI : expr := EAlu ALU_ADD (EVar 34) (EMd M_MUL (ELit (-1)) (EVar 40)).  (* [comment removed for export] *)
Definition z_CI : BL.za := Eval vm_compute in (BL.zc e_CI).
Lemma z_CI_ok : BL.zcomp e_CI = Some z_CI. Proof. vm_compute. reflexivity. Qed.

Lemma esub_neg1 a b : 0 <= a -> a <= b < BL.MM -> (b + ((BL.MM - 1) * a) mod BL.MM) mod BL.MM = b - a.
Proof.
  intros Ha Hb. destruct (Z.eq_dec a 0) as [->|NZ]. { rewrite Z.mul_0_r, Z.mod_0_l, Z.add_0_r, Z.mod_small; unfold BL.MM in *; lia. }
  apply BL.esub_val'. lia. lia.
Qed.
Lemma esub_neg1' a b : 0 <= a -> a <= b < BL.MM -> (((BL.MM - 1) * a) mod BL.MM + b) mod BL.MM = b - a.
Proof. intros. rewrite Z.add_comm. apply esub_neg1; auto. Qed.
End BMU.
