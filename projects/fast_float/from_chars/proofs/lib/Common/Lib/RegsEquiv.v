(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common.Lib Require Import LiaTuning MState Exec Frame.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.  (* [comment removed for export] *)
Open Scope bv_scope.

(* [comment removed for export] *)


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma reg_of_nat : forall r : reg, exists n, r = Z_to_bv 5 (Z.of_nat n) /\ (n < 32)%nat.
Proof.
  intros r. exists (Z.to_nat (bv_unsigned r)). pose proof (bv_unsigned_in_range 5 r) as Hr.
  unfold bv_modulus in Hr. simpl in Hr. split; [|lia].
  rewrite Z2Nat.id by lia. apply bv_eq. rewrite Z_to_bv_unsigned. symmetry.
  apply bv_wrap_small. unfold bv_modulus. simpl. lia.
Qed.

Definition mkR_of (R : bvmap 5 word) : bvmap 5 word :=
  mkR (getr R 1) (getr R 2) (getr R 3) (getr R 4) (getr R 5) (getr R 6) (getr R 7) (getr R 8)
      (getr R 9) (getr R 10) (getr R 11) (getr R 12) (getr R 13) (getr R 14) (getr R 15) (getr R 16)
      (getr R 17) (getr R 18) (getr R 19) (getr R 20) (getr R 21) (getr R 22) (getr R 23) (getr R 24)
      (getr R 25) (getr R 26) (getr R 27) (getr R 28) (getr R 29) (getr R 30) (getr R 31).

Lemma regs_eqv_mkR : forall R, regs_eqv R (mkR_of R).
Proof.
  intros R r. destruct (reg_of_nat r) as (n & -> & Hn).
  do 32 (destruct n as [|n]; [reflexivity|]). lia.
Qed.

(* [comment removed for export] *)
Lemma getr_mkR : forall x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 (r : reg),
  getr (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31) r =
  match Z.to_nat (bv_unsigned r) with
  | 0 => Z_to_bv 64 0 | 1 => x1 | 2 => x2 | 3 => x3 | 4 => x4 | 5 => x5 | 6 => x6 | 7 => x7
  | 8 => x8 | 9 => x9 | 10 => x10 | 11 => x11 | 12 => x12 | 13 => x13 | 14 => x14 | 15 => x15
  | 16 => x16 | 17 => x17 | 18 => x18 | 19 => x19 | 20 => x20 | 21 => x21 | 22 => x22 | 23 => x23
  | 24 => x24 | 25 => x25 | 26 => x26 | 27 => x27 | 28 => x28 | 29 => x29 | 30 => x30 | _ => x31
  end%nat.
Proof.
  intros. destruct (reg_of_nat r) as (n & -> & Hn).
  do 32 (destruct n as [|n]; [reflexivity|]). lia.
Qed.

(* [comment removed for export] *)
Section GetrMkR.
  Variables x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word.
  Let R := mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31.
  #[using="Type"] Lemma getr_mkR_0 : getr R 0 = Z_to_bv 64 0. Proof. LiaFast.lf_pins LiaFast.u0. reflexivity. Qed.
  #[using="Type"] Lemma getr_mkR_1 : getr R 1 = x1. Proof. LiaFast.lf_pins LiaFast.u0. reflexivity. Qed.
  #[using="Type"] Lemma getr_mkR_2 : getr R 2 = x2. Proof. LiaFast.lf_pins LiaFast.u0. reflexivity. Qed.
  #[using="Type"] Lemma getr_mkR_3 : getr R 3 = x3. Proof. LiaFast.lf_pins LiaFast.u0. reflexivity. Qed.
  #[using="Type"] Lemma getr_mkR_4 : getr R 4 = x4. Proof. LiaFast.lf_pins LiaFast.u0. reflexivity. Qed.
  #[using="Type"] Lemma getr_mkR_5 : getr R 5 = x5. Proof. LiaFast.lf_pins LiaFast.u0. reflexivity. Qed.
  #[using="Type"] Lemma getr_mkR_6 : getr R 6 = x6. Proof. LiaFast.lf_pins LiaFast.u0. reflexivity. Qed.
  #[using="Type"] Lemma getr_mkR_7 : getr R 7 = x7. Proof. LiaFast.lf_pins LiaFast.u0. reflexivity. Qed.
  #[using="Type"] Lemma getr_mkR_8 : getr R 8 = x8. Proof. LiaFast.lf_pins LiaFast.u0. reflexivity. Qed.
  #[using="Type"] Lemma getr_mkR_9 : getr R 9 = x9. Proof. LiaFast.lf_pins LiaFast.u0. reflexivity. Qed.
  #[using="Type"] Lemma getr_mkR_10 : getr R 10 = x10. Proof. LiaFast.lf_pins LiaFast.u0. reflexivity. Qed.
  #[using="Type"] Lemma getr_mkR_11 : getr R 11 = x11. Proof. LiaFast.lf_pins LiaFast.u0. reflexivity. Qed.
  #[using="Type"] Lemma getr_mkR_12 : getr R 12 = x12. Proof. LiaFast.lf_pins LiaFast.u0. reflexivity. Qed.
  #[using="Type"] Lemma getr_mkR_13 : getr R 13 = x13. Proof. LiaFast.lf_pins LiaFast.u0. reflexivity. Qed.
  #[using="Type"] Lemma getr_mkR_14 : getr R 14 = x14. Proof. LiaFast.lf_pins LiaFast.u0. reflexivity. Qed.
  #[using="Type"] Lemma getr_mkR_15 : getr R 15 = x15. Proof. LiaFast.lf_pins LiaFast.u0. reflexivity. Qed.
  #[using="Type"] Lemma getr_mkR_16 : getr R 16 = x16. Proof. LiaFast.lf_pins LiaFast.u0. reflexivity. Qed.
  #[using="Type"] Lemma getr_mkR_17 : getr R 17 = x17. Proof. LiaFast.lf_pins LiaFast.u0. reflexivity. Qed.
  #[using="Type"] Lemma getr_mkR_18 : getr R 18 = x18. Proof. LiaFast.lf_pins LiaFast.u0. reflexivity. Qed.
  #[using="Type"] Lemma getr_mkR_19 : getr R 19 = x19. Proof. LiaFast.lf_pins LiaFast.u0. reflexivity. Qed.
  #[using="Type"] Lemma getr_mkR_20 : getr R 20 = x20. Proof. LiaFast.lf_pins LiaFast.u0. reflexivity. Qed.
  #[using="Type"] Lemma getr_mkR_21 : getr R 21 = x21. Proof. LiaFast.lf_pins LiaFast.u0. reflexivity. Qed.
  #[using="Type"] Lemma getr_mkR_22 : getr R 22 = x22. Proof. LiaFast.lf_pins LiaFast.u0. reflexivity. Qed.
  #[using="Type"] Lemma getr_mkR_23 : getr R 23 = x23. Proof. LiaFast.lf_pins LiaFast.u0. reflexivity. Qed.
  #[using="Type"] Lemma getr_mkR_24 : getr R 24 = x24. Proof. LiaFast.lf_pins LiaFast.u0. reflexivity. Qed.
  #[using="Type"] Lemma getr_mkR_25 : getr R 25 = x25. Proof. LiaFast.lf_pins LiaFast.u0. reflexivity. Qed.
  #[using="Type"] Lemma getr_mkR_26 : getr R 26 = x26. Proof. LiaFast.lf_pins LiaFast.u0. reflexivity. Qed.
  #[using="Type"] Lemma getr_mkR_27 : getr R 27 = x27. Proof. LiaFast.lf_pins LiaFast.u0. reflexivity. Qed.
  #[using="Type"] Lemma getr_mkR_28 : getr R 28 = x28. Proof. LiaFast.lf_pins LiaFast.u0. reflexivity. Qed.
  #[using="Type"] Lemma getr_mkR_29 : getr R 29 = x29. Proof. LiaFast.lf_pins LiaFast.u0. reflexivity. Qed.
  #[using="Type"] Lemma getr_mkR_30 : getr R 30 = x30. Proof. LiaFast.lf_pins LiaFast.u0. reflexivity. Qed.
  #[using="Type"] Lemma getr_mkR_31 : getr R 31 = x31. Proof. LiaFast.lf_pins LiaFast.u0. reflexivity. Qed.
End GetrMkR.
