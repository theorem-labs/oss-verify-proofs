(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (9 recorded proofs replaced by written proofs (upd_nat_length, zupd_length, zlength_zupd and 6 more)). *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith Bool List Lia.
From OSSVerify.Proofs.zstd.huf_decompress.lib Require KReplay.
Ltac2 kr_t_Prelim () := "c59OSSVerify5KrLib4Spec6Prelim7zlengthC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes6lengthI47Corelib4Init9Datatypes4list00K47Corelib4Init9Datatypes4list01K47Corelib4Init5Logic2eq01K47Corelib4Init9Datatypes3nat02K47Corelib4Init9Datatypes4list02C47Corelib4Init5Peano;f_equal_natC47Corelib4Init9Datatypes8list_indc59OSSVerify5KrLib4Spec6Prelim7upd_natC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic2eq00I47Corelib7Numbers7BinNums1Z00I47Corelib4Init9Datatypes3nat00K47Corelib4Init9Datatypes3nat01C56Stdlib6ZArith6BinInt1Z3ltbC56Stdlib6ZArith6BinInt1Z6to_natc59OSSVerify5KrLib4Spec6Prelim>upd_nat_lengthC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec6Prelim4zupdC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums1Z01I47Corelib4Init9Datatypes4bool00C56Stdlib6ZArith6BinInt1Z6of_natc59OSSVerify5KrLib4Spec6Prelim;zupd_lengthC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic8eq_ind_rC47Corelib4Init5Peano2ltC56Stdlib6ZArith6BinInt1Z2ltC46Stdlib9micromega;ZifyClasses7rew_iffK46Stdlib9micromega6VarMap1t01I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr01K47Corelib4Init9Datatypes6option02C46Stdlib9micromega5Tauto8BFormulaC46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundK47Corelib7Numbers7BinNums1Z02C56Stdlib6ZArith6BinInt1Z3addC56Stdlib6ZArith4Znat5Nat2Z9is_nonnegC56Stdlib6ZArith6BinInt1Z2leK46Stdlib9micromega6VarMap1t02K46Stdlib9micromega6VarMap1t03K47Corelib7Numbers7BinNums8positive02K46Stdlib9micromega7EnvRing5PExpr02K46Stdlib9micromega=RingMicromega7Formula01K46Stdlib9micromega7EnvRing5PExpr03C46Stdlib9micromega;ZifyClasses;rew_iff_revC47Corelib5Lists7ListDef3nthC46Stdlib9micromega;ZifyClasses5mkrelK46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega5Tauto8GFormula03K46Stdlib9micromega5Tauto8GFormula08C46Stdlib9micromega;ZifyClasses5mkappC56Stdlib6ZArith4Znat5Nat2Z6inj_ltK46Stdlib9micromega=RingMicromega3Op205C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K47Corelib4Init9Datatypes4unit01C56Stdlib6ZArith4Znat5Nat2Z8inj_succI46Stdlib9micromega:ZMicromega;ZArithProof00K47Corelib4Init9Datatypes4bool01K47Corelib7Numbers7BinNums8positive03K46Stdlib9micromega=RingMicromega3Op203K46Stdlib9micromega=RingMicromega3Op201C47Corelib4Init5Logic3notC47Corelib4Init5Logic9False_indI47Corelib4Init5Logic3and00C56Stdlib6ZArith6BinInt1Z8ltb_specI47Corelib4Init9Datatypes8BoolSpec00C56Stdlib6ZArith6BinInt1Z3maxC56Stdlib6ZArith6BinInt1Z8max_specI47Corelib4Init5Logic2or00K46Stdlib9micromega=RingMicromega5Psatz02K46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega:ZMicromega;ZArithProof02K47Corelib7Numbers7BinNums8positive01K46Stdlib9micromega5Tauto8GFormula06c59OSSVerify5KrLib4Spec6Prelim@nth_upd_nat_sameC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib4Spec6Prelim4znthC1?~~~~~~~~~~~~~~~K46Stdlib9micromega5Tauto8GFormula05C46Stdlib9micromega8ZifyInst@of_nat_to_nat_eqK46Stdlib9micromega:ZMicromega;ZArithProof01C56Stdlib6ZArith4Znat5Nat2Z7inj_iffC47Corelib4Init5Logic7iff_symK47Corelib7Numbers7BinNums1Z03K46Stdlib9micromega7EnvRing3Pol01K46Stdlib9micromega=RingMicromega5Psatz04K46Stdlib9micromega5Tauto8GFormula07c59OSSVerify5KrLib4Spec6PrelimAnth_upd_nat_otherC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic5False00C46Stdlib5Lists4List2InC46Stdlib5Lists4List6nth_InC47Corelib4Init5Logic8iff_reflC47Corelib5Lists7ListDef6repeatC46Stdlib5Lists4List=repeat_lengthc59OSSVerify5KrLib4Spec6Prelim7zrepeatC1?~~~~~~~~~~~~~~~".
(* [comment removed for export] *)
Unset Lia Cache.
Import ListNotations.
Open Scope Z_scope.

Definition u8  (x : Z) : Z := x mod 2^8.
Definition u16 (x : Z) : Z := x mod 2^16.
Definition u32 (x : Z) : Z := x mod 2^32.
Definition u64 (x : Z) : Z := x mod 2^64.
(* [comment removed for export] *)
Definition s32 (x : Z) : Z := (x + 2^31) mod 2^32 - 2^31.
Definition s64 (x : Z) : Z := (x + 2^63) mod 2^64 - 2^63.

Definition zlength {A} (l : list A) : Z := Z.of_nat (length l).

Definition znth (l : list Z) (i : Z) : Z :=
  if i <? 0 then 0 else nth (Z.to_nat i) l 0.

Fixpoint upd_nat (l : list Z) (i : nat) (v : Z) : list Z :=
  match l, i with
  | [], _ => []
  | _ :: t, O => v :: t
  | h :: t, S i' => h :: upd_nat t i' v
  end.

Definition zupd (l : list Z) (i : Z) (v : Z) : list Z :=
  if i <? 0 then l else upd_nat l (Z.to_nat i) v.

Lemma upd_nat_length : forall l i v, length (upd_nat l i v) = length l.
Proof. induction l; intros [|i] v; cbn; auto. Qed.

Lemma zupd_length : forall l i v, length (zupd l i v) = length l.
Proof. intros. unfold zupd. destruct (i <? 0); auto using upd_nat_length. Qed.

Lemma zlength_zupd : forall l i v, zlength (zupd l i v) = zlength l.
Proof. intros. unfold zlength. rewrite zupd_length. reflexivity. Qed.

Lemma nth_upd_nat_same : forall l i v, (i < length l)%nat -> nth i (upd_nat l i v) 0 = v.
Proof. induction l; intros [|i] v H; cbn in *; try lia; auto. apply IHl. lia. Qed.

Lemma nth_upd_nat_other : forall l i j v, i <> j -> nth j (upd_nat l i v) 0 = nth j l 0.
Proof. induction l; intros [|i] [|j] v H; cbn; auto; try congruence. Qed.

Lemma znth_zupd_eq : forall l i v, 0 <= i < zlength l -> znth (zupd l i v) i = v.
Proof.
  intros l i v H. unfold znth, zupd, zlength in *.
  destruct (Z.ltb_spec i 0); [lia|]. apply nth_upd_nat_same. lia.
Qed.

Lemma znth_zupd_neq : forall l i j v, i <> j -> znth (zupd l i v) j = znth l j.
Proof.
  intros l i j v H. unfold znth, zupd.
  destruct (Z.ltb_spec j 0); [reflexivity|]. destruct (Z.ltb_spec i 0); [reflexivity|].
  apply nth_upd_nat_other. intros E. apply H. lia.
Qed.

Lemma znth_range : forall l i, 0 <= i < zlength l -> In (znth l i) l.
Proof.
  intros l i H. unfold znth, zlength in *. destruct (Z.ltb_spec i 0); [lia|].
  apply nth_In. lia.
Qed.

(* [comment removed for export] *)
Definition zrepeat (v : Z) (n : Z) : list Z := repeat v (Z.to_nat n).
Lemma zlength_zrepeat : forall v n, 0 <= n -> zlength (zrepeat v n) = n.
Proof. intros. unfold zlength, zrepeat. rewrite repeat_length. lia. Qed.
