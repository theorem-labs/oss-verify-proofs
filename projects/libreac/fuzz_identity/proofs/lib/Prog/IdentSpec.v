From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
Import ListNotations.
Open Scope Z_scope.

Definition dg (x : Z) : byte := Z_to_bv 8 (0x30 + x).

Fixpoint dec_digits (fuel : nat) (x : Z) : list byte :=
  match fuel with
  | O => []
  | S n => (if x <? 10 then [] else dec_digits n (x / 10)) ++ [dg (x mod 10)]
  end.

Definition DEC (x m : Z) : list byte :=
  repeat (dg 0) (Z.to_nat m - length (dec_digits (S (Z.to_nat (Z.log2 x))) x))
  ++ dec_digits (S (Z.to_nat (Z.log2 x))) x.

Fixpoint z_all (p : Z -> bool) (n : nat) (z : Z) : bool :=
  match n with
  | O => true
  | S k => if p z then z_all p k (z + 1) else false
  end.

Lemma z_all_spec : forall p n z, z_all p n z = true -> forall y, z <= y < z + Z.of_nat n -> p y = true.
Proof.
  intros p n. induction n as [|k IH]; intros z H y Hy; [lia|].
  cbn [z_all] in H. destruct (p z) eqn:E; [|discriminate].
  destruct (Z.eq_dec y z) as [->|Hne]; [exact E|].
  apply (IH (z + 1) H). lia.
Qed.

Fixpoint bytes_eqb (xs ys : list byte) : bool :=
  match xs, ys with
  | [], [] => true
  | x :: xs', y :: ys' => (bv_unsigned x =? bv_unsigned y) && bytes_eqb xs' ys'
  | _, _ => false
  end.

Lemma bytes_eqb_eq : forall xs ys, bytes_eqb xs ys = true -> xs = ys.
Proof.
  induction xs as [|x xs IH]; intros [|y ys] H; cbn [bytes_eqb] in H; try discriminate; [reflexivity|].
  apply andb_true_iff in H as [H1 H2]. apply Z.eqb_eq in H1.
  f_equal; [apply bv_eq; exact H1 | apply IH; exact H2].
Qed.
