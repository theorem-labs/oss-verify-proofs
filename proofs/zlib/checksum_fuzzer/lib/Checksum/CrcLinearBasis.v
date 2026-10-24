(** CRC linear maps and a bounded operator certificate for the binary's
    one-byte chunk size. The payload size is not restricted by this lemma. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Checksum Require Import CrcAlgebra CrcGenModel.
Import ListNotations.
Open Scope Z_scope.

Theorem linear32_equal : forall (f g : Z -> Z),
  f 0 = 0 -> g 0 = 0 ->
  (forall a b, f (Z.lxor a b) = Z.lxor (f a) (f b)) ->
  (forall a b, g (Z.lxor a b) = Z.lxor (g a) (g b)) ->
  (forall i, (i < 32)%nat -> f (2 ^ Z.of_nat i) = g (2 ^ Z.of_nat i)) ->
  forall p, 0 <= p < 2^32 -> f p = g p.
Proof.
  intros f g F0 G0 FL GL BASIS.
  assert (H : forall n, (n <= 32)%nat -> forall p, 0 <= p < 2 ^ Z.of_nat n -> f p = g p).
  { induction n as [|n IH]; intros Hn p Hp.
    - assert (p=0) by (cbn in Hp;lia). subst. congruence.
    - destruct (Z_lt_ge_dec p (2 ^ Z.of_nat n)) as [LT|GE].
      + apply IH;lia.
      + rewrite Nat2Z.inj_succ in Hp. rewrite <- Z.add_1_r in Hp.
        pose proof (lxor_pow2_split p (Z.of_nat n) ltac:(lia) ltac:(lia)) as E.
        set (q := p - 2 ^ Z.of_nat n) in E.
        assert (Hq : 0 <= q < 2 ^ Z.of_nat n).
        { subst q. rewrite Z.pow_add_r in Hp by lia. change (2^1) with 2 in Hp. lia. }
        rewrite E, FL, GL, (IH ltac:(lia) q Hq), BASIS by lia. reflexivity. }
  exact (H 32%nat ltac:(lia)).
Qed.
Fixpoint csteps (n : nat) (p : Z) : Z :=
  match n with O => p | S n' => cstep (csteps n' p) end.
Lemma csteps_zero : forall n, csteps n 0 = 0.
Proof. induction n;cbn;[reflexivity|rewrite IHn;apply cstep_0]. Qed.
Lemma csteps_xor : forall n a b, csteps n (Z.lxor a b) = Z.lxor (csteps n a) (csteps n b).
Proof. induction n;intros;cbn;[reflexivity|rewrite IHn;apply cstep_lxor]. Qed.
Lemma csteps_add : forall n k p, csteps (n+k) p = csteps n (csteps k p).
Proof. induction n;intros;cbn;[reflexivity|rewrite IHn;reflexivity]. Qed.
Lemma csteps_range : forall n p, 0 <= p < 2^32 -> 0 <= csteps n p < 2^32.
Proof. induction n;intros;cbn;[exact H|apply cstep_range,IHn,H]. Qed.

Definition gen_values : list Z := Eval vm_compute in
  map (fun n => combine_gen_model (Z.of_nat n)) (seq 0 256).
Definition gen_value (n : nat) := nth n gen_values 0.
Definition gen_values_check : bool := forallb
  (fun n => gen_value n =? combine_gen_model (Z.of_nat n)) (seq 0 256).
Lemma gen_values_checked : gen_values_check = true.
Proof. vm_compute. reflexivity. Qed.
Lemma gen_value_correct : forall n, (n < 256)%nat ->
  gen_value n = combine_gen_model (Z.of_nat n).
Proof.
  intros n Hn. apply Z.eqb_eq.
  exact (forallb_seq _ 0 256 n gen_values_checked ltac:(lia)).
Qed.
Definition gen_step_check : bool := forallb
  (fun n => forallb (fun i =>
    mm (gen_value (S n)) (2 ^ Z.of_nat i) =?
    csteps 8 (mm (gen_value n) (2 ^ Z.of_nat i))) (seq 0 32)) (seq 0 255).
Lemma gen_step_checked : gen_step_check = true.
Proof. vm_compute. reflexivity. Qed.
Lemma gen_step_basis : forall n i, (n < 255)%nat -> (i < 32)%nat ->
  mm (gen_value (S n)) (2 ^ Z.of_nat i) =
    csteps 8 (mm (gen_value n) (2 ^ Z.of_nat i)).
Proof.
  intros n i Hn Hi. apply Z.eqb_eq.
  exact (forallb_seq _ 0 32 i
    (forallb_seq _ 0 255 n gen_step_checked ltac:(lia)) ltac:(lia)).
Qed.
