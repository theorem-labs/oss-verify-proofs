(** Exact byte-index expressions used by the fixed five-chain CRC loop. *)
From Stdlib Require Import ZArith NArith List Lia Bool Btauto.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Checksum Require Import CrcAlgebra CrcLib CrcWord.
Open Scope Z_scope.
Theorem linear64_equal : forall (f g : Z -> Z),
  f 0 = 0 -> g 0 = 0 ->
  (forall a b, f (Z.lxor a b) = Z.lxor (f a) (f b)) ->
  (forall a b, g (Z.lxor a b) = Z.lxor (g a) (g b)) ->
  (forall i, (i < 64)%nat -> f (2 ^ Z.of_nat i) = g (2 ^ Z.of_nat i)) ->
  forall p, 0 <= p < 2^64 -> f p = g p.
Proof.
  intros f g F0 G0 FL GL BASIS.
  assert (H : forall n, (n <= 64)%nat -> forall p, 0 <= p < 2 ^ Z.of_nat n -> f p = g p).
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
  exact (H 64%nat ltac:(lia)).
Qed.
Lemma land_mask_linear : forall a b mask,
  Z.land (Z.lxor a b) mask = Z.lxor (Z.land a mask) (Z.land b mask).
Proof. intros. apply Z.bits_inj'. intros n Hn. repeat (rewrite Z.land_spec || rewrite Z.lxor_spec). btauto. Qed.
Definition braid_index_machine (j : nat) (a : Z) : Z :=
  match j with
  | O => Z.shiftl (Z.land a 255) 2
  | S O => Z.land (Z.shiftr a 6) 1020
  | S (S O) => Z.land (Z.shiftr a 14) 1020
  | _ => Z.shiftl (Z.shiftr (a mod 2^32) 24) 2
  end.
Definition braid_index_expected (j : nat) (a : Z) : Z :=
  Z.shiftl (Z.land (Z.shiftr (a mod 2^32) (8*Z.of_nat j)) 255) 2.
Lemma braid_index_machine_zero : forall j, braid_index_machine j 0 = 0.
Proof. intros [|[|[|j]]];reflexivity. Qed.
Lemma braid_index_expected_zero : forall j, braid_index_expected j 0 = 0.
Proof. intros. unfold braid_index_expected. change (0 mod 2^32) with 0. rewrite Z.shiftr_0_l. reflexivity. Qed.
Lemma braid_index_machine_linear : forall j a b,
  braid_index_machine j (Z.lxor a b) = Z.lxor (braid_index_machine j a) (braid_index_machine j b).
Proof.
  intros [|[|[|j]]] a b;unfold braid_index_machine;
    rewrite ?Z.shiftr_lxor,?low32_xor,?Z.shiftr_lxor,?land_mask_linear,?Z.shiftl_lxor;reflexivity.
Qed.
Lemma braid_index_expected_linear : forall j a b,
  braid_index_expected j (Z.lxor a b) = Z.lxor (braid_index_expected j a) (braid_index_expected j b).
Proof. intros. unfold braid_index_expected. rewrite low32_xor,Z.shiftr_lxor,land_mask_linear,Z.shiftl_lxor. reflexivity. Qed.
Definition braid_index_check := List.forallb (fun j => List.forallb (fun i =>
  braid_index_machine j (2^Z.of_nat i) =? braid_index_expected j (2^Z.of_nat i)) (List.seq 0 64)) (List.seq 0 4).
Lemma braid_index_checked : braid_index_check = true.
Proof. vm_compute. reflexivity. Qed.
Theorem braid_index_correct : forall j a, (j < 4)%nat -> 0 <= a < 2^64 ->
  braid_index_machine j a = braid_index_expected j a.
Proof.
  intros j a Hj Ha. eapply linear64_equal with (f:=braid_index_machine j) (g:=braid_index_expected j);
    [apply braid_index_machine_zero|apply braid_index_expected_zero|apply braid_index_machine_linear|apply braid_index_expected_linear| |exact Ha].
  intros i Hi. apply Z.eqb_eq.
  exact (forallb_seq _ 0 64 i (forallb_seq _ 0 4 j braid_index_checked ltac:(lia)) ltac:(lia)).
Qed.
Lemma braid_index_low32 : forall j a q, (j < 4)%nat -> 0 <= a < 2^64 -> a mod 2^32 = q ->
  braid_index_machine j a = Z.shiftl (Z.land (Z.shiftr q (8*Z.of_nat j)) 255) 2.
Proof. intros j a q Hj Ha E. rewrite braid_index_correct by assumption. unfold braid_index_expected. rewrite E. reflexivity. Qed.
