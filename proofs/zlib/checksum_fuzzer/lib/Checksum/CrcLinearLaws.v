From Stdlib Require Import ZArith NArith List Lia Bool.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Checksum Require Import CrcAlgebra CrcGenModel CrcLinearBasis.
Open Scope Z_scope.
Lemma gen_step_functional : forall n p, (n < 255)%nat -> 0 <= p < 2^32 ->
  mm (gen_value (S n)) p = csteps 8 (mm (gen_value n) p).
Proof.
  intros n p Hn Hp. eapply linear32_equal with
    (f:=fun x => mm (gen_value (S n)) x)
    (g:=fun x => csteps 8 (mm (gen_value n) x));
    [apply mm_0| | | | |exact Hp].
  - rewrite mm_0. apply csteps_zero.
  - intros a b. apply mm_lxor.
  - intros a b. rewrite mm_lxor, csteps_xor. reflexivity.
  - intros i Hi. apply gen_step_basis;assumption.
Qed.
Lemma mm_identity : forall p, mm (2^31) p = p.
Proof.
  intros p. change (mm_loop (S 31) (2^31) (2^31) p 0 = p).
  rewrite mm_loop_exit by (vm_compute;congruence). apply Z.lxor_0_l.
Qed.
Lemma gen_value_zero : gen_value 0 = 2^31.
Proof. vm_compute. reflexivity. Qed.
Theorem gen_value_advance : forall n, (n <= 255)%nat -> forall p, 0 <= p < 2^32 ->
  mm (gen_value n) p = csteps (8*n) p.
Proof.
  induction n as [|n IH];intros Hn p Hp.
  - rewrite gen_value_zero,mm_identity. reflexivity.
  - rewrite gen_step_functional by lia. rewrite IH by lia.
    replace (8*S n)%nat with (8+8*n)%nat by lia. rewrite csteps_add. reflexivity.
Qed.
Theorem bounded_combine_advance : forall n p, 0 <= n <= 255 -> 0 <= p < 2^32 ->
  mm (combine_gen_model n) p = csteps (8 * Z.to_nat n) p.
Proof.
  intros n p Hn Hp.
  pose proof (gen_value_correct (Z.to_nat n) ltac:(lia)) as E.
  rewrite Z2Nat.id in E by lia. rewrite <- E. apply gen_value_advance;lia.
Qed.
