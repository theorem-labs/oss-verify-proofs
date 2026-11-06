(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Sem.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.AS Require Import PropExec AxSymExec3 AxSymExec3Sound.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2. Import AX2S.
Open Scope Z_scope.

Fixpoint terms_eqb (a b : list (Z * expr)) : bool :=
  match a, b with
  | [], [] => true
  | (k, x) :: a', (k', y) :: b' => (Z.eqb k k' && expr_eqb x y && terms_eqb a' b')%bool
  | _, _ => false
  end.
Definition leq (a b : expr) : bool :=
  let x := lin_of a in let y := lin_of b in (Z.eqb (fst x) (fst y) && terms_eqb (snd x) (snd y))%bool.

Definition esub2 (a b : expr) : expr := EAlu ALU_SUB a b.
Definition eaddl (a : expr) (k : Z) : expr := EAlu ALU_ADD a (ELit k).
Definition x4 (v : nat) : expr := EExt false 0 4 (EVar v).
Definition x1 (v : nat) : expr := EExt false 0 1 (EVar v).
(* [comment removed for export] *)
Definition nsub (a b : expr) : expr := unlin (ladd (lin_of a) (lscale (-1) (lin_of b))).

Local Notation u := bv_unsigned.

Lemma u_rngL : forall (w : word), 0 <= u w < 2 ^ 64.
Proof. intros w. pose proof (bv_unsigned_in_range _ w) as H. unfold bv_modulus in H. exact H. Qed.
Lemma u_litmL : forall z, u (Z_to_bv 64 z) = z mod 2 ^ 64.
Proof. intros z. rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. reflexivity. Qed.
Lemma u_eaddlL : forall E a k, u (edenot E (eaddl a k)) = (u (edenot E a) + k mod 2 ^ 64) mod 2 ^ 64.
Proof. intros E a k. unfold eaddl. cbn [edenot]. rewrite alu_add. unfold v_add. rewrite !u_litmL. reflexivity. Qed.

Lemma terms_eqb_eq : forall a b, terms_eqb a b = true -> a = b.
Proof.
  induction a as [|[k x] a IH]; intros [|[k' y] b] H; cbn [terms_eqb] in H; try discriminate; [reflexivity|].
  apply andb_prop in H as [H1 H2]. apply andb_prop in H1 as [H1 H3]. apply Z.eqb_eq in H1. apply expr_eqb_eq in H3.
  rewrite (IH _ H2). subst. reflexivity.
Qed.

Lemma leq_lin : forall a b, leq a b = true -> lin_of a = lin_of b.
Proof.
  intros a b H. unfold leq in H. apply andb_prop in H as [H1 H2]. apply Z.eqb_eq in H1. apply terms_eqb_eq in H2.
  destruct (lin_of a), (lin_of b). cbn in *. subst. reflexivity.
Qed.

Lemma leq_den : forall E a b, leq a b = true -> edenot E a = edenot E b.
Proof.
  intros E a b H. apply leq_lin in H.
  pose proof (lin_of_sound E a) as Ha. pose proof (lin_of_sound E b) as Hb. rewrite H in Ha.
  assert (Q : eqm (uE E a) (uE E b)) by (eapply eqm_trans; [apply eqm_sym; exact Ha | exact Hb]).
  apply bv_eq. unfold uE in Q. destruct Q as [q Hq].
  pose proof (u_rngL (edenot E a)). pose proof (u_rngL (edenot E b)).
  assert (q = 0) by nia. subst q. lia.
Qed.

Lemma nsub_den : forall E a b, edenot E (nsub a b) = alu64 ALU_SUB (edenot E a) (edenot E b).
Proof. intros E a b. unfold nsub. apply unlin_lsub. Qed.

(* [comment removed for export] *)
Lemma adenot_lin : forall E a B P j, leq (eaddl (a_base a) (a_off a)) (eaddl (EAlu ALU_ADD B P) j) = true -> 0 <= j ->
  u (edenot E B) + u (edenot E P) + j < 2 ^ 64 -> u (adenot E a) = u (edenot E B) + u (edenot E P) + j.
Proof.
  intros E a B P j H Hj Hr. pose proof (leq_den E _ _ H) as D. apply (f_equal u) in D.
  rewrite !u_eaddlL in D. cbn [edenot] in D. rewrite alu_add in D. unfold v_add in D. rewrite u_litmL in D.
  unfold adenot, v_addi. rewrite u_litmL. rewrite Z.add_mod_idemp_r in D by lia. rewrite D.
  pose proof (u_rngL (edenot E B)). pose proof (u_rngL (edenot E P)).
  rewrite (Z.mod_small (u (edenot E B) + u (edenot E P))) by lia. rewrite (Z.mod_small j) by lia. apply Z.mod_small. lia.
Qed.
