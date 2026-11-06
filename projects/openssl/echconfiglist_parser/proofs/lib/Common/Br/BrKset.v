(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Bool Lia.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib Require Import AxSymExec3 AxSymExec3Sound AxSymExec3B AsanPlanCore AsanPlan AsanPlanSound.
Import AX2S. Import AX2B.
Import ListNotations. Import AX2. Import APC.
Open Scope Z_scope.

Definition zkey (z : Z) : Z := if Z.leb 0 z then 2 * z else 1 - 2 * z.
Definition lkey (e : expr) : Z := match e with ELit z => zkey z | _ => 0 end.
Definition kkeyZ (K : kentry) : Z :=
  match K with
  | KWord a w _ => 1 + 16 * (zkey (a_off a) + 8 * Z.of_nat w)
  | KZero a n => 2 + 16 * (zkey (a_off a) + 4 * lkey n)
  | KBlob a n _ => 3 + 16 * (zkey (a_off a) + 4 * lkey n)
  | KImg lo hi => 4 + 16 * (zkey lo + 4 * zkey (hi - lo))
  | KAlign e m => 5 + 16 * zkey m
  | KRange e lo hi => 6 + 16 * (zkey lo + 4 * zkey (hi - lo))
  | KWr a n => 7 + 16 * (zkey (a_off a) + 4 * lkey n)
  | KDisj a1 n1 a2 n2 => 8 + 16 * (zkey (a_off a1) + 4 * (lkey n1 + 4 * (zkey (a_off a2) + 4 * lkey n2)))
  | KFill a n c => 9 + 16 * (zkey (a_off a) + 4 * (lkey n + 4 * zkey c))
  | KUnk a n => 10 + 16 * (zkey (a_off a) + 4 * lkey n)
  end%Z.
Definition kkey (K : kentry) : positive := Z.to_pos (1 + Z.abs (kkeyZ K)).
Definition kset : Type := ptree (list kentry).
Definition kset_bucket (s : kset) (p : positive) : list kentry :=
  match pt_get s p with Some l => l | None => [] end.
Definition kset_add (K : kentry) (s : kset) : kset := pt_set (kkey K) (K :: kset_bucket s (kkey K)) s.
Definition kset_of (k : list kentry) : kset := List.fold_right kset_add PTLeaf k.
Definition kset_mem (s : kset) (K : kentry) : bool := existsb (fun X => kentry_eqb X K) (kset_bucket s (kkey K)).
Lemma c_saddr_eqb_eq : forall a b, saddr_eqb a b = true -> a = b.
Proof. exact saddr_eqb_eq. Qed.
Lemma c_kentry_eqb_eq : forall x y, kentry_eqb x y = true -> x = y.
Proof. exact (APS.kentry_eqb_eq). Qed.
Lemma c_saddr_eqb_refl : forall a, saddr_eqb a a = true.
Proof. intros [b o]. unfold saddr_eqb. cbn [a_base a_off]. rewrite kx_expr_eqb_refl, Z.eqb_refl. reflexivity. Qed.
Lemma c_kentry_eqb_refl : forall x, kentry_eqb x x = true.
Proof.
  intros x. destruct x; cbn [kentry_eqb]; rewrite ?c_saddr_eqb_refl, ?kx_expr_eqb_refl, ?Nat.eqb_refl, ?Z.eqb_refl; cbn; rewrite ?c_saddr_eqb_refl, ?kx_expr_eqb_refl, ?Nat.eqb_refl, ?Z.eqb_refl; cbn; rewrite ?kx_expr_eqb_refl, ?Nat.eqb_refl, ?Z.eqb_refl; reflexivity.
Qed.
Lemma kentry_eqb_sym : forall x y, kentry_eqb x y = kentry_eqb y x.
Proof.
  intros x y. destruct (kentry_eqb x y) eqn:E1; destruct (kentry_eqb y x) eqn:E2; try reflexivity.
  - apply c_kentry_eqb_eq in E1. subst. rewrite c_kentry_eqb_refl in E2. discriminate.
  - apply c_kentry_eqb_eq in E2. subst. rewrite c_kentry_eqb_refl in E1. discriminate.
Qed.
Lemma kset_bucket_add : forall K s p,
  kset_bucket (kset_add K s) p = if Pos.eqb p (kkey K) then K :: kset_bucket s p else kset_bucket s p.
Proof.
  intros K s p. unfold kset_add, kset_bucket at 1. destruct (Pos.eqb_spec p (kkey K)) as [->|NE].
  - rewrite pt_gss. reflexivity.
  - rewrite pt_gso by exact NE. reflexivity.
Qed.
Lemma kset_mem_of : forall k K, kset_mem (kset_of k) K = existsb (fun X => kentry_eqb X K) k.
Proof.
  intros k K. unfold kset_mem. induction k as [|X r IH].
  - cbn [kset_of fold_right]. unfold kset_bucket. rewrite pt_get_leaf. reflexivity.
  - cbn [kset_of fold_right existsb]. fold (kset_of r). rewrite kset_bucket_add.
    destruct (Pos.eqb_spec (kkey K) (kkey X)) as [E|NE].
    + cbn [existsb]. rewrite IH. reflexivity.
    + rewrite IH. destruct (kentry_eqb X K) eqn:EQ; [|reflexivity].
      apply c_kentry_eqb_eq in EQ. subst. congruence.
Qed.
Lemma kset_mem_of' : forall k K, kset_mem (kset_of k) K = existsb (kentry_eqb K) k.
Proof.
  intros k K. rewrite kset_mem_of. induction k as [|X r IH]; [reflexivity|]. cbn [existsb]. rewrite IH, kentry_eqb_sym. reflexivity.
Qed.
