(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec SeqExec.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.

Fixpoint regupds (base : bvmap 5 word) (ks : list reg) (vs : list word) : bvmap 5 word :=
  match ks, vs with
  | k :: kt, v :: vt => regupd (regupds base kt vt) k v
  | _, _ => base
  end.

Fixpoint ridx (r : reg) (ks : list reg) : option nat :=
  match ks with
  | [] => None
  | k :: kt => if bv_eqb k r then Some 0%nat else option_map S (ridx r kt)
  end.

Definition rsel (base : bvmap 5 word) (vs : list word) (r : reg) (o : option nat) : word :=
  match o with Some i => nth i vs (getr base r) | None => getr base r end.

Lemma gf_bv_eqb_true_eq : forall {n} (a b : bv n), bv_eqb a b = true -> a = b.
Proof. intros n a b H. unfold bv_eqb in H. apply Z.eqb_eq in H. apply bv_eq. exact H. Qed.
Lemma gf_bv_eqb_false_neq : forall {n} (a b : bv n), bv_eqb a b = false -> a <> b.
Proof. intros n a b H E. subst b. unfold bv_eqb in H. rewrite Z.eqb_refl in H. discriminate H. Qed.

Lemma getr_regupds : forall ks vs base r, length ks = length vs -> bv_eqb r 0 = false ->
  getr (regupds base ks vs) r = rsel base vs r (ridx r ks).
Proof.
  induction ks as [|k kt IH]; intros vs base r Hl Hr.
  - reflexivity.
  - destruct vs as [|v vt]; [discriminate Hl|]. cbn [regupds ridx]. injection Hl as Hl.
    destruct (bv_eqb k r) eqn:E.
    + apply gf_bv_eqb_true_eq in E. subst k. cbn [rsel nth]. apply getr_same. apply gf_bv_eqb_false_neq. exact Hr.
    + rewrite getr_other by (apply not_eq_sym; apply gf_bv_eqb_false_neq; exact E).
      rewrite (IH vt base r Hl Hr). destruct (ridx r kt); reflexivity.
Qed.

(* [comment removed for export] *)
From Ltac2 Require Ltac2.
Module GresFastL2.
  Import Ltac2.
  Ltac2 mk_cons (ty : constr) (x : constr) (l : constr) : constr :=
    Constr.Unsafe.make (Constr.Unsafe.App constr:(@cons) (Array.of_list [ty; x; l])).
  Ltac2 rec reify (m : constr) : constr * constr * constr * (constr list) :=
    lazy_match! m with
    | regupd ?m1 ?k ?v =>
        let (ks, vs, b, vl) := reify m1 in
        (mk_cons constr:(reg) k ks, mk_cons constr:(word) v vs, b, v :: vl)
    | _ => (constr:(@nil reg), constr:(@nil word), m, [])
    end.
  Ltac2 rec nat_to_int (n : constr) : int :=
    lazy_match! n with
    | O => 0
    | S ?j => Int.add 1 (nat_to_int j)
    end.
  (* [comment removed for export] *)
  Ltac2 one () :=
    match! goal with
    | [ |- context [getr (regupd ?m ?k ?v) ?r] ] =>
        let chain := constr:(regupd $m $k $v) in
        let (ks, vs, b, vl) := reify chain in
        let o := Std.eval_vm None constr:(ridx $r $ks) in
        let rhs := lazy_match! o with
                   | Some ?i => List.nth vl (nat_to_int i)
                   | None => constr:(getr $b $r)
                   end in
        let e := Fresh.in_goal @Egf in
        assert ($e : getr $chain $r = $rhs) by (exact (getr_regupds $ks $vs $b $r (eq_refl _) (eq_refl false)));
        let eh := Control.hyp e in
        ltac1:(E |- rewrite E; clear E) (Ltac1.of_constr eh)
    end.
End GresFastL2.
Ltac gf_one := ltac2:(GresFastL2.one ()).
(* [comment removed for export] *)
Ltac gres_slow :=
  repeat first [ rewrite getr_same by reg_neq_tac
               | rewrite getr_other by reg_neq_tac ];
  rewrite ?getr_zero.
Ltac gres_fast :=
  rewrite ?getr_zero;      (* [comment removed for export] *)
  repeat gf_one;
  lazymatch goal with
  | |- context [getr (regupd _ _ _) _] => gres_slow     (* [comment removed for export] *)
  | |- _ => rewrite ?getr_zero
  end.

(* [comment removed for export] *)
Ltac with_mems k :=
  match goal with
  | |- context [@mkst _ _ _ ?m _] =>
      assert_fails (is_var m);
      let M := fresh "gfM" in set (M := m); with_mems k; subst M
  | _ => k
  end.

