(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/A/ACej.v, with its module paths changed; the call contexts and allocation traces are libreac/fuzz_grant's, read from fuzz_grant.asan: the calls of the malloc and free wrappers' 4-byte jumps (0x52b50, 0x52b4c) in main, target_run and LLVMFuzzerTestOneInput, each trace closed under prefixes. libunwind's DwarfFDECache::add calls those jumps too (at 0x861e0 and 0x86204), and this list leaves its two traces out: that cache is reached only from a report of an error, which the proof shows is not reached. *)
From Stdlib Require Import ZArith List Bool Lia.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YG00 YG01.
Import ListNotations.
Local Open Scope Z_scope.
Definition CTX_main : list (list Z) :=
[[0x8bb14]].
Definition TRACES_main : list (list Z) :=
[[0x52c8c; 0x802dc];
[0x52c8c; 0x8040c];
[0x52dec; 0x80264];
[0x52dec; 0x802b8]].
Definition CTX_target_alloc_init : list (list Z) :=
[[0x80370]].
Definition CTX_target_alloc_count : list (list Z) :=
[[0x80394]].
Definition CTX_target_run : list (list Z) :=
[[0x80384]].
Definition TRACES_target_run : list (list Z) :=
[[0x52c8c; 0x805d8];
[0x52dec; 0x80544]].
Definition CTX_emit_printf : list (list Z) :=
[[0x805bc]].
Definition CTX_LLVMFuzzerTestOneInput : list (list Z) :=
[[0x805ac]].
Definition TRACES_LLVMFuzzerTestOneInput : list (list Z) :=
[[0x52c8c; 0x812a0];
[0x52c8c; 0x812a0; 0x805ac];
[0x52c8c; 0x813b8];
[0x52c8c; 0x813b8; 0x805ac];
[0x52c8c; 0x817d0];
[0x52c8c; 0x817d0; 0x805ac];
[0x52dec; 0x80994];
[0x52dec; 0x80994; 0x805ac];
[0x52dec; 0x80e90];
[0x52dec; 0x80e90; 0x805ac];
[0x52dec; 0x8132c];
[0x52dec; 0x8132c; 0x805ac]].
Definition Tfib_universe : list (list Z) :=
[[0x52c8c];
[0x52c8c; 0x802dc];
[0x52c8c; 0x8040c];
[0x52c8c; 0x805d8];
[0x52c8c; 0x812a0];
[0x52c8c; 0x812a0; 0x805ac];
[0x52c8c; 0x813b8];
[0x52c8c; 0x813b8; 0x805ac];
[0x52c8c; 0x817d0];
[0x52c8c; 0x817d0; 0x805ac];
[0x52dec];
[0x52dec; 0x80264];
[0x52dec; 0x802b8];
[0x52dec; 0x80544];
[0x52dec; 0x80994];
[0x52dec; 0x80994; 0x805ac];
[0x52dec; 0x80e90];
[0x52dec; 0x80e90; 0x805ac];
[0x52dec; 0x8132c];
[0x52dec; 0x8132c; 0x805ac]].
Fixpoint listZ_eqb (a b : list Z) : bool :=
match a, b with [], [] => true | x :: a', y :: b' => Z.eqb x y && listZ_eqb a' b' | _, _ => false end.
Fixpoint memZL (t : list Z) (l : list (list Z)) : bool :=
match l with [] => false | u :: l' => listZ_eqb t u || memZL t l' end.
Lemma listZ_eqb_eq : forall a b, listZ_eqb a b = true -> a = b.
Proof.
induction a as [|x a IH]; destruct b as [|y b]; cbn; intros H; try discriminate; [reflexivity|].
apply andb_prop in H as [H1 H2]. apply Z.eqb_eq in H1. f_equal; [exact H1 | apply IH, H2].
Qed.
Lemma memZL_In : forall t l, memZL t l = true -> In t l.
Proof.
induction l as [|u l IH]; cbn; intros H; [discriminate|].
apply Bool.orb_prop in H as [H|H]; [left; symmetry; apply listZ_eqb_eq, H | right; apply IH, H].
Qed.
Fixpoint allb {X} (f : X -> bool) (l : list X) : bool := match l with [] => true | x :: l' => f x && allb f l' end.
Lemma allb_In : forall {X} (f : X -> bool) l x, allb f l = true -> In x l -> f x = true.
Proof. induction l; cbn; intros x H Hin; [destruct Hin|]. apply andb_prop in H as [H1 H2]. destruct Hin as [<-|Hin]; auto. Qed.
Lemma TRACES_main_U : forall t, In t TRACES_main -> In t Tfib_universe.
Proof. intros t H. apply memZL_In. exact (allb_In (fun t => memZL t Tfib_universe) TRACES_main t ltac:(vm_compute; reflexivity) H). Qed.
Lemma TRACES_target_run_U : forall t, In t TRACES_target_run -> In t Tfib_universe.
Proof. intros t H. apply memZL_In. exact (allb_In (fun t => memZL t Tfib_universe) TRACES_target_run t ltac:(vm_compute; reflexivity) H). Qed.
Lemma TRACES_LLVMFuzzerTestOneInput_U : forall t, In t TRACES_LLVMFuzzerTestOneInput -> In t Tfib_universe.
Proof. intros t H. apply memZL_In. exact (allb_In (fun t => memZL t Tfib_universe) TRACES_LLVMFuzzerTestOneInput t ltac:(vm_compute; reflexivity) H). Qed.
Fixpoint nodupZL (l : list (list Z)) : bool :=
match l with [] => true | t :: l' => negb (memZL t l') && nodupZL l' end.
Lemma memZL_false : forall t l, memZL t l = false -> ~ In t l.
Proof.
induction l as [|u l IH]; cbn; intros H Hin; [exact Hin|].
apply Bool.orb_false_elim in H as [H1 H2]. destruct Hin as [<-|Hin]; [|exact (IH H2 Hin)].
assert (E : forall a, listZ_eqb a a = true) by (induction a; cbn; [reflexivity|]; rewrite Z.eqb_refl; assumption).
rewrite E in H1. discriminate.
Qed.
Lemma nodupZL_NoDup : forall l, nodupZL l = true -> NoDup l.
Proof.
induction l as [|t l IH]; cbn; intros H; [constructor|].
apply andb_prop in H as [H1 H2]. constructor; [apply memZL_false; destruct (memZL t l); [discriminate|reflexivity] | apply IH, H2].
Qed.
Lemma Tfib_universe_ok : universe_ok Tfib_universe.
Proof.
split; [unfold DEPOT_MAX; (first [lazymatch goal with |- _ <> @nil _ => discriminate end | vm_compute; discriminate])|]. split.
- apply Forall_forall. intros t Ht.
pose proof (allb_In (fun t : list Z => (length t <=? kUnwindMax)%nat) Tfib_universe t ltac:(vm_compute; reflexivity) Ht) as H.
apply Nat.leb_le in H. exact H.
- apply nodupZL_NoDup. vm_compute. reflexivity.
Qed.
