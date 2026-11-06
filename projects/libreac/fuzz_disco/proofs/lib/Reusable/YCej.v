(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Generated for fuzz_disco's asan-ubsan image: the trace lists are a Theorem Labs lane's gen_traces.py output on
   fuzz_disco.asan-ubsan (ipc malloc 0x536f8 / free 0x53598, frame-keeping LLVMFuzzerTestOneInput returning to 0x80eb8),
   equal set-wise to the 12 malloc / free traces of a Theorem Labs lane's measured TRLIST; the register_globals trace lives in YF0m's
   TFIB_TR0, as in the donor. The CTX_ contexts are the donor's call-site return addresses carried through the function-pair
   offsets. cgif's program contexts (cgif_newgif, read_frameconfig, ...) have no disco counterpart and are dropped. *)
From Stdlib Require Import ZArith List Bool Lia.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YG00 YG01.
Import ListNotations.
Local Open Scope Z_scope.
Definition CTX_main : list (list Z) :=
[[0x8fbf8]].
Definition TRACES_main : list (list Z) :=
[[0x536f8; 0x80b70];
[0x536f8; 0x80bc4];
[0x53598; 0x80be8];
[0x53598; 0x80d18]].
Definition CTX_target_alloc_init : list (list Z) :=
[[0x80c7c]].
Definition CTX_target_alloc_count : list (list Z) :=
[[0x80ca0]].
Definition CTX_target_run : list (list Z) :=
[[0x80c90]].
Definition TRACES_target_run : list (list Z) :=
[[0x536f8; 0x80e50];
[0x53598; 0x80ee4]].
Definition CTX_emit_printf : list (list Z) :=
[[0x80ec8]].
Definition CTX_LLVMFuzzerTestOneInput : list (list Z) :=
[[0x80eb8]].
Definition TRACES_LLVMFuzzerTestOneInput : list (list Z) :=
[[0x536f8; 0x816b8];
[0x536f8; 0x816b8; 0x80eb8];
[0x536f8; 0x81aac];
[0x536f8; 0x81aac; 0x80eb8];
[0x536f8; 0x81d30];
[0x536f8; 0x81d30; 0x80eb8];
[0x53598; 0x82cf0];
[0x53598; 0x82cf0; 0x80eb8];
[0x53598; 0x83224];
[0x53598; 0x83224; 0x80eb8];
[0x53598; 0x83464];
[0x53598; 0x83464; 0x80eb8]].
Definition Tfib_universe : list (list Z) :=
[[0x53598];
[0x53598; 0x80be8];
[0x53598; 0x80d18];
[0x53598; 0x80ee4];
[0x53598; 0x82cf0];
[0x53598; 0x82cf0; 0x80eb8];
[0x53598; 0x83224];
[0x53598; 0x83224; 0x80eb8];
[0x53598; 0x83464];
[0x53598; 0x83464; 0x80eb8];
[0x536f8];
[0x536f8; 0x80b70];
[0x536f8; 0x80bc4];
[0x536f8; 0x80e50];
[0x536f8; 0x816b8];
[0x536f8; 0x816b8; 0x80eb8];
[0x536f8; 0x81aac];
[0x536f8; 0x81aac; 0x80eb8];
[0x536f8; 0x81d30];
[0x536f8; 0x81d30; 0x80eb8]].

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
