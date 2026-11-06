(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: re-derived for libreac/fuzz_boxreg's asan image (fuzz_boxreg.asan sha256 eacfa205) by universe.py 4fd01bdf8b9b (from pautrlen/compose.py CTXALL=1 over fuzz_boxreg.asan, names from its twin's nm; hand decision in decisions.fuzz_boxreg.asan.json): CTX_/TRACES_ per fuzz_boxreg function, 11 allocator traces, Tfib_universe 17; module paths changed *)
From Stdlib Require Import ZArith List Bool Lia.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Reusable Require Import YG00 YG01.
Import ListNotations.
Local Open Scope Z_scope.
Definition CTX_main : list (list Z) :=
[[0x8826c]].
Definition TRACES_main : list (list Z) :=
[[0x52528; 0x7fb78];
[0x52528; 0x7fca8];
[0x52688; 0x7fb00];
[0x52688; 0x7fb54]].
Definition CTX_target_alloc_init : list (list Z) :=
[[0x7fc0c]].
Definition CTX_target_alloc_count : list (list Z) :=
[[0x7fc30]].
Definition CTX_target_run : list (list Z) :=
[[0x7fc20]].
Definition TRACES_target_run : list (list Z) :=
[[0x52528; 0x7fe74];
[0x52688; 0x7fde0]].
Definition CTX_emit_printf : list (list Z) :=
[[0x7fe58]].
Definition CTX_LLVMFuzzerTestOneInput : list (list Z) :=
[[0x7fe48]].
Definition TRACES_LLVMFuzzerTestOneInput : list (list Z) :=
[[0x52528; 0x80600];
[0x52528; 0x80600; 0x7fe48];
[0x52528; 0x80aac];
[0x52528; 0x80aac; 0x7fe48];
[0x52528; 0x80e1c];
[0x52528; 0x80e1c; 0x7fe48];
[0x52688; 0x8011c];
[0x52688; 0x8011c; 0x7fe48]].
Definition CTX_check : list (list Z) :=
[[0x801a8];
[0x801a8; 0x7fe48];
[0x80ac0];
[0x80ac0; 0x7fe48]].
Definition CTX_read_name : list (list Z) :=
[[0x80520];
[0x80520; 0x7fe48];
[0x80584];
[0x80584; 0x7fe48]].
Definition TRACES_read_name : list (list Z) :=
[[0x52688; 0x813a0]].
Definition CTX_range_free : list (list Z) :=
[[0x80568];
[0x80568; 0x7fe48];
[0x81578]].
Definition CTX_lowest_free : list (list Z) :=
[[0x80938];
[0x80938; 0x7fe48];
[0x80d10];
[0x80d10; 0x7fe48]].
Definition CTX_reac_boxreg_init : list (list Z) :=
[[0x8017c];
[0x8017c; 0x7fe48]].
Definition CTX_reac_boxreg_find : list (list Z) :=
[[0x80620];
[0x80620; 0x7fe48];
[0x807f8];
[0x807f8; 0x7fe48];
[0x8087c];
[0x8087c; 0x7fe48];
[0x81c74]].
Definition CTX_reac_boxreg_declare : list (list Z) :=
[[0x80960];
[0x80960; 0x7fe48]].
Definition CTX_lowest_free_base : list (list Z) :=
[[0x818ec];
[0x81d9c]].
Definition CTX_reac_boxreg_add : list (list Z) :=
[[0x8080c];
[0x8080c; 0x7fe48];
[0x80890];
[0x80890; 0x7fe48]].
Definition CTX_reac_boxreg_set_name : list (list Z) :=
[[0x805ac];
[0x805ac; 0x7fe48]].
Definition Tfib_universe : list (list Z) :=
[[0x52528];
[0x52528; 0x7fb78];
[0x52528; 0x7fca8];
[0x52528; 0x7fe74];
[0x52528; 0x80600];
[0x52528; 0x80600; 0x7fe48];
[0x52528; 0x80aac];
[0x52528; 0x80aac; 0x7fe48];
[0x52528; 0x80e1c];
[0x52528; 0x80e1c; 0x7fe48];
[0x52688];
[0x52688; 0x7fb00];
[0x52688; 0x7fb54];
[0x52688; 0x7fde0];
[0x52688; 0x8011c];
[0x52688; 0x8011c; 0x7fe48];
[0x52688; 0x813a0]].
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
Lemma TRACES_read_name_U : forall t, In t TRACES_read_name -> In t Tfib_universe.
Proof. intros t H. apply memZL_In. exact (allb_In (fun t => memZL t Tfib_universe) TRACES_read_name t ltac:(vm_compute; reflexivity) H). Qed.
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
