(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/libreac/fuzz_scene/lib/A/ACej.v at 6ebe35ba632 (the lemma part, which names no address), with its module paths changed; the call contexts and allocation traces are reac-pw/fuzz_role's own, read from fuzz_role.asan (sha256 614cffc0864cc31d9d1ced61322c4efd567b64bc89fe09a227a05b5126e0debb) by pg-reloc/gen_traces.py (sha256 a78026af1ae206cc68df7256ad677ca595768d16ceedd89936dd82bd9ee7c80d): the calls of the allocation wrappers' 4-byte jumps (0x52428 __interceptor_trampoline_malloc, 0x52424 __interceptor_trampoline_free) in main, target_run and LLVMFuzzerTestOneInput, the only functions that call them (10 call sites), each trace closed under prefixes (16 traces). First entry = the pc each interceptor records, the return address of its GetCurrentPc call (malloc 0x526c4, free 0x52564, both checked on the pin: the jal at 0x526c0 / 0x52560 reaches 0x7292c). *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/reac-pw/fuzz_role/lib/A/ACej.v at 9f8c843f0e03 (the lemma part, unchanged, with its module paths changed); the call contexts and allocation traces are reac-pw/fuzz_headamp's own, read from fuzz_headamp.asan (sha256 f3e0669d2819724922df0556b11c2dcd22d1e16fe7e0fe1535ce784b34436c47, symbols of its unstripped twin b5f352154c54) by pg-reloc/gen_traces.py (sha256 a78026af1ae206cc68df7256ad677ca595768d16ceedd89936dd82bd9ee7c80d) with --ipc malloc=0x532fc --ipc free=0x5319c --fp LLVMFuzzerTestOneInput=0x80abc --exclude _ZN9libunwind13DwarfFDECacheINS_17LocalAddressSpaceEE3addEmmmm: 14 call sites in main, target_run and LLVMFuzzerTestOneInput, 24 traces closed under prefixes. *)
From Stdlib Require Import ZArith List Bool Lia.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YG00 YG01.
Import ListNotations.
Local Open Scope Z_scope.
Definition CTX_LLVMFuzzerTestOneInput : list (list Z) :=
[[0x80abc]].
Definition TRACES_LLVMFuzzerTestOneInput : list (list Z) :=
[[0x532fc; 0x80e94];
[0x532fc; 0x80e94; 0x80abc];
[0x532fc; 0x82e64];
[0x532fc; 0x82e64; 0x80abc];
[0x532fc; 0x82e98];
[0x532fc; 0x82e98; 0x80abc];
[0x532fc; 0x83744];
[0x532fc; 0x83744; 0x80abc];
[0x5319c; 0x8379c];
[0x5319c; 0x8379c; 0x80abc];
[0x5319c; 0x837a4];
[0x5319c; 0x837a4; 0x80abc];
[0x5319c; 0x837ac];
[0x5319c; 0x837ac; 0x80abc];
[0x5319c; 0x837b4];
[0x5319c; 0x837b4; 0x80abc]].
Definition CTX_main : list (list Z) :=
[[]].
Definition TRACES_main : list (list Z) :=
[[0x532fc; 0x80774];
[0x532fc; 0x807c8];
[0x5319c; 0x807ec];
[0x5319c; 0x8091c]].
Definition CTX_target_run : list (list Z) :=
[[]].
Definition TRACES_target_run : list (list Z) :=
[[0x532fc; 0x80a54];
[0x5319c; 0x80ae8]].
Definition Tfib_universe : list (list Z) :=
[[0x5319c];
[0x5319c; 0x807ec];
[0x5319c; 0x8091c];
[0x5319c; 0x80ae8];
[0x5319c; 0x8379c];
[0x5319c; 0x8379c; 0x80abc];
[0x5319c; 0x837a4];
[0x5319c; 0x837a4; 0x80abc];
[0x5319c; 0x837ac];
[0x5319c; 0x837ac; 0x80abc];
[0x5319c; 0x837b4];
[0x5319c; 0x837b4; 0x80abc];
[0x532fc];
[0x532fc; 0x80774];
[0x532fc; 0x807c8];
[0x532fc; 0x80a54];
[0x532fc; 0x80e94];
[0x532fc; 0x80e94; 0x80abc];
[0x532fc; 0x82e64];
[0x532fc; 0x82e64; 0x80abc];
[0x532fc; 0x82e98];
[0x532fc; 0x82e98; 0x80abc];
[0x532fc; 0x83744];
[0x532fc; 0x83744; 0x80abc]].
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
