(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/YCej.v (the asan-ubsan twin of lib/A/ACej.v; lemma part as in proofs/libreac/fuzz_grant/lib/A/ACej.v on a working branch 707b9264999), with its module paths changed (YG00 / YG01 from the shared lib/Reusable, gate 6o); the call contexts and allocation traces are libreac/fuzz_scene's, read from fuzz_scene.asan-ubsan (sha256 pinned in projects/libreac/fuzz_scene/harness.yaml) by gen_traces.py: the calls of the malloc and free wrappers' 4-byte jumps (0x54d44 __interceptor_trampoline_malloc, 0x54d40 __interceptor_trampoline_free) in main, target_run and LLVMFuzzerTestOneInput, the only functions that call them (12 call sites), each trace closed under prefixes (20 traces). First entry = the pc each interceptor records, the return address of its LONG-branch GetCurrentPc call: malloc 0x54fe0 = ___interceptor_malloc 0x54f18 + 0xc8 (the call at 0x54fdc, reached by `bltu 2, GetMallocContextSize()` at 0x54f78), free 0x54e80 = ___interceptor_free 0x54d48 + 0x138 (call 0x54e7c, branch 0x54e48) (cgif_file: 0x52bcc / 0x52a6c at the same offsets); the long branch is taken because scene's malloc_context_size is 30 (internal path, static on the pinned originals; and a Theorem Labs lane's hsform.py mcs gate, 30 in all 10 collected asan-ubsan hand-off states, a Theorem Labs lane 2026-10-29). LLVMFuzzerTestOneInput keeps its frame pointer, so the unwinder continues to 0x827a0, the return address of target_run's call of it at 0x8279c. Cross-check: (internal path) measures the same 12 program traces (prefix-closed 20); its count 13 (22) adds one runtime trace from __asan_register_globals, which cgif_file's universe (190 traces, interceptor pcs only) does not list either. *)
From Stdlib Require Import ZArith List Bool Lia.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Reusable Require Import YG00 YG01.
Import ListNotations.
Local Open Scope Z_scope.
Definition CTX_LLVMFuzzerTestOneInput : list (list Z) :=
[[0x827a0]].
Definition TRACES_LLVMFuzzerTestOneInput : list (list Z) :=
[[0x54fe0; 0x82c50];
[0x54fe0; 0x82c50; 0x827a0];
[0x54fe0; 0x82e70];
[0x54fe0; 0x82e70; 0x827a0];
[0x54e80; 0x82fa0];
[0x54e80; 0x82fa0; 0x827a0];
[0x54fe0; 0x82fac];
[0x54fe0; 0x82fac; 0x827a0];
[0x54e80; 0x83160];
[0x54e80; 0x83160; 0x827a0];
[0x54e80; 0x83168];
[0x54e80; 0x83168; 0x827a0]].
Definition CTX_main : list (list Z) :=
[[]].
Definition TRACES_main : list (list Z) :=
[[0x54fe0; 0x82458];
[0x54fe0; 0x824ac];
[0x54e80; 0x824d0];
[0x54e80; 0x82600]].
Definition CTX_target_run : list (list Z) :=
[[]].
Definition TRACES_target_run : list (list Z) :=
[[0x54fe0; 0x82738];
[0x54e80; 0x827cc]].
Definition Tfib_universe : list (list Z) :=
[[0x54e80];
[0x54e80; 0x824d0];
[0x54e80; 0x82600];
[0x54e80; 0x827cc];
[0x54e80; 0x82fa0];
[0x54e80; 0x82fa0; 0x827a0];
[0x54e80; 0x83160];
[0x54e80; 0x83160; 0x827a0];
[0x54e80; 0x83168];
[0x54e80; 0x83168; 0x827a0];
[0x54fe0];
[0x54fe0; 0x82458];
[0x54fe0; 0x824ac];
[0x54fe0; 0x82738];
[0x54fe0; 0x82c50];
[0x54fe0; 0x82c50; 0x827a0];
[0x54fe0; 0x82e70];
[0x54fe0; 0x82e70; 0x827a0];
[0x54fe0; 0x82fac];
[0x54fe0; 0x82fac; 0x827a0]].
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
