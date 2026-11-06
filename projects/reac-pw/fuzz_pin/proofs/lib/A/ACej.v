(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/A/ACej.v (lemma part as in proofs/libreac/fuzz_grant/lib/A/ACej.v on cold/pg-core 707b9264999), with its module paths changed; the call contexts and allocation traces are libreac/fuzz_scene's, read from fuzz_scene.asan (sha256 pinned in projects/libreac/fuzz_scene/harness.yaml) by pg-core/reloc/gen_traces.py: the calls of the malloc and free wrappers' 4-byte jumps (0x54d18 __interceptor_trampoline_malloc, 0x54d14 __interceptor_trampoline_free) in main, target_run and LLVMFuzzerTestOneInput, the only functions that call them (12 call sites), each trace closed under prefixes (20 traces). First entry = the pc each interceptor records, the return address of its LONG-branch GetCurrentPc call: malloc 0x54fb4 = ___interceptor_malloc 0x54eec + 0xc8 (the call at 0x54fb0, reached by `bltu 2, GetMallocContextSize()` at 0x54f4c), free 0x54e54 = ___interceptor_free 0x54d1c + 0x138 (call 0x54e50, branch 0x54e1c) (cgif_file: 0x52bcc / 0x52a6c at the same offsets); the long branch is taken because scene's malloc_context_size is 30 (cold/rewalk/port-map/MCS-CHECK.md, h-rw-man-7, static on the pinned originals; and port-reply's hsform.py mcs gate, 30 in all 10 collected hand-off states, h-rw-pre-6 2026-10-29 00:00Z). LLVMFuzzerTestOneInput keeps its frame pointer, so the unwinder continues to 0x82774, the return address of target_run's call of it at 0x82770. Cross-check: cold/rewalk/PauTrlen.md measures the same 12 program traces (prefix-closed 20); its count 13 (22) adds one runtime trace from __asan_register_globals, which cgif_file's universe (190 traces, interceptor pcs only) does not list either. *)
(* Modified by Theorem Labs, 2026-10: proofs/libreac/fuzz_scene/lib/A/ACej.v at 6ebe35ba632; module paths changed to reac-pw/fuzz_pin; the call contexts, allocation traces and Tfib_universe are fuzz_pin.asan's (sha256 3e4859aed23f, names from its unstripped twin 435309a6b12c), read by port_core's gen_traces.py a78026af1ae2 (--ipc malloc=0x52df0 --ipc free=0x52c90 --fp LLVMFuzzerTestOneInput=0x805b0 --exclude _ZN9libunwind13DwarfFDECacheINS_17LocalAddressSpaceEE3addEmmmm): 8 call sites in main, target_run and LLVMFuzzerTestOneInput, 12 traces closed under prefixes; the lemma part is scene's. *)
From Stdlib Require Import ZArith List Bool Lia.
From OSSVerify.Proofs.reac_pw.fuzz_pin.lib.Reusable Require Import YG00 YG01.
Import ListNotations.
Local Open Scope Z_scope.
Definition CTX_LLVMFuzzerTestOneInput : list (list Z) :=
[[0x805b0]].
Definition TRACES_LLVMFuzzerTestOneInput : list (list Z) :=
[[0x52df0; 0x80828];
[0x52df0; 0x80828; 0x805b0];
[0x52c90; 0x80934];
[0x52c90; 0x80934; 0x805b0]].
Definition CTX_main : list (list Z) :=
[[]].
Definition TRACES_main : list (list Z) :=
[[0x52df0; 0x80268];
[0x52df0; 0x802bc];
[0x52c90; 0x802e0];
[0x52c90; 0x80410]].
Definition CTX_target_run : list (list Z) :=
[[]].
Definition TRACES_target_run : list (list Z) :=
[[0x52df0; 0x80548];
[0x52c90; 0x805dc]].
Definition Tfib_universe : list (list Z) :=
[[0x52c90];
[0x52c90; 0x802e0];
[0x52c90; 0x80410];
[0x52c90; 0x805dc];
[0x52c90; 0x80934];
[0x52c90; 0x80934; 0x805b0];
[0x52df0];
[0x52df0; 0x80268];
[0x52df0; 0x802bc];
[0x52df0; 0x80548];
[0x52df0; 0x80828];
[0x52df0; 0x80828; 0x805b0]].
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
