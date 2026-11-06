(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/YCej.v, with its module paths changed and its addresses moved to omx-clap-core/fuzz_state's ASan+UBSan build (fuzz_state.asan-ubsan). *)
(* Modified by Theorem Labs, 2026-10: INTERIM, regenerated for fuzz_state.asan-ubsan (not relocated), as the A twin A/ACej.v is. The trace universe below is the output of
   a Theorem Labs lane's gen_traces.py over the pinned fuzz_state.asan-ubsan (sha256 5ac5ce0954f8...) and its unstripped twin, with this
   build's own interceptor pcs (malloc_context_size = 30, the second GetCurrentPc call of each interceptor): malloc 0x53384, free 0x53224, realloc 0x53620;
   libunwind's FDE cache (the runtime's own error path) excluded. No --fp list is given, so each trace is [ipc; the call site's return address]; a walk that needs a
   deeper trace fails loudly against it. The donor's cgif traces are gone: fuzz_state has none of cgif's functions. The generic lemmas (listZ_eqb .. Tfib_universe_ok)
   are the donor's text. *)
From Stdlib Require Import ZArith List Bool Lia.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YG00 YG01.
Import ListNotations.
Local Open Scope Z_scope.
Definition CTX_LLVMFuzzerTestOneInput : list (list Z) :=
[[]].
Definition TRACES_LLVMFuzzerTestOneInput : list (list Z) :=
[[0x53384; 0x810c4];
[0x53224; 0x81190]].
Definition CTX_check_as_written : list (list Z) :=
[[]].
Definition TRACES_check_as_written : list (list Z) :=
[[0x53384; 0x816a0];
[0x53384; 0x816bc];
[0x53224; 0x81a7c]].
Definition CTX_check_no_overread : list (list Z) :=
[[]].
Definition TRACES_check_no_overread : list (list Z) :=
[[0x53384; 0x813a0];
[0x53224; 0x814e8];
[0x53224; 0x814f0];
[0x53224; 0x814f8]].
Definition CTX_check_round_trip : list (list Z) :=
[[]].
Definition TRACES_check_round_trip : list (list Z) :=
[[0x53384; 0x81da4];
[0x53384; 0x81db8];
[0x53224; 0x824ac];
[0x53224; 0x824b4]].
Definition CTX_fuzz_malloc : list (list Z) :=
[[]].
Definition TRACES_fuzz_malloc : list (list Z) :=
[[0x53384; 0x82aa0]].
Definition CTX_fuzz_realloc : list (list Z) :=
[[]].
Definition TRACES_fuzz_realloc : list (list Z) :=
[[0x53620; 0x82cf0]].
Definition CTX_main : list (list Z) :=
[[]].
Definition TRACES_main : list (list Z) :=
[[0x53384; 0x80b40];
[0x53384; 0x80b94];
[0x53224; 0x80bb8];
[0x53224; 0x80ce8]].
Definition CTX_past_nul : list (list Z) :=
[[]].
Definition TRACES_past_nul : list (list Z) :=
[[0x53384; 0x828d8]].
Definition CTX_target_run : list (list Z) :=
[[]].
Definition TRACES_target_run : list (list Z) :=
[[0x53384; 0x80e20];
[0x53224; 0x80eb4]].
Definition Tfib_universe : list (list Z) :=
[[0x53224];
[0x53224; 0x80bb8];
[0x53224; 0x80ce8];
[0x53224; 0x80eb4];
[0x53224; 0x81190];
[0x53224; 0x814e8];
[0x53224; 0x814f0];
[0x53224; 0x814f8];
[0x53224; 0x81a7c];
[0x53224; 0x824ac];
[0x53224; 0x824b4];
[0x53384];
[0x53384; 0x80b40];
[0x53384; 0x80b94];
[0x53384; 0x80e20];
[0x53384; 0x810c4];
[0x53384; 0x813a0];
[0x53384; 0x816a0];
[0x53384; 0x816bc];
[0x53384; 0x81da4];
[0x53384; 0x81db8];
[0x53384; 0x828d8];
[0x53384; 0x82aa0];
[0x53620];
[0x53620; 0x82cf0]].
(* 25 traces, from 22 call sites in 9 function(s): LLVMFuzzerTestOneInput, check_as_written, check_no_overread, check_round_trip, fuzz_malloc, fuzz_realloc, main, past_nul, target_run *)
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
Lemma TRACES_LLVMFuzzerTestOneInput_U : forall t, In t TRACES_LLVMFuzzerTestOneInput -> In t Tfib_universe.
Proof. intros t H. apply memZL_In. exact (allb_In (fun t => memZL t Tfib_universe) TRACES_LLVMFuzzerTestOneInput t ltac:(vm_compute; reflexivity) H). Qed.
Lemma TRACES_check_as_written_U : forall t, In t TRACES_check_as_written -> In t Tfib_universe.
Proof. intros t H. apply memZL_In. exact (allb_In (fun t => memZL t Tfib_universe) TRACES_check_as_written t ltac:(vm_compute; reflexivity) H). Qed.
Lemma TRACES_check_no_overread_U : forall t, In t TRACES_check_no_overread -> In t Tfib_universe.
Proof. intros t H. apply memZL_In. exact (allb_In (fun t => memZL t Tfib_universe) TRACES_check_no_overread t ltac:(vm_compute; reflexivity) H). Qed.
Lemma TRACES_check_round_trip_U : forall t, In t TRACES_check_round_trip -> In t Tfib_universe.
Proof. intros t H. apply memZL_In. exact (allb_In (fun t => memZL t Tfib_universe) TRACES_check_round_trip t ltac:(vm_compute; reflexivity) H). Qed.
Lemma TRACES_fuzz_malloc_U : forall t, In t TRACES_fuzz_malloc -> In t Tfib_universe.
Proof. intros t H. apply memZL_In. exact (allb_In (fun t => memZL t Tfib_universe) TRACES_fuzz_malloc t ltac:(vm_compute; reflexivity) H). Qed.
Lemma TRACES_fuzz_realloc_U : forall t, In t TRACES_fuzz_realloc -> In t Tfib_universe.
Proof. intros t H. apply memZL_In. exact (allb_In (fun t => memZL t Tfib_universe) TRACES_fuzz_realloc t ltac:(vm_compute; reflexivity) H). Qed.
Lemma TRACES_main_U : forall t, In t TRACES_main -> In t Tfib_universe.
Proof. intros t H. apply memZL_In. exact (allb_In (fun t => memZL t Tfib_universe) TRACES_main t ltac:(vm_compute; reflexivity) H). Qed.
Lemma TRACES_past_nul_U : forall t, In t TRACES_past_nul -> In t Tfib_universe.
Proof. intros t H. apply memZL_In. exact (allb_In (fun t => memZL t Tfib_universe) TRACES_past_nul t ltac:(vm_compute; reflexivity) H). Qed.
Lemma TRACES_target_run_U : forall t, In t TRACES_target_run -> In t Tfib_universe.
Proof. intros t H. apply memZL_In. exact (allb_In (fun t => memZL t Tfib_universe) TRACES_target_run t ltac:(vm_compute; reflexivity) H). Qed.
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
