(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: generated for libdiginet/fuzz_transport's ASan build in the form of proofs/cgif/cgif_file_fuzzer/lib/A/ACej.v (origin/ossv/recipes 25e3d17bdb50); module paths changed (cgif lib/X -> lib/Reusable/X). *)
(* ACej: the trace universe of fuzz_transport's start-up certificate, image A.
   Image: libdiginet's fuzz_transport.asan (result/bin/fuzz_transport/fuzz_transport.asan of libdiginet's pinned
   build), sha256 e89be137db17b720e0310addc2dcc601998945478a9102e6a9850b0566106350 (the pin of harness.yaml);
   symbols from the unstripped twin unstripped/fuzz_transport/fuzz_transport.asan of the same build, sha256
   86efc3a80314981197619c115e313dbde50e8b86a6c5fefad4e5cc420250c792, whose .text is byte-equal to the image's.
   CTX_<f> / TRACES_<f> and Tfib_universe below are machine-generated from that image by port_core
   0e4e065eab9f's gen_traces.py (internal record, sha256 a78026af1ae2), run as
     gen_traces.py bin/fuzz_transport/fuzz_transport.asan unstripped/fuzz_transport/fuzz_transport.asan
       --ipc malloc=0x539a0 --ipc free=0x53840
       --fp LLVMFuzzerTestOneInput=0x81160
       --exclude _ZN9libunwind13DwarfFDECacheINS_17LocalAddressSpaceEE3addEmmmm
   (13 traces, from 8 call sites in 3 functions; stderr empty), and reassembled into this unit by
   acej.py (sha256 5db4ca1babf0; internal record), fuzz_decode's, whose control re-emits cgif's
   released lib/A/ACej.v byte for byte from cgif's own data. The ipc are the return addresses of the
   GetCurrentPc calls on the unwinding arm of __interceptor_malloc (0x5399c) and __interceptor_free (0x5383c).
   The frame pointers: LLVMFuzzerTestOneInput sets s0 = sp + imm (0x812a0: addi s0, sp, 0x140), and its only
   call (0x8115c: jal in target_run) returns to 0x81160, so the fast unwinder walks from its frame on to that
   address. build_and_receive sets s0 = sp + imm too (0x8581c: addi s0, sp, 0xc0) and has two callers, both in
   LLVMFuzzerTestOneInput (0x81d00, return address 0x81d04; 0x8237c, return address 0x82380); gen_traces keeps
   one --fp return address per function, so the 8 walks through build_and_receive's frame are the definition
   TRACES_receive_override below, from the unit's rows file
   libdiginet__fuzz_transport.rows (sha256 3824dd4d0ddb; internal record) through rows.py, in the form
   fuzz_decode's own unit uses for the rows its gen_traces could not emit. receive's malloc call at 0x83814
   comes before receive first writes s0 (0x8381c: mv s0, a0), so s0 there is still its caller's and the walk
   goes on from the frame of each function that calls receive (LLVMFuzzerTestOneInput and build_and_receive).
   Every CTX_<f> the tool writes is [[]]: no function with an allocation site is an --fp function. As for
   fuzz_decode, the unit states the tool's CTX_<f> / TRACES_<f> pairs; no statement file of this unit owns one
   of these names, so none is filtered out.
   The tail call: receive's last free is 0x83a70: j -> __interceptor_trampoline_free, after its epilogue, so it
   pushes no return address: those traces start [0x53840; 0x81b70] and [0x53840; 0x85a8c], the return addresses
   of receive's two calls (0x81b6c: jal in LLVMFuzzerTestOneInput; 0x85a88: jal in build_and_receive).
   libunwind's DwarfFDECache::add calls the same entries and this list leaves its traces out, as fuzz_grant's
   released unit does: that cache is reached only from a report of an error, which the proof shows is not
   reached.
   Each pc below is checked against the image by xcheck_pcs.py (sha256 ff6151d17c42; internal record)
   (capstone, a decoder and frame model independent of gen_traces). *)
From Stdlib Require Import ZArith List Bool Lia.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YG00 YG01.
Import ListNotations.
Local Open Scope Z_scope.
Definition CTX_main : list (list Z) :=
[[]].
Definition TRACES_main : list (list Z) :=
[[0x539a0; 0x80e18];
[0x539a0; 0x80e6c];
[0x53840; 0x80e90];
[0x53840; 0x80fc0]].
Definition CTX_receive : list (list Z) :=
[[]].
Definition TRACES_receive : list (list Z) :=
[[0x53840; 0x81b70];
[0x53840; 0x81b70; 0x81160];
[0x539a0; 0x83818];
[0x539a0; 0x83818; 0x81160];
[0x53840; 0x85a8c]].
Definition CTX_target_run : list (list Z) :=
[[]].
Definition TRACES_target_run : list (list Z) :=
[[0x539a0; 0x810f8];
[0x53840; 0x8118c]].
(* Extra trace rows: frame walks that gen_traces 0e4e065eab9f cannot emit, because it takes one --fp
   per function and a function that keeps its frame pointer in s0 has more than one caller here.
   Read from targets/libdiginet__fuzz_transport.rows; xcheck_pcs.py checks each row against the image as it checks a
   generated row (it recomputes the walk through every call of a frame keeper). *)
Definition TRACES_receive_override : list (list Z) :=
[[0x539a0; 0x83818; 0x81d04];
[0x539a0; 0x83818; 0x81d04; 0x81160];
[0x53840; 0x85a8c; 0x81d04];
[0x53840; 0x85a8c; 0x81d04; 0x81160];
[0x539a0; 0x83818; 0x82380];
[0x539a0; 0x83818; 0x82380; 0x81160];
[0x53840; 0x85a8c; 0x82380];
[0x53840; 0x85a8c; 0x82380; 0x81160]].
Definition Tfib_universe : list (list Z) :=
[[0x53840];
[0x53840; 0x80e90];
[0x53840; 0x80fc0];
[0x53840; 0x8118c];
[0x53840; 0x81b70];
[0x53840; 0x81b70; 0x81160];
[0x53840; 0x85a8c];
[0x53840; 0x85a8c; 0x81d04];
[0x53840; 0x85a8c; 0x81d04; 0x81160];
[0x53840; 0x85a8c; 0x82380];
[0x53840; 0x85a8c; 0x82380; 0x81160];
[0x539a0];
[0x539a0; 0x80e18];
[0x539a0; 0x80e6c];
[0x539a0; 0x810f8];
[0x539a0; 0x83818];
[0x539a0; 0x83818; 0x81160];
[0x539a0; 0x83818; 0x81d04];
[0x539a0; 0x83818; 0x81d04; 0x81160];
[0x539a0; 0x83818; 0x82380];
[0x539a0; 0x83818; 0x82380; 0x81160]].
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
Lemma TRACES_receive_U : forall t, In t TRACES_receive -> In t Tfib_universe.
Proof. intros t H. apply memZL_In. exact (allb_In (fun t => memZL t Tfib_universe) TRACES_receive t ltac:(vm_compute; reflexivity) H). Qed.
Lemma TRACES_target_run_U : forall t, In t TRACES_target_run -> In t Tfib_universe.
Proof. intros t H. apply memZL_In. exact (allb_In (fun t => memZL t Tfib_universe) TRACES_target_run t ltac:(vm_compute; reflexivity) H). Qed.
Lemma TRACES_receive_override_U : forall t, In t TRACES_receive_override -> In t Tfib_universe.
Proof. intros t H. apply memZL_In. exact (allb_In (fun t => memZL t Tfib_universe) TRACES_receive_override t ltac:(vm_compute; reflexivity) H). Qed.
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
