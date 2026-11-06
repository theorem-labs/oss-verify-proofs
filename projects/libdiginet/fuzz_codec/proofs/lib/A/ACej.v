(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: generated for libdiginet/fuzz_codec's ASan build in the form of proofs/cgif/cgif_file_fuzzer/lib/A/ACej.v (origin/ossv/recipes 25e3d17bdb50); module paths changed (cgif lib/X -> lib/Reusable/X). *)
(* ACej: the trace universe of fuzz_codec's start-up certificate, image A.
   Image: libdiginet/fuzz_codec's fuzz_codec.asan (result/bin/fuzz_codec/fuzz_codec.asan of libdiginet's pinned build),
   sha256 7d470194ffdbde8b30a9810840f8e81d620ba1c555d510c475daeff37548a422 (the pin of harness.yaml); symbols from
   the unstripped twin result/unstripped/fuzz_codec/fuzz_codec.asan of the same build, sha256
   b28356da1a6547814e3a3c56e2d9e065e4f5b45715ccb5a236942cda3471fe1d, whose .text is byte-equal to the image's.
   CTX_<f> / TRACES_<f> and Tfib_universe below are machine-generated from that image by port_core 0e4e065eab9f's
   gen_traces.py (sha256 a78026af1ae2; internal record), sha256
   a78026af1ae206cc68df7256ad677ca595768d16ceedd89936dd82bd9ee7c80d, run as
     gen_traces.py bin/fuzz_codec/fuzz_codec.asan unstripped/fuzz_codec/fuzz_codec.asan
       --ipc malloc=0x52f88 --ipc free=0x52e28
       --exclude _ZN9libunwind13DwarfFDECacheINS_17LocalAddressSpaceEE3addEmmmm
   (8 traces, from 6 call sites in 2 functions; stderr empty), and reassembled into this unit by
   fuzz_decode's acej.py (sha256 5db4ca1babf0; internal record), whose control re-emits cgif's
   released lib/A/ACej.v byte for byte from cgif's own data. The ipc are the return addresses of the
   GetCurrentPc calls on the unwinding arm of __interceptor_malloc (0x52f84) and __interceptor_free (0x52e24).
   No --fp: no function on an allocation path sets s0 = sp + imm, so the fast unwinder stops after the call's
   return address; every trace is [ipc; return address] and every CTX_<f> the tool writes is [[]]. As for
   fuzz_decode, the unit states the tool's CTX_<f> / TRACES_<f> pairs; no statement file of this unit owns one of
   these names, so none is filtered out, and the tool emits every trace itself, so no override row is added.
   No tail jump: no function reaches an allocation entry with j / c.j (xcheck_pcs.py lists 6 calls and 0 tail
   jumps), so every trace is [ipc; the return address of a call].
   Each pc below is checked against the image by xcheck_pcs.py (sha256 ff6151d17c42; internal record) (capstone, a
   decoder and frame model independent of gen_traces). *)
From Stdlib Require Import ZArith List Bool Lia.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YG00 YG01.
Import ListNotations.
Local Open Scope Z_scope.
Definition CTX_main : list (list Z) :=
[[]].
Definition TRACES_main : list (list Z) :=
[[0x52f88; 0x80400];
[0x52f88; 0x80454];
[0x52e28; 0x80478];
[0x52e28; 0x805a8]].
Definition CTX_target_run : list (list Z) :=
[[]].
Definition TRACES_target_run : list (list Z) :=
[[0x52f88; 0x806e0];
[0x52e28; 0x80774]].
Definition Tfib_universe : list (list Z) :=
[[0x52e28];
[0x52e28; 0x80478];
[0x52e28; 0x805a8];
[0x52e28; 0x80774];
[0x52f88];
[0x52f88; 0x80400];
[0x52f88; 0x80454];
[0x52f88; 0x806e0]].
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
