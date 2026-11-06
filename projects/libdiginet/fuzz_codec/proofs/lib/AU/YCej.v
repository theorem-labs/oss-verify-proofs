(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: generated for libdiginet/fuzz_codec's ASan+UBSan build (image B) in the form of proofs/cgif/cgif_file_fuzzer/lib/YCej.v (commit 25e3d17bdb50); module paths changed (cgif lib/X -> lib/Reusable/X, libreac/fuzz_knock's layout at commit 4b6f0df50aa7). *)
(* YCej: the trace universe of fuzz_codec's start-up certificate, image B.
(* Read from: fuzz_codec.asan-ubsan (libdiginet/fuzz_codec asan-ubsan) sha256 73109e32e77beff294d41ae6f16d607479ad1884485781b322645e6f8afa99c3; unstripped twin sha256 43feeaa314a42fe569b4443c710a74561e9077e617f7412cc54fbf4a6557b266 *)
   Image: the pinned bin/fuzz_codec/fuzz_codec.asan-ubsan of libdiginet,
   sha256 73109e32e77beff294d41ae6f16d607479ad1884485781b322645e6f8afa99c3 (the pin of harness.yaml); symbols from
   its unstripped twin unstripped/fuzz_codec/fuzz_codec.asan-ubsan, sha256
   43feeaa314a42fe569b4443c710a74561e9077e617f7412cc54fbf4a6557b266, whose .text is byte-equal to the image's.
   CTX_<f> / TRACES_<f> and Tfib_universe below are machine-generated from that image by
   gen_traces.py (sha256 a78026af1ae2; internal record), sha256
   a78026af1ae206cc68df7256ad677ca595768d16ceedd89936dd82bd9ee7c80d, run as
     gen_traces.py bin/fuzz_codec/fuzz_codec.asan-ubsan unstripped/fuzz_codec/fuzz_codec.asan-ubsan
       --ipc malloc=0x530d8 --ipc free=0x52f78
       --exclude _ZN9libunwind13DwarfFDECacheINS_17LocalAddressSpaceEE3addEmmmm
   (8 traces, from 6 call sites in 2 functions; stderr empty), and reassembled into this unit by
   fuzz_decode's acej.py (sha256 5db4ca1babf0; internal record),
   whose controls re-emit the donor's released
   lib/YCej.v and lib/A/ACej.v (commit 25e3d17bdb50) byte for byte from their own data. The ipc are the return
   addresses of the GetCurrentPc calls on the unwinding arm of __interceptor_malloc (0x530d4) and
   __interceptor_free (0x52f74).
   No --fp: at each allocation site s0 holds the frame of the calling function (main or target_run), which sets
   no s0 = sp + imm, so the fast unwinder stops after the call's return address; every trace is [ipc; return
   address] and every CTX_<f> the tool writes is [[]]. The tool's CTX_<f> / TRACES_<f> pairs are stated as it
   writes them (none is filtered out), and the tool emits every trace itself, so no override row is added.
   No allocation site is a tail jump: the 6 sites are calls that write ra, 4 in main and 2 in target_run; the
   only other calls of the allocation entries are those of libunwind's FDE cache (excluded above), and
   LLVMFuzzerTestOneInput makes none.
   Each pc below is checked against the image by xcheck_pcs.py (sha256 ff6151d17c42; capstone, a decoder and
   frame model independent of gen_traces). *)
From Stdlib Require Import ZArith List Bool Lia.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YG00 YG01.
Import ListNotations.
Local Open Scope Z_scope.
Definition CTX_main : list (list Z) :=
[[]].
Definition TRACES_main : list (list Z) :=
[[0x530d8; 0x80550];
[0x530d8; 0x805a4];
[0x52f78; 0x805c8];
[0x52f78; 0x806f8]].
Definition CTX_target_run : list (list Z) :=
[[]].
Definition TRACES_target_run : list (list Z) :=
[[0x530d8; 0x80830];
[0x52f78; 0x808c4]].
Definition Tfib_universe : list (list Z) :=
[[0x52f78];
[0x52f78; 0x805c8];
[0x52f78; 0x806f8];
[0x52f78; 0x808c4];
[0x530d8];
[0x530d8; 0x80550];
[0x530d8; 0x805a4];
[0x530d8; 0x80830]].
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
