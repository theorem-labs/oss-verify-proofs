(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: generated for libdiginet/fuzz_transport's ASan build in the form of proofs/cgif/cgif_file_fuzzer/lib/A/ACej.v (origin/ossv/recipes 25e3d17bdb50); module paths changed (cgif lib/X -> lib/Reusable/X). *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libdiginet/fuzz_transport/lib/A/ACej.v, with its addresses changed; 12 lines of the source are left out. *)
(* YCej: the trace universe of fuzz_transport's start-up certificate, image B, in the form of proofs/cgif/cgif_file_fuzzer/lib/YCej.v
(* Read from: fuzz_transport.asan-ubsan (libdiginet/fuzz_transport asan-ubsan) sha256 41113a03c82fde8282db830ab5f4fbe376e392a38d22670b8cb8c9f02969ece4; unstripped twin sha256 e217cb0a84f1e1810805155304b281a259ef83a85f50efcf0c65b40697bfa4dc *)
   (commit 25e3d17bdb50) with the donor's module paths changed (lib/X -> lib/Reusable/X, fuzz_grant B's layout at
   commit 4f87de75d67).
   Image: the pinned bin/fuzz_transport/fuzz_transport.asan-ubsan of libdiginet,
   sha256 41113a03c82fde8282db830ab5f4fbe376e392a38d22670b8cb8c9f02969ece4 (the pin of harness.yaml); symbols from
   its unstripped twin unstripped/fuzz_transport/fuzz_transport.asan-ubsan, sha256
   e217cb0a84f1e1810805155304b281a259ef83a85f50efcf0c65b40697bfa4dc, whose .text is byte-equal to the image's.
   CTX_<f> / TRACES_<f> are machine-generated from that image by
   gen_traces.py (sha256 a78026af1ae2; internal record), the port_core release's generator,
   run as
     gen_traces.py bin/fuzz_transport/fuzz_transport.asan-ubsan unstripped/fuzz_transport/fuzz_transport.asan-ubsan
       --ipc malloc=0x539dc --ipc free=0x5387c --fp LLVMFuzzerTestOneInput=0x8119c
       --exclude _ZN9libunwind13DwarfFDECacheINS_17LocalAddressSpaceEE3addEmmmm
   (11 traces, from 8 call sites in 3 functions; stderr empty). TRACES_receive_override, the commented block
   before Tfib_universe, declares the four rows gen_traces cannot emit. The unit is reassembled by
   acej.py (sha256 5db4ca1babf0; internal record), fuzz_decode's, whose controls re-emit the
   donor's released lib/YCej.v and lib/A/ACej.v (commit 25e3d17bdb50) byte for byte from their own data, and
   fuzz_decode's lib/B/YCej.v (commit 7eb81ddb186), override block included, from its committed inputs.
   Tfib_universe (15 rows) is closed under non-empty prefixes and equals the prefix closure of the traces of
   pautrlen/compose.py (start-up tool set, sha256 7bf620a82573) on this image.
   The ipc are the return addresses of the GetCurrentPc calls on the unwinding arm of
   __interceptor_malloc (0x539d8) and __interceptor_free (0x53878).
   The --fp function: LLVMFuzzerTestOneInput sets s0 = sp + imm (0x812dc: addi s0, sp, 0x140); 0x8119c is the
   return address of its only call (0x81198: jal in target_run). receive keeps no frame record and calls malloc
   (0x836dc) before it writes s0 (0x836e4), so that call runs on its caller's s0: the walk from
   LLVMFuzzerTestOneInput's frame is in TRACES_receive, the walks from build_and_receive's frame (it keeps s0
   too) are the override block. At every other site s0 holds a value that the calling function wrote, so the
   trace is [ipc; return address]. Image B has no tail jump to an allocation entry. Every CTX_<f> the tool
   writes is [[]]. As for fuzz_decode, the unit states the tool's CTX_<f> / TRACES_<f> pairs; no statement file
   of this unit owns one of these names, so none is filtered out.
   Each pc below is checked against the image by xcheck_pcs.py (sha256 aea1f2f6192d; internal record) (capstone, a
   decoder and frame model independent of gen_traces). *)
From Stdlib Require Import ZArith List Bool Lia.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YG00 YG01.
Import ListNotations.
Local Open Scope Z_scope.
Definition CTX_main : list (list Z) :=
[[]].
Definition TRACES_main : list (list Z) :=
[[0x539dc; 0x80e54];
[0x539dc; 0x80ea8];
[0x5387c; 0x80ecc];
[0x5387c; 0x80ffc]].
Definition CTX_receive : list (list Z) :=
[[]].
Definition TRACES_receive : list (list Z) :=
[[0x539dc; 0x836e0];
[0x539dc; 0x836e0; 0x8119c];
[0x5387c; 0x83810]].
Definition CTX_target_run : list (list Z) :=
[[]].
Definition TRACES_target_run : list (list Z) :=
[[0x539dc; 0x81134];
[0x5387c; 0x811c8]].
(* override: four receive malloc traces that gen_traces.py (sha256 a78026af1ae2; internal record) cannot emit.
   receive (0x836a8) keeps no frame record and calls malloc at 0x836dc before its first write of s0
   (0x836e4: mv s0, a0), so at that call s0 is still its caller's frame pointer and the fast unwinder continues
   from the caller's frame record. Both callers of receive keep one: LLVMFuzzerTestOneInput (0x812dc: addi s0,
   sp, 0x140; its call 0x81ea0 returns to 0x81ea4) and build_and_receive (0x859d4: addi s0, sp, 0xc0; its call
   0x85d08 returns to 0x85d0c). On LLVMFuzzerTestOneInput's frame the walk appends 0x8119c, the return address
   of its only call (0x81198 in target_run); gen_traces emits that row, [0x539dc; 0x836e0; 0x8119c], in
   TRACES_receive from --fp LLVMFuzzerTestOneInput=0x8119c. On build_and_receive's frame the walk appends
   0x82110 or 0x82718, the return addresses of its two calls (0x8210c and 0x82714 in LLVMFuzzerTestOneInput),
   then 0x8119c. gen_traces keeps one --fp return address per function, so it cannot emit these four rows.
   They are the rows of the prefix closure of the traces of pautrlen/compose.py (start-up tool set) on this
   image that gen_traces' output does not hold, written below by closure.py (sha256 09360e41bbe8; internal record) from
   that closure; the recompute of xcheck_pcs.py requires the same four. *)
Definition TRACES_receive_override : list (list Z) :=
[[0x539dc; 0x836e0; 0x82110];
[0x539dc; 0x836e0; 0x82110; 0x8119c];
[0x539dc; 0x836e0; 0x82718];
[0x539dc; 0x836e0; 0x82718; 0x8119c]].
Definition Tfib_universe : list (list Z) :=
[[0x5387c];
[0x5387c; 0x80ecc];
[0x5387c; 0x80ffc];
[0x5387c; 0x811c8];
[0x5387c; 0x83810];
[0x539dc];
[0x539dc; 0x80e54];
[0x539dc; 0x80ea8];
[0x539dc; 0x81134];
[0x539dc; 0x836e0];
[0x539dc; 0x836e0; 0x8119c];
[0x539dc; 0x836e0; 0x82110];
[0x539dc; 0x836e0; 0x82110; 0x8119c];
[0x539dc; 0x836e0; 0x82718];
[0x539dc; 0x836e0; 0x82718; 0x8119c]].
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
