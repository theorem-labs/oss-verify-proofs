(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: generated for reac-repacer/fuzz_wire's ASan build (image A) in the form of proofs/cgif/cgif_file_fuzzer/lib/A/ACej.v (commit 25e3d17bdb50); module paths changed (cgif lib/X -> lib/Reusable/X). *)
(* ACej: the trace universe of fuzz_wire's start-up certificate, image A.
   Image: reac-repacer/fuzz_wire's fuzz_wire.asan (result/bin/fuzz_wire/fuzz_wire.asan of reac-repacer's pinned build),
   sha256 2f8f8697cd4f (the pin of harness.yaml); symbols from
   the unstripped twin result/unstripped/fuzz_wire/fuzz_wire.asan of the same build, sha256
   d2f662a22962, whose .text is byte-equal to the image's.
   CTX_<f> / TRACES_<f> and Tfib_universe below are machine-generated from that image by port_core 0e4e065eab9f's
   gen_traces.py (tools/pg-reloc/0e4e065eab9f/gen_traces.py at commit 7f0e4b05267), sha256
   a78026af1ae206cc68df7256ad677ca595768d16ceedd89936dd82bd9ee7c80d, run as
     gen_traces.py bin/fuzz_wire/fuzz_wire.asan unstripped/fuzz_wire/fuzz_wire.asan
       --ipc malloc=0x52594 --ipc free=0x52434
       --exclude _ZN9libunwind13DwarfFDECacheINS_17LocalAddressSpaceEE3addEmmmm
   (14 traces, from 12 call sites in 4 functions; stderr empty), and reassembled into this unit by acej.py
   (sha256 5db4ca1babf0; acej.py is not in the published tree),
   whose control re-emits cgif's released lib/A/ACej.v byte for byte from cgif's own data. The ipc are the return
   addresses of the GetCurrentPc calls on the unwinding arm of __interceptor_malloc (0x52590) and
   __interceptor_free (0x52430).
   No --fp: the functions that set s0 = sp + imm among the allocating functions and their direct callees
   (__asan_memcpy, __asan_report_load1, check_meter, check_read) make no allocation call, so the fast unwinder
   stops after the call's return address; every trace is [ipc; return address] and every CTX_<f> the tool writes
   is [[]]. As for fuzz_decode, the unit states the tool's CTX_<f> / TRACES_<f> pairs; no statement file of this
   unit owns one of these names, so none is filtered out, and the tool emits every trace itself, so no override
   row is added. No tail call: every call of an allocation entry in the image's .text is a jal that writes ra,
   so no trace is attributed through a tail jump.
   Each pc below is checked against the image by xcheck_pcs.py
   (sha256 ff6151d17c42; xcheck_pcs.py is not in the published tree), with capstone, a decoder and frame model independent of
   gen_traces. *)
From Stdlib Require Import ZArith List Bool Lia.
From OSSVerify.Proofs.reac_repacer.fuzz_wire.lib.Reusable Require Import YG00 YG01.
Import ListNotations.
Local Open Scope Z_scope.
Definition CTX_LLVMFuzzerTestOneInput : list (list Z) :=
[[]].
Definition TRACES_LLVMFuzzerTestOneInput : list (list Z) :=
[[0x52594; 0x7fed4];
[0x52594; 0x7ff5c];
[0x52434; 0x7ffa4];
[0x52434; 0x7ffac]].
Definition CTX_check_copy : list (list Z) :=
[[]].
Definition TRACES_check_copy : list (list Z) :=
[[0x52594; 0x80c88];
[0x52434; 0x80dd0]].
Definition CTX_main : list (list Z) :=
[[]].
Definition TRACES_main : list (list Z) :=
[[0x52594; 0x7fa0c];
[0x52594; 0x7fa60];
[0x52434; 0x7fa84];
[0x52434; 0x7fbb4]].
Definition CTX_target_run : list (list Z) :=
[[]].
Definition TRACES_target_run : list (list Z) :=
[[0x52594; 0x7fcec];
[0x52434; 0x7fd80]].
Definition Tfib_universe : list (list Z) :=
[[0x52434];
[0x52434; 0x7fa84];
[0x52434; 0x7fbb4];
[0x52434; 0x7fd80];
[0x52434; 0x7ffa4];
[0x52434; 0x7ffac];
[0x52434; 0x80dd0];
[0x52594];
[0x52594; 0x7fa0c];
[0x52594; 0x7fa60];
[0x52594; 0x7fcec];
[0x52594; 0x7fed4];
[0x52594; 0x7ff5c];
[0x52594; 0x80c88]].
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
Lemma TRACES_check_copy_U : forall t, In t TRACES_check_copy -> In t Tfib_universe.
Proof. intros t H. apply memZL_In. exact (allb_In (fun t => memZL t Tfib_universe) TRACES_check_copy t ltac:(vm_compute; reflexivity) H). Qed.
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
