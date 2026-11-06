(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: INTERIM, regenerated for fuzz_state.asan (not relocated). The trace universe
   below is the output of a Theorem Labs lane's gen_traces.py over the pinned
   fuzz_state.asan (sha256 64b53ff86172...) and its unstripped twin, with the interceptor pcs a Theorem Labs lane measured on
   the ORIGINAL images (malloc_context_size = 30, second GetCurrentPc call): malloc 0x53314, free 0x531b4,
   realloc 0x535b0; libunwind's FDE cache (the runtime's own error path) excluded. No --fp list is given, so each
   trace is [ipc; the call site's return address]; a walk that needs a deeper trace fails loudly against it.
   The donor's cgif traces are gone: fuzz_state has none of cgif's functions. This file is REPLACED by a Theorem Labs lane's
   shared st_nev trace allowance (C5, a working branch af454d3e557) when its A/ consumer hunks land; then ACej
   holds only the driver's traces. The generic lemmas (listZ_eqb .. Tfib_universe_ok) are the donor's text. *)
(* Modified by Theorem Labs, 2026-10: with a Theorem Labs lane's C5 trace allowance (traces outside the universe charged to st_nev) the universe is the driver's traces, AF0m.v DRV_TRACES (main and target_run, and the frame-0 fallbacks [0x53314] and [0x531b4] that api_env asks for), plus fuzz_realloc's two realloc traces [0x535b0] and [0x535b0; 0x82b34], which stay because FS_AREALLOC_A (FSH_ReallocModel.v) still takes In (call_trace ..) U until realloc's contract takes the C5 form; the per-function CTX_* / TRACES_* lists and their _U lemmas are gone. *)
From Stdlib Require Import ZArith List Bool Lia.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YG00 YG01.
Import ListNotations.
Local Open Scope Z_scope.
(* The trace universe. Source: gen_traces.py (internal path) over the pinned fuzz_state.asan
   (sha256 64b53ff86172...) and its unstripped twin, --ipc malloc=0x53314 free=0x531b4 realloc=0x535b0 (the return
   of the interceptors' second GetCurrentPc call; malloc_context_size = 30). Each trace is [ipc; the return address
   of the call], each call a `jal` read from the image: main (0x80a7c) calls __interceptor_trampoline_malloc 0x53074
   at 0x80acc / 0x80b20 and __interceptor_trampoline_free 0x53070 at 0x80b44 / 0x80c74; target_run (0x80d4c) calls
   them at 0x80dac / 0x80e40; fuzz_realloc (0x829e8) calls __interceptor_trampoline_realloc 0x53078 at 0x82b30.
   [0x53314], [0x531b4] and [0x535b0] are the one-frame traces call_trace gives when frame 0 is not usable. *)
Definition Tfib_universe : list (list Z) :=
[[0x53314; 0x80ad0]; [0x53314; 0x80b24]; [0x53314; 0x80db0]; [0x53314];
[0x531b4; 0x80b48]; [0x531b4; 0x80c78]; [0x531b4; 0x80e44]; [0x531b4];
[0x535b0]; [0x535b0; 0x82b34]].
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
