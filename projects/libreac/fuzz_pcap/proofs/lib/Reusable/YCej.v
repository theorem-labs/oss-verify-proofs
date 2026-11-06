From OSSVerify.Proofs.libreac.fuzz_pcap.lib Require Import SymAddr.
(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/YCej.v, with its module paths changed; the call contexts and allocation traces are libreac/fuzz_pcap's (v1.9.0), read from fuzz_pcap.asan-ubsan: the calls of the malloc and free wrappers (0x52c28, 0x52c24) in main, target_run, LLVMFuzzerTestOneInput and musl's fmemopen, __fdopen and fclose. The only other function that calls them is libunwind's DwarfFDECache::add (malloc at +0x7c, 0x827cc; free at +0xa0, 0x827f0); its two calls are excluded, as the donor excludes its own copies: DwarfFDECache::add is reached only through BufferedStackTrace::UnwindSlow -> _Unwind_Backtrace (the slow unwinder), which malloc and free never take while fast_unwind_on_malloc is set. The two-frame chain of the fmemopen call runs through pcap_source_open's frame record. The universe also holds the five traces of the two calls the harness never makes (__fdopen's malloc and fmemopen's second malloc). *)
From Stdlib Require Import ZArith List Bool Lia.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YG00 YG01.
Import ListNotations.
Local Open Scope Z_scope.
Definition CTX_main : list (list Z) :=
[[(symaddr (Symbols.AsanUbsan.s_libc_start_main_stage2 + 0x44)%Z)]].
Definition TRACES_main : list (list Z) :=
[[(symaddr (Symbols.AsanUbsan.s___interceptor_free + 0x138)%Z); (symaddr (Symbols.AsanUbsan.s_main + 0xcc)%Z)];
[(symaddr (Symbols.AsanUbsan.s___interceptor_free + 0x138)%Z); (symaddr (Symbols.AsanUbsan.s_main + 0x1fc)%Z)];
[(symaddr (Symbols.AsanUbsan.s___interceptor_malloc + 0xc8)%Z); (symaddr (Symbols.AsanUbsan.s_main + 0x54)%Z)];
[(symaddr (Symbols.AsanUbsan.s___interceptor_malloc + 0xc8)%Z); (symaddr (Symbols.AsanUbsan.s_main + 0xa8)%Z)]].
Definition CTX_target_alloc_init : list (list Z) :=
[[(symaddr (Symbols.AsanUbsan.s_main + 0x160)%Z)]].
Definition CTX_target_alloc_count : list (list Z) :=
[[(symaddr (Symbols.AsanUbsan.s_main + 0x184)%Z)]].
Definition CTX_target_run : list (list Z) :=
[[(symaddr (Symbols.AsanUbsan.s_main + 0x174)%Z)]].
Definition TRACES_target_run : list (list Z) :=
[[(symaddr (Symbols.AsanUbsan.s___interceptor_free + 0x138)%Z); (symaddr (Symbols.AsanUbsan.s_target_run + 0xf8)%Z)];
[(symaddr (Symbols.AsanUbsan.s___interceptor_malloc + 0xc8)%Z); (symaddr (Symbols.AsanUbsan.s_target_run + 0x64)%Z)]].
Definition CTX_emit_printf : list (list Z) :=
[[(symaddr (Symbols.AsanUbsan.s_target_run + 0xdc)%Z)]].
Definition CTX_LLVMFuzzerTestOneInput : list (list Z) :=
[[(symaddr (Symbols.AsanUbsan.s_target_run + 0xcc)%Z)]].
Definition TRACES_LLVMFuzzerTestOneInput : list (list Z) :=
[[(symaddr (Symbols.AsanUbsan.s___interceptor_free + 0x138)%Z); (symaddr (Symbols.AsanUbsan.s_LLVMFuzzerTestOneInput + 0x27c)%Z)];
[(symaddr (Symbols.AsanUbsan.s___interceptor_free + 0x138)%Z); (symaddr (Symbols.AsanUbsan.s_LLVMFuzzerTestOneInput + 0x27c)%Z); (symaddr (Symbols.AsanUbsan.s_target_run + 0xcc)%Z)];
[(symaddr (Symbols.AsanUbsan.s___interceptor_free + 0x138)%Z); (symaddr (Symbols.AsanUbsan.s_LLVMFuzzerTestOneInput + 0x680)%Z)];
[(symaddr (Symbols.AsanUbsan.s___interceptor_free + 0x138)%Z); (symaddr (Symbols.AsanUbsan.s_LLVMFuzzerTestOneInput + 0x680)%Z); (symaddr (Symbols.AsanUbsan.s_target_run + 0xcc)%Z)];
[(symaddr (Symbols.AsanUbsan.s___interceptor_free + 0x138)%Z); (symaddr (Symbols.AsanUbsan.s_LLVMFuzzerTestOneInput + 0x688)%Z)];
[(symaddr (Symbols.AsanUbsan.s___interceptor_free + 0x138)%Z); (symaddr (Symbols.AsanUbsan.s_LLVMFuzzerTestOneInput + 0x688)%Z); (symaddr (Symbols.AsanUbsan.s_target_run + 0xcc)%Z)];
[(symaddr (Symbols.AsanUbsan.s___interceptor_malloc + 0xc8)%Z); (symaddr (Symbols.AsanUbsan.s_LLVMFuzzerTestOneInput + 0x1a0)%Z)];
[(symaddr (Symbols.AsanUbsan.s___interceptor_malloc + 0xc8)%Z); (symaddr (Symbols.AsanUbsan.s_LLVMFuzzerTestOneInput + 0x1a0)%Z); (symaddr (Symbols.AsanUbsan.s_target_run + 0xcc)%Z)];
[(symaddr (Symbols.AsanUbsan.s___interceptor_malloc + 0xc8)%Z); (symaddr (Symbols.AsanUbsan.s_LLVMFuzzerTestOneInput + 0x2b4)%Z)];
[(symaddr (Symbols.AsanUbsan.s___interceptor_malloc + 0xc8)%Z); (symaddr (Symbols.AsanUbsan.s_LLVMFuzzerTestOneInput + 0x2b4)%Z); (symaddr (Symbols.AsanUbsan.s_target_run + 0xcc)%Z)]].
Definition CTX_pcap_source_open : list (list Z) :=
[[(symaddr (Symbols.AsanUbsan.s_LLVMFuzzerTestOneInput + 0x1f8)%Z)];
[(symaddr (Symbols.AsanUbsan.s_LLVMFuzzerTestOneInput + 0x1f8)%Z); (symaddr (Symbols.AsanUbsan.s_target_run + 0xcc)%Z)];
[(symaddr (Symbols.AsanUbsan.s_LLVMFuzzerTestOneInput + 0x638)%Z)];
[(symaddr (Symbols.AsanUbsan.s_LLVMFuzzerTestOneInput + 0x638)%Z); (symaddr (Symbols.AsanUbsan.s_target_run + 0xcc)%Z)]].
Definition CTX_pcap_source_next : list (list Z) :=
[[(symaddr (Symbols.AsanUbsan.s_LLVMFuzzerTestOneInput + 0x2ec)%Z)];
[(symaddr (Symbols.AsanUbsan.s_LLVMFuzzerTestOneInput + 0x2ec)%Z); (symaddr (Symbols.AsanUbsan.s_target_run + 0xcc)%Z)];
[(symaddr (Symbols.AsanUbsan.s_LLVMFuzzerTestOneInput + 0x5a4)%Z)];
[(symaddr (Symbols.AsanUbsan.s_LLVMFuzzerTestOneInput + 0x5a4)%Z); (symaddr (Symbols.AsanUbsan.s_target_run + 0xcc)%Z)];
[(symaddr (Symbols.AsanUbsan.s_LLVMFuzzerTestOneInput + 0x650)%Z)];
[(symaddr (Symbols.AsanUbsan.s_LLVMFuzzerTestOneInput + 0x650)%Z); (symaddr (Symbols.AsanUbsan.s_target_run + 0xcc)%Z)];
[(symaddr (Symbols.AsanUbsan.s_LLVMFuzzerTestOneInput + 0x670)%Z)];
[(symaddr (Symbols.AsanUbsan.s_LLVMFuzzerTestOneInput + 0x670)%Z); (symaddr (Symbols.AsanUbsan.s_target_run + 0xcc)%Z)]].
Definition CTX_pcap_source_close : list (list Z) :=
[[(symaddr (Symbols.AsanUbsan.s_LLVMFuzzerTestOneInput + 0x620)%Z)];
[(symaddr (Symbols.AsanUbsan.s_LLVMFuzzerTestOneInput + 0x620)%Z); (symaddr (Symbols.AsanUbsan.s_target_run + 0xcc)%Z)];
[(symaddr (Symbols.AsanUbsan.s_LLVMFuzzerTestOneInput + 0x65c)%Z)];
[(symaddr (Symbols.AsanUbsan.s_LLVMFuzzerTestOneInput + 0x65c)%Z); (symaddr (Symbols.AsanUbsan.s_target_run + 0xcc)%Z)]].
(* musl fmemopen is reached pcap_source_open -> libreac_fuzz_fopen (tail j) -> __wrap_fmemopen (j) ->
   ___interceptor_fmemopen (tail jr through its REAL slot) -> fmemopen, each restoring s0 before its jump; so s0 at
   fmemopen's two malloc calls (+0x98 return 0x8e7d8, +0xa8 return 0x8e7e8) is pcap_source_open's frame pointer, and
   the context of those calls is CTX_pcap_source_open. The +0xa8 call (buffer NULL) is never made by the harness. *)
Definition TRACES_fmemopen : list (list Z) :=
[[(symaddr (Symbols.AsanUbsan.s___interceptor_malloc + 0xc8)%Z); (symaddr (Symbols.AsanUbsan.s_fmemopen + 0x9c)%Z); (symaddr (Symbols.AsanUbsan.s_LLVMFuzzerTestOneInput + 0x1f8)%Z)];
[(symaddr (Symbols.AsanUbsan.s___interceptor_malloc + 0xc8)%Z); (symaddr (Symbols.AsanUbsan.s_fmemopen + 0x9c)%Z); (symaddr (Symbols.AsanUbsan.s_LLVMFuzzerTestOneInput + 0x1f8)%Z); (symaddr (Symbols.AsanUbsan.s_target_run + 0xcc)%Z)];
[(symaddr (Symbols.AsanUbsan.s___interceptor_malloc + 0xc8)%Z); (symaddr (Symbols.AsanUbsan.s_fmemopen + 0x9c)%Z); (symaddr (Symbols.AsanUbsan.s_LLVMFuzzerTestOneInput + 0x638)%Z)];
[(symaddr (Symbols.AsanUbsan.s___interceptor_malloc + 0xc8)%Z); (symaddr (Symbols.AsanUbsan.s_fmemopen + 0x9c)%Z); (symaddr (Symbols.AsanUbsan.s_LLVMFuzzerTestOneInput + 0x638)%Z); (symaddr (Symbols.AsanUbsan.s_target_run + 0xcc)%Z)];
[(symaddr (Symbols.AsanUbsan.s___interceptor_malloc + 0xc8)%Z); (symaddr (Symbols.AsanUbsan.s_fmemopen + 0xac)%Z); (symaddr (Symbols.AsanUbsan.s_LLVMFuzzerTestOneInput + 0x1f8)%Z)];
[(symaddr (Symbols.AsanUbsan.s___interceptor_malloc + 0xc8)%Z); (symaddr (Symbols.AsanUbsan.s_fmemopen + 0xac)%Z); (symaddr (Symbols.AsanUbsan.s_LLVMFuzzerTestOneInput + 0x1f8)%Z); (symaddr (Symbols.AsanUbsan.s_target_run + 0xcc)%Z)];
[(symaddr (Symbols.AsanUbsan.s___interceptor_malloc + 0xc8)%Z); (symaddr (Symbols.AsanUbsan.s_fmemopen + 0xac)%Z); (symaddr (Symbols.AsanUbsan.s_LLVMFuzzerTestOneInput + 0x638)%Z)];
[(symaddr (Symbols.AsanUbsan.s___interceptor_malloc + 0xc8)%Z); (symaddr (Symbols.AsanUbsan.s_fmemopen + 0xac)%Z); (symaddr (Symbols.AsanUbsan.s_LLVMFuzzerTestOneInput + 0x638)%Z); (symaddr (Symbols.AsanUbsan.s_target_run + 0xcc)%Z)]].
(* musl fclose: s0 is the FILE*, a heap address, so the chain ends at the call (frees at +0xa0 and +0xa8). *)
Definition TRACES_fclose : list (list Z) :=
[[(symaddr (Symbols.AsanUbsan.s___interceptor_free + 0x138)%Z); (symaddr (Symbols.AsanUbsan.s_fclose + 0xa4)%Z)];
[(symaddr (Symbols.AsanUbsan.s___interceptor_free + 0x138)%Z); (symaddr (Symbols.AsanUbsan.s_fclose + 0xac)%Z)]].
(* musl __fdopen (from fopen): s0 is fopen's mode string, a read-only address, so the chain ends at the call.
   The harness never calls fopen (both pcap_source_open calls pass the fuzz-input name). *)
Definition TRACES_fdopen : list (list Z) :=
[[(symaddr (Symbols.AsanUbsan.s___interceptor_malloc + 0xc8)%Z); (symaddr (Symbols.AsanUbsan.s_fdopen + 0x4c)%Z)]].
Definition Tfib_universe : list (list Z) :=
[[(symaddr (Symbols.AsanUbsan.s___interceptor_free + 0x138)%Z)];
[(symaddr (Symbols.AsanUbsan.s___interceptor_free + 0x138)%Z); (symaddr (Symbols.AsanUbsan.s_main + 0xcc)%Z)];
[(symaddr (Symbols.AsanUbsan.s___interceptor_free + 0x138)%Z); (symaddr (Symbols.AsanUbsan.s_main + 0x1fc)%Z)];
[(symaddr (Symbols.AsanUbsan.s___interceptor_free + 0x138)%Z); (symaddr (Symbols.AsanUbsan.s_target_run + 0xf8)%Z)];
[(symaddr (Symbols.AsanUbsan.s___interceptor_free + 0x138)%Z); (symaddr (Symbols.AsanUbsan.s_LLVMFuzzerTestOneInput + 0x27c)%Z)];
[(symaddr (Symbols.AsanUbsan.s___interceptor_free + 0x138)%Z); (symaddr (Symbols.AsanUbsan.s_LLVMFuzzerTestOneInput + 0x27c)%Z); (symaddr (Symbols.AsanUbsan.s_target_run + 0xcc)%Z)];
[(symaddr (Symbols.AsanUbsan.s___interceptor_free + 0x138)%Z); (symaddr (Symbols.AsanUbsan.s_LLVMFuzzerTestOneInput + 0x680)%Z)];
[(symaddr (Symbols.AsanUbsan.s___interceptor_free + 0x138)%Z); (symaddr (Symbols.AsanUbsan.s_LLVMFuzzerTestOneInput + 0x680)%Z); (symaddr (Symbols.AsanUbsan.s_target_run + 0xcc)%Z)];
[(symaddr (Symbols.AsanUbsan.s___interceptor_free + 0x138)%Z); (symaddr (Symbols.AsanUbsan.s_LLVMFuzzerTestOneInput + 0x688)%Z)];
[(symaddr (Symbols.AsanUbsan.s___interceptor_free + 0x138)%Z); (symaddr (Symbols.AsanUbsan.s_LLVMFuzzerTestOneInput + 0x688)%Z); (symaddr (Symbols.AsanUbsan.s_target_run + 0xcc)%Z)];
[(symaddr (Symbols.AsanUbsan.s___interceptor_free + 0x138)%Z); (symaddr (Symbols.AsanUbsan.s_fclose + 0xa4)%Z)];
[(symaddr (Symbols.AsanUbsan.s___interceptor_free + 0x138)%Z); (symaddr (Symbols.AsanUbsan.s_fclose + 0xac)%Z)];
[(symaddr (Symbols.AsanUbsan.s___interceptor_malloc + 0xc8)%Z)];
[(symaddr (Symbols.AsanUbsan.s___interceptor_malloc + 0xc8)%Z); (symaddr (Symbols.AsanUbsan.s_main + 0x54)%Z)];
[(symaddr (Symbols.AsanUbsan.s___interceptor_malloc + 0xc8)%Z); (symaddr (Symbols.AsanUbsan.s_main + 0xa8)%Z)];
[(symaddr (Symbols.AsanUbsan.s___interceptor_malloc + 0xc8)%Z); (symaddr (Symbols.AsanUbsan.s_target_run + 0x64)%Z)];
[(symaddr (Symbols.AsanUbsan.s___interceptor_malloc + 0xc8)%Z); (symaddr (Symbols.AsanUbsan.s_LLVMFuzzerTestOneInput + 0x1a0)%Z)];
[(symaddr (Symbols.AsanUbsan.s___interceptor_malloc + 0xc8)%Z); (symaddr (Symbols.AsanUbsan.s_LLVMFuzzerTestOneInput + 0x1a0)%Z); (symaddr (Symbols.AsanUbsan.s_target_run + 0xcc)%Z)];
[(symaddr (Symbols.AsanUbsan.s___interceptor_malloc + 0xc8)%Z); (symaddr (Symbols.AsanUbsan.s_LLVMFuzzerTestOneInput + 0x2b4)%Z)];
[(symaddr (Symbols.AsanUbsan.s___interceptor_malloc + 0xc8)%Z); (symaddr (Symbols.AsanUbsan.s_LLVMFuzzerTestOneInput + 0x2b4)%Z); (symaddr (Symbols.AsanUbsan.s_target_run + 0xcc)%Z)];
[(symaddr (Symbols.AsanUbsan.s___interceptor_malloc + 0xc8)%Z); (symaddr (Symbols.AsanUbsan.s_fdopen + 0x4c)%Z)];
[(symaddr (Symbols.AsanUbsan.s___interceptor_malloc + 0xc8)%Z); (symaddr (Symbols.AsanUbsan.s_fmemopen + 0x9c)%Z); (symaddr (Symbols.AsanUbsan.s_LLVMFuzzerTestOneInput + 0x1f8)%Z)];
[(symaddr (Symbols.AsanUbsan.s___interceptor_malloc + 0xc8)%Z); (symaddr (Symbols.AsanUbsan.s_fmemopen + 0x9c)%Z); (symaddr (Symbols.AsanUbsan.s_LLVMFuzzerTestOneInput + 0x1f8)%Z); (symaddr (Symbols.AsanUbsan.s_target_run + 0xcc)%Z)];
[(symaddr (Symbols.AsanUbsan.s___interceptor_malloc + 0xc8)%Z); (symaddr (Symbols.AsanUbsan.s_fmemopen + 0x9c)%Z); (symaddr (Symbols.AsanUbsan.s_LLVMFuzzerTestOneInput + 0x638)%Z)];
[(symaddr (Symbols.AsanUbsan.s___interceptor_malloc + 0xc8)%Z); (symaddr (Symbols.AsanUbsan.s_fmemopen + 0x9c)%Z); (symaddr (Symbols.AsanUbsan.s_LLVMFuzzerTestOneInput + 0x638)%Z); (symaddr (Symbols.AsanUbsan.s_target_run + 0xcc)%Z)];
[(symaddr (Symbols.AsanUbsan.s___interceptor_malloc + 0xc8)%Z); (symaddr (Symbols.AsanUbsan.s_fmemopen + 0xac)%Z); (symaddr (Symbols.AsanUbsan.s_LLVMFuzzerTestOneInput + 0x1f8)%Z)];
[(symaddr (Symbols.AsanUbsan.s___interceptor_malloc + 0xc8)%Z); (symaddr (Symbols.AsanUbsan.s_fmemopen + 0xac)%Z); (symaddr (Symbols.AsanUbsan.s_LLVMFuzzerTestOneInput + 0x1f8)%Z); (symaddr (Symbols.AsanUbsan.s_target_run + 0xcc)%Z)];
[(symaddr (Symbols.AsanUbsan.s___interceptor_malloc + 0xc8)%Z); (symaddr (Symbols.AsanUbsan.s_fmemopen + 0xac)%Z); (symaddr (Symbols.AsanUbsan.s_LLVMFuzzerTestOneInput + 0x638)%Z)];
[(symaddr (Symbols.AsanUbsan.s___interceptor_malloc + 0xc8)%Z); (symaddr (Symbols.AsanUbsan.s_fmemopen + 0xac)%Z); (symaddr (Symbols.AsanUbsan.s_LLVMFuzzerTestOneInput + 0x638)%Z); (symaddr (Symbols.AsanUbsan.s_target_run + 0xcc)%Z)]].
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
Lemma TRACES_fmemopen_U : forall t, In t TRACES_fmemopen -> In t Tfib_universe.
Proof. intros t H. apply memZL_In. exact (allb_In (fun t => memZL t Tfib_universe) TRACES_fmemopen t ltac:(vm_compute; reflexivity) H). Qed.
Lemma TRACES_fclose_U : forall t, In t TRACES_fclose -> In t Tfib_universe.
Proof. intros t H. apply memZL_In. exact (allb_In (fun t => memZL t Tfib_universe) TRACES_fclose t ltac:(vm_compute; reflexivity) H). Qed.
Lemma TRACES_fdopen_U : forall t, In t TRACES_fdopen -> In t Tfib_universe.
Proof. intros t H. apply memZL_In. exact (allb_In (fun t => memZL t Tfib_universe) TRACES_fdopen t ltac:(vm_compute; reflexivity) H). Qed.
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
