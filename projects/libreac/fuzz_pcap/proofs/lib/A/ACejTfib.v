From OSSVerify.Proofs.libreac.fuzz_pcap.lib Require Import SymAddr.
(* Image root: the original libreac v1.9.0 set: the pinned fuzz_pcap.asan image (sha256 b7a91d9b1fb0),
   its unstripped twin (sha256 36da3052c383); statements of record
   ed6b6b7b0ab. malloc_context_size 30 (kUnwindMax 30); nothing here rests on a malloc_context_size of 1. *)
(* libreac/fuzz_pcap v1.9.0, fuzz_pcap.asan: the facts about the allocation-trace universe (ACej.v, Tfib_universe) that
   cgif_file_fuzzer's TFIB_T closing takes at its entry points, in the form its consumers use them (cgif_file_fuzzer at
   ossv/recipes c8557374ad2e):
   - lib/A/AD2l.v:37 `as_universe := Tfib_universe`: ACej.Tfib_universe (re-exported here);
   - lib/A/AD2l.v:78, field ts_universe (lib/A/AF0m.v:313) `universe_ok (as_universe B)`: ACej.Tfib_universe_ok;
   - lib/A/AD2l.v:79-82, field ts_universe_drv (lib/A/AF0m.v:314) `forall t, In t DRV_TRACES -> In t (as_universe B)`:
     Tfib_universe_drv below, over Tfib_drv_traces, the list that the core's lib/A/AF0m.v DRV_TRACES must be.
   No fact here depends on EV_MAX (lib/Reusable/YG00.v): universe_ok (lib/Reusable/YG01.v) is stated with DEPOT_MAX and
   kUnwindMax only. *)
From Stdlib Require Import ZArith List Bool Lia.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YG00 YG01.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.A Require Export ACej.
Import ListNotations.
Local Open Scope Z_scope.
(* The driver's traces, in the order and form of cgif_file_fuzzer's lib/A/AF0m.v:18-20: main +0x50, +0xa4 and target_run
   +0x60 call the malloc wrapper (returns 0x802ec, 0x80340, 0x805cc); main +0xc8, +0x1f8 and target_run +0xf4 call the
   free wrapper (returns 0x80364, 0x80494, 0x80660). s0 holds an integer at each call, so the chain ends at the call. The
   two one-word traces are the frame0_ok = false case. Trace start (pc0): malloc 0x52e74, free 0x52d14. *)
Definition Tfib_drv_traces : list (list Z) :=
[[(symaddr (Symbols.Asan.s___interceptor_malloc + 0xc8)%Z); (symaddr (Symbols.Asan.s_main + 0x54)%Z)]; [(symaddr (Symbols.Asan.s___interceptor_malloc + 0xc8)%Z); (symaddr (Symbols.Asan.s_main + 0xa8)%Z)]; [(symaddr (Symbols.Asan.s___interceptor_malloc + 0xc8)%Z); (symaddr (Symbols.Asan.s_target_run + 0x64)%Z)]; [(symaddr (Symbols.Asan.s___interceptor_malloc + 0xc8)%Z)];
[(symaddr (Symbols.Asan.s___interceptor_free + 0x138)%Z); (symaddr (Symbols.Asan.s_main + 0xcc)%Z)]; [(symaddr (Symbols.Asan.s___interceptor_free + 0x138)%Z); (symaddr (Symbols.Asan.s_main + 0x1fc)%Z)]; [(symaddr (Symbols.Asan.s___interceptor_free + 0x138)%Z); (symaddr (Symbols.Asan.s_target_run + 0xf8)%Z)]; [(symaddr (Symbols.Asan.s___interceptor_free + 0x138)%Z)]].
Lemma Tfib_universe_drv : forall t, In t Tfib_drv_traces -> In t Tfib_universe.
Proof.
intros t H. apply memZL_In.
exact (allb_In (fun t => memZL t Tfib_universe) Tfib_drv_traces t ltac:(vm_compute; reflexivity) H).
Qed.
(* The core owners' declared plan is that lib/A/AF0m.v defines DRV_TRACES := ACejTfib.Tfib_drv_traces (importing this
   file) and that AD2l cites Tfib_universe_drv for the field ts_universe_drv. Neither file is on any branch yet. *)
