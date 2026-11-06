(* Image root: reac-pw/fuzz_link, fuzz_link.asan (sha256 059dae63e07ca2d80ae9227fa125d40586a02172c96d2b6884f8617ab912061d;
   unstripped twin sha256 66cd0f159895f119b29a44eb3760cfda78506402a019729057dba69562af9d9f). __asan_default_options
   (0x81d20) returns "allocator_may_return_null=1" only, so malloc_context_size keeps its default 30 (kUnwindMax 30);
   nothing here rests on a malloc_context_size of 1. *)
(* The facts about the allocation-trace universe (ACej.v, Tfib_universe) that the TFIB_T closing takes at its entry
   points, in the form its consumers use them:
   - lib/A/AD2l.v:41 `as_universe := Tfib_univ` (ACejUniv.v), whose fixed traces are ACej.Tfib_universe (re-exported
     here);
   - lib/A/AD2l.v:80, field ts_universe `universe_ok (as_universe B)`: ACej.Tfib_universe_ok;
   - lib/A/AD2l.v:81, field ts_universe_drv `forall t, In t DRV_TRACES -> In t (as_universe B)`: Tfib_universe_drv
     below, over lib/A/AF0m.v's DRV_TRACES.
   No fact here depends on EV_MAX (lib/Reusable/YG00.v): universe_ok (lib/Reusable/YG01.v) is stated with DEPOT_MAX and
   kUnwindMax only. *)
From Stdlib Require Import ZArith List Bool Lia.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YG00 YG01.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A Require Export ACej.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A Require Import AF0m.
Import ListNotations.
Local Open Scope Z_scope.
(* The driver's traces, AF0m.v's DRV_TRACES: main +0x50, +0xa4 and target_run +0x60 call the malloc wrapper (returns
   0x81d80, 0x81dd4, 0x82060); main +0xc8, +0x1f8 and target_run +0xf4 call the free wrapper (returns 0x81df8, 0x81f28,
   0x820f4). s0 holds an integer at each call, so the chain ends at the call. The two one-word traces are the
   frame0_ok = false case. Trace start (pc0): malloc 0x5436c, free 0x5420c. Each row is a row of Tfib_universe. *)
Lemma Tfib_universe_drv : forall t, In t DRV_TRACES -> In t Tfib_universe.
Proof.
intros t H. apply memZL_In.
exact (allb_In (fun t => memZL t Tfib_universe) DRV_TRACES t ltac:(vm_compute; reflexivity) H).
Qed.
