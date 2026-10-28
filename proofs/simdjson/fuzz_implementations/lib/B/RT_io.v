(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.Lib Require Import Mem Frame Cells Step Arr ImageA RzCPS.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.A Require Import Shadow.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.B Require Import Layout RT_iface RT_state RT_rep RT_facts TopA_iodefs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Section GWIN. Context {GWc : OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.A.Shadow.GW}.
Theorem rta_io : forall Σ m, ART_A Σ m -> io_consts m.
Proof.
  intros Σ m HA. pose proof (ART_consts Σ m HA) as (_ & _ & _ & _ & _ & _ & _ & IC). unfold icells_rep in IC.
  repeat match type of IC with _ /\ (_ /\ (_ /\ (_ /\ _))) => destruct IC as [_ IC] end. destruct IC as (IR & IO & _).
  split; [exact IR|]. split; [exact IO|].
  unfold io_acc. repeat (apply Forall_cons; [cbn [fst snd];
    match goal with |- acc _ _ ?a ?n => apply (rta_acc_static_cs Σ m HA (a, a + n)) end;
    [unfold CS_ACC; solve [repeat (first [left; reflexivity | right])] | cbn [fst snd]; lia | cbn [fst snd]; lia]|]).
  apply Forall_nil.
Qed.

Theorem rta_mtab : forall Σ m, ART_A Σ m -> mtab_rep (lay Σ) m.
Proof.
  intros Σ m HA. pose proof (ART_consts Σ m HA) as (_ & _ & _ & _ & _ & _ & _ & IC). unfold icells_rep in IC.
  repeat match type of IC with _ /\ (_ /\ (_ /\ (_ /\ (_ /\ _)))) => destruct IC as [_ IC] end. destruct IC as (MT & _). exact MT.
Qed.

End GWIN.
