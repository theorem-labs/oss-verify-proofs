(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Lib Require Import Mem Frame Cells Step Arr ImageA RzCPS.
From OssFuzzTheorems.Proofs.openssl.pem.lib.A Require Import Shadow.
From OssFuzzTheorems.Proofs.openssl.pem.lib.A Require Import Layout RT_iface RT_state RT_rep RT_facts TopA_iodefs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Theorem rta_io : forall Σ m, ART_A Σ m -> io_consts m.
Proof.
  intros Σ m HA. pose proof (ART_consts Σ m HA) as (_ & _ & _ & _ & _ & _ & _ & IC). unfold icells_rep in IC.
  repeat match type of IC with _ /\ (_ /\ _) => destruct IC as [_ IC] end. destruct IC as [IR IO].
  split; [exact IR|]. split; [exact IO|].
  unfold io_acc. repeat (apply Forall_cons; [cbn [fst snd];
    match goal with |- acc _ _ ?a ?n => apply (rta_acc_static_cs Σ m HA (a, a + n)) end;
    [unfold CS_ACC; solve [repeat (first [left; reflexivity | right])] | cbn [fst snd]; lia | cbn [fst snd]; lia]|]).
  apply Forall_nil.
Qed.
