(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.leptonica.edge_fuzzer.lib.K5.Lib Require Import Mem Frame Cells Step Arr.
From OSSVerify.Proofs.leptonica.edge_fuzzer.lib.K5.B9 Require Import ImageA.
From OSSVerify.Proofs.leptonica.edge_fuzzer.lib.K5.Lib Require Import RzCPS.
From OSSVerify.Proofs.leptonica.edge_fuzzer.lib.K5.B9 Require Import Layout.
From OSSVerify.Proofs.leptonica.edge_fuzzer.lib.K5.AG Require Import Shadow.
From OSSVerify.Proofs.leptonica.edge_fuzzer.lib.K5.B9 Require Import RT_iface RT_state RT_rep RT_facts TopA_iodefs.
Import ListNotations.
Open Scope Z_scope.

Theorem rta_io : forall Σ m, ART_A Σ m -> io_consts m.
Proof.
  intros Σ m HA. pose proof (ART_consts Σ m HA) as (_ & _ & _ & _ & _ & _ & _ & IC). unfold icells_rep in IC.
  repeat match type of IC with _ /\ (_ /\ _) => destruct IC as [_ IC] end. destruct IC as [IR IO].
  split; [exact IR|]. split; [exact IO|].
  (* [comment removed for export] *)
  apply Forall_forall. intros [a n] Hin. cbn [fst snd].
  assert (B : forallb (fun r => existsb (fun c => andb (Z.eqb (fst c) (fst r)) (Z.eqb (snd c) (Z.add (fst r) (snd r)))) CS_ACC) io_acc = true) by (vm_compute; reflexivity).
  rewrite forallb_forall in B. specialize (B _ Hin). apply existsb_exists in B as ([c1 c2] & Hc & E). cbn [fst snd] in E.
  apply andb_prop in E as [E1 E2]. apply Z.eqb_eq in E1. apply Z.eqb_eq in E2. subst c1 c2.
  apply (rta_acc_static_cs Σ m HA (a, a + n) a n Hc); cbn [fst snd]; lia.
Qed.
