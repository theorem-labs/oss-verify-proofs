(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Lib Require Import Tac Arr Bytes ZBridge Frame ITree Ceiling.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Http Require Import HttpRep HttpTac.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Top Require Import AllocIF.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.B0.ZAW Require Import Segs Shadow Contracts AllocA0.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.B0.ZAA Require Import AEnv ADepot ALayout APrim PEnv ASec AQuar AHeap ALedger AHeap2 ALinkPg ALinkVm ALink ALinkPrim ALinkFree AFreeL8 ALinkFreeIn AVaOf.
Import ListNotations.
Open Scope Z_scope.

Definition set_pages (s : astB) (P' : list word) : astB :=
  mkASB (bs_H s) P' (bs_prim s) (bs_sec s) (bs_quar s) (bs_depot s) (bs_dtotal s) (bs_nsec s) (bs_live s) (bs_depot0 s).

Lemma set_pages_ghost : forall s P', bs_ghost (set_pages s P') = (bs_H s, P'). Proof. reflexivity. Qed.
Lemma set_pages_nsec : forall s P', bs_nsec (set_pages s P') = bs_nsec s. Proof. reflexivity. Qed.
Lemma set_pages_va : forall s P', va_of (set_pages s P') = va_of s. Proof. reflexivity. Qed.

Section PG.
Context {HC : HasCeiling}.
Variables (AL : alayout) (E : penv).
#[using="Type"] Lemma RHEAP_B_set_pages : forall s P' LB (m : mem), RHEAP_B AL E s LB m -> RHEAP_B AL E (set_pages s P') LB m.
Proof. intros [h pg pr se qu de dt ns lv d0] P' LB m HR. exact HR. Qed.
End PG.
