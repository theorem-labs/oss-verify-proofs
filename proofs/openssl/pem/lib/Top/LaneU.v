(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From OssFuzzTheorems.openssl.pem.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Lib Require Import Ceiling Image Stage.
From OssFuzzTheorems.Proofs.openssl.pem.lib.P Require Import Rnd.
From OssFuzzTheorems.Proofs.openssl.pem.lib.U Require Import Fz_iface Driver_iface.
From OssFuzzTheorems.Proofs.openssl.pem.lib.U Require Impl_closed.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Spec Require Import ModelInv UnforcedK.
From OssFuzzTheorems.Proofs.openssl.pem.lib Require Spec.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Top Require Import TopBridge PlainLane.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
Theorem U_realizes_at :
  (forall (CE__ : Ceiling) (RN__ : RunRnd), exists C : cli_sig, cli0_at_main C /\ rfuzz_init_stmt C /\ rfuzz_one_stmt C) ->
  forall lim : Z, (KLIM + SMALLREQ <= lim)%Z ->
  image_realizes usegs Ubsan.M.init_pc Ubsan.M.phdrs lim Spec.spec.
Proof.
  intros FUZZ lim Hlim. apply (plain_lane_realizes usegs ustage).
  - exact segs_low_usegs.
  - exact Hlim.
  - intros en inp Hve Hvi. exact (Impl_closed.impl_U_closed FUZZ en inp Hve Hvi).
Qed.

Theorem U_realizes_of :
  (forall (CE__ : Ceiling) (RN__ : RunRnd), exists C : cli_sig, cli0_at_main C /\ rfuzz_init_stmt C /\ rfuzz_one_stmt C) ->
  image_realizes usegs Ubsan.M.init_pc Ubsan.M.phdrs target_alloc_limit Spec.spec.
Proof. intros FUZZ. apply (U_realizes_at FUZZ). unfold KLIM, SMALLREQ, target_alloc_limit. lia. Qed.
