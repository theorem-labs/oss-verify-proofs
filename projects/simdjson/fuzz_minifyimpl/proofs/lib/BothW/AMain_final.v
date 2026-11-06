(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import MemImageType.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib Require Import BothMainU.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.Plain Require Import PImg.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.BothW Require Import BImg AMalloc_iface ADriver_iface AInstance AInstanceM AInstanceF AMain_closed AMain_closedI AFreeAll.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.Common Require Import RunDraw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Set Keyed Unification.   (* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition asan_client_stmt : Prop := forall rc : runConstT, @asan_client_at rc (AI_of (@AHI_free rc)).

Theorem both_impl_final :
  forall XPf : (forall rc : runConstT, Z -> ExitParams), (forall rc : runConstT, @xp_closed_stmt rc (XPf rc)) ->
  asan_client_stmt -> impl_stmt ASTAGE.
Proof. intros XPf XPC CLIENT. exact (both_impl_of_free (fun rc : runConstT => @AHI_free rc) XPf XPC CLIENT). Qed.
