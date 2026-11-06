(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import MemImageType.
From OSSVerify.Proofs.simdjson.fuzz_utf8.lib Require Import AsanMainU.
From OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Plain Require Import PImg.
From OSSVerify.Proofs.simdjson.fuzz_utf8.lib.AsanW Require Import AImg AMalloc_iface ADriver_iface AInstance AInstanceM AInstanceF AMain_closed AMain_closedI AFreeAll.
From OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common Require Import RunDraw.

Set Keyed Unification.   (* [comment removed for export] *)
(* [comment removed for export] *)
Theorem asan_impl_final :
  forall XPf : (forall rc : runConstT, Z -> ExitParams), (forall rc : runConstT, @xp_closed_stmt rc (XPf rc)) ->
  impl_stmt ASTAGE.
Proof. intros XPf XPC. exact (asan_impl_of_free (fun rc : runConstT => @AHI_free rc) XPf XPC). Qed.
