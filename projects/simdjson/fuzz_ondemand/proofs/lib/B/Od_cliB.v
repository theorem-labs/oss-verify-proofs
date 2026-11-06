(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.simdjson.fuzz_ondemand.lib.Lib Require Import Mem Frame Cells Step Arr ImageA RzCPS.
From OSSVerify.Proofs.simdjson.fuzz_ondemand.lib.A Require Import Shadow.
From OSSVerify.Proofs.simdjson.fuzz_ondemand.lib.B Require Import Layout RT_iface RT_state RT_rep RT_facts TopA_iodefs RT_io RT_cli Od_defsB.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Lemma rta_got_tabs3 : forall Σ m, ART_A Σ m ->
  ro_cells bsegs m 0x11b9f8 [C8 (Z_to_bv 64 0x23900); C8 (Z_to_bv 64 0x24cc0); C8 (Z_to_bv 64 0x24da0); C8 (Z_to_bv 64 0x23a40)].
Proof. intros Σ m HA. apply (cli_ro_at m); [exact (rta_cli_ro Σ m HA)| cli_in]. Qed.

Theorem rta_got_tabs : forall Σ m, ART_A Σ m -> ro_cells bsegs m OD_GOT_TABS od_got_cells.
Proof.
  intros Σ m HA. unfold OD_GOT_TABS, od_got_cells.
  change [C8 (Z_to_bv 64 0x23900); C8 (Z_to_bv 64 0x24cc0); C8 (Z_to_bv 64 0x24da0); C8 (Z_to_bv 64 0x23a40); C8 (Z_to_bv 64 0x2cd30)]
    with ([C8 (Z_to_bv 64 0x23900); C8 (Z_to_bv 64 0x24cc0); C8 (Z_to_bv 64 0x24da0); C8 (Z_to_bv 64 0x23a40)] ++ [C8 (Z_to_bv 64 0x2cd30)]).
  apply ro_cells_app_c. split; [exact (rta_got_tabs3 Σ m HA)|].
  exact (rta_got_nothrow Σ m HA).
Qed.
