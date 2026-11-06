(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.simdjson.fuzz_ondemand.lib.Lib Require Import Mem Frame Cells Step Arr ImageA RzCPS.
From OSSVerify.Proofs.simdjson.fuzz_ondemand.lib.A Require Import Layout Shadow RT_iface RT_state RT_rep RT_facts TopA_iodefs RT_io RT_cli Od_defsA.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Lemma rta_got_tabs3 : forall Σ m, ART_A Σ m ->
  ro_cells asegs m 0x10d878 [C8 (Z_to_bv 64 0x238a0); C8 (Z_to_bv 64 0x24d40); C8 (Z_to_bv 64 0x239e0)].
Proof. intros Σ m HA. apply (cli_ro_at m); [exact (rta_cli_ro Σ m HA)| cli_in]. Qed.

Theorem rta_got_tabs : forall Σ m, ART_A Σ m -> ro_cells asegs m OD_GOT_TABS od_got_cells.
Proof.
  intros Σ m HA. unfold OD_GOT_TABS, od_got_cells.
  change [C8 (Z_to_bv 64 0x238a0); C8 (Z_to_bv 64 0x24d40); C8 (Z_to_bv 64 0x239e0); C8 (Z_to_bv 64 0x2d070)]
    with ([C8 (Z_to_bv 64 0x238a0); C8 (Z_to_bv 64 0x24d40); C8 (Z_to_bv 64 0x239e0)] ++ [C8 (Z_to_bv 64 0x2d070)]).
  apply ro_cells_app_c. split; [exact (rta_got_tabs3 Σ m HA)|].
  exact (rta_got_nothrow Σ m HA).
Qed.
