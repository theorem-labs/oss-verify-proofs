(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Plain Require Import RunDraw.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Plain Require PC_s12iface ROpNew_nt RF_malloc_spec RF_free_spec.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.SegN Require NUMP_sound.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.SegP2 Require PS2_main.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.

Theorem stage2_closed : forall rc : runConstT, @PC_s12iface.stage2_stmt rc.
Proof.
  intros rc.
  apply (PS2_main.stage2_proof (ROpNew_nt.opnew_nt_proof RF_malloc_spec.rmalloc_spec)
                               (ROpNew_nt.opdelete_arr_proof RF_free_spec.rfree_spec_proof)).
  - intros GP. apply (NUMP_sound.NUMP.summ_ghostfree NUMP_sound.NUMP.GP0 GP); [reflexivity | repeat constructor | exact NUMP_sound.NUMP.sfp_ok].
  - intros GP. apply (NUMP_sound.NUMP.summ_ghostfree NUMP_sound.NUMP.GP0 GP); [reflexivity | repeat constructor | exact NUMP_sound.NUMP.pff_ok].
  - intros GP. apply (NUMP_sound.NUMP.summ_ghostfree NUMP_sound.NUMP.GP0 GP); [reflexivity | repeat constructor | exact NUMP_sound.NUMP.sfpc_ok].
  - intros GP. apply (NUMP_sound.NUMP.summ_ghostfree NUMP_sound.NUMP.GP0 GP); [reflexivity | repeat constructor | exact NUMP_sound.NUMP.pffc_ok].
Qed.

Print Assumptions stage2_closed.
