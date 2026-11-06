(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From OSSVerify.Proofs.simdjson.fuzz_atpointer.lib.Malloc Require Import Zf4 Za Zel.
From OSSVerify.Proofs.simdjson.fuzz_atpointer.lib.MallocU Require Import Zhz Zi1 Zgr Zhe Zhk Zg3 Zgt Zhc Zh3 Zgs.

From OSSVerify.Proofs.simdjson.fuzz_atpointer.lib.Lib Require Import Ceiling.
From OSSVerify.Proofs.simdjson.fuzz_atpointer.lib.P Require Import Rnd.
From OSSVerify.Proofs.simdjson.fuzz_atpointer.lib.Malloc Require Import Z7h.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Local Ltac std_lia__ := lia.
Local Ltac lia := first [std_lia__ | try (pose proof ceil_window_holds as CEIL_RANGE__); unfold ceil_window in *; std_lia__].
Local Ltac std_nia__ := nia.
Local Ltac nia := first [std_nia__ | try (pose proof ceil_window_holds as CEIL_RANGE__); unfold ceil_window in *; std_nia__].
Local Ltac OSSVerify.Proofs.simdjson.fuzz_atpointer.lib.Lib.Z11w.flia ::= first [ assumption | OSSVerify.Proofs.simdjson.fuzz_atpointer.lib.Lib.Z11w.slim; lia | lia ].
Local Ltac OSSVerify.Proofs.simdjson.fuzz_atpointer.lib.Lib.Z11w.mlia ::= Z.div_mod_to_equations; lia.
Local Ltac OSSVerify.Proofs.simdjson.fuzz_atpointer.lib.Lib.Step.slia ::= first [ exact I | lia | split; [lia|exact I] ].
Section WithCeiling0. Context {CE__ : Ceiling} {RN__ : RunRnd}.
Theorem rmalloc_spec : rmalloc_stmt.
Proof. try (pose proof ceil_window_holds as CEIL_RANGE__).
  exact (rmalloc_spec_proof ras_pre2 as_inv2 ralloc_slot_spec ras_pre2_intro (rbig_spec ram_pre ralloc_meta_spec ramp_big)).
Qed.
End WithCeiling0.
