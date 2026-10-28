(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump_raw_tape.lib.Lib Require Import Tac Mem Frame Cells Step Arr ImageA.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump_raw_tape.lib.A Require Import Shadow.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump_raw_tape.lib.B Require Import Layout RT_iface R_unwind_defs R_unwind_gen RT_state RT_rep RT_sep.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Section GWIN. Context {GWc : OssFuzzTheorems.Proofs.simdjson.fuzz_dump_raw_tape.lib.A.Shadow.GW}.
Lemma ART_stkwin : forall Σ (m : mem), ART_A Σ m -> stk bsegs m (l_ACEIL (lay Σ)) (l_top (lay Σ)).
Proof. intros Σ m HA. pose proof (ART_shadow Σ m HA) as (_ & _ & _ & _ & SW). exact SW. Qed.

Lemma art_trace_main : forall Σ (m : mem) pc (ra s0 sp : word),
  ART_A Σ m -> l_ACEIL (lay Σ) <= bv_unsigned sp -> unwind_ok ra s0 sp -> 0 <= pc < 2 ^ 64 ->
  exists ch tr, chain_cells [(0, bv_unsigned sp)] m (bv_unsigned s0) ch
    /\ unwind_trace pc 4096 (l_top (lay Σ) - 0x800000) (l_top (lay Σ)) 30 (bv_unsigned sp) ((bv_unsigned ra, bv_unsigned s0) :: ch) = Some tr
    /\ tr_ok tr /\ (1 <= length tr <= 30)%nat.
Proof.
  intros Σ m pc ra s0 sp HA HLO UW Hpc.
  pose proof (geo_layout Σ m HA) as HL. unfold layout_ok in HL. destruct HL as ((W1 & W2) & _ & (T1 & T2) & _).
  unfold sp_window_lo, sp_window_hi in *.
  assert (H0 : 0 <= l_ACEIL (lay Σ)) by (unfold l_ACEIL, STACK_WIN; lia).
  assert (H64 : l_top (lay Σ) <= 2 ^ 64) by lia.
  pose proof (bv_unsigned_in_range 64 ra) as Rra. unfold bv_modulus in Rra. change (2 ^ Z.of_N 64) with (2 ^ 64) in Rra.
  destruct (gen_trace_main m pc (l_top (lay Σ) - 0x800000) (l_top (lay Σ)) 30 (l_ACEIL (lay Σ)) (bv_unsigned sp) (l_top (lay Σ))
              (bv_unsigned ra) (bv_unsigned s0) (ART_stkwin Σ m HA) H0 HLO H64 ltac:(lia) ltac:(lia) Hpc Rra UW)
    as (ch & tr & CC & UT & (L1 & L2) & TR).
  exists ch, tr. split; [exact CC|]. split; [exact UT|]. split; [exact TR|]. lia.
Qed.

End GWIN.
