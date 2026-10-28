(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.simdjson.fuzz_print_json.lib.Lib Require Import Tac Arr Bytes StoreFast FP.
From OssFuzzTheorems.Proofs.simdjson.fuzz_print_json.lib.Sj Require Import SjS1Out SjStage2 SjLeaves SjTape SjTapeInv SjTapeList SjExpDigits.
From OssFuzzTheorems.Proofs.simdjson.fuzz_print_json.lib.U Require Import Sj_stage2_defs Sj_stage2_tapek Sj_tables Sj_stage2_traps Sj_stage2_guard
  Sj_stage2_numkit Sj_stage2_numkit2 Sj_stage2_numkitr Sj_stage2_numr_defs Sj_stage2_numr_loops.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac lia ::= r_lia.
Local Ltac tlia ::= r_tlia.
Local Ltac solve_load ::= first [ solve_load_base | s2_load_cp | solve_load_image ].
Local Ltac solve_store ::= first [ solve_store0 | s2_store_wr ].
Local Ltac s2_store_done_wr ::= s2_store_done_wr_v2.

Section NumR1.
  Variable E : s2env.
  Hypothesis OK : env_ok E.
  Variables (CP : Z) (t : list Z).
  Hypothesis TOK : bytes_ok t.
  Hypothesis CP0 : (0 < CP)%Z.
  Hypothesis CPHI : (CP + blen t + 64 <= e_lo E)%Z.
  Hypothesis CPSEP : cp_sep E CP t.
  Notation rl := (blen t).

  Ltac n_exit KX := ngrun_to 0x43990%Z; eapply KX; s2_close_memx.
  Ltac n_close := first [ unfold RSL; s2_close_mem0 | eapply MEMI_RSL; [s2_close_mem0 | reflexivity ..] | eassumption ].

  Lemma seg_numr_entry : forall (Q : machine_state -> Prop),
    rdel_errA_k E CP Q ->
    (forall neg p, (0 <= neg <= 1)%Z -> (neg < rl)%Z -> (neg < p <= rl)%Z -> B (crs t) p = 46%Z -> numr_frac_k E CP t Q neg p) ->
    (forall neg p, (0 <= neg <= 1)%Z -> (neg < rl)%Z -> (neg < p <= rl)%Z -> numr_scan_k E CP t Q neg p 0 (B (crs t) p)) ->
    rootnum_k E CP t Q.
  Proof using OK TOK CP0 CPHI CPSEP.
    intros Q KX KF KS. unfold rootnum_k. intros until m1. intros HM CPRO.
    pose proof (crs_bytes_ok t TOK) as BOK. pose proof (crs_blen t) as CBL0. pose proof CBL0 as CBL. rewrite zbytes_length in CBL.
    pose proof (blen_nonneg t) as RL0.
    pose proof (B_range (crs t) 0 BOK) as HBF.
    s2_env OK. unfold RSL in HM.
    s2_open_mem HM.
    ngrun_to 0x438f0%Z.
    match goal with |- context [Z.b2z ?c] =>
      assert (HNEG : (0 <= Z.b2z c <= 1)%Z) by (destruct c; cbn; lia);
      set (neg := Z.b2z c) in *; clearbody neg end.
    pose proof (B_range (crs t) neg BOK) as HB0.
    ngrun.
    if_cases K0; zify_cond K0.
    -
      ngrun. if_cases K1; zify_cond K1; [|exfalso; lia].
      n_exit KX.
    -
      assert (HS : (neg < rl)%Z) by (apply Bc_lt; lia).
      ngrun_to 0x43928%Z.
      eapply (numr_L1 E OK Q CP t TOK CP0 CPHI (S (Z.to_nat rl))); [exact CPRO | lia | lia |].
      intros p' ya2 yt4 ya6 yt5 HP'.
      pose proof (B_range (crs t) p' BOK) as HBP.
      ngrun.
      if_cases K2; zify_cond K2.
      2:{ n_exit KX. }
      ngrun.
      if_cases K3; zify_cond K3.
      + ngrun.
        if_cases K5; zify_cond K5.
        * ngrun_to 0x44cb0%Z. eapply (KS neg p' HNEG HS ltac:(lia)); n_close.
        * ngrun_to 0x43b94%Z. eapply (KF neg p' HNEG HS ltac:(lia) ltac:(lia)); n_close.
      + ngrun.
        if_cases K4; zify_cond K4.
        2:{ n_exit KX. }
        ngrun.
        if_cases K5; zify_cond K5.
        * ngrun_to 0x44cb0%Z. eapply (KS neg p' HNEG HS ltac:(lia)); n_close.
        * ngrun_to 0x43b94%Z. eapply (KF neg p' HNEG HS ltac:(lia) ltac:(lia)); n_close.
  Qed.
End NumR1.
