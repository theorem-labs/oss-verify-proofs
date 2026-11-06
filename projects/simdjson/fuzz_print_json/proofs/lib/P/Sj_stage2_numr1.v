(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.simdjson.fuzz_print_json.lib.Lib Require Import Tac Arr Bytes StoreFast FP.
From OSSVerify.Proofs.simdjson.fuzz_print_json.lib.Sj Require Import SjS1Out SjStage2 SjLeaves SjTape SjTapeInv SjTapeList.
From OSSVerify.Proofs.simdjson.fuzz_print_json.lib.P Require Import Sj_stage2_defs Sj_stage2_tapek Sj_tables Sj_stage2_auto Sj_stage2_auto2
  Sj_stage2_numkit Sj_stage2_numkit3 Sj_stage2_numr_defs Sj_stage2_numr_loops.
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
Local Ltac s2_store_done_wr ::= s2_note_tape; s2_store_done_wr_v2.

Section NumR1.
  Variable E : s2env.
  Hypothesis OK : env_ok E.
  Variables (CP : Z) (t : list Z).
  Hypothesis TOK : bytes_ok t.
  Hypothesis CP0 : (0 <= CP)%Z.
  Hypothesis CPHI : (CP + blen t + 64 <= e_lo E)%Z.
  Hypothesis CPSEP : cp_sep E CP t.
  Notation rl := (blen t).

  Lemma seg_numr_entry : forall (Q : machine_state -> Prop),
    rdel_err_k E CP Q ->
    (forall neg p, (0 <= neg <= 1)%Z -> (neg < rl)%Z -> (neg < p <= rl)%Z -> B (crs t) p = 46%Z -> numr_frac_k E CP t Q neg p) ->
    (forall neg p, (0 <= neg <= 1)%Z -> (neg < rl)%Z -> (neg < p <= rl)%Z -> numr_scan_k E CP t Q neg p) ->
    rootnum_k E CP t Q.
  Proof using OK TOK CP0 CPHI CPSEP.
    intros Q KX KF KS. unfold rootnum_k. intros until m1. intros HM CPRO.
    pose proof (crs_bytes_ok t TOK) as BOK. pose proof (crs_blen t) as CBL0. pose proof CBL0 as CBL. rewrite zbytes_length in CBL.
    pose proof (blen_nonneg t) as RL0.
    pose proof (B_range (crs t) 0 BOK) as HBF.
    s2_env OK. unfold RSL in HM.
    s2_open_mem HM.
    srun_to 0x41c58%Z.
    match goal with |- context [Z.b2z ?c] =>
      assert (HNEG : (0 <= Z.b2z c <= 1)%Z) by (destruct c; cbn; lia);
      set (neg := Z.b2z c) in *; clearbody neg end.
    pose proof (B_range (crs t) neg BOK) as HB0.
    srun.
    if_cases K0; zify_cond K0.
    -
      srun. if_cases K1; zify_cond K1; [|exfalso; lia].
      srun_to 0x41de0%Z. s2_err_exit KX.
      eapply (MEMX_of_MEMI E (e_nxt0 E)); [s2_close_mem0 | reflexivity ..].
    -
      assert (HS : (neg < rl)%Z) by (apply Bc_lt; lia).
      srun_to 0x41c78%Z.
      eapply (numr_L1 E Q CP t TOK CP0 (S (Z.to_nat rl))); [exact CPRO | lia | lia |].
      intros p' ya2 yt3 yt0 yt4 HP'.
      pose proof (B_range (crs t) p' BOK) as HBP.
      srun.
      if_cases K2; zify_cond K2.
      2:{ srun_to 0x41de0%Z. s2_err_exit KX. eapply (MEMX_of_MEMI E (e_nxt0 E)); [s2_close_mem0 | reflexivity ..]. }
      srun.
      if_cases K3; zify_cond K3.
      + srun.
        if_cases K5; zify_cond K5.
        * srun_to 0x429fc%Z. eapply (KS neg p' HNEG HS ltac:(lia)); [unfold RSL; s2_close_mem0 | exact CPRO].
        * eapply (KF neg p' HNEG HS ltac:(lia) ltac:(lia)); [unfold RSL; s2_close_mem0 | exact CPRO].
      + srun.
        if_cases K4; zify_cond K4.
        2:{ srun_to 0x41de0%Z. s2_err_exit KX. eapply (MEMX_of_MEMI E (e_nxt0 E)); [s2_close_mem0 | reflexivity ..]. }
        srun.
        if_cases K5; zify_cond K5.
        * srun_to 0x429fc%Z. eapply (KS neg p' HNEG HS ltac:(lia)); [unfold RSL; s2_close_mem0 | exact CPRO].
        * eapply (KF neg p' HNEG HS ltac:(lia) ltac:(lia)); [unfold RSL; s2_close_mem0 | exact CPRO].
  Qed.
End NumR1.
