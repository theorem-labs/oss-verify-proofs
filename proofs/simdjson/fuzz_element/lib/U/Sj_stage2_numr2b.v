(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Lib Require Import Tac Arr Bytes StoreFast FP.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Sj Require Import SjS1Out SjStage2 SjLeaves SjTape SjTapeInv SjTapeList SjExpDigits.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.U Require Import Sj_stage2_defs Sj_stage2_tapek Sj_tables Sj_stage2_traps Sj_stage2_guard
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

Section NumR2b.
  Variable E : s2env.
  Hypothesis OK : env_ok E.
  Variables (CP : Z) (t : list Z).
  Hypothesis TOK : bytes_ok t.
  Hypothesis CP0 : (0 < CP)%Z.
  Hypothesis CPHI : (CP + blen t + 64 <= e_lo E)%Z.
  Hypothesis CPSEP : cp_sep E CP t.
  Notation rl := (blen t).

  Ltac n_close := first [ unfold RSL; s2_close_mem0 | eapply MEMI_RSL; [s2_close_mem0 | reflexivity ..] | eassumption ].

  Lemma seg_numr_frac : forall (Q : machine_state -> Prop) neg p,
    (0 <= neg <= 1)%Z -> (0 <= p < rl)%Z ->
    (forall d r, (1 <= d)%Z -> (r = p + d)%Z -> (r <= rl)%Z -> numr_ftail_k E CP t Q neg p d r) ->
    numr_frac_k E CP t Q neg p.
  Proof using OK TOK CP0 CPHI CPSEP.
    intros Q neg p HNEG HP KT. unfold numr_frac_k. intros until m1. intros HM CPRO.
    pose proof (crs_bytes_ok t TOK) as BOK. pose proof (crs_blen t) as CBL0. pose proof CBL0 as CBL. rewrite zbytes_length in CBL.
    pose proof (B_range (crs t) (p + 1) BOK) as HB1. pose proof (B_range (crs t) (p + 2) BOK) as HB2. pose proof (B_range (crs t) (p + 3) BOK) as HB3.
    pose proof (B_range (crs t) (p + 4) BOK) as HB4. pose proof (B_range (crs t) (p + 5) BOK) as HB5. pose proof (B_range (crs t) (p + 6) BOK) as HB6.
    pose proof (B_range (crs t) (p + 7) BOK) as HB7. pose proof (B_range (crs t) (p + 8) BOK) as HB8.
    s2_env OK. unfold RSL in HM.
    s2_open_mem HM.
    ngrun_to 0x43de4%Z. fold_V8.
    ngrun.
    if_cases K0; zify_cond K0.
    -
      ngrun_to 0x44d90%Z.
      replace (p + 2)%Z with (p + 1 + 1)%Z by lia. replace (p + 3)%Z with (p + 1 + 2)%Z by lia. replace (p + 4)%Z with (p + 1 + 3)%Z by lia.
      replace (p + 5)%Z with (p + 1 + 4)%Z by lia. replace (p + 6)%Z with (p + 1 + 5)%Z by lia. replace (p + 7)%Z with (p + 1 + 6)%Z by lia.
      replace (p + 8)%Z with (p + 1 + 7)%Z by lia.
      eapply (KT 1%Z (p + 1)%Z); [lia | lia | lia | n_close ..].
    -
      pose proof (V8_range _ _ _ _ _ _ _ _ HB1 HB2 HB3 HB4 HB5 HB6 HB7 HB8) as HVR. rewrite ?(Z.mod_small _ _ HVR) in K0.
      pose proof (swar8_last _ _ _ _ _ _ _ _ HB1 HB2 HB3 HB4 HB5 HB6 HB7 HB8 K0) as HL.
      assert (HNZ : (p + 8 < rl)%Z) by (apply Bc_lt; lia).
      ngrun_to 0x43e50%Z.
      replace (CP + p + 9)%Z with (CP + (p + 9))%Z by lia.
      replace (Z_to_bv 64 1) with (Z_to_bv 64 (p + 9 - p - 8)) by (f_equal; lia).
      eapply (numr_L2 E OK Q CP t TOK CP0 CPHI (S (Z.to_nat rl)) p (p + 9)%Z); [exact CPRO | lia | lia |].
      intros q' ys6 ys7 ys8 ys9 ys11 yra ya2 yt5 HQ'.
      ngrun_to 0x44d90%Z.
      eapply (KT (q' - p)%Z q'); [lia | lia | lia | n_close ..].
  Qed.
End NumR2b.
