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

Section NumR2.
  Variable E : s2env.
  Hypothesis OK : env_ok E.
  Variables (CP : Z) (t : list Z).
  Hypothesis TOK : bytes_ok t.
  Hypothesis CP0 : (0 < CP)%Z.
  Hypothesis CPHI : (CP + blen t + 64 <= e_lo E)%Z.
  Hypothesis CPSEP : cp_sep E CP t.
  Notation rl := (blen t).

  Ltac n_exit KX := ngrun_to 0x43b4c%Z; eapply KX; s2_close_memx.
  Ltac n_close := first [ unfold RSL; s2_close_mem0 | eapply MEMI_RSL; [s2_close_mem0 | reflexivity ..] | eassumption ].

  Lemma seg_numr_fdig : forall (Q : machine_state -> Prop) neg p d x,
    (0 <= p)%Z -> (1 <= d)%Z -> (p + d <= rl)%Z -> (0 <= x < 2^64)%Z -> (x mod 256 = B (crs t) (p + d))%Z -> rdel_errA_k E CP Q ->
    (forall d' x', (d <= d')%Z -> (p + d' <= rl)%Z -> (0 <= x' < 2^64)%Z -> (x' mod 256 = B (crs t) (p + d'))%Z ->
       numr_scan_k E CP t Q neg (p + d') (1 - d') x') ->
    numr_fdig_k E CP t Q neg p d x.
  Proof using OK TOK CP0 CPHI CPSEP.
    intros Q neg p d x HP HD HPD HX HXB KX KS. unfold numr_fdig_k. intros until m1. intros HM CPRO.
    pose proof (crs_bytes_ok t TOK) as BOK. pose proof (crs_blen t) as CBL0. pose proof CBL0 as CBL. rewrite zbytes_length in CBL. pose proof (B_range (crs t) (p + d) BOK) as HB0.
    pose proof (low_sub48 x _ HXB) as HX48.
    s2_env OK. unfold RSL in HM.
    s2_open_mem HM.
    ngrun.
    if_cases K0; zify_cond K0.
    -
      ngrun.
      if_cases K1; zify_cond K1.
      + ngrun_to 0x44e6c%Z.
        replace (CP + p + d)%Z with (CP + (p + d))%Z by lia.
        eapply (KS d x); [lia | lia | lia | exact HXB | n_close ..].
      + n_exit KX.
    - assert (HNZ : (p + d < rl)%Z) by (apply Bc_lt; lia).
      ngrun_to 0x44e24%Z.
      eapply (numr_L3 E OK Q CP t TOK CP0 CPHI (S (Z.to_nat rl)) p d); [exact CPRO | lia | lia | lia | lia |].
      intros d' ya2 yt5 yt1 yt6 HD' HPD'.
      pose proof (B_range (crs t) (p + d') BOK) as HBD.
      ngrun_to 0x44e6c%Z.
      replace (CP + p + d')%Z with (CP + (p + d'))%Z by lia.
      eapply (KS d' (B (crs t) (p + d'))); [lia | lia | lia | apply Z.mod_small; lia | n_close ..].
  Qed.

  Lemma seg_numr_ftail : forall (Q : machine_state -> Prop) neg p d r,
    (0 <= p)%Z -> (1 <= d)%Z -> (r = p + d)%Z -> (r <= rl)%Z ->
    (forall d' x, (d <= d')%Z -> (p + d' <= rl)%Z -> (0 <= x < 2^64)%Z -> (x mod 256 = B (crs t) (p + d'))%Z -> numr_fdig_k E CP t Q neg p d' x) ->
    numr_ftail_k E CP t Q neg p d r.
  Proof using OK TOK CP0 CPHI CPSEP.
    intros Q neg p d r HP HD HR HPD KD. unfold numr_ftail_k. intros until m1. intros HM CPRO.
    pose proof (crs_bytes_ok t TOK) as BOK. pose proof (crs_blen t) as CBL0. pose proof CBL0 as CBL. rewrite zbytes_length in CBL.
    pose proof (B_range (crs t) r BOK) as HB0. pose proof (B_range (crs t) (r + 1) BOK) as HB1. pose proof (B_range (crs t) (r + 2) BOK) as HB2.
    pose proof (B_range (crs t) (r + 3) BOK) as HB3. pose proof (B_range (crs t) (r + 4) BOK) as HB4. pose proof (B_range (crs t) (r + 5) BOK) as HB5.
    pose proof (B_range (crs t) (r + 6) BOK) as HB6. pose proof (B_range (crs t) (r + 7) BOK) as HB7.
    s2_env OK. unfold RSL in HM.
    s2_open_mem HM.
    ngrun.
    if_cases K0; zify_cond K0.
    - pose proof (V8_range _ _ _ _ _ _ _ _ HB0 HB1 HB2 HB3 HB4 HB5 HB6 HB7) as HVR.
      pose proof (V8_low _ _ _ _ _ _ _ _ HB0 HB1 HB2 HB3 HB4 HB5 HB6 HB7) as HVL.
      eapply (KD d); [lia | lia | exact HVR | rewrite HVL; f_equal; lia | n_close ..].
    - pose proof (swar4_last _ _ _ _ _ _ _ _ HB0 HB1 HB2 HB3 HB4 HB5 HB6 HB7 K0) as HL.
      assert (HNZ : (r + 3 < rl)%Z) by (apply Bc_lt; lia).
      pose proof (B_range (crs t) (p + (d + 4)) BOK) as HB4'.

      ngrun_cut_f ltac:(fun pc => lazymatch pc with 0x44e04%Z => fail | _ => idtac end)
                  ltac:(fun n => lazymatch n with 5%Z => fail | 13%Z => fail | 14%Z => fail | 16%Z => fail | 9%Z => fail | 26%Z => fail | _ => idtac end).
      eapply (KD (d + 4)%Z (B (crs t) (p + (d + 4)))); [lia | lia | lia | apply Z.mod_small; lia | n_close ..].
  Qed.

End NumR2.
