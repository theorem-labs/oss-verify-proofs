(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.simdjson.fuzz_element.lib.Lib Require Import Tac Arr Bytes StoreFast FP.
From OSSVerify.Proofs.simdjson.fuzz_element.lib.Sj Require Import SjS1Out SjStage2 SjLeaves SjTape SjTapeInv SjTapeList.
From OSSVerify.Proofs.simdjson.fuzz_element.lib.P Require Import Sj_stage2_defs Sj_stage2_tapek Sj_tables Sj_stage2_auto Sj_stage2_auto2
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

Section NumR2.
  Variable E : s2env.
  Hypothesis OK : env_ok E.
  Variables (CP : Z) (t : list Z).
  Hypothesis TOK : bytes_ok t.
  Hypothesis CP0 : (0 <= CP)%Z.
  Hypothesis CPHI : (CP + blen t + 64 <= e_lo E)%Z.
  Hypothesis CPSEP : cp_sep E CP t.
  Notation rl := (blen t).

  Ltac n_exit KX := srun_to 0x41294%Z; s2_err_exit KX; eapply (MEMX_of_MEMI E (e_nxt0 E)); [s2_close_mem0 | reflexivity ..].
  Ltac n_scan KS pp := eapply (KS pp); [lia | eapply MEMI_RSL; [s2_close_mem0 | reflexivity ..] | eassumption].

  Lemma seg_numr_fdig : forall (Q : machine_state -> Prop) neg p d,
    (0 <= p)%Z -> (1 <= d)%Z -> (p + d <= rl)%Z -> rdel_err_k E CP Q ->
    (forall p', (p < p' <= rl)%Z -> numr_scan_k E CP t Q neg p') ->
    numr_fdig_k E CP t Q neg p d.
  Proof using OK TOK CP0 CPHI CPSEP.
    intros Q neg p d HP HD HPD KX KS. unfold numr_fdig_k. intros until m1. intros HM CPRO.
    pose proof (crs_bytes_ok t TOK) as BOK. pose proof (crs_blen t) as CBL0. pose proof CBL0 as CBL. rewrite zbytes_length in CBL.
    pose proof (B_range (crs t) (p + d) BOK) as HB0.
    s2_env OK. unfold RFSL in HM.
    s2_open_mem HM.
    srun.
    if_cases K0; zify_cond K0.
    -
      srun.
      if_cases K1; zify_cond K1.
      + n_exit KX.
      + srun_to 0x41eb0%Z.
        replace (CP + p + d)%Z with (CP + (p + d))%Z by lia.
        n_scan KS (p + d)%Z.
    - assert (HNZ : (p + d < rl)%Z) by (apply Bc_lt; lia).
      srun_to 0x41e70%Z.
      replace (CP + p + d)%Z with (CP + (p + d))%Z by lia.
      eapply (numr_L3 E Q CP t TOK CP0 (S (Z.to_nat rl))); [exact CPRO | lia | lia |].
      intros q' ya2 ya0 yt0 ya1 HQ'.
      srun_to 0x41eb0%Z.
      n_scan KS q'.
  Qed.

  Lemma seg_numr_ftail : forall (Q : machine_state -> Prop) neg p d r,
    (0 <= p)%Z -> (1 <= d)%Z -> (r = p + d)%Z -> (r <= rl)%Z ->
    (forall d', (d <= d')%Z -> (p + d' <= rl)%Z -> numr_fdig_k E CP t Q neg p d') ->
    numr_ftail_k E CP t Q neg p d r.
  Proof using OK TOK CP0 CPHI CPSEP.
    intros Q neg p d r HP HD HR HPD KD. unfold numr_ftail_k. intros until m1. intros HM CPRO.
    pose proof (crs_bytes_ok t TOK) as BOK. pose proof (crs_blen t) as CBL0. pose proof CBL0 as CBL. rewrite zbytes_length in CBL.
    pose proof (B_range (crs t) r BOK) as HB0. pose proof (B_range (crs t) (r + 1) BOK) as HB1. pose proof (B_range (crs t) (r + 2) BOK) as HB2.
    pose proof (B_range (crs t) (r + 3) BOK) as HB3. pose proof (B_range (crs t) (r + 4) BOK) as HB4. pose proof (B_range (crs t) (r + 5) BOK) as HB5.
    pose proof (B_range (crs t) (r + 6) BOK) as HB6. pose proof (B_range (crs t) (r + 7) BOK) as HB7.
    s2_env OK. unfold RFSL in HM.
    s2_open_mem HM.
    srun.
    if_cases K0; zify_cond K0.
    - eapply (KD d); [lia | lia | unfold RFSL; s2_close_mem0 | exact CPRO].
    - pose proof (swar4_last _ _ _ _ _ _ _ _ HB0 HB1 HB2 HB3 HB4 HB5 HB6 HB7 K0) as HL.
      assert (HNZ : (r + 3 < rl)%Z) by (apply Bc_lt; lia).
      srun_to 0x41e48%Z.
      eapply (KD (d + 4)%Z); [lia | lia | unfold RFSL; s2_close_mem0 | exact CPRO].
  Qed.

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
    srun_to 0x41520%Z. fold_V8.
    srun.
    if_cases K0; zify_cond K0.
    -
      srun_to 0x41ddc%Z.
      replace (p + 2)%Z with (p + 1 + 1)%Z by lia. replace (p + 3)%Z with (p + 1 + 2)%Z by lia. replace (p + 4)%Z with (p + 1 + 3)%Z by lia.
      replace (p + 5)%Z with (p + 1 + 4)%Z by lia. replace (p + 6)%Z with (p + 1 + 5)%Z by lia. replace (p + 7)%Z with (p + 1 + 6)%Z by lia.
      replace (p + 8)%Z with (p + 1 + 7)%Z by lia.
      eapply (KT 1%Z (p + 1)%Z); [lia | lia | lia | unfold RFSL; s2_close_mem0 | eassumption].
    -
      pose proof (V8_range _ _ _ _ _ _ _ _ HB1 HB2 HB3 HB4 HB5 HB6 HB7 HB8) as HVR. rewrite ?(Z.mod_small _ _ HVR) in K0.
      pose proof (swar8_last _ _ _ _ _ _ _ _ HB1 HB2 HB3 HB4 HB5 HB6 HB7 HB8 K0) as HL.
      assert (HNZ : (p + 8 < rl)%Z) by (apply Bc_lt; lia).
      srun_to 0x4158c%Z.
      replace (CP + p + 9)%Z with (CP + (p + 9))%Z by lia.
      replace (Z_to_bv 64 1) with (Z_to_bv 64 (p + 9 - p - 8)) by (f_equal; lia).
      lazymatch goal with CPRO' : bytes_at psegs _ CP (zbytes (crs t)) |- _ =>
        eapply (numr_L2 E Q CP t TOK CP0 (S (Z.to_nat rl)) p (p + 9)%Z); [exact CPRO' | lia | lia |] end.
      intros q' ys9 ys10 ys11 yra ya0 ya1 ya2 yt6 HQ'.
      srun_to 0x41ddc%Z.
      eapply (KT (q' - p)%Z q'); [lia | lia | lia | unfold RFSL; s2_close_mem0 | eassumption].
  Qed.
End NumR2.
