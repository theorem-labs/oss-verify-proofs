(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.simdjson.fuzz_print_json.lib.Lib Require Import Tac Arr Bytes StoreFast FP.
From OssFuzzTheorems.Proofs.simdjson.fuzz_print_json.lib.Sj Require Import SjS1Out SjStage2 SjLeaves SjTape SjTapeInv SjTapeList SjExpDigits.
From OssFuzzTheorems.Proofs.simdjson.fuzz_print_json.lib.U Require Import Sj_stage2_defs Sj_stage2_tapek Sj_tables Sj_stage2_traps Sj_stage2_guard
  Sj_stage2_numkit Sj_stage2_numkit2 Sj_stage2_numkitr Sj_stage2_numkit3 Sj_stage2_numkit6 Sj_stage2_numr_defs Sj_stage2_numr_loops Sj_stage2_numr_kit.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac lia ::= r_lia.
Local Ltac tlia ::= r_tlia.
Local Ltac solve_load ::= first [ solve_load_base | s2_load_cp | s2_load_sown | solve_load_image ].
Local Ltac solve_store ::= first [ solve_store0 | s2_store_wr ].
Local Ltac s2_store_done_wr ::= s2_note_tape; s2_store_done_wr_v2.
Local Ltac ngstep ::= ngstep_l.

Local Ltac nnorm ::=
  s2norm;
  repeat match goal with
  | |- context [Z.land (Z.modulo ?x 18446744073709551616) 255] => rewrite (land255_mod x)
  | |- context [Z.land (B ?bs ?i) 255] => rewrite (land255_small (B bs i)) by lia
  | |- context [Z.land ?x 255] => rewrite (land255_any x)
  end.

Section NumR5.
  Variable E : s2env.
  Hypothesis OK : env_ok E.
  Variables (CP : Z) (t : list Z).
  Hypothesis TOK : bytes_ok t.
  Hypothesis CP0 : (0 < CP)%Z.
  Hypothesis CPHI : (CP + blen t + 64 <= e_lo E)%Z.
  Hypothesis CPSEP : cp_sep E CP t.
  Notation rl := (blen t).

  Ltac n_close := first [ unfold RSL; s2_close_mem0 | eapply MEMI_RSL; [s2_close_mem0 | reflexivity ..] | eassumption ].
  Local Ltac n_closed_branch a b ::= lazymatch a with 0x474bc%Z => if_false | 0x46df8%Z => first [if_true | if_false] | 0x46e08%Z => first [if_true | if_false] end.

  Lemma seg_numr_flt : forall (Q : machine_state -> Prop) neg x,
    (0 <= x < 2^64)%Z -> (0 <= neg <= 1)%Z -> (neg < rl)%Z ->
    numr_tail_k E CP t Q 0x44ecc -> numr_tail_k E CP t Q 0x4731c ->
    numr_flt_k E CP t Q neg x.
  Proof using OK TOK CP0 CPHI CPSEP.
    intros Q neg x HX HNEG HS K33c K78c. unfold numr_flt_k. intros until m1. intros HM CPRO.
    pose proof (crs_bytes_ok t TOK) as BOK. pose proof (crs_blen t) as CBL0. pose proof CBL0 as CBL. rewrite zbytes_length in CBL.
    pose proof (B_range (crs t) neg BOK) as HB0.
    assert (HXM : (0 <= x mod 256 < 256)%Z) by (apply Z.mod_pos_bound; lia).
    s2_env OK. unfold RSL in HM.
    s2_open_mem HM.
    ngrun.
    if_cases K0.
    - eapply K33c; n_close.
    - ngrun.
      if_cases K1; zify_cond K1.
      +
        ngrun.
        if_cases K2; zify_cond K2.
        * ngrun_to 0x44ea4%Z.
          eapply (numr_L6 E OK Q CP t TOK CP0 CPHI (S (Z.to_nat rl)) neg); [exact CPRO | lia | lia |].
          intros ya3 yt1 yt0. ngrun. if_cases K9; [eapply K33c | ngrun_to 0x4731c%Z; eapply K78c]; n_close.
        * ngrun. if_cases K9; [eapply K33c | ngrun_to 0x4731c%Z; eapply K78c]; n_close.
      + ngrun_to 0x44ea4%Z.
        eapply (numr_L6 E OK Q CP t TOK CP0 CPHI (S (Z.to_nat rl)) neg); [exact CPRO | lia | lia |].
        intros ya3 yt1 yt0. ngrun. if_cases K9; [eapply K33c | ngrun_to 0x4731c%Z; eapply K78c]; n_close.
  Qed.

  Lemma seg_numr_wr : forall (Q : machine_state -> Prop),
    Z.of_nat (length (e_tws E)) = 1%Z -> rdel_errA_k E CP Q -> rdel_errB_k E CP Q -> (forall v r, num_word v -> rdel_fin0_k (gapp E [v; r] []) CP Q) -> rdel_fin9_k E CP Q ->
    numr_tail_k E CP t Q 0x46d6c.
  Proof using OK TOK CP0 CPHI CPSEP.
    intros Q GLT KXA KXB KF0 KF9. unfold numr_tail_k. intros until m1. intros HM CPRO.
    pose proof (crs_blen t) as CBL0. pose proof (blen_nonneg (e_bs E)) as LEN0.
    s2_env OK. unfold RSL in HM.
    s2_open_mem HM.
    ngexp r_cuts ltac:(idtac; r_leaf KXA KXB KF0 KF9).
  Qed.
End NumR5.
