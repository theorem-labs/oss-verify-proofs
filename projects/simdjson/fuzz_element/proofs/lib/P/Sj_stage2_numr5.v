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
  Sj_stage2_numkit Sj_stage2_numkit2 Sj_stage2_numkit3 Sj_stage2_numr_defs Sj_stage2_numr_loops.
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

Section NumR5.
  Variable E : s2env.
  Hypothesis OK : env_ok E.
  Variables (CP : Z) (t : list Z).
  Hypothesis TOK : bytes_ok t.
  Hypothesis CP0 : (0 <= CP)%Z.
  Hypothesis CPHI : (CP + blen t + 64 <= e_lo E)%Z.
  Hypothesis CPSEP : cp_sep E CP t.
  Notation rl := (blen t).

  Ltac n_close := first [ unfold RSL; s2_close_mem0 | eassumption ].
  Local Ltac n_closed_branch a b ::= lazymatch a with 0x435d8%Z => if_false end.

  Lemma seg_numr_flt : forall (Q : machine_state -> Prop) neg c,
    (0 <= c < 256)%Z -> (0 <= neg <= 1)%Z -> (neg < rl)%Z ->
    numr_tail_k E CP t Q 0x42580 -> numr_tail_k E CP t Q 0x4353c ->
    numr_flt_k E CP t Q neg c.
  Proof using OK TOK CP0 CPHI CPSEP.
    intros Q neg c HC HNEG HS K6d4 K690. unfold numr_flt_k. intros until m1. intros HM CPRO.
    pose proof (crs_bytes_ok t TOK) as BOK. pose proof (crs_blen t) as CBL0. pose proof CBL0 as CBL. rewrite zbytes_length in CBL.
    s2_env OK. unfold RSL in HM.
    s2_open_mem HM.
    srun.
    if_cases K0.
    - eapply K6d4; n_close.
    - srun.
      if_cases K1.
      + srun_to 0x42560%Z.
        replace (CP + neg + 1)%Z with (CP + (neg + 1))%Z by lia.
        eapply (numr_L6 E Q CP t TOK CP0 (S (Z.to_nat rl))); [exact CPRO | lia | lia |].
        intros ya3 yt1 ya5. srun. if_cases K9; [eapply K690 | eapply K6d4]; n_close.
      + srun.
        if_cases K2.
        * srun_to 0x42560%Z.
          replace (CP + neg + 1)%Z with (CP + (neg + 1))%Z by lia.
          eapply (numr_L6 E Q CP t TOK CP0 (S (Z.to_nat rl))); [exact CPRO | lia | lia |].
          intros ya3 yt1 ya5. srun. if_cases K9; [eapply K690 | eapply K6d4]; n_close.
        * srun. if_cases K9; [eapply K690 | eapply K6d4]; n_close.
  Qed.

  Lemma seg_numr_wr : forall (Q : machine_state -> Prop),
    Z.of_nat (length (e_tws E)) = 1%Z -> rdel_err_k E CP Q -> (forall v r, num_word v -> rdel_flt0_k (gapp E [v; r] []) CP Q) -> rdel_flt9_k E CP Q ->
    numr_wr_k E CP t Q.
  Proof using OK TOK CP0 CPHI CPSEP.
    intros Q GLT KX KF0 KF9. unfold numr_wr_k. intros until m1. intros HS1V HM CPRO.
    pose proof (crs_blen t) as CBL0. pose proof (blen_nonneg (e_bs E)) as LEN0.
    s2_env OK. unfold RSL in HM.
    s2_open_mem HM.
    srun.
    if_cases K0; zify_cond K0.
    -
      srun_to 0x43890%Z.
      destruct (bv_unsigned xs3 <? 1)%Z.
      + change (Z.land ((Z.b2z true + -1) mod 18446744073709551616) 9) with 0%Z.
        s2_tape2. s2_kvr KF0; [s2_num_word | eapply MEMI_DSL; [s2_close_mem0 | reflexivity ..]].
      + change (Z.land ((Z.b2z false + -1) mod 18446744073709551616) 9) with 9%Z.
        eapply KF9; [ s2_errnz | eapply (MEMX_of_MEMI E (e_nxt0 E)); [s2_close_mem0 | reflexivity ..] ].
    -
      srun.
      if_cases K1; zify_cond K1.
      + eapply KF9; [ s2_fail09 HS1V | eapply (MEMX_of_MEMI E (e_nxt0 E)); [s2_close_mem0 | reflexivity ..] ].
      +
        srun. if_false. srun_to 0x41294%Z. s2_err_exit KX. eapply (MEMX_of_MEMI E (e_nxt0 E)); [s2_close_mem0 | reflexivity ..].
  Qed.

  Lemma seg_numr_wr0 : forall (Q : machine_state -> Prop),
    numr_wr_k E CP t Q -> numr_tail_k E CP t Q 0x435a0.
  Proof using OK.
    intros Q KW. unfold numr_tail_k. intros until m1. intros HM CPRO. zstep. eapply (KW 0%Z); [left; reflexivity | exact HM | exact CPRO].
  Qed.
End NumR5.
