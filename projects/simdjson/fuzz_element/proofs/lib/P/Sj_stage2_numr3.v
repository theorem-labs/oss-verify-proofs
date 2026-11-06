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

Section NumR3.
  Variable E : s2env.
  Hypothesis OK : env_ok E.
  Variables (CP : Z) (t : list Z).
  Hypothesis TOK : bytes_ok t.
  Hypothesis CP0 : (0 <= CP)%Z.
  Hypothesis CPHI : (CP + blen t + 64 <= e_lo E)%Z.
  Hypothesis CPSEP : cp_sep E CP t.
  Notation rl := (blen t).

  Ltac n_exit KX := srun_to 0x41294%Z; s2_err_exit KX; eapply (MEMX_of_MEMI E (e_nxt0 E)); [s2_close_mem0 | reflexivity ..].
  Ltac n_close := first [ unfold RSL; s2_close_mem0 | eassumption ].

  Lemma seg_numr_e78 : forall (Q : machine_state -> Prop) neg c,
    numr_flt_k E CP t Q neg c -> numr_e78_k E CP t Q neg c.
  Proof using OK TOK CP0 CPHI CPSEP.
    intros Q neg c KF. unfold numr_e78_k. intros until m1. intros HM CPRO.
    s2_env OK. unfold RSL in HM.
    s2_open_mem HM.
    srun.
    if_cases K0.
    - srun_to 0x42534%Z. eapply KF; n_close.
    - srun_to 0x42534%Z. eapply KF; n_close.
  Qed.

  Lemma seg_numr_e48 : forall (Q : machine_state -> Prop) neg q0,
    (0 <= q0 <= rl)%Z -> rdel_err_k E CP Q ->
    (forall c, (0 <= c < 256)%Z -> numr_e78_k E CP t Q neg c) ->
    numr_e48_k E CP t Q neg q0.
  Proof using OK TOK CP0 CPHI CPSEP.
    intros Q neg q0 HQ0 KX KE. unfold numr_e48_k. intros until m1. intros HM CPRO.
    pose proof (crs_bytes_ok t TOK) as BOK. pose proof (crs_blen t) as CBL0. pose proof CBL0 as CBL. rewrite zbytes_length in CBL.
    pose proof (B_range (crs t) q0 BOK) as HB0.
    s2_env OK. unfold RSL in HM.
    s2_open_mem HM.
    srun.
    if_cases K0; zify_cond K0.
    - assert (HNZ : (q0 < rl)%Z) by (apply Bc_lt; lia).
      srun_to 0x424f4%Z.
      eapply (numr_L4 E Q CP t TOK CP0 (S (Z.to_nat rl)) q0 0%Z); [exact CPRO | lia | lia | lia | lia |].
      intros c' ya0 ya4 ya7 HC' HQ'.
      pose proof (B_range (crs t) (q0 + c') BOK) as HBC.
      srun.
      if_cases K1.
      +
        srun_to 0x434f8%Z.
        eapply (numr_L5 E Q CP t TOK CP0 (S (Z.to_nat rl)) q0); [exact CPRO | lia | lia |].
        intros ya0' ya6'.
        srun.
        if_cases K2.
        * eapply (KE _ HBC); n_close.
        * srun_to 0x42524%Z. eapply (KE _ HBC); n_close.
      + eapply (KE _ HBC); n_close.
    - n_exit KX.
  Qed.

  Lemma seg_numr_exp : forall (Q : machine_state -> Prop) neg p,
    (0 <= p <= rl)%Z ->
    (forall c, (0 <= c < 256)%Z -> numr_flt_k E CP t Q neg c) -> numr_int_k E CP t Q p ->
    (forall q0, (0 <= q0 <= rl)%Z -> numr_e48_k E CP t Q neg q0) ->
    numr_scan_k E CP t Q neg p.
  Proof using OK TOK CP0 CPHI CPSEP.
    intros Q neg p HP KF KI KE. unfold numr_scan_k. intros until m1. intros HM CPRO.
    pose proof (crs_bytes_ok t TOK) as BOK. pose proof (crs_blen t) as CBL0. pose proof CBL0 as CBL. rewrite zbytes_length in CBL.
    pose proof (B_range (crs t) p BOK) as HB0.
    pose proof (B_range (crs t) (p + 1) BOK) as HB1. pose proof (B_range (crs t) (p + 2) BOK) as HB2.
    s2_env OK. unfold RSL in HM.
    s2_open_mem HM.
    srun.
    if_cases K0; zify_cond K0.
    -
      srun.
      if_cases K1.
      + eapply (KF _ HB0); n_close.
      + eapply KI; n_close.
    - assert (HNZ : (p < rl)%Z).
      { apply Bc_lt; [ intro E0; rewrite E0 in K0; vm_compute in K0; discriminate K0
                     | intro E0; rewrite E0 in K0; vm_compute in K0; discriminate K0 | lia ]. }
      srun.
      if_cases K2; zify_cond K2.
      +
        assert (HNZ1 : (p + 1 < rl)%Z) by (apply Bc_lt; lia).
        srun_to 0x424d4%Z.
        replace (CP + p + 2)%Z with (CP + (p + 2))%Z by lia.
        eapply (KE (p + 2)%Z); [lia | n_close ..].
      + srun.
        if_cases K3; zify_cond K3.
        *
          srun_to 0x424d4%Z.
          replace (CP + p + 1)%Z with (CP + (p + 1))%Z by lia.
          eapply (KE (p + 1)%Z); [lia | n_close ..].
        *
          assert (HNZ1 : (p + 1 < rl)%Z) by (apply Bc_lt; lia).
          srun_to 0x424d4%Z.
          replace (CP + p + 2)%Z with (CP + (p + 2))%Z by lia.
          eapply (KE (p + 2)%Z); [lia | n_close ..].
  Qed.
End NumR3.
