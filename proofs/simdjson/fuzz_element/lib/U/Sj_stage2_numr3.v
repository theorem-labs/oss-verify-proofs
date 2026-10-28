(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Lib Require Import Tac Arr Bytes StoreFast FP.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Sj Require Import SjS1Out SjStage2 SjLeaves SjTape SjTapeInv SjTapeList SjExpDigits.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.U Require Import Sj_stage2_defs Sj_stage2_tapek Sj_tables Sj_stage2_traps Sj_stage2_guard
  Sj_stage2_numkit Sj_stage2_numkit2 Sj_stage2_numkitr Sj_stage2_numkit3 Sj_stage2_numr_defs Sj_stage2_numr_loops.
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

Section NumR3.
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

  Lemma seg_numr_exp : forall (Q : machine_state -> Prop) neg p e0 x,
    (0 <= p <= rl)%Z -> (0 <= x < 2^64)%Z -> (x mod 256 = B (crs t) p)%Z ->
    (forall x', (0 <= x' < 2^64)%Z -> numr_flt_k E CP t Q neg x') -> numr_int_k E CP t Q p ->
    (forall q0, (0 <= q0 <= rl)%Z -> numr_e48_k E CP t Q neg q0 e0) ->
    numr_scan_k E CP t Q neg p e0 x.
  Proof using OK TOK CP0 CPHI CPSEP.
    intros Q neg p e0 x HP HX HXB KF KI KE. unfold numr_scan_k. intros until m1. intros HM CPRO.
    pose proof (crs_bytes_ok t TOK) as BOK. pose proof (crs_blen t) as CBL0. pose proof CBL0 as CBL. rewrite zbytes_length in CBL.
    pose proof (B_range (crs t) p BOK) as HB0.
    pose proof (B_range (crs t) (p + 1) BOK) as HB1. pose proof (B_range (crs t) (p + 2) BOK) as HB2.
    s2_env OK. unfold RSL in HM.
    s2_open_mem HM.
    ngrun.
    if_cases K0; zify_cond K0.
    -
      ngrun.
      if_cases K1.
      + eapply (KF _ HX); n_close.
      + eapply KI; n_close.
    - assert (HNZ : (p < rl)%Z).
      { pose proof (low_e_nz x _ HXB K0) as N0.
        apply Bc_lt; [exact N0 | | lia].
        intro E32. rewrite E32 in HXB. clear - HXB K0.
        rewrite Z.land_lor_distr_l in K0. change (Z.land 32 255) with 32%Z in K0.
        change 255%Z with (Z.ones 8) in K0. rewrite Z.land_ones in K0 by lia. change (2 ^ 8)%Z with 256%Z in K0. rewrite HXB in K0. discriminate K0. }
      ngrun.
      if_cases K2; zify_cond K2.
      +
        assert (HNZ1 : (p + 1 < rl)%Z) by (apply Bc_lt; lia).
        ngrun_to 0x44eb4%Z.
        replace (CP + p + 2)%Z with (CP + (p + 2))%Z by lia.
        eapply (KE (p + 2)%Z); [lia | n_close ..].
      + ngrun.
        if_cases K3; zify_cond K3.
        *
          ngrun_to 0x44eb4%Z.
          replace (CP + p + 1)%Z with (CP + (p + 1))%Z by lia.
          eapply (KE (p + 1)%Z); [lia | n_close ..].
        *
          assert (HNZ1 : (p + 1 < rl)%Z) by (apply Bc_lt; lia).
          ngrun_to 0x44eb4%Z.
          replace (CP + p + 2)%Z with (CP + (p + 2))%Z by lia.
          eapply (KE (p + 2)%Z); [lia | n_close ..].
  Qed.

  Lemma seg_numr_eadd : forall (Q : machine_state -> Prop) neg w e0 x,
    (-1000000000000000000 < w < 1000000000000000000)%Z -> (-2097152 <= e0 <= 0)%Z -> (0 <= x < 2^64)%Z ->
    (forall x', (0 <= x' < 2^64)%Z -> numr_flt_k E CP t Q neg x') ->
    numr_eadd_k E CP t Q neg w e0 x.
  Proof using OK TOK CP0 CPHI CPSEP.
    intros Q neg w e0 x HW HE0 HX KF. unfold numr_eadd_k. intros until m1. intros HM CPRO.
    s2_env OK. unfold RSL in HM.
    s2_open_mem HM.
    destruct (Z_lt_dec w 0) as [WN|WP].
    - zstep. zstep. zstep. g_bias. ngrun_to 0x45020%Z. eapply (KF _ HX); n_close.
    - zstep. zstep. zstep. g_bias. ngrun_to 0x45020%Z. eapply (KF _ HX); n_close.
  Qed.

  Lemma seg_numr_eneg : forall (Q : machine_state -> Prop) neg v e0 x,
    (0 <= v < 1000000000000000000)%Z -> (-2097152 <= e0 <= 0)%Z -> (0 <= x < 2^64)%Z ->
    (forall w, (-1000000000000000000 < w < 1000000000000000000)%Z -> numr_eadd_k E CP t Q neg w e0 x) ->
    numr_eneg_k E CP t Q neg v e0 x.
  Proof using OK TOK CP0 CPHI CPSEP.
    intros Q neg v e0 x HV HE0 HX KA. unfold numr_eneg_k. intros until m1. intros HM CPRO.
    s2_env OK. unfold RSL in HM.
    s2_open_mem HM.
    destruct (Z.eq_dec v 0) as [V0|VN].
    - zstep. zstep. zstep. g_bias. ngrun_to 0x45008%Z. eapply (KA (0 - v)%Z); [lia | n_close ..].
    - zstep. zstep. zstep. g_bias. ngrun_to 0x45008%Z. eapply (KA (0 - v)%Z); [lia | n_close ..].
  Qed.

  Lemma seg_numr_e14 : forall (Q : machine_state -> Prop) neg v e0 x,
    (0 <= v < 10 ^ 18)%Z -> (-2097152 <= e0 <= 0)%Z -> (0 <= x < 2^64)%Z ->
    numr_eneg_k E CP t Q neg v e0 x -> numr_eadd_k E CP t Q neg v e0 x ->
    numr_e14_k E CP t Q neg v e0 x.
  Proof using OK TOK CP0 CPHI CPSEP.
    intros Q neg v e0 x HV HE0 HX KN KA. unfold numr_e14_k. intros until m1. intros HM CPRO.
    s2_env OK. unfold RSL in HM.
    s2_open_mem HM.
    ngrun.
    if_cases K0.
    - eapply KA; n_close.
    - eapply KN; n_close.
  Qed.

  Lemma seg_numr_e48 : forall (Q : machine_state -> Prop) neg q0 e0,
    (0 <= q0 <= rl)%Z -> rdel_errA_k E CP Q ->
    (forall v x, (0 <= v < 10 ^ 18)%Z -> (0 <= x < 2^64)%Z -> numr_e14_k E CP t Q neg v e0 x) ->
    (forall v x, (0 <= v < 10 ^ 18)%Z -> (0 <= x < 2^64)%Z -> numr_eneg_k E CP t Q neg v e0 x) ->
    (forall v x, (0 <= v < 10 ^ 18)%Z -> (0 <= x < 2^64)%Z -> numr_eadd_k E CP t Q neg v e0 x) ->
    numr_e48_k E CP t Q neg q0 e0.
  Proof using OK TOK CP0 CPHI CPSEP.
    intros Q neg q0 e0 HQ0 KX KE KN KA. unfold numr_e48_k. intros until m1. intros HM CPRO.
    pose proof (crs_bytes_ok t TOK) as BOK. pose proof (crs_blen t) as CBL0. pose proof CBL0 as CBL. rewrite zbytes_length in CBL.
    pose proof (B_range (crs t) q0 BOK) as HB0.
    s2_env OK. unfold RSL in HM.
    s2_open_mem HM.
    ngrun.
    if_cases K0; zify_cond K0.
    -
      ngrun. if_false. n_exit KX.
    - assert (HNZ : (q0 < rl)%Z) by (apply Bc_lt; lia).
      assert (HD1 : digits (crs t) q0 (0 + 1)) by (intros i Hi; replace (q0 + i)%Z with q0 by lia; lia).
      ngrun_to 0x44ed8%Z.
      replace (B (crs t) q0) with (B (crs t) (q0 + 0)) by (f_equal; lia).
      eapply (numr_L4 E OK Q CP t TOK CP0 CPHI (S (Z.to_nat rl)) q0 0%Z); [exact CPRO | lia | lia | lia | lia | exact HD1 |].
      intros c' yt6 yt3 HC' HQ' HD' HND.
      pose proof (B_range (crs t) (q0 + c') BOK) as HBC.
      ngrun.
      if_cases KT3; zify_cond KT3; [|exfalso; lia].
      ngrun.
      if_cases K19; zify_cond K19.
      +
        pose proof (dval_bound (crs t) q0 c' ltac:(lia) HD') as HDB.
        assert (HP18 : (10 ^ c' <= 10 ^ 18)%Z) by (apply Z.pow_le_mono_r; lia).
        eapply (KE (dval (crs t) q0 c') (B (crs t) (q0 + c'))); [lia | lia | n_close ..].
      +
        ngrun.
        if_cases KZ; zify_cond KZ.
        *
          ngrun.
          if_cases KB; zify_cond KB; [exfalso; lia|].
          ngrun.
          if_cases KS.
          -- ngrun_to 0x45008%Z. eapply (KA 999999999999999999%Z (B (crs t) (q0 + c'))); [lia | lia | n_close ..].
          -- ngrun_to 0x44ff4%Z. eapply (KN 999999999999999999%Z (B (crs t) (q0 + c'))); [lia | lia | n_close ..].
        *
          ngrun_to 0x47490%Z.
          eapply (numr_L5 E OK Q CP t TOK CP0 CPHI (S (Z.to_nat rl)) q0); [exact CPRO | lia | lia |].
          intros q' yt6' HQ'' HZ.
          ngrun.
          if_cases KB; zify_cond KB.
          --
             assert (HQC : (q' <= q0 + c')%Z).
             { destruct (Z_le_dec q' (q0 + c')) as [L|G]; [exact L|]. exfalso. apply HND. rewrite (HZ (q0 + c')%Z) by lia. lia. }
             assert (HZS : zeros (crs t) q0 (q' - q0)).
             { intros i Hi. destruct (Z.eq_dec i 0) as [->|NE]; [replace (q0 + 0)%Z with q0 by lia; lia| apply HZ; lia]. }
             pose proof (dval_lt18 (crs t) q0 c' (q' - q0) ltac:(lia) ltac:(lia) HD' HZS) as HV18.
             ngrun.
             if_cases KS.
             ++ ngrun_to 0x45008%Z. eapply (KA (dval (crs t) q0 c') (B (crs t) (q0 + c'))); [exact HV18 | lia | n_close ..].
             ++ ngrun_to 0x44ff4%Z. eapply (KN (dval (crs t) q0 c') (B (crs t) (q0 + c'))); [exact HV18 | lia | n_close ..].
          -- ngrun.
             if_cases KS.
             ++ ngrun_to 0x45008%Z. eapply (KA 999999999999999999%Z (B (crs t) (q0 + c'))); [lia | lia | n_close ..].
             ++ ngrun_to 0x44ff4%Z. eapply (KN 999999999999999999%Z (B (crs t) (q0 + c'))); [lia | lia | n_close ..].
  Qed.
End NumR3.
