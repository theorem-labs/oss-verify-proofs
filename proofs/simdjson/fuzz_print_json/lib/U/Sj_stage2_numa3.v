(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.simdjson.fuzz_print_json.lib.Lib Require Import Tac Arr Bytes StoreFast FP.
From OssFuzzTheorems.Proofs.simdjson.fuzz_print_json.lib.Sj Require Import SjS1Out SjStage2 SjLeaves SjTape SjTapeInv SjTapeList SjExpDigits.
From OssFuzzTheorems.Proofs.simdjson.fuzz_print_json.lib.U Require Import Sj_stage2_defs Sj_stage2_tapek Sj_tables Sj_stage2_traps Sj_stage2_guard
  Sj_stage2_numkit Sj_stage2_numkit2 Sj_stage2_numkit3 Sj_stage2_numa_defs Sj_stage2_numa_defs2 Sj_stage2_numa_loops.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac lia ::= s2lia.
Local Ltac tlia ::= s2tlia.
Local Ltac solve_load ::= first [ solve_load_base | s2_load_buf | solve_load_image ].
Local Ltac solve_store ::= first [ solve_store0 | s2_store_wr ].
Local Ltac s2_store_done_wr ::= s2_store_done_wr_v2.

Section NumA3.
  Variable E : s2env.
  Hypothesis OK : env_ok E.
  Notation bs := (e_bs E).
  Notation o s := (e_off E (k s)).

  Ltac n_exit KX := ngrun_to 0x4be14%Z; eapply KX; [s2_errok_code | s2_close_memx].
  Ltac n_close := unfold NSL; s2_close_mem0.

  Lemma seg_numa_exp : forall (Q : machine_state -> Prop) (s : st) neg p e0 x,
    (0 <= p <= e_len E)%Z -> (0 <= x < 2^64)%Z -> (x mod 256 = B bs p)%Z ->
    (forall x', (0 <= x' < 2^64)%Z -> numa_flt_k E Q s neg x') -> numa_int_k E Q s neg p ->
    (forall q0, (0 <= q0 <= e_len E)%Z -> numa_e48_k E Q s neg q0 e0) ->
    numa_scan_k E Q s neg p e0 x.
  Proof using OK.
    intros Q s neg p e0 x HP HX HXB KF KI KE. unfold numa_scan_k. intros until m1. intros HM.
    pose proof (ok_bytes _ OK) as BOK. pose proof (B_range bs p BOK) as HB0.
    pose proof (B_range bs (p + 1) BOK) as HB1. pose proof (B_range bs (p + 2) BOK) as HB2.
    s2_env OK. unfold NSL in HM.
    s2_open_mem HM.
    ngrun.
    if_cases K0; zify_cond K0.
    -
      ngrun.
      if_cases K1.
      + eapply KI. n_close.
      + eapply (KF _ HX). n_close.
    - assert (HNZ : (p < e_len E)%Z) by (apply B_nz_lt; exact (low_e_nz x _ HXB K0)).
      ngrun.
      if_cases K2; zify_cond K2.
      +
        assert (HNZ1 : (p + 1 < e_len E)%Z) by (apply B_nz_lt; lia).
        ngrun_to 0x48524%Z.
        replace (e_BUF E + p + 2)%Z with (e_BUF E + (p + 2))%Z by lia.
        eapply (KE (p + 2)%Z); [lia | n_close].
      + ngrun.
        if_cases K3; zify_cond K3.
        *
          ngrun_to 0x48524%Z.
          replace (e_BUF E + p + 1)%Z with (e_BUF E + (p + 1))%Z by lia.
          eapply (KE (p + 1)%Z); [lia | n_close].
        *
          assert (HNZ1 : (p + 1 < e_len E)%Z) by (apply B_nz_lt; lia).
          ngrun_to 0x48524%Z.
          replace (e_BUF E + p + 2)%Z with (e_BUF E + (p + 2))%Z by lia.
          eapply (KE (p + 2)%Z); [lia | n_close].
  Qed.

  Lemma seg_numa_e14 : forall (Q : machine_state -> Prop) (s : st) neg v e0 x,
    (0 <= v < 10 ^ 18)%Z -> (-2097152 <= e0 <= 0)%Z -> (0 <= x < 2^64)%Z ->
    (forall x', (0 <= x' < 2^64)%Z -> numa_flt_k E Q s neg x') ->
    numa_e14_k E Q s neg v e0 x.
  Proof using OK.
    intros Q s neg v e0 x HV HE0 HX KF. unfold numa_e14_k. intros until m1. intros HM.
    change (10 ^ 18)%Z with 1000000000000000000%Z in HV.
    s2_env OK. unfold NSL in HM.
    s2_open_mem HM.
    ngrun.
    if_cases K0.
    -
      zstep. zstep. zstep. g_bias. ngrun_to 0x485ec%Z.
      eapply (KF _ HX). n_close.
    -
      destruct (Z.eq_dec v 0) as [V0|VN].
      + zstep. zstep. zstep. g_bias. ngrun_to 0x485c4%Z. zstep. zstep. zstep. g_bias. ngrun_to 0x485ec%Z.
        eapply (KF _ HX). n_close.
      + zstep. zstep. zstep. g_bias. ngrun_to 0x485c4%Z. zstep. zstep. zstep. g_bias. ngrun_to 0x485ec%Z.
        eapply (KF _ HX). n_close.
  Qed.

  Lemma seg_numa_e48 : forall (Q : machine_state -> Prop) (s : st) neg q0 e0,
    (0 <= q0 <= e_len E)%Z -> exit_k E Q ->
    (forall v x, (0 <= v < 10 ^ 18)%Z -> (0 <= x < 2^64)%Z -> numa_e14_k E Q s neg v e0 x) ->
    numa_e48_k E Q s neg q0 e0.
  Proof using OK.
    intros Q s neg q0 e0 HQ0 KX KE. unfold numa_e48_k. intros until m1. intros HM.
    pose proof (ok_bytes _ OK) as BOK. pose proof (B_range bs q0 BOK) as HB0.
    s2_env OK. unfold NSL in HM.
    s2_open_mem HM.
    ngrun.
    if_cases K0; zify_cond K0.
    -
      ngrun. if_false. n_exit KX.
    - assert (HNZ : (q0 < e_len E)%Z) by (apply B_nz_lt; lia).
      assert (HD1 : digits bs q0 (0 + 1)) by (intros i Hi; replace (q0 + i)%Z with q0 by lia; lia).
      ngrun_to 0x48554%Z.
      replace (B bs q0) with (B bs (q0 + 0)) by (f_equal; lia).
      eapply (numa_L4 E OK Q (S (Z.to_nat (e_len E))) q0 0%Z); [exact BUFRO | lia | lia | lia | lia | exact HD1 |].
      intros c' ys0 yt5 HC' HQ' HD' HND.
      pose proof (B_range bs (q0 + c') BOK) as HBC.
      ngrun.
      if_cases KT3; zify_cond KT3; [|exfalso; lia].
      ngrun.
      if_cases K19; zify_cond K19.
      +
        ngrun.
        if_cases KZ; zify_cond KZ.
        *
          ngrun.
          if_cases KB; zify_cond KB; [exfalso; lia|].
          ngrun_to 0x485a4%Z.
          eapply (KE 999999999999999999%Z (B bs (q0 + c'))); [lia | lia | n_close].
        *
          ngrun_to 0x48ae4%Z.
          eapply (numa_L5 E OK Q (S (Z.to_nat (e_len E))) q0); [exact BUFRO | lia | lia |].
          intros q' yt6 HQ'' HZ.
          ngrun.
          if_cases KB; zify_cond KB.
          --
             assert (HQC : (q' <= q0 + c')%Z).
             { destruct (Z_le_dec q' (q0 + c')) as [L|G]; [exact L|]. exfalso. apply HND. rewrite (HZ (q0 + c')%Z) by lia. lia. }
             assert (HZS : zeros bs q0 (q' - q0)).
             { intros i Hi. destruct (Z.eq_dec i 0) as [->|NE]; [replace (q0 + 0)%Z with q0 by lia; lia| apply HZ; lia]. }
             eapply (KE (dval bs q0 c') (B bs (q0 + c'))); [eapply (dval_lt18 bs q0 c' (q' - q0)); [lia | lia | exact HD' | exact HZS] | lia | n_close].
          -- ngrun_to 0x485a4%Z.
             eapply (KE 999999999999999999%Z (B bs (q0 + c'))); [lia | lia | n_close].
      +
        pose proof (dval_bound bs q0 c' ltac:(lia) HD') as HDB.
        assert (HP18 : (10 ^ c' <= 10 ^ 18)%Z) by (apply Z.pow_le_mono_r; lia).
        eapply (KE (dval bs q0 c') (B bs (q0 + c'))); [lia | lia | n_close].
  Qed.
End NumA3.
