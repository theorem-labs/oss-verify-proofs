(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump_raw_tape.lib.Lib Require Import Tac Arr Bytes StoreFast FP ImageA.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump_raw_tape.lib.Sj Require Import SjS1Out SjStage2 SjLeaves SjTape SjTapeInv SjTapeList SjExpDigits.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump_raw_tape.lib.B Require Import Sj_akit Sj_stage2_defs Sj_stage2_tapek Sj_stage2_traps Sj_stage2_guard Sj_tables Sj_stage2_hooks Sj_stage2_numkit Sj_stage2_numkit2
  Sj_stage2_numa_defs Sj_stage2_numa_defs2 Sj_stage2_numa_loops.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac lia ::= s2lia.
Local Ltac tlia ::= s2tlia.
Local Ltac solve_load ::= first [ solve_load_base | s2_load_shadow | s2_load_buf | s2_load_sown | solve_load_image ].
Local Ltac solve_store ::= first [ solve_store0 | s2_store_wr ].

Section NumA3.
  Variable E : s2env.
  Hypothesis OK : env_ok E.
  Hypothesis SHZ : a_shz E.
  Notation bs := (e_bs E).
  Notation LEN := (blen bs).
  Notation o s := (e_off E (k s)).

  Lemma seg_numa_scan : forall (Q : machine_state -> Prop) (s : st) neg p e0,
    (0 <= k s <= e_n E)%Z -> (0 <= neg <= 1)%Z -> (0 <= p <= LEN)%Z ->
    (forall q0, (p < q0 <= LEN)%Z -> numa_expd_k E Q s neg q0 e0) ->
    numa_flt_k E Q s neg p ->
    numa_int_k E Q s neg p ->
    numa_scan_k E Q s neg p e0.
  Proof using OK SHZ.
    intros Q s neg p e0 HK HNEG HP KE KF KI. unfold numa_scan_k. intros until m1. intros HM.
    pose proof (ok_bytes _ OK) as BOK. pose proof (off_bound E OK (k s) HK) as HO.
    pose proof (B_range bs p BOK) as HB0. pose proof (B_range bs (p + 1) BOK) as HB1. pose proof (B_range bs (p + 2) BOK) as HB2.
    s2_env OK.
    nopen HM.
    ngrun.
    if_cases K0; zify_cond K0.
    -
      ngrun.
      if_cases K1; first [ (kapply KI; nclose) | (kapply KF; nclose) ].
    - assert (HNZ : (p < LEN)%Z) by (nz_lt_by ltac:(intro EZ; rewrite EZ in K0; discriminate K0)).
      ngrun.
      if_cases K2; zify_cond K2.
      +
        assert (HNZ1 : (p + 1 < LEN)%Z) by (nz_lt_by ltac:(lia)).
        ngrun_to 0xc0e08%Z. kapply (KE (p + 2)%Z); [lia | nclose].
      + ngrun.
        if_cases K3; zify_cond K3.
        *
          kapply (KE (p + 1)%Z); [lia | nclose].
        *
          assert (HNZ1 : (p + 1 < LEN)%Z) by (nz_lt_by ltac:(lia)).
          ngrun_to 0xc0e08%Z. kapply (KE (p + 2)%Z); [lia | nclose].
  Qed.

  Ltac esign KN KA p' v :=
    ngrun;
    (let KSG := fresh "KSG" in if_cases KSG);
      first [ (kapply (KN p' v); [lia | lia | nclose])
            | (nstep; kapply (KN p' v); [lia | lia | nclose])
            | (ngrun_to 0xc1278%Z; kapply (KA p' v); [lia | lia | nclose]) ].

  Lemma seg_numa_expd : forall (Q : machine_state -> Prop) (s : st) neg q0 e0,
    (0 <= k s <= e_n E)%Z -> (0 <= neg <= 1)%Z -> (0 <= q0 <= LEN)%Z -> exit_k E Q ->
    (forall p' v, (q0 <= p' <= LEN)%Z -> (0 <= v < 10 ^ 18)%Z -> numa_eneg_k E Q s neg p' e0 v) ->
    (forall p' v, (q0 <= p' <= LEN)%Z -> (0 <= v < 10 ^ 18)%Z -> numa_eadd_k E Q s neg p' e0 v) ->
    numa_expd_k E Q s neg q0 e0.
  Proof using OK SHZ.
    intros Q s neg q0 e0 HK HNEG HQ0 KX KN KA. unfold numa_expd_k. intros until m1. intros HM.
    pose proof (ok_bytes _ OK) as BOK. pose proof (off_bound E OK (k s) HK) as HO.
    pose proof (B_range bs q0 BOK) as HBQ.
    change (10 ^ 18)%Z with 1000000000000000000%Z in *.
    s2_env OK.
    nopen HM.
    ngrun.
    if_cases K3; zify_cond K3.
    -
      ngrun. if_cases K4; zify_cond K4; try (exfalso; lia).
      nexit KX.
    - assert (HNZ : (q0 < LEN)%Z) by (nz_lt_by ltac:(lia)).
      assert (HD1 : digits bs q0 (0 + 1)) by (intros i Hi; replace (q0 + i)%Z with q0 by lia; lia).
      ngrun_to 0xc0e4c%Z.
      kapply (numa_L4 E OK SHZ Q (S (Z.to_nat (LEN))) q0 0%Z); [nclose | lia | lia | lia | lia | exact HD1 |].
      intros c'. intro_words. intros HC1 HC2 HD' HND.
      pose proof (B_range bs (q0 + c') BOK) as HBC.
      ngrun.
      if_cases K5; zify_cond K5; try (exfalso; lia).
      ngrun.

      if_cases K19; zify_cond K19;
        first [ (assert (H19 : (19 <= c')%Z) by lia;
                 ngrun;
                 if_cases KZ; zify_cond KZ;
                   [
                     ngrun;
                     if_cases KB; zify_cond KB; try (exfalso; lia);
                     esign KN KA (q0 + c')%Z 999999999999999999%Z
                   |
                     ngrun_to 0xc1208%Z;
                     kapply (numa_L5 E OK SHZ Q (S (Z.to_nat (LEN))) q0); [nclose | lia | lia |];
                     intros z'; intro_words; intros HZ1 HZ2;
                     ngrun;
                     if_cases KB; zify_cond KB;
                       [
                         assert (HQC : (z' <= q0 + c')%Z)
                           by (destruct (Z_le_dec z' (q0 + c')) as [L|G]; [exact L|]; exfalso; apply HND; rewrite (HZ2 (q0 + c')%Z) by lia; lia);
                         assert (HZS : zeros bs q0 (z' - q0))
                           by (intros i Hi; destruct (Z.eq_dec i 0) as [->|NE]; [replace (q0 + 0)%Z with q0 by lia; lia | apply HZ2; lia]);
                         pose proof (dval_lt18 bs q0 c' (z' - q0) ltac:(lia) ltac:(lia) HD' HZS) as HV;
                         change (10 ^ 18)%Z with 1000000000000000000%Z in HV;
                         esign KN KA (q0 + c')%Z (dval bs q0 c')
                       | esign KN KA (q0 + c')%Z 999999999999999999%Z ] ])
              | (assert (H18 : (c' < 19)%Z) by lia;
                 pose proof (dval_bound bs q0 c' ltac:(lia) HD') as HDB;
                 assert (HP18 : (10 ^ c' <= 10 ^ 18)%Z) by (apply Z.pow_le_mono_r; lia);
                 change (10 ^ 18)%Z with 1000000000000000000%Z in HP18;
                 esign KN KA (q0 + c')%Z (dval bs q0 c')) ].
  Qed.

  Lemma seg_numa_eadd : forall (Q : machine_state -> Prop) (s : st) neg p e0 v,
    (-2097152 <= e0 <= 0)%Z -> (-1000000000000000000 < v < 1000000000000000000)%Z ->
    numa_flt_k E Q s neg p ->
    numa_eadd_k E Q s neg p e0 v.
  Proof using OK SHZ.
    intros Q s neg p e0 v HE0 HV KF. unfold numa_eadd_k. intros until m1. intros HM.
    s2_env OK.
    nopen HM.
    destruct (Z_lt_dec v 0) as [VN|VP].
    - zstep. zstep. zstep. g_bias. ngrun_to 0xc1290%Z. kapply KF. nclose.
    - zstep. zstep. zstep. g_bias. ngrun_to 0xc1290%Z. kapply KF. nclose.
  Qed.

  Lemma seg_numa_eneg : forall (Q : machine_state -> Prop) (s : st) neg p e0 v,
    (0 <= v < 1000000000000000000)%Z ->
    numa_eadd_k E Q s neg p e0 (- v) ->
    numa_eneg_k E Q s neg p e0 v.
  Proof using OK SHZ.
    intros Q s neg p e0 v HV KA. unfold numa_eneg_k. intros until m1. intros HM.
    s2_env OK.
    nopen HM.
    destruct (Z.eq_dec v 0) as [V0|VN].
    - zstep. zstep. zstep. g_bias. ngrun_to 0xc1278%Z. kapply KA. nclose.
    - zstep. zstep. zstep. g_bias. ngrun_to 0xc1278%Z. kapply KA. nclose.
  Qed.
End NumA3.
