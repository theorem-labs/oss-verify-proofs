(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Lib Require Import Tac Arr Bytes StoreFast FP ImageA.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Sj Require Import SjS1Out SjStage2 SjLeaves SjTape SjTapeInv SjTapeList.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.A Require Import Sj_akit Sj_stage2_defs Sj_stage2_tapek Sj_stage2_traps Sj_stage2_guard Sj_tables Sj_stage2_hooks Sj_stage2_numkit Sj_stage2_numkit2 Sj_stage2_numkit3
  Sj_stage2_numr_defs Sj_stage2_numr_loops.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac lia ::= lia0.
Local Ltac tlia ::= r_tlia.
Local Ltac solve_load ::= first [ solve_load_base | s2_load_shadow_cp | s2_load_shadow | s2_load_cp | s2_load_sown | solve_load_image ].
Local Ltac solve_store ::= first [ solve_store0 | s2_store_wr ].

Section NumR2.
  Variable E : s2env.
  Hypothesis OK : env_ok E.
  Hypothesis SHZ : a_shz E.
  Variable CP : Z.
  Hypothesis HCP : cp_ok E CP.
  Hypothesis SHZC : cp_shz E CP.
  Notation bs := (crs (rtxt E)).
  Notation LEN := (blen (rtxt E)).
  Notation o s := 0%Z.

  Lemma seg_numr_dot : forall (Q : machine_state -> Prop) (s : st) neg p,
    (0 <= k s <= e_n E)%Z -> (0 <= neg <= 1)%Z -> (o s + neg < p <= LEN)%Z ->
    (B bs p = 46%Z -> numr_frac_k E Q CP s neg p) -> numr_scan_k E Q CP s neg p ->
    numr_dot_k E Q CP s neg p.
  Proof using OK SHZ HCP SHZC.
    intros Q s neg p HK HNEG HP KF KS. unfold numr_dot_k. intros until m1. intros HM.
    pose proof (rtxt_ok E OK) as BOK. pose proof (off_bound E OK (k s) HK) as HO. pose proof (B_range bs p BOK) as HBP.
    s2_env OK.
    nopen HM.
    ngrun.
    if_cases K5; zify_cond K5.
    - ngrun_to 0xbee74%Z. kapply KS. nclose.
    - kapply (KF ltac:(lia)). nclose.
  Qed.

  Lemma seg_numr_frac : forall (Q : machine_state -> Prop) (s : st) neg p,
    (0 <= k s <= e_n E)%Z -> (0 <= neg <= 1)%Z -> (o s + neg < p < LEN)%Z ->
    (forall r, (p < r <= LEN)%Z -> numr_ftail_k E Q CP s neg p r) ->
    numr_frac_k E Q CP s neg p.
  Proof using OK SHZ HCP SHZC.
    intros Q s neg p HK HNEG HP KT. unfold numr_frac_k. intros until m1. intros HM.
    pose proof (rtxt_ok E OK) as BOK. pose proof (off_bound E OK (k s) HK) as HO.
    pose proof (B_range bs (p + 1) BOK) as HB0. pose proof (B_range bs (p + 2) BOK) as HB1. pose proof (B_range bs (p + 3) BOK) as HB2.
    pose proof (B_range bs (p + 4) BOK) as HB3. pose proof (B_range bs (p + 5) BOK) as HB4. pose proof (B_range bs (p + 6) BOK) as HB5.
    pose proof (B_range bs (p + 7) BOK) as HB6. pose proof (B_range bs (p + 8) BOK) as HB7.
    s2_env OK.
    nopen HM.
    ngrun_to 0xbd6c4%Z. fold_V8.
    ngrun.

    if_cases KC; zify_cond KC;
      first [ (pose proof (V8_range _ _ _ _ _ _ _ _ HB0 HB1 HB2 HB3 HB4 HB5 HB6 HB7) as HVR; rewrite ?(Z.mod_small _ _ HVR) in KC;
               pose proof (swar8_last _ _ _ _ _ _ _ _ HB0 HB1 HB2 HB3 HB4 HB5 HB6 HB7 KC) as HL;
               assert (HNZ : (p + 8 < LEN)%Z) by (nz_lt_by ltac:(lia));
               ngrun_to 0xbd764%Z;
               kapply (numr_L2 E OK SHZ CP HCP SHZC Q (S (Z.to_nat (LEN))) p 0%Z); [nclose | lia | lia | lia | lia |];
               intros j'; intro_words; intros HJ1 HJ2;
               ngrun_to 0xbed04%Z; kapply (KT (p + 1 + 8 * j')%Z); [lia | nclose])
            | (ngrun_to 0xbed04%Z; kapply (KT (p + 1)%Z); [lia | nclose]) ].
  Qed.

  Lemma seg_numr_ftail : forall (Q : machine_state -> Prop) (s : st) neg p r,
    (0 <= k s <= e_n E)%Z -> (0 <= neg <= 1)%Z -> (o s + neg < p)%Z -> (p < r <= LEN)%Z ->
    (forall r', (r <= r' <= LEN)%Z -> numr_ftail2_k E Q CP s neg p r') ->
    numr_ftail_k E Q CP s neg p r.
  Proof using OK SHZ HCP SHZC.
    intros Q s neg p r HK HNEG HP HR KT. unfold numr_ftail_k. intros until m1. intros HM.
    pose proof (rtxt_ok E OK) as BOK. pose proof (off_bound E OK (k s) HK) as HO.
    pose proof (B_range bs r BOK) as HB0. pose proof (B_range bs (r + 1) BOK) as HB1. pose proof (B_range bs (r + 2) BOK) as HB2.
    pose proof (B_range bs (r + 3) BOK) as HB3.
    s2_env OK.
    nopen HM.
    ngrun_to 0xbed5c%Z.

    match goal with |- context [Z_to_bv 64 (Z.lor (Z.lor ?a ?b) (Z.lor ?c ?d))] => set (val := Z.lor (Z.lor a b) (Z.lor c d)) end.
    ngrun.

    if_cases KC; zify_cond KC;
      first [ (unfold val in KC; pose proof (swar4_last_sx _ _ _ _ HB0 HB1 HB2 HB3 KC) as HL;
               assert (HNZ : (r + 3 < LEN)%Z) by (nz_lt_by ltac:(lia));
               clear KC HL; clearbody val;
               nfrun_to 0xbedc4%Z ltac:(nkeep ltac:(fun n => lazymatch n with 10%Z => fail | 11%Z => fail | 30%Z => fail | _ => idtac end));
               kapply (KT (r + 4)%Z); [lia | nclose])
            | (clear KC; clearbody val; ngrun_to 0xbedc4%Z; kapply (KT r); [lia | nclose]) ].
  Qed.

  Lemma seg_numr_ftail2 : forall (Q : machine_state -> Prop) (s : st) neg p r,
    (0 <= k s <= e_n E)%Z -> (0 <= neg <= 1)%Z -> (o s + neg < p)%Z -> (p < r <= LEN)%Z -> rdelA_k E Q CP ->
    (forall p', (r <= p' <= LEN)%Z -> numr_scan_k E Q CP s neg p') ->
    numr_ftail2_k E Q CP s neg p r.
  Proof using OK SHZ HCP SHZC.
    intros Q s neg p r HK HNEG HP HR KX KS. unfold numr_ftail2_k. intros until m1. intros HM.
    pose proof (rtxt_ok E OK) as BOK. pose proof (off_bound E OK (k s) HK) as HO.
    pose proof (B_range bs r BOK) as HB0.
    assert (EB : B bs (p + (r - p)) = B bs r) by (f_equal; lia).
    s2_env OK.
    nopen HM.
    ngrun.
    if_cases K0; zify_cond K0.
    -
      ngrun.
      if_cases K1; zify_cond K1.
      + ngrun_to 0xbee74%Z. kapply (KS r); [lia | nclose].
      + nexit KX.
    - assert (HNZ : (r < LEN)%Z) by (nz_lt_by ltac:(lia)).
      ngrun_to 0xbee00%Z.
      kapply (numr_L3 E OK SHZ CP HCP SHZC Q (S (Z.to_nat (LEN))) r); [nclose | lia | lia |].
      intros q'. intro_words. intros HQ'.
      ngrun_to 0xbee74%Z. kapply (KS q'); [lia | nclose].
  Qed.
End NumR2.
