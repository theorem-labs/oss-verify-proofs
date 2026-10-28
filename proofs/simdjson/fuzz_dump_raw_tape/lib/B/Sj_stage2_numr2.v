(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump_raw_tape.lib.Lib Require Import Tac Arr Bytes StoreFast FP ImageA.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump_raw_tape.lib.Sj Require Import SjS1Out SjStage2 SjLeaves SjTape SjTapeInv SjTapeList.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump_raw_tape.lib.B Require Import Sj_akit Sj_stage2_defs Sj_stage2_tapek Sj_stage2_traps Sj_stage2_guard Sj_tables Sj_stage2_hooks Sj_stage2_numkit Sj_stage2_numkit2 Sj_stage2_numkit2b Sj_stage2_numkit3
  Sj_stage2_numr_defs Sj_stage2_numr_loops.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac lia ::= s2lia.
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

  Lemma seg_numr_frac : forall (Q : machine_state -> Prop) (s : st) neg p,
    (0 <= k s <= e_n E)%Z -> (0 <= neg <= 1)%Z -> (o s + neg < p < LEN)%Z ->
    (forall d, (1 <= d)%Z -> (p + d <= LEN)%Z -> numr_ftail_k E Q CP s neg p d) ->
    numr_frac_k E Q CP s neg p.
  Proof using OK SHZ HCP SHZC.
    intros Q s neg p HK HNEG HP KT. unfold numr_frac_k. intros until m1. intros HM.
    pose proof (rtxt_ok E OK) as BOK. pose proof (conj (Z.le_refl 0) (Z.le_refl 0)) as HO.
    pose proof (B_range bs (p + 1) BOK) as HB0. pose proof (B_range bs (p + 2) BOK) as HB1. pose proof (B_range bs (p + 3) BOK) as HB2.
    pose proof (B_range bs (p + 4) BOK) as HB3. pose proof (B_range bs (p + 5) BOK) as HB4. pose proof (B_range bs (p + 6) BOK) as HB5.
    pose proof (B_range bs (p + 7) BOK) as HB6. pose proof (B_range bs (p + 8) BOK) as HB7.
    s2_env OK.
    nopen HM.
    ngrun_to 0xb7af4%Z. fold_V8.
    ngrun.

    if_cases KC; zify_cond KC;
      first [ (pose proof (V8_range _ _ _ _ _ _ _ _ HB0 HB1 HB2 HB3 HB4 HB5 HB6 HB7) as HVR; rewrite ?(Z.mod_small _ _ HVR) in KC;
               pose proof (swar8_last _ _ _ _ _ _ _ _ HB0 HB1 HB2 HB3 HB4 HB5 HB6 HB7 KC) as HL;
               assert (HNZ : (p + 8 < LEN)%Z) by (nz_lt_by ltac:(lia));
               ngrun_to 0xb7b78%Z;
               kapply (numr_L2 E OK SHZ CP HCP SHZC Q (S (Z.to_nat (LEN))) p 0%Z); [nclose | lia | lia | lia | lia |];
               intros j'; intro_words; intros HJ1 HJ2;
               ngrun_to 0xb969c%Z; kapply (KT (1 + 8 * j')%Z); [lia | lia | nclose])
            | (ngrun_to 0xb969c%Z; kapply (KT 1%Z); [lia | lia | nclose]) ].
  Qed.

  Lemma seg_numr_ftail : forall (Q : machine_state -> Prop) (s : st) neg p d,
    (0 <= k s <= e_n E)%Z -> (0 <= neg <= 1)%Z -> (o s + neg < p)%Z -> (1 <= d)%Z -> (p + d <= LEN)%Z ->
    (forall d', (d <= d')%Z -> (p + d' <= LEN)%Z -> numr_ftail2_k E Q CP s neg p d') ->
    numr_ftail_k E Q CP s neg p d.
  Proof using OK SHZ HCP SHZC.
    intros Q s neg p d HK HNEG HP HD HR KT. unfold numr_ftail_k. intros until m1. intros HM.
    pose proof (rtxt_ok E OK) as BOK. pose proof (conj (Z.le_refl 0) (Z.le_refl 0)) as HO.
    pose proof (B_range bs (p + d) BOK) as HB0. pose proof (B_range bs (p + d + 1) BOK) as HB1. pose proof (B_range bs (p + d + 2) BOK) as HB2.
    pose proof (B_range bs (p + d + 3) BOK) as HB3.
    s2_env OK.
    nopen HM.
    ngrun_to 0xb9718%Z.

    match goal with |- context [Z_to_bv 64 (Z.lor (Z.lor ?a ?b) (Z.lor ?c ?d))] => set (val := Z.lor (Z.lor a b) (Z.lor c d)) end.
    ngrun.

    if_cases KC; zify_cond KC;
      first [ (unfold val in KC; pose proof (swar4_last_sx _ _ _ _ HB0 HB1 HB2 HB3 KC) as HL;
               assert (HNZ : (p + d + 3 < LEN)%Z) by (nz_lt_by ltac:(lia));
               clear KC HL; clearbody val;
               ngrun_to 0xb9780%Z;
               kapply (KT (d + 4)%Z); [lia | lia | nclose])
            | (clear KC; clearbody val; ngrun_to 0xb9780%Z; kapply (KT d); [lia | lia | nclose]) ].
  Qed.

  Lemma seg_numr_ftail2 : forall (Q : machine_state -> Prop) (s : st) neg p d,
    (0 <= k s <= e_n E)%Z -> (0 <= neg <= 1)%Z -> (o s + neg < p)%Z -> (1 <= d)%Z -> (p + d <= LEN)%Z -> rdelA_k E Q CP ->
    (forall d', (d <= d')%Z -> (p + d' <= LEN)%Z -> numr_scan_k E Q CP s neg (p + d') (1 - d')) ->
    numr_ftail2_k E Q CP s neg p d.
  Proof using OK SHZ HCP SHZC.
    intros Q s neg p d HK HNEG HP HD HR KX KS. unfold numr_ftail2_k. intros until m1. intros HM.
    pose proof (rtxt_ok E OK) as BOK. pose proof (conj (Z.le_refl 0) (Z.le_refl 0)) as HO.
    pose proof (B_range bs (p + d) BOK) as HB0.
    s2_env OK.
    nopen HM.
    ngrun.
    if_cases K0; zify_cond K0.
    -
      ngrun.
      if_cases K1; zify_cond K1.
      + ngrun_to 0xb9838%Z. kapply (KS d); [lia | lia | nclose].
      + nexit KX.
    - assert (HNZ : (p + d < LEN)%Z) by (nz_lt_by ltac:(lia)).
      ngrun_to 0xb97b4%Z.
      kapply (numr_L3 E OK SHZ CP HCP SHZC Q (S (Z.to_nat (LEN))) p d); [nclose | lia | lia | lia | lia |].
      intros d'. intro_words. intros HD1 HD2.
      pose proof (B_range bs (p + d') BOK) as HB1.
      ngrun_to 0xb9838%Z. kapply (KS d'); [lia | lia | nclose].
  Qed.
End NumR2.
