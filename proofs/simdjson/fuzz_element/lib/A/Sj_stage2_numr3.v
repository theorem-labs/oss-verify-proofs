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
Local Ltac g_store_hook ::= s2_note_tape.

Section NumR3.
  Variable E : s2env.
  Hypothesis OK : env_ok E.
  Hypothesis SHZ : a_shz E.
  Variable CP : Z.
  Hypothesis HCP : cp_ok E CP.
  Hypothesis SHZC : cp_shz E CP.
  Notation bs := (crs (rtxt E)).
  Notation LEN := (blen (rtxt E)).
  Notation o s := 0%Z.

  Lemma seg_numr_expd : forall (Q : machine_state -> Prop) (s : st) neg q0,
    (0 <= k s <= e_n E)%Z -> (0 <= neg <= 1)%Z -> (0 <= q0 <= LEN)%Z -> rdelA_k E Q CP ->
    (forall p', (q0 <= p' <= LEN)%Z -> numr_flt_k E Q CP s neg p') ->
    numr_expd_k E Q CP s neg q0.
  Proof using OK SHZ HCP SHZC.
    intros Q s neg q0 HK HNEG HQ0 KX KF. unfold numr_expd_k. intros until m1. intros HM.
    pose proof (rtxt_ok E OK) as BOK. pose proof (off_bound E OK (k s) HK) as HO.
    pose proof (B_range bs q0 BOK) as HBQ.
    s2_env OK.
    nopen HM.
    ngrun.
    if_cases K3; zify_cond K3.
    - assert (HNZ : (q0 < LEN)%Z) by (nz_lt_by ltac:(lia)).
      ngrun_to 0xbef04%Z.
      kapply (numr_L4 E OK SHZ CP HCP SHZC Q (S (Z.to_nat (LEN))) q0 1%Z); [nclose | lia | lia | lia | lia |].
      intros c'. intro_words. intros HC1 HC2.
      ngrun.

      if_cases K4; zify_cond K4;
        first [ (ngrun_to 0xc3c48%Z;
                 kapply (numr_L5 E OK SHZ CP HCP SHZC Q (S (Z.to_nat (LEN))) q0); [nclose | lia | lia |];
                 intro_words;
                 ngexp ltac:(fun pc => lazymatch pc with 0xbf030%Z => fail | _ => idtac end)
                       ltac:(idtac; kapply (KF (q0 + c')%Z); [lia | nclose]))
              | ngexp ltac:(fun pc => lazymatch pc with 0xbf030%Z => fail | _ => idtac end)
                      ltac:(idtac; kapply (KF (q0 + c')%Z); [lia | nclose]) ].
    -
      nexit KX.
  Qed.

  Lemma seg_numr_scan : forall (Q : machine_state -> Prop) (s : st) neg p,
    (0 <= k s <= e_n E)%Z -> (0 <= neg <= 1)%Z -> (0 <= p <= LEN)%Z ->
    (forall q0, (p < q0 <= LEN)%Z -> numr_expd_k E Q CP s neg q0) ->
    numr_flt_k E Q CP s neg p ->
    numr_int_k E Q CP s neg p ->
    numr_scan_k E Q CP s neg p.
  Proof using OK SHZ HCP SHZC.
    intros Q s neg p HK HNEG HP KE KF KI. unfold numr_scan_k. intros until m1. intros HM.
    pose proof (rtxt_ok E OK) as BOK. pose proof (off_bound E OK (k s) HK) as HO.
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
        ngrun_to 0xbeec8%Z. kapply (KE (p + 2)%Z); [lia | nclose].
      + ngrun.
        if_cases K3; zify_cond K3.
        *
          kapply (KE (p + 1)%Z); [lia | nclose].
        *
          assert (HNZ1 : (p + 1 < LEN)%Z) by (nz_lt_by ltac:(lia)).
          ngrun_to 0xbeec8%Z. kapply (KE (p + 2)%Z); [lia | nclose].
  Qed.
  Ltac int_fin KX KJ :=
    lazymatch goal with |- evt _ _ (MS _ _ (Z_to_bv 64 ?pc) _ _ _ _) =>
      lazymatch pc with
      | 0xc28f4%Z => nstep; gdec; int_exp KX KJ
      | 0xbd5a4%Z => nexit0 KX
      | 0xc2f14%Z => n_tape2; s2_kvr_kapply KJ; nclose
      end end
  with int_exp KX KJ :=
    ngexp ltac:(fun pc => lazymatch pc with 0xc28f4%Z => fail | 0xbd5a4%Z => fail | 0xc2f14%Z => fail | _ => idtac end) ltac:(idtac; int_fin KX KJ).

  Lemma seg_numr_int : forall (Q : machine_state -> Prop) (s : st) neg p,
    (0 <= k s <= e_n E)%Z -> (0 <= p <= LEN)%Z -> (0 <= W s)%Z -> (W s + 2 <= e_tcap E)%Z -> Z.of_nat (length (e_tws E)) = 1%Z -> rdelA_k E Q CP -> (forall v r, num_word v -> numr_join_k (gapp E [v; r] []) Q CP s) ->
    numr_int_k E Q CP s neg p.
  Proof using OK SHZ HCP SHZC.
    intros Q s neg p HK HP HW0 HW GLT KX KJ. unfold numr_int_k. intros until m1. intros HM.
    pose proof (rtxt_ok E OK) as BOK. pose proof (off_bound E OK (k s) HK) as HO.
    pose proof (B_range bs p BOK) as HB0. pose proof (sown_range (B bs p)) as HSW.
    s2_env OK.
    nopen HM.
    int_exp KX KJ.
  Qed.
End NumR3.
