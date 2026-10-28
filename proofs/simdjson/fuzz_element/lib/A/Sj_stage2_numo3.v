(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Lib Require Import Tac Arr Bytes StoreFast FP ImageA.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Sj Require Import SjS1Out SjStage2 SjLeaves SjTape SjTapeInv SjTapeList.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.A Require Import Sj_akit Sj_stage2_defs Sj_stage2_tapek Sj_stage2_traps Sj_stage2_guard Sj_tables Sj_stage2_hooks Sj_stage2_numkit Sj_stage2_numkit2
  Sj_stage2_numo_defs Sj_stage2_numo_loops.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac lia ::= lia0.
Local Ltac tlia ::= s2tlia.
Local Ltac solve_load ::= first [ solve_load_base | s2_load_shadow | s2_load_buf | s2_load_sown | solve_load_image ].
Local Ltac solve_store ::= first [ solve_store0 | s2_store_wr ].
Local Ltac g_store_hook ::= s2_note_tape.

Section NumO3.
  Variable E : s2env.
  Hypothesis OK : env_ok E.
  Hypothesis SHZ : a_shz E.
  Notation bs := (e_bs E).
  Notation LEN := (blen bs).
  Notation o s := (e_off E (k s)).

  Lemma seg_numo_expd : forall (Q : machine_state -> Prop) (s : st) neg q0,
    (0 <= k s <= e_n E)%Z -> (0 <= neg <= 1)%Z -> (0 <= q0 <= LEN)%Z -> exit_k E Q ->
    (forall p', (q0 <= p' <= LEN)%Z -> numo_flt_k E Q s neg p') ->
    numo_expd_k E Q s neg q0.
  Proof using OK SHZ.
    intros Q s neg q0 HK HNEG HQ0 KX KF. unfold numo_expd_k. intros until m1. intros HM.
    pose proof (ok_bytes _ OK) as BOK. pose proof (off_bound E OK (k s) HK) as HO.
    pose proof (B_range bs q0 BOK) as HBQ.
    s2_env OK.
    nopen HM.
    ngrun.
    if_cases K3; zify_cond K3.
    - assert (HNZ : (q0 < LEN)%Z) by (nz_lt_by ltac:(lia)).
      ngrun_to 0xc347c%Z.
      kapply (numo_L4 E OK SHZ Q (S (Z.to_nat (LEN))) q0 1%Z); [nclose | lia | lia | lia | lia |].
      intros c'. intro_words. intros HC1 HC2.
      ngrun.

      if_cases K4; zify_cond K4;
        first [ (ngrun_to 0xc438c%Z;
                 kapply (numo_L5 E OK SHZ Q (S (Z.to_nat (LEN))) q0); [nclose | lia | lia |];
                 intro_words;
                 ngexp ltac:(fun pc => lazymatch pc with 0xc34f8%Z => fail | _ => idtac end)
                       ltac:(idtac; kapply (KF (q0 + c')%Z); [lia | nclose]))
              | ngexp ltac:(fun pc => lazymatch pc with 0xc34f8%Z => fail | _ => idtac end)
                      ltac:(idtac; kapply (KF (q0 + c')%Z); [lia | nclose]) ].
    -
      nexit KX.
  Qed.

  Lemma seg_numo_scan : forall (Q : machine_state -> Prop) (s : st) neg p,
    (0 <= k s <= e_n E)%Z -> (0 <= neg <= 1)%Z -> (0 <= p <= LEN)%Z ->
    (forall q0, (p < q0 <= LEN)%Z -> numo_expd_k E Q s neg q0) ->
    numo_flt_k E Q s neg p ->
    numo_int_k E Q s neg p ->
    numo_scan_k E Q s neg p.
  Proof using OK SHZ.
    intros Q s neg p HK HNEG HP KE KF KI. unfold numo_scan_k. intros until m1. intros HM.
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
        ngrun_to 0xc3438%Z. kapply (KE (p + 2)%Z); [lia | nclose].
      + ngrun.
        if_cases K3; zify_cond K3.
        *
          kapply (KE (p + 1)%Z); [lia | nclose].
        *
          assert (HNZ1 : (p + 1 < LEN)%Z) by (nz_lt_by ltac:(lia)).
          ngrun_to 0xc3438%Z. kapply (KE (p + 2)%Z); [lia | nclose].
  Qed.
  Ltac int_fin KX KJ :=
    lazymatch goal with |- evt _ _ (MS _ _ (Z_to_bv 64 ?pc) _ _ _ _) =>
      lazymatch pc with
      | 0xc3a84%Z => nstep; gdec; int_exp KX KJ
      | 0xcb1dc%Z => nexit0 KX
      | 0xc3b10%Z => n_tape2; s2_kvr_kapply KJ; nclose
      end end
  with int_exp KX KJ :=
    ngexp ltac:(fun pc => lazymatch pc with 0xc3a84%Z => fail | 0xcb1dc%Z => fail | 0xc3b10%Z => fail | _ => idtac end) ltac:(idtac; int_fin KX KJ).

  Lemma seg_numo_int : forall (Q : machine_state -> Prop) (s : st) neg p,
    (0 <= k s <= e_n E)%Z -> (0 <= p <= LEN)%Z -> (0 <= W s)%Z -> (W s + 2 <= e_tcap E)%Z -> Z.of_nat (length (e_tws E)) = W s -> exit_k E Q ->
    (forall v r, num_word v -> numo_join_k (gapp E [v; r] []) Q s) ->
    numo_int_k E Q s neg p.
  Proof using OK SHZ.
    intros Q s neg p HK HP HW0 HW GLT KX KJ. unfold numo_int_k. intros until m1. intros HM.
    pose proof (ok_bytes _ OK) as BOK. pose proof (off_bound E OK (k s) HK) as HO.
    pose proof (B_range bs p BOK) as HB0. pose proof (sown_range (B bs p)) as HSW.
    s2_env OK.
    nopen HM.
    int_exp KX KJ.
  Qed.
End NumO3.
