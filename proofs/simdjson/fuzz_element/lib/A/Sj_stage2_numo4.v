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

Section NumO4.
  Variable E : s2env.
  Hypothesis OK : env_ok E.
  Hypothesis SHZ : a_shz E.
  Notation bs := (e_bs E).
  Notation LEN := (blen bs).
  Notation o s := (e_off E (k s)).

  Lemma seg_numo_flt : forall (Q : machine_state -> Prop) (s : st) neg p,
    (0 <= k s <= e_n E)%Z -> (0 <= neg <= 1)%Z -> (o s + neg < LEN)%Z -> (0 <= p <= LEN)%Z ->
    numo_range_k E Q s neg -> numo_slowcall_k E Q s ->
    numo_flt_k E Q s neg p.
  Proof using OK SHZ.
    intros Q s neg p HK HNEG HS HP KR KSL. unfold numo_flt_k. intros until m1. intros HM.
    pose proof (ok_bytes _ OK) as BOK. pose proof (off_bound E OK (k s) HK) as HO.
    pose proof (B_range bs p BOK) as HB0. pose proof (sown_range (B bs p)) as HSW.
    s2_env OK.
    nopen HM.
    ngrun.
    if_cases K0.
    - kapply KR. nclose.
    - ngrun_to 0xc3558%Z.
      kapply (numo_L6 E OK SHZ Q (S (Z.to_nat (LEN))) (o s + neg)%Z); [nclose | lia | lia |].
      intro_words.
      ngrun.
      if_cases K1; first [ (kapply KR; nclose) | (ngrun_to 0xe99dc%Z; kapply KSL; nclose) ].
  Qed.

  Lemma seg_numo_range : forall (Q : machine_state -> Prop) (s : st) neg,
    (0 <= W s)%Z -> (W s + 2 <= e_tcap E)%Z -> Z.of_nat (length (e_tws E)) = W s -> exit_k E Q -> (forall v r, num_word v -> numo_join_k (gapp E [v; r] []) Q s) ->
    (forall e, (-342 <= e <= 308)%Z -> numo_cmp_k E Q s neg e) ->
    numo_range_k E Q s neg.
  Proof using OK SHZ.
    intros Q s neg HW0 HW GLT KX KJ KC. unfold numo_range_k. intros until m1. intros HM.
    destruct (word_signed_repr xa4) as (e & HE & ->).
    s2_env OK.
    nopen HM.
    ngrun.
    if_cases K0; zify_cond K0.
    - assert (HER : (-342 <= e <= 308)%Z) by lia.
      kapply (KC e HER). nclose.
    - ngexp ltac:(fun pc => lazymatch pc with 0xc3b10%Z => fail | 0xcb1dc%Z => fail | _ => idtac end)
            ltac:(idtac; first [ nexit0 KX | (n_tape2; s2_kvr_kapply KJ; nclose) ]).
  Qed.
End NumO4.
