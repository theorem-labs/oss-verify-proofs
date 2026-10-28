(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump.lib.Lib Require Import Tac Arr Bytes StoreFast FP ImageA.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump.lib.Sj Require Import SjS1Out SjStage2 SjLeaves SjTape SjTapeInv SjTapeList SjExpDigits.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump.lib.B Require Import Sj_akit Sj_stage2_defs Sj_stage2_tapek Sj_stage2_traps Sj_stage2_guard Sj_tables Sj_stage2_hooks Sj_stage2_numkit Sj_stage2_numkit2
  Sj_stage2_numo_defs Sj_stage2_numo_defs2 Sj_stage2_numo_defs3 Sj_stage2_numo_loops.
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
Local Ltac g_store_hook ::= s2_note_tape.

  Ltac int_fin KX KC KBIG KW3 KEND :=
    lazymatch goal with |- evt _ _ (MS _ _ (Z_to_bv 64 ?pc) _ _ _ _) =>
      lazymatch pc with
      | 0xc3ca8%Z => nstep; gdec; int_exp KX KC KBIG KW3 KEND
      | 0xcd104%Z => nexit0 KX
      | 0xcd17c%Z => first [ (n_tape2; s2_kvr_kapply KC; nclose) | (kapply KC; nclose) ]
      | 0xc3c78%Z => kapply KBIG; nclose
      | 0xc3640%Z => kapply KW3; nclose
      | 0xc36c4%Z => first [ (n_tape2; s2_kvr_kapply KEND; nclose) | (kapply KEND; nclose) ]
      end end
  with int_exp KX KC KBIG KW3 KEND :=
    ngexp ltac:(fun pc => lazymatch pc with 0xc3ca8%Z => fail | 0xcd104%Z => fail | 0xcd17c%Z => fail | 0xc3c78%Z => fail | 0xc3640%Z => fail | 0xc36c4%Z => fail | _ => idtac end)
          ltac:(idtac; int_fin KX KC KBIG KW3 KEND).

  Ltac int_go KX KC KBIG KW3 KEND := ngstep; int_exp KX KC KBIG KW3 KEND.

Section NumO3b.
  Variable E : s2env.
  Hypothesis OK : env_ok E.
  Hypothesis SHZ : a_shz E.
  Notation bs := (e_bs E).
  Notation LEN := (blen bs).
  Notation o s := (e_off E (k s)).

  Lemma seg_numo_intbig : forall (Q : machine_state -> Prop) (s : st) neg,
    exit_k E Q -> numo_intbig_k E Q s neg.
  Proof using OK SHZ.
    intros Q s neg KX. unfold numo_intbig_k. intros until m1. intros HM.
    s2_env OK.
    nopen HM.
    int_go KX KX KX KX KX.
  Qed.

  Lemma seg_numo_intend : forall (Q : machine_state -> Prop) (s : st) neg p,
    (0 <= k s <= e_n E)%Z -> (0 <= p <= LEN)%Z -> (0 <= W s)%Z -> (W s + 2 <= e_tcap E)%Z -> exit_k E Q ->
    objcont_k E Q (mkst (k s + 1) (depth s) (W s + 2) (sb s) (scopes s)) ->
    numo_intend_k E Q s neg p.
  Proof using OK SHZ.
    intros Q s neg p HK HP HW0 HW KX KC. unfold numo_intend_k. intros until m1. intros HM.
    pose proof (ok_bytes _ OK) as BOK. pose proof (off_bound E OK (k s) HK) as HO.
    pose proof (B_range bs p BOK) as HB0. pose proof (sown_range (B bs p)) as HSW.
    s2_env OK.
    nopen HM.
    int_go KX KC KX KX KX.
  Qed.

End NumO3b.

Section NumO3c.
  Variable E : s2env.
  Hypothesis OK : env_ok E.
  Hypothesis SHZ : a_shz E.
  Notation bs := (e_bs E).
  Notation LEN := (blen bs).
  Notation o s := (e_off E (k s)).

  Lemma seg_numo_intw3 : forall (Q : machine_state -> Prop) (s : st) neg p,
    (0 <= k s <= e_n E)%Z -> (0 <= p <= LEN)%Z -> (0 <= W s)%Z -> (W s + 2 <= e_tcap E)%Z -> Z.of_nat (length (e_tws E)) = W s -> exit_k E Q ->
    (forall v r, num_word v -> numo_intend_k (gapp E [v; r] []) Q s neg p) ->
    numo_intw3_k E Q s neg p.
  Proof using OK SHZ.
    intros Q s neg p HK HP HW0 HW GLT KX KEND. unfold numo_intw3_k. intros until m1. intros HM.
    pose proof (ok_bytes _ OK) as BOK. pose proof (off_bound E OK (k s) HK) as HO.
    s2_env OK.
    nopen HM.
    int_go KX KX KX KX KEND.
  Qed.

  Lemma seg_numo_int : forall (Q : machine_state -> Prop) (s : st) neg p,
    (0 <= k s <= e_n E)%Z -> (0 <= p <= LEN)%Z -> (0 <= W s)%Z -> (W s + 2 <= e_tcap E)%Z -> Z.of_nat (length (e_tws E)) = W s -> exit_k E Q -> (forall v r, exit_k (gapp E [v; r] []) Q) ->
    (forall v r, num_word v -> objcont_k (gapp E [v; r] []) Q (mkst (k s + 1) (depth s) (W s + 2) (sb s) (scopes s))) ->
    numo_int_k E Q s neg p.
  Proof using OK SHZ.
    intros Q s neg p HK HP HW0 HW GLT KX KX2 KC.
    pose proof (seg_numo_intbig E OK SHZ Q s neg KX) as KBIG.
    assert (KEND : forall v r, num_word v -> numo_intend_k (gapp E [v; r] []) Q s neg p)
      by (intros v r Hv; exact (seg_numo_intend (gapp E [v; r] []) (env_ok_gapp E _ _ OK) SHZ Q s neg p HK HP HW0 HW (KX2 v r) (KC v r Hv))).
    pose proof (seg_numo_intw3 Q s neg p HK HP HW0 HW GLT KX KEND) as KW3.
    unfold numo_int_k. intros until m1. intros HM.
    pose proof (ok_bytes _ OK) as BOK. pose proof (off_bound E OK (k s) HK) as HO.
    pose proof (B_range bs p BOK) as HB0. pose proof (sown_range (B bs p)) as HSW.
    pose proof (B_range bs (o s) BOK) as HBT.
    s2_env OK.
    nopen HM.
    int_exp KX KC KBIG KW3 KEND.
  Qed.
End NumO3c.
