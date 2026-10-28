(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump.lib.Lib Require Import Tac Arr Bytes StoreFast FP ImageA.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump.lib.Sj Require Import SjS1Out SjStage2 SjLeaves SjTape SjTapeInv SjTapeList SjExpDigits.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump.lib.B Require Import Sj_akit Sj_stage2_defs Sj_stage2_tapek Sj_stage2_traps Sj_stage2_guard Sj_tables Sj_stage2_hooks Sj_stage2_numkit Sj_stage2_numkit2
  Sj_stage2_numo_defs Sj_stage2_numo_defs2 Sj_stage2_numo_loops.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac lia ::= s2lia.
Local Ltac tlia ::= s2tlia.
Local Ltac solve_load ::= first [ solve_load_base | s2_load_shadow | s2_load_buf | s2_load_sown | s2_load_pow | solve_load_image ].
Local Ltac solve_store ::= first [ solve_store0 | s2_store_wr ].

Section NumO5.
  Variable E : s2env.
  Hypothesis OK : env_ok E.
  Hypothesis SHZ : a_shz E.
  Notation bs := (e_bs E).
  Notation LEN := (blen bs).
  Notation o s := (e_off E (k s)).

  Lemma seg_numo_cmp : forall (Q : machine_state -> Prop) (s : st) neg e,
    (-342 <= e <= 308)%Z -> numo_write_k E Q s neg -> numo_cmpslow_k E Q s neg e ->
    numo_cmp_k E Q s neg e.
  Proof using OK SHZ.
    intros Q s neg e HE KW KSL. unfold numo_cmp_k. intros until m1. intros HM.
    s2_env OK.
    nopen HM.

    ngrun.
    if_cases K0; zify_cond K0; first [ (kapply KSL; nclose) | idtac ].
    ngrun.
    if_cases K1; zify_cond K1; first [ (kapply KSL; nclose) | idtac ].
    ngrun.

    if_cases K2; zify_cond K2;
      first [ (assert (HE2 : (-22 <= e < 0)%Z) by lia;
               ngrun_to 0xc3bb0%Z;
               nreg_set 10%Z (151168 + 8 * - e)%Z;
               ngexp ltac:(fun pc => lazymatch pc with 0xc3be4%Z => fail | _ => idtac end) ltac:(idtac; kapply KW; nclose))
            | (assert (HE2 : (0 <= e <= 22)%Z) by lia;
               ngrun_to 0xc3988%Z;
               nreg_set 10%Z (151168 + 8 * e)%Z;
               ngexp ltac:(fun pc => lazymatch pc with 0xc3be4%Z => fail | _ => idtac end) ltac:(idtac; kapply KW; nclose)) ].
  Qed.

  Ltac keepA n := nkeep ltac:(fun n => lazymatch n with 10%Z => fail | 11%Z => fail | 12%Z => fail | 13%Z => fail | 14%Z => fail | _ => idtac end) n.
  Lemma seg_numo_cmpslow : forall (Q : machine_state -> Prop) (s : st) neg e,
    (-342 <= e <= 308)%Z -> numo_write_k E Q s neg -> numo_cmpB_k E Q s neg ->
    numo_cmpslow_k E Q s neg e.
  Proof using OK SHZ.
    intros Q s neg e HE KW KB. unfold numo_cmpslow_k. intros until m1. intros HM.
    s2_env OK.
    nopen HM.
    ngrun.

    if_cases K9;
      first [ (ngrun_to 0xc39bc%Z; rewrite (p5u_sw e 684 HE) by lia;
               ngrun_cut_f ltac:(fun pc => idtac) keepA;
               if_cases K1;
                 first [ (kapply KB; nclose)
                       | (ngrun_to 0xc3ab4%Z; rewrite (p5u_sw e 685 HE) by lia; ngrun_to 0xc3ae8%Z; kapply KB; nclose) ])
            | ngexp ltac:(fun pc => lazymatch pc with 0xc3be4%Z => fail | _ => idtac end) ltac:(idtac; kapply KW; nclose) ].
  Qed.
End NumO5.
