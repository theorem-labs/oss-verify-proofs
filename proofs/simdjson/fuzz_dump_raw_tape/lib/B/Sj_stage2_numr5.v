(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump_raw_tape.lib.Lib Require Import Tac Arr Bytes StoreFast FP ImageA.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump_raw_tape.lib.Sj Require Import SjS1Out SjStage2 SjLeaves SjTape SjTapeInv SjTapeList SjExpDigits.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump_raw_tape.lib.B Require Import Sj_akit Sj_stage2_defs Sj_stage2_tapek Sj_stage2_traps Sj_stage2_guard Sj_tables Sj_stage2_hooks Sj_stage2_numkit Sj_stage2_numkit2 Sj_stage2_numkit2b Sj_stage2_numkit3
  Sj_stage2_numr_defs Sj_stage2_numr_defs2 Sj_stage2_numr_loops.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac lia ::= s2lia.
Local Ltac tlia ::= r_tlia.
Local Ltac solve_load ::= first [ solve_load_base | s2_load_shadow_cp | s2_load_shadow | s2_load_cp | s2_load_sown | s2_load_pow | solve_load_image ].
Local Ltac solve_store ::= first [ solve_store0 | s2_store_wr ].

Section NumR5.
  Variable E : s2env.
  Hypothesis OK : env_ok E.
  Hypothesis SHZ : a_shz E.
  Variable CP : Z.
  Hypothesis HCP : cp_ok E CP.
  Hypothesis SHZC : cp_shz E CP.
  Notation bs := (crs (rtxt E)).
  Notation LEN := (blen (rtxt E)).
  Notation o s := 0%Z.

  Lemma seg_numr_cmp : forall (Q : machine_state -> Prop) (s : st) neg e,
    (-342 <= e <= 308)%Z -> numr_write_k E Q CP s neg -> numr_cmpslow_k E Q CP s neg e ->
    numr_cmp_k E Q CP s neg e.
  Proof using OK SHZ HCP SHZC.
    intros Q s neg e HE KW KSL. unfold numr_cmp_k. intros until m1. intros HM.
    s2_env OK.
    nopen HM.

    ngrun.
    if_cases K0; zify_cond K0; first [ (kapply KSL; nclose) | idtac ].
    ngrun.
    if_cases K1; zify_cond K1; first [ (kapply KSL; nclose) | idtac ].
    ngrun.

    if_cases K2; zify_cond K2;
      first [ (assert (HE2 : (-22 <= e < 0)%Z) by lia;
               ngrun_to 0xbce9c%Z;
               nreg_set 10%Z (152480 + 8 * - e)%Z;
               ngexp ltac:(fun pc => lazymatch pc with 0xbcecc%Z => fail | _ => idtac end) ltac:(idtac; kapply KW; nclose))
            | (assert (HE2 : (0 <= e <= 22)%Z) by lia;
               ngrun_to 0xb9bc0%Z;
               nreg_set 10%Z (152480 + 8 * e)%Z;
               ngexp ltac:(fun pc => lazymatch pc with 0xbcecc%Z => fail | _ => idtac end) ltac:(idtac; kapply KW; nclose)) ].
  Qed.

  Ltac keepA n := nkeep ltac:(fun n => lazymatch n with 10%Z => fail | 11%Z => fail | 12%Z => fail | 13%Z => fail | 14%Z => fail | _ => idtac end) n.
  Lemma seg_numr_cmpslow : forall (Q : machine_state -> Prop) (s : st) neg e,
    (-342 <= e <= 308)%Z -> numr_write_k E Q CP s neg -> numr_cmpB_k E Q CP s neg ->
    numr_cmpslow_k E Q CP s neg e.
  Proof using OK SHZ HCP SHZC.
    intros Q s neg e HE KW KB. unfold numr_cmpslow_k. intros until m1. intros HM.
    s2_env OK.
    nopen HM.
    ngrun.

    if_cases K9;
      first [ (ngrun_to 0xbaabc%Z; rewrite (p5u_sw e 684 HE) by lia;
               ngrun_cut_f ltac:(fun pc => idtac) keepA;
               if_cases K1;
                 first [ (kapply KB; nclose)
                       | (ngrun_to 0xbaba8%Z; rewrite (p5u_sw e 685 HE) by lia; ngrun_to 0xbabdc%Z; kapply KB; nclose) ])
            | ngexp ltac:(fun pc => lazymatch pc with 0xbcecc%Z => fail | _ => idtac end) ltac:(idtac; kapply KW; nclose) ].
  Qed.
End NumR5.
