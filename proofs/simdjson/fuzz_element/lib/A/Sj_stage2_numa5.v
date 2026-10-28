(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Lib Require Import Tac Arr Bytes StoreFast FP ImageA.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Sj Require Import SjS1Out SjStage2 SjLeaves SjTape SjTapeInv SjTapeList.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.A Require Import Sj_akit Sj_stage2_defs Sj_stage2_tapek Sj_stage2_traps Sj_stage2_guard Sj_tables Sj_stage2_hooks Sj_stage2_numkit
  Sj_stage2_numkit2 Sj_stage2_numa_defs Sj_stage2_numa_defs2 Sj_stage2_numa_loops.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac lia ::= lia0.
Local Ltac tlia ::= s2tlia.
Local Ltac solve_load ::= first [ solve_load_base | s2_load_shadow | s2_load_pow | solve_load_image ].
Local Ltac solve_store ::= first [ solve_store0 | s2_store_wr ].

Section NumA5.
  Variable E : s2env.
  Hypothesis OK : env_ok E.
  Hypothesis SHZ : a_shz E.
  Notation bs := (e_bs E).
  Notation LEN := (blen bs).
  Notation o s := (e_off E (k s)).

  Lemma seg_numa_cmpslow : forall (Q : machine_state -> Prop) (s : st) neg e,
    (-342 <= e <= 308)%Z -> numa_write_k E Q s neg -> numa_fbcall_k E Q s ->
    numa_cmpslow_k E Q s neg e.
  Proof using OK SHZ.
    intros Q s neg e HE KW KFB. unfold numa_cmpslow_k. intros until m1. intros HM.
    s2_env OK.
    nopen HM.
    ngrun.

    if_cases K9;
      first [ (ngrun_to 0xc70e8%Z;
               rewrite (pow5_addr e 163040 5472 HE eq_refl), (pow5_addr e 157568 0 HE eq_refl);
               ngexp_f ltac:(fun pc => lazymatch pc with 0xc7200%Z => fail | 0xc73ac%Z => fail | 0xc77d0%Z => fail | _ => idtac end)
                       ltac:(idtac; lazymatch goal with |- evt _ _ (MS _ _ (Z_to_bv 64 ?pc) _ _ _ _) =>
                               lazymatch pc with 0xc7200%Z =>
                                 ngexp_f ltac:(fun pc => lazymatch pc with 0xc73ac%Z => fail | 0xc77d0%Z => fail | _ => idtac end)
                                         ltac:(idtac; first [ (kapply KW; nclose) | (ngrun_to 0xe9abc%Z; kapply KFB; nclose) ])
                                         ltac:(nkeep ltac:(fun n => lazymatch n with 25%Z => fail | _ => idtac end))
                               end end)
                       ltac:(nkeep ltac:(fun n => lazymatch n with 25%Z => fail | 11%Z => fail | _ => idtac end)))
            | ngexp ltac:(fun pc => lazymatch pc with 0xc73ac%Z => fail | _ => idtac end) ltac:(idtac; kapply KW; nclose) ].
  Qed.

  Lemma seg_numa_cmp : forall (Q : machine_state -> Prop) (s : st) neg e,
    (-342 <= e <= 308)%Z -> numa_write_k E Q s neg -> numa_cmpslow_k E Q s neg e ->
    numa_cmp_k E Q s neg e.
  Proof using OK SHZ.
    intros Q s neg e HE KW KSL. unfold numa_cmp_k. intros until m1. intros HM.
    s2_env OK.
    nopen HM.

    ngrun.
    if_cases K0; first [ (ngrun_to 0xc70c4%Z; kapply KSL; nclose) | idtac ].
    ngrun.
    if_cases K1; zify_cond K1; first [ (ngrun_to 0xc70c4%Z; kapply KSL; nclose) | idtac ].
    ngrun.

        if_cases K2; zify_cond K2;
          first [ (assert (HE2 : (-22 <= e < 0)%Z) by lia;
                   ngrun_to 0xc7374%Z;
                   nreg_set 10%Z (157344 + 8 * - e)%Z;
                   ngexp ltac:(fun pc => lazymatch pc with 0xc73ac%Z => fail | _ => idtac end) ltac:(idtac; kapply KW; nclose))
                | (assert (HE2 : (0 <= e <= 22)%Z) by lia;
                   ngrun_to 0xc70a4%Z;
                   nreg_set 10%Z (157344 + 8 * e)%Z;
                   ngexp ltac:(fun pc => lazymatch pc with 0xc73ac%Z => fail | _ => idtac end) ltac:(idtac; kapply KW; nclose)) ].
  Qed.
End NumA5.
