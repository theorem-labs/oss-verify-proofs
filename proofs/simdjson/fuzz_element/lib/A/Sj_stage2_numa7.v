(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Lib Require Import Tac Arr Bytes StoreFast FP ImageA.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Sj Require Import SjS1Out SjStage2 SjLeaves SjTape SjTapeInv SjTapeList.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.A Require Import Sj_akit Sj_stage2_defs Sj_stage2_tapek Sj_stage2_traps Sj_stage2_guard Sj_tables Sj_stage2_hooks Sj_stage2_numkit
  Sj_stage2_numkit2 Sj_stage2_numa_defs Sj_stage2_numa_loops.
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

Section NumA7.
  Variable E : s2env.
  Hypothesis OK : env_ok E.
  Hypothesis SHZ : a_shz E.
  Notation bs := (e_bs E).
  Notation LEN := (blen bs).

  Lemma seg_numa_slowret : forall (Q : machine_state -> Prop) (s : st) r v,
    (0 <= W s)%Z -> (W s + 2 <= e_tcap E)%Z -> Z.of_nat (length (e_tws E)) = W s -> (forall vw rw, num_word vw -> numa_fin_k (gapp E [vw; rw] []) Q s 0 r) -> numa_slowret_k E Q s r v.
  Proof using OK SHZ.
    intros Q s r v HW0 HW GLT KF. unfold numa_slowret_k. intros until m1. intros HM.
    s2_env OK.
    nopen HM.
    ngrun_to 0xc73ec%Z.
    n_tape2. s2_kvr_kapply KF. nclose.
  Qed.

  Lemma seg_numa_fbret : forall (Q : machine_state -> Prop) (s : st) r v,
    (r = 0 \/ r = 1)%Z -> exit_k E Q -> numa_write_k E Q s 0 -> numa_fbret_k E Q s r v.
  Proof using OK SHZ.
    intros Q s r v HR KX KW. unfold numa_fbret_k. intros until m1. intros HM.
    s2_env OK.
    nopen HM.
    destruct HR as [-> | ->].
    -
      repeat (ngrun_to 0xcb1dc%Z; gdec).
      nexit KX.
    - ngrun. first [ if_true | idtac ].
      kapply KW. nclose.
  Qed.
End NumA7.
