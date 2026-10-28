(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.Lib Require Import Tac Arr Bytes StoreFast FP ImageA.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.Sj Require Import SjS1Out SjStage2 SjLeaves SjTape SjTapeInv SjTapeList.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.B Require Import Sj_akit Sj_stage2_defs Sj_stage2_tapek Sj_stage2_traps Sj_stage2_guard Sj_tables Sj_stage2_hooks Sj_stage2_numkit Sj_stage2_numkit2 Sj_stage2_numkit2b Sj_stage2_numkit3
  Sj_stage2_numr_defs Sj_stage2_numr_defs2 Sj_stage2_numr_defs3 Sj_stage2_numr_loops Sj_stage2_numr6.
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
Local Ltac g_store_hook ::= s2_note_tape.

Section NumR4b.
  Variable E : s2env.
  Hypothesis OK : env_ok E.
  Hypothesis SHZ : a_shz E.
  Variable CP : Z.
  Hypothesis HCP : cp_ok E CP.
  Hypothesis SHZC : cp_shz E CP.
  Notation bs := (crs (rtxt E)).
  Notation LEN := (blen (rtxt E)).

  Lemma seg_numr_range : forall (Q : machine_state -> Prop) (s : st) neg,
    Z.of_nat (length (e_tws E)) = 1%Z -> rdelAc_k E Q CP -> rdelB_k E Q CP -> (forall v r, num_word v -> rdelC_k (gapp E [v; r] []) Q CP) ->
    (forall e, (-342 <= e <= 308)%Z -> numr_cmp_k E Q CP s neg e) ->
    numr_range_k E Q CP s neg.
  Proof using OK SHZ HCP SHZC.
    intros Q s neg GLT KDA KDB KDC KCMP. unfold numr_range_k. intros until m1. intros HM.
    destruct (word_signed_repr xa4) as (e & HE & ->).
    s2_env OK.
    nopen HM.
    ngrun.
    if_cases K0; zify_cond K0;
      first [ (assert (HER : (-342 <= e <= 308)%Z) by lia; kapply (KCMP e HER); nclose)
            | rexp KDA KDB KDC ].
  Qed.
End NumR4b.
