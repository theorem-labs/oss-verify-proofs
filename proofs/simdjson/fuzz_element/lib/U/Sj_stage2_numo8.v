(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Lib Require Import Tac Arr Bytes StoreFast FP.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Sj Require Import SjS1Out SjStage2 SjLeaves SjTape SjTapeInv SjTapeList.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.U Require Import Sj_stage2_defs Sj_stage2_tapek Sj_tables Sj_stage2_traps Sj_stage2_guard
  Sj_stage2_numkit Sj_stage2_numkit2 Sj_stage2_numkit3 Sj_stage2_numkit4 Sj_stage2_numkit5 Sj_stage2_numkit6 Sj_stage2_numo_defs.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac lia ::= s2lia.
Local Ltac tlia ::= s2tlia.
Local Ltac solve_load ::= first [ solve_load_base | s2_load_buf | s2_load_sown | s2_load_pow | solve_load_image ].
Local Ltac solve_store ::= first [ solve_store0 | s2_store_wr ].
Local Ltac s2_store_done_wr ::= s2_store_done_wr_v2.
Local Ltac ngstep ::= ngstep_l.

Section NumO8.
  Variable E : s2env.
  Hypothesis OK : env_ok E.
  Notation bs := (e_bs E).

  Local Ltac n_closed_branch a b ::= fail.
  Ltac cuts8 pc := lazymatch pc with 0x4bd84%Z => fail | 0x4bf48%Z => fail | _ => idtac end.
  Ltac fin8 KW KFB :=
    lazymatch goal with |- evt _ _ (MS _ _ (Z_to_bv 64 ?pc) _ _ _ _) =>
      lazymatch pc with
      | 0x4bd84%Z => eapply KW; eapply MEMI_NSL; [s2_close_mem0 | reflexivity ..]
      | 0x4bf48%Z => eapply KFB; eapply MEMI_NSL; [s2_close_mem0 | reflexivity ..]
      end end.
  Ltac keepB n := lazymatch n with 9%Z => fail | 21%Z => fail | 25%Z => fail | _ => idtac end.
  Ltac keepA n := lazymatch n with 10%Z => fail | 14%Z => fail | 15%Z => fail | 16%Z => fail | _ => keepB n end.

  Lemma seg_numo_cmpB : forall (Q : machine_state -> Prop) (s : st) neg,
    numo_tailm_k E Q s neg 0x4bd84 -> numo_tailm_k E Q s neg 0x4bf48 ->
    numo_tailm_k E Q s neg 0x4ba7c.
  Proof using OK.
    intros Q s neg KW KFB. unfold numo_tailm_k. intros until m1. intros HM.
    s2_env OK. unfold NSL in HM.
    s2_open_mem HM.
    ngexp_f cuts8 ltac:(idtac; fin8 KW KFB) keepB.
  Qed.
End NumO8.
