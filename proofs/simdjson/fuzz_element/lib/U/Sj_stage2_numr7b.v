(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Lib Require Import Tac Arr Bytes StoreFast FP.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Sj Require Import SjS1Out SjStage2 SjLeaves SjTape SjTapeInv SjTapeList.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.U Require Import Sj_stage2_defs Sj_stage2_tapek Sj_tables Sj_stage2_traps Sj_stage2_guard
  Sj_stage2_numkit Sj_stage2_numkit2 Sj_stage2_numkitr Sj_stage2_numkit3 Sj_stage2_numkit4 Sj_stage2_numkit6 Sj_stage2_numr_defs Sj_stage2_numr_kit.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac lia ::= r_lia.
Local Ltac tlia ::= r_tlia.
Local Ltac solve_load ::= first [ solve_load_base | s2_load_cp | s2_load_sown | s2_load_pow | solve_load_image ].
Local Ltac solve_store ::= first [ solve_store0 | s2_store_wr ].
Local Ltac s2_store_done_wr ::= s2_note_tape; s2_store_done_wr_v2.
Local Ltac ngstep ::= ngstep_l.

Section NumR7b.
  Variable E : s2env.
  Hypothesis OK : env_ok E.
  Variables (CP : Z) (t : list Z).
  Hypothesis TOK : bytes_ok t.
  Hypothesis CP0 : (0 < CP)%Z.
  Hypothesis CPHI : (CP + blen t + 64 <= e_lo E)%Z.
  Hypothesis CPSEP : cp_sep E CP t.
  Notation rl := (blen t).

  Ltac n_close := first [ unfold RSL; s2_close_mem0 | eapply MEMI_RSL; [s2_close_mem0 | reflexivity ..] | eassumption ].
  Local Ltac n_closed_branch a b ::= lazymatch a with 0x47678%Z => if_false end.
  Ltac cuts7 pc := lazymatch pc with 0x46f28%Z => fail | _ => r_cuts pc end.
  Ltac fin7 KXA KXB KF0 KF9 KW :=
    lazymatch goal with |- evt _ _ (MS _ _ (Z_to_bv 64 ?pc) _ _ _ _) =>
      lazymatch pc with
      | 0x46f28%Z => eapply KW; n_close
      | _ => r_leaf KXA KXB KF0 KF9
      end end.

  Lemma seg_numr_zero : forall (Q : machine_state -> Prop),
    Z.of_nat (length (e_tws E)) = 1%Z -> rdel_errA_k E CP Q -> rdel_errB_k E CP Q -> (forall v r, num_word v -> rdel_fin0_k (gapp E [v; r] []) CP Q) -> rdel_fin9_k E CP Q ->
    numr_tail_k E CP t Q 0x45af4.
  Proof using OK TOK CP0 CPHI CPSEP.
    intros Q GLT KXA KXB KF0 KF9. unfold numr_tail_k. intros until m1. intros HM CPRO.
    pose proof (crs_blen t) as CBL0. pose proof (blen_nonneg (e_bs E)) as LEN0.
    s2_env OK. unfold RSL in HM.
    s2_open_mem HM.
    ngexp r_cuts ltac:(idtac; r_leaf KXA KXB KF0 KF9).
  Qed.
End NumR7b.
