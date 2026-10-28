(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.simdjson.fuzz_print_json.lib.Lib Require Import Tac Arr Bytes StoreFast FP.
From OssFuzzTheorems.Proofs.simdjson.fuzz_print_json.lib.Sj Require Import SjS1Out SjStage2 SjLeaves SjTape SjTapeInv SjTapeList SjExpDigits.
From OssFuzzTheorems.Proofs.simdjson.fuzz_print_json.lib.U Require Import Sj_stage2_defs Sj_stage2_tapek Sj_tables Sj_stage2_traps Sj_stage2_guard
  Sj_stage2_numkit Sj_stage2_numkit2 Sj_stage2_numkitr Sj_stage2_numkit3 Sj_stage2_numr_defs Sj_stage2_numr_defs2 Sj_stage2_numr_loops.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac lia ::= r_lia.
Local Ltac tlia ::= r_tlia.
Local Ltac solve_load ::= first [ solve_load_base | s2_load_cp | s2_load_sown | solve_load_image ].
Local Ltac solve_store ::= first [ solve_store0 | s2_store_wr ].
Local Ltac s2_store_done_wr ::= s2_note_tape; s2_store_done_wr_v2.

Section NumR4.
  Variable E : s2env.
  Hypothesis OK : env_ok E.
  Variables (CP : Z) (t : list Z).
  Hypothesis TOK : bytes_ok t.
  Hypothesis CP0 : (0 < CP)%Z.
  Hypothesis CPHI : (CP + blen t + 64 <= e_lo E)%Z.
  Hypothesis CPSEP : cp_sep E CP t.
  Notation rl := (blen t).

  Local Ltac n_closed_branch a b ::= lazymatch a with 0x474bc%Z => if_false end.
  Ltac cuts4 pc := lazymatch pc with 0x47014%Z => fail | 0x46de8%Z => fail | 0x43990%Z => fail | 0x46ff8%Z => fail | _ => idtac end.

  Ltac r_s0_sown :=
    lazymatch goal with |- context [sown ?c] =>
      let SR := fresh "SR" in pose proof (sown_range c) as SR;
      let S0 := fresh "S0" in let S1 := fresh "S1" in
      destruct (Z.eq_dec (sown c) 0) as [S0|S1]; [rewrite S0 | replace (sown c) with 1%Z by lia] end;
    match goal with |- context [Z.land ?X 9] => let v := eval vm_compute in (Z.land X 9) in change (Z.land X 9) with v end.

  Lemma seg_numr_i468 : forall (Q : machine_state -> Prop) c,
    (0 <= c < 256)%Z -> rdel_fin0_k E CP Q -> rdel_fin9_k E CP Q ->
    numr_i468_k E CP t Q c.
  Proof using OK TOK CP0 CPHI CPSEP.
    intros Q c HC KF0 KF9. unfold numr_i468_k. intros until m1. intros HM CPRO.
    pose proof (crs_blen t) as CBL0. pose proof (blen_nonneg (e_bs E)) as LEN0.
    s2_env OK. unfold RSL in HM.
    s2_open_mem HM.
    ngrun_to 0x47014%Z.
    r_s0_sown; [ eapply KF0; eapply MEMI_DSL; [s2_close_mem0 | reflexivity ..] | (eapply (KF9 9%Z); [lia | s2_close_memx]) ].
  Qed.

  Lemma seg_numr_int : forall (Q : machine_state -> Prop) p,
    (0 <= p <= rl)%Z -> Z.of_nat (length (e_tws E)) = 1%Z -> rdel_errA_k E CP Q -> rdel_errB_k E CP Q ->
    (forall c, (0 <= c < 256)%Z -> forall v r, num_word v -> numr_i468_k (gapp E [v; r] []) CP t Q c) ->
    numr_int_k E CP t Q p.
  Proof using OK TOK CP0 CPHI CPSEP.
    intros Q p HP GLT KXA KXB KI. unfold numr_int_k. intros until m1. intros HM CPRO.
    pose proof (crs_bytes_ok t TOK) as BOK. pose proof (crs_blen t) as CBL0. pose proof CBL0 as CBL. rewrite zbytes_length in CBL.
    pose proof (B_range (crs t) p BOK) as HB0. pose proof (blen_nonneg (e_bs E)) as LEN0.
    s2_env OK. unfold RSL in HM.
    s2_open_mem HM.
    ngexp cuts4 ltac:(idtac; lazymatch goal with |- evt _ _ (MS _ _ (Z_to_bv 64 ?pc) _ _ _ _) =>
                        lazymatch pc with
                        | 0x43990%Z => eapply KXA; s2_close_memx
                        | 0x46de8%Z => eapply KXB; [s2_errok_code | s2_close_memx]
                        | 0x46ff8%Z => s2_tape2; s2_kvr (KI (B (crs t) p) HB0); [s2_num_word | unfold RSL; s2_close_mem0 | eassumption]
                        end end).
  Qed.
End NumR4.
