(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.simdjson.fuzz_print_json.lib.Lib Require Import Tac Arr Bytes StoreFast FP.
From OssFuzzTheorems.Proofs.simdjson.fuzz_print_json.lib.Sj Require Import SjS1Out SjStage2 SjLeaves SjTape SjTapeInv SjTapeList.
From OssFuzzTheorems.Proofs.simdjson.fuzz_print_json.lib.U Require Import Sj_stage2_defs Sj_stage2_tapek Sj_tables Sj_stage2_traps Sj_stage2_guard
  Sj_stage2_numkit Sj_stage2_numkit2 Sj_stage2_numkitr Sj_stage2_numkit3 Sj_stage2_numkit4 Sj_stage2_numkit5 Sj_stage2_numkit6 Sj_stage2_numr_defs Sj_stage2_numr_kit.
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
Local Ltac s2_store_done_wr ::= s2_store_done_wr_v2.
Local Ltac ngstep ::= ngstep_l.

Section NumR9.
  Variable E : s2env.
  Hypothesis OK : env_ok E.
  Variables (CP : Z) (t : list Z).
  Hypothesis TOK : bytes_ok t.
  Hypothesis CP0 : (0 < CP)%Z.
  Hypothesis CPHI : (CP + blen t + 64 <= e_lo E)%Z.
  Hypothesis CPSEP : cp_sep E CP t.
  Notation rl := (blen t).

  Ltac n_close := first [ unfold RSL; s2_close_mem0 | eapply MEMI_RSL; [s2_close_mem0 | reflexivity ..] | eassumption ].
  Local Ltac n_closed_branch a b ::= lazymatch a with 0x474bc%Z => if_false end.
  Ltac cuts9 pc := lazymatch pc with 0x46d6c%Z => fail | 0x45ac4%Z => fail | _ => idtac end.
  Ltac fin9 KW :=
    lazymatch goal with |- evt _ _ (MS _ _ (Z_to_bv 64 ?pc) _ _ _ _) =>
      lazymatch pc with
      | 0x46d6c%Z => eapply KW; n_close
      end end.
  Ltac keepB n := lazymatch n with 9%Z => fail | 19%Z => fail | 26%Z => fail | _ => idtac end.
  Ltac keepA n := lazymatch n with 13%Z => fail | 14%Z => fail | 15%Z => fail | 17%Z => fail | _ => keepB n end.

  Lemma seg_numr_cmp : forall (Q : machine_state -> Prop) e,
    (-342 <= e <= 308)%Z ->
    numr_tail_k E CP t Q 0x46d6c -> numr_tail_k E CP t Q 0x45ac4 ->
    numr_cmp_k E CP t Q e.
  Proof using OK TOK CP0 CPHI CPSEP.
    intros Q e HE KW KB. unfold numr_cmp_k. intros until m1. intros HM CPRO.
    pose proof (crs_blen t) as CBL0.
    s2_env OK. unfold RSL in HM.
    s2_open_mem HM.
    ngrun.
    if_cases K0.
    - ngrun_to 0x459cc%Z. rewrite (p5u_sw e 684 HE) by lia.
      ngrun_cut_f ltac:(fun pc => idtac) keepA.
      if_cases K1.
      + eapply KB; n_close.
      + nstep. nstep. rewrite (p5u_sw e 685 HE) by lia. ngrun_to 0x45ac4%Z.
        eapply KB; n_close.
    -
      ngexp cuts9 ltac:(idtac; fin9 KW).
  Qed.
End NumR9.
