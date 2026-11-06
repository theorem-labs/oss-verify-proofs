(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.simdjson.fuzz_element.lib.Lib Require Import Tac Arr Bytes StoreFast FP.
From OSSVerify.Proofs.simdjson.fuzz_element.lib.Sj Require Import SjS1Out SjStage2 SjLeaves SjTape SjTapeInv SjTapeList.
From OSSVerify.Proofs.simdjson.fuzz_element.lib.P Require Import Sj_stage2_defs Sj_stage2_tapek Sj_tables Sj_stage2_auto Sj_stage2_auto2
  Sj_stage2_numkit Sj_stage2_numkit2 Sj_stage2_numkit3 Sj_stage2_numr_defs.
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

Section NumR8.
  Variable E : s2env.
  Hypothesis OK : env_ok E.
  Variables (CP : Z) (t : list Z).
  Hypothesis TOK : bytes_ok t.
  Hypothesis CP0 : (0 <= CP)%Z.
  Hypothesis CPHI : (CP + blen t + 64 <= e_lo E)%Z.
  Hypothesis CPSEP : cp_sep E CP t.
  Notation rl := (blen t).

  Ltac n_close := first [ unfold RSL; s2_close_mem0 | eassumption ].
  Ltac cuts7 pc := lazymatch pc with 0x435a0%Z => fail | 0x435a4%Z => fail | 0x43464%Z => fail | 0x41294%Z => fail | 0x43748%Z => fail | _ => idtac end.
  Ltac fin7 KX KI KW KFB :=
    lazymatch goal with |- evt _ _ (MS _ _ (Z_to_bv 64 ?pc) _ _ _ _) =>
      lazymatch pc with
      | 0x435a0%Z => eapply KW; n_close
      | 0x43748%Z => eapply KFB; n_close
      | 0x43464%Z => s2_tape2; s2_kvr KI; [s2_num_word | eapply MEMI_DSL; [s2_close_mem0 | reflexivity ..]]
      | 0x41294%Z => s2_err_exit KX; eapply (MEMX_of_MEMI E (e_nxt0 E)); [s2_close_mem0 | reflexivity ..]
      end end.

  Lemma seg_numr_cmp : forall (Q : machine_state -> Prop) e,
    (-342 <= e <= 308)%Z ->
    numr_tail_k E CP t Q 0x435a0 -> numr_tail_k E CP t Q 0x43748 ->
    numr_cmp_k E CP t Q e.
  Proof using OK TOK CP0 CPHI CPSEP.
    intros Q e HE KW KFB. unfold numr_cmp_k. intros until m1. intros HM CPRO.
    s2_env OK. unfold RSL in HM.
    s2_open_mem HM.
    srun.
    if_cases K0.
    - nexp cuts7 ltac:(idtac; fin7 KW KW KW KFB).
    - destruct (pow5_read m1 e 1376 HE ltac:(left; reflexivity)) as [w1 RD1].
      destruct (pow5_read m1 e 1384 HE ltac:(right; reflexivity)) as [w2 RD2].
      nexp_f ltac:(fun pc => lazymatch pc with 0x42f60%Z => fail | _ => cuts7 pc end)
             ltac:(idtac; lazymatch goal with |- evt _ _ (MS _ _ (Z_to_bv 64 ?pc) _ _ _ _) =>
                     lazymatch pc with 0x42f60%Z => nexp_f cuts7 ltac:(idtac; fin7 KW KW KW KFB) ltac:(fun n => lazymatch n with 24%Z => fail | _ => idtac end) end end)
             ltac:(fun n => lazymatch n with 5%Z => fail | 13%Z => fail | 16%Z => fail | 17%Z => fail | 24%Z => fail | _ => idtac end).
  Qed.
End NumR8.
