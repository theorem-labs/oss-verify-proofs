(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.simdjson.fuzz_atpointer.lib.Lib Require Import Tac Arr Bytes Z10q FP.
From OSSVerify.Proofs.simdjson.fuzz_atpointer.lib.Sj Require Import Zpf Zpi Zpa SjTape Zpj Zpk.
From OSSVerify.Proofs.simdjson.fuzz_atpointer.lib.U Require Import Zwd Z103 Z107 Z104 Zwk
  Zxc Zxd Zxj Zxf Zxg Zxh Zxi Zyi Zym.
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

Section NumR8.
  Variable E : s2env.
  Hypothesis OK : env_ok E.
  Variables (CP : Z) (t : list Z).
  Hypothesis TOK : bytes_ok t.
  Hypothesis CP0 : (0 < CP)%Z.
  Hypothesis CPHI : (CP + blen t + 64 <= e_lo E)%Z.
  Hypothesis CPSEP : cp_sep E CP t.
  Notation rl := (blen t).

  Ltac n_close := first [ unfold RSL; s2_close_mem0 | eapply MEMI_RSL; [s2_close_mem0 | reflexivity ..] | eassumption ].
  Local Ltac n_closed_branch a b ::= lazymatch a with 0x2fa98%Z => if_false end.
  Ltac cuts8 pc := lazymatch pc with 0x2f348%Z => fail | 0x2fb8c%Z => fail | 0x2fe1c%Z => fail | 0x2e144%Z => fail | _ => idtac end.
  Ltac fin8 KW KFB KAL1 KAL2 :=
    lazymatch goal with |- evt _ _ (MS _ _ (Z_to_bv 64 ?pc) _ _ _ _) =>
      lazymatch pc with
      | 0x2f348%Z => eapply KW; n_close
      | 0x2fb8c%Z => eapply KFB; n_close
      | 0x2fe1c%Z => eapply KAL1; n_close
      | 0x2e144%Z => eapply KAL2; n_close
      end end.
  Ltac keepB n := lazymatch n with 9%Z => fail | 19%Z => fail | 26%Z => fail | _ => idtac end.

  Lemma seg_numr_al : forall (Q : machine_state -> Prop) pc,
    (pc = 0x2fe1c \/ pc = 0x2e144)%Z ->
    numr_tail_k E CP t Q 0x2f348 -> numr_tail_k E CP t Q pc.
  Proof using OK TOK CP0 CPHI CPSEP.
    intros Q pc [-> | ->] KW; unfold numr_tail_k; intros until m1; intros HM CPRO;
      pose proof (crs_blen t) as CBL0; s2_env OK; unfold RSL in HM; s2_open_mem HM;
      ngrun_to 0x2f348%Z; eapply KW; n_close.
  Qed.

  Lemma seg_numr_cmpB : forall (Q : machine_state -> Prop),
    numr_tail_k E CP t Q 0x2f348 -> numr_tail_k E CP t Q 0x2fb8c ->
    numr_tail_k E CP t Q 0x2e0a0.
  Proof using OK TOK CP0 CPHI CPSEP.
    intros Q KW KFB. unfold numr_tail_k. intros until m1. intros HM CPRO.
    pose proof (crs_blen t) as CBL0.
    s2_env OK. unfold RSL in HM.
    s2_open_mem HM.
    pose proof (seg_numr_al Q 0x2fe1c ltac:(left; reflexivity) KW) as KAL1.
    pose proof (seg_numr_al Q 0x2e144 ltac:(right; reflexivity) KW) as KAL2.
    ngexp_f cuts8 ltac:(idtac; fin8 KW KFB KAL1 KAL2) keepB.
  Qed.
End NumR8.
