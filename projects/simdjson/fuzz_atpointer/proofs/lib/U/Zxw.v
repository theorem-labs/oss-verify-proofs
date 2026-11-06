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
  Zxc Zxd Zxf Zxg Zxh Zxi Zxx.
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

Section NumO9.
  Variable E : s2env.
  Hypothesis OK : env_ok E.
  Notation bs := (e_bs E).

  Local Ltac n_closed_branch a b ::= fail.
  Ltac cuts8 pc := lazymatch pc with 0x341a4%Z => fail | 0x34368%Z => fail | 0x33e9c%Z => fail | _ => idtac end.
  Ltac fin8 KW KFB :=
    lazymatch goal with |- evt _ _ (MS _ _ (Z_to_bv 64 ?pc) _ _ _ _) =>
      lazymatch pc with
      | 0x341a4%Z => eapply KW; eapply MEMI_NSL; [s2_close_mem0 | reflexivity ..]
      | 0x34368%Z => eapply KFB; eapply MEMI_NSL; [s2_close_mem0 | reflexivity ..]
      end end.
  Ltac keepB n := lazymatch n with 9%Z => fail | 21%Z => fail | 25%Z => fail | _ => idtac end.
  Ltac keepA n := lazymatch n with 10%Z => fail | 14%Z => fail | 15%Z => fail | 16%Z => fail | _ => keepB n end.

  Lemma seg_numo_cmp : forall (Q : machine_state -> Prop) (s : st) neg e,
    (-342 <= e <= 308)%Z ->
    numo_tailm_k E Q s neg 0x341a4 -> numo_tailm_k E Q s neg 0x33e9c ->
    numo_cmp_k E Q s neg e.
  Proof using OK.
    intros Q s neg e HE KW KB. unfold numo_cmp_k. intros until m1. intros HM.
    s2_env OK. unfold NSL in HM.
    s2_open_mem HM.
    ngrun.
    if_cases K0.
    -
      ngexp cuts8 ltac:(idtac; fin8 KW KW).
    - ngrun_to 0x33d9c%Z. rewrite (p5u_sw e 684 HE) by lia.
      ngrun_cut_f ltac:(fun pc => idtac) keepA.
      if_cases K1.
      + eapply KB. eapply MEMI_NSL; [s2_close_mem0 | reflexivity ..].
      + nstep. nstep. rewrite (p5u_sw e 685 HE) by lia. ngrun_to 0x33e9c%Z.
        eapply KB. eapply MEMI_NSL; [s2_close_mem0 | reflexivity ..].
  Qed.
End NumO9.
