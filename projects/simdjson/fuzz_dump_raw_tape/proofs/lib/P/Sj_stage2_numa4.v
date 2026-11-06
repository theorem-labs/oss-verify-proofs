(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.simdjson.fuzz_dump_raw_tape.lib.Lib Require Import Tac Arr Bytes StoreFast FP.
From OSSVerify.Proofs.simdjson.fuzz_dump_raw_tape.lib.Sj Require Import SjS1Out SjStage2 SjLeaves SjTape SjTapeInv SjTapeList.
From OSSVerify.Proofs.simdjson.fuzz_dump_raw_tape.lib.P Require Import Sj_stage2_defs Sj_stage2_tapek Sj_tables Sj_stage2_auto Sj_stage2_auto2
  Sj_stage2_numkit Sj_stage2_numa_defs.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac lia ::= s2lia.
Local Ltac tlia ::= s2tlia.
Local Ltac solve_load ::= first [ solve_load_base | s2_load_buf | solve_load_image ].
Local Ltac solve_store ::= first [ solve_store0 | s2_store_wr ].
Local Ltac s2_store_done_wr ::= s2_note_tape; s2_store_done_wr_v2.

Section NumA4.
  Variable E : s2env.
  Hypothesis OK : env_ok E.
  Notation bs := (e_bs E).

  Ltac n_exit KX := srun_to 0x409cc%Z; s2_err_exit KX; eapply (MEMX_of_MEMI E (e_nxt0 E)); [s2_close_mem0 | reflexivity ..].
  Ltac n_close := unfold NSL; s2_close_mem0.
  Local Ltac n_closed_branch a b ::= lazymatch a with 0x45398%Z => if_false end.

  Lemma seg_numa_join : forall (Q : machine_state -> Prop) (s : st) neg,
    lab_k E Q 0x446b4 (mkst (k s + 1) (depth s) (W s + 2) (sb s) (scopes s)) ->
    numa_join_k E Q s neg.
  Proof using OK.
    intros Q s neg KC. unfold numa_join_k. intros until m1. intros HM.
    s2_env OK. unfold NSL in HM.
    s2_open_mem HM.
    srun. if_true.
    eapply KC. cbn [scopes].
    eapply MEMJ_of_MEMI; [s2_close_mem0 | reflexivity ..].
  Qed.

  Lemma seg_numa_i3f4 : forall (Q : machine_state -> Prop) (s : st) neg c,
    (0 <= c < 256)%Z -> exit_k E Q -> numa_join_k E Q s neg -> numa_i3f4_k E Q s neg c.
  Proof using OK.
    intros Q s neg c HC KX KJ. unfold numa_i3f4_k. intros until m1. intros HM.
    s2_env OK. unfold NSL in HM.
    s2_open_mem HM.
    pose proof (sown_read m1 c MI HC) as RS. unfold T_SOWN in RS. pose proof (sown_range c) as HSR.
    srun.
    if_cases K0.
    - replace (e_TAPE E + 8 * W s + 16)%Z with (e_TAPE E + 8 * (W s + 2))%Z by lia.
      eapply KJ. n_close.
    - n_exit KX.
  Qed.

  Lemma seg_numa_int : forall (Q : machine_state -> Prop) (s : st) neg p,
    (0 <= p <= e_len E)%Z -> (0 <= W s)%Z -> (W s + 2 <= e_tcap E)%Z -> Z.of_nat (length (e_tws E)) = W s -> exit_k E Q ->
    (forall c, (0 <= c < 256)%Z -> forall v r, num_word v -> numa_i3f4_k (gapp E [v; r] []) Q s neg c) ->
    numa_int_k E Q s neg p.
  Proof using OK.
    intros Q s neg p HP HW0 HW GLT KX KI. unfold numa_int_k. intros until m1. intros HM.
    pose proof (ok_bytes _ OK) as BOK. pose proof (B_range bs p BOK) as HB0.
    s2_env OK. unfold NSL in HM.
    s2_open_mem HM.
    nexp ltac:(fun pc => lazymatch pc with 0x452e8%Z => fail | 0x409cc%Z => fail | _ => idtac end)
         ltac:(idtac; lazymatch goal with |- evt _ _ (MS _ _ (Z_to_bv 64 ?pc) _ _ _ _) =>
                 lazymatch pc with
                 | 0x452e8%Z => s2_tape2; s2_kvr (KI (B bs p) HB0); [s2_num_word | n_close]
                 | 0x409cc%Z => s2_err_exit KX; eapply (MEMX_of_MEMI E (e_nxt0 E)); [s2_close_mem0 | reflexivity ..]
                 end end).
  Qed.
End NumA4.
