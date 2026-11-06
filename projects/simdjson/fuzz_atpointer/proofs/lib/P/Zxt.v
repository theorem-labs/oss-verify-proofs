(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.simdjson.fuzz_atpointer.lib.Lib Require Import Tac Arr Bytes Z10q FP.
From OSSVerify.Proofs.simdjson.fuzz_atpointer.lib.Sj Require Import Zpf Zpi Zpa SjTape Zpj Zpk Zpe.
From OSSVerify.Proofs.simdjson.fuzz_atpointer.lib.P Require Import Zwd Z103 Z107 Zwa Zwb
  Zsl Zxc Zxx Zx3.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.
Local Ltac transport_call_extra segs W m m' MU WM ::= s2_timg_call segs W m m' MU WM.
Local Ltac lia ::= s2lia.
Local Ltac tlia ::= s2tlia.
Local Ltac solve_load ::= first [ solve_load_base | s2_load_buf | solve_load_image ].
Local Ltac solve_store ::= first [ solve_store0 | s2_store_wr ].
Local Ltac s2_store_done_wr ::= s2_note_tape; s2_store_done_wr_v2.

Section NumO6.
  Variable E : s2env.
  Hypothesis OK : env_ok E.
  Notation bs := (e_bs E).
  Notation o s := (e_off E (k s)).
  Hypothesis HSLOWF : slowf_stmt_g psegs 0x3cb88 0xab000.
  Hypothesis HPFF : pff_stmt_g psegs 0x3cc10 0xab000.
  Hypothesis HROOM : (e_lo E + 368 + NUM_STACK <= bv_unsigned (e_sp E))%Z.

  Ltac n_close := unfold OSL; s2_close_mem0.

  Lemma seg_numo_slow : forall (Q : machine_state -> Prop) (s : st) neg,
    (0 <= k s <= e_n E)%Z ->
    numo_wr_k E Q s neg (W s) ->
    numo_tail_k E Q s neg (W s) 0x30a5c.
  Proof using OK HSLOWF HROOM.
    intros Q s neg HK KW. unfold numo_tail_k. intros until m1. intros HM.
    pose proof (off_range _ _ (ok_s1 _ OK) (k s) HK) as HOR.
    s2_env OK. unfold OSL in HM.
    s2_open_mem HM.
    srun_to 0x3cb88%Z.
    eapply (numa_call E OK HROOM Q 0x3cb88 9 0 0x30a68 (o s)); cycle 13; [n_close | | exact HSLOWF | lia | reflexivity | lia | reflexivity ..].
    intros flag v yt0 yt1 yt2 ya1 ya2 ya3 ya4 ya5 ya6 ya7 yt3 yt4 yt5 yt6 F' fc' m' HM'.
    clear - OK KW HM'. s2_env OK. s2_open_mem HM'.
    srun_to 0x30a90%Z.
    eapply KW; [s2_a09 | eapply MEMI_OSL; [s2_close_mem0 | reflexivity ..]].
  Qed.

  Lemma seg_numo_fb : forall (Q : machine_state -> Prop) (s : st) neg,
    (0 <= k s <= e_n E)%Z -> exit_k E Q ->
    numo_wr_k E Q s neg (W s) ->
    numo_tail_k E Q s neg (W s) 0x30bb8.
  Proof using OK HPFF HROOM.
    intros Q s neg HK KX KW. unfold numo_tail_k. intros until m1. intros HM.
    pose proof (off_range _ _ (ok_s1 _ OK) (k s) HK) as HOR.
    s2_env OK. unfold OSL in HM.
    s2_open_mem HM.
    srun_to 0x3cc10%Z.
    eapply (numa_call E OK HROOM Q 0x3cc10 0 1 0x30bc4 (o s)); cycle 13; [n_close | | exact HPFF | lia | reflexivity | lia | reflexivity ..].
    intros flag v yt0 yt1 yt2 ya1 ya2 ya3 ya4 ya5 ya6 ya7 yt3 yt4 yt5 yt6 F' fc' m' HM'.
    clear - OK KX KW HM'. s2_env OK. s2_open_mem HM'.
    destruct flag.
    - srun. if_true. srun. if_false. srun. if_true. srun. if_false.
      srun_to 0x2d2c8%Z. s2_err_exit KX. eapply (MEMX_of_MEMI E (e_nxt0 E)); [s2_close_mem0 | reflexivity ..].
    - srun. if_false. srun_to 0x30a90%Z.
      eapply KW; [s2_a09 | eapply MEMI_OSL; [s2_close_mem0 | reflexivity ..]].
  Qed.
End NumO6.
