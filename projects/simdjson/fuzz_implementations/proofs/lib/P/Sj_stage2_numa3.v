(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.simdjson.fuzz_implementations.lib.Lib Require Import Tac Arr Bytes StoreFast FP.
From OSSVerify.Proofs.simdjson.fuzz_implementations.lib.Sj Require Import SjS1Out SjStage2 SjLeaves SjTape SjTapeInv SjTapeList.
From OSSVerify.Proofs.simdjson.fuzz_implementations.lib.P Require Import Sj_stage2_defs Sj_stage2_tapek Sj_tables Sj_stage2_auto Sj_stage2_auto2
  Sj_stage2_numkit Sj_stage2_numa_defs Sj_stage2_numa_loops.
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

Section NumA3.
  Variable E : s2env.
  Hypothesis OK : env_ok E.
  Notation bs := (e_bs E).
  Notation o s := (e_off E (k s)).

  Ltac n_exit KX := srun_to 0x46ef8%Z; s2_err_exit KX; eapply (MEMX_of_MEMI E (e_nxt0 E)); [s2_close_mem0 | reflexivity ..].
  Ltac n_close := unfold NSL; s2_close_mem0.

  Lemma seg_numa_e98 : forall (Q : machine_state -> Prop) (s : st) neg c,
    numa_flt_k E Q s neg c -> numa_e98_k E Q s neg c.
  Proof using OK.
    intros Q s neg c KF. unfold numa_e98_k. intros until m1. intros HM.
    s2_env OK. unfold NSL in HM.
    s2_open_mem HM.
    srun.
    if_cases K0.
    - srun_to 0x4b4dc%Z. eapply KF. n_close.
    - srun_to 0x4b4dc%Z. eapply KF. n_close.
  Qed.

  Lemma seg_numa_e48 : forall (Q : machine_state -> Prop) (s : st) neg q0,
    (0 <= q0 <= e_len E)%Z -> exit_k E Q ->
    (forall c, (0 <= c < 256)%Z -> numa_e98_k E Q s neg c) ->
    numa_e48_k E Q s neg q0.
  Proof using OK.
    intros Q s neg q0 HQ0 KX KE. unfold numa_e48_k. intros until m1. intros HM.
    pose proof (ok_bytes _ OK) as BOK. pose proof (B_range bs q0 BOK) as HB0.
    s2_env OK. unfold NSL in HM.
    s2_open_mem HM.
    srun.
    if_cases K0; zify_cond K0.
    - assert (HNZ : (q0 < e_len E)%Z) by (apply B_nz_lt; lia).
      srun_to 0x4b488%Z.
      replace (Z_to_bv 64 0) with (Z_to_bv 64 (0 + 0)) at 2 by reflexivity.
      eapply (numa_L4 E OK Q (S (Z.to_nat (e_len E))) q0 0%Z); [exact BUFRO | lia | lia | lia | lia |].
      intros c' ya1 ya5 yt0 HC' HQ'.
      pose proof (B_range bs (q0 + c') BOK) as HBC.
      srun.
      if_cases K1.
      +
        srun_to 0x4b83c%Z.
        eapply (numa_L5 E OK Q (S (Z.to_nat (e_len E))) q0); [exact BUFRO | lia | lia |].
        intros ya1' ya7'.
        srun.
        if_cases K2.
        * eapply (KE _ HBC). n_close.
        * srun_to 0x4b4b8%Z. eapply (KE _ HBC). n_close.
      + eapply (KE _ HBC). n_close.
    - n_exit KX.
  Qed.

  Lemma seg_numa_exp : forall (Q : machine_state -> Prop) (s : st) neg p,
    (0 <= p <= e_len E)%Z ->
    (forall c, (0 <= c < 256)%Z -> numa_flt_k E Q s neg c) -> numa_int_k E Q s neg p ->
    (forall q0, (0 <= q0 <= e_len E)%Z -> numa_e48_k E Q s neg q0) ->
    numa_scan_k E Q s neg 0x4b434 p.
  Proof using OK.
    intros Q s neg p HP KF KI KE. unfold numa_scan_k. intros until m1. intros HM.
    pose proof (ok_bytes _ OK) as BOK. pose proof (B_range bs p BOK) as HB0.
    pose proof (B_range bs (p + 1) BOK) as HB1. pose proof (B_range bs (p + 2) BOK) as HB2.
    s2_env OK. unfold NSL in HM.
    s2_open_mem HM.
    srun.
    if_cases K0; zify_cond K0.
    -
      srun.
      if_cases K1.
      + eapply KI. n_close.
      + eapply (KF _ HB0). n_close.
    - assert (HNZ : (p < e_len E)%Z).
      { apply B_nz_lt. intro E0. rewrite E0 in K0. vm_compute in K0. discriminate K0. }
      srun.
      if_cases K2; zify_cond K2.
      +
        assert (HNZ1 : (p + 1 < e_len E)%Z) by (apply B_nz_lt; lia).
        srun_to 0x4b468%Z.
        replace (e_BUF E + p + 2)%Z with (e_BUF E + (p + 2))%Z by lia.
        eapply (KE (p + 2)%Z); [lia | n_close].
      + srun.
        if_cases K3; zify_cond K3.
        *
          replace (e_BUF E + p + 1)%Z with (e_BUF E + (p + 1))%Z by lia.
          eapply (KE (p + 1)%Z); [lia | n_close].
        *
          assert (HNZ1 : (p + 1 < e_len E)%Z) by (apply B_nz_lt; lia).
          srun_to 0x4b468%Z.
          replace (e_BUF E + p + 2)%Z with (e_BUF E + (p + 2))%Z by lia.
          eapply (KE (p + 2)%Z); [lia | n_close].
  Qed.
End NumA3.
