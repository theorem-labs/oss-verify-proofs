(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.simdjson.fuzz_atpointer.lib.Lib Require Import Tac Arr Bytes Z10q FP.
From OSSVerify.Proofs.simdjson.fuzz_atpointer.lib.Sj Require Import Zpf Zpi Zpa SjTape Zpj Zpk.
From OSSVerify.Proofs.simdjson.fuzz_atpointer.lib.P Require Import Zwd Z103 Z107 Zwa Zwb
  Zxc Zxx Zy0.
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

Section NumO3.
  Variable E : s2env.
  Hypothesis OK : env_ok E.
  Notation bs := (e_bs E).
  Notation o s := (e_off E (k s)).

  Ltac n_exit KX := srun_to 0x2d2c8%Z; s2_err_exit KX; eapply (MEMX_of_MEMI E (e_nxt0 E)); [s2_close_mem0 | reflexivity ..].
  Ltac n_close := unfold OSL; s2_close_mem0.

  Lemma seg_numo_e98 : forall (Q : machine_state -> Prop) (s : st) neg c,
    numo_flt_k E Q s neg (W s) c -> numo_e98_k E Q s neg (W s) c.
  Proof using OK.
    intros Q s neg c KF. unfold numo_e98_k. intros until m1. intros HM.
    s2_env OK. unfold OSL in HM.
    s2_open_mem HM.
    srun.
    if_cases K0.
    - srun_to 0x306d0%Z. eapply KF. n_close.
    - srun_to 0x306d0%Z. eapply KF. n_close.
  Qed.

  Lemma seg_numo_e48 : forall (Q : machine_state -> Prop) (s : st) neg q0,
    (0 <= q0 <= e_len E)%Z -> exit_k E Q ->
    (forall c, (0 <= c < 256)%Z -> numo_e98_k E Q s neg (W s) c) ->
    numo_e48_k E Q s neg (W s) q0.
  Proof using OK.
    intros Q s neg q0 HQ0 KX KE. unfold numo_e48_k. intros until m1. intros HM.
    pose proof (ok_bytes _ OK) as BOK. pose proof (B_range bs q0 BOK) as HB0.
    s2_env OK. unfold OSL in HM.
    s2_open_mem HM.
    srun.
    if_cases K0; zify_cond K0.
    - assert (HNZ : (q0 < e_len E)%Z) by (apply B_nz_lt; lia).
      srun_to 0x30680%Z.
      replace (Z_to_bv 64 0) with (Z_to_bv 64 (0 + 0)) at 2 by reflexivity.
      eapply (numo_L4 E OK Q (S (Z.to_nat (e_len E))) q0 0%Z); [exact BUFRO | lia | lia | lia | lia |].
      intros c' ya1 ya5 yt0 HC' HQ'.
      pose proof (B_range bs (q0 + c') BOK) as HBC.
      srun.
      if_cases K1.
      +
        srun_to 0x30a40%Z.
        eapply (numo_L5 E OK Q (S (Z.to_nat (e_len E))) q0); [exact BUFRO | lia | lia |].
        intros ya1' ya7'.
        srun.
        if_cases K2.
        * eapply (KE _ HBC). n_close.
        * srun_to 0x306b0%Z. eapply (KE _ HBC). n_close.
      + eapply (KE _ HBC). n_close.
    - n_exit KX.
  Qed.

  Lemma seg_numo_exp : forall (Q : machine_state -> Prop) (s : st) neg p,
    (0 <= p <= e_len E)%Z ->
    (forall c, (0 <= c < 256)%Z -> numo_flt_k E Q s neg (W s) c) -> numo_int_k E Q s neg (W s) p ->
    (forall q0, (0 <= q0 <= e_len E)%Z -> numo_e48_k E Q s neg (W s) q0) ->
    numo_scan_k E Q s neg (W s) 0x30630 p.
  Proof using OK.
    intros Q s neg p HP KF KI KE. unfold numo_scan_k. intros until m1. intros HM.
    pose proof (ok_bytes _ OK) as BOK. pose proof (B_range bs p BOK) as HB0.
    pose proof (B_range bs (p + 1) BOK) as HB1. pose proof (B_range bs (p + 2) BOK) as HB2.
    s2_env OK. unfold OSL in HM.
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
        srun_to 0x30660%Z.
        replace (e_BUF E + p + 2)%Z with (e_BUF E + (p + 2))%Z by lia.
        eapply (KE (p + 2)%Z); [lia | n_close].
      + srun.
        if_cases K3; zify_cond K3.
        *
          replace (e_BUF E + p + 1)%Z with (e_BUF E + (p + 1))%Z by lia.
          eapply (KE (p + 1)%Z); [lia | n_close].
        *
          assert (HNZ1 : (p + 1 < e_len E)%Z) by (apply B_nz_lt; lia).
          srun_to 0x30660%Z.
          replace (e_BUF E + p + 2)%Z with (e_BUF E + (p + 2))%Z by lia.
          eapply (KE (p + 2)%Z); [lia | n_close].
  Qed.
End NumO3.
