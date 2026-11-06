(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Zbitwise.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.simdjson.fuzz_ondemand.lib.Lib Require Import Tac Arr Bytes StoreFast.
From OSSVerify.Proofs.simdjson.fuzz_ondemand.lib.Sj Require Import SjS1Out SjLeaves.
From OSSVerify.Proofs.simdjson.fuzz_ondemand.lib.P Require Import Od_pstr_defs.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac solve_load ::= first [ solve_load_base | ps_load_buf | solve_load_image ].
Local Ltac solve_store ::= first [ ps_solve_store0 | ps_store_wr ].

Section Enc.
  Variable E : psenv.
  Hypothesis OK : ps_ok E.
  Local Notation BUF := (q_BUF E) (only parsing).
  Local Notation SB := (q_SB E) (only parsing).
  Local Notation sbo := (q_sbo E) (only parsing).

  Definition ps_headk (d' pn : Z) : Prop :=
    forall xra xs7 xs8 xs9 xs10 xs11 mm', PSINV E mm' ->
      evt psegs (ps_post E) (PSS E 0x397c0 xra (Z_to_bv 64 (SB + sbo + d')) (Z_to_bv 64 (BUF + pn)) xs7 xs8 xs9 xs10 xs11 mm').

  Ltac enc_done HK :=
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?m1 _) =>
      eapply evt_eq; [| eapply HK]; [s1_st_eq | ps_close ] end.

  Lemma ps_enc1 : forall d pn (cp : word) xra xs8 xs9 xs10 xs11 mm,
    PSINV E mm -> (0 <= d)%Z -> (d + 1 <= q_j E - q_i E)%Z -> ps_headk (d + 1) pn ->
    evt psegs (ps_post E) (PSS E 0x397b4 xra (Z_to_bv 64 (SB + sbo + d)) cp (Z_to_bv 64 (BUF + pn)) xs8 xs9 xs10 xs11 mm).
  Proof using OK.
    intros until mm. intros INV Hd0 Hd HK. ps_open INV. pose proof OK as OK0. ps_env OK0.
    pstep. pstep. pstep.
    enc_done HK.
  Qed.

  Lemma ps_enc2 : forall d pn (cp : word) xra xs8 xs9 xs10 xs11 mm,
    PSINV E mm -> (0 <= d)%Z -> (d + 2 <= q_j E - q_i E)%Z -> ps_headk (d + 2) pn ->
    evt psegs (ps_post E) (PSS E 0x398f8 xra (Z_to_bv 64 (SB + sbo + d)) cp (Z_to_bv 64 (BUF + pn)) xs8 xs9 xs10 xs11 mm).
  Proof using OK.
    intros until mm. intros INV Hd0 Hd HK. ps_open INV. pose proof OK as OK0. ps_env OK0.
    do 4 pstep.
    pstep. pstep. pstep. pstep. pstep.
    enc_done HK.
  Qed.

  Lemma ps_enc3 : forall d pn (cp : word) xra xs8 xs9 xs10 xs11 mm,
    PSINV E mm -> (0 <= d)%Z -> (d + 3 <= q_j E - q_i E)%Z -> ps_headk (d + 3) pn ->
    evt psegs (ps_post E) (PSS E 0x39924 xra (Z_to_bv 64 (SB + sbo + d)) cp (Z_to_bv 64 (BUF + pn)) xs8 xs9 xs10 xs11 mm).
  Proof using OK.
    intros until mm. intros INV Hd0 Hd HK. ps_open INV. pose proof OK as OK0. ps_env OK0.
    do 7 pstep.
    pstep. pstep. pstep. pstep. pstep. pstep.
    enc_done HK.
  Qed.

  Lemma ps_enc4 : forall d pn (cp : word) xra xa1 xs9 xs10 xs11 mm,
    PSINV E mm -> (0 <= d)%Z -> (d + 4 <= q_j E - q_i E)%Z -> ps_headk (d + 4) pn ->
    evt psegs (ps_post E) (PSS E 0x39968 xra (Z_to_bv 64 (SB + sbo + d)) xa1 (Z_to_bv 64 (BUF + pn)) cp xs9 xs10 xs11 mm).
  Proof using OK.
    intros until mm. intros INV Hd0 Hd HK. ps_open INV. pose proof OK as OK0. ps_env OK0.
    do 10 pstep.
    pstep. pstep. pstep. pstep. pstep. pstep. pstep.
    enc_done HK.
  Qed.
End Enc.
