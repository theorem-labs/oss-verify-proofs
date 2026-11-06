(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Zbitwise.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.simdjson.fuzz_ondemand.lib.Lib Require Import Tac Arr Bytes StoreFast.
From OSSVerify.Proofs.simdjson.fuzz_ondemand.lib.Sj Require Import SjS1Out SjLeaves.
From OSSVerify.Proofs.simdjson.fuzz_ondemand.lib.U Require Import Od_pstr_defs.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac solve_load ::= first [ solve_load_base | ps_load_buf | solve_load_image ].
Local Ltac solve_store ::= first [ ps_solve_store0 | ps_store_wr ].

Ltac utrap G := if_cases G; zify_cond G; [exfalso; rewrite ?lxor_ones64 in G by lia; lia|].
Ltac uok G := if_cases G; zify_cond G; [|exfalso; rewrite ?lxor_ones64 in G by lia; lia].

Section Enc.
  Variable E : psenv.
  Hypothesis OK : psu_ok E.
  Local Notation BUF := (q_BUF E) (only parsing).
  Local Notation SB := (q_SB E) (only parsing).
  Local Notation sbo := (q_sbo E) (only parsing).

  Ltac enc_done d w pn HK :=
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?m1 _) =>
      eapply evt_eq; [| eapply (psu_adv E OK d w pn)]; [s1_st_eq | psu_close | exact HK] end.

  Lemma psu_enc1 : forall d pn (cp : word) xra xs1 xs11 xt4 xt5 mm,
    PSUINV E mm -> (0 <= d)%Z -> (d + 1 <= q_j E - q_i E)%Z -> psu_headk E (d + 1) pn ->
    evt usegs (psu_post E) (PSU E 0x43e24 xra xs1 cp (Z_to_bv 64 (SB + sbo + d)) (Z_to_bv 64 (BUF + pn)) xs11 xt4 xt5 mm).
  Proof using OK.
    intros until mm. intros INV Hd0 Hd HK. psu_open INV. pose proof OK as OK0. psu_env OK0.
    pstep. pstep. pstep. pstep. uok G1.
    enc_done d 1%Z pn HK.
  Qed.

  Lemma psu_enc2 : forall d pn (cp : word) xra xs1 xs11 xt4 xt5 mm,
    PSUINV E mm -> (0 <= d)%Z -> (d + 2 <= q_j E - q_i E)%Z -> psu_headk E (d + 2) pn ->
    evt usegs (psu_post E) (PSU E 0x43e84 xra xs1 cp (Z_to_bv 64 (SB + sbo + d)) (Z_to_bv 64 (BUF + pn)) xs11 xt4 xt5 mm).
  Proof using OK.
    intros until mm. intros INV Hd0 Hd HK. psu_open INV. pose proof OK as OK0. psu_env OK0.
    pstep. pstep. pstep. pstep. utrap G0.
    pstep. pstep. pstep. pstep. pstep. pstep. uok G1.
    enc_done d 2%Z pn HK.
  Qed.

  Lemma psu_enc3 : forall d pn (cp : word) xra xs1 xs11 xt4 xt5 mm,
    PSUINV E mm -> (0 <= d)%Z -> (d + 3 <= q_j E - q_i E)%Z -> psu_headk E (d + 3) pn ->
    evt usegs (psu_post E) (PSU E 0x43e40 xra xs1 cp (Z_to_bv 64 (SB + sbo + d)) (Z_to_bv 64 (BUF + pn)) xs11 xt4 xt5 mm).
  Proof using OK.
    intros until mm. intros INV Hd0 Hd HK. psu_open INV. pose proof OK as OK0. psu_env OK0.
    pstep. pstep. pstep. pstep. utrap G0.
    pstep. pstep. pstep. pstep. pstep. utrap G2.
    pstep. pstep. pstep. pstep. pstep. pstep. uok G1.
    enc_done d 3%Z pn HK.
  Qed.

  Lemma psu_enc4 : forall d pn (cp : word) xra xs1 xa1 xt4 xt5 mm,
    PSUINV E mm -> (0 <= d)%Z -> (d + 4 <= q_j E - q_i E)%Z -> psu_headk E (d + 4) pn ->
    evt usegs (psu_post E) (PSU E 0x43ec4 xra xs1 xa1 (Z_to_bv 64 (SB + sbo + d)) (Z_to_bv 64 (BUF + pn)) cp xt4 xt5 mm).
  Proof using OK.
    intros until mm. intros INV Hd0 Hd HK. psu_open INV. pose proof OK as OK0. psu_env OK0.
    pstep. pstep. pstep. pstep. utrap G0.
    pstep. pstep. pstep. pstep. pstep. utrap G2.
    pstep. pstep. pstep. pstep. pstep. utrap G3.
    pstep. pstep. pstep. pstep. pstep. pstep. uok G1.
    enc_done d 4%Z pn HK.
  Qed.
End Enc.
