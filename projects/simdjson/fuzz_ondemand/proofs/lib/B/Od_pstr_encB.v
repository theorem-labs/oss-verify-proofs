(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Zbitwise.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.simdjson.fuzz_ondemand.lib.Lib Require Import Tac Arr Bytes ImageA StoreFast.
From OSSVerify.Proofs.simdjson.fuzz_ondemand.lib.Sj Require Import SjS1Out SjLeaves.
From OSSVerify.Proofs.simdjson.fuzz_ondemand.lib.A Require Import Shadow.
From OSSVerify.Proofs.simdjson.fuzz_ondemand.lib.B Require Import Layout Od_pstr_defsB.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac solve_load ::= first [ solve_load_base | asan_load_hook | ps_load_buf | solve_load_image ].
Local Ltac solve_store ::= first [ ps_solve_store0 | ps_store_wr ].

Section Enc.
  Variable E : psenv.
  Hypothesis OK : psb_ok E.
  Hypothesis SHZ : psb_shz E.
  Local Notation BUF := (q_BUF E) (only parsing).
  Local Notation SB := (q_SB E) (only parsing).
  Local Notation sbo := (q_sbo E) (only parsing).

  Ltac enc_done d w pn HK :=
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?m1 _) =>
      eapply evt_eq; [| eapply (psb_adv E OK d w pn)]; [s1_st_eq | psb_close | exact HK] end.

  Lemma psb_enc1 : forall d pn (cp : word) xra xs1 xa1 xa5 xa6 xs3 mm,
    PSBINV E mm -> (0 <= d)%Z -> (d + 1 <= q_j E - q_i E)%Z -> psb_headk E (d + 1) pn ->
    evt bsegs (psb_post E) (PSB E 0xd2560 xra (Z_to_bv 64 ((SB + sbo + d) / 8 + 2147450880)) xs1 (Z_to_bv 64 (BUF + pn)) xa1 (Z_to_bv 64 (SB + sbo + d))
                              cp xa5 xa6 xs3 mm).
  Proof using OK SHZ.
    intros until mm. intros INV Hd0 Hd HK. psb_open INV. pose proof OK as OK0. psb_env OK0. psb_shzp SHZ.

    pa. pa. if_false. pa. pa. pa. pa. uok.
    enc_done d 1%Z pn HK.
  Qed.

  Lemma psb_enc2 : forall d pn (cp : word) xra xs1 xa1 xa5 xa6 xs3 mm,
    PSBINV E mm -> (0 <= d)%Z -> (d + 2 <= q_j E - q_i E)%Z -> psb_headk E (d + 2) pn ->
    evt bsegs (psb_post E) (PSB E 0xd2590 xra (Z_to_bv 64 ((SB + sbo + d) / 8 + 2147450880)) xs1 (Z_to_bv 64 (BUF + pn)) xa1 (Z_to_bv 64 (SB + sbo + d))
                              cp xa5 xa6 xs3 mm).
  Proof using OK SHZ.
    intros until mm. intros INV Hd0 Hd HK. psb_open INV. pose proof OK as OK0. psb_env OK0. psb_shzp SHZ.
    pa. pa. if_false. pa. pa. pa. pa. utrap. pa. pa. pa. pa. pa. if_false. pa. pa. pa. pa. pa. pa. uok.
    enc_done d 2%Z pn HK.
  Qed.

  Lemma psb_enc3 : forall d pn (cp : word) xra xs1 xa1 xa5 xa6 xs3 mm,
    PSBINV E mm -> (0 <= d)%Z -> (d + 3 <= q_j E - q_i E)%Z -> psb_headk E (d + 3) pn ->
    evt bsegs (psb_post E) (PSB E 0xd25f0 xra (Z_to_bv 64 ((SB + sbo + d) / 8 + 2147450880)) xs1 (Z_to_bv 64 (BUF + pn)) xa1 (Z_to_bv 64 (SB + sbo + d))
                              cp xa5 xa6 xs3 mm).
  Proof using OK SHZ.
    intros until mm. intros INV Hd0 Hd HK. psb_open INV. pose proof OK as OK0. psb_env OK0. psb_shzp SHZ.
    pa. pa. if_false. pa. pa. pa. pa. utrap. pa. pa. pa. pa. pa. if_false. pa. pa. pa. pa. pa. utrap. pa. pa. pa. pa. pa. if_false. pa. pa. pa. pa. pa. pa. uok.
    enc_done d 3%Z pn HK.
  Qed.

  Lemma psb_enc4 : forall d pn (cp : word) xra xa1 xa4 xa5 xa6 xs3 mm,
    PSBINV E mm -> (0 <= d)%Z -> (d + 4 <= q_j E - q_i E)%Z -> psb_headk E (d + 4) pn ->
    evt bsegs (psb_post E) (PSB E 0xd266c xra (Z_to_bv 64 ((SB + sbo + d) / 8 + 2147450880)) cp (Z_to_bv 64 (BUF + pn)) xa1 (Z_to_bv 64 (SB + sbo + d))
                              xa4 xa5 xa6 xs3 mm).
  Proof using OK SHZ.
    intros until mm. intros INV Hd0 Hd HK. psb_open INV. pose proof OK as OK0. psb_env OK0. psb_shzp SHZ.
    pa. pa. if_false. pa. pa. pa. pa. utrap. pa. pa. pa. pa. pa. if_false. pa. pa. pa. pa. pa. utrap. pa. pa. pa. pa. pa. if_false. pa. pa. pa. pa. pa. utrap. pa. pa. pa. pa. pa. if_false. pa. pa. pa. pa. pa. pa. uok.
    enc_done d 4%Z pn HK.
  Qed.
End Enc.
