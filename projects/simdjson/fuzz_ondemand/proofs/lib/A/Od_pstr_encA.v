(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Zbitwise.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.simdjson.fuzz_ondemand.lib.Lib Require Import Tac Arr Bytes ImageA StoreFast.
From OSSVerify.Proofs.simdjson.fuzz_ondemand.lib.Sj Require Import SjS1Out SjLeaves.
From OSSVerify.Proofs.simdjson.fuzz_ondemand.lib.A Require Import Layout Shadow Od_pstr_defsA.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac solve_load ::= first [ solve_load_base | asan_load_hook | ps_load_buf | solve_load_image ].
Local Ltac solve_store ::= first [ ps_solve_store0 | ps_store_wr ].
Ltac pa := zstep; anorm; psnorm; ps_store_done_wr.

Section Enc.
  Variable E : psenv.
  Hypothesis OK : psa_ok E.
  Hypothesis SHZ : psa_shz E.
  Local Notation BUF := (q_BUF E) (only parsing).
  Local Notation SB := (q_SB E) (only parsing).
  Local Notation sbo := (q_sbo E) (only parsing).

  Definition psa_headk (d' pn : Z) : Prop :=
    forall xra xa2 xa4 xa5 xt1 xt3 xs8 xs9 xs11 mm', PSAINV E mm' ->
      evt asegs (psa_post E) (PSA E 0xc4ab4 xra (Z_to_bv 64 (SB + sbo + d')) (Z_to_bv 64 (BUF + pn)) xa2 xa4 xa5 xt1 xt3 xs8 xs9 xs11 mm').

  Ltac enc_done HK :=
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?m1 _) =>
      eapply evt_eq; [| eapply HK]; [s1_st_eq | psa_close ] end.

  Lemma psa_enc1 : forall d pn (cp : word) xra xa1 xa5 xt1 xt3 xs8 xs9 mm,
    PSAINV E mm -> (0 <= d)%Z -> (d + 1 <= q_j E - q_i E)%Z -> psa_headk (d + 1) pn ->
    evt asegs (psa_post E) (PSA E 0xc4d94 xra (Z_to_bv 64 (SB + sbo + d)) xa1 (Z_to_bv 64 (BUF + pn)) cp xa5 xt1 xt3 xs8 xs9
                              (Z_to_bv 64 ((SB + sbo + d) / 8 + 2147450880)) mm).
  Proof using OK SHZ.
    intros until mm. intros INV Hd0 Hd HK. psa_open INV. pose proof OK as OK0. psa_env OK0. psa_shzp SHZ.
    pa. pa. if_false. pa. pa. pa. pa.
    enc_done HK.
  Qed.

  Lemma psa_enc2 : forall d pn (cp : word) xra xa1 xa5 xt1 xt3 xs8 xs9 mm,
    PSAINV E mm -> (0 <= d)%Z -> (d + 2 <= q_j E - q_i E)%Z -> psa_headk (d + 2) pn ->
    evt asegs (psa_post E) (PSA E 0xc4e1c xra (Z_to_bv 64 (SB + sbo + d)) xa1 (Z_to_bv 64 (BUF + pn)) cp xa5 xt1 xt3 xs8 xs9
                              (Z_to_bv 64 ((SB + sbo + d) / 8 + 2147450880)) mm).
  Proof using OK SHZ.
    intros until mm. intros INV Hd0 Hd HK. psa_open INV. pose proof OK as OK0. psa_env OK0. psa_shzp SHZ.
    pa. pa. if_false. pa. pa. pa. pa.
    pa. pa. pa. pa. if_false. pa. pa. pa.
    pa. pa. pa. pa. pa.
    enc_done HK.
  Qed.

  Lemma psa_enc3 : forall d pn (cp : word) xra xa1 xa5 xt1 xt3 xs8 xs9 mm,
    PSAINV E mm -> (0 <= d)%Z -> (d + 3 <= q_j E - q_i E)%Z -> psa_headk (d + 3) pn ->
    evt asegs (psa_post E) (PSA E 0xc4db4 xra (Z_to_bv 64 (SB + sbo + d)) xa1 (Z_to_bv 64 (BUF + pn)) cp xa5 xt1 xt3 xs8 xs9
                              (Z_to_bv 64 ((SB + sbo + d) / 8 + 2147450880)) mm).
  Proof using OK SHZ.
    intros until mm. intros INV Hd0 Hd HK. psa_open INV. pose proof OK as OK0. psa_env OK0. psa_shzp SHZ.
    pa. pa. if_false. pa. pa. pa. pa.
    pa. pa. pa. pa. if_false. pa. pa. pa. pa. pa.
    pa. pa. pa. pa. if_false. pa. pa. pa.
    pa. pa. pa.
    enc_done HK.
  Qed.

  Lemma psa_enc4 : forall d pn (cp : word) xa1 xa4 xa5 xt1 xt3 xs8 xs9 mm,
    PSAINV E mm -> (0 <= d)%Z -> (d + 4 <= q_j E - q_i E)%Z -> psa_headk (d + 4) pn ->
    evt asegs (psa_post E) (PSA E 0xc4e6c cp (Z_to_bv 64 (SB + sbo + d)) xa1 (Z_to_bv 64 (BUF + pn)) xa4 xa5 xt1 xt3 xs8 xs9
                              (Z_to_bv 64 ((SB + sbo + d) / 8 + 2147450880)) mm).
  Proof using OK SHZ.
    intros until mm. intros INV Hd0 Hd HK. psa_open INV. pose proof OK as OK0. psa_env OK0. psa_shzp SHZ.
    pa. pa. if_false. pa. pa. pa. pa.
    pa. pa. pa. pa. if_false. pa. pa. pa. pa. pa.
    pa. pa. pa. pa. if_false. pa. pa. pa. pa. pa.
    pa. pa. pa. pa. if_false. pa. pa. pa.
    pa. pa. pa. pa.
    enc_done HK.
  Qed.
End Enc.
