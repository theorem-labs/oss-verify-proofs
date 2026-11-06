(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: the contract of check_groupa on fuzz_grant.asan, written for libreac/fuzz_grant with proof steps adapted from proofs/cgif/cgif_file_fuzzer/lib/A/ACe6.v. *)
(* check_groupa (fuzz_grant.c:116, 0x81b70 in fuzz_grant.asan): the contract of the ASan build's code.
   The walk that proves it is CheckGroupaWalk.v (pb_check_groupa). *)
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI00.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YI16 YC5d YM05.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.A.Prog Require Import PaTable GrantSyms GrantList GrantPa GrantBase.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.A.Prog Require Import HeadampTxEffective.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Prog Require Import HeadampModel GrantSweepModel.
Import ListNotations.
Open Scope Z_scope.
Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section d.
Context {PI : PAImg grant_listing}.
#[local] Notation SEGS := (@pa_segs _ grant_listing PI).
#[local] Notation BASE := (@pa_val _ grant_listing PI A_TEXT).
Section e.
Variable B : asyms.
Definition A_check_groupaP : Z := BASE + AF_check_groupa.
(* The machine stack the call needs: its own 128-byte frame, at most 16 bytes lost to `andi sp,sp,-32`,
   and below that the deepest callee, reac_ctrl_parse, whose TPARSE_STK is 160 + 2 * ESTACK (CtrlParse.v;
   CheckGroupaWalk.v checks the sum against it). ESTACK also covers __asan_memcpy and __asan_stack_malloc_2. *)
Definition TCG_STK : Z := 304 + 2 * ESTACK.
Definition tcheck_groupa_post (regs : bvmap 5 word) ly S (W : world SEGS) mem md : world SEGS -> config -> Prop :=
  apost_base SEGS B TCG_STK [] regs ly S W mem md 0
    (fun ly' S' W' regs' mem' md' => frames S' = frames S /\ ablocks B ly' S' = ablocks B ly S /\ (exists f, S' = set_fs f S)).
(* a0 = row, a1 = ch, a2 = param, a3 = tx, a4 = want. The row is 34 bytes inside a heap block and holds
   Pau's group-A row `GA ch p v` for v the table's effective value; want is that value. *)
Definition tcheck_groupa_spec : Prop :=
  forall ly S W (regs : bvmap 5 word) mem md ch0 (row ch p tx rb rn : Z) (T : list byte),
  afn_pre SEGS B TCG_STK ly S W regs mem md ch0 ->
  Z.of_nat (length (frames S)) <= 7 -> spZ regs + 32 <= ly_top ly ->
  arodata_okP SEGS pa_relro_lo pa_relro_hi B (aview SEGS (w_H W) mem) ->
  getr regs 10 = w64 row -> getr regs 11 = w64 ch -> getr regs 12 = w64 p -> getr regs 13 = w64 tx ->
  getr regs 14 = w64 (eff T tx ch p) ->
  0 <= ch < 48 -> 0 <= p < 3 ->
  In (tx, TX_SIZE) (ablocks B ly S) -> length T = 460%nat ->
  obj_at SEGS (mrestrict (w_H W) mem) tx LAY_TX (tx_vals T) ->
  In (rb, rn) (ablocks B ly S) -> rb <= row -> row + 34 <= rb + rn ->
  garr8 SEGS (mrestrict (w_H W) mem) row (GAz ch p (eff T tx ch p)) ->
  SRr SEGS W (cfg_at SEGS A_check_groupaP regs mem md) (tcheck_groupa_post regs ly S W mem md).
End e.
End d.
End b.
