(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: the contract of reac_grant_build_sweep on fuzz_grant.asan, written for libreac/fuzz_grant in the contract form of proofs/cgif/cgif_file_fuzzer/lib/YC7x.v and proofs/cgif/cgif_file_fuzzer/lib/YC21.v; module paths changed. *)
(* reac_grant_build_sweep (src/reac_grant.c, 0x848f0 in fuzz_grant.asan): the contract of the ASan build's code.
   The walk that proves it is GrantBuildSweepWalk.v (pb_reac_grant_build_sweep). *)
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
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Prog Require Import HeadampModel GrantModel GrantSweepModel BuildSweepModel.
Import ListNotations.
Open Scope Z_scope.
(* The machine stack the call needs: its own 192-byte frame, at most 16 bytes lost to `andi sp,sp,-32`,
   and below that the deepest callee: 208 + max (TEFF_STK = 16 + ESTACK, HeadampTxEffective.v)
   (TBGS_STK = 1632 + TSTAMP_STK = 1920 + ESTACK, CtrlBuildGrantSweep.v); GrantBuildSweepWalk.v checks
   the sum against both. *)
Definition TBSW_STK : Z := 2128 + ESTACK.
(* The rows the call lays down, as a footprint. *)
Definition bsw_FP (s al mx base w : Z) : list (Z * Z) :=
if bsw_ok s al mx base w then [(s, s + 34 * (8 + 3 * w))] else [].
Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section d.
Context {PI : PAImg grant_listing}.
#[local] Notation SEGS := (@pa_segs _ grant_listing PI).
#[local] Notation BASE := (@pa_val _ grant_listing PI A_TEXT).
Section e.
Variable B : asyms.
Definition treac_grant_build_sweep_spec : Prop :=
forall ly S W (regs : bvmap 5 word) mem md ch0 (s mx al tx base w : Z) (T : list byte),
afn_pre SEGS B TBSW_STK ly S W regs mem md ch0 -> Z.of_nat (length (frames S)) <= 7 -> spZ regs + 32 <= ly_top ly ->
arodata_okP SEGS pa_relro_lo pa_relro_hi B (aview SEGS (w_H W) mem) ->
getr regs 10 = w64 s -> getr regs 11 = w64 mx -> getr regs 12 = w64 al -> getr regs 13 = w64 tx ->
0 <= s < 2 ^ 63 -> - 2 ^ 31 <= mx < 2 ^ 31 -> 0 <= al < 2 ^ 64 ->
(al <> 0 -> afobj SEGS B ly S W mem al 2 /\ garr8 SEGS (mrestrict (w_H W) mem) al [base; w]) ->
In (tx, TX_SIZE) (ablocks B ly S) -> length T = 460%nat ->
obj_at SEGS (mrestrict (w_H W) mem) tx LAY_TX (tx_vals T) -> tx_set01 T -> tx_legal T ->
(bsw_ok s al mx base w = true ->
exists sb sn, In (sb, sn) (ablocks B ly S) /\ sb <= s /\ s + 34 * (8 + 3 * w) <= sb + sn) ->
SRr SEGS W (cfg_at SEGS (BASE + AF_reac_grant_build_sweep) regs mem md)
(apost_base SEGS B TBSW_STK (bsw_FP s al mx base w) regs ly S W mem md 0
(fun ly' S' W' regs' mem' md' =>
frames S' = frames S /\ ablocks B ly' S' = ablocks B ly S /\ (exists f, S' = set_fs f S) /\
getr regs' 10 = w64 (if bsw_ok s al mx base w then 8 + 3 * w else -1) /\
(bsw_ok s al mx base w = true ->
garr8 SEGS (mrestrict (w_H W') mem') s
(map bv_unsigned (SWEEP base (Z.to_nat w) (sweep_vals T tx base (Z.to_nat w))))))).
End e.
End d.
End b.
