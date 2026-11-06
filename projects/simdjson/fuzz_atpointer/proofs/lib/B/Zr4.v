(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.simdjson.fuzz_atpointer.lib.AS Require Import Zp7 Z1b.
From OSSVerify.Proofs.simdjson.fuzz_atpointer.lib.Lib Require Import Tac Arr Bytes ImageA RzCPS Z119 FP Z10q.
From OSSVerify.Proofs.simdjson.fuzz_atpointer.lib.Sj Require Import Zpe SjNumU SjNumN Zpd.
From OSSVerify.Proofs.simdjson.fuzz_atpointer.lib.P Require Import Rnd Zso Zvm.
From OSSVerify.Proofs.simdjson.fuzz_atpointer.lib.A Require Import Shadow.
From OSSVerify.Proofs.simdjson.fuzz_atpointer.lib.B Require Import Layout Zks D_defs D_kit D_clx Zpm Zpl Zq2 Sj_rtf Zqc Zqd
  Zsl Zqh Zqf Zuj Zr0 Zs5.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.

Definition fcb_kf14 (E : fcbenv) (Q : machine_state -> Prop) : Prop :=
  forall xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs5 xs6 xs7 xs8 xs9 xt3 xt4 xt5 xt6 xF xfc mm js c0 c8 c16 c24 c32 c40 c48 c56 q w lm nb tm IP IL FPT FL,
    FCINV E mm true js c0 c8 c16 c24 c32 c40 c48 c56 q w lm nb tm IP IL FPT FL -> frm0 xfc ->
    (tm <> 0 -> fcb_spans E IP IL FPT FL /\ 1 <= bv_unsigned w <= 18446744073709551614)%Z ->
    (-9223372036854775808 <= q < 9223372036854775808)%Z ->
    evt bsegs Q (FCB E 0xd1f50 xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 (Z_to_bv 64 (q_f E)) xs5 xs6 xs7 xs8 xs9 (Z_to_bv 64 (q_OUT E)) xt3 xt4 xt5 xt6 xF xfc mm).
