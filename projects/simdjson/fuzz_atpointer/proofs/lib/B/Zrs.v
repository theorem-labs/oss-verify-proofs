(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From OSSVerify.Proofs.simdjson.fuzz_atpointer.lib.Lib Require Import Tac Arr Bytes ImageA RzCPS.
From OSSVerify.Proofs.simdjson.fuzz_atpointer.lib.B Require Import Layout Zr0 Zs5.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.

Definition fcb_parse_stmt (E : fcbenv) (Q : machine_state -> Prop) : Prop :=
  forall xra xt0 xt1 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs7 xt3 xt4 xt5 xt6 xF xfc mm c0 c8 c16 c24 c32 c40 c48 c56,
    FCPINV E mm c0 c8 c16 c24 c32 c40 c48 c56 -> frm0 xfc ->
    evt bsegs Q (FCB E 0xd0944 xra xt0 xt1 (Z_to_bv 64 53) xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 (Z_to_bv 64 (q_f E)) (Z_to_bv 64 (q_FIRST E)) (Z_to_bv 64 (q_LAST E)) xs7
                     (Z_to_bv 64 1) (Z_to_bv 64 42949673006) (Z_to_bv 64 (q_OUT E)) xt3 xt4 xt5 xt6 xF xfc mm).
