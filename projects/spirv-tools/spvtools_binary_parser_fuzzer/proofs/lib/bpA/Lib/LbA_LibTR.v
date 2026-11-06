(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From Stdlib Require Import ZArith List.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import AsIface RtA_TR LbA_PrsStmt.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require KReplay.
Ltac2 kr_t_LbA_LibTR () := "C47Corelib5Lists7ListDef3mapC47Corelib4Init9Datatypes3fstC47Corelib4Init9Datatypes3appK47Corelib4Init5Logic2eq01I47Corelib4Init9Datatypes4list00C69OSSVerify5KrLib3bpA2Rt6RtA_TR5TR_bpC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes6lengthC56Stdlib5Arith8PeanoNat3Nat3lebI47Corelib4Init5Logic2eq00K47Corelib4Init9Datatypes3nat02I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01I47Corelib7Numbers7BinNums1Z00c69OSSVerify5KrLib3bpA3Lib9LbA_LibTR5LIB_AC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes3nat01".
Import ListNotations.
Open Scope Z_scope.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.

Definition LIB_FREE_RAS_1 : list Z :=

  [0xf4d9c; 0xf4e3c; 0xeac9c; 0xead40; 0xf50ec; 0xf518c; 0xf47b8; 0xf49c4; 0xf4bd0;

   0xf7d2c; 0xf7fb4; 0xfa830; 0xfea58; 0xfb73c;

   0xeb068; 0xeb110; 0xeb1b8; 0xeb1f0; 0xeb238; 0xeb270; 0xeb2b8; 0xeb2f0;

   0xea6a4; 0xea888; 0xea890;

   0x11e744;

   0xfa27c; 0xfb168].

Definition LIB_MALLOC_RAS_1 : list Z := [].

Definition LIB_FULL : list (list Z) :=

  [[APC0_FREE; 0xe8f5c; 0xe8b48]; [APC0_FREE; 0xe8f68; 0xe8b48];

   [APC0_FREE; 0xea6a4; 0xe8f54; 0xe8b48]; [APC0_FREE; 0xea888; 0xe8f54; 0xe8b48]; [APC0_FREE; 0xea890; 0xe8f54; 0xe8b48]]

  ++ map (fun pp => fst pp :: snd pp ++ [AWO_PM_RA; 0xe8f54; 0xe8b48]) PM_PF.

Definition LIB_A : list (list Z) :=
  map (fun r => [APC0_FREE; r]) LIB_FREE_RAS_1 ++ map (fun r => [APC0_MALLOC; r]) LIB_MALLOC_RAS_1 ++ LIB_FULL.

Lemma LIB_A_len : Nat.leb (length (TR_bp LIB_A)) 1000 = true.
Proof.
ltac2:(KReplay.run1 (kr_t_LbA_LibTR ()) [] "p;2p;1p;3p-1R0p10000p4p710p8P0p1000LR1p4p710p8P0P1p4p7210p8P0p1000ip4p710p8g001Fj28Tg001`j17Tg002@j13Tg0038j22Tg003Xj25Tg0048j34Tg004Rj10Tf0R0#0#0#0#0#0#0#0#0p=6%00#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0p=1g0051R0g005QR1'8g0061#7g006O#3'2g007K#6#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1'5=401do"). Qed.
