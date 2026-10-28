(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From Stdlib Require Import ZArith List.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BsIface RtB_TR LbB_PrsStmt.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require KReplay.
Ltac2 kr_t_LbB_LibTR () := "C47Corelib5Lists7ListDef3mapC47Corelib4Init9Datatypes3fstC47Corelib4Init9Datatypes3appK47Corelib4Init5Logic2eq01I47Corelib4Init9Datatypes4list00C6ARocqVerifyHarness?AgentSubmission3bpB2Rt6RtB_TR5TR_bpC47Corelib4Init9Datatypes6lengthC56Stdlib5Arith8PeanoNat3Nat3lebI47Corelib4Init5Logic2eq00K47Corelib4Init9Datatypes3nat02I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01I47Corelib7Numbers7BinNums1Z00c6ARocqVerifyHarness?AgentSubmission3bpB3Lib9LbB_LibTR5LIB_AK47Corelib4Init9Datatypes3nat01".
Import ListNotations.
Open Scope Z_scope.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.

Definition LIB_FREE_RAS_1 : list Z :=

  [0xed8d0; 0xed9ac; 0xed020; 0xed100; 0xedca8; 0xedd84; 0xee10c; 0xee2bc; 0xee46c;

   0xf8900; 0xf8b70; 0xfb5bc; 0x100228; 0xfc600;

   0xed60c; 0xed61c; 0xed62c; 0xed66c; 0xed6b4; 0xed6f4; 0xed73c; 0xed77c; 0xed7c4;

   0xeb480; 0xec22c; 0xec2b0;

   0x1200e8;

   0xfad2c; 0xfc020; 0xec5f0; 0xec748; 0xec89c].

Definition LIB_MALLOC_RAS_1 : list Z := [].

Definition LIB_FULL : list (list Z) :=

  [[APC0_FREE; 0xe8c18; 0xe8790]; [APC0_FREE; 0xe8c28; 0xe8790];

   [APC0_FREE; 0xeb480; 0xe8c10; 0xe8790]; [APC0_FREE; 0xec22c; 0xe8c10; 0xe8790]; [APC0_FREE; 0xec2b0; 0xe8c10; 0xe8790]; [APC0_FREE; 0xfd148; 0xeb704; 0xe8c10; 0xe8790]; [APC0_FREE; 0xfd148; 0xeb99c; 0xe8c10; 0xe8790]; [APC0_FREE; 0xfd148; 0xebce0; 0xe8c10; 0xe8790]; [APC0_FREE; 0xfd148; 0xebfb4; 0xe8c10; 0xe8790]]

  ++ map (fun pp => fst pp :: snd pp ++ [AWO_PM_RA; 0xe8c10; 0xe8790]) PM_PF.

Definition LIB_A : list (list Z) :=
  map (fun r => [APC0_FREE; r]) LIB_FREE_RAS_1 ++ map (fun r => [APC0_MALLOC; r]) LIB_MALLOC_RAS_1 ++ LIB_FULL.

Lemma LIB_A_len : Nat.leb (length (TR_bp LIB_A)) 1000 = true.
Proof.
ltac2:(KReplay.run1 (kr_t_LbB_LibTR ()) [] "p;2p;1p;3p-1R0p10000p4p710p8P0p1000LR1p4p710p8P0P1p4p7210p8P0p1000ip4p710p8g001Fj28Tg001`j17Tg002@j13Tg0038j22Tg003Xj25Tg0048j34Tg004Rj10Tf0R0#0#0#0#0#0#0#0#0p=6%00#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0p=1g0051R0g005QR1'8g0061#7g006O#3'2g007K#6#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1'5=401do"). Qed.
