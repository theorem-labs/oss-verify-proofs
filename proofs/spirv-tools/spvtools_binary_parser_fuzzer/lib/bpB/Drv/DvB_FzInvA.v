(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From Stdlib Require Import ZArith List.
From OssFuzzTheorems.spirv_tools.spvtools_binary_parser_fuzzer.images Require Import AsanUbsan.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BMem BSegs BsConst DvB_FuzzStmt BsDrvDefs.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require LbB_DStat LbB_TopDefs.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require KReplay.
Ltac2 kr_t_DvB_FzInvA () := "K47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00I47Corelib4Init9Datatypes6option00C7ARocqVerifyHarness?AgentSubmission3bpB2HF3Lib4BMem7mem_invC6ARocqVerifyHarness?AgentSubmission3bpB3Drv9BsDrvDefs;arelro_noneC6ARocqVerifyHarness?AgentSubmission3bpB2Rt7BsConst6ACONSTC6ARocqVerifyHarness?AgentSubmission3bpB3Lib9LbB_DStat5dstatK47Corelib4Init5Logic3and01K47Corelib7Numbers7BinNums8positive03C6ARocqVerifyHarness?AgentSubmission3bpB2Rt5BSegs5asegsC6ARocqVerifyHarness?AgentSubmission3bpB3Drv<DvB_FuzzStmt6fz_invC6ARocqVerifyHarness?AgentSubmission3bpB3Lib9LbB_DStat6relro0C47Corelib4Init5Logic5proj2C6ARocqVerifyHarness?AgentSubmission3bpB2Rt7BsIface3memC6ARocqVerifyHarness?AgentSubmission3bpB3Lib;LbB_TopDefs5FZP_A".
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.

Lemma fzinv_A : forall m, mem_inv asegs m -> arelro_none m -> ACONST m -> LbB_DStat.dstat m -> fz_inv LbB_TopDefs.FZP_A m.
Proof.
ltac2:(KReplay.run1 (kr_t_DvB_FzInvA ()) [] "h01Dh11Rh22_Hh33_H0h41mp;1p;2p;4g0000j10Tg000Uj14Tg0013j13Tg001Vj15Tg0028j28Tg0034j12Tg0046j17Tg0050j11Tg005lj46Tg006G#0#0#0R0#0#0#0#4#3%40#3#5[g006lf0R0'8f1#2f2R1#7f3#1f4R2#2%12P1P0C6W0W3W1W2W4o"). Qed.

Lemma fzinv'_A : forall m, fz_inv LbB_TopDefs.FZP_A m -> LbB_DStat.dstat m.
Proof.
ltac2:(KReplay.run1 (kr_t_DvB_FzInvA ()) [] "h01Kh11mp;2p;1p;3g007cj23Tg008cj12Tg0050j10Tg009`j31Tg00:;g00;2f0R0'3f1R1#2%01;10W0W1o"). Qed.
