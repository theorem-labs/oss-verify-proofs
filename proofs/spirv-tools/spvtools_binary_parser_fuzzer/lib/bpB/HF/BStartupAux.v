(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BPropExec BCatExec BCatSim BSeqExec BStepTac BHoare BWalkTac BStoreOk BStreamSim BMemSplit.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require KReplay.
Ltac2 kr_t_BStartupAux () := "K47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00C45stdpp9bitvector;definitions;bv_unsignedI47Corelib4Init5Logic2eq00C45stdpp9bitvector;definitions7Z_to_bvC45stdpp9bitvector;definitions5bv_eqC45stdpp9bitvector;definitions7bv_wrapC45stdpp9bitvector;definitionsDbv_unsigned_in_rangeC45stdpp9bitvector;definitions=bv_wrap_smallC45stdpp9bitvector;definitions@Z_to_bv_unsignedC47Corelib4Init5Logic8eq_ind_rK47Corelib7Numbers7BinNums8positive03I47Corelib7Numbers7BinNums1Z00I47Corelib7Numbers7BinNums1N00I47Corelib4Init5Logic3and00c6ARocqVerifyHarness?AgentSubmission3bpB2HF;BStartupAux<Z_to_bv_u_eqC47Corelib4Init5Logic6eq_sym".
Import ListNotations.
Open Scope bv_scope.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.

Local Open Scope Z_scope.

Lemma Z_to_bv_u_eq : forall (a : word) (z : Z), z = bv_unsigned a -> Z_to_bv 64 z = a.
Proof.
ltac2:(KReplay.run1 (kr_t_BStartupAux ()) [] "h01zh11Hh22b1h32b2h41nh51ap;1p;2p;3p;6g0000j13Tg000Uj1;Tg0013j12Tg001Vj20Tg002@j31Tg002Zj25Tg003@j3:Tg003dj29Tg004Jj28Tg005=j37Tg005ij26Tg006Xj64Tg0076#3#3#3#3#3#3#;R0#2R1g007[R2f0R3f1R4,00512P2f2R5,001503f3R6511X02g0089R1%23R7%24R8g008W%25?14310651064512R9[10541053512%26?154[R:f4R;#2?165\9A:543P3n2001000000120000000W3W2W4P:^38^27^41P3P01006R1,50R7P6P21901100;9123X021806970110071601E4O4b1P4P3E4W1W0W5o"). Qed.

Lemma Z_to_bv_u_eq_sym : forall (a : word) (z : Z), z = bv_unsigned a -> a = Z_to_bv 64 z.
Proof.
ltac2:(KReplay.run1 (kr_t_BStartupAux ()) [] "h01Hh11ah21zp;1p;2p;3p;4g0000j10Tg000Uj17Tg0013j12Tg001Vj21Tg002@j36Tg002Zj25Tg0092j33Tg00:6j44Tg0076#0#0#0#0#0#0#7R0#2R1g007[R2f0R3f1R4,10562P11504f2R0A3043C4W0W2W1o"). Qed.
