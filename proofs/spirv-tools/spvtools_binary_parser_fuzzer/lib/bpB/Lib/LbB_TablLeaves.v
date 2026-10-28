(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BeapCeil.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.bpB.Lib Require Import LbB_TablStmt.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.bpB.Lib Require LbB_TablReg LbB_TablGT3 LbB_TablJmp LbB_TablTS LbB_TablAcc LbB_TablSplit LbB_TablLO
  LbB_TablLP2 LbB_TablLX LbB_TablSpec.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require KReplay.
Ltac2 kr_t_LbB_TablLeaves () := "C6ARocqVerifyHarness?AgentSubmission3bpB3Lib;LbB_TablReg;fixword_okAC6ARocqVerifyHarness?AgentSubmission3bpB3Lib;LbB_TablRegBis_host_endian_okAC6ARocqVerifyHarness?AgentSubmission3bpB3Lib;LbB_TablGT3Bgenerates_type_okAC6ARocqVerifyHarness?AgentSubmission3bpB3Lib;LbB_TablReg?is_ext_inst_okAC6ARocqVerifyHarness?AgentSubmission3bpB3Lib;LbB_TablJmp?is_optional_okAC6ARocqVerifyHarness?AgentSubmission3bpB3Lib;LbB_TablRegBis_nonsemantic_okAC6ARocqVerifyHarness?AgentSubmission3bpB3Lib;LbB_TablJmp9fpenc_okAC6ARocqVerifyHarness?AgentSubmission3bpB3Lib:LbB_TablTSDoperand_type_str_okAC6ARocqVerifyHarness?AgentSubmission3bpB3Lib;LbB_TablAcc>idesc_name_okAC6ARocqVerifyHarness?AgentSubmission3bpB3Lib;LbB_TablAccBidesc_operands_okAC6ARocqVerifyHarness?AgentSubmission3bpB3Lib;LbB_TablAccBodesc_operands_okAC6ARocqVerifyHarness?AgentSubmission3bpB3Lib;LbB_TablAccBedesc_operands_okAC6ARocqVerifyHarness?AgentSubmission3bpB3Lib=LbB_TablSplit@opcode_split_okAC6ARocqVerifyHarness?AgentSubmission3bpB3Lib:LbB_TablLOAlookup_opcode_okAC6ARocqVerifyHarness?AgentSubmission3bpB3Lib;LbB_TablLP2Blookup_operand_okAC6ARocqVerifyHarness?AgentSubmission3bpB3Lib:LbB_TablLX>lookup_ext_okAC6ARocqVerifyHarness?AgentSubmission3bpB3Lib<LbB_TablSpec?spec_lookup_okAK6ARocqVerifyHarness?AgentSubmission3bpB3Lib<LbB_TablStmt<tabl_leavesA01I6ARocqVerifyHarness?AgentSubmission3bpB2HF8BeapCeil8HeapCeil00".
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.

Theorem tabl_leaves_okA {HCEIL : HeapCeil} : tabl_leavesA.
Proof.
ltac2:(KReplay.run1 (kr_t_LbB_TablLeaves ()) [] "h05HCEILp;1p;Bg0000j1ATg0014j1@Tg002?j10Tg003Jj11Tg004Rj1?Tg005Zj12Tg006ej13Tg007gj14Tg0093j15Tg00::j16Tg00;Ej17Tg00<Pj18Tg00=[j19Tg00>fj1>Tg00?oj1:Tg00A:j1;Tg00B@j1<Tg00CIlB=Tg00DQR0f0R1%A1%@1%01%11%?1%21%31%41%51%61%71%81%91%>1%:1%;1%<1MB=X00P1O1W0o"). Qed.
