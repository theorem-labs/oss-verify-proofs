(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import HeapCeil.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.bpA.Lib Require Import LbA_TablStmt.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.bpA.Lib Require LbA_TablReg LbA_TablGT3 LbA_TablJmp LbA_TablTS LbA_TablAcc LbA_TablSplit LbA_TablLO
  LbA_TablLP2 LbA_TablLX LbA_TablSpec.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require KReplay.
Ltac2 kr_t_LbA_TablLeaves () := "C69OSSVerify5KrLib3bpA3Lib;LbA_TablReg;fixword_okAC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpA3Lib;LbA_TablRegBis_host_endian_okAC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpA3Lib;LbA_TablGT3Bgenerates_type_okAC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpA3Lib;LbA_TablReg?is_ext_inst_okAC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpA3Lib;LbA_TablJmp?is_optional_okAC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpA3Lib;LbA_TablRegBis_nonsemantic_okAC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpA3Lib;LbA_TablJmp9fpenc_okAC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpA3Lib:LbA_TablTSDoperand_type_str_okAC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpA3Lib;LbA_TablAcc>idesc_name_okAC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpA3Lib;LbA_TablAccBidesc_operands_okAC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpA3Lib;LbA_TablAccBodesc_operands_okAC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpA3Lib;LbA_TablAccBedesc_operands_okAC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpA3Lib=LbA_TablSplit@opcode_split_okAC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpA3Lib:LbA_TablLOAlookup_opcode_okAC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpA3Lib;LbA_TablLP2Blookup_operand_okAC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpA3Lib:LbA_TablLX>lookup_ext_okAC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpA3Lib<LbA_TablSpec?spec_lookup_okAC1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib3bpA3Lib<LbA_TablStmt<tabl_leavesA01C1?~~~~~~~~~~~~~~~I69OSSVerify5KrLib3bpA2HF8HeapCeil8HeapCeil00C1?~~~~~~~~~~~~~~~".
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.

Theorem tabl_leaves_okA {HCEIL : HeapCeil} : tabl_leavesA.
Proof.
ltac2:(KReplay.run1 (kr_t_LbA_TablLeaves ()) [] "h05HCEILp;1p;Bg0000j1ATg0014j1@Tg002?j10Tg003Jj11Tg004Rj1?Tg005Zj12Tg006ej13Tg007gj14Tg0093j15Tg00::j16Tg00;Ej17Tg00<Pj18Tg00=[j19Tg00>fj1>Tg00?oj1:Tg00A:j1;Tg00B@j1<Tg00CIlB=Tg00DQR0f0R1%A1%@1%01%11%?1%21%31%41%51%61%71%81%91%>1%:1%;1%<1MB=X00P1O1W0o"). Qed.
