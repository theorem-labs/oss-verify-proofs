(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From Stdlib Require Import ZArith List.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import HeapCeil AsIface AsCXXHeap RtA_Iface.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import LbA_VMvStmt LbA_VMv LbA_VMvc2 LbA_VMvc3.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require KReplay.
Ltac2 kr_t_LbA_VMvAll () := "C69OSSVerify5KrLib3bpA2Rt9RtA_Iface?asan_rt_hyps_bpC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpA2Rt9RtA_Iface:rt_bp_baseC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpA2Rt7AsIface<asan_rt_hypsC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpA2Rt9RtA_Iface;rt_bp_annotC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpA2Rt9RtA_IfaceAannotate_gen_stmtC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpA2Rt9AsCXXHeap9ah_memsetC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpA2Rt7AsIface@asan_memset_stmtC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpA3Lib;LbA_VMvStmt=vmove_stmt_atC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic3and00C69OSSVerify5KrLib3bpA3Lib7LbA_VMv7vmove_1C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpA3Lib9LbA_VMvc2:vmove_1_c2C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpA3Lib9LbA_VMvc3:vmove_1_c3C1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic3and01C69OSSVerify5KrLib3bpA3Lib;LbA_VMvStmt8AVMOVE_1C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpA3Lib;LbA_VMvStmt?AVMOVE_DEL_RA_1C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpA3Lib;LbA_VMvStmt8AVMOVE_2C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpA3Lib;LbA_VMvStmt?AVMOVE_DEL_RA_2C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpA3Lib;LbA_VMvStmt8AVMOVE_3C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpA3Lib;LbA_VMvStmt?AVMOVE_DEL_RA_3C1?~~~~~~~~~~~~~~~".
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.

Section All.
  Context {HCEIL : HeapCeil}.
  Variable H : asr.

  Theorem vmove_all : asan_rt_hyps_bp H -> vmove_stmtA H.
Proof.
ltac2:(KReplay.run1 (kr_t_LbA_VMvAll ()) ["All"] "h04HANNh12HHh23HMSh32HRp;2p;3p;1p;4p;5g0000j2<Tg0015j3;Tg0025j23Tg0035j32Tg0046j1:Tg005=j39Tg006<j14Tg007@j40Tg008Fj25Tg008aj56Tg009]j57Tg00:^j58Tg00;_j41Tp,5HCEILR0p,1HR1'<f0R29;011301f1R39201%:0A9013%40P0P1g00<:g00=;C0P0P1g00>Cg00?DC0R4P0P1g00@Lg00AMC0R5'5P0P1f2R6P3P2D6P4P5P0P1P6P3P2D7P0P1P6P3P2D8C1C1b2b0b1W3o"). Qed.
End All.
