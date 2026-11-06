(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require As0Gc.
From Stdlib Require Import ZArith NArith List Lia Bool.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import HeapCeil.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import ASegs AsShadow AsConst AsIface FakeStackRep RtA_Iface.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import RtA_SM0 RtA_SM2 RtA_SM3 RtA_SM5 RtA_SM6 RtA_SM8 RtA_SF5 RtA_SF6 RtA_SF8 RtA_SetShadow.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require KReplay.
Ltac2 kr_t_RtA_Ext () := "C69OSSVerify5KrLib3bpA2Rt9RtA_IfaceDstack_malloc_stmt_bpC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1Z02K47Corelib7Numbers7BinNums8positive01C69OSSVerify5KrLib3bpA2Rt9RtA_IfaceDstack_malloc_sz_stmtC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpA2Rt9RtA_Iface?stack_free_stmtC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpA2Rt9RtA_IfaceBstack_free_sz_stmtC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpA2Rt7AsIface?set_shadow_stmtC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic3and00C69OSSVerify5KrLib3bpA2Rt7RtA_SM0Astack_malloc_0_okC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpA2Rt7RtA_SM2Astack_malloc_2_okC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpA2Rt7RtA_SM3Astack_malloc_3_okC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpA2Rt7RtA_SM5Astack_malloc_5_okC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpA2Rt7RtA_SM6Astack_malloc_6_okC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpA2Rt7RtA_SM8Astack_malloc_8_okC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpA2Rt7RtA_SF5?stack_free_5_okC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpA2Rt7RtA_SF6?stack_free_6_okC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpA2Rt7RtA_SF8?stack_free_8_okC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpA2Rt9RtA_IfaceCasan_rt_hyps_bp_extC1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic3and01K47Corelib7Numbers7BinNums1Z01C69OSSVerify5KrLib3bpA2Rt9RtA_Iface<AFS_MALLOC_0C1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive03C69OSSVerify5KrLib3bpA2Rt9RtA_Iface<AFS_MALLOC_2C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpA2Rt9RtA_Iface<AFS_MALLOC_3C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpA2Rt9RtA_Iface<AFS_MALLOC_5C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpA2Rt9RtA_Iface<AFS_MALLOC_6C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpA2Rt9RtA_Iface<AFS_MALLOC_8C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpA2Rt9RtA_Iface:AFS_FREE_5C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpA2Rt9RtA_Iface:AFS_FREE_6C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpA2Rt9RtA_Iface:AFS_FREE_8C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpA2Rt7AsIface>ASET_SHADOW_00C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpA2Rt9RtA_Iface>ASET_SHADOW_F8C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpA2Rt=RtA_SetShadow@set_shadow_00_okC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpA2Rt=RtA_SetShadow@set_shadow_f8_okC1?~~~~~~~~~~~~~~~".
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.

Section Ext.
  Context {HCEIL : HeapCeil}.
  Variable H : asr.
  Hypothesis RFS_is : forall LF m, as_RFS H LF m <-> RFSI (as_FSB H) LF m.

  Theorem rt_bp_ext_ok : asan_rt_hyps_bp_ext H.
Proof.
ltac2:(KReplay.run1 (kr_t_RtA_Ext ()) ["Ext"] "p;4p;1p;2p;3g0000j45Tg001:j11Tg001_j12Tg002=j13Tg002bj4DTg003lj47Tg0051j4=Tg0069j26Tg007<j20Tg007Wj3<Tg008\j3;Tg009aj3:Tg00:fj39Tg00;kj3CTg00=0j3BTg00>5j3ATg00?8j3?Tg00@;j3>Tg00A>j2@Tg00BGj48Tf6f5f4f3f2f1f0C8C8p=4p,5HCEILR0p,1HR1g00BbR2g00C@C5P0P1g00DBR3#1R4#2g00DgC5R5P0P1%33R3#2g00EiC5R6P0P1%34#2R7g00FkC5R8P0P1%13#2R9g00GmC5R:P0P1%14#1#2R4g00HoCDR;P0P1P7g00J1C7R7P0P1P9g00K1C7R9P0P1P4g00L1C=R4g00M1,62R2%33#3#3#1#1#1#2g00N3'6R3'0R<'0R='0R>'0R?'0R@'0RA'0RB'0RC'0p,6RFS_isRD9<01P5PCA;01DP6PBA:01DP8PAA901DP:P@AC01DP;P?AB01DP7P>AA01DP9P=A?01DP4P<A>01DP2P3g00O7g00PAF4F4F4F4F41@01eo"). Qed.
End Ext.
