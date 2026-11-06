(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.spirv_tools.spvtools_binary_parser_fuzzer.images Require Import Asan.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import HPropExec HShapeAlg HSpec HeapCeil.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import HMem HCells HStep HLFrame HMState HSysStep HExec.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import ASegs AsShadow AsConst AsIface AsCXXHeap AsDriverLaws AsStack0 RtA_Iface.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import DvA_FuzzStmt AsDrvDefs AsMainPre AsTargetRun AsMainTop AsMainTails.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require KReplay.
Ltac2 kr_t_DvA_MainA () := "C69OSSVerify5KrLib3bpA2Rt7AsIface<asan_rt_hypsC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpA2Rt9RtA_IfaceCasan_rt_hyps_bp_extC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpA2Rt9RtA_IfaceCalloc_ok_of_live_bpC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpA2Rt9RtA_Iface9RHEAP_ahmC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpA2Rt9RtA_IfaceAannotate_gen_stmtC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpA2Rt9RtA_Iface7cost_bpC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic3and00C69OSSVerify5KrLib3bpA3Drv9AsMainPreEas_main_realizes_stmtC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic5proj1C69OSSVerify5KrLib3bpA3Drv;AsTargetRun=as_target_runC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpA3Drv;AsMainTails;atail_usageC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpA3Drv;AsMainTails:atail_openC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpA3Drv;AsMainTails;atail_rderrC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib3bpA3Drv9AsMainTop@as_main_realizesC1?~~~~~~~~~~~~~~~".
Import ListNotations.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.
Open Scope Z_scope.

Section MainA.
  Context {HCEIL : HeapCeil}.
  Variable H : asr.
  Variable FZP : fuzz_params.
  Hypothesis HHB : asan_rt_hyps_bp H.
  Hypothesis DL : asan_driver_laws H.
  Hypothesis LIVE : ADRV_LIVE <= as_LIVE_MAX H /\ ADRV_CNT <= as_LIVE_CNT_MAX H.
  Hypothesis PO : fz_params_ok FZP.
  Hypothesis FZINV : forall m, mem_inv asegs m -> arelro_none m -> ACONST m -> LbA_DStat.dstat m -> fz_inv FZP m.
  Hypothesis FZINV' : forall m, fz_inv FZP m -> LbA_DStat.dstat m.
  Hypothesis FZ : fuzz_stmt H FZP.

  Theorem as_main_A : as_main_realizes_stmt H FZP.
Proof.
ltac2:(KReplay.run1 (kr_t_DvA_MainA ()) ["MainA"] "h03AHMh12H0h22HHh32HRh41Xh52_Hh63_H0h71ap;2p;1p;3p;9p;4p;<g0000j2=Tg0010j2<Tg0029j12Tg003Bj21Tg004Aj1;Tg005Hj13Tg006ER0j20Tg006`j34Tg007lj35Tg008Gl96Tg009Mj47Tg00:Qj48Tg00;Tj49Tg00<Xl<:Tp,3HHBp,5HCEILR1p,1HR2'=R31<12R4%22R51112R6%;1%32'0R7'0R8'0R9'0R:'0P0P3P:p,3FZPR;9412f0R<P0P4P9P6P<P0P5P8P6P<A567<X48X65f1R5P<O2n2001000000120000000X19X54P5P<O2n2001000000120000000P6P1P2P;f2R6P<p,2POR4p,2DLR9P1P2P6P9P;P4p,5FZINVp,6FZINV'p,2FZM96p,4LIVEP1P2P;P9C7P1P2P;P9C8P1P2P;P9C9M<:b0X3:X23P5P<O2n2001000000120000000b7o"). Qed.
End MainA.
