(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase Fs State Run.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import CatSim ShapeAlg Spec.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require KReplay.
Ltac2 kr_t_ShapeLaws () := "C4ELinuxProcessSemantics?LinuxProcessSem2Fs2FsC4ELinuxProcessSemantics?LinuxProcessSem3Run=is_prefix_nilI47Corelib4Init9Datatypes4list00K47Corelib4Init9Datatypes4list01C4ELinuxProcessSemantics?LinuxProcessSem3Run9is_prefixC47Corelib4Init9Datatypes3appI47Corelib4Init5Logic2eq00I47Corelib4Init5Logic3and00I47Corelib4Init5Logic2ex00K47Corelib4Init5Logic2or01C49OSSVerify5KrLib8ShapeAlg6t_emitC1?~~~~~~~~~~~~~~~I4ELinuxProcessSemantics?LinuxProcessSem5State5event00C49OSSVerify5KrLib8ShapeAlg4TSetC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00K4ELinuxProcessSemantics?LinuxProcessSem5State5event03K47Corelib4Init9Datatypes4list02c49OSSVerify5KrLib9ShapeLaws>t_emit_has_nilC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8ShapeAlg6t_exitC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive03C49OSSVerify5KrLib8ShapeAlg5t_nilC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8ShapeAlg6t_alt2C1?~~~~~~~~~~~~~~~".
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.

Lemma t_emit_has_nil : forall evs T, t_emit evs T [].
Proof.
ltac2:(KReplay.run1 (kr_t_ShapeLaws ()) [] "h01Th13evsh23tr'p;1p;3p;2p10000p4p70g000^R0p4p710p8g001Xj19Tg0028j18Tg002Xj30Tg003Nj31Tg003kj37Tg004Ej22Tg004`j23TP0j24Tg005:j35Tg005Tj36Tg006HR0#9R1g007>%80R2f1R3500f2f0R45109712P3P4O1'2X21,31140335A6342eW0W1o"). Qed.

Lemma t_exit_has_nil : forall code fs, t_exit code fs [].
Proof.
ltac2:(KReplay.run1 (kr_t_ShapeLaws ()) [] "h04codeh12fsp;1p;2p;3g0080j10Tg008Uj17Tg0093j12Tg009Vj21Tg0028j16Tg00:Lj35Tg00:lj23Tg00;ij34Tg00<]#0#0#0#0#0#0#7#2g0000g006HR0f1R1f0R2'1%60R035g00=B'3A4120eW1W0o"). Qed.

Lemma t_alt2_has_nil_l : forall A B : TSet, A [] -> t_alt2 A B [].
Proof.
ltac2:(KReplay.run1 (kr_t_ShapeLaws ()) [] "h01Ah11Bh21Hp;1p;3g0028j12Tg005:j31Tg00>5j30Tg007>R0f1R1g006H#2R2O1R3f2R4P2O1f0713A0412eW2X10W0o"). Qed.

