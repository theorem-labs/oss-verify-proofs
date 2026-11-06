(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require BvWfKernel.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require Import PropExec CatExec CatSim FPSteps ShapeAlg SpinAlg FrmKeep FrmKeepC FrmKeepEs0 FrmKeepEu0 FrmKeepEa0 FrmKeepCEb0.
From OSSVerify.jsoncons.fuzz_ubjson_encoder.images Require Plain.
From OSSVerify.jsoncons.fuzz_ubjson_encoder.images Require Ubsan Asan AsanUbsan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require Import BMode.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require KReplay.
Ltac2 kr_t_FrmInit () := "I47Corelib4Init9Datatypes4list00K47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00K47Corelib4Init5Logic2eq01I4ELinuxProcessSemantics?LinuxProcessSem<MemImageType7Segment00I47Corelib7Numbers7BinNums1N00I4ELinuxProcessSemantics?LinuxProcessSem<MemImageType8PhdrInfo00K47Corelib7Numbers7BinNums8positive03I4ELinuxProcessSemantics?LinuxProcessSem;StackLayout9EntryDraw00I47Corelib7Numbers7BinNums1Z00I4ELinuxProcessSemantics?LinuxProcessSem5State9ProcInput00K47Corelib7Numbers7BinNums1Z01C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib7SpinAlg8frm_safeC13~~~C4ELinuxProcessSemantics?LinuxProcessSem3Run;init_configC79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib7SpinAlg9srealizesC13~~~C4ELinuxProcessSemantics?LinuxProcessSem3Run6cfg_msC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics7ms_fcsrC79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib7FPSteps8frm_zeroC13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib7FrmInit7init_fzC13~~~K47Corelib4Init5Logic3and01C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib7SpinAlg=srealizes0_ofC13~~~I79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib5BMode5BMode00C13~~~I4ELinuxProcessSemantics?LinuxProcessSem3Run;SpuriousCfg00C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8ShapeAlg4TSetC13~~~C46Stdlib5Lists4List2InC4ELinuxProcessSemantics?LinuxProcessSem<MemImageType>seg_executableC4ELinuxProcessSemantics?LinuxProcessSem<MemImageType<seg_writableC47Corelib4Init9Datatypes4andbI47Corelib4Init5Logic2eq00I47Corelib4Init9Datatypes6option00C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics:fetch_wordK47Corelib4Init9Datatypes6option01C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics:fetch_tailI47Corelib4Init5Logic2or00C89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8FrmKeepC4FRMC=word_frm_safeC13~~~C89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib:FrmKeepEs05FRMS0:fetch_safeC13~~~C89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8FrmKeepC4FRMC>safe_of_coarseC13~~~C79OSSVerify8jsonconsCfuzz_ubjson_encoder6images5Plain1M?loaded_segmentsC13~~~I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool02K47Corelib4Init9Datatypes4bool01C89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib:FrmKeepEs05FRMS05no_wxC13~~~C89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib:FrmKeepEu05FRMU0:fetch_safeC13~~~C79OSSVerify8jsonconsCfuzz_ubjson_encoder6images5Ubsan1M?loaded_segmentsC13~~~C89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib:FrmKeepEu05FRMU05no_wxC13~~~C89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib:FrmKeepEa05FRMA0:fetch_safeC13~~~C79OSSVerify8jsonconsCfuzz_ubjson_encoder6images4Asan1M?loaded_segmentsC13~~~C89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib:FrmKeepEa05FRMA05no_wxC13~~~C79OSSVerify8jsonconsCfuzz_ubjson_encoder6images9AsanUbsan1M?loaded_segmentsC13~~~C89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib;FrmKeepCEb06FRMCB05no_wxC13~~~C89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib;FrmKeepCEb06FRMCB0:fetch_safeC13~~~".
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Lemma init_fz : forall segs pc ph sp brk0 mb rnd lim inp,
  frm_zero (ms_fcsr (cfg_ms (init_config segs pc ph sp brk0 mb rnd lim inp))).
Proof.
ltac2:(KReplay.run1 (kr_t_FrmInit ()) [] "h04brk0h13inph23limh32mbh42pch52phh63rndh74segsh82spp;1p;2g0000j14Tg000Pj10Tg0015j12Tg001Sj11Tg0026j23Tg002P#4g003Og003mg004m#0#0#0#0#0#0#2#1R0g005Rg006RR1g0070g007j,31W1W2W6X30X00W8W5W4W7o"). Qed.

Lemma top_of_guarded {bmK : BMode} : forall segs scfg pc ph sp brk0 mb rnd lim inp T,
  frm_safe segs ->
  srealizes segs scfg (init_config segs pc ph sp brk0 mb rnd lim inp) T ->
  srealizes0 segs scfg (init_config segs pc ph sp brk0 mb rnd lim inp) T.
Proof.
ltac2:(KReplay.run1 (kr_t_FrmInit ()) [] "h03bmKh12FSh21Hh31Th44brk0h53inph63limh72mbh82pch92phh:3rndh;4scfgh<4segsh=2spp;1p;9p;5p;4p;7g0000j1<Tg000Pj10Tg0015j14Tg001Sj13Tg008Hj12Tg009Sl91Tg00:Kj5;Tg00;Wj15Tg00<Jj16Tg00=Ij17Tg00>Tl98Tg00?^j49Tg00@9j7:Tg00AIR0g002P#<g00BQg003Og003mg004m#0#0#0#0#0#0#4#3R1g005Rg006Rg0070g00CKf:R2#2f<R3f;R4P2P4f9R5f8R6f7R7f6R8f5R9f4R:f3R;f2R<M91f1R=D;f=P3P4P3P2P5P6P7P8P9P:P;M91R4P<%23%54#6#7P=P3P2P5P6P7P8P9P:P;M98C9f0R;F:W2W1W3W5W6W:X71X41W=W9W8W;W<X00P;O1W0o"). Qed.

(* [comment removed for export] *)
Lemma frm_safe_Ms0 : frm_safe Plain.M.loaded_segments.
Proof.
ltac2:(KReplay.run1 (kr_t_FrmInit ()) [] "h01ah11wh21Hh33segp;3p;1p;2p;4g00DSj3@Tg00Djj1?Tg00Enj15Tg00G0j24Tg00GNj31Tg000Pj10Tg0015j13Tg001Sj12Tg00Ghj16Tg00HJj27Tg00ILj28Tg00Inj29Tg00K0j2:Tg00KJj1>Tg00L`j3=Tg00N6j2<Tg00?^j4;Tg002PR0f0R1g00OMR25@0g00P[R0f1R3#?%53'4g00Q;31[]3g004m#0#0#0#0#0R4#0#3#2R5%34#2R4%64R617231841R7311923=167':R7%>3g00Q[510[]1]0g00R;f2?=31,<3X27X14X05C;o"). Qed.
Lemma frm_safe_Mu0 : frm_safe Ubsan.M.loaded_segments.
Proof.
ltac2:(KReplay.run1 (kr_t_FrmInit ()) [] "h01ah11wh21Hh33segp;3p;1p;2p;4g00DSj3@Tg00Djj1?Tg00Enj15Tg00G0j24Tg00GNj31Tg000Pj10Tg0015j13Tg001Sj12Tg00Ghj16Tg00HJj27Tg00ILj28Tg00Inj29Tg00K0j2:Tg00KJj1>Tg00SLj3=Tg00N6j2<Tg00?^j4;Tg002PR0f0R1g00TbR25@0g00P[R0f1R3#?%53'4g00Q;31[]3g004m#0#0#0#0#0R4#0#3#2R5%34#2R4%64R617231841R7311923=167':R7%>3g00Q[510[]1]0g00V0f2?=31,<3X27X14X05C;o"). Qed.
Lemma frm_safe_Ma0 : frm_safe Asan.M.loaded_segments.
Proof.
ltac2:(KReplay.run1 (kr_t_FrmInit ()) [] "h01ah11wh21Hh33segp;3p;1p;2p;4g00DSj3@Tg00Djj1?Tg00Enj15Tg00G0j24Tg00GNj31Tg000Pj10Tg0015j13Tg001Sj12Tg00Ghj16Tg00HJj27Tg00ILj28Tg00Inj29Tg00K0j2:Tg00KJj1>Tg00WAj3=Tg00N6j2<Tg00?^j4;Tg002PR0f0R1g00XWR25@0g00P[R0f1R3#?%53'4g00Q;31[]3g004m#0#0#0#0#0R4#0#3#2R5%34#2R4%64R617231841R7311923=167':R7%>3g00Q[510[]1]0g00Ydf2?=31,<3X27X14X05C;o"). Qed.
Lemma frm_safe_Mb0 : frm_safe AsanUbsan.M.loaded_segments.
Proof.
ltac2:(KReplay.run1 (kr_t_FrmInit ()) [] "h01ah13segh21wp;3p;1p;2p;4g00DSj3>Tg00Djj1=Tg00Enj15Tg00G0j24Tg00GNj31Tg000Pj10Tg0015j13Tg001Sj12Tg00Ghj16Tg00HJj27Tg00ILj28Tg00Inj29Tg00K0j2:Tg00KJj1<Tg00?^j4;Tg002PR0f0R1g00[5R25>0g00P[R0f1R3#=%53'4g00Q;31[]1g004m#0#0#0#0#0R4#0#3#2%34#2R4%64R517231841R4311923=154':%<3g00Q[510[]2]0g00\Gg00]ZC;o"). Qed.
