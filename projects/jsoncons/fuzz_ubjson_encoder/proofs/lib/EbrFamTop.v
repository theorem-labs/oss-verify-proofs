(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require BvWfKernel.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.jsoncons.fuzz_ubjson_encoder.images Require Import AsanUbsan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require Import PropExec CatSim StoreOk Hoare ShapeAlg SpinAlg AsanAcct HeapIface HeapIfaceA HeapIfaceAEx HeapIfaceAEr HeapIfaceANull IcptIfaceAB0
     ArtMem ArtRuns ArtBridge EbtLift EbrDep EarUkey EbrInv EbrInvFreePure EbrFsInv EbrFsInvLaws EbrFsInvLaws4 EbrWrapKit EbrWrapFreeR
     EbrWrapMallocAll EbrWrapFree EbrWrapMemI EbrWrapSmallocI EbrIfaceLaws EbrIfaceInst EbrIfaceInstFree EbrIfaceInstAnn EbrIfaceInstSfree EbrIfaceLayoutPM
     EbrIcptInst EbrIcptLawsGap EbrFam.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require Import StrictOfB L5Defs PeSpecsAb PeBCxa PeBImgGap PeCTopAsmB.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require KReplay.
Ltac2 kr_t_EbrFamTop () := "I47Corelib4Init9Datatypes4list00C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib6EbrInv8art_rn_kC13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib?EbrWrapSmallocI@art_inst_smallocC13~~~K47Corelib7Numbers7BinNums1Z02K47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums8positive01K47Corelib4Init9Datatypes4list01K47Corelib4Init9Datatypes4list02C46Stdlib5Lists4List2InC79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib6EbrInv5rn_arC13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib6EbrFam7art_HIkC13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib:HeapIfaceABastack_malloc_specC13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib@EbrIfaceInstFree=art_inst_freeC13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib<EbrIfaceInst;art_inst_okC13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib6EbrInv9art_ifaceC13~~~I89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib<HeapIfaceAEx3HAJ>asan_iface_okR00C13~~~K79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib6L5Defs5ScfgP01C13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib6L5Defs4SCFGC13~~~I79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib<IcptIfaceAB08aicpt_ok00C13~~~I89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib<HeapIfaceAEx3HAJ;asan_ext_ok00C13~~~C89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib9PeBImgGap6PMBGAP:rt_img_gapC13~~~I47Corelib4Init5Logic3and00C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib;EbrIcptInst;art_icpt_okC13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib?EbrIfaceInstAnnAart_inst_annotateC13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib<EbrIfaceInstBart_inst_frame_ctrC13~~~C89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib6PeBCxa6PMBCXA=cxa_atexit_okC13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib@EbrIfaceInstFreeBart_inst_free_nullC13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3libAEbrIfaceInstSfree?art_inst_sfree5C13~~~K89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib<HeapIfaceAEx3HAJ;asan_ext_ok01C13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib>EbrIcptLawsGap?art_law_img_gapC13~~~K47Corelib4Init5Logic3and01I47Corelib7Numbers7BinNums1Z00I79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib6EbrInv7art_run00C13~~~K47Corelib7Numbers7BinNums1Z01K47Corelib7Numbers7BinNums8positive03C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib<EbrIfaceInst5art_LC13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib<EbrIfaceInst5art_CC13~~~I79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8EbrFsInv7art_fsg00C13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8EbrFsInv9art_fsinvC13~~~C89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib9PeSpecsAb3PMB3EXTC13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib@EbrIfaceLayoutPM>art_pma_layoutC13~~~I89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib<HeapIfaceAEr3HAR<asan_famR_ok00C13~~~C89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib:PeCTopAsmB7PECASMB7inst_okC13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib6EbrFam:art_fam_okC13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib6EbrFam6art_LRC13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib9EbrFamTop<art_fam_instC13~~~".
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

#[local] Abbreviation ASEGS := AsanUbsan.M.loaded_segments.

Section FamTop.
Variables MAPS0 RESV0 NOACC0 : list (word * word).
Variables BASE BUDGET : Z.
Variable rn : art_run.
Variable scfg : SpuriousCfg.
Variable IL : icpt_layout.
Hypothesis Halloc : sc_alloc scfg = false.
Hypothesis Hwx : wx_segs_nowrap ASEGS.
Hypothesis STATIC : bridge_static ASEGS MAPS0 RESV0 NOACC0 (art_RES rn) (rn_HI rn) BUDGET LENMAX KMAX.
Hypothesis Htp : rn_tp rn = 0x67a180.
Hypothesis Hkey0 : rn_key rn = 0.
Hypothesis Htsd : rn_tsd rn = 0x69b638.
Hypothesis Hloff : rn_loff rn = 0x10.
Hypothesis ILY : as0_icpt_layout IL.

#[local] Abbreviation HIk := (art_HIk MAPS0 RESV0 NOACC0 BASE BUDGET rn).

(* [comment removed for export] *)
#[using="Halloc Hwx STATIC Htp Hkey0 Htsd Hloff ILY"]
Theorem art_fam_inst : forall D, @PECASMB.inst_ok (MkScfgP scfg) art_L art_C IL (rn_ar rn) (HIk D).
Proof.
ltac2:(KReplay.run1 (kr_t_EbrFamTop ()) ["FamTop"] "h01Dh13OKRh22SMh31kh43rnDp;1p;2p;9p;3p;7p;5p;;p;@p;8p;>p;:p;6p;4g0000j17Tg000Pj2NTg001Zl9>Tg0035j11Tg003Sj1MTg0048j15Tg004]j1?Tg005=j30Tg005]j3<Tg0064j16Tg007;j78Tg008Dj59Tg009\l;:Tg00;5l@LTg00<Hj8KTg00=Sj54Tg00>oj1ITg00@8j1HTg00A>j5BTg00BPj5@Tg00Cij1ATg00E?j23Tg00EZl>=Tg00Fll9CTg00HHl:DTg00Ibj8ETg00K8l9FTg00LVl9GTg00N2l:;Tg00OKj6JTg00Pdj42Tg00Q?R0#7#7p,2rnR1f0R2'Ng00Q]p,5MAPS0R3p,5RESV0R4p,6NOACC0R5p,4BASER6p,6BUDGETR7P2p,4scfgR8p,3HwxR9p,3HtpR:M9>g00Rhg00SFR;#1%M;R<#1%5;#1%5<#1%?05005005005005009<02g00SkR<%61R;P8P3P4P5P6P7P1f3F8R1f1R=D9[^30P3P4P5P6P7P=P8p,6HallocR0P9p,6STATICR>P:p,5Hkey0R?p,4HtsdR@p,5HloffRAP3P4P5P6P7P=P8P0P9P>P:M;:P2M@LP<%6=g00U8R>P8g00VEP3P4P5P6P7g00WRP=GKD4P<P;P>%I8R=#HR0P1D4P<P;p,2ILRBP0P1DBRCP<P;P0P1g00X_RDD@RE%A1RF'3RG'3P2PCPGP8PBP7P9p,3ILYP3P4P5P6f2RBP:P?P@PAM>=PEPFP<P;P0P1PDP3P4P5P6P7PBP8P9P:M9CP=P<P;P>P1g00YkP2P3P4P5P6P7PBP:P?P@PAM:DRAGEPAP3P4P5P6P7PBP8P9P:M9FP3P4P5P6P7PBP8P9P:M9GM:;P3P4P5P6P7PBEJC2C2C2b1b2b4W0o"). Qed.

(* [comment removed for export] *)


(* [comment removed for export] *)
#[using="Halloc Hwx STATIC Htp Hkey0 Htsd Hloff ILY"]
Theorem art_fam_top : @PECASMB.fam_ok (MkScfgP scfg) art_L art_C IL art_LR (rn_ar rn) HIk.
Proof.
ltac2:(KReplay.run1 (kr_t_EbrFamTop ()) ["FamTop"] "h01Dp;1p;6p;7p;>p;4g0064j19Tg00>oj18Tg00@8j12Tg007;j61j73Tg00[Ej67Tg0000j10Tg00\_j64Tg00^4l>5Tg00Pdj46Tg00SkR0p,2rnR1#9R2g00U8R3p,4scfgR4#8R5#2g00_@p,5MAPS0R6p,5RESV0R7p,6NOACC0R8p,4BASER9p,6BUDGETR:P1E1E7g00Q?#0#0P5P0P3p,2ILP2P6P7P8P9P:P1f0F3E4]0P6P7P8P9P:P1P4p,6Hallocp,3Hwxp,6STATICp,3Htpp,5Hkey0p,4Htsdp,5HloffM>5g00`HC6o"). Qed.
End FamTop.
