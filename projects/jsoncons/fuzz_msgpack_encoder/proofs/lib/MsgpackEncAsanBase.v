(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require BvWfKernel.
(* [comment removed for export] *)
From Stdlib Require Import NArith ZArith List Lia Bool.
From Stdlib Require Import QArith_base.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence MustExit FinInput Classifier Measure.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.jsoncons.fuzz_msgpack_encoder.images Require Plain.
From OSSVerify.jsoncons.fuzz_msgpack_encoder.images Require Asan.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require PropExec. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0084. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0089. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0092. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0179. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0080. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0123. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0289. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0213. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0024. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0290. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0253. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0260. Require OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0102. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require PnALayFacts. From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require MsgpackEncImgFacts MsgpackEncFinalS MsgpackEncAsanTop MsgpackEncAsanAsm MsgpackEncAsanRows. Import OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.PropExec OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0038.StoreOk OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0084.HeapIface OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0089.HeapIfaceA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0089.IcptIfaceA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090.LibIface OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0092.LibIfaceAB OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0084.L5Defs OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090.L5Core OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0179.L5DefsA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0089.HeapIfaceAMx OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0080.HeapIfaceAMxI OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0089.HeapIfaceAMr OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0123.NarIfaceInst OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0289.NarFam OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0090.PmSpecs OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0213.PmSpecsA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0213.PnSpecsAa OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0024.PnLayoutA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0024.PnLayoutQA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0290.NTopAsmA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0253.PnATsTsw OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0260.PnATsVPot OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0260.PnATs12Pot OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0102.NemModel OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0260.NemSpecsTsA OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.Mh_0260.PnAEncTobK OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.PnALayFacts OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.MsgpackEncImgFacts OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.MsgpackEncFinalS OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.MsgpackEncAsanTop OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.MsgpackEncAsanAsm OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib.MsgpackEncAsanRows.
From OSSVerify.Proofs.jsoncons.fuzz_msgpack_encoder.lib Require KReplay.
Ltac2 kr_t_MsgpackEncAsanBase () := "C59OSSVerify5KrLib7Mh_00849HeapIface6creditC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic8eq_ind_rI47Corelib4Init9Datatypes4prod00K47Corelib7Numbers7BinNums8positive01K47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1Z02K47Corelib4Init9Datatypes4prod01K47Corelib4Init5Logic2eq01I47Corelib4Init5Logic2eq00I47Corelib7Numbers7BinNums1Z00K47Corelib7Numbers7BinNums8positive03c49OSSVerify5KrLibBMsgpackEncAsanBase6RES_MEC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib;PnALayFacts6RES_okC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z2ltC56Stdlib6ZArith6BinInt1Z3powC56Stdlib6ZArith6BinInt1Z:pow_nonnegC56Stdlib6ZArith6BinInt1Z7compareK47Corelib4Init9Datatypes4list01I47Corelib4Init9Datatypes4list00K46Stdlib9micromega6VarMap1t01I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr01K47Corelib7Numbers7BinNums1N02K46Stdlib9micromega7EnvRing5PExpr07K46Stdlib9micromega7EnvRing5PExpr05C46Stdlib9micromega5Tauto8BFormulaC46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundC56Stdlib6ZArith6BinInt1Z2leI47Corelib4Init5Logic3and00C56Stdlib6ZArith6BinInt1Z3mulC47Corelib4Init9Datatypes3fstC47Corelib4Init9Datatypes3sndK46Stdlib9micromega=RingMicromega7Formula01K46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega5Tauto8GFormula05K47Corelib7Numbers7BinNums1Z01K46Stdlib9micromega=RingMicromega3Op203C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K47Corelib4Init9Datatypes4unit01I47Corelib4Init5Logic4True00I47Corelib4Init9Datatypes:comparison00I46Stdlib9micromega:ZMicromega;ZArithProof00I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01c49OSSVerify5KrLibBMsgpackEncAsanBase:RES_ME_valC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0260:PnAEncTobK7PNAETBK9TSPE_lawsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_02896NarFam6art_LRC1?~~~~~~~~~~~~~~~K46Stdlib9micromega6VarMap1t02K46Stdlib9micromega6VarMap1t03K46Stdlib9micromega7EnvRing5PExpr02C69OSSVerify5KrLib7Mh_02609PnATsVPot7PQATSPV7T12VMAXC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_00907PmSpecs4PMSP9credit_leC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0123<NarIfaceInst5art_LC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02538PnATsTsw7PQATSTW6TSWMAXC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_0260;NemSpecsTsA5NETSA7TSPEMAXC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib7Mh_02908NTopAsmA6NTASMA6fam_okC1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic3and01K69OSSVerify5KrLib7Mh_02908NTopAsmA6NTASMA6open_A01C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib7Mh_0089:HeapIfaceA8asan_run00C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib7Mh_0089:HeapIfaceA:asan_iface00C1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib@MsgpackEncFinalS:ScfgP_cfg0C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7Mh_0123<NarIfaceInst5art_CC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib;PnALayFacts6art_ILC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib7Mh_0089:HeapIfaceA;asan_layout00C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib7Mh_0089:HeapIfaceABasan_statics_cells00C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib7Mh_0089:IcptIfaceA;icpt_layout00C1?~~~~~~~~~~~~~~~I69OSSVerify5KrLib7Mh_0089<HeapIfaceAMr3HAR7layoutR00C1?~~~~~~~~~~~~~~~C49OSSVerify5KrLibAMsgpackEncAsanAsm7na0_tgtC1?~~~~~~~~~~~~~~~c49OSSVerify5KrLibBMsgpackEncAsanBase9RES_ME_okC1?~~~~~~~~~~~~~~~c49OSSVerify5KrLibBMsgpackEncAsanBase5RESGEC1?~~~~~~~~~~~~~~~K49OSSVerify5KrLibBMsgpackEncAsanRows9open_asan01C1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib@MsgpackEncFinalS=open_S_closedC1?~~~~~~~~~~~~~~~c49OSSVerify5KrLibBMsgpackEncAsanBase>na0_tgt_closedC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLibBMsgpackEncAsanRowsKmsgpack_enc_asan_base_abortC1?~~~~~~~~~~~~~~~c49OSSVerify5KrLibBMsgpackEncAsanBase<open_asan_ofC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLibBMsgpackEncAsanRowsEmsgpack_enc_asan_baseC1?~~~~~~~~~~~~~~~".
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
Definition TSPE : Z -> Z -> list (list Z) -> list Z -> credit := NETSA.TSPE art_LR.
Definition RES_ME : credit := PQATSPV.T12VMAX art_L PQATSTW.TSWMAX NETSA.TSPEMAX.
Lemma RES_ME_val : RES_ME = (206, 29362816).
Proof.
ltac2:(KReplay.run1 (kr_t_MsgpackEncAsanBase ()) [] "p;2p;1p;4p;3g0000R0p4p70p1000mp4p710p8g001Kj27Tg001kj11Tg002Pj12Tg0035j13Tg003Sj46Tg0043j25Tg004Mj34Tf0#2#2p=0g004gR1/71P1P1g005E#1R1#0#1#1#1#2#3%11#0#0#0#0#0#1#2#1#2#1#2#0#0#0#3C6R1'5g005j=401do"). Qed.
Lemma RES_ME_ok : RES_ok RES_ME.
Proof.
ltac2:(KReplay.run1 (kr_t_MsgpackEncAsanBase ()) [] "h02Hah16__sat1h27__arithh34__ffh46__sat0h58__varmaph65__with71cp;1p;4p;2p;3p;6p;7g0000R0p4p70g000mR1p4p710p8g001kj10Tg002Pj12Tg0035j16Tg003Sj4VTg006hj1<Tg007_j2KTg008Gj2;Tg008cj2BTg009@j3ATg009dj2?Tg0043j2=Tg00:Ej1UTg00:ej1TTg00;Ej1STg00;cj1MTg00<Aj1LTg00<lj24Tg00=Oj1ETg00=mj3DTg00>Pj3FTg00?3j2CTg00?Uj2GTg004Mj3HTg00@Aj3ITg00@`j4JTg00ARj27Tg00Anj25Tg00BIj2@Tg00Bfj3NTg00CCj3OTP1j6PTg00C`j4QTg00DKj7>Tg00Doj7RTf0R1#2#2p=1g00ESR2/71p=3g004gR3f1R4g00F1P1CQp=9P4g00FXR5g00G7R6P6g00GWR7P1g00H7F>p=8f2R8P5P6P6P7P4P1FRp=:P0P3P3g005ER6#0R5#1#0#0#0#2#6R9%05R:#1#1#1#1#1#0#2#0#2#0#2#1#1#1#6R;CVR<%<1X70%26R6#6R0%0:#2R:#6R='K1;20R>%3=1B0=R?,;2[R@[%30RAg00HWRBAA0=4UW0%3?\B^0AP4g00I31?20'=P>eO1P@g00IYR@#U%T@%S3%M3%L3R@1432R>1439RA'9,8@%06#2#0#0#0#0#1#6R6,43,9A,8@5:@143;RA,9>,8@%65R5,431430%E:5D35F3,9A,8@5:@3:1C@7P1P8g00JER@g00JeR7'=1G18=H@7dAI324CJb3b5b6%391796'5%3;1@5?R5,7;'5'5P1b2b1b4b1AN33<R1#31716'5AO33<R3#31735'5'5e%<<eg005jg00KEEPo"). Qed.
Lemma TSPE_OK : @NTASMA.tspe_laws TSPE NETSA.TSPEMAX.
Proof.
ltac2:(KReplay.run1 (kr_t_MsgpackEncAsanBase ()) [] "p;1p10000p4p70p1000mp4p710p8g00LGj10Tg00MP#0o"). Qed.
Lemma RESGE : PMSP.credit_le (PQATSPV.T12VMAX art_L PQATSTW.TSWMAX NETSA.TSPEMAX) RES_ME.
Proof.
ltac2:(KReplay.run1 (kr_t_MsgpackEncAsanBase ()) [] "h04__x1h14__x2h27__arithh34__ffh48__varmaph55__witp;1p;2p;4p;7p;3p10000p4p70p1000mp4p710p8g00:Ej1HTg00:ej1GTg00NJj26Tg00;Ej14Tg00Nhj4FTg00;cj1;Tg00<Aj1:Tg00OFj23Tg00C`j42Tg002Pj17Tg00Doj78Tg00?3j29Tg0043j2ETg00?Uj2BTg004Mj3>Tg00@Aj3<Tg00@`j4=Tg00ARj21Tg00Anj2?Tg00Oij3@Tg00CCj3ATg00Bfj35Tg00Poj2CTg00DKj7DTf1R0g00FXR1g00G7R2P2g00GWR3f0R4g00H7FDp=0g004gR5g00IYR6#H%G6P5f2R6,65P0%45CF%;5%:5R7P1P2P2P3P5g005ER2,35R1g00F1R8P1C2,07P5%72,35R2P8P2C2,07F81973P4P6g00JER7g00JeR3'E1B46=>73dg00ES=<50C=b3b4b5X05W111441100'?^05^15P4g00R2g00S1g00T53@R49A55A5554O2b2g005j,C4eo"). Qed.

Section Base.
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma OPENA_closed : forall (ar : asan_run) (HIk : list (list Z) -> asan_iface),
    @NTASMA.fam_ok ScfgP_cfg0 art_L art_C art_IL art_LR ar HIk -> @NTASMA.open_A art_L art_C art_IL art_LR ar HIk RES_ME.
Proof.
ltac2:(KReplay.run1 (kr_t_MsgpackEncAsanBase ()) ["Base"] "h03FAMh13HIkh22arp;1p;7p;3p;2p;4p;8g0000R0p4p70p1000mp4p710p8g00:ej14Tg00U;j76Tg004Mj30Tg00Anj23Tg0043j21Tg00V>j42Tg00VYj85Tg00W^R1g004g#4#4g00X`[R2g00Ydg00R2R3g00ZdR4g00[cR5g00MPR6f1R7f0F6P3P4P5P6f2R8P7g005jR9g00\ZR:?033g00]_R;?044R<g00^kR=?055R>g00`0R??066R@A0188RAA0277RBA0099RC'3RD'3RE'3RF'3RG'311:3P<PG11;4P>PF11=5P@PE11?6PAPD1118PBPC11271109C2C2C2C2C2C2G5W0W1W2o"). Qed.
Let OPENA := OPENA_closed.

(* [comment removed for export] *)
Lemma na0_tgt_closed : as0_tgt_stmt cfg0.
Proof.
ltac2:(KReplay.run1 (kr_t_MsgpackEncAsanBase ()) ["Base"] "p;4p10000p4p70p1000mp4p710p8g00a7j40Tg005jg00b5g00c6p,5OPENAC0o"). Qed.
Lemma open_asan_of : open_asan.
Proof.
ltac2:(KReplay.run1 (kr_t_MsgpackEncAsanBase ()) ["Base"] "p;2p10000p4p70p1000mp4p710p8g00d3j20Tg00e6g00f9'0o"). Qed.

(* [comment removed for export] *)
Theorem msgpack_enc_asan_base_abort_c :
  strong_universal_error_free_T_scfg_budgets_abort cfg0 SanitizerBudgets.lim_source SanitizerBudgets.lim_target
    (mkImage OSSVerify.jsoncons.fuzz_msgpack_encoder.images.Plain.M.loaded_segments OSSVerify.jsoncons.fuzz_msgpack_encoder.images.Plain.M.init_pc OSSVerify.jsoncons.fuzz_msgpack_encoder.images.Plain.M.phdrs)
    (mkImage OSSVerify.jsoncons.fuzz_msgpack_encoder.images.Asan.M.loaded_segments OSSVerify.jsoncons.fuzz_msgpack_encoder.images.Asan.M.init_pc OSSVerify.jsoncons.fuzz_msgpack_encoder.images.Asan.M.phdrs).
Proof.
ltac2:(KReplay.run1 (kr_t_MsgpackEncAsanBase ()) ["Base"] "p;1p10000p4p70p1000mp4p710p8g00g?j10Tg00hR#0o"). Qed.

(* [comment removed for export] *)
Theorem msgpack_enc_asan_base_c :
  strong_universal_error_free_T_scfg cfg0
    (mkImage OSSVerify.jsoncons.fuzz_msgpack_encoder.images.Plain.M.loaded_segments OSSVerify.jsoncons.fuzz_msgpack_encoder.images.Plain.M.init_pc OSSVerify.jsoncons.fuzz_msgpack_encoder.images.Plain.M.phdrs)
    (mkImage OSSVerify.jsoncons.fuzz_msgpack_encoder.images.Asan.M.loaded_segments OSSVerify.jsoncons.fuzz_msgpack_encoder.images.Asan.M.init_pc OSSVerify.jsoncons.fuzz_msgpack_encoder.images.Asan.M.phdrs).
Proof.
ltac2:(KReplay.run1 (kr_t_MsgpackEncAsanBase ()) ["Base"] "p;1p10000p4p70p1000mp4p710p8g00iVj10Tg00hR#0o"). Qed.
End Base.
