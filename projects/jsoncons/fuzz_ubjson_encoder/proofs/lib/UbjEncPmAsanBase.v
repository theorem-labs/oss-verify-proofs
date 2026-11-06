(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require BvWfKernel.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.jsoncons.fuzz_ubjson_encoder.images Require Import Plain.
From OSSVerify.jsoncons.fuzz_ubjson_encoder.images Require Import Asan AsanUbsan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require Import BMode ShapeAlg SpinAlg HeapIface LibIface LibIfaceE L5Defs
     UbjEncShapes UbjEncGLink FrmInit Es0HeapBridgeHe PeSpecsS PeCSink PeCSpecs PeCSpecsS PeCTopS PeCTopAsmS
     PeHeapS PeHeapP Es0OpnewS Es0OpdelS PeSSinkPush UbjEncPmPay UbjEncPmStated UbjEncPmBase
     AsanAcct HeapIfaceA HeapIfaceAEx HeapIfaceAEr IcptIfaceA IcptIfaceAB0 EarIfaceInst EarFam EbrIfaceInst EbrFam PeALayFacts PeBLayFacts PeCSinkA PeCTopAsmA PeCTopAsmB
     UbjEncPmAsanAsmA UbjEncPmAsanAsmB.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.Heap Require Import HeIface HeInst0 HeV16 HePmLayout.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.Spec Require Import UbjRef UbjRefFacts.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require PropExec.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require KReplay.
Ltac2 kr_t_UbjEncPmAsanBase () := "K47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1Z02K47Corelib4Init5Logic2eq01K47Corelib7Numbers7BinNums8positive01C56Stdlib6ZArith6BinInt1Z3powI47Corelib4Init5Logic2eq00I47Corelib7Numbers7BinNums1Z00K47Corelib7Numbers7BinNums8positive03C5ELinuxProcessSemanticsEEquivalenceDefinition;Equivalence@SanitizerBudgets:lim_sourceC5ELinuxProcessSemanticsEEquivalenceDefinition;Equivalence@SanitizerBudgets:lim_targetC79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib>UbjEncPmStated3tbSC13~~~C56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z2ltC56Stdlib6ZArith6BinInt1Z:pow_nonnegC56Stdlib6ZArith6BinInt1Z7compareK47Corelib4Init9Datatypes4list01I47Corelib4Init9Datatypes4list00K46Stdlib9micromega6VarMap1t01I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr01K47Corelib7Numbers7BinNums1N02K46Stdlib9micromega7EnvRing5PExpr07K46Stdlib9micromega=RingMicromega7Formula01C46Stdlib9micromega5Tauto8BFormulaC46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundC56Stdlib6ZArith6BinInt1Z2leK46Stdlib9micromega7EnvRing5PExpr03C56Stdlib6ZArith6BinInt1Z3addC89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib7PeCSink4PESK7SP_S_okC13~~~I89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib7PeCSink4PESK>sink_policy_ok00C13~~~K46Stdlib9micromega5Tauto8GFormula04K47Corelib7Numbers7BinNums1Z01C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K47Corelib4Init9Datatypes4unit01C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib5BMode:bm_on_instC13~~~I47Corelib4Init5Logic4True00I47Corelib4Init9Datatypes:comparison00I46Stdlib9micromega:ZMicromega;ZArithProof00K46Stdlib9micromega=RingMicromega3Op203I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib@UbjEncPmAsanBase5P_S31C13~~~I45stdpp9bitvector;definitions2bv00C4ELinuxProcessSemantics?LinuxProcessSem3Run8valid_spC45stdpp9bitvector;definitions;bv_unsignedC79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib<UbjEncPmBase;valid_sp_loC13~~~C89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib4Heap:HePmLayout<pm_layout_L0C13~~~C89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib4Heap7HeInst02L0C13~~~I89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8PeSpecsS3PMS6layout00C13~~~C4ELinuxProcessSemantics?LinuxProcessSem3Run8sc_allocC79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib?Es0HeapBridgeHe;HIV0_okS_atC13~~~I89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib4Heap7HeIface>heap_ifaceS_ok00C13~~~C89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib7PeCSink4PESK4SP_SC13~~~I89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib:PeCTopAsmS7PECASMS9rows_open00C13~~~C89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib9Es0OpnewS6L5NEWS9opnewS_okC13~~~C89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib9Es0OpdelS6L5DELS9opdelS_okC13~~~C89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib7PeHeapP4PEHP;opdelP_of_SC13~~~K89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib:PeCTopAsmS7PECASMS9rows_open01C13~~~C47Corelib4Init5Logic6eq_indC89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib4Heap5HeV164HIV0C13~~~C89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib7PeHeapP4PEHP;opnewP_of_SC13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib@UbjEncPmAsanBase:ScfgP_cfg0C13~~~C79OSSVerify8jsonconsCfuzz_ubjson_encoder6images5Plain1M?loaded_segmentsC13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib9PeLayoutS6ADDR_SC13~~~C89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib;PeSSinkPush5PESSK5NMAXPC13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib>UbjEncPmStated4cfg0C13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib@UbjEncPmAsanBaseBlim_source_san_valC13~~~C89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib:PeCTopAsmS7PECASMS2tbC13~~~C89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib7PeCTopS5PECTS6TopLayC13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib>UbjEncPmStated4LStSC13~~~C89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib4Heap5HeV167HIV0_okC13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib<UbjEncPmBase4KPM0C13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib@UbjEncPmAsanBase8ROWS_S31C13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib;UbjEncPmPay8pay_in_SC13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib;UbjEncPmPay9pay_out_SC13~~~C89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib9PeCSpecsS5PECSS7pay_outC13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib>UbjEncPmStated4LaySC13~~~I79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib9LibIfaceE>lib_iface_ok_x00C13~~~C89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib:PeCTopAsmS7PECASMS=top_iface_asmC13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib@UbjEncPmAsanBase3G_AC13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib@UbjEncPmAsanBase6PO_S31C13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib@UbjEncPmAsanBase9PMODE_S31C13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib@UbjEncPmAsanBase6tb_S31C13~~~C4ELinuxProcessSemantics?LinuxProcessSem3Run5sc_fsC79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib5BMode5bm_onC13~~~K47Corelib4Init5Logic2or01C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib?Es0HeapBridgeHeGsrc0_realizes_spec_heapC13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib>UbjEncPmStated4DLLSC13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib@UbjEncPmAsanBase6LIBS31C13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib>UbjEncPmStated4LSXSC13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib>UbjEncPmStated7BudgetSC13~~~K47Corelib4Init5Logic4True01C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib?Es0HeapBridgeHeDsrc0_realizes_G_heapC13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib;UbjEncGLink=ue_base_abortC13~~~C89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib>UbjEncPmStated2ES?loaded_segmentsC13~~~C89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib>UbjEncPmStated2ES7init_pcC13~~~C89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib>UbjEncPmStated2ES5phdrsC13~~~c89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib@UbjEncPmAsanBase2EA?loaded_segmentsC13~~~c89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib@UbjEncPmAsanBase2EA7init_pcC13~~~c89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib@UbjEncPmAsanBase2EA5phdrsC13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib7FrmInit<frm_safe_Ms0C13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib7FrmInit<frm_safe_Ma0C13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib@UbjEncPmAsanBase8norm_S31C13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib@UbjEncPmAsanBase9weird_S31C13~~~c89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib@UbjEncPmAsanBase2EB?loaded_segmentsC13~~~c89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib@UbjEncPmAsanBase2EB7init_pcC13~~~c89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib@UbjEncPmAsanBase2EB5phdrsC13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib7FrmInit<frm_safe_Mb0C13~~~".
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

#[local] Instance ScfgP_cfg0 : ScfgP := {| SCFG := cfg0 |}.

Module EA := Asan.M.
Module EB := AsanUbsan.M.

(* [comment removed for export] *)
Definition GB_A : Z := 2 ^ 30.
Definition G_A (p : list byte) : Prop := UbjRefFacts.F (map bv_unsigned p) <= GB_A.
(* [comment removed for export] *)
Definition P_S31 : PESK.sink_policy := @PESK.SP_S bm_on_inst (2 ^ 31).

Lemma lim_source_san_val : SanitizerBudgets.lim_source = 2 ^ 31.
Proof.
ltac2:(KReplay.run1 (kr_t_UbjEncPmAsanBase ()) [] "p;1p;2p;3g0000j11Tg000Uj13Tg0013j26Tg001Mj12Tg0022j25Tg002Oj34Tf0R0#1#1p=7%10#1#1#1p=0g002iR0g003GR1#1R2#7#0#0#0#0#0#0#0#3'6g003l%32%21#2#2#2#3'5540do"). Qed.
Lemma lim_target_san_val : SanitizerBudgets.lim_target = 2 ^ 39.
Proof.
ltac2:(KReplay.run1 (kr_t_UbjEncPmAsanBase ()) [] "p;1p;2p;3g0000j10Tg000Uj12Tg0013j26Tg001Mj13Tg0022j25Tg002Oj34Tf0R0#0#0#0#0p=7%00#0#0#0#0#0#0#0p=1g002iR0g003G#0R1#0R2#0#7#1#1#1#1#2'6g005B%21%32#3#3#2'5540do"). Qed.
Lemma tb_S31 : PECASMS.tb P_S31 = tbS.
Proof.
ltac2:(KReplay.run1 (kr_t_UbjEncPmAsanBase ()) [] "p;2g0013j20Tg002ig006X'0o"). Qed.
Lemma PO_S31 : PESK.sink_policy_ok P_S31.
Proof.
ltac2:(KReplay.run1 (kr_t_UbjEncPmAsanBase ()) [] "h02Hah16__sat1h27__arithh34__ffh46__sat0h56__sat3h66__sat5h78__varmaph85__with96__sat2h:6__sat4p;1p;2p;3p;4p;7g0000j14Tg000Uj13Tg001Mj12Tg0022j29Tg007ej2;Tg008Mj25Tg008ij38Tg009Mj2ETg0013j2>Tg009nj1CTg00:Nj1ATg00:nj1@Tg00;Lj1OTg00;jj1NTg00<Uj2?Tg00=8j16Tg00=Vj3:Tg00>9j4=Tg00>dj2MTg00?Fj2JTg002Oj3ITg00@2j3HTg00@Qj4FTg00ACj27Tg00A_j3GTg00BBj2DTg00B_j4KTg00Cnj1LTg00EFj7BTg00EjR0f0R1'7p=1%41#4p=0f1R2g00FHg00FgR3P3g00GGR3P1g00GgFBp=<g00HGg003GR4#4R5#3R6%24#2#2R4#2R7#3R8'9R91;68R:1506R;%181509[R<[R=%16R>g00IRR?A8682UW0R8%19\?^0>R@P2g00In1E06'>P;eRAO1RBP<g00JTRC#CRD%ACRCg002iRE#@RF%OERG%NERHPE%05R5#0#0#0#0#0#0#0#3RI,?Eg00K@RJ1?E6RK%675:ER7C='<1MH3R3P1f2RLg00KgRMg00LGRN'>1J1L=IMNdAHE02CFRNb3b7b817I9RIP1b2b1b4b1PIe%25#4R5#3RI,;6%1I196IRM,50[RL\;A86I2V?X0>%1M\?^0>P:P=P8P@%44R4#3R@,;6%1@196@R8,50[R0\;A86@2V?X0>%18\?^0>PBP0f4PAO1P<f7PAO1PLPDPCPFPGPEP7PJ%659:EK%649:EK5GEC=,<HP3PNb3b7b81DM8,79R9P1b2b6b5b1b4b1b9b5b:b6P9eCKg00Lg#Leo"). Qed.
Lemma PMODE_S31 : PESK.sp_mode P_S31.
Proof.
ltac2:(KReplay.run1 (kr_t_UbjEncPmAsanBase ()) [] "p;2g0013j20Tg00Kgg00LG'0o"). Qed.

Section AsanBases.
#[local] Existing Instance PropExec.fx0.

(* [comment removed for export] *)
Lemma ROWS_S31 : forall sp, valid_sp sp ->
  @PECASMS.rows_open _ bm_on_inst (HeInst0.L0 (bv_unsigned sp)) (@HeV16.HIV0 bm_on_inst (bv_unsigned sp) SanitizerBudgets.lim_source) P_S31.
Proof.
ltac2:(KReplay.run1 (kr_t_UbjEncPmAsanBase ()) ["AsanBases"] "h03HISh12LYh21Vh32sph41zp;1p;2p;5p;7p;8p;6p;3p;9g0000j10Tg00=8j1JTg00N8j1>Tg00N[j1:Tg00OPj21Tg00P:j2HTg00QMj2?Tg00Rdj13Tg00Snj1<Tg00U>j1;Tg0013j29Tg00V3j58Tg00WIj5ITg00Xaj27Tg00Ymj56Tg00[Fj7GTg00\[j7BTg00^0j8@Tg00_Cj7ATg000Uj15Tg001Mj12Tg0022j2=Tg00`\j6DTg00a8j3ETg00bBl9FTg00HGR0f0R1g003lR23Ep=4g00cUR3P0g00dkR4g00f9R5f2R6f1R7P2g00gDP1M9Fp=Cg003GR8#0R9#0#0#0#0#0#JR:#>%:111:7R;1H71'?%3;#<g00hVR;P0g00Kg%;;'9P6P2D811:6R6#3P;P0%46P2DIg002iR6P2P3P0f4,1:R;#3%4;1701D6X46P3P0f3,1:R:#3R6%4:R:1702P3P0P6P:P7P2P1FG9C6:P3P0P4P5P6P:P2P3P0P6P:P7P2P1FBG@FA%59%28#2#2#2#5'=g00idEDP3P0P6P:g00LgD6eb0b1W2W3o"). Qed.

(* [comment removed for export] *)
Lemma LIBS31 : forall sp, valid_sp sp ->
  @lib_iface_ok_x (LayS sp) cfg0 bm_on_inst (@HeV16.HIV0 bm_on_inst (bv_unsigned sp) SanitizerBudgets.lim_source) (LStS sp) (fun _ => True) G_A.
Proof.
ltac2:(KReplay.run1 (kr_t_UbjEncPmAsanBase ()) ["AsanBases"] "h01Vh17__arithh24__ffh38__varmaph45__with52sph61zp;1p;2p;3p;5p;4p;7p;6p;?g0000j10Tg00=8j1<Tg00N8j1:Tg00N[j1@Tg00kBj1ZTg00OPj27Tg00Rdj16Tg00lRj2DTg00a8j34Tg00maj15Tg00:Nj13Tg00P:j2=Tg00QMj2YTg00U>j1UTg0013j29Tg00noj5OTg010<j1NTg011Hj2KTg000Uj12Tg001Mj11Tg0022j2HTg012\j3CTg009nj1ETg00:nj1FTg00;Lj1BTg00;jj1GTg00<Uj28Tg00>9j4ATg00EFj7ITg00>dj2JTg00?Fj2?Tg002Oj3LTg00@2j3MTg00@Qj4>Tg00ACj2PTg013kj3QTg015;j2RTg00`\j6TTg016Mj1XTg017[j7WTg0190l?VTf3R0g00hVR1g00HGR2f2R3f1R4f0R5g01:KR6FWp=;g00cUP2P5P4g00LgR7P3P0f4g01;Zg01<lf5f6P6f7f8M?Vp=Sg003GR0#0R8#0R9#0R:#0#0#0#<R;#:%@5g002iR<%Z717;3R=#6/D5g003lR>942=%53%<:#:#3g00IRUR:C;X6<17;4R;#6A42;>R=1=45,Y;P2P;P>P1g00KgR>%U1'9DO%N;1K45P:%28%10#1#1#1#2R0'H=C2:g00JTR8#E%38%F<%B<%G<R8g00FHg00FgR;P;g00GGR;P<%19#0#2R9,8<g00K@18<0CAg00GgFI1J8;P5P3g00LGR;,9>1?53=L>;dg00Ej=M<4C>b2b3b41P90P5b19Q201R76eM9Sg006Xg01>AET%X4P=%54P:C;eW0W5o"). Qed.

(* [comment removed for export] *)
Lemma norm_S31 : @plain_norm_stmt ES.loaded_segments ES.init_pc ES.phdrs cfg0 SanitizerBudgets.lim_source.
Proof.
ltac2:(KReplay.run1 (kr_t_UbjEncPmAsanBase ()) ["AsanBases"] "h01pp;1p;2p;3p;?g00U>j1?Tg0013j22Tg01?Sj17Tg0000j11Tg00=8j1>Tg00N8j1:Tg00:Nj18Tg01@Ej16Tg002Oj35Tg000Uj13Tg001Mj10Tg0022j24Tg00ACj29Tg01AKj3=Tg01Ael?;Tg00hVR0g00HGR1f4f3g003lR2g016Mg00mag01CGf2g01:Kg01DUg01Egg01G5f1f0M?;p=<g00KgR3%?0'2%70,23g003G#1R0#1R4#1#>#:#8R5g00IRU%61R1=531%30%04#0#0#3'4/9212313=g01HFX05D<o"). Qed.
Lemma weird_S31 : @plain_g_stmt ES.loaded_segments ES.init_pc ES.phdrs cfg0 SanitizerBudgets.lim_source G_A.
Proof.
ltac2:(KReplay.run1 (kr_t_UbjEncPmAsanBase ()) ["AsanBases"] "h01pp;1p;2p;3p;?g00U>j1?Tg0013j22Tg01?Sj17Tg0000j11Tg00=8j1>Tg00N8j1:Tg00:Nj18Tg01@Ej16Tg002Oj35Tg000Uj13Tg001Mj10Tg0022j24Tg00ACj29Tg01AKj3=Tg01Hbl?;Tg00hVR0g00HGR1f4f3g003lR2g016Mg00mag01CGf2g01:Kg01DUg01Egg01G5f1f0M?;p=<g00KgR3%?0'2%70,23g003G#1R0#1R4#1#>#:#8R5g00IRU%61R1=531%30%04#0#0#3'4/9212313=g01HFX05D<o"). Qed.

(* [comment removed for export] *)
Let ROWS_A : forall (ar : asan_run) (HIk : list (list Z) -> asan_iface),
  @PECASMA.fam_ok ScfgP_cfg0 EarIfaceInst.art_L EarIfaceInst.art_C PEALF.art_IL EarFam.art_LR ar HIk ->
  @PECASMA.rows_open ScfgP_cfg0 EarIfaceInst.art_L ar HIk UbjEncPmAsanAsmA.P_TA :=
  fun ar HIk _ => @PECASMA.rows_closed ScfgP_cfg0 EarIfaceInst.art_L ar HIk UbjEncPmAsanAsmA.P_TA.   (* [comment removed for export] *)
Let TGTA : tgt_g_stmt EA.loaded_segments EA.init_pc EA.phdrs cfg0 SanitizerBudgets.lim_target G_A := UbjEncPmAsanAsmA.ea0_tgt ROWS_A.
Let ROWS_B : forall (ar : asan_run) (HIk : list (list Z) -> asan_iface),
  @PECASMB.fam_ok ScfgP_cfg0 EbrIfaceInst.art_L EbrIfaceInst.art_C PEBLF.art_IL EbrFam.art_LR ar HIk ->
  @PECASMB.rows_open ScfgP_cfg0 EbrIfaceInst.art_L ar HIk UbjEncPmAsanAsmB.P_TA :=
  fun ar HIk _ => @PECASMB.rows_closed ScfgP_cfg0 EbrIfaceInst.art_L ar HIk UbjEncPmAsanAsmB.P_TA.   (* [comment removed for export] *)
Let TGTB : tgt_g_stmt EB.loaded_segments EB.init_pc EB.phdrs cfg0 SanitizerBudgets.lim_target G_A := UbjEncPmAsanAsmB.eb0_tgt ROWS_B.

(* [comment removed for export] *)
Theorem ue_asan_base :
  strong_universal_error_free_T_scfg_budgets_abort cfg0 SanitizerBudgets.lim_source SanitizerBudgets.lim_target
    (mkImage ES.loaded_segments ES.init_pc ES.phdrs) (mkImage EA.loaded_segments EA.init_pc EA.phdrs).
Proof.
ltac2:(KReplay.run1 (kr_t_UbjEncPmAsanBase ()) ["AsanBases"] "p;?g01JAl?0Tg01KUg01M1g01NEg01OWg01Q5g01RKg00hVg003lg005Bg01:Kg01S_g01Tng01V=g01WQf0M?0p=1p,4TGTA#1o"). Qed.
(* [comment removed for export] *)
Theorem ue_both_base :
  strong_universal_error_free_T_scfg_budgets_abort cfg0 SanitizerBudgets.lim_source SanitizerBudgets.lim_target
    (mkImage ES.loaded_segments ES.init_pc ES.phdrs) (mkImage EB.loaded_segments EB.init_pc EB.phdrs).
Proof.
ltac2:(KReplay.run1 (kr_t_UbjEncPmAsanBase ()) ["AsanBases"] "p;?g01JAl?0Tg01KUg01M1g01NEg01Xfg01ZDg01[Zg00hVg003lg005Bg01:Kg01S_g01\ng01V=g01WQf0M?0p=1p,4TGTB#1o"). Qed.
End AsanBases.
