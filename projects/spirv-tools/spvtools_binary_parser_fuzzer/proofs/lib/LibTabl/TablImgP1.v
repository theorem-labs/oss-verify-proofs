(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From OSSVerify.spirv_tools.spvtools_binary_parser_fuzzer.images Require Import Plain.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import PropExec LibIface LibEff S1Layout.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs Require Import PrsGrammar.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibTabl Require Import TablData TablGrammar TablRep.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require KReplay.
Ltac2 kr_t_TablImgP1 () := "K47Corelib4Init5Logic2eq01C59OSSVerify5KrLib7LibTabl7TablRep7img_okbC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic2eq00I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01C69OSSVerify6KrSpec8ProblemscSrc_spirv_tools_spvtools_binary_parser_fuzzer_repro1M?loaded_segmentsC1@~~~~~~~~~~~~~~~~c59OSSVerify5KrLib7LibTabl9TablImgP12tiC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7LibTabl7TablRep8ti_ro_loC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7LibTabl7TablRep8ti_ro_hiC1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes4prod00K47Corelib7Numbers7BinNums1Z02K47Corelib7Numbers7BinNums8positive01K47Corelib7Numbers7BinNums8positive02I47Corelib4Init5Logic3and00C47Corelib4Init5Logic3notK47Corelib4Init9Datatypes4prod01C49OSSVerify5KrLib8LibIface6ly_imgC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List2hdC47Corelib4Init9Datatypes3sndC56Stdlib6ZArith6BinInt1Z2leK47Corelib4Init5Logic2or01K47Corelib4Init9Datatypes4list01I47Corelib4Init9Datatypes4list00K46Stdlib9micromega6VarMap1t02I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr01K46Stdlib9micromega7EnvRing5PExpr02K46Stdlib9micromega=RingMicromega7Formula01K47Corelib4Init9Datatypes6option02C46Stdlib9micromega5Tauto8BFormulaC46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundK47Corelib4Init5Logic3and01K47Corelib4Init5Logic2ex01C47Corelib4Init5Logic7f_equalC56Stdlib6ZArith6BinInt1Z2ltC47Corelib4Init5Logic6eq_indC46Stdlib5Lists4List2InC49OSSVerify5KrLib8LibIface5ly_rwC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8LibIface8ly_relroC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib6LibEff7ro_addrC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic2or00I47Corelib4Init5Logic2ex00K46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega5Tauto8GFormula05K46Stdlib9micromega5Tauto8GFormula08K46Stdlib9micromega5Tauto8GFormula03I47Corelib7Numbers7BinNums1Z00I47Corelib4Init5Logic5False00K46Stdlib9micromega=RingMicromega3Op203C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K47Corelib4Init9Datatypes4unit01K47Corelib7Numbers7BinNums8positive03K47Corelib7Numbers7BinNums1Z01c69OSSVerify5KrLib7LibTabl9TablImgP12Ly1LC1?~~~~~~~~~~~~~~~I46Stdlib9micromega:ZMicromega;ZArithProof00K46Stdlib9micromega=RingMicromega3Op205C59OSSVerify5KrLib7LibTabl7TablRep7ti_specC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3mulC56Stdlib6ZArith6BinInt1Z3addK46Stdlib9micromega7EnvRing5PExpr05K46Stdlib9micromega7EnvRing5PExpr03C49OSSVerify5KrLib8LibIface9in_rangesC1?~~~~~~~~~~~~~~~".
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Abbreviation SEGS := Plain.M.loaded_segments.
Module Ly := S1Layout.

Definition ti : tabl_img := {|
  ti_spans   := 0x14c1c;
  ti_strings := 0x15e18;
  ti_insn    := 0x23edc;
  ti_opnd    := 0x30c2c;
  ti_ext     := 0x40910;
  ti_spec    := 0xe6f68;
  ti_tstr    := [
    (0x11319, 4); (0x11bfc, 2); (0x12b48, 7); (0x10c0a, 9); (0x118d2, 19); (0x10663, 8);
    (0x137b6, 14); (0x12b74, 28); (0x10e49, 23); (0x12e21, 34); (0x137b6, 14); (0x12f64, 14);
    (0x126f8, 15); (0x140f0, 15); (0x12708, 16); (0x137c5, 12); (0x10e61, 14); (0x110a4, 13);
    (0x14100, 14); (0x10e70, 23); (0x13b09, 19); (0x115ac, 12); (0x1276a, 19); (0x109de, 23);
    (0x12719, 28); (0x11f88, 12); (0x13ebe, 16); (0x131cd, 28); (0x109d3, 10); (0x110b2, 8);
    (0x11a93, 15); (0x115b9, 19); (0x102b8, 21); (0x112f4, 10); (0x14172, 11); (0x12f73, 5);
    (0x121cc, 29); (0x1447e, 17); (0x10775, 12); (0x12404, 16); (0x12736, 13); (0x12e44, 12);
    (0x11bfc, 2); (0x12f73, 5); (0x12736, 13); (0x137b6, 14); (0x137b6, 14); (0x12b50, 35);
    (0x12f64, 14); (0x13ebe, 16); (0x12f79, 25); (0x14172, 11); (0x1109c, 7); (0x1109c, 7);
    (0x1109c, 7); (0x1109c, 7); (0x1175f, 16); (0x14490, 24); (0x11aa3, 20); (0x137e2, 20);
    (0x12f93, 15); (0x10c14, 37); (0x13587, 45); (0x131ea, 41); (0x11bff, 41); (0x1414d, 36);
    (0x11770, 42); (0x10799, 14); (0x110d6, 17); (0x1055f, 17); (0x11ab8, 13); (0x121ea, 9);
    (0x10782, 22); (0x12744, 37); (0x12b91, 37); (0x12bb7, 20); (0x12bb7, 20); (0x1410f, 27);
    (0x1410f, 27); (0x112ff, 25); (0x129c3, 22); (0x1424c, 29); (0x12bcc, 21); (0x13574, 18);
    (0x102ce, 19); (0x1412b, 33); (0x129f4, 25); (0x129f4, 25); (0x118e6, 17); (0x129da, 25);
    (0x110bb, 26); (0x12415, 35); (0x12415, 35); (0x13ecf, 32); (0x135b5, 14); (0x12a0e, 21);
    (0x13ef0, 61); (0x13214, 67); (0x13984, 53); (0x10e88, 54); (0x10ebf, 49); (0x107a8, 48);
    (0x10c3a, 53); (0x137d2, 15); (0x137d2, 15); (0x112f4, 10); (0x1109c, 7); (0x13b1d, 12) ];
  ti_tstr_dflt := (0x1109c, 7);
  ti_ro_lo   := 0x10000;
  ti_ro_hi   := 0x65000
|}.

Definition tc : tabl_consts := {|
  tc_fixword := 0x6aaf4;  tc_is_host_endian := 0x6abbc;  tc_binary_endianness := 0x6ab2c;
  tc_opcode_split := 0x6b0dc;
  tc_lookup_opcode := 0x6b2d4;  tc_lookup_operand := 0x6b340;  tc_lookup_ext := 0x6b8a8;
  tc_spec_lookup := 0x6bd60;
  tc_idesc_operands := 0x6b284;  tc_idesc_name := 0x6b2a0;  tc_odesc_operands := 0x6b268;
  tc_edesc_operands := 0x6b2b8;
  tc_operand_type_str := 0x6b96c;  tc_generates_type := 0x6b134;  tc_is_ext_inst := 0x6b248;
  tc_is_optional := 0x6bb6c;  tc_is_nonsemantic := 0x6c04c;  tc_fpenc := 0x6bce4;
  tc_import_type_get := 0x6bda4;  tc_push_types := 0x6bad0;  tc_take_first := 0x6bc98;
  tc_strlen := 0xe18a8;
  tc_lookup_stack := 64;  tc_import_stack := 64;  tc_pattern_stack := 96
|}.

Definition A_STRCMP : Z := 0xe15d8.
Definition A_STRNCMP : Z := 0xe1938.
Definition A_EXPAND : Z := 0x6bba4.
Definition A_OPCODE_STRING : Z := 0x6b0f4.

Lemma imgok : img_okb SEGS ti = true.
Proof.
ltac2:(KReplay.run1 (kr_t_TablImgP1 ()) [] "p;2p;3g0000j22Tg000Jj21Tg001Fj30Tg001`R0g002@R1'2g002`g004U'1=001do"). Qed.

Lemma rodata : forall a, ti_ro_lo ti <= a < ti_ro_hi ti -> ro_addr Ly.L a.
Proof.
ltac2:(KReplay.run1 (kr_t_TablImgP1 ()) [] "p'0h02hih11Hh22loh32Hrh44__x1h54__p1h64__p2h74__p3h87__arithh94__ffh:8__varmaph;5__with<1Eh=3Hinh>1eh?2Hah@1ai001pi011xi021zp;1p;2p;4p;3p;6p;7p;8g005Nj1kTg006Kj1jTg007HR0j2TTg007hj1>Tg008Fj16Tg008kj11Tg009PR1j20Tg009kj1ETg00:Dj4OTg00:dj1gTg00;Xj3bTg00;oj3_Tg001Fj38Tg00<Lj2CTg0000j2MTg00<hj3[Tg00=Bj1ZTg00=bj1YTg00>Bj2XTg00>`j1WTg00?>j1VTg00?ij2=Tg00@Lj2STg00@oj4FTg00AZj1RTg00B<j2QTg00B^j2UTg00CJj3iTg00Cij4hTg00D[j4LTg00E6j4PTg00EPj6BTg00Emj29Tg00FIj7DTg00Fej3KTg00G<j1fTg00Goj1aTg00Hej2`Tg00IXR2j2NTg00J2R3j2cTg00JLj7dTg00K0j7eTg00KTj8^Tg00L8j6]Tf3R4f2R5'Cf1R6f0R7'9'0p=5%17#1#1#1#1#1#1#1p=:%17#1p=H%17#1#1#1p=Ag00L\R8P8P6P7COp=3A8567g00M:R9'Np=41c87p=21N79p=\1967,05p=IP8P6g00MWP7CFp=GP6g00N>R:g00N]R;P;g00O=R<P7g00O]Fdp=?P5P:P;P;P<P6P7Fep=<P4P:P;P;P<P5P6P7G^p=@A8867p=71C56/07p=;P6P:P;P;P<P7E]p=Jg004UR:#kP7P7%j:C51T88R:g00P=R=#:#:#>R>%H=#6#1#H#6#1#A#:#>R?'3R@1367RA34P6P4P4P7C5RB'0X08#2X28RC#2%6=RD#6#1RE#6#6#6#1#A#:#>RF/3?RG=4:ARH/0BX08#2X28#2RI#ERJ%1E#6#6#1#A#:#>RE/3FRK=4:ARL/0BX08#2X28#2RM#ERN'0P8PCP>P813>794:@P>P5P5P7C5'0X08P8P8g00PbRCPCCOg00Q@RO#gRP5b:9_88RQA8:@@RR#\1C>6RS?I6?RT1M:@9[R9g00R;RR#ZRU%YRRR1X86RV%W8RW%V8RX1=8>1S8=R='G,?XRYP8P=g00RgRZ%HD#6#1#6#A#:#>RD,=8CF,?XR[5<X%R;R;P8P=PZ1=8?CF,?X9<XYC@1QX<R<P7P5g001`RYg002@RZ'M1U75=8YZdAi8C6ChRCb9b:b;X48P>P7P7PDC5PT[^48P7P5P6O2b8CL13>Q94:@AIS6Q'0eCPCPPJPNP3P8P6f4RSPSP7C5RQ,0HX08#2X28P9P7P6f6R@P@P7C5RT,0HX08#2P3P81357RH94:GP5f7R5P5P7C5RZ'0X08P9P713S7RY94:GPSf9R\P\P7C5R]'0P1f5R^/36R_94:GP^f:R`P`P6C5RaP9P71354Rb94:Gf8Rcf=RdPdPSC5ReP213\^R\98:GP9P9P613`@R@98:GP:P8P0P8P8P8P7P7n2001100000120102102X>:RfPGf;Rg/35RhP7EB17?5P:P8P0P8P8P8P7P6n2001100000120102102X>:R0PGf<RG/3cRcP6EB17FGRi17FdP8PFP7fDRjPjPgC5Rj17?GP9[]3X28fCRk19k`R`5;F17?gP8P?fFRl19l7Rm5;FP9]3X08PFfERnPnP?C5p-0RoPUPRPVPWPX1=8F/G=,?X1JX4Rp5<XP;PX1JXS=<X[P;1JX^C@R[C@P<PCb9b:b;X48X5oX6oW7A;F76AI46DP^[RD[^48^5o^6o^7oP7P9fGR4,C>R>194?P4P6PlO6b8W3PGP7P6FDW1W3f>R?P7P^FDW1P7O1b1P7O1b1W<P7O1P9P9P7n010000000X19P7O1RSn200100000021100010000W3W=P6P7O2n2001000000121000000W1X08P6P7O2n2001000000121101000W1X28P6P7O2n2001000000121101000X1IPJeP3P810LQX08#2X28P9P710LTX08#2P3P8A4:KH/0ZX08P9P7A4:KY/0]P1A4:K_PaP9P7A4:KbP2A8:K\P9P9P6A8:K@P:P8PfPKPhP7EB17F5P:P8P0PKPcP6EB17EG17EdP8PEP9\i^3jX28A;Ek`17FgP8PFA;ElmP9]3X08PEPnPnPFC5PUPRPVPWPX1=8E/G=,?X=<XpP;P[C@P<PCb9b:b;X48X5oX6oX7oA;E76PD[^48^5o^6o^7oP7P9P>194FP4P6PlO6b8W3PGP7P6FDW1W3P?P7P^FDW1P7O1b1P7O1b1W<P7O1PSn200100000021100010000X3eW=P6P7O2n2001000000121000000W1X08P6P7O2n2001000000121101000W1X28P6P7O2n2001000000121101000X1MPNeCLCLAK:AP/0BX08#2X28#2%fO9K:A/0BX08#2X28#2#E%aO9K:A/0BX08#2X28#2#E'0'0e1`O6eW?X@8o"). Qed.

Lemma relro : forall a, ti_spec ti <= a < ti_spec ti + 16 * 65 ->
  in_ranges (ly_img Ly.L) a /\ ~ in_ranges (ly_rw Ly.L) a.
Proof.
ltac2:(KReplay.run1 (kr_t_TablImgP1 ()) [] "p'0h02hih11Hh22loh32Hrh44__x1h57__arithh64__ffh74__p1h84__p2h94__p3h:8__varmaph;5__with<1eh=1Eh>2Hah?3Hinh@1ai001pi011xi021zp;1p;2p;3p;4p;6p;7p;8g00SNj1kTg007hj1:Tg008kj16Tg008Fj18Tg00TJj2dTg00Tgj2HTg007HR0j2WTg001Fj30Tg009PR1j22Tg009kj1ETg0000j2LTg00<hj3^Tg00=Bj1\Tg00=bj1[Tg00>Bj2ZTg00>`j1YTg00?>j1XTg00@Lj2VTg00UDj3UTg00Ugj3TTg00@oj4@Tg00AZj1QTg00B<j2PTg00B^j2RTg00CJj3OTg00Cij4STg00D[j4GTg00E6j4NTg00EPj6MTg00<Lj2FTg00Emj2CTg00FIj7KTg00:dj1hTg00Fej3JTg00G<j1cTg00VJj2ITg00:Dj4`Tg00IXR2j2aTg00J2R3j2bTg00?ij2_Tg00JLj7eTg00K0j7fTg00KTj8]Tg00L8j6gTf0R4#6#6#6#6p=5f3R5f2R6'Ff1R7/C4'2p=1%64#6p==%84#6p=7g00L\R8P8P7P4C`p=3g00M:R9,a4p=91b84p=4%84#8p=D1_84p=;P8P7g00MWP4C@p=AP7g00N>R:g00N]R;P;g00O=R<P4g00O]Fep=<P6P:P;P;P<P7P4Ffp=>P5P:P;P;P<P6P7P4G]p=?P7P:P;P;P<P4Egp=B1F67/24p=j1C74,26p=ig004U#kR:P4P4g00P=R=#5R>#:R?%6>R>#8#:R@'dRA,H:C11W88R:%6>#=#5#5#:R>%==#7#=#7#5#5#5#:RB'3RC1374RD30#9P7P5P5P4C1RE'2X08#4X28RF#4%8=#7#D#7#5#5#5#:RG/3BRH=0:D#9RI/2EX08#4X28#4RJ#ERKP8PFP>P813>490:C#9P>P6P6P4C1'2X08PBA0:CCRF#9P>P7P7PBC1RL1L:C9^F9g00R;RF#\RC%[FRF1Z87RM%Y8RN%X8RO%D=#=#8#7#8#D#7#8#7#7#=#:RP#;RQ1V8=R='A,<OP8P=g00RgRR%;?%;@5U89T8QC@,<ORQ5>O%Q;R;%;>/A=,<OP8P=PR%;BC@,<O5>OC?1PO<R<P4P6g001`RRg002@R>'L1R46=0R>dg00Pb=O87CSR>b6b:b;X48PPP4P41HPARAC1PL[^48P4P6P7O2b5PLeCGCNCNP3P8P7f4RLPLP4C1,2IX08#4X28P9P4P7f6RRPRP4C1,2IX08#4P3P8136490:H#9P6f7R6P6P4C1'2X08P9P413L490:H#9PLf9R3P3P4C1'2P1f5R1/3790:H#9P1f:RIPIP7C1P9P4136590:H#9f8R@f=R?P?PLC1P2133190:HP9P9P713IR90:HP:P8P0P8P8P8P4P4n2001100000120102102X<:PHf;RR/36P4EMA08B6P:P8P0P8P8P8P4P7n2001100000120102102X<:PHf<RH/3@P7EMA08GHA08G?P8PGP4fDR?P?PRC1A08BHP9[]3X28PGfCR?P?PIC1A08BRP8PBPGfFRRPRP4C1P9]3X08PGfERIPIPBC1p-0RIPCPFPMPNPO%;G/A=,<O1BO55>OP;PO1BOL=>OQP;1BO1C?C?P<P>b6b:b;X48X7IX8IW9AjG47Ai57AP1[[^48^7I^8I^9IP4P9fGRI,FP1CIBPIP7PRO6b5W3PHP4P7FKW1W3f>P4P1FKW1P4O1b1P4O1b1W=P4O1P9P9P4n010000000X19P4O1n200100000021100010000W3W?P7P4O2n2001000000121000000W1X08P7P4O2n2001000000121101000W1X28P7P4O2n2001000000121101000X1JPKeCGg00Q@RK#hRJ9J:D/2EX08#4X28#4%cKRK9J:D/2EX08#4X28#4#E'2e1IJ71IK7#E'2eW>X@8o"). Qed.

Definition IFX : img_facts SEGS ti := img_facts_of SEGS ti imgok.
