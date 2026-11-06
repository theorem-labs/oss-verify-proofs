(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From OSSVerify.spirv_tools.spvtools_binary_parser_fuzzer.images Require Import Ubsan.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import PropExec LibIface LibEff U1Layout.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs Require Import PrsGrammar.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibTabl Require Import TablData TablGrammar TablRep.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require KReplay.
Ltac2 kr_t_TablImgU1 () := "K47Corelib4Init5Logic2eq01C59OSSVerify5KrLib7LibTabl7TablRep7img_okbC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic2eq00I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01C59OSSVerify5KrImgWTgt_spvtools_binary_parser_fuzzer_ubsan1M?loaded_segmentsC1@~~~~~~~~~~~~~~~~c59OSSVerify5KrLib7LibTabl9TablImgU12tiC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7LibTabl7TablRep8ti_ro_loC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7LibTabl7TablRep8ti_ro_hiC1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes4prod00K47Corelib7Numbers7BinNums1Z02K47Corelib7Numbers7BinNums8positive01I47Corelib4Init5Logic3and00K47Corelib7Numbers7BinNums8positive02C47Corelib4Init5Logic3notK47Corelib4Init9Datatypes4prod01C49OSSVerify5KrLib8LibIface6ly_imgC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List2hdC47Corelib4Init9Datatypes3sndC56Stdlib6ZArith6BinInt1Z2leK47Corelib4Init5Logic2or01K47Corelib4Init9Datatypes4list01I47Corelib4Init9Datatypes4list00K46Stdlib9micromega6VarMap1t02I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr01K46Stdlib9micromega7EnvRing5PExpr02K46Stdlib9micromega=RingMicromega7Formula01K47Corelib4Init9Datatypes6option02C46Stdlib9micromega5Tauto8BFormulaC46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundK47Corelib4Init5Logic3and01K47Corelib4Init5Logic2ex01C47Corelib4Init5Logic7f_equalC56Stdlib6ZArith6BinInt1Z2ltC47Corelib4Init5Logic6eq_indC46Stdlib5Lists4List2InC49OSSVerify5KrLib8LibIface5ly_rwC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8LibIface8ly_relroC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib6LibEff7ro_addrC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic2or00I47Corelib4Init5Logic2ex00K46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega5Tauto8GFormula05K46Stdlib9micromega5Tauto8GFormula08K46Stdlib9micromega5Tauto8GFormula03I47Corelib7Numbers7BinNums1Z00I47Corelib4Init5Logic5False00K46Stdlib9micromega=RingMicromega3Op203C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K47Corelib4Init9Datatypes4unit01K47Corelib7Numbers7BinNums8positive03K47Corelib7Numbers7BinNums1Z01c69OSSVerify5KrLib7LibTabl9TablImgU12Ly1LC1?~~~~~~~~~~~~~~~I46Stdlib9micromega:ZMicromega;ZArithProof00K46Stdlib9micromega=RingMicromega3Op205C59OSSVerify5KrLib7LibTabl7TablRep7ti_specC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3mulC56Stdlib6ZArith6BinInt1Z3addK46Stdlib9micromega7EnvRing5PExpr05K46Stdlib9micromega7EnvRing5PExpr03C49OSSVerify5KrLib8LibIface9in_rangesC1?~~~~~~~~~~~~~~~".
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Abbreviation SEGS := Ubsan.M.loaded_segments.
Module Ly := U1Layout.

Definition ti : tabl_img := {|
  ti_spans   := 0x14c58;
  ti_strings := 0x15e54;
  ti_insn    := 0x23f18;
  ti_opnd    := 0x30c68;
  ti_ext     := 0x4094c;
  ti_spec    := 0xe8cc0;
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
  tc_fixword := 0x6bf10;  tc_is_host_endian := 0x6c010;  tc_binary_endianness := 0x6bf50;
  tc_opcode_split := 0x6c5b8;
  tc_lookup_opcode := 0x6c804;  tc_lookup_operand := 0x6c8f0;  tc_lookup_ext := 0x6cecc;
  tc_spec_lookup := 0x6d9dc;
  tc_idesc_operands := 0x6c790;  tc_idesc_name := 0x6c7b8;  tc_odesc_operands := 0x6c768;
  tc_edesc_operands := 0x6c7dc;
  tc_operand_type_str := 0x6d0fc;  tc_generates_type := 0x6c634;  tc_is_ext_inst := 0x6c748;
  tc_is_optional := 0x6d2b0;  tc_is_nonsemantic := 0x6dcd4;  tc_fpenc := 0x6d7bc;
  tc_import_type_get := 0x6da2c;  tc_push_types := 0x6d134;  tc_take_first := 0x6d744;
  tc_strlen := 0xe3600;
  tc_lookup_stack := 64;  tc_import_stack := 64;  tc_pattern_stack := 96
|}.

Definition A_STRCMP : Z := 0xe3330.
Definition A_STRNCMP : Z := 0xe3690.
Definition A_EXPAND : Z := 0x6d2f0.
Definition A_OPCODE_STRING : Z := 0x6c5e4.

Lemma imgok : img_okb SEGS ti = true.
Proof.
ltac2:(KReplay.run1 (kr_t_TablImgU1 ()) [] "p;2p;3g0000j22Tg000Jj21Tg001Fj30Tg001`R0g002@R1'2g002`g004?'1=001do"). Qed.

Lemma rodata : forall a, ti_ro_lo ti <= a < ti_ro_hi ti -> ro_addr Ly.L a.
Proof.
ltac2:(KReplay.run1 (kr_t_TablImgU1 ()) [] "p'0h02hih11Hh22loh32Hrh44__x1h54__p1h64__p2h74__p3h87__arithh94__ffh:8__varmaph;5__with<1Eh=3Hinh>1eh?2Hah@1ai001pi011xi021zp;1p;2p;4p;3p;6p;7p;8g0058j1kTg0065j1jTg0072R0j2TTg007Rj1?Tg0080j16Tg008UR1j20Tg0090j11Tg009Uj1FTg009nj4OTg00:Nj1gTg00;Bj3bTg00;Yj3_Tg001Fj38Tg00<6j2DTg0000j2MTg00<Rj3[Tg00<lj1ZTg00=Lj1YTg00=lj2XTg00>Jj1WTg00>hj1VTg00?Sj2>Tg00@6j2STg00@Yj4GTg00ADj1RTg00Afj2QTg00BHj2UTg00C4j3iTg00CSj4hTg00DEj4LTg00D`j4PTg00E:j6BTg00EWj2:Tg00F3j7ETg00FOj3KTg00Ffj1fTg00GYj1aTg00HOj2`Tg00IBR2j2NTg00I\R3j2cTg00J6j7dTg00JZj7eTg00K>j8^Tg00Kbj6]Tf3R4f2R5'Df1R6f0R7':'0p=5%17#1#1#1#1#1#1#1p=;%17#1p==%17#1#1#1p=Cg00LFR8P8P6P7COp=3A8567g00LdR9'Np=41c87p=21N79p=\1:67,05p=IP8P6g00MAP7CGp=HP6g00MhR:g00NGR;P;g00NgR<P7g00OGFdp=@P5P:P;P;P<P6P7Fep=<P4P:P;P;P<P5P6P7G^p=AA8867p=71D56/07p=9P6P:P;P;P<P7E]p=Jg004?R:#kP7P7%j:C51T88R:g00OgR=#;#;#?R>%==#6#=#6#=#C#;#?R?'3R@1367RA34P6P4P4P7C5RB'0X08#2X28RC#2%6=RD#6#1#6RE#6#6#6#C#;#?RF/3?RG=4:ARH/0BX08#2X28#2RI#FRJ%1E#=#C#;#?RE/3FRK=4:ARL/0BX08#2X28#2RM#FRN'0P8PCP>P813>794:@P>P5P5P7C5'0X08P8P8g00PLRCPCCOg00PjRO#gRP5b:9_88RQA8:@@RR#\1D>6RS?I6?RT1M:@9[R9g00QeRR#ZRU%YRRR1X86RV%W8RW%V8RX1>8>1S8=R='H,@XRYP8P=g00RQRZ%=D#6#1#6#C#;#?RD,>8CG,@XR[5<X%R;R;P8P=PZ1>8?CG,@X9<XYCA1QX<R<P7P5g001`RYg002@RZ'M1U75=8YZdAi8C6ChRCb9b:b;X48P>P7P7PDC5PT[^48P7P5P6O2b8CL13>Q94:@AIS6Q'0eCPCPPJPNP3P8P6f4RSPSP7C5RQ,0HX08#2X28P9P7P6f6R@P@P7C5RT,0HX08#2P3P81357RH94:GP5f7R5P5P7C5RZ'0X08P9P713S7RY94:GPSf9R\P\P7C5R]'0P1f5R^/36R_94:GP^f:R`P`P6C5RaP9P71354Rb94:Gf8Rcf=RdPdPSC5ReP213\^R\98:GP9P9P613`@R@98:GP:P8P0P8P8P8P7P7n2001100000120102102X>:RfPGf;Rg/35RhP7EB17?5P:P8P0P8P8P8P7P6n2001100000120102102X>:R0PGf<RG/3cRcP6EB17FGRi17FdP8PFP7fDRjPjPgC5Rj17?GP9[]3X28fCRk1:k`R`59F17?gP8P?fFRl1:l7Rm59FP9]3X08PFfERnPnP?C5p-0RoPUPRPVPWPX1>8F/H=,@X1JX4Rp5<XP;PX1JXS=<X[P;1JX^CAR[CAP<PCb9b:b;X48X5oX6oW7A9F76AI46DP^[RD[^48^5o^6o^7oP7P9fGR4,D>R>1:4?P4P6PlO6b8W3PGP7P6FEW1W3f>R?P7P^FEW1P7O1b1P7O1b1W<P7O1P9P9P7n010000000X19P7O1RSn200100000021100010000W3W=P6P7O2n2001000000121000000W1X08P6P7O2n2001000000121101000W1X28P6P7O2n2001000000121101000X1IPJeP3P810LQX08#2X28P9P710LTX08#2P3P8A4:KH/0ZX08P9P7A4:KY/0]P1A4:K_PaP9P7A4:KbP2A8:K\P9P9P6A8:K@P:P8PfPKPhP7EB17F5P:P8P0PKPcP6EB17EG17EdP8PEP9\i^3jX28A9Ek`17FgP8PFA9ElmP9]3X08PEPnPnPFC5PUPRPVPWPX1>8E/H=,@X=<XpP;P[CAP<PCb9b:b;X48X5oX6oX7oA9E76PD[^48^5o^6o^7oP7P9P>1:4FP4P6PlO6b8W3PGP7P6FEW1W3P?P7P^FEW1P7O1b1P7O1b1W<P7O1PSn200100000021100010000X3eW=P6P7O2n2001000000121000000W1X08P6P7O2n2001000000121101000W1X28P6P7O2n2001000000121101000X1MPNeCLCLAK:AP/0BX08#2X28#2%fO9K:A/0BX08#2X28#2#F%aO9K:A/0BX08#2X28#2#F'0'0e1`O6eW?X@8o"). Qed.

Lemma relro : forall a, ti_spec ti <= a < ti_spec ti + 16 * 65 ->
  in_ranges (ly_img Ly.L) a /\ ~ in_ranges (ly_rw Ly.L) a.
Proof.
ltac2:(KReplay.run1 (kr_t_TablImgU1 ()) [] "p'0h02hih11Hh22loh32Hrh44__x1h57__arithh64__ffh74__p1h84__p2h94__p3h:8__varmaph;5__with<1eh=1Eh>2Hah?3Hinh@1ai001pi011xi021zp;1p;2p;3p;4p;6p;7p;8g00S8j1jTg007Rj1;Tg0090j17Tg0080j13Tg00T4j2aTg00TQj2HTg0072R0j2VTg001Fj30Tg008UR1j22Tg009Uj1ATg0000j2LTg00<Rj3]Tg00<lj1\Tg00=Lj1ZTg00=lj2YTg00>Jj1XTg00>hj1WTg00@6j2UTg00Tnj3TTg00UQj3STg00@Yj4CTg00ADj1PTg00Afj2OTg00BHj2QTg00C4j3RTg00CSj4NTg00DEj4FTg00D`j4GTg00E:j6MTg00<6j2DTg00EWj2@Tg00F3j7KTg00:Nj1gTg00FOj3ITg00Ffj1`Tg00V4j2JTg009nj4_Tg00IBR2j2^Tg00I\R3j2bTg00?Sj2cTg00J6j7dTg00JZj7eTg00K>j8fTg00Kbj6[Tf0R4#7#7#7#7p=5f3R5f2R6'Df1R7/@4'2p=1%74#7p=9g00LFR8P8P7P4C_p=4g00LdR9,^4p=81b84p=6%34#7p=B1c84p=:P8P7g00MAP4CCp=?P7g00MhR:g00NGR;P;g00NgR<P4g00OGFdp=<P6P:P;P;P<P7P4Fep==P5P:P;P;P<P6P7P4Gfp=>P7P:P;P;P<P4E[p=E1D67/24p=i1@74,26p=hg004?#jR:P4P4g00OgR=#5R>#;R?%7>R>#3#;R@'aRA,H:C11V88R:%7>#9#5#5#;R>%9=#3#9#3#9#5#5#5#;RB'4RC1474RD30#8P7P5P5P4C1RE'2X08#6X28RF#6%3=#B#3#3#3#3#5#5#5#;RG/4BRH=0:D#8RI/2EX08#6X28#6RJ#ARKP8PFP>P814>490:C#8P>P6P6P4C1'2X08PBA0:CCRF#8P>P7P7PBC1RL1L:C9]F9g00QeRF#\RC%ZFRF1Y87RM%X8RN%W8RO%3=#B#B#9#3#3#9#3#3#9#5#;RP#:RQ1U8=R='?,<OP8P=g00RQRR%:?%:@5T89S8QCC,<ORQ5=O%P;R;%:>/?=,<OP8P=PR%:BCC,<O5=OC>1OO<R<P4P6g001`RRg002@R>'L1Q46=0R>dg00PL=R87CNR>b6b:b;X48PPP4P41HPARAC1PL[^48P4P6P7O2b5PLeCFCGCGP3P8P7f4RLPLP4C1,2IX08#6X28P9P4P7f6RRPRP4C1,2IX08#6P3P8146490:H#8P6f7R6P6P4C1'2X08P9P414L490:H#8PLf9R3P3P4C1'2P1f5R1/4790:H#8P1f:RIPIP7C1P9P4146590:H#8f8R@f=R?P?PLC1P2143190:HP9P9P714IR90:HP:P8P0P8P8P8P4P4n2001100000120102102X<:PHf;RR/46P4EMA08B6P:P8P0P8P8P8P4P7n2001100000120102102X<:PHf<RH/4@P7EMA08GHA08G?P8PGP4fDR?P?PRC1A08BHP9[]3X28PGfCR?P?PIC1A08BRP8PBPGfFRRPRP4C1P9]3X08PGfERIPIPBC1p-0RIPCPFPMPNPO%:G/?=,<O1EO55=OP;PO1EOL==OQP;1EO1C>C>P<P>b6b:b;X48X7IX8IW9AiG47Ah57AP1[[^48^7I^8I^9IP4P9fGRI,DP1@IBPIP7PRO6b5W3PHP4P7FKW1W3f>P4P1FKW1P4O1b1P4O1b1W=P4O1P9P9P4n010000000X19P4O1n200100000021100010000W3W?P7P4O2n2001000000121000000W1X08P7P4O2n2001000000121101000W1X28P7P4O2n2001000000121101000X1JPKeCFg00PjRK#gRJ9I:D/2EX08#6X28#6%`KRK9I:D/2EX08#6X28#6#A'2e1JJ71JK7#A'2eW>X@8o"). Qed.

Definition IFX : img_facts SEGS ti := img_facts_of SEGS ti imgok.
