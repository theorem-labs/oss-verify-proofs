(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OssFuzzTheorems.zstd.huf_decompress.images Require Import AsanUbsan.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.AS Require Import PropExec StoreOk AgentLib AsanAcct AsanAcctImages AxSymExec3 AsanPlan AsanPlanSound AsanHexScan.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib Require KReplay.
Ltac2 kr_t_AsanPlanImages () := "C6ARocqVerifyHarness?AgentSubmission2AS:AxSymExec33AX2=mk_itab_soundc5ARocqVerifyHarness?AgentSubmission2AS>BothPlanImages5ASEGSC6ARocqVerifyHarness?AgentSubmission2AS8AsanPlan2AP<BOTH_TEXT_LOC6ARocqVerifyHarness?AgentSubmission2AS8AsanPlan2AP;BOTH_TEXT_NC5ARocqVerifyHarness?AgentSubmission2AS>AsanAcctImages>Both_wx_nowrapI47Corelib4Init9Datatypes4list00c5ARocqVerifyHarness?AgentSubmission2AS>BothPlanImages>segs_in_hull_bC56Stdlib6ZArith6BinInt1Z2ltC56Stdlib6ZArith6BinInt1Z2leI47Corelib4Init5Logic2or00I47Corelib4Init9Datatypes6option00K47Corelib7Numbers7BinNums1Z02C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics<find_segmentK47Corelib4Init9Datatypes6option02I47Corelib4Init5Logic2eq00K47Corelib4Init9Datatypes4list01K47Corelib4Init5Logic2eq01K47Corelib4Init9Datatypes4list02C47Corelib4Init9Datatypes4andbI47Corelib4Init5Logic3and00C46Stdlib4Bool4Bool=andb_true_iffC56Stdlib6ZArith6BinInt1Z3lebC4ELinuxProcessSemantics?LinuxProcessSem<MemImageType8seg_sizeC46Stdlib5Lists4List7forallbC56Stdlib6ZArith6BinInt1Z6leb_leC46Stdlib4Bool4Bool>andb_false_iffC56Stdlib6ZArith6BinInt1Z6leb_gtC4ELinuxProcessSemantics?LinuxProcessSem<MemImageType8seg_baseC56Stdlib6ZArith6BinInt1Z4of_NC56Stdlib6ZArith4Znat3N2Z9is_nonnegK47Corelib4Init9Datatypes3nat02K46Stdlib9micromega=RingMicromega5Psatz02K46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega:ZMicromega;ZArithProof02K46Stdlib9micromega6VarMap1t02K46Stdlib9micromega6VarMap1t03I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr02K47Corelib7Numbers7BinNums8positive01K47Corelib7Numbers7BinNums8positive02C46Stdlib9micromega5Tauto8BFormulaC46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundK47Corelib4Init5Logic2or01C56Stdlib6ZArith6BinInt1Z3addK46Stdlib9micromega6VarMap1t01K46Stdlib9micromega7EnvRing5PExpr03K46Stdlib9micromega7EnvRing5PExpr01K47Corelib4Init5Logic2or02C47Corelib4Init5Logic6eq_symK47Corelib4Init9Datatypes6option01C47Corelib4Init5Logic6eq_indC47Corelib4Init9Datatypes8list_indK46Stdlib9micromega=RingMicromega7Formula01K46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega5Tauto8GFormula08I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01K47Corelib4Init9Datatypes4bool02I47Corelib7Numbers7BinNums1Z00K46Stdlib9micromega=RingMicromega3Op205C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K47Corelib4Init9Datatypes4unit01K46Stdlib9micromega=RingMicromega3Op203I4ELinuxProcessSemantics?LinuxProcessSem<MemImageType7Segment00K47Corelib7Numbers7BinNums8positive03K47Corelib7Numbers7BinNums1Z01I46Stdlib9micromega:ZMicromega;ZArithProof00K47Corelib4Init9Datatypes3nat01K46Stdlib9micromega:ZMicromega;ZArithProof01C6ARocqVerifyHarness?AgentSubmission2AS8AsanPlan2AP6img_loC6ARocqVerifyHarness?AgentSubmission2AS8AsanPlan2AP6img_hiC6ARocqVerifyHarness?AgentSubmission2AS8AsanPlan2AP4BOTHK47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00C45stdpp9bitvector;definitions;bv_unsignedC6ARocqVerifyHarness?AgentSubmission2AS=AsanPlanSound3APS7in_hullC56Stdlib6ZArith6BinInt1Z3ltbC56Stdlib6ZArith6BinInt1Z6ltb_gec5ARocqVerifyHarness?AgentSubmission2AS>BothPlanImagesJfind_segment1_none_outsidec5ARocqVerifyHarness?AgentSubmission2AS>BothPlanImagesAasan_segs_in_hullC6ARocqVerifyHarness?AgentSubmission2AS=AsanPlanSound3APS:res_len_okI47Corelib4Init9Datatypes3nat00I47Corelib4Init9Datatypes4prod00K47Corelib4Init9Datatypes4prod01C4ELinuxProcessSemantics?LinuxProcessSem3RunAsegments_reservedC45stdpp9bitvector;definitions7Z_to_bvC47Corelib4Init9Datatypes3fstC47Corelib4Init9Datatypes3sndI47Corelib5Lists7ListDef6Forall00C56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z3powC56Stdlib6ZArith6BinInt1Z:pow_nonnegK46Stdlib9micromega7EnvRing5PExpr07C5ARocqVerifyHarness?AgentSubmission2AS8AgentLib7u64_litK47Corelib4Init5Logic3and01K47Corelib5Lists7ListDef6Forall01K47Corelib5Lists7ListDef6Forall02C47Corelib4Init5Logic8eq_ind_rC45stdpp9bitvector;definitionsDZ_to_bv_obligation_1K45stdpp9bitvector;definitions2bv01K46Stdlib9micromega5Tauto8GFormula05I47Corelib4Init5Logic4True00C56Stdlib6ZArith6BinInt1Z6moduloC6ARocqVerifyHarness?AgentSubmission2AS=AsanPlanSound3APS7hull_okC6ARocqVerifyHarness?AgentSubmission2AS8AsanPlan2AP3KHIC6ARocqVerifyHarness?AgentSubmission2AS8AsanPlan2AP:shadow_offC6ARocqVerifyHarness?AgentSubmission2AS=AsanPlanSound3APS9shadow_okC6ARocqVerifyHarness?AgentSubmission2AS=AsanPlanSound3APS9sum_sizesC5ARocqVerifyHarness?AgentSubmission2AS;AsanHexScan8hexscanZC4ARocqVerifyHarness@ProcessOversightGTgt_huf_decompress_bothUTgt_huf_decompress_both_seg_bytes_002C4ARocqVerifyHarness@ProcessOversightGTgt_huf_decompress_bothUTgt_huf_decompress_both_seg_bytes_003C47Corelib7Strings:PrimString6lengthC67Corelib7Numbers6Cyclic5Int63<Uint63Axioms4to_ZC56Stdlib6ZArith6BinInt1Z3divC56Stdlib6ZArith6BinInt1Z4to_NI47Corelib7Numbers7BinNums1N00C4ARocqVerifyHarness@ProcessOversightGTgt_huf_decompress_bothSTgt_huf_decompress_both_segment_000C4ARocqVerifyHarness@ProcessOversightGTgt_huf_decompress_bothSTgt_huf_decompress_both_segment_001C4ARocqVerifyHarness@ProcessOversightGTgt_huf_decompress_bothSTgt_huf_decompress_both_segment_002C4ARocqVerifyHarness@ProcessOversightGTgt_huf_decompress_bothSTgt_huf_decompress_both_segment_003C6ARocqVerifyHarness?AgentSubmission2AS=AsanPlanSound3APS6in_ivsC56Stdlib6ZArith6BinInt1Z;lt_ge_casesC46Stdlib4Bool4Bool<orb_true_iffK46Stdlib9micromega5Tauto8GFormula03C56Stdlib6ZArith6BinInt1Z6ltb_ltC47Corelib4Init9Datatypes3orbC46Stdlib5Lists4List7existsbC6ARocqVerifyHarness?AgentSubmission2AS8AsanPlan2AP9ph_addr_zC4ELinuxProcessSemantics?LinuxProcessSem<MemImageType7ph_addrC6ARocqVerifyHarness?AgentSubmission2AS8AsanPlan2AP8ph_ent_zC4ELinuxProcessSemantics?LinuxProcessSem<MemImageType6ph_entC6ARocqVerifyHarness?AgentSubmission2AS8AsanPlan2AP8ph_num_zC4ELinuxProcessSemantics?LinuxProcessSem<MemImageType6ph_numC46Stdlib9micromega9SatDivModCZ_mod_nonneg_nonnegC56Stdlib6ZArith6BinInt1Z7div_modC47Corelib4Init5Logic3notC56Stdlib6ZArith6BinInt1Z3mulC56Stdlib6ZArith6BinInt1Z=mod_pos_boundC56Stdlib6ZArith6BinInt1Z=mod_neg_boundC56Stdlib5omega8PreOmega1Z;div_0_r_extC56Stdlib5omega8PreOmega1Z;mod_0_r_extK47Corelib7Numbers7BinNums1Z03K46Stdlib9micromega7EnvRing3Pol01K46Stdlib9micromega=RingMicromega5Psatz04K46Stdlib9micromega:ZMicromega;ZArithProof03K46Stdlib9micromega5Tauto8GFormula07K46Stdlib9micromega7EnvRing5PExpr05C4ELinuxProcessSemantics?LinuxProcessSem5State<reserved_topC56Stdlib6ZArith6BinInt1Z3subC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics5wviewc5ARocqVerifyHarness?AgentSubmission2AS>BothPlanImages>asan_rw_windowC6ARocqVerifyHarness?AgentSubmission2AS8AsanPlan2AP5rw_loC6ARocqVerifyHarness?AgentSubmission2AS8AsanPlan2AP6rw_lenK5ARocqVerifyHarness?AgentSubmission2AS8AsanInit9img_facts01K46Stdlib9micromega=RingMicromega3Op201c5ARocqVerifyHarness?AgentSubmission2AS>BothPlanImages3APHI47Corelib4Init5Logic5False00c5ARocqVerifyHarness?AgentSubmission2AS>BothPlanImages=asan_res_hullc5ARocqVerifyHarness?AgentSubmission2AS>BothPlanImages>asan_res_sizesc5ARocqVerifyHarness?AgentSubmission2AS>BothPlanImages>asan_shadow_ok".
(* [comment removed for export] *)
Unset Lia Cache.
Import ListNotations.
Import AX2. Import AP.
Open Scope Z_scope.

Definition ASEGS := AsanUbsan.M.loaded_segments.
Definition AITAB : itab := mk_itab ASEGS BOTH_TEXT_LO BOTH_TEXT_N.

Lemma asan_IT_ok : itab_sound ASEGS AITAB.
Proof.
ltac2:(KReplay.run1 (kr_t_AsanPlanImages ()) [] "p;3g0000j30Tg0014g0020g003030o"). Qed.

Lemma asan_wx : wx_segs_nowrap ASEGS.
Proof.
ltac2:(KReplay.run1 (kr_t_AsanPlanImages ()) [] "g003oo"). Qed.

(* [comment removed for export] *)
Definition segs_in_hull_b (segs : list Segment) (lo hi : Z) : bool :=
  forallb (fun seg => (lo <=? Z.of_N (seg_base seg)) && (Z.of_N (seg_base seg) + Z.of_N (seg_size seg) <=? hi))%bool segs.

Lemma find_segment1_none_outside : forall segs lo hi x,
  segs_in_hull_b segs lo hi = true -> (x < lo \/ hi <= x) -> find_segment segs x 1 = None.
Proof.
ltac2:(KReplay.run1 (kr_t_AsanPlanImages ()) [] "h01Hh11xh22Hxh34__x1h44__x2h54__x3h62b1h72b2h82Hbh92hih:2loh;3segh<2H1h=2H2h>2Hsh?7__arithh@4__ffhA8__varmaphB5__withC4__x4hD4cstrhE5cstr0hF1mhG1nhH4segshI1yhJ2HlhK2IHhL1bhM1lhN1sp;1p;3p;2p;4p;6p;5p;7p;8g0054j1TTg005Tj3HTg006Yj29Tg0075j26Tg007QR0j2CTg007kj1`Tg008Mj1]Tg008kj3ATg009oj1RTg00:Qj38Tg00:kj1MTg00;Kj2LTg00;ej3?Tg00<Ej24Tg00<cR1j2@Tg00=>j2iTg00=_j21Tg00><j17Tg00?:j3GTg00?Vj2\Tg00@6j2[Tg00@Xj2ZTg00A8j1QTg00B6j1>Tg00BTj1PTg00C7j1OTg00CVj2ETg00D?j3NTg00Dhj2YTg00ETj2FTg00F2j4ITg00FPj1XTg00Fnj1WTg00GYj2DTg00H<j1VTg00Haj1nTg00IFj2mTg00Ihj2lTg00JTj3kTg00K3j4hTg00Kej3gTg00L?j2<Tg00L\j1cTg00M:j3STg00M]j2bTg00N@j3aTg00NZj4dTg00O6j2eTg00OXj6_Tg00P4j5fTg00PVj4UTg00QAj7^Tg00Qej8jTg00RIR2f0R3g00RiR438p=0%Q3#>p=2%73#>p=;f2R5f1R6'</13p=5%>3,<6p=:g00SIR79823p=3g00SiR8P6g00TGP3CUp=KP6g00TnR9g00UMR:P:g00UmR;P3g00VMF^p==P8P6g00VmP3CUp=Jf3R<P9P:P:P;P5P6P3Gjp=Bg00WTR9#TR=P9AH<56#0196<1656R>'CR?%`9R@f5RAg00XSRB#]RC7A5%R9RD38[[^18^98^:8REXH=%M9?H56#01L@DX2?W8X18X98X:8f4RF9?9A?H56#0P11463RG#0%05RH%06RI'@[RJ%03,@I1456RI#0RK[%0</@H\K1i63P6n2001000000120000000X72X62RKPJ^72^62RJP3f8RH#2RL,1A%;H=5LF'4RLf6RM%23RN'1%73,:NRO/1A'4X;9f7RP5G9RQP5O3%0L%0Q'@P1f9RQ#2RL,1M%;Q=5LA'4#011PN11OM'4X;9=G9H#0f:RM=?9Q?AAC=8@DP3f;RA#2RL,1H%;A=5LP'4#011MN11OQ'4X;9=G9A#0PKPJP3f>RJ#2RK,1ARO%;J=5KMRKP5O3%0O%0K'@P1f<f?RK#2RO'1#0%;K=5OA#0f@=?9K?AAC=8@DP3fARK#2,1J#0fBRO#2%;O;5J#0P11163RJ#0P>[R>16631156RM#0RN[16<5RL\N1\63P6n2001000000120000000XF8XG8RNP>^F8^G8R>P3PKfDRH#2RRP5O316KRPNP>P3fFR>#2%7>':RNPOP<O316NOP2fGRN#2RR/1O%7N,:R95OC'4RRP7P1%3G%35%36RG'CRS[%33,CG%3I[RI14<5#3\S1[63P3n2001000000120000000X72X62PI^72^62P3fHRI#2RSfCRG'1RT%7I,:S95GCRSP0fER0,9G16HGfIRU#2RV/1H#3%7U,:V95HC#3'CPK19H>fJRV#2RW/10#3RX%7V,:W950C#3RWP1%3J1965RJ[1936%3M[RM11<5#3\J1Z63P3n2001000000120000000XI8X18RJPM^I8^18RMP3fKR1#QRY#>RZP>%PYRYg00Y8R[/6ZR\fL#7R]#PR^%>],6[R]g00YVR_g00ZBR`#ORa#O,E81E8a1E8`5N85N8g00Za'Y%M_3?R`%T_R_P81F85RaP61F8<CI%X8Rb%W8Rc1D8BRd%VB,D8Re'K,=c%R:R:Pc%nBRB,D8Rf,Je,=cP:1Kdf,=cCBCB1mc;R;P3P51L241l35#0dAk8[6ChR[b@bAbBX38X48X581935195<\L[^38^48^58P3P1fNR4#2RgPUPFPQO5b?bEbDO3b03gW2P3O1160HPJPMP31<>C%71,:ZPYP\P^P]P`P_P8PaP6P81F8FP<%c8CICIPbPc%VB,D8RB/Je,=cP:PcAS8dfRf/JB,=cP:1b8C9S8e,Kf,=cCBCBP;P[b@bAbBX38X48X58XC81<65/6F1<5<1<FC'9[\L^38^48^58^C8P3PVPU%;4PgPFPPO6b?bEbDO3b09aXWW2P3O1n200100000021100011000O3b0CdA827RP2P7P2P@P31e9UAAIHCn0100000020000=8@DXL2P>P0PHPGPAPKO514TSP3E_b0A?9N>?AOC=8@Deb=b0b<b0W=W<P6P3O2n2001000000121000000b>b0WJW>P6P3O2n2001000000121000000b8b0X2?W8X18X98X:8XKEXM=XN9P3DfWHo"). Qed.

Lemma asan_segs_in_hull : segs_in_hull_b ASEGS (img_lo BOTH) (img_hi BOTH) = true.
Proof.
ltac2:(KReplay.run1 (kr_t_AsanPlanImages ()) [] "p;2p;1p;3g00;Kj24Tg00[Mj13Tg00\Gj10Tg005Tj31Tg00:Qj32Tg00RIR0g00RiR1'4g0014g00]AR2#3%0231=201do"). Qed.

Lemma asan_in_hull : forall a : word,
  APS.in_hull BOTH (bv_unsigned a) = false -> find_segment ASEGS (bv_unsigned a) 1 = None.
Proof.
ltac2:(KReplay.run1 (kr_t_AsanPlanImages ()) [] "h01Hh14__x1h24__x2h31xh41yh52H0h67__arithh74__ffh88__varmaph95__with:2b1h;2b2h<1ap;1p;2p;4p;3p;6p;7p;8g00Haj13Tg00^9j1WTg00^Wj1FTg00_:j21Tg00_dj2VTg00[Mj1LTg00\Gj1ETg00<Ej29Tg007QR0j26Tg00@6j2ATg00=_j25Tg00`ej27Tg006Yj22Tg0075j24Tg00@Xj2UTg00:kj1RTg0054j1QTg00ETj2NTg00L\j1KTg00F2j4HTg00FPj1GTg00Fnj1DTg00GYj2:Tg00PVj4<Tg009oj1CTg00IFj2BTg00;Kj2ITg00Ihj2JTg00:Qj3=Tg00JTj3@Tg00K3j4MTg00Kej3?Tg00aBj2OTg00N@j3PTg00abj6>Tg00QAj7STg00Qej8TTg00RIR1f0R2g00SI3=p=0f1R3g00TnR4g00UMR5P5g00UmR6P2g00VMFSp=8f3R7P4P5P5P6f2R4P3P2GTp=;g00XSR8#3R9#3#3#3#3#3#WR:#Fg00]AR;11:2'V#0g0014%L;R<%E;R;11:3g00c3g00<cR=1932#0%04R>%03R?'6[R@%02,6?1943#0R?[%07/6>\?1A32P3n2001000000120000000X;1X:1P@^;1^:1P211:4R@,5<R?17@;R@P3O3%0?%0@'6P011:7R0,5<#0170;#0f4,1:R0/2<14;0'6P215<0#0g00SiR@P=1532#01234R?[R>1223RA1543#0RB[1247\B1U32P3n2001000000120000000X4@W3P>^4@^3@P2P<f6,1:R>P3O312><f7,1:RB/2<RC14;BRBg00YVRD#RRE%QDRDP@1N@4P3%K@CHRF%G@RG%D@RHP@1:@8R8g00TG1:@9R9C<,8HRI%C5R5PIC;1BH6R6P2P4g00RiRI,I11J24==1Idg00Y8=@@3CMRIb7b8b9X1@X2@P?\A^1@^2@P2P<f8,1:R:P3O3b63?b0b5W0P2O1170;#0P=1732#01434R=[R01423R<1743#0RA[1447\A1O32P3n2001000000120000000X4@X3@P0^4@^3@P2P>P;P3O314;>PEPDPFPGPHP@P8g00VmP9C<,8HRHP5PHC;P6PIb7b8b9X1@X2@P=\<^1@^2@P2P:P;P3O3b69PCBb0b5W0P2O1n200100000021100011000b0b5E>W0W<o"). Qed.

Lemma asan_res_len : APS.res_len_ok ASEGS BOTH.
Proof.
ltac2:(KReplay.run1 (kr_t_AsanPlanImages ()) [] "p;1p;2g00C7j10Tg00;Kj22Tg00d;j21Tg00e?g00ZB#0#0#0#0'2g0014g00]A'1do"). Qed.

Lemma asan_res_hull : Forall (fun iv => img_lo BOTH <= bv_unsigned (fst iv) /\ bv_unsigned (fst iv) + bv_unsigned (snd iv) <= img_hi BOTH) (segments_reserved ASEGS).
Proof.
  assert (E : segments_reserved ASEGS = [(Z_to_bv 64 0x10000, Z_to_bv 64 0x20000); (Z_to_bv 64 0x30000, Z_to_bv 64 0x81000);
                                         (Z_to_bv 64 0xb1000, Z_to_bv 64 0x2000); (Z_to_bv 64 0xb3000, Z_to_bv 64 0x55c000)])
    by (vm_compute; reflexivity).
  rewrite E. cbn [img_lo img_hi BOTH].
  repeat constructor; cbn [fst snd]; rewrite ?u64_lit by lia; lia.
Qed.

Lemma asan_hull_ok : APS.hull_ok BOTH.
Proof.
ltac2:(KReplay.run1 (kr_t_AsanPlanImages ()) [] "h07__arithh14__ffh28__varmaph35__witp;1p;2p;4p;3p;7g00Haj10Tg008Mj16Tg0075j25Tg0112j27Tg00H<j13Tg00<cj22Tg00:kj1ATg0054j1@Tg00L\j1MTg00FPj1LTg00Fnj1KTg00M]j29Tg00PVj4?Tg00IFj2ITg00;Kj2=Tg00Ihj2HTg00:Qj3<Tg00JTj3ETg00K3j4DTg00laj4:Tg00[Mj1FTg00\Gj1GTg011Rj1BTg00QAj7JTf0R0#0#0p=;%00#0#0#0p=1g00SiR1g00Y8R27<0p=8%30#3#3#3p=4%30#3p=Cf1R3g00Tng00UMR4P4g00UmR4P0g00VMFJp=>g00XS#0R5#0#;#1#1R6#0R7#0#;#6R8,52R9%66R6,78#8R:%45#0#C#0#3#1#1#1#6R5/76#8R;%47#4#4#4#0#;#1#1#1#6R7,55R<'2R='2g00YVR>#AR?%@>R>%M1R@%L1RA%K1RBP11912g00VmRC1918C?'>1IB4R4P0f2R8g00RIRDg00RiRE'=1H08=<DEdAE123CDR3b1b2b3P9P0b0P:P=1=12R=P;P<P=P?P>P@PAP11915PC1917C?,>BP4P3b1b2b3P<P0b0C:C:C:g012SR0,55,2;,2:,29eg00]AR9#FR:,5217:6#8%G9R:/76#815:0'2'2'2e%B9eo"). Qed.

Lemma asan_shadow_ok : APS.shadow_ok BOTH.
Proof.
ltac2:(KReplay.run1 (kr_t_AsanPlanImages ()) [] "h02Hah17__arithh24__ffh36__sat0h46__sat1h58__varmaph65__witp;1p;2p;3p;4p;7g00Haj13Tg008Mj15Tg00i]j2>Tg006Yj2:Tg0075j22Tg00jEj2MTg00jbj3BTg00:kj1@Tg0054j1?Tg00L\j1=Tg00FPj1<Tg00Fnj1;Tg00M]j26Tg00H<j14Tg00PVj49Tg00^9j1NTg00kFj3LTg0102j7KTg00IFj2GTg00;Kj2ATg00Ihj2CTg00:Qj3DTg00JTj3ETg00K3j4FTg00<cj28Tg013Jj1HTg014Hj1ITg00QAj7JTf0R0#4#4p=0%30#3p=1f1R1g00TnR2g00UMR3P3g00UmR4P0g00VMFJp=7g00XSR5#3R6#5R7%06#0R6#5R8'>g00Y8R9/:712981M78R:,:9[[1297R;g010VR<AB781UW0129:\<^0;g00YVR;#@%?;g00SiR;#=%<;%;;R<P2P3P3P4P;16;9g00VmR3%45#0#0#0#0#0#0#0#3#1#1#1#1#1#1#1#5R5,6;R2C9,7<P;P2P316;7%N65L;C9,7<FK1G<4P0f2R<g00RIR4g00RiR6'A1C0<=D46dAE;91CFb2b5b61295125:'8P0b1b3b4g00]AR0#HR5,29125:'8e%I0eo"). Qed.

Lemma asan_res_sizes : APS.sum_sizes (segments_reserved ASEGS) = 0x5ff000.
Proof. vm_compute. reflexivity. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma asan_hex2 : hexscanZ AsanUbsan_seg_bytes_002 0 8192 = true.
Proof.
ltac2:(KReplay.run1 (kr_t_AsanPlanImages ()) [] "p;2p;1p;3g00;Kj25Tg00Haj11Tg008Mj12Tg016Nj34Tg00:Qj33Tf0#1#1p=0g00RIR0g00RiR1'5g017Jg00Y8g00XS#1#0#0#0#0#0#0#234=301do"). Qed.
Lemma asan_hex3 : hexscanZ AsanUbsan_seg_bytes_003 0 5619712 = true.
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
Lemma asan_len2 : Z.to_N (Uint63.to_Z (PrimString.length AsanUbsan_seg_bytes_002) / 2) = 8192%N.
Proof.
ltac2:(KReplay.run1 (kr_t_AsanPlanImages ()) [] "p;1p;2p;3g00Haj11Tg00^9j13Tg00;Kj22Tg01:Pj19Tg01;4j18Tg008Mj17Tg01;ej24Tg01<Bj15Tg00:Qj36Tf0#1#1p=0g01<`R0g00XS#1R1#0#0#0#0#0#0#3R2'2g017J#9#8%71'4#5=602do"). Qed.
Lemma asan_len3 : Z.to_N (Uint63.to_Z (PrimString.length AsanUbsan_seg_bytes_003) / 2) = 5619712%N.
Proof. vm_compute. reflexivity. Qed.

Lemma asan_segs_eq : ASEGS = [AsanUbsan_segment_000; AsanUbsan_segment_001;
                              AsanUbsan_segment_002; AsanUbsan_segment_003].
Proof.
ltac2:(KReplay.run1 (kr_t_AsanPlanImages ()) [] "p;1p;3p;2g0054j13Tg00:kj12Tg00;ej30Tg00;Kj21Tg00WTR0#3g01=>g01>_g01@@g01Aa%20500500500500'1o"). Qed.

Lemma asan_rw_window : forall m (x : word),
  0xb1000 <= bv_unsigned x < 0x60f000 -> wview ASEGS m x <> None.
Proof.
  intros m x Hx. unfold wview. destruct (m x); [discriminate|].
  destruct (find_segment ASEGS (bv_unsigned x) 1) as [seg|] eqn:Hf.
  - apply find_segment_some_spec in Hf as (Hin & Hb & Ht).
    rewrite asan_segs_eq in Hin.
    destruct Hin as [<-|[<-|[<-|[<-|[]]]]];
      cbn [seg_base seg_size seg_writable seg_perms seg_bytes string_has Ascii.eqb
           AsanUbsan_segment_000 AsanUbsan_segment_001
           AsanUbsan_segment_002 AsanUbsan_segment_003] in Hb, Ht |- *.
    + exfalso. lia.
    + exfalso. lia.
    + cbn -[segment_byte_at]. apply (segment_byte_at_someZ _ 8192); [exact asan_hex2 | rewrite Z2N.id by lia; cbn in Hb, Ht; lia].
    + cbn -[segment_byte_at]. apply (segment_byte_at_someZ _ 5619712); [exact asan_hex3 | rewrite Z2N.id by lia; cbn in Hb, Ht; lia].
  - exfalso. destruct (Z.lt_ge_cases (bv_unsigned x) 0xb3000) as [Hl|Hl].
    + apply (find_segment_none_spec _ _ _ Hf AsanUbsan_segment_002);
        [rewrite asan_segs_eq; cbn; tauto | cbn; lia].
    + apply (find_segment_none_spec _ _ _ Hf AsanUbsan_segment_003);
        [rewrite asan_segs_eq; cbn; tauto | cbn; lia].
Qed.

(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.AS Require AsanNodesMmLib.

Lemma asan_hull_cov : AsanNodesMmLib.hull_cov ASEGS BOTH.
Proof.
  split; [cbn; lia|].
  assert (E : segments_reserved ASEGS = [(Z_to_bv 64 0x10000, Z_to_bv 64 0x20000); (Z_to_bv 64 0x30000, Z_to_bv 64 0x81000);
                                         (Z_to_bv 64 0xb1000, Z_to_bv 64 0x2000); (Z_to_bv 64 0xb3000, Z_to_bv 64 0x55c000)])
    by (vm_compute; reflexivity).
  intros z Hz. rewrite E. cbn [img_lo img_hi BOTH] in Hz.
  unfold APS.in_ivs. cbn [existsb fst snd]. rewrite !u64_lit by lia.
  destruct (Z.lt_ge_cases z 0x30000); [|destruct (Z.lt_ge_cases z 0xb1000); [|destruct (Z.lt_ge_cases z 0xb3000)]];
    repeat (apply orb_true_iff; first [left; apply andb_true_iff; split; [apply Z.leb_le; lia | apply Z.ltb_lt; lia] | right]).
Qed.

(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.AS Require Import AsanInit.
From LinuxProcessSemantics.LinuxProcessSem Require Import Run.

Definition APH : PhdrInfo := AsanUbsan.M.phdrs.

Lemma asan_img_facts : img_facts ASEGS BOTH APH.
Proof.
  constructor.
  - repeat split; reflexivity.
  - cbn [img_lo img_hi BOTH]. lia.
  - vm_compute. reflexivity.
  - exact asan_res_hull.
  - rewrite asan_res_sizes. reflexivity.
  - cbn [rw_lo rw_len BOTH]. split; [lia|]. intros m x Hx. apply asan_rw_window. lia.
  - exact asan_shadow_ok.
Qed.
