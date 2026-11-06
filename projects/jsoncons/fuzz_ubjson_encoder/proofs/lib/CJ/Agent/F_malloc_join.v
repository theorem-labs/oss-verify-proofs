(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require BvWfKernel.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.CJ.Lib Require Import Tac Image ZBridge SysStep SFModel ITree Nodes Decode Arr.
(* [comment removed for export] *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.CJ.Agent Require Import F_syscalls MallocRep F_malloc_free F_malloc_fast F_malloc_enframe MallocTree MallocFacts_A MallocKit_A.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.CJ.Spec Require Import STree Malloc MallocCtrl Monad Prog.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.CJ.Agent Require Import Malloc_fp F_malloc_enf AllocSlot_iface Malloc_iface.
Import ListNotations.
Open Scope Z_scope.

Ltac shw := match goal with |- evt _ _ (MS ?R _ ?pc _ _ _ _) => idtac "PC" pc; idtac "REGS" R end.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.CJ.Lib Require Import RunP.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require KReplay.
Ltac2 kr_t_F_malloc_join () := "C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc4aptrC13~~~I35stdpp9countable9Countable00C35stdpp4base;RelDecisionC35stdpp4base4fmapC99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ5Agent9Malloc_fp9unk_agreeC13~~~I35stdpp4gmap4gmap00C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc9s_regionsC13~~~I47Corelib4Init5Logic2eq00C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc:get_shadowC13~~~C35stdpp9decidable;prod_eq_decC35stdpp9countable>prod_countableC99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc8s_groupsC13~~~I47Corelib4Init9Datatypes6option00C35stdpp4gmap;gmap_lookupK47Corelib4Init9Datatypes6option01C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc6r_kindC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc5r_lenC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc;round_up_pgC13~~~C56Stdlib6ZArith6BinInt1Z2ltC99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc9cell_readC13~~~K99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc7cellval02C13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ5Agent9Malloc_fp;grp_hdr_covC13~~~C47Corelib4Init5Logic3notC47Corelib4Init5Logic6eq_indI47Corelib4Init9Datatypes4prod00K47Corelib7Numbers7BinNums8positive01K47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1Z02C56Stdlib6ZArith6BinInt1Z3addI47Corelib4Init5Logic2ex00I47Corelib4Init5Logic3and00K47Corelib4Init5Logic3and01C47Corelib4Init5Logic8eq_ind_rK47Corelib4Init5Logic2ex01C35stdpp4base6lookupC56Stdlib6ZArith6BinInt1Z2leC47Corelib4Init9Datatypes3fstC47Corelib4Init9Datatypes3sndI47Corelib7Numbers7BinNums1N00I99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc6region00C13~~~I99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc4ghdr00C13~~~I47Corelib7Numbers7BinNums1Z00I99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc6mstate00C13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ5Agent:MallocTree3memC13~~~C45stdpp7numbers1N6eq_decC35stdpp9countable;N_countableI99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc6shadow00C13~~~C45stdpp7numbers1Z6eq_decC35stdpp9countable;Z_countableI99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc5rkind00C13~~~K99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc5rkind03C13~~~K47Corelib7Numbers7BinNums1Z01I99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc7cellval00C13~~~K47Corelib7Numbers7BinNums8positive03I47Corelib4Init5Logic5False00K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00I47Corelib4Init9Datatypes4list00C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib5Frame5munchC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc6r_baseC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib5Frame=disjoint_fromC13~~~C56Stdlib6ZArith6BinInt1Z3powC99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib3Mem2waC13~~~C45stdpp9bitvector;definitions;bv_unsignedC99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib5Frame7outsideC13~~~C56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z:pow_nonnegC56Stdlib6ZArith6BinInt1Z7compareK47Corelib4Init5Logic2eq01K47Corelib4Init9Datatypes4list01K46Stdlib9micromega6VarMap1t02K46Stdlib9micromega6VarMap1t03I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr01K46Stdlib9micromega7EnvRing5PExpr02K47Corelib4Init9Datatypes6option02K46Stdlib9micromega7EnvRing5PExpr03C46Stdlib9micromega5Tauto8BFormulaC46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundC99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib5Frame@disjoint_outsideC13~~~K47Corelib4Init9Datatypes3nat02K46Stdlib9micromega=RingMicromega5Psatz02K46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega:ZMicromega;ZArithProof02K47Corelib4Init9Datatypes4list02K46Stdlib9micromega7EnvRing5PExpr07C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib3Mem;wa_unsignedC13~~~K46Stdlib9micromega=RingMicromega7Formula01K46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega5Tauto8GFormula05K46Stdlib9micromega5Tauto8GFormula08K46Stdlib9micromega=RingMicromega3Op203C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K47Corelib4Init9Datatypes4unit01K46Stdlib9micromega=RingMicromega3Op205C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib5Frame3ivlC13~~~I47Corelib4Init5Logic4True00I47Corelib4Init9Datatypes:comparison00I46Stdlib9micromega:ZMicromega;ZArithProof00I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01K47Corelib4Init9Datatypes3nat01K46Stdlib9micromega:ZMicromega;ZArithProof01I47Corelib4Init5Logic2or00C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics<write_to_memC56Stdlib6ZArith6BinInt1Z3lebC47Corelib4Init9Datatypes6lengthC56Stdlib6ZArith6BinInt1Z6of_natC56Stdlib6ZArith6BinInt1Z3ltbC47Corelib4Init9Datatypes4andbC56Stdlib6ZArith6BinInt1Z3subC56Stdlib6ZArith6BinInt1Z6to_natC46Stdlib5Lists4List9nth_errorC56Stdlib6ZArith6BinInt1Z9leb_spec0I47Corelib4Init9Datatypes7reflect00C56Stdlib6ZArith6BinInt1Z9ltb_spec0C56Stdlib6ZArith4Znat5Nat2Z9is_nonnegK46Stdlib9micromega6VarMap1t01C47Corelib4Init5Logic9False_indC99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib3MemAwrite_to_mem_specC13~~~K46Stdlib9micromega5Tauto8GFormula03K47Corelib4Init9Datatypes4bool02C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc:s_next_ridC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc:s_reservedC13~~~C56Stdlib6ZArith6BinInt1Z4of_NC56Stdlib6ZArith4Znat3N2Z7inj_iffC47Corelib4Init5Logic7iff_symC46Stdlib9micromega;ZifyClasses7rew_iffC56Stdlib6ZArith4Znat3N2Z9is_nonnegC56Stdlib6NArith6BinNat1N2leC46Stdlib9micromega;ZifyClasses;rew_iff_revK99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ5Agent9Malloc_fp4mrel01C13~~~C46Stdlib9micromega;ZifyClasses5mkrelC56Stdlib6ZArith4Znat3N2Z6inj_le".
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Section CEIL_WRAP_1.
Context {RUNp : RunP}.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma unk_agree_ext st st' o m :
  unk_agree st o m -> s_regions st' = s_regions st -> (forall rid, get_shadow st' rid = get_shadow st rid) ->
  s_groups st' = s_groups st -> unk_agree st' o m.
Proof.
ltac2:(KReplay.run1 (kr_t_F_malloc_join ()) ["CEIL_WRAP_1"] "p'0h02ghh11Hh21bh32Hch42Hrh51gh61mh71oh83ridh92sth:3st'h;2EGh<2ERh=2ESh>2Hbh?2Hfh@2HkhA2HohB2HxhC2NGhD2UAhE1hhF3offhG1rhH1si001xp;3p;4p;1p;2p;6g0000R0p4p70R1p1001>p4p710p8P1p1001\R2p4p710p8P1P2p4p7210p8P1p10025p4p73110p8g002Gj3OTg003^j4LTg0042j19Tg005Ej30Tg005_j2;Tg0073j4XTg007Qj6WTg0082j11Tg009Dj1FTg009fj4ITg00:?j25Tg00:aj1STg00<1j1[Tg00=@j1ZTg00>Uj27Tg00?1j2CTg00@Dj1BTg00AWj3MTg00C0j1KTg00CIj6HTg00Cej2VTg00DEj1UTg00Djj1DTg00EOj1TTg00Emj2JTg00FJR1j2?Tg00FdR2j26Tg00G?j4GTg00GZj6RTg00H8j4ETg00HRj6QTg00Hfj2PTg00IBj3NTg00I_j3YTg00J<R3g00JZR4f3R5f2R6f1R7f0R8EQp=@1P67/68p==f6R9f5R:g00KlR;f4R<P5P6P7EQ;08p=2g00M<R==N38p=<A0378p=AAY3=8p=31678,66p=8AN3=7=038p=:1P<51J78,76'6p=4A0367/68p=>g00MZR>g00NlR?AO578P3g00P>R@g00PWRAP4CLRB%95%9<30g00Q5RC1;:81;9830^83P0P3P@P=g00RGRDCXREP3P@PAP=PDg00R`EWRDP;CLRF%1:%1930%F4RGPBP3P@PAP4CIRAP5f:R@#9C@154630g00S>%S5g00TO30g00U`%[<#Z,757=5g00V>RHf=RI/;9/C<%B530f>RJf7RK;M:#KPBf?RL#9PBPAf9RMP8C@f8RN,5450GX5BP<f@RO#9RPf;RQEHPBPAPNPPC@154K50GPC1;OM1C8N%BK50HXHCP6fARC/;MRGPQPMO1EH1CGK%B950HPJP@PMPNPKP7P:P<P8fBRH?M@NRGP11V3=RP%F;RAPPPFP0PEPDP;CIRDP7fERE#115;8R0F2%<7RB/AI%37RRg00WQ#U#D#D#TRS,JRRT,7Q7=Q38X0;,?;X2Pg00X6RUP8PAPPPFPDP7fGRV#1P0F21ABL17IT9=RI38X0;,?;P1P;PAPPPFPDP6fHR1#1P0F21:6O%36RLPJPJPLPSD438X0;PUP8PAPPPFPDP<fJRL#1P0F21:<H%3<RHPOPOPHPSD438P2PAPPPFPDP:fKRH#115;7F2%<:fCRO%3:RWPCPCPWPSD43>PUP8PAPPPFPDPKfMRK#115;5F2%<NfF%3NRNfDRWPWPNPSD43>P21:MV%3MRVPEPEPVPSD4PUP8fIRU,:Qf<#3RQP1P1PQPSD4POPPPAPPPFPDP7fT#1P0F21ABK17HT9=RH38X0;,?;X2PPIP;PAPPPFPDPJfS#1RRP0F2%<JfLR0%3JRTPLPLPTPSD43>RT'6X0;PMPFPRPAPPPFPDPJP815;@F2/6TX5FPAPPPFPDPIPR15;MF21:IHRH%3IRIPUPUPIPSD4RS'6P:PHPSP7P8CGCGfR#1P0ERCECEO1WBW?P7P8O2n2001000000121000000W1W>P7P8O2n2001000000121000000W1X0;P7P8O2n2001000000121100000W1X2PP7P8O2n2001000000121100000W1%KGeO9b3b4WCW3WAW@W4XE=XF=XG4X83AO9:<eW;W=W<WDX6?X7?X:>X9>P5P6P7P8O4X6?W7X:>W9o"). Qed.

Lemma unk_agree_munch st o m m' W :
  unk_agree st o m -> munch W m m' ->
  (forall rid r, (s_regions st) !! rid = Some r -> r_kind r = RKGroup -> disjoint_from W (r_base r) (round_up_pg (r_len r))) ->
  (forall rid r, (s_regions st) !! rid = Some r -> 0 <= r_base r /\ r_base r + round_up_pg (r_len r) <= 2^64) ->
  unk_agree st o m'.
Proof.
ltac2:(KReplay.run1 (kr_t_F_malloc_join ()) ["CEIL_WRAP_1"] "h06__sat3h14__x1h24__x2h34__x3h41oh51rh63ridh72Hah81Wh97__arithh:4__ffh;6__sat2h<8__varmaph=5__with>1mh?2m'h@2sthA2B0hB2B1hC2HBhD2HDhE2HchF2HkhG2HohH2HrhI2MUhJ2NGhK2UAhL1ahM1hhN3offhO1zp;1p;3p;4p;2p;6p;7p;8g00Djj19Tg00XSj1RTg00Y1j1PTg009Dj1GTg00YTj1UTg002Gj3KTg00Z4j3hTg003^j4eTg009fj4`Tg0042j1@Tg00:?j2FTg005Ej33Tg00:aj1TTg00[Aj12Tg00\Qj3sTg00Emj20Tg00EOj1LTg00]fj2gTg00Hfj26Tg00FdR0j27Tg00>Uj28Tg005_j2aTg00?1j2_Tg00@Dj1^Tg00AWj3]Tg00C0j1\Tg00^Cj1?Tg00_Kj2ITg00`5j2HTg00aDj2[Tg00alj3ZTg00bPj2YTg00c1j2OTg00cKj1XTg00ckj2ETg00dIj4WTg00dgj1VTg00eEj1wTg00f0j2STg00fSj2CTg00DEj1vTg00g6j1uTg00gXj3QTg00h;j2rTg00h]j2qTg00iIj3pTg00ihj4oTg00jZj6lTg00l2j1=Tg00lQj2:Tg00m:j3>Tg00mcj2JTg00nOj3MTg00noj3iTg00oRj2jTg00GZj6kTg00CIj6fTg00HRj6mTg00<1j1nTg00=@j1dTg010cj4NTg011Nj7cTg0122j7bTg012Vj8tTg00J<R1g00JZR2f3R3f2R4f1R5f0R6Emp=B%n6#dp=4g00U`R7/66p=1g00M<R8P5g013:P6CNp=;P5g013aR9g014@R:P:g014`R;P6g015@Fcp=5P8P5g015`P6CNp=DP4P9P:P:P;P5P6Fbp=AP3P9P:P:P;P4P5P6Gtp=<g00MZR9g00NlR<g00WQR=#9R>#9#9R?#9#9#9R@#RRA#P%R?#P#GR?[RBg016G#URCf4RD?K34Ah534%G2REP1g00P>RFg00PWRGP2CeRHP1PFPGP2C`RGP5f8RF#@CB1F26RI33g00S>RJ%T5g00TORK33f6RL%24%443s[[^52^61PHPGP5f9RM#@CB=3EI%25RI#1%45,0I%L>RI%L@R@'gRN'6'7[^52^61PHPGP3f<RG#@CB1F2453E%T3=3JK%13RK%4D,83'7g00V>f?RJ/aL/_D%^333f@REf7RHf5RO3]#\P?PJ%2HRP/0L#?RQO1PJ%2FRR/0H#?O1=3?6X4?f;R?PQPMPFPHPDO3%1P%4H,0P/6N'7P0%1R%4F,0R/6N%2M/0F#?,IA,HJP6f:#2#1%2?%4?'0/6NP8%2GRR/0?R0fC/H6XO8fBPR%4GP0PJf=PGPMPFO41[I@RM187IRR%1@187N[RP[RS%1IRTg017RRUAZI@5UW7R@%1N\U^7TRTP5g017n1Y7I'OPReO1RRPPg018TRU#XRV%UURWP81E84P51E83CWRX%V8RY%w8RZ1S87R[1C8>R>';,5Z%v=,C8R\,D>,5Z5AZR]%u:R:1C8=R=AQ8=>R>';,5ZAQ8=\R\,D>,5Z5AZC<1rZ;R;P6P4g019@R^g019`R_'O1q64=3^_dAp875CoR7b:b<b=X18X28X38%15R_1854'71054R^,651053,8^'7[^18^28^38P6%4ER^PJ%2ER`P?O4b9b0b;b0El%?0,IAPMPSP@PTPRPPg01:@RP#=RR#=RT#=R@#=,:81:8R1:8PRP5>85>8g01:_RR'J1:8@1:8T=>8P5>8/JR=MUV5MUPWPXPYPZ1S8I=i8ARA,;\,5ZP:PZ1;[=,5ZP:PZP]P:1;[>,5Z1D>A,5Z5AZC<C<C<P;P7b:b<b=X18X28X381064/6N183D,7K103DRK#118KN'7[\_[^18^28^38P6P^PJP`PDPOP?O6b9b0b;b0,j0EkWBWAP5P6O2n2001000000121000000bLO2PEPQO1PGPFPHPLPOPDP3P4P5P6O9EfWJWEWGWFWHXM8XN8X52X61AKFHOeWCWDWIWKX8CX?BX><X4<X@9PDP3P4P5P6O5W8W?X><W4W@o"). Qed.

(* [comment removed for export] *)
Lemma unk_agree_write st o m a bs :
  unk_agree st o m ->
  (forall rid r, (s_regions st) !! rid = Some r -> r_kind r = RKGroup ->
     a + Z.of_nat (length bs) <= r_base r \/ r_base r + round_up_pg (r_len r) <= a) ->
  (forall rid r, (s_regions st) !! rid = Some r -> 0 <= r_base r /\ r_base r + round_up_pg (r_len r) <= 2^64) ->
  0 <= a -> a + Z.of_nat (length bs) <= 2^64 ->
  unk_agree st o (write_to_mem m (wa a) bs).
Proof.
ltac2:(KReplay.run1 (kr_t_F_malloc_join ()) ["CEIL_WRAP_1"] "p'0h06__sat3h14__x1h24__x2h34__x3h47__arithh54__ffh66__sat2h78__varmaph85__with91bi001bh:4cstrh;2r0h<4__p1h=4__p2h>4__x4h?1oh@1li011lhA1ri021rhB3ridhC1HhD2HahE1ahF2bshG2l0hH1mhI1ni031nhJ2sthK2A0hL2A1hM2B0hN2B1hO2HBhP2HDhQ2HchR2HkhS2HohT2HrhU2NGhV2UAhW2a0hX1hhY2n0hZ2o0h[3offh\1zp%0p&0p;1p;3p;4p;2p;6p;7p;8g00Djj1?Tg00XSj1iTg00Y1j1zTg00YTj1\Tg002Gj3lTg009Dj1gTg003^k406Tg009fj4yTg0042j1YTg00:?j2[Tg005Ej30Tg00:aj1ZTg00[Aj14Tg01;KR0j2eTg00EOj1cTg00]fk204Tg00FdR1j2>Tg00>Uj27Tg005_j2uTg00?1j2tTg00@Dj1rTg00AWj3qTg00C0j1RTg00Emj21Tg00^Cj15Tg01;ej4Sk301Tg00_Kj2mTg01<ij2BTg01=Fj2;Tg01=fj1ITg01>Fj2ATg01>cj28Tg01?Aj2FTg01?^j1HTg01@>j3GTg00Hfj23Tg01@\k20>Tg01A?R2j2kTg01Abk20=Tg01BEj1jTg00aDk20<Tg00alk309Tg00bPk208Tg00c1j2WTg00l2j1NTg00lQj2ETg00m:j3DTg00mcj2UTg00cKk107Tg00nOj3VTg00ckj2PTg01Bjk105Tg00dgk103Tg00eEk102Tg00DEj1aTg00fSj2CTg00gXj3MTg00g6j1xTg00f0j2`Tg00h;j2vTg00h]j2wTg00iIj3sTg00ihj4{Tg01CHj2hTg00noj3|Tg00oRj2}Tg00GZj6^Tg01Cgj6~Tg00CIk600Tg00HRj6pTg00<1j1]Tg00=@j1bTg00dIj4oTg010cj4dTg011Nj7fTg01E>j6nTg0122k70:Tg012Vk80;Tg00J<R3g00JZR4f3R5f2R6f1R7f0R8Epp=X1;78#Ip=Q1167/38p=O%]7#b,16/38p==g00U`R9/38p=2%]8#bp=T%47/18p=:%I8,17p=@g00M<R:P6P7P8Cop=<P:P7g015`P8Cdp=JP7g013aR;g014@R<P<g014`R=P8g015@R>Ffp=KP6P;P<P<P=P:P7g013:P8CdP>Ffp=9P7P;P<P<P=P8Enp=_P6P;P<P<P=P7P8K0:p=LP5P;P<P<P=P6P7P8L0;p=6g00MZS00g00NlR;g00WQR>#?R?#?S01#?R@#i#zRA#\S02Q00Q02f4RB?l56%g4RCP3g00P>RDg00PWREP4H06RFP3PDPEP4CyREP7f7RD#YCX1[48RG30g00S>RH%Z7g00TORI30f6RJf5RK,QA%46RL3OA=L6J'e[[^A4^B3PFPEP7f8RL#YCX=0CG%47RG#2%c?RM%?@#?#?R@#cRN+04RO9=G7'>[^A4^B3%2BRG1QAB=OKOPFPEP5f=RE#YCX1[4650C%Z5=0HI%25S03%TB,75'>g00V>f@RI/uJ/tB%r530fARH?qDK#R%gARCPI%4DRF/1J#5S04O1PH%5If?RP%4LRQ/1D#5CS=0C8X?Cf;RRPLPDPBO3%2FA=FDO'>P1%2QA=QLOfBRQ%5HPIf9R1/:L#5RFCSPQPFO150CP8f:#4#2%4R?=ROPCg019@RFPCfDRS%i@S05f<R@#4RT/1RRR#5RU'mRV'BfCRW,;AS06#IS07,1SRX,AV'81FVS#H9GAWfERYPUO1n0100000020000fFRZ%4ER[/1@#5O1R\90C8X?CP:PRPFPC1BY81;AS,@YR],A8'81F8Y#H9GASP\n0100000020000=0C\X\:PHPEP@P1PLO413XTA=T@S'eP013][A=[EYPFPCf>R[#4R]/1ER0,BZ1;AY,@ZRT,A0'81F0Z#H9GAYfGRX%50O1R0n0100000020000=0C0P813T]1:P[RT-0>XS0813XT1BXT'kS09fHS0:1:IP'BS0;PFP2fIS0<%4HS0=/1I'3S0>PFPC1:WQRPfKRTfJR0,;A'@R\'AR^,871FPT#H9GA0fLR_%5PO1R`n0100000020000=0C`S0?P71:QH,30R020=P\RQ17P\/k^R^1:SW1;AT,@_'AR\PFP21:YSfMRP1;A_'@'7R`PFPCg019`Ra/87fNRb1:XZRcfO'F#H5GARdfP%5cO1Rcn0100000020000=0CcS0@P71:ZY1;AP,@b'7RPA0CdcRe1;AbRb#jS0A%Ib#2S0B20<MNRb179MRf%2N179O[Rg[Rh%2MRig017RRjB09MN7UWDRN%2O\j^DiRiP7g017n2089M'WPfeO1RfPgp-0Rjg018TRkg01:@Rl#NRm#NRn,E:Ro1E:m1E:lRl5D:Rm5D:g01:_Rp'U&07kRq3VS0C%\kRr1P:6Rs1P:BRt&05:Ru7<57<7&03:Rv&02:Rw%a?,C:Rx%a>,C:Ry5M:Rz1C:>R>1C:?R?5M:R{'J,Kw%x<R<PwA9w{xP<Pw1`:9R|=9wy1_wJR}5LwP<1_wDS0DC6C6C61vw=R=P8P61WFa1w86=0FadAs:97C{R9b5b7b8X1:X2:X3:X>:X<jW=11561187S0E'71176S0F/3B1>GJPL[[[^1:^2:^3:^>:^<j^=jP8g00X6S0G%T_S0H,7T%4_S0IPTfS,QAfTS0JPKPEPXO9b4b0b6b0b:'hPFPC18aaPdPcn0100000020000=0CcS0KeWGP8O1%RPR_1WCcRGPFPCg01EbR~,8aPdPcn0100000020000=0CceWIP8O1S0Ln10210010200021110110103b9b;W@P8O1%R0PQP^P\PFP2P`PFPC18~7PdPcn0100000020000=0CcP7PGPFPC18~aPdPcn0100000020000=0CceX@PP8O1PGPFPC18~~PdPcn0100000020000=0CceXY_P8O1n10210010200021010110103b9b;WIP8O1R_n10210010200021110111103b9b;WCP8O1A=][ZQ08Q09Q0;PFP2Q0>Q0?P7PQP^P\PFP2P`Q0@P7Q0AQ0BPbPhPNPiPfPgQ0CPr1P:5R`?<BuA<t6u7<7PvPwA9w>zP<PwQ01,C:Rz9M:x=9w>P<Pw1Jyz,Kw9Lw}P<Q0DC6C6C6P=P9b5b7b8X1:X2:X3:X>:X<jX=j1157,38AOB57175BR},>JPL[[[^1:^2:^3:^>:^<j^=jP8Q0G%2TQ0IQ0HPTQ0JP1PEPXO9b4b0b6b0b:,heQ0KeXGPP8O1Q0Ln10210010200021110110103b9b;X@0P8O1P_n10210010200021110111103b9b;WCP8O1n200100000021100011000bZPVQ06#jRVQ07#2R_PbPhPNPiPfPg%NnRn#N,E:=D:m/Up1E:nAD:ol5D:/Up=Vkq5VkPrA<`5u9<s7PvPwAM:>x1`:MQ055|:RM59wP<PwA9w|>R>P<PwA9w|?1J?x,Kw5LwP<A9w|{1J{M,Kw5LwC6C6C6P=P9b5b7b8X1:X2:X3:AO86O%27R|Q03/>}115BR}#217}O'>[[[^1:^2:^3:P8%THPIQ0=PKPJP@O6b4b0b6b0b:,}RE^PY%5SPWPUCSPWPYPSPUPVP_PbPhPNPiPfPgPqPr1P:7PvPwP>P<P>C6P=P9b5b7b8X1:%28P|[^1:P8Q0<PSO2b4b0b6b0b:PVP_PbPhPNPiPfPgPqPrA<s7uPvPwA9w{MRMP<PMC6P=P9b5b7b8X1:X2:Q0E/3OQ0F/3O[^1:^2:P8Q0:,QAQ0<PWO3b4b0b6b0b:E~E^WNWMP7P8O2n2001000000121000000bWPHQ04O1PEPLPDPJPKPBP5P6P7P8O9J00WUWQWSWRWTXX:X[:XA4XB3%5J>01DK9l1LeWLWKWOWPWVWFXE:XH;X?;WJPBP5P6P7P8O5WFXE:XH;W?WJo"). Qed.
(* [comment removed for export] *)

Lemma mrel_same st st' :
  s_regions st' = s_regions st -> s_next_rid st' = s_next_rid st -> s_reserved st' = s_reserved st -> mrel st st'.
Proof.
ltac2:(KReplay.run1 (kr_t_F_malloc_join ()) ["CEIL_WRAP_1"] "h03EN0h17__arithh24__x1h34cstrh45cstr0h52sth63st'h72ENh82ERh92ESh:1Hh;4__ffh<8__varmaph=5__with>1gh?1nh@1rhA2r'hB3ridhC1xhD1yp;4p;1p;3p;2p;7p;6p;5p;<g003^j4\Tg0042j1:Tg005Ej30j1DTg01FBj12Tg00Cej2[Tg00YTj1ETg01GVj1BTg009Dj1TTg009fj4STg00:?j2=Tg00:aj1<Tg00[Aj1>Tg00<1j19Tg00HfR0j21Tg00Fdj24Tg00c1j25Tg01HjR1j13Tg01IHj2VTg01Iij3UTg01JFj4@Tg01Jmj17Tg00cKj1RTg00ckj2QTg00dgj1PTg00eEj1MTg00fSj2LTg010cj4KTg011Nj7JTg00h;j2ITg00h]j2NTg00iIj3HTg00ihj4OTg00G?j4;Tg00GZj6?Tg00H8j4GTg01KPR2j2CTg01Klj4YTg01LWj5XTg00HRj6WTg01Mkl<FTg00J<R3g00JZR4f3R5f2R6f1R7f0R8EWp=8g00M<R9?078p=6P3P9P8P1P7P6P5f4R:f5R;f6R<f7R=f8R>M<Fp=AP3P9P2P1P0g01NPP;P:P5P6P7P8M<Fp=Zg00MZR0P3g00P>R1g00PWR2P4C\R?%:8%:730%27%265031[99#E%B6%B530P:P5%T4R@P?P3P1P2P4CSR2P7%:<R1C81=48RA30P4P?P2P5%:=RBC8=0@Ag00S>RA%<8%<6RC30%>8%>6RD'6%96RE%98'1'4'4'4XA4P7P?PBP?P2P5P8C81=4650@A0ACC16DD11EE'4'4'4X>?P?P2P6PBC81=4750@%<7R@=0A@RB%>7R2/62R?%97RE/1ERE'4RD'4P8PBPD15A@P?PE1592%2<R<%2=R=503%3<R2%3=RE'6R?%D3R@%D9RA%37%38'6A03781V783UXD3XC3RDP<P21592P=PE159EM9AP:C@P?%7=g00U`R=/1Ef9#2RE#7%3E,1=g018TRE#R%EE1Q97%P9%M9REg013ag014@R?P?g014`R?P9g00WQ,L9RBg013:PBCKg015@FJ1IE?P8P6g019@R?g019`RE'51N86=0?EdAH9=7COb;b<b=X29RE1188^29R?P8%9;O1b1b4b3b0C;C;C;P1P;E?CGW:X@4XB3P3%2:R:%2;/C8X?31C::%3:R;/1;P:P;159;R4P:P;P4EZ%25R5=03:%35R3/6;R1P@PAPDP5P31593P:P;P4M9AP7C@P1%7:11=;%7<11=2PEP?P8%2>#3O1b1b4b3b0CYP5P7E?P8DXW9W7W8X60X50P7P8O2X60W5o"). Qed.
End CEIL_WRAP_1.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
