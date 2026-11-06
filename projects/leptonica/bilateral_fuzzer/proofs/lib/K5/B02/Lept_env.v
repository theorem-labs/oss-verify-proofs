(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.K5.Lib Require Import Tac.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.K5.B02 Require Import ImageA.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.K5.Lib Require Import RzCPS StoreFast.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.K5.PG Require Import Str_tac Startup_glue.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.K5.B02 Require Import Layout.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.K5.AG Require Import Shadow.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.K5.B02 Require Import RT_iface RT_traces RT_gaps_iface LeptTac D_kit Lept_kit Lept_iface.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib Require KReplay.
Ltac2 kr_t_Lept_env () := "K47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00I47Corelib4Init9Datatypes6option00I47Corelib4Init9Datatypes4list00C47Corelib4Init9Datatypes6lengthC56Stdlib6ZArith6BinInt1Z6of_natI47Corelib4Init5Logic2eq00C56Stdlib6ZArith6BinInt1Z2leK47Corelib7Numbers7BinNums1Z02C56Stdlib6ZArith6BinInt1Z3powC69OSSVerify5KrLib2K53B02:Lept_iface4LIB0C1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive01C45stdpp9bitvector;definitions7Z_to_bvK69OSSVerify5KrLib2K53Lib5Cells4cell02C1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes4list01K47Corelib4Init9Datatypes4list02C69OSSVerify5KrLib2K53Lib4Step8rw_cellsC1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib2K53Lib5Cells4cell01C1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic3and00C56Stdlib6ZArith6BinInt1Z3addC69OSSVerify5KrLib2K53Lib3Mem2waC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics<write_to_memK47Corelib4Init9Datatypes3nat02I47Corelib4Init5Logic2or00C47Corelib4Init5Logic8iff_reflC46Stdlib9micromega;ZifyClasses3injK47Corelib4Init5Logic2eq01C46Stdlib9micromega;ZifyClasses6eq_iffC46Stdlib9micromega;ZifyClasses8or_morphC56Stdlib6ZArith4Znat5Nat2Z9is_nonnegC56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z2ltC56Stdlib6ZArith6BinInt1Z:pow_nonnegC56Stdlib6ZArith6BinInt1Z7compareK46Stdlib9micromega6VarMap1t02K46Stdlib9micromega6VarMap1t01K46Stdlib9micromega6VarMap1t03I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr02K46Stdlib9micromega7EnvRing5PExpr03K47Corelib4Init9Datatypes6option02C46Stdlib9micromega5Tauto8BFormulaC46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundC46Stdlib9micromega;ZifyClasses;rew_iff_revC69OSSVerify5KrLib2K53Lib5Cells:cells_sizeC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib9StoreFast@rw_cells_frame_nC1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic3and01C46Stdlib9micromega;ZifyClasses5mkappC46Stdlib9micromega;ZifyClasses6mkapp2C46Stdlib9micromega;ZifyClasses5mkrelK46Stdlib9micromega7EnvRing5PExpr01K46Stdlib9micromega=RingMicromega7Formula01K46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega5Tauto8GFormula06K46Stdlib9micromega5Tauto8GFormula08C69OSSVerify5KrLib2K53B026ImageA5asegsC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B02:Lept_iface;g_pix_allocC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B02:Lept_iface=g_pix_deallocC1?~~~~~~~~~~~~~~~I47Corelib7Numbers7BinNums1Z00I47Corelib4Init9Datatypes3nat00K46Stdlib9micromega=RingMicromega3Op203C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K47Corelib4Init9Datatypes4unit01K47Corelib7Numbers7BinNums8positive03K47Corelib7Numbers7BinNums1Z01C69OSSVerify5KrLib2K53B02:Lept_ifaceAg_LeptMsgSeverityC1?~~~~~~~~~~~~~~~I69OSSVerify5KrLib2K53Lib5Cells4cell00C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B028RT_iface8e_mallocC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B028RT_iface6e_freeC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes3nat01C46Stdlib9micromega8ZifyInst7Inj_Z_ZI47Corelib4Init5Logic4True00I47Corelib4Init9Datatypes:comparison00I46Stdlib9micromega:ZMicromega;ZArithProof00I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01C69OSSVerify5KrLib2K53B02:Lept_iface4LIBHC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2K53B028Lept_env:LIB0_writeC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B02:Lept_iface@g_stderr_handlerC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B02:Lept_iface9e_devnullC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B028RT_iface6io_sspC1?~~~~~~~~~~~~~~~K46Stdlib9micromega5Tauto8GFormula03C69OSSVerify5KrLib2K53Lib9StoreFast@ro_cells_frame_nC1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic2ex01C69OSSVerify5KrLib2K53Lib4Step8ro_cellsC1?~~~~~~~~~~~~~~~K46Stdlib9micromega5Tauto8GFormula05I47Corelib4Init5Logic2ex00C69OSSVerify5KrLib2K53B028RT_iface8SEGTOP_AC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B025D_kit8agree_onC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B028RT_iface=client_staticC1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes4prod00C46Stdlib5Lists4List2InC47Corelib4Init9Datatypes3fstC47Corelib4Init9Datatypes3sndC47Corelib5Lists7ListDef3mapK47Corelib4Init5Logic2or01C47Corelib4Init5Logic7and_indK47Corelib4Init5Logic2or02C69OSSVerify5KrLib2K53B02=RT_gaps_ifaceAgp_globals_clientC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B025D_kit9agree_subC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes4prod01C47Corelib4Init5Logic7f_equalC47Corelib4Init5Logic6eq_indI47Corelib4Init5Logic5False00C69OSSVerify5KrLib2K53B02=RT_gaps_iface<LEPT_GLOBALSC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2K53B028Lept_env<static_agreeC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B025D_kitArw_cells_agree_nwC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B028RT_iface3rtsC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B028RT_iface3ARTC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitions;bv_unsignedC69OSSVerify5KrLib2K53B02=RT_gaps_iface;gp_ssp_keepC1?~~~~~~~~~~~~~~~".
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
Lemma LIB0_write : forall (m : mem) a bs (n : Z), Z.of_nat (length bs) = n -> 0 <= a -> a + n <= 2^64 ->
  LIB0 m -> (a + n <= 0x10f180 \/ 0x10f1e8 <= a) -> LIB0 (write_to_mem m (wa a) bs).
Proof.
ltac2:(KReplay.run1 (kr_t_Lept_env ()) [] "h06__sat5h14__x1h24__x2h32Hah47__arithh54__ffh66__sat4h78__varmaph85__with94cstrh:1xh;1Hh<1mh=1nh>2H1h?2H2h@2H3hA2HdhB2HlhC2HnhD1ahE2bshF1yp;1p;2p;3p;4p;6p;<p;Bp;7p;8g0000j12Tg000Uj1_Tg0013j1XTg001Vj1|Tg0028j1^Tg002Xj2\Tg0038R0j19Tg003Xj3YTg0042R1j20Tg004Nj15Tg004lj2dTg005Ij1GTg006Dj1ATg006ij2QTg007Oj1sTg008Gj1]Tg008gj3OTg009Gj4=Tg00:@j1[Tg00;8R2j2RTg00;SR3j21Tg00<0j1MTg00<bj3LTg00=fj17Tg00>Ej2:Tg00>_j1cTg00?=j4bTg00?`j2@Tg00@:j3UTg00@`j6TTg00AHj1{Tg00Amj2zTg00BUj2`Tg00C1j3yTg00CUj2xTg00D6j2wTg00DTj1rTg00E2j4qTg00EPj1pTg00Enj1oTg00FYj2WTg00G<j3DTg00G_j1nTg00HAj2mTg00Hcj2lTg00IOj3kTg00Inj4jTg00J`j4STg00KKj1JTg00LGl<PTg00MMj4ZTg00Mhl<iTg00NMlBhTg00O3l<gTg00OXj2tTg00P;j4fTg00Pfj7uTg00QJj7vTg00Qnj8eTf0R4#2#2p=6f2R5f1R6'1/04p=ag00RRR7P6g00SJP4C=p=FP7P6g00TLP4C=p=H%24#2#2#2p=>%A4#Ap=3%24#Ap=C%A4#2p=B1056/:4p=4g00UPR8/@4p=8g00UnR9P8P8P8P0P0f5R0f4R:f3R;P5P6P4M<ip=VP8P8P8P8P8P8P3P4P6P5P3P;P:P0f6R3f7R<f8R=f9R>MBhp=IP8P8P1P<P1P3P0P:P;P5P6P4M<gp=K1t84p=?P8P6g00VMP4Cfp=<P6g00W4R1g00WSR?P?g00X3R@P4g00XSFup=;P5P1P?P?P@P6P4Fvp=EP;P1P?P?P@P5P6P4Gep=Ng00Y3R1#2RA#2RB#2RC#2#6RD#_RE#X%_C#XRF#|[%^F1\F6#9=Y84g00YXRG/0;%5AR;%5DRD'dRH9a:5%G3P2P7P<g00Z6R:g00[>RI%A1#5,QE#s%]IRJ3ORKC=g00\6,QE#[=OIJRL,F<g00]3,QE#[=OIJRJ,H<'R11<0%>1#3#3#6#C#B#6#>#5RI%>1#3#3#6#C#3#B#B#6#5RE/0<34%M==L><#G[P4P7P>P:PKC=f:R:/FL1H:J'RP2f;R2/FL1H2J112>10E274If=R>f<R<#M;L2#G[P41F>Lf>R=/HJ11=<10E=74IP7f@RMf?RN#M;L=ROPIPKC=P7PO%>1#3#3#6#C#3#6#>#5RPPLC=RQP7PO%>1#3#3#6#C#3#B#>#5RRPJC=RS'RP7PMPIPKPNP=P>P<P2P:P3g00]n#7#7#7#7R3#9RT,1IRU/0NRV11N>RW/0IRX':%5BRB,1IRY/0NRZ/:XPVPXPZPXP4X:8RZ1064#cXF8X:8RVPUPYPZPZPZP8P8g00^M1164Cb#8X<8X=8RUPIPI%8IPTPBPZPZ%94#8X:9R9P3PB%8BEVM:IPNPN%8NRTGKp-0R[/@X9UXXET1\F=RF#{R\%9F,0GRF1z;DR]1`G;R^10GD1`GH[R_[R`10G;Rag00_1RbAy;D6UW3RD10GH\b^3aRaP6g00_M1xG;'@P^eO1R^P_g00`3R;#]Rb%^;R;P81w85P6%r8CqRH%p8Rc%o8Rd1W81R11W8A5D8RA%?IRe'<,;dRf%?E/<1,;d5EdRg%n?R?%?B9D8e/<1,;d=EdfCN1md@R@P4P5g00`_Rfg00a?Re'@1l45=YfedAk8G6CjRGb5b7b8X18X28114610E474IRE1165Re/0I94Y6[^18^28P4fBfDP0O3R0b4b0b6b0b9CS%JK#9,1I?4NXeM<PPQPSP7PMPPPLPNP=P>P<P2P:P5%73#7#7#7R3#9R5,1PRS/0NRQ10WPRX':%5CRC,1PRI/0NRK/:XPQPXPKPXPZPVPSPIPZPZPZPUPPPP%8PP5PCPZPZP9P3PC%8CEVR3M:IPNPNPTGK1@[X9UXXETP\PFP]P`PDPaP^P_PbP;PHPcPdPgP?%?PR9%?CRS5D8/<1,;d1<A9,;d5EdCNP@PGb5b7b8X18X2810eP94I6\E^18^28P0b4b0b6b0b9CS%JL#9,1P?4NXeM<PP7PMPRPJPNP=P>P<P2P:P611R5R:/0NR210WRRW':11RCR</0NR>/:WP2PWP>PWPZPVP:P<PZPZPZPUPRPR%8RP5PCP3M:IPNPNPTGK1@[W9UWWETP\PFP]P`PDPaP^P_PbP;PHPcPdPgP?%?RR?=D8S/<1,;d1<A?,;d5EdCNP@PGb5b7b8X18X2810eR94<6\E^18^28P0b4b0b6b0b9CS%JJ#9,1R?4NWeM<PCZCZ%GOeWAW@W?P6P4O2n2001000000121000000W;W>P6P4O2n2001000000121000000W;WBW3WCX=8WEXD8W<o"). Qed.
Lemma LIBH_write : forall (m : mem) a bs (n : Z), Z.of_nat (length bs) = n -> 0 <= a -> a + n <= 2^64 ->
  LIBH m -> (a + n <= 0x10f180 \/ 0x10f1e8 <= a) -> LIBH (write_to_mem m (wa a) bs).
Proof.
ltac2:(KReplay.run1 (kr_t_Lept_env ()) [] "h02Hah11xh26__sat3h34__x1h44__x2h51mh61nh71Hh82H0h92H1h:2Hdh;2Hlh<2Hnh=7__arithh>4__ffh?6__sat2h@8__varmaphA5__withB1ahC2bshD4cstrhE1yp;1p;2p;3p;9p;4p;<p;6p;8p;Bp;7g0000j18Tg000Uj1FTg0013j1CTg001Vj1tTg0028j1KTg002Xj2MTg0038R0j1:Tg003Xj3GTg0042R1j20Tg00;SR2j22Tg004Nj17Tg004lj2OTg00a_j1NTg005Ij1ATg006ij2kTg00:@j1hTg008Gj1ITg008gj3aTg00>Ej26Tg00<0j1ETg00<bj3DTg00bZl9ZTg00=fj13Tg00>_j1YTg00?=j4XTg00?`j24Tg00O3l<UTg00@:j3STg00@`j6RTg00AHj1PTg00Amj2QTg00BUj2BTg00C1j3TTg00CUj2sTg00D6j2rTg00DTj1qTg00E2j4pTg00EPj1oTg00Enj1nTg00FYj2LTg00G<j3HTg00OXj2=Tg00G_j1gTg00Qnj8fTg00HAj2eTg00Hcj2bTg00IOj3cTg00Inj4dTg00J`j4`Tg00KKj1_Tg00LGl<iTg00MMj4^Tg009Gj4jTg006Dj1<Tg00Mhl<]Tg00NMlBlTg00P;j4mTg00Pfj7\Tg00QJj7[Tf0R3#8#8p=1g00RRR4f1R5g00cYP3Cjp=@%<3#<p=5%83#<p=?%<3#8p=9g00UnR6g00UPR7P7P7P0P0f5R0f4R8f3R9f2R:P5P3M<]p=WP7P7P7P7P7P7P2P3P5P:P2P9P8P0f6R2f7R;f8R<f9R=MBlp=VP7P5g00VMP3Cmp=;P5g00W4R>g00WSR?P?g00X3R@P3g00XSF\p=>P:P>P?P?P@P5P3F[p=Jg00Y3RA#8RB#1RC#8#1RD#FRE#C%FC#CRF#t[%KF1MF5#:=G73g00YXRG/09128:%7BR8%7DRD'OR9'0%N2g00;8%A;g00[>RHg00d`,kE#h%IH3aRH,@;12;0%1A#1#5#5#1#?#9#1#1#1#7RE'0%1A#1#5#5#1#?#5#9#9#1#7RI/0;'6%E<=D=;#N[P3%A=f:RJ/@H12J</0E10IJ'6f<RKf;RL#E;DJRM#A1@MHRMPKPLPJP=P<P;P2P:P3M9ZP4PK%1A#1#5#5#1#?#9#9#1#1#7RKPHPLPJP=P<P;P2P5g00]n#3#3#3#3#3#3#3#3R2#:R;,2KR</0LR412L=/0KR='6%7CRC,2KRN/0LRO/6=P4P=POP=P7P7P1P3X17ROP11053#YXE7X17P<PNPOPOPOP7P7g00^M1253CX,47X57X67PKPK147KP;PCPOPO%:3,47X16P2PC147CEWM:VPLPL147LM<Up-0/4=9S==ER1MFJRJ#P%:J,0G1Q8D1BG8RJ10GD1BG9[RF[10G8R2g00_1R6AT8D5UW010G9\6^02P5g00_M1sG8'4PJeO1PFg00`3RF#I%KFP71r7:P5%q7Cp%o7%n7RFP>P?P?P@1L7ARA1L7B5H7RB1=7E';,>F1=7I/;A,>F5JF%g?1=7KR?1=7C5H7/;A,>F1;B?,>F5JFGf1eF@P3P:g00`_RFg00a?R@'41b3:=GF@dAc7G5Cdb>b@bAX37X471235/0E10I3'610N5125:/0K'6[^37^47P3f>f@P0O3b=b2b?b2bDC`%_H#:,2K/0L/6=eM<iPMeC^W:W9W8P5P3O2n2001000000121000000W7W;W0W<X67WCXB7W5o"). Qed.
(* [comment removed for export] *)
Lemma io_ssp_write : forall (m : mem) a bs (n : Z), Z.of_nat (length bs) = n -> 0 <= a -> a + n <= 2^64 ->
  io_ssp m -> (a + n <= 0x10000 \/ SEGTOP_A <= a \/ (0x10f180 <= a /\ a + n <= 0x10f1e8)) -> io_ssp (write_to_mem m (wa a) bs).
Proof.
ltac2:(KReplay.run1 (kr_t_Lept_env ()) [] "p'0h04__p1h16__sat4h24__x1h34__x2h42Hah51gh61xi001xh71Hh87__arithh94__ffh:6__sat3h;8__varmaph<5__with=4cstrh>1mh?1nh@2H1hA2H2hB2HdhC2HlhD2HnhE1ahF2bshG1yp;1p;2p;3p;4p;6p;<p;Bp;7p;8g0000j18Tg000Uj1ZTg0013j1NTg001Vj1|Tg0028j1XTg002Xj2UTg0038R0j1ATg003Xj3OTg0042R1j20Tg00;SR2j21Tg004Nj1:Tg004lj2^Tg00e`j1JTg006ij2oTg00:@j1CTg008Gj1TTg008gj3BTg00;8R3j2=Tg00<0j1HTg00<bj3GTg00=fj1<Tg00>Ej29Tg00>_j1aTg00?=j4`Tg00?`j2DTg00@:j3RTg00@`j6KTg00AHj1]Tg00Amj2\Tg00BUj2[Tg00C1j3{Tg00CUj2zTg00D6j2yTg00DTj1xTg00E2j4wTg00EPj1rTg00Enj1qTg00FYj2YTg00G<j3ITg00f[j6pTg00G_j1nTg00HAj2mTg00Hcj2kTg00IOj3jTg00Inj4iTg00J`j4STg00KKj1PTg00g?l<QTg00MMj4hTg00hEj4lTg006Dj1FTg00h_j4gTg00Mhl<fTg00NMlBeTg00O3l<dTg00OXj2sTg00P;j4tTg00Pfj7cTg00iXj7uTg00QJj7vTg00Qnj8bTf0R4#8#8p=5%84#8#8#8p=6%F4#8p=3%F4#Fp=2%84#Fp=Eg00RRR5f2R6f1R7P4Cgp=41067/94p=7g00UPR8/D4p=?g00UnR9P8P8P8P0P0f5R0f4R:f3R;P6P7P4M<fp=_P8P8P8P8P8P8P2P4P7P6P2P;P:P0f6R2f7R<f8R=f9R>MBep=MP8P8P1P<P1P2P0P:P;P6P7P4M<dp=L1s84p=>P6g00W4R1g00WSR?P?g00X3R@P8P7g00VMP4Ctg00XSFcp=;P6P1P?P?P@P7P4Fup=WP6P1P?P?P@P7P4Fvp=@P;P1P?P?P@P6P7P4Gbp=Vg00Y3RA#8RB#5RC#8#5RD#ZRE#NRF%ZC#NRG#|[%XG1UG7#A=O84g00YXRH/0;11:6%:BR;%:DRI'^RJ'0%J2g00j<PF%6A#3#2#3#6#2#3#5#:RKg00[>RL%3A#E#3#2#5#2#2#3#5#3#5#:RM,oE#C%TLRE3BRN54=%C4=BLERO94=M'=X5F11<0RP%5D#6#6#:RDg00jVRQ%6A#2#2#5#E#3#5#6#:RR/0<%6A#2#2#5#E#2#3#3#5#:RS,0P'=77<37%H==G><#J[P4f:R<?4KNA4<MO'=P3f;R3?4KN%C7=BLE943M113>R>10R310>S'=97Q377Df=R>f<R=#H;G3#J[P4A4>KNf>RP%C:=BLE74M11P=RT10RP10TS'=97QP77DPFfAf@RQ#Hf?RT3GRU?4KNA4UMO'=X5FP2%HT=GQPRU?4KN%C2=BLERE94UMP5PQPKPNPTPPP>P=P3P<P6g00]n#<#<#<#<#<#<#<#<RU#ARL,1KR2/0TRO11T>RV/0KRW'9%:CRC,1KRX/0TRY/9WPOPWPYPWP4X68RY1074#aXG8X68ROP2PXPYPYPYP8P8g00^M1174C`#?X>8X?8R2PKPK%?KPLPCPYPY%A4#?X69PUPC%?CE_RUM:MPTPT%?TR9GLp-0RZ/DW9RWWEK1UGPRG#]R[%AG,0HRG1\;IR\1[H;R]10HI1[HJ[R^[R_10H;R`g00_1RaA{;I7UW4RI10HJ\a^4`R`P7g00_M1zH;'DP]eO1R]P^g00`3R;#TRa%X;R;P81y86P7%x8CwRJ%r8Rb%q8Rc1Y8ARd1Y8B5I8RB%>D5;cRe%3A#E#3#2#2#6#6#6#:RA#>=;cdRf%>R=;cdPcP1P?P?P@P:EpR:5Wc5@c5@c%n?R?%>KR1%>CRg5I8=;cdA;cB15@cCV1mc@R@P4P6g00`_R1g00a?Rh'D1k46=O1hdAj8H7CiRHb9b;b<X28X38X0Z1147Rh/0DRD10A4RA10R4/=6'9'91176R1/0K97X7[^28^38^0ZP4fDRXfBRi'1/0SPiPXP0O4b8b1b:b1b=CS%PN#A,1K?7TWeM<QP5PQPMPEPTPPP>P=P3P<P711MLR</0TR310VMRV'911MCR=/0TR>/9VP3PVP>PVPYPOP<P=PYPYPYP2PMPM%?MPLPCPUM:MPTPTP9GL1DZV9RVVEKP[PGP\P_PIP`P]P^PaP;PJPbPc%>S9;cB9Wc:9@cf9@ceP?%>MR?=I8g=;cdA;cB?5@cCVP@PHb9b;b<X28X38X0Z10hS,=6,9A,9D101M97=7[^28^38^0ZP410RXPiPXP0O4b8b1b:b1b=CS%PE#A,1M?7TVeM<QChClWBWAW@P7P4O2n2001000000121000000W7X5FP7P4O2n2001000000121100000W7WCW4WDX?8WFXE8W>o"). Qed.

Ltac lept_transport_extra3 m a bs n Hn Ha Hl :=
  lept_transport_extra2 m a bs n Hn Ha Hl;
  repeat match goal with
  | H : LIBH m |- _ =>
      first [ apply (LIBH_write m a bs n Hn Ha Hl) in H; [ | tlia ]
            | idtac "note: dropping LIBH (store may hit the library statics)"; clear H ]
  | H : io_ssp m |- _ =>
      first [ apply (io_ssp_write m a bs n Hn Ha Hl) in H; [ | unfold SEGTOP_A; tlia ]
            | idtac "note: dropping io_ssp"; clear H ]
  end.
Ltac transport_chunks_extra m a bs n Hn Ha Hl ::= lept_transport_extra3 m a bs n Hn Ha Hl.

(* [comment removed for export] *)
Section Env.
Variable RT : rt_sig.
Hypothesis GP : rt_gaps RT.

Lemma static_agree : forall (P : Z -> Prop) (m m' : mem), agree_on P m m' -> (forall a, client_static a -> P a) ->
  forall lo n, In (lo, n) LEPT_GLOBALS -> agree_on (fun x => lo <= x < lo + n) m m'.
Proof using GP.
ltac2:(KReplay.run1 (kr_t_Lept_env ()) ["Env"] "p'0h01Hh12Hxh22loh33Hinh41nh51Eh62H0h71xh81eh92hih:2AGh;2HPh<1Ph=1ah>1mh?2m'h@1ri001pi011zp;1p;3p;2p;4p;5p;6p;7g0000j19Tg000Uj1PTg0013j1OTg001Vj1aTg00kSj3[Tg00lMj1XTg00mOR0j2WTg00moj3ETg00nFj3VTg00ncj3UTg00o@j4RTg00BUj23Tg00;8j2FTg00j<j2YTg00;Sj28Tg004Nj1DTg003Xj30Tg0042j2BTg00>ER1j26Tg00?`j2GTg00o\j3MTg0106j5LTg010Sj3ATg008Gj1`Tg008gj3NTg00MMj4_Tg00hEj4STg010mj4^Tg0128j6]Tg0133j4QTg006Dj1KTg013Sj6\Tg0140j7ZTf0R2#9#9p=>g00UPR3P3f1R4P2CQp=1f4R5f3R6'Bf2R71842'3'Fp=;P3P3P71842CQp=71B74/F2p=@%92#9#9#9p=<%K2#Kp=:%92#Kp=J%K2#9p=IA0742g014LR8'6p=Cf6R9f5R:;05A0674/62'6p=4A0:56A0742/68'6p=5P5P3P6P7P4P2E\p==A0342p=21342,F7p=HP3P:P5P6P7P4P2FZp=?1628p=Tp-0\3g00Y3R;#>R<#9R=#9#>#P#O%P=#O#a[R>A[742%X2P:P4O1[^=31W33R?1142R@g014iRA3Ef7RBP6P2P2P6P7D;RCX73P9P:P5P:P4p,2RTp,2GPP4P3P?P?AV332RDAU33277DX@?RDPACRRA9E?@13629@46'FX93,Y3X23P5P311:2=E?A13729@:7'FX931856R@115@RE=E?ARA134@9@54P1%<;#:#:#>#J#I#>#<#DR@%D<R<'1RF1156R650?P?%<;#:#:#>#J#I#I#<#DRG%D=R='1RHP6P?%<;#:#:#>#J#:#>#<#DRI/1=RJP6%<;#:#:#>#J#:#I#<#DR;/1=RK=C?6F4P?18@<R6,1@RLA7::5RMP?18G=RN,1GROPMP?18I=RP,1IRQPMP?18;=RR,1;RSPME5F4P711:5R590?FP?P0P3P3P3P2P2n2001100000120101101X8?RMPF119:RTP2D=12<:P?P0P3P3P3P2P4n2001100000120101101X8?R0PF11B9RUP4D=12@Bf8RV,2@P@P2PBPBP2f9RWD;f:RX,2<P?PLf;RY9777RZP?POPZP?PQPZP?PSPZE5F4[]1X23P@P9P9P@PVD;12<WP<1B@WR<18@27HWP?PLA7@@4RZP?POPZP?PQPZP?PSPZE5F4]1X4313V69@@VP<13W6A0?LLR@P?POPLP?PQPLAC?SLF4RZ'613X61G?L9M@ZW6X0<P2DLW1PXP2P4E?W0W1PWP2P:E?W0P2O1b0P2O1b0W5P2O1P?PHP5P?PJP5AC?K5F4P1A0?HTP?PJPTP?PKPTE5P?PLA7BB9R9P?POP9P?PQP9P?PSP9E5F4P2A0?HUP?PMPH11VBR9P2D=12=BP?P0PH11WVRTP4D=12GW12GXPGP2PWPWP2PYD;f<R5,2=P?PLf=R:9777R<P?POP<P?PQP<P?PSP<E5F4[]1X23PGPVPVPGPXD;12=YR<P=1BGYRZ18G27HYP?PLA7GG4R@P?POP@P?PQP@P?PSP@E5F4]1X4313XN9@GXPZ13YNA0?LORGA0?OOR@P?PQPOP?PSPOE5R6'6R['6135N1G?O9M@69AG[W6X0ZP2DLW1P5P2P4E?W0W1PYP2PBE?W0P2O1b0P2O1b0W5P2O1P?PJPUP?PKPUE5P1A0?J9AC?K9P?PLA7WWVRVP?POPVP?PQPVP?PSPVE5F4P2A0?JTP?PMPJ11XWRVP2D=12=WP?P0PJ11YXR9P4D=12IY12I5PIP2PYPYP2P:D;f>RU,2=P?PLf?RB9777RZP?POPZP?PQPZP?PSPZE5F4[]1X23PIPXPXPIP5D;12=:P=1BI:RZ18I27H:P?PLA7II4R[P?POP[P?PQP[P?PSP[E5F4]1X43135P9@I5PZ13:PA0?LQRIA0?OQR[A0?QQRGAC?SQR6'6R@'6RN'613UP1G?Q9MG69A[@9AINW6X0ZP2DLW1PUP2P4E?W0W1P:P2PWE?W0P2O1b0P2O1b0W5P2O1AC?KTP1A0?KVP8P?PLA7YYXRXP?POPXP?PQPXP?PSPXE5F4P2A0?K9P?PMPK115YP2D=P<P?P0PK11:5P4D=12;:12;UP;P2P:P:P2PBD;f@R0,2=P?PLfA9777R7P?POP7P?PQP7P?PSP7E5F4[]1X23P;P5P5P;PUD;12=BP=1B;BR=18;27HBP?PLA7;;4R7P?POP7P?PQP7P?PSP7E5F4]1X4313UR9@;UP=13BRA0?LSRUA0?OSR;A0?QSR7A0?SSR<#TRM'6R9'6RX'6130R1G?S9M<89A7M9A;99AUXW6X0=P2DLW1P0P2P4E?W0W1PBP2PYE?W0P2O1b0P2O1b0W5P2O1P8P?PLA7::5R:P?POP:P?PQP:P?PSP:E5F4P2n010000100X38P2O1n200100001021100011000W3P2O1n200100001021100011000W3P2O1n200100001021100011000W3P2O1n200100001021100011000P?P?PD%`?9N?K9N?J9N?H9N?FCR9E?EePAeP2C_CSCSC^O2X1CX73PWP4O1\C^73eE]W3X43X23W;W:X?>W>W<o"). Qed.

Lemma LIBH_agree : forall (P : Z -> Prop) (m m' : mem), LIBH m -> agree_on P m m' -> (forall a, client_static a -> P a) -> LIBH m'.
Proof using GP.
ltac2:(KReplay.run1 (kr_t_Lept_env ()) ["Env"] "h01ah11Hh22AGh32H1h42H2h52H3h62H4h72HPh81Ph91mh:2m'p;1p;2p;3p;4p;8p;7g0000j13Tg000Uj1MTg0013j1LTg001Vj1TTg00a_j19Tg005Ij1NTg006ij2ATg00:@j1JTg008Gj1PTg008gj3=Tg00kSj3;Tg00lMj1STg006Dj1:Tg004Nj17Tg007Oj1RTg009Gj44Tg00;8R0j2BTg00mOj2QTg003Xj30Tg00>Ej21Tg00?`j2>Tg00o\j3FTg00moj3CTg015oj8<Tg0170j7?Tg010Sj38Tg00MMj4KTg0133j4OTf0R1#3#3p=6g00RRR2f1R3g00cYP1C4p=HP2P3g00SJP1C4p=IP2P3g00TLP1C4p=D%31#3#3#3p=5%:1#:p=2%31#:p=@%:1#3p=Eg00UPR4P4P3P1COp=Gp-0\4g00Y3R5#6R6#3R7#3#6#MR8#L%M7#L#T[R9%93P0f2R:#Ng00[>R;g00d`,A8#J%P;R<3=R=,H:f4R>f3R?;;:%S1R@f7RAP3O1[^04%9>[[P1%N>P0P2f5RBg00Z6RC%:5#7,A8#R==;<RDC4g00\6,A8#J==;<RE,IBg00]3,A8#J==;<R<,DB'Bf6RB/H=f8R;?;ABf;RBP3O1\@^04%9;[[[P1P2PAPCPDC41I;E1D;<'BP0f9R0/IE1D0<f:R0/H=f<RC?;B0f?R0P3O1\@^04%9C[[[P11IBE1DC<f=RC/H=f>=;0CfBP3O1\@^04P2P0%55#2#2#6#@#E#6#5#7R@PDC4RCP2P0%55#2#2#6#@#2#6#5#7RBPEC4RAP2P0%55#2#2#6#@#2#E#5#7R8P<C4RF'BRG'BP2P0%55#2#2#6#@#E#E#5#7R5P=C4PCPGP2f@RGP0P@PDP;fAR;PGP0P3P1P@%76R61Q44R41G@6R6;06%77R7,G5R@=0461GB7RD=0461G87RC=046g014LRH'1'1'11>463Fg014iRI9C46eG<F?PAPFP2PGP0PBPEP>P;PGP0P3P1PBP7A046DA04@DRBA04DDR>A04CD/1HRE'1RF'11>4D9F>E98BF38AC4DIeG<F?P2PGP0P8P<P?P;PGP0P3P1P8P7A046CA04@CR8A04DCR?A04CCR</1HRF'1RB'11>4C9F<H98?F988B38AC4CIeG<F?CKCKP2PGP0P5P=P:P;PGP0P3P1P5P7A046@A04@@R6A04D@A04C@/1H'1RH'11>4@9F6H38AC4@IeG<F?CK%90eW7W2W6W5W4P3P1O2n2001000000121000000W1W3P3P1O2n2001000000121000000W1P3P1O2n2001000000121000000W1X:9W9W8o"). Qed.

Lemma io_ssp_agree : forall (P : Z -> Prop) Σ' (m m' : mem), io_ssp m -> ART RT Σ' m' -> agree_on P m m' ->
  (forall a, client_static a -> P a) -> io_ssp m'.
Proof using GP.
ltac2:(KReplay.run1 (kr_t_Lept_env ()) ["Env"] "h01ah12AGh21Hh32HAh42HPh52Hah61Ph71mh82m'h93Σ'p;1p;3p;2p;8g0183j1:Tg0000j10Tg000Uj12Tg0013j14Tg001Vj19Tg00e`j18Tg018kj37Tg00kSj36Tg00lMj13Tg019cj21Tg01:Mj85Tg00UPR0p-0[p,2RTR1#:g00Y3#0#0#0R2#0#0#0#2R3#4R4%22#4#9[R2f1R5#8f3R6=715f5R7f2R8766f0R9#3f8P5O1[^00P1p,2GPf6P7f4P6P81139#3P6P5P81135P9O2O2W5X04G5W4W1W3W2X82W7W9W6o"). Qed.
End Env.

(* [comment removed for export] *)
Ltac static_in_P :=
  let a := fresh "a" in let Ha := fresh "Ha" in intros a Ha;
  first [ right; left; exact Ha
        | split; [ right; left; exact Ha
                 | first [ cbn [outside]; exact I
                         | let Hc := fresh in intros Hc;
                           pose proof (client_static_below a Ha); pose proof (client_static_ge a Ha); unfold SEGTOP_A in *; first [ lia | tlia ]
                         | cbn [outside]; pose proof (client_static_below a Ha); pose proof (client_static_ge a Ha);
                           unfold SEGTOP_A in *; repeat split; tlia ] ] ].

Ltac lept_rt_transport_extra m m' AG :=
  repeat match goal with
  | H : LIBH m |- _ =>
      first [ lazymatch goal with _ : LIBH m' |- _ => clear H end
            | match goal with GP : rt_gaps ?RT |- _ => apply (fun h => LIBH_agree RT GP _ m m' h AG ltac:(static_in_P)) in H end
            | idtac "note: dropping LIBH at a runtime call"; clear H ]
  | H : io_ssp m |- _ =>
      first [ lazymatch goal with _ : io_ssp m' |- _ => clear H end
            | match goal with GP : rt_gaps ?RT, A : ART ?RT ?S m' |- _ =>
                apply (fun h => io_ssp_agree RT GP _ S m m' h A AG ltac:(static_in_P)) in H end
            | idtac "note: dropping io_ssp at a runtime call"; clear H ]
  end.
Ltac rt_transport_extra m m' AG ::= lept_rt_transport_extra m m' AG.

(* [comment removed for export] *)
Ltac lib_load_step :=
  next_instr ltac:(fun i =>
    lazymatch i with
    | Load _ _ _ ?rs ?imm =>
        reg_val rs ltac:(fun v =>
          lazymatch v with
          | Z_to_bv 64 ?E =>
              is_Zlit E;
              let a := eval vm_compute in (E + bv_signed imm)%Z in
              let inb := eval vm_compute in (existsb (fun r => (fst r <=? a) && (a <? fst r + snd r))%Z LEPT_GLOBALS) in
              lazymatch inb with
              | true =>
                  lazymatch goal with
                  | LH : LIBH ?m |- _ =>
                      let C1 := fresh "LC" in let C2 := fresh "LC" in let C3 := fresh "LC" in let C4 := fresh "LC" in
                      pose proof LH as ((C1 & C2 & C3) & C4);
                      unfold g_LeptMsgSeverity, g_pix_alloc, g_pix_dealloc, g_stderr_handler, e_devnull, e_malloc, e_free in C1, C2, C3, C4;
                      lstep; clear C1 C2 C3 C4
                  end
              end
          end)
    end).
Ltac special_step ::= lib_load_step.

(* [comment removed for export] *)
Ltac lib_refresh RT GP :=
  lazymatch goal with
  | |- cps _ (ASTA RT ?S _ (eq (MS _ _ _ _ _ ?m' _))) _ =>
      lazymatch goal with
      | A : ART RT S m' |- _ =>
          let G := fresh "GSEV" in
          pose proof (gp_got_lib RT GP S m' A) as G; unfold g_GOT_LeptMsgSeverity in G;
          let AG := fresh "ACCG" in
          pose proof (gp_acc_globals RT GP S m' A) as AG; unfold LEPT_GLOBALS in AG;
          apply Forall_inv in AG; cbn [fst snd] in AG
      end
  end.

(* [comment removed for export] *)
Ltac lit_in := eexists; unfold LEPT_LITS; repeat first [ left; reflexivity | right ].
Ltac lenv_tac :=
  unfold lenv, LSTK, STDERR_STACK; rewrite ?unsigned_lit by lia;
  split; [assumption|]; split; [assumption|]; split; [assumption|]; split; [assumption|]; split; [assumption|];
  repeat match goal with H : rt_sp0 _ _ = _ |- _ => rewrite H end;
  repeat split; ul.
Ltac lres_tac :=
  unfold lres; repeat match goal with H : rt_frames _ _ = _ |- _ => rewrite H end;
  repeat match goal with H : rt_live _ _ = _ |- _ => rewrite H end;
  cbn [length]; unfold FRAMES_MAX, LIVE_MAX in *;
  repeat lazymatch goal with |- _ /\ _ => split end;
  lazymatch goal with
  | |- forall p n, In _ _ -> _ =>
      let p := fresh "p" in let n := fresh "n" in let H := fresh "H" in intros p n H; cbn [In] in H;
      repeat (destruct H as [H|H]; [injection H as <- <-; lia|]); eauto
  | |- _ => first [ lia | assumption
                  | unfold mcost in *; repeat match goal with _ : context [if ?c then _ else _] |- _ => destruct c end; lia ]
  end.
(* [comment removed for export] *)
Ltac alg_tac :=
  repeat match goal with H : rt_live _ _ = _ |- _ => rewrite H end;
  repeat match goal with H : rt_frames _ _ = _ |- _ => rewrite H end;
  repeat match goal with H : rt_sp0 _ _ = _ |- _ => rewrite H end;
  repeat match goal with H : rt_credit _ _ = _ |- _ => rewrite H end;
  repeat split;
  first [ reflexivity | lia | solve [auto]
        | unfold mcost in *; repeat match goal with _ : context [if ?c then _ else _] |- _ => destruct c end;
          repeat match goal with |- context [if ?c then _ else _] => destruct c end; lia
        | lazymatch goal with |- ?g => idtac "alg_tac leaves:" g end ].

Ltac after_call_unfold ::=
  unfold lpost, lpost_f, keeps, keepsL, rsize in *;
  cbn [p_w p_h p_d p_spp p_wpl p_xres p_yres p_inf p_spec p_cmap p_data c_arr c_depth c_nalloc c_n] in *.

(* [comment removed for export] *)
Ltac ul ::= unfold STDERR_STACK, LSTK in *; unfold SEGTOP_A, STACK_WIN, USTACK_TOP, RT_STACK, LIVE_MAX in *; lia.
