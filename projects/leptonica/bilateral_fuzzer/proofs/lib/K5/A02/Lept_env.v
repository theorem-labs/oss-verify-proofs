(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.K5.Lib Require Import Tac.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.K5.A02 Require Import ImageA.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.K5.Lib Require Import RzCPS StoreFast.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.K5.PG Require Import Str_tac Startup_glue.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.K5.A02 Require Import Layout.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.K5.AG Require Import Shadow.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.K5.A02 Require Import RT_iface RT_traces RT_gaps_iface LeptTac D_kit Lept_kit Lept_iface.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib Require KReplay.
Ltac2 kr_t_Lept_env () := "K47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00I47Corelib4Init9Datatypes6option00I47Corelib4Init9Datatypes4list00C47Corelib4Init9Datatypes6lengthC56Stdlib6ZArith6BinInt1Z6of_natI47Corelib4Init5Logic2eq00C56Stdlib6ZArith6BinInt1Z2leK47Corelib7Numbers7BinNums1Z02C56Stdlib6ZArith6BinInt1Z3powC69OSSVerify5KrLib2K53A02:Lept_iface4LIB0C1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive01C45stdpp9bitvector;definitions7Z_to_bvK69OSSVerify5KrLib2K53Lib5Cells4cell02C1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes4list01K47Corelib4Init9Datatypes4list02C69OSSVerify5KrLib2K53Lib4Step8rw_cellsC1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib2K53Lib5Cells4cell01C1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic3and00C56Stdlib6ZArith6BinInt1Z3addC69OSSVerify5KrLib2K53Lib3Mem2waC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics<write_to_memK47Corelib4Init9Datatypes3nat02I47Corelib4Init5Logic2or00C47Corelib4Init5Logic8iff_reflC46Stdlib9micromega;ZifyClasses3injK47Corelib4Init5Logic2eq01C46Stdlib9micromega;ZifyClasses6eq_iffC46Stdlib9micromega;ZifyClasses8or_morphC56Stdlib6ZArith4Znat5Nat2Z9is_nonnegC56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z2ltC56Stdlib6ZArith6BinInt1Z:pow_nonnegC56Stdlib6ZArith6BinInt1Z7compareK46Stdlib9micromega6VarMap1t02K46Stdlib9micromega6VarMap1t01K46Stdlib9micromega6VarMap1t03I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr02K46Stdlib9micromega7EnvRing5PExpr03K47Corelib4Init9Datatypes6option02C46Stdlib9micromega5Tauto8BFormulaC46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundC46Stdlib9micromega;ZifyClasses;rew_iff_revC69OSSVerify5KrLib2K53Lib5Cells:cells_sizeC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib9StoreFast@rw_cells_frame_nC1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic3and01C46Stdlib9micromega;ZifyClasses5mkappC46Stdlib9micromega;ZifyClasses6mkapp2C46Stdlib9micromega;ZifyClasses5mkrelK46Stdlib9micromega7EnvRing5PExpr01K46Stdlib9micromega=RingMicromega7Formula01K46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega5Tauto8GFormula06K46Stdlib9micromega5Tauto8GFormula08C69OSSVerify5KrLib2K53A026ImageA5asegsC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A02:Lept_iface;g_pix_allocC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A02:Lept_iface=g_pix_deallocC1?~~~~~~~~~~~~~~~I47Corelib7Numbers7BinNums1Z00I47Corelib4Init9Datatypes3nat00K46Stdlib9micromega=RingMicromega3Op203C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K47Corelib4Init9Datatypes4unit01K47Corelib7Numbers7BinNums8positive03K47Corelib7Numbers7BinNums1Z01C69OSSVerify5KrLib2K53A02:Lept_ifaceAg_LeptMsgSeverityC1?~~~~~~~~~~~~~~~I69OSSVerify5KrLib2K53Lib5Cells4cell00C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A028RT_iface8e_mallocC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A028RT_iface6e_freeC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes3nat01C46Stdlib9micromega8ZifyInst7Inj_Z_ZI47Corelib4Init5Logic4True00I47Corelib4Init9Datatypes:comparison00I46Stdlib9micromega:ZMicromega;ZArithProof00I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01C69OSSVerify5KrLib2K53A02:Lept_iface4LIBHC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2K53A028Lept_env:LIB0_writeC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A02:Lept_iface@g_stderr_handlerC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A02:Lept_iface9e_devnullC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A028RT_iface6io_sspC1?~~~~~~~~~~~~~~~K46Stdlib9micromega5Tauto8GFormula03C69OSSVerify5KrLib2K53Lib9StoreFast@ro_cells_frame_nC1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic2ex01C69OSSVerify5KrLib2K53Lib4Step8ro_cellsC1?~~~~~~~~~~~~~~~K46Stdlib9micromega5Tauto8GFormula05I47Corelib4Init5Logic2ex00C69OSSVerify5KrLib2K53A028RT_iface8SEGTOP_AC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A025D_kit8agree_onC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A028RT_iface=client_staticC1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes4prod00C46Stdlib5Lists4List2InC47Corelib4Init9Datatypes3fstC47Corelib4Init9Datatypes3sndC47Corelib5Lists7ListDef3mapK47Corelib4Init5Logic2or01C47Corelib4Init5Logic7and_indK47Corelib4Init5Logic2or02C69OSSVerify5KrLib2K53A02=RT_gaps_ifaceAgp_globals_clientC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A025D_kit9agree_subC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes4prod01C47Corelib4Init5Logic7f_equalC47Corelib4Init5Logic6eq_indI47Corelib4Init5Logic5False00C69OSSVerify5KrLib2K53A02=RT_gaps_iface<LEPT_GLOBALSC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2K53A028Lept_env<static_agreeC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A025D_kitArw_cells_agree_nwC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A028RT_iface3rtsC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A028RT_iface3ARTC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitions;bv_unsignedC69OSSVerify5KrLib2K53A02=RT_gaps_iface;gp_ssp_keepC1?~~~~~~~~~~~~~~~".
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
Lemma LIB0_write : forall (m : mem) a bs (n : Z), Z.of_nat (length bs) = n -> 0 <= a -> a + n <= 2^64 ->
  LIB0 m -> (a + n <= 0x102120 \/ 0x102188 <= a) -> LIB0 (write_to_mem m (wa a) bs).
Proof.
ltac2:(KReplay.run1 (kr_t_Lept_env ()) [] "h06__sat5h14__x1h24__x2h32Hah47__arithh54__ffh66__sat4h78__varmaph85__with94cstrh:1xh;1Hh<1mh=1nh>2H1h?2H2h@2H3hA2HdhB2HlhC2HnhD1ahE2bshF1yp;1p;2p;3p;4p;6p;<p;Bp;7p;8g0000j12Tg000Uj1_Tg0013j1WTg001Vj1|Tg0028j1^Tg002Xj2\Tg0038R0j17Tg003Xj3YTg0042R1j20Tg004Nj14Tg004lj2dTg005Ij1BTg006Dj1CTg006ij2PTg007Oj1sTg008Gj1]Tg008gj3NTg009Gj4<Tg00:@j1[Tg00;8R2j2QTg00;SR3j21Tg00<0j1LTg00<bj3KTg00=fj16Tg00>Ej28Tg00>_j1cTg00?=j4bTg00?`j2@Tg00@:j3TTg00@`j6STg00AHj1{Tg00Amj2zTg00BUj2`Tg00C1j3yTg00CUj2xTg00D6j2wTg00DTj1rTg00E2j4qTg00EPj1pTg00Enj1oTg00FYj2VTg00G<j3DTg00G_j1nTg00HAj2mTg00Hcj2lTg00IOj3kTg00Inj4jTg00J`j4RTg00KKj1ITg00LGl<OTg00MMj4ZTg00Mhl<iTg00NMlBhTg00O3l<gTg00OXj2tTg00P;j4fTg00Pfj7uTg00QJj7vTg00Qnj8eTf0R4#2#2p=?f2R5f1R6'1/04p=ag00RRR7P6g00SJP4C<p=FP7P6g00TLP4C<p=G%24#2#2#2p==%C4#2#2#2p=9%24#Cp=A%C4#2p=X1056/84p=3g00UPR8/@4p=5g00UnR9P8P8P8P0P0f5R0f4R:f3R;P5P6P4M<ip=UP8P8P8P8P8P8P3P4P6P5P3P;P:P0f6R3f7R<f8R=f9R>MBhp=HP8P8P1P<P1P3P0P:P;P5P6P4M<gp=J1t84p=>P8P6g00VMP4Cfp=;P6g00W4R1g00WSR?P?g00X3R@P4g00XSFup=:P5P1P?P?P@P6P4Fvp=EP;P1P?P?P@P5P6P4Gep=Mg00Y3R1#2RA#2RB#2RC#2#?RD#_RE#W%_C#WRF#|[%^F1\F6#7=Y84g00YXRG/0;%4AR;%4DRD'dRH9a:5%B3P2P7P<g00Z6R:g00[>RI%C1#4,PE#s%]IRJ3NRKC<g00\6,PE#[=NIJRL,F<g00]3,PE#[=NIJRJ,G<'Q11<0%?1#=#9#A#?#X#=#4RI%?1#=#9#A#9#9#4RE/0<33%L==K><#B[P4P7P>P:PKC<f:R:/FL1G:J'QP2f;R2/FL1G2J112>10E273If=R>f<R<#L;K2#B[P41F>Lf>R=/GJ11=<10E=73IP7f@RMf?RN#L;K=ROPIPKC<P7PO%?1#=#9#A#A#X#=#4RPPLC<RQP7PO%?1#=#9#A#9#=#4RRPJC<RS'QP7PMPIPKPNP=P>P<P2P:P3g00]n#6#6#6#6R3#7RT,1IRU/0NRV11N>RW/0IRX'8%4BRB,1IRY/0NRZ/8XPVPXPZPXP4X:8RZ1064#cXF8X:8RVPUPYPZPZPZP8P8g00^M1164Cb#5X<8X=8RUPIPI%5IPTPBPZPZ%74#5X:9R9P3PB%5BEUM:HPNPN%5NRTGJp-0R[/@X9TXXES1\F=RF#{R\%7F,0GRF1z;DR]1`G;R^10GD1`GH[R_[R`10G;Rag00_1RbAy;D6UW3RD10GH\b^3aRaP6g00_M1xG;'@P^eO1R^P_g00`3R;#]Rb%^;R;P81w85P6%r8CqRH%p8Rc%o8Rd1V81R11V8A5D8RA%>IRe';,:dRf%>E/;1,:d5EdRg%n?R?%>B9D8e/;1,:d=EdfCM1md@R@P4P5g00`_Rfg00a?Re'@1l45=YfedAk8G6CjRGb5b7b8X18X28114610E473IRE1165Re/0I93Y6[^18^28P4fBfDP0O3R0b4b0b6b0b9CR%IK#7,1I?3NXeM<OPQPSP7PMPPPLPNP=P>P<P2P:P5%63#6#6#6R3#7R5,1PRS/0NRQ10WPRX'8%4CRC,1PRI/0NRK/8XPQPXPKPXPZPVPSPIPZPZPZPUPPPP%5PP5PCPZPZP9P3PC%5CEUR3M:HPNPNPTGJ1@[X9TXXESP\PFP]P`PDPaP^P_PbP;PHPcPdPgP?%>PR9%>CRS5D8/;1,:d1;A9,:d5EdCMP@PGb5b7b8X18X2810eP93I6\E^18^28P0b4b0b6b0b9CR%IL#7,1P?3NXeM<OP7PMPRPJPNP=P>P<P2P:P611R5R:/0NR210WRRW'811RCR</0NR>/8WP2PWP>PWPZPVP:P<PZPZPZPUPRPR%5RP5PCP3M:HPNPNPTGJ1@[W9TWWESP\PFP]P`PDPaP^P_PbP;PHPcPdPgP?%>RR?=D8S/;1,:d1;A?,:d5EdCMP@PGb5b7b8X18X2810eR93<6\E^18^28P0b4b0b6b0b9CR%IJ#7,1R?3NWeM<OCZCZ%BOeWAW@W?P6P4O2n2001000000121000000W;W>P6P4O2n2001000000121000000W;WBW3WCX=8WEXD8W<o"). Qed.
Lemma LIBH_write : forall (m : mem) a bs (n : Z), Z.of_nat (length bs) = n -> 0 <= a -> a + n <= 2^64 ->
  LIBH m -> (a + n <= 0x102120 \/ 0x102188 <= a) -> LIBH (write_to_mem m (wa a) bs).
Proof.
ltac2:(KReplay.run1 (kr_t_Lept_env ()) [] "h02Hah11xh26__sat3h34__x1h44__x2h51mh61nh71Hh82H0h92H1h:2Hdh;2Hlh<2Hnh=7__arithh>4__ffh?6__sat2h@8__varmaphA5__withB1ahC2bshD4cstrhE1yp;1p;2p;3p;9p;4p;<p;6p;8p;Bp;7g0000j13Tg000Uj1ETg0013j1BTg001Vj1tTg0028j1JTg002Xj2MTg0038R0j1:Tg003Xj3GTg0042R1j20Tg00;SR2j22Tg004Nj18Tg004lj2OTg00a_j1NTg005Ij1?Tg006ij2kTg00:@j1hTg008Gj1HTg008gj3aTg00>Ej26Tg00<0j1DTg00<bj3CTg00bZl9ZTg00=fj15Tg00>_j1YTg00?=j4XTg00?`j24Tg00O3l<UTg00@:j3STg00@`j6RTg00AHj1PTg00Amj2QTg00BUj2ATg00C1j3TTg00CUj2sTg00D6j2rTg00DTj1qTg00E2j4pTg00EPj1oTg00Enj1nTg00FYj2KTg00G<j3FTg00OXj2<Tg00G_j1gTg00Qnj8fTg00HAj2eTg00Hcj2bTg00IOj3cTg00Inj4dTg00J`j4`Tg00KKj1_Tg00LGl<iTg00MMj4^Tg009Gj4jTg006Dj1LTg00Mhl<]Tg00NMlBlTg00P;j4mTg00Pfj7\Tg00QJj7[Tf0R3#3#3p=1g00RRR4f1R5g00cYP3Cjp=@%33#3#3#3p=9%L3#3p=7%33#Lp=>g00UnR6g00UPR7P7P7P0P0f5R0f4R8f3R9f2R:P5P3M<]p=WP7P7P7P7P7P7P2P3P5P:P2P9P8P0f6R2f7R;f8R<f9R=MBlp=VP7P5g00VMP3Cmp=;P5g00W4R>g00WSR?P?g00X3R@P3g00XSF\p==P:P>P?P?P@P5P3F[p=Ig00Y3RA#3RB#1RC#3#1RD#ERE#B%EC#BRF#t[%JF1MF5#:=G73g00YXRG/09128:%8BR8%8DRD'OR9'0%N2g00;8%?;g00[>RHg00d`,kE#h%HH3aRH,@;12;0%1A#9#7#1#>#1#7#9#8RE'0%1A#9#7#1#>#7#1#7#1#8RI/0;'6%D<=C=;#N[P3%?=f:RJ/@H12J</0E10IJ'6f<RKf;RL#D;CJRM#?1@MHRMPKPLPJP=P<P;P2P:P3M9ZP4PK%1A#9#7#1#>#>#1#9#8RKPHPLPJP=P<P;P2P5g00]n#5#5#5#5#5#5#5#5R2#:R;,2KR</0LR412L=/0KR='6%8CRC,2KRN/0LRO/6=P4P=POP=P7P7P1P3X17ROP11053#YXE7X17P<PNPOPOPOP7P7g00^M1253CX,47X57X67PKPK147KP;PCPOPO%:3,47X16P2PC147CEWM:VPLPL147LM<Up-0/4=9S==ER1MFJRJ#P%:J,0G1Q8D1AG8RJ10GD1AG9[RF[10G8R2g00_1R6AT8D5UW010G9\6^02P5g00_M1sG8'4PJeO1PFg00`3RF#H%JFP71r7:P5%q7Cp%o7%n7RFP>P?P?P@1K7ARA1K7B5F7RB1<7E';,=F1<7I/;A,=F5IF%g?1<7KR?1<7C5F7/;A,=F1;B?,=F5IFGf1eF@P3P:g00`_RFg00a?R@'41b3:=GF@dAc7G5Cdb>b@bAX37X471235/0E10I3'610N5125:/0K'6[^37^47P3f>f@P0O3b=b2b?b2bDC`%_H#:,2K/0L/6=eM<iPMeC^W:W9W8P5P3O2n2001000000121000000W7W;W0W<X67WCXB7W5o"). Qed.
(* [comment removed for export] *)
Lemma io_ssp_write : forall (m : mem) a bs (n : Z), Z.of_nat (length bs) = n -> 0 <= a -> a + n <= 2^64 ->
  io_ssp m -> (a + n <= 0x10000 \/ SEGTOP_A <= a \/ (0x102120 <= a /\ a + n <= 0x102188)) -> io_ssp (write_to_mem m (wa a) bs).
Proof.
ltac2:(KReplay.run1 (kr_t_Lept_env ()) [] "p'0h04__p1h16__sat4h24__x1h34__x2h42Hah51gh61xi001xh71Hh87__arithh94__ffh:6__sat3h;8__varmaph<5__with=4cstrh>1mh?1nh@2H1hA2H2hB2HdhC2HlhD2HnhE1ahF2bshG1yp;1p;2p;3p;4p;6p;<p;Bp;7p;8g0000j12Tg000Uj1ZTg0013j1NTg001Vj1}Tg0028j1YTg002Xj2RTg0038R0j1BTg003Xj3[Tg0042R1j20Tg00;SR2j21Tg004Nj16Tg004lj2]Tg00e`j1KTg006Dj1DTg006ij2mTg00:@j1FTg008Gj1WTg008gj3GTg00;8R3j29Tg00<0j1ITg00<bj3HTg00=fj17Tg00>Ej25Tg00>_j1`Tg00?=j4_Tg00?`j2ETg00@:j3LTg00@`j6STg00AHj1|Tg00Amj2{Tg00BUj2\Tg00C1j3zTg00CUj2yTg00D6j2xTg00DTj1uTg00E2j4tTg00EPj1qTg00Enj1pTg00FYj2XTg00G<j3JTg00f[j6oTg00G_j1nTg00HAj2lTg00Hcj2kTg00IOj3iTg00Inj4jTg00J`j4TTg00KKj1OTg00g?l<PTg00MMj4hTg00hEj4gTg00h_j4fTg00Mhl<eTg00NMlBdTg00O3l<rTg00OXj2sTg00P;j4cTg00Pfj7vTg00iXj7wTg00QJj7bTg00Qnj8aTf0R4#2#2p=C%D4#Dp=>%D4#2p==%24#Dp=@%D4#2#2#2p=8g00RRR5f2R6f1R7P4Cfp=3%24#2#2#2p=;1067/54p=4g00UPR8/E4p=?g00UnR9P8P8P8P0P0f5R0f4R:f3R;P6P7P4M<ep=^P8P8P8P8P8P8P2P4P7P6P2P;P:P0f6R2f7R<f8R=f9R>MBdp=MP8P8P1P<P1P2P0P:P;P6P7P4M<rp=Q1s84p=<P6g00W4R1g00WSR?P?g00X3R@P8P7g00VMP4Ccg00XSFvp=:P6P1P?P?P@P7P4Fwp=VP6P1P?P?P@P7P4Fbp=AP;P1P?P?P@P6P7P4Gap=Ug00Y3RA#2RB#CRC#2#CRD#ZRE#NRF%ZC#NRG#}[%YG1RG7#B=[84g00YXRH/0;11:6%6BR;%6DRI']RJ'0%K2g00j<PF%DA#>#>#=#@#>#>#=#8#6RKg00[>RL%=A#@#@#>#>#>#=#8#8#6RM,mE#F%WLRE3GRN53=%F4=GLERO93=M'9X5F11<0RP%CD#;#;#6RDg00jVRQ%CA#;#8#@#C#=#;#6RR/0<%CA#;#8#@#8#8#6RS,0P'974<34%I==H><#K[P4f:R<?3KNA3<MO'9P3f;R3?3KN%F7=GLE933M113>R>10R310>S'994Q374Df=R>f<R=#I;H3#K[P4A3>KNf>RP%F:=GLE73M11P=RT10RP10TS'994QP74DPFfAf@RQ#If?RT3HRU?3KNA3UMO'9X5FP2%IT=HQPRU?3KN%F2=GLERE93UMP5PQPKPNPTPPP>P=P3P<P6g00]n#7#7#7#7#7#7#7#7RU#BRL,1KR2/0TRO11T>RV/0KRW'5%6CRC,1KRX/0TRY/5WPOPWPYPWP4X68RY1074#`XG8X68ROP2PXPYPYPYP8P8g00^M1174C_#?X>8X?8R2PKPK%?KPLPCPYPY%B4#?X69PUPC%?CE^RUM:MPTPT%?TR9GQp-0RZ/EW9LWWES1RGPRG#|R[%BG,0HRG1{;IR\1\H;R]10HI1\HJ[R^[R_10H;R`g00_1RaAz;I7UW4RI10HJ\a^4`R`P7g00_M1yH;'EP]eO1R]P^g00`3R;#WRa%Y;R;P81x86P7%u8CtRJ%q8Rb%p8Rc1X8ARd1X8B5J8RB%<D5:cRe%=A#@#8#=#;#;#;#6RA#<=:cdRf%<R=:cdPcP1P?P?P@P:EoR:5Vc5Ac5Ac%n?R?%<KR1%<CRg5J8=:cdA:cB15AcCU1lc@R@P4P6g00`_R1g00a?Rh'E1k46=[1hdAi8H7CjRHb9b;b<X28X38X0Z1147Rh/0DRD10A4RA10R4/96'5'51176R1/0K94X7[^28^38^0ZP4fDRXfBRi'1/0SPiPXP0O4b8b1b:b1b=CT%ON#B,1K?4TWeM<PP5PQPMPEPTPPP>P=P3P<P711MLR</0TR310VMRV'511MCR=/0TR>/5VP3PVP>PVPYPOP<P=PYPYPYP2PMPM%?MPLPCPUM:MPTPTP9GQ1EZV9LVVESP[PGP\P_PIP`P]P^PaP;PJPbPc%<S9:cB9Vc:9Acf9AceP?%<MR?=J8g=:cdA:cB?5AcCUP@PHb9b;b<X28X38X0Z10hS,96,5A,5D101M94=7[^28^38^0ZP410RXPiPXP0O4b8b1b:b1b=CT%OE#B,1M?4TVeM<PChCgWBWAW@P7P4O2n2001000000121000000W7X5FP7P4O2n2001000000121100000W7WCW4WDX?8WFXE8W>o"). Qed.

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
ltac2:(KReplay.run1 (kr_t_Lept_env ()) ["Env"] "p'0h01Hh12Hxh22loh33Hinh41nh51Eh62H0h71xh81eh92hih:2AGh;2HPh<1Ph=1ah>1mh?2m'h@1ri001pi011zp;1p;3p;2p;4p;5p;6p;7g0000j1:Tg000Uj1NTg0013j1MTg001Vj1`Tg00kSj3ZTg00lMj1XTg00mOR0j2WTg00moj3FTg00nFj3VTg00ncj3UTg00o@j4PTg00BUj23Tg00;8j2GTg00j<j2YTg00;Sj29Tg004Nj1DTg003Xj30Tg0042j2BTg00>ER1j26Tg00?`j2KTg00o\j3HTg0106j5JTg010Sj3ATg008Gj1STg008gj3LTg00MMj4_Tg00hEj4RTg010mj4^Tg0128j6]Tg0133j4QTg006Dj1OTg013Sj6[Tg0140j7\Tf0R2#:#:p=8g00UPR3P3f1R4P2CQp=1f4R5f3R6'Bf2R71942'3'Gp=;P3P3P71942CQp=71B74/G2p=@%:2#:#:#:p=<%O2#:p=?%:2#Op=EA0742g014LR8'6p=Cf6R9f5R:;05A0674/62'6p=4A0:56A0742/68'6p=5P5P3P6P7P4P2E[p==A0342p=21342,G7p=IP3P:P5P6P7P4P2F\p=>1628p=Tp-0\3g00Y3R;#8R<#:R=#:#8#N#M%N=#M#`[R>AZ742%X2P:P4O1[^=31W33R?1142R@g014iRA3Ff7RBP6P2P2P6P7D;RCX73P9P:P5P:P4p,2RTp,2GPP4P3P?P?AV332RDAU33277DX@?RDPACPRA9F?@13629@46'GX93,Y3X23P5P311:2=F?A13729@:7'GX931956R@115@RE=F?ARA134@9@54P1%8;#<#?#8#E#8#?#<#DR@%D<R<'1RF1156R650?P?%8;#<#?#8#E#E#8#<#DRG%D=R='1RHP6P?%8;#<#?#8#E#E#?#<#DRI/1=RJP6%8;#<#?#8#E#?#8#<#DR;/1=RK=C?6F4P?19@<R6,1@RLA7::5RMP?19G=RN,1GROPMP?19I=RP,1IRQPMP?19;=RR,1;RSPME5F4P711:5R590?FP?P0P3P3P3P2P2n2001100000120101101X8?RMPF119:RTP2D=12<:P?P0P3P3P3P2P4n2001100000120101101X8?R0PF11B9RUP4D=12@Bf8RV,2@P@P2PBPBP2f9RWD;f:RX,2<P?PLf;RY9777RZP?POPZP?PQPZP?PSPZE5F4[]1X23P@P9P9P@PVD;12<WP<1B@WR<19@27IWP?PLA7@@4RZP?POPZP?PQPZP?PSPZE5F4]1X4313V69@@VP<13W6A0?LLR@P?POPLP?PQPLAC?SLF4RZ'613X61K?L9H@ZW6X0<P2DJW1PXP2P4E>W0W1PWP2P:E>W0P2O1b0P2O1b0W5P2O1P?PHP5P?PJP5AC?K5F4P1A0?HTP?PJPTP?PKPTE5P?PLA7BB9R9P?POP9P?PQP9P?PSP9E5F4P2A0?HUP?PMPH11VBR9P2D=12=BP?P0PH11WVRTP4D=12GW12GXPGP2PWPWP2PYD;f<R5,2=P?PLf=R:9777R<P?POP<P?PQP<P?PSP<E5F4[]1X23PGPVPVPGPXD;12=YR<P=1BGYRZ19G27IYP?PLA7GG4R@P?POP@P?PQP@P?PSP@E5F4]1X4313XN9@GXPZ13YNA0?LORGA0?OOR@P?PQPOP?PSPOE5R6'6R['6135N1K?O9H@69AG[W6X0ZP2DJW1P5P2P4E>W0W1PYP2PBE>W0P2O1b0P2O1b0W5P2O1P?PJPUP?PKPUE5P1A0?J9AC?K9P?PLA7WWVRVP?POPVP?PQPVP?PSPVE5F4P2A0?JTP?PMPJ11XWRVP2D=12=WP?P0PJ11YXR9P4D=12IY12I5PIP2PYPYP2P:D;f>RU,2=P?PLf?RB9777RZP?POPZP?PQPZP?PSPZE5F4[]1X23PIPXPXPIP5D;12=:P=1BI:RZ19I27I:P?PLA7II4R[P?POP[P?PQP[P?PSP[E5F4]1X43135P9@I5PZ13:PA0?LQRIA0?OQR[A0?QQRGAC?SQR6'6R@'6RN'613UP1K?Q9HG69A[@9AINW6X0ZP2DJW1PUP2P4E>W0W1P:P2PWE>W0P2O1b0P2O1b0W5P2O1AC?KTP1A0?KVP8P?PLA7YYXRXP?POPXP?PQPXP?PSPXE5F4P2A0?K9P?PMPK115YP2D=P<P?P0PK11:5P4D=12;:12;UP;P2P:P:P2PBD;f@R0,2=P?PLfA9777R7P?POP7P?PQP7P?PSP7E5F4[]1X23P;P5P5P;PUD;12=BP=1B;BR=19;27IBP?PLA7;;4R7P?POP7P?PQP7P?PSP7E5F4]1X4313UR9@;UP=13BRA0?LSRUA0?OSR;A0?QSR7A0?SSR<#TRM'6R9'6RX'6130R1K?S9H<89A7M9A;99AUXW6X0=P2DJW1P0P2P4E>W0W1PBP2PYE>W0P2O1b0P2O1b0W5P2O1P8P?PLA7::5R:P?POP:P?PQP:P?PSP:E5F4P2n010000100X38P2O1n200100001021100011000W3P2O1n200100001021100011000W3P2O1n200100001021100011000W3P2O1n200100001021100011000P?P?PD%S?9L?K9L?J9L?H9L?FCP9F?EePAeP2C_CRCRC^O2X1CX73PWP4O1\C^73eE]W3X43X23W;W:X?>W>W<o"). Qed.

Lemma LIBH_agree : forall (P : Z -> Prop) (m m' : mem), LIBH m -> agree_on P m m' -> (forall a, client_static a -> P a) -> LIBH m'.
Proof using GP.
ltac2:(KReplay.run1 (kr_t_Lept_env ()) ["Env"] "h01ah11Hh22AGh32H1h42H2h52H3h62H4h72HPh81Ph91mh:2m'p;1p;2p;3p;4p;8p;7g0000j13Tg000Uj1LTg0013j1KTg001Vj1STg00a_j1:Tg005Ij1MTg006ij2ATg00:@j1HTg008Gj1OTg008gj3=Tg00kSj3;Tg00lMj1RTg006Dj1JTg004Nj17Tg007Oj1QTg009Gj44Tg00;8R0j2BTg00mOj2PTg003Xj30Tg00>Ej22Tg00?`j2>Tg00o\j3DTg00moj3GTg015oj8<Tg0170j7@Tg010Sj38Tg00MMj4ITg0133j4NTf0R1#3#3p=1g00RRR2f1R3g00cYP1C4p=EP2P3g00SJP1C4p=FP2P3g00TLP1C4p=C%31#3#3#3p=5%J1#3p=6%31#Jp=9g00UPR4P4P3P1CNp=?p-0\4g00Y3R5#1R6#3R7#3#1#LR8#K%L7#K#S[R9%:3P0f2R:#Mg00[>R;g00d`,A8#H%O;R<3=R=,E:f4R>f3R?;;:%R1R@f7RAP3O1[^04%:>[[P1%M>P0P2f5RBg00Z6RC%J5#7,A8#Q==;<RDC4g00\6,A8#H==;<RE,FBg00]3,A8#H==;<R<,CB'Bf6RB/E=f8R;?;ABf;RBP3O1\@^04%:;[[[P1P2PAPCPDC41F;E1C;<'BP0f9R0/FE1C0<f:R0/E=f<RC?;B0f?R0P3O1\@^04%:C[[[P11FBE1CC<f=RC/E=f>=;0CfBP3O1\@^04P2P0%15#5#6#1#9#1#6#5#7R@PDC4RCP2P0%15#5#6#1#9#9#6#5#7RBPEC4RAP2P0%15#5#6#1#9#6#1#5#7R8P<C4RF'BRG'BP2P0%15#5#6#1#9#9#1#5#7R5P=C4PCPGP2f@RGP0P@PDP;fAR;PGP0P3P1P@%76R61P44R41?@6R6;06%77R7,?5R@=0461?B7RD=0461?87RC=046g014LRH'2'2'21>463Dg014iRI9G46eG<F@PAPFP2PGP0PBPEP>P;PGP0P3P1PBP7A046DA04@DRBA04DDR>A04CD/2HRE'2RF'21>4D9D>E98BF38AG4DIeG<F@P2PGP0P8P<P?P;PGP0P3P1P8P7A046CA04@CR8A04DCR?A04CCR</2HRF'2RB'21>4C9D<H98?F988B38AG4CIeG<F@CICIP2PGP0P5P=P:P;PGP0P3P1P5P7A046@A04@@R6A04D@A04C@/2H'2RH'21>4@9D6H38AG4@IeG<F@CI%:0eW7W2W6W5W4P3P1O2n2001000000121000000W1W3P3P1O2n2001000000121000000W1P3P1O2n2001000000121000000W1X:9W9W8o"). Qed.

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
