(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.K5.Lib Require Import Tac.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.K5.B23 Require Import ImageA.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.K5.Lib Require Import RzCPS StoreFast.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.K5.PG Require Import Str_tac Startup_glue.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.K5.B23 Require Import Layout.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.K5.AG Require Import Shadow.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.K5.B23 Require Import RT_iface RT_traces RT_gaps_iface LeptTac D_kit Lept_kit Lept_iface.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.K5.Lib Require Import FarStep.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib Require KReplay.
Ltac2 kr_t_Lept_env () := "K47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00I47Corelib4Init9Datatypes6option00I47Corelib4Init9Datatypes4list00C47Corelib4Init9Datatypes6lengthC56Stdlib6ZArith6BinInt1Z6of_natI47Corelib4Init5Logic2eq00C56Stdlib6ZArith6BinInt1Z2leK47Corelib7Numbers7BinNums1Z02C56Stdlib6ZArith6BinInt1Z3powC69OSSVerify5KrLib2K53B23:Lept_iface4LIB0C1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive01C45stdpp9bitvector;definitions7Z_to_bvK69OSSVerify5KrLib2K53Lib5Cells4cell02C1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes4list01K47Corelib4Init9Datatypes4list02C69OSSVerify5KrLib2K53Lib4Step8rw_cellsC1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib2K53Lib5Cells4cell01C1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic3and00C56Stdlib6ZArith6BinInt1Z3addC69OSSVerify5KrLib2K53Lib3Mem2waC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics<write_to_memK47Corelib4Init9Datatypes3nat02I47Corelib4Init5Logic2or00C47Corelib4Init5Logic8iff_reflC46Stdlib9micromega;ZifyClasses3injK47Corelib4Init5Logic2eq01C46Stdlib9micromega;ZifyClasses6eq_iffC46Stdlib9micromega;ZifyClasses8or_morphC56Stdlib6ZArith4Znat5Nat2Z9is_nonnegC56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z2ltC56Stdlib6ZArith6BinInt1Z:pow_nonnegC56Stdlib6ZArith6BinInt1Z7compareK46Stdlib9micromega6VarMap1t02K46Stdlib9micromega6VarMap1t01K46Stdlib9micromega6VarMap1t03I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr02K46Stdlib9micromega7EnvRing5PExpr03K47Corelib4Init9Datatypes6option02C46Stdlib9micromega5Tauto8BFormulaC46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundC46Stdlib9micromega;ZifyClasses;rew_iff_revC69OSSVerify5KrLib2K53Lib5Cells:cells_sizeC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib9StoreFast@rw_cells_frame_nC1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic3and01C46Stdlib9micromega;ZifyClasses5mkappC46Stdlib9micromega;ZifyClasses6mkapp2C46Stdlib9micromega;ZifyClasses5mkrelK46Stdlib9micromega7EnvRing5PExpr01K46Stdlib9micromega=RingMicromega7Formula01K46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega5Tauto8GFormula06K46Stdlib9micromega5Tauto8GFormula08C69OSSVerify5KrLib2K53B236ImageA5asegsC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B23:Lept_iface;g_pix_allocC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B23:Lept_iface=g_pix_deallocC1?~~~~~~~~~~~~~~~I47Corelib7Numbers7BinNums1Z00I47Corelib4Init9Datatypes3nat00K46Stdlib9micromega=RingMicromega3Op203C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K47Corelib4Init9Datatypes4unit01K47Corelib7Numbers7BinNums8positive03K47Corelib7Numbers7BinNums1Z01C69OSSVerify5KrLib2K53B23:Lept_ifaceAg_LeptMsgSeverityC1?~~~~~~~~~~~~~~~I69OSSVerify5KrLib2K53Lib5Cells4cell00C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B238RT_iface8e_mallocC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B238RT_iface6e_freeC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes3nat01C46Stdlib9micromega8ZifyInst7Inj_Z_ZI47Corelib4Init5Logic4True00I47Corelib4Init9Datatypes:comparison00I46Stdlib9micromega:ZMicromega;ZArithProof00I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01C69OSSVerify5KrLib2K53B23:Lept_iface4LIBHC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2K53B238Lept_env:LIB0_writeC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B23:Lept_iface@g_stderr_handlerC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B23:Lept_iface9e_devnullC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B238RT_iface6io_sspC1?~~~~~~~~~~~~~~~K46Stdlib9micromega5Tauto8GFormula03C69OSSVerify5KrLib2K53Lib9StoreFast@ro_cells_frame_nC1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic2ex01C69OSSVerify5KrLib2K53Lib4Step8ro_cellsC1?~~~~~~~~~~~~~~~K46Stdlib9micromega5Tauto8GFormula05I47Corelib4Init5Logic2ex00C69OSSVerify5KrLib2K53B238RT_iface8SEGTOP_AC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B235D_kit8agree_onC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B238RT_iface=client_staticC1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes4prod00C46Stdlib5Lists4List2InC47Corelib4Init9Datatypes3fstC47Corelib4Init9Datatypes3sndC47Corelib5Lists7ListDef3mapK47Corelib4Init5Logic2or01C47Corelib4Init5Logic7and_indK47Corelib4Init5Logic2or02C69OSSVerify5KrLib2K53B23=RT_gaps_ifaceAgp_globals_clientC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B235D_kit9agree_subC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes4prod01C47Corelib4Init5Logic7f_equalC47Corelib4Init5Logic6eq_indI47Corelib4Init5Logic5False00C69OSSVerify5KrLib2K53B23=RT_gaps_iface<LEPT_GLOBALSC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2K53B238Lept_env<static_agreeC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B235D_kitArw_cells_agree_nwC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B238RT_iface3rtsC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53B238RT_iface3ARTC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitions;bv_unsignedC69OSSVerify5KrLib2K53B23=RT_gaps_iface;gp_ssp_keepC1?~~~~~~~~~~~~~~~".   (* [comment removed for export] *)
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
Lemma LIB0_write : forall (m : mem) a bs (n : Z), Z.of_nat (length bs) = n -> 0 <= a -> a + n <= 2^64 ->
  LIB0 m -> (a + n <= 0x22a5e0 \/ 0x22a688 <= a) -> LIB0 (write_to_mem m (wa a) bs).
Proof.
ltac2:(KReplay.run1 (kr_t_Lept_env ()) [] "h06__sat5h14__x1h24__x2h32Hah47__arithh54__ffh66__sat4h78__varmaph85__with94cstrh:1xh;1Hh<1mh=1nh>2H1h?2H2h@2H3hA2HdhB2HlhC2HnhD1ahE2bshF1yp;1p;2p;3p;4p;6p;<p;Bp;7p;8g0000j12Tg000Uj1YTg0013j1WTg001Vj1{Tg0028j1]Tg002Xj2ZTg0038R0j17Tg003Xj3XTg0042R1j20Tg004Nj15Tg004lj2bTg005Ij1GTg006Dj1:Tg006ij2RTg007Oj1pTg008Gj1[Tg008gj3OTg009Gj4<Tg00:@j1\Tg00;8R2j2PTg00;SR3j21Tg00<0j1LTg00<bj3KTg00=fj18Tg00>Ej2;Tg00>_j1cTg00?=j4aTg00?`j2BTg00@:j3TTg00@`j6STg00AHj1zTg00Amj2yTg00BUj2_Tg00C1j3xTg00CUj2uTg00D6j2tTg00DTj1qTg00E2j4oTg00EPj1nTg00Enj1mTg00FYj2VTg00G<j3DTg00G_j1jTg00HAj2iTg00Hcj2hTg00IOj3kTg00Inj4lTg00J`j4MTg00KKj1JTg00LGl<QTg00MMj4^Tg00Mhl<gTg00NMlBfTg00O3l<eTg00OXj2rTg00P;j4sTg00Pfj7dTg00QJj7vTg00Qnj8wTf0R4#2#2p=3f2R5f1R6'1/04p=`g00RRR7P6g00SJP4C<p=CP7P6g00TLP4C<p=E%:4#2p=6%:4#2#:#2p=@%24#:p=?1056/;4p=4g00UPR8/B4p=9g00UnR9P8P8P8P0P0f5R0f4R:f3R;P5P6P4M<gp=UP8P8P8P8P8P8P3P4P6P5P3P;P:P0f6R3f7R<f8R=f9R>MBfp=HP8P8P1P<P1P3P0P:P;P5P6P4M<ep=I1r84p=AP8P6g00VMP4Csp=>P6g00W4R1g00WSR?P?g00X3R@P4g00XSFdp==P5P1P?P?P@P6P4Fvp=FP;P1P?P?P@P5P6P4Gwp=Ng00Y3R1#2RA#2RB#2RC#2#3RD#YRE#W%YC#WRF#{[%]F1ZF6#7=X84g00YXRG/0;%5AR;%5DRD'bRH9`:5%G3P2P7P<g00Z6R:g00[>RI%:1#5,RE#p%[IRJ3ORKC<g00\6,RE#\=OIJRL,C<g00]3,RE#\=OIJRJ,E<'P11<0%21#3#6#@#?#?#:#:#6#3#3#5RI%21#3#6#@#?#@#3#6#3#5RE/0<34%L==K><#G[P4P7P>P:PKC<f:R:/CL1E:J'PP2f;R2/CL1E2J112>10E274If=R>f<R<#L;K2#G[P41C>Lf>R=/EJ11=<10E=74IP7f@RMf?RN#L;K=ROPIPKC<P7PO%21#3#6#@#?#6#?#6#3#3#5RPPLC<RQP7PO%21#3#6#@#?#@#3#3#3#5RRPJC<RS'PP7PMPIPKPNP=P>P<P2P:P3g00]n#8#8#8#8R3#7RT,1IRU/0NRV11N>RW/0IRX';%5BRB,1IRY/0NRZ/;XPVPXPZPXP4X:8RZ1064#cXF8X:8RVPUPYPZPZPZP8P8g00^M1164Ca#9X<8X=8RUPIPI%9IPTPBPZPZ%74#9X:9R9P3PB%9BEUM:HPNPN%9NRTGIp-0R[/BX9TXXES1ZF=RF#zR\%7F,0GRF1y;DR]1_G;R^10GD1_GH[R_[R`10G;Rag00_1RbAx;D6UW3RD10GH\b^3aRaP6g00_M1uG;'BP^eO1R^P_g00`3R;#[Rb%];R;P81t85P6%q8CoRH%n8Rc%m8Rd1V81R11V8A5D8RA%AIRe'>,=dRf%AE/>1,=d5FdRg%j?R?%AB9D8e/>1,=d=FdfCN1id@R@P4P5g00`_Rfg00a?Re'B1h45=XfedAk8G6ClRGb5b7b8X18X28114610E474IRE1165Re/0I94Y6[^18^28P4fBfDP0O3R0b4b0b6b0b9CM%JK#7,1I?4NXeM<QPQPSP7PMPPPLPNP=P>P<P2P:P5%83#8#8#8R3#7R5,1PRS/0NRQ10WPRX';%5CRC,1PRI/0NRK/;XPQPXPKPXPZPVPSPIPZPZPZPUPPPP%9PP5PCPZPZP9P3PC%9CEUR3M:HPNPNPTGI1B[X9TXXESP\PFP]P`PDPaP^P_PbP;PHPcPdPgP?%APR9%ACRS5D8/>1,=d1>A9,=d5FdCNP@PGb5b7b8X18X2810eP94I6\E^18^28P0b4b0b6b0b9CM%JL#7,1P?4NXeM<QP7PMPRPJPNP=P>P<P2P:P611R5R:/0NR210WRRW';11RCR</0NR>/;WP2PWP>PWPZPVP:P<PZPZPZPUPRPR%9RP5PCP3M:HPNPNPTGI1B[W9TWWESP\PFP]P`PDPaP^P_PbP;PHPcPdPgP?%ARR?=D8S/>1,=d1>A?,=d5FdCNP@PGb5b7b8X18X2810eR94<6\E^18^28P0b4b0b6b0b9CM%JJ#7,1R?4NWeM<QC^C^%GOeWAW@W?P6P4O2n2001000000121000000W;W>P6P4O2n2001000000121000000W;WBW3WCX=8WEXD8W<o"). Qed.
Lemma LIBH_write : forall (m : mem) a bs (n : Z), Z.of_nat (length bs) = n -> 0 <= a -> a + n <= 2^64 ->
  LIBH m -> (a + n <= 0x22a5e0 \/ 0x22a688 <= a) -> LIBH (write_to_mem m (wa a) bs).
Proof.
ltac2:(KReplay.run1 (kr_t_Lept_env ()) [] "h02Hah11xh26__sat3h34__x1h44__x2h51mh61nh71Hh82H0h92H1h:2Hdh;2Hlh<2Hnh=7__arithh>4__ffh?6__sat2h@8__varmaphA5__withB1ahC2bshD4cstrhE1yp;1p;2p;3p;9p;4p;<p;6p;8p;Bp;7g0000j14Tg000Uj1ETg0013j1BTg001Vj1sTg0028j1ITg002Xj2KTg0038R0j19Tg003Xj3GTg0042R1j20Tg00;SR2j23Tg004Nj18Tg004lj2NTg00a_j1MTg005Ij1@Tg006ij2gTg00:@j1aTg008Gj1LTg008gj3_Tg006Dj1<Tg00>Ej27Tg00<0j1DTg00<bj3CTg00bZl9YTg00=fj16Tg00>_j1XTg00?=j4WTg00?`j25Tg00O3l<TTg00@:j3OTg00@`j6PTg00AHj1QTg00Amj2RTg00BUj2ATg00C1j3STg00CUj2rTg00D6j2qTg00DTj1pTg00E2j4oTg00EPj1nTg00Enj1kTg00FYj2JTg00G<j3FTg00OXj2;Tg00G_j1`Tg00Qnj8bTg00HAj2cTg00Hcj2dTg00IOj3eTg00Inj4fTg00J`j4^Tg00KKj1]Tg00LGl<hTg00MMj4\Tg009Gj4iTg00Mhl<jTg00NMlB[Tg00P;j4lTg00Pfj7mTg00QJj7ZTf0R3#4#4p=2g00RRR4f1R5g00cYP3Cip=?%<3#4p=1%43#<p=>g00UnR6g00UPR7P7P7P0P0f5R0f4R8f3R9f2R:P5P3M<jp=VP7P7P7P7P7P7P2P3P5P:P2P9P8P0f6R2f7R;f8R<f9R=MB[p=UP7P5g00VMP3Clp==P5g00W4R>g00WSR?P?g00X3R@P3g00XSFmp=:P:P>P?P?P@P5P3FZp=Hg00Y3RA#4RB#2RC#4#2RD#ERE#B%EC#BRF#s[%IF1KF5#9=G73g00YXRG/09138:%8BR8%8DRD'NR9'0%M2g00;8%@;g00[>RHg00d`,gE#a%LH3_RH,?;13;0%4A#2#1#1#1#>#>#<#<#1#2#2#8RE'0%4A#2#1#1#1#>#1#1#2#1#2#8RI/0;'7%D<=C=;#M[P3%@=f:RJ/?H13J</0E10IJ'7f<RKf;RL#D;CJRM#@1?MHRMPKPLPJP=P<P;P2P:P3M9YP4PK%4A#2#1#1#1#>#1#2#2#2#2#8RKPHPLPJP=P<P;P2P5g00]n#6#6#6#6#6#6#6#6R2#9R;,3KR</0LR413L=/0KR='7%8CRC,3KRN/0LRO/7=P4P=POP=P7P7P1P3X17ROP11053#XXE7X17P<PNPOPOPOP7P7g00^M1353CW,57X57X67PKPK157KP;PCPOPO%93,57X16P2PC157CEVM:UPLPL157LM<Tp-0/5=9O==EP1KFJRJ#Q%9J,0G1R8D1AG8RJ10GD1AG9[RF[10G8R2g00_1R6AS8D5UW010G9\6^02P5g00_M1rG8'5PJeO1PFg00`3RF#L%IFP71q7:P5%p7Co%n7%k7RFP>P?P?P@1J7ARA1J7B5F7RB1;7E'=,:F1;7I/=A,:F5HF%`?1;7KR?1;7C5F7/=A,:F1=B?,:F5HFGb1cF@P3P:g00`_RFg00a?R@'51d3:=GF@dAe7G5Cfb>b@bAX37X471335/0E10I3'710N5135:/0K'7[^37^47P3f>f@P0O3b=b2b?b2bDC^%]H#9,3K/0L/7=eM<hPMeC\W:W9W8P5P3O2n2001000000121000000W7W;W0W<X67WCXB7W5o"). Qed.
(* [comment removed for export] *)
Lemma io_ssp_write : forall (m : mem) a bs (n : Z), Z.of_nat (length bs) = n -> 0 <= a -> a + n <= 2^64 ->
  io_ssp m -> (a + n <= 0x10000 \/ SEGTOP_A <= a \/ (0x22a5e0 <= a /\ a + n <= 0x22a688)) -> io_ssp (write_to_mem m (wa a) bs).
Proof.
ltac2:(KReplay.run1 (kr_t_Lept_env ()) [] "p'0h04__p1h16__sat4h24__x1h34__x2h42Hah51gh61xi001xh71Hh87__arithh94__ffh:6__sat3h;8__varmaph<5__with=4cstrh>1mh?1nh@2H1hA2H2hB2HdhC2HlhD2HnhE1ahF2bshG1yp;1p;2p;3p;4p;6p;<p;Bp;7p;8g0000j13Tg000Uj1ZTg0013j1NTg001Vj1|Tg0028j1XTg002Xj2UTg0038R0j1BTg003Xj3OTg0042R1j20Tg00;SR2j22Tg004Nj17Tg004lj2^Tg00e`j1JTg006ij2oTg00:@j1DTg008Gj1TTg008gj3CTg00;8R3j2=Tg00<0j1HTg00<bj3FTg00=fj1<Tg00>Ej26Tg00>_j1aTg00?=j4`Tg00?`j2ETg00@:j3RTg00@`j6KTg00AHj1]Tg00Amj2\Tg00BUj2[Tg00C1j3{Tg00CUj2zTg00D6j2yTg00DTj1xTg00E2j4wTg00EPj1rTg00Enj1qTg00FYj2YTg00G<j3ITg00f[j6pTg00G_j1nTg00HAj2mTg00Hcj2kTg00IOj3jTg00Inj4iTg00J`j4STg00KKj1PTg00g?l<QTg00MMj4hTg00hEj4lTg006Dj1GTg00h_j4gTg00Mhl<fTg00NMlBeTg00O3l<dTg00OXj2sTg00P;j4tTg00Pfj7cTg00iXj7uTg00QJj7vTg00Qnj8bTf0R4#3#3p=9%G4#3p=1%34#Gp=8%G4#Gp=;%34#3#3#3p=?g00RRR5f2R6f1R7P4Cgp=41067/64p=5g00UPR8/E4p=@g00UnR9P8P8P8P0P0f5R0f4R:f3R;P6P7P4M<fp=_P8P8P8P8P8P8P2P4P7P6P2P;P:P0f6R2f7R<f8R=f9R>MBep=MP8P8P1P<P1P2P0P:P;P6P7P4M<dp=L1s84p=>P6g00W4R1g00WSR?P?g00X3R@P8P7g00VMP4Ctg00XSFcp=:P6P1P?P?P@P7P4Fup=WP6P1P?P?P@P7P4Fvp=AP;P1P?P?P@P6P7P4Gbp=Vg00Y3RA#3RB#9RC#3#9RD#ZRE#NRF%ZC#NRG#|[%XG1UG7#B=O84g00YXRH/0;12:6%7BR;%7DRI'^RJ'0%J2g00j<PF%3A#9#1#8#1#1#;#8#;#?#7RKg00[>RL%;A#1#8#8#;#;#1#;#8#1#9#7RM,oE#D%TLRE3CRN54=%D4=CLERO94=M'=X5F12<0RP%9D#?#?#7RDg00jVRQ%3A#9#1#1#1#8#8#;#1#?#7RR/0<%3A#9#1#1#1#8#1#1#9#1#9#7RS,0P'=75<35%H==F><#J[P4f:R<?4KNA4<MO'=P3f;R3?4KN%D7=CLE943M123>R>10R310>S'=95Q375Df=R>f<R=#H;F3#J[P4A4>KNf>RP%D:=CLE74M12P=RT10RP10TS'=95QP75DPFfAf@RQ#Hf?RT3FRU?4KNA4UMO'=X5FP2%HT=FQPRU?4KN%D2=CLERE94UMP5PQPKPNPTPPP>P=P3P<P6g00]n#<#<#<#<#<#<#<#<RU#BRL,2KR2/0TRO12T>RV/0KRW'6%7CRC,2KRX/0TRY/6WPOPWPYPWP4X68RY1074#aXG8X68ROP2PXPYPYPYP8P8g00^M1274C`#@X>8X?8R2PKPK%@KPLPCPYPY%B4#@X69PUPC%@CE_RUM:MPTPT%@TR9GLp-0RZ/EW9RWWEK1UGPRG#]R[%BG,0HRG1\;IR\1[H;R]10HI1[HJ[R^[R_10H;R`g00_1RaA{;I7UW4RI10HJ\a^4`R`P7g00_M1zH;'EP]eO1R]P^g00`3R;#TRa%X;R;P81y86P7%x8CwRJ%r8Rb%q8Rc1Y8ARd1Y8B5I8RB%>D5:cRe%;A#1#8#1#1#?#?#?#7RA#>=:cdRf%>R=:cdPcP1P?P?P@P:EpR:5Wc5Ac5Ac%n?R?%>KR1%>CRg5I8=:cdA:cB15AcCV1mc@R@P4P6g00`_R1g00a?Rh'E1k46=O1hdAj8H7CiRHb9b;b<X28X38X0Z1247Rh/0DRD10A4RA10R4/=6'6'61276R1/0K95X7[^28^38^0ZP4fDRXfBRi'2/0SPiPXP0O4b8b1b:b1b=CS%PN#B,2K?5TWeM<QP5PQPMPEPTPPP>P=P3P<P712MLR</0TR310VMRV'612MCR=/0TR>/6VP3PVP>PVPYPOP<P=PYPYPYP2PMPM%@MPLPCPUM:MPTPTP9GL1EZV9RVVEKP[PGP\P_PIP`P]P^PaP;PJPbPc%>S9:cB9Wc:9Acf9AceP?%>MR?=I8g=:cdA:cB?5AcCVP@PHb9b;b<X28X38X0Z10hS,=6,6A,6D101M95=7[^28^38^0ZP410RXPiPXP0O4b8b1b:b1b=CS%PE#B,2M?5TVeM<QChClWBWAW@P7P4O2n2001000000121000000W7X5FP7P4O2n2001000000121100000W7WCW4WDX?8WFXE8W>o"). Qed.

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
ltac2:(KReplay.run1 (kr_t_Lept_env ()) ["Env"] "p'0h01Hh12Hxh22loh33Hinh41nh51Eh62H0h71xh81eh92hih:2AGh;2HPh<1Ph=1ah>1mh?2m'h@1ri001pi011zp;1p;3p;2p;4p;5p;6p;7g0000j19Tg000Uj1OTg0013j1NTg001Vj1`Tg00kSj3YTg00lMj1WTg00mOR0j2VTg00moj3FTg00nFj3TTg00ncj3STg00o@j4PTg00BUj23Tg00;8j2HTg00j<j2XTg00;Sj2:Tg006Dj1DTg004Nj1ETg003Xj30Tg0042j2@Tg00>ER1j27Tg00?`j2ITg00o\j3LTg0106j5KTg010Sj3BTg008Gj1_Tg008gj3MTg00MMj4^Tg00hEj4RTg010mj4]Tg0128j6\Tg0133j4QTg013Sj6ZTg0140j7[Tf0R2#9#9p=4g00UPR3P3f1R4P2CQp=1f4R5f3R6'@f2R71:42'3'Hp=;P3P3P71:42CQp=81@74/H2p=?%D2#9p=>%D2#9#D#9p=G%92#Dp=CA0742g014LR8'7p=Af6R9f5R:;05A0674/72'7p=5A0:56A0742/78'7p=6P5P3P6P7P4P2EZp==A0342p=21342,H7p=JP3P:P5P6P7P4P2F[p=<1728p=Up-0\3g00Y3R;#4R<#9R=#9#4#O#N%O=#N#`[R>AY742%W2P:P4O1[^=31V33R?1142R@g014iRA3Ff7RBP6P2P2P6P7D;RCX73P9P:P5P:P4p,2RTp,2GPP4P3P?P?AT332RDAS33278DX@?RDPACPRA9F?@13629?46'HX93,X3X23P5P311:2=F?A13729?:7'HX931:56R@115@RE=F?ARA134@9?54P1%9;#4#>#G#C#C#D#D#>#4#4#ER@%E<R<'1RF1156R650?P?%9;#4#>#G#C#>#4#4#4#4#ERG%E=R='1RHP6P?%9;#4#>#G#C#>#C#>#4#4#ERI/1=RJP6%9;#4#>#G#C#G#4#4#4#ER;/1=RK=A?6F5P?1:@<R6,1@RLA8::5RMP?1:G=RN,1GROPMP?1:I=RP,1IRQPMP?1:;=RR,1;RSPME6F5P711:5R590?FP?P0P3P3P3P2P2n2001100000120101101X8?RMPF119:RTP2D=12<:P?P0P3P3P3P2P4n2001100000120101101X8?R0PF11B9RUP4D=12@Bf8RV,2@P@P2PBPBP2f9RWD;f:RX,2<P?PLf;RY9877RZP?POPZP?PQPZP?PSPZE6F5[]1X23P@P9P9P@PVD;12<WP<1@@WR<1:@27JWP?PLA8@@4RZP?POPZP?PQPZP?PSPZE6F5]1X4313V69?@VP<13W6A0?LLR@P?POPLP?PQPLAA?SLF5RZ'713X61I?L9L@ZW6X0<P2DKW1PXP2P4E<W0W1PWP2P:E<W0P2O1b0P2O1b0W5P2O1P?PHP5P?PJP5AA?K5F5P1A0?HTP?PJPTP?PKPTE6P?PLA8BB9R9P?POP9P?PQP9P?PSP9E6F5P2A0?HUP?PMPH11VBR9P2D=12=BP?P0PH11WVRTP4D=12GW12GXPGP2PWPWP2PYD;f<R5,2=P?PLf=R:9877R<P?POP<P?PQP<P?PSP<E6F5[]1X23PGPVPVPGPXD;12=YR<P=1@GYRZ1:G27JYP?PLA8GG4R@P?POP@P?PQP@P?PSP@E6F5]1X4313XN9?GXPZ13YNA0?LORGA0?OOR@P?PQPOP?PSPOE6R6'7R['7135N1I?O9L@69BG[W6X0ZP2DKW1P5P2P4E<W0W1PYP2PBE<W0P2O1b0P2O1b0W5P2O1P?PJPUP?PKPUE6P1A0?J9AA?K9P?PLA8WWVRVP?POPVP?PQPVP?PSPVE6F5P2A0?JTP?PMPJ11XWRVP2D=12=WP?P0PJ11YXR9P4D=12IY12I5PIP2PYPYP2P:D;f>RU,2=P?PLf?RB9877RZP?POPZP?PQPZP?PSPZE6F5[]1X23PIPXPXPIP5D;12=:P=1@I:RZ1:I27J:P?PLA8II4R[P?POP[P?PQP[P?PSP[E6F5]1X43135P9?I5PZ13:PA0?LQRIA0?OQR[A0?QQRGAA?SQR6'7R@'7RN'713UP1I?Q9LG69B[@9BINW6X0ZP2DKW1PUP2P4E<W0W1P:P2PWE<W0P2O1b0P2O1b0W5P2O1AA?KTP1A0?KVP8P?PLA8YYXRXP?POPXP?PQPXP?PSPXE6F5P2A0?K9P?PMPK115YP2D=P<P?P0PK11:5P4D=12;:12;UP;P2P:P:P2PBD;f@R0,2=P?PLfA9877R7P?POP7P?PQP7P?PSP7E6F5[]1X23P;P5P5P;PUD;12=BP=1@;BR=1:;27JBP?PLA8;;4R7P?POP7P?PQP7P?PSP7E6F5]1X4313UR9?;UP=13BRA0?LSRUA0?OSR;A0?QSR7A0?SSR<#URM'7R9'7RX'7130R1I?S9L<89B7M9B;99BUXW6X0=P2DKW1P0P2P4E<W0W1PBP2PYE<W0P2O1b0P2O1b0W5P2O1P8P?PLA8::5R:P?POP:P?PQP:P?PSP:E6F5P2n010000100X38P2O1n200100001021100011000W3P2O1n200100001021100011000W3P2O1n200100001021100011000W3P2O1n200100001021100011000P?P?PD%_?9M?K9M?J9M?H9M?FCP9F?EePAeP2C^CRCRC]O2X1CX73PWP4O1\C^73eE\W3X43X23W;W:X?>W>W<o"). Qed.

Lemma LIBH_agree : forall (P : Z -> Prop) (m m' : mem), LIBH m -> agree_on P m m' -> (forall a, client_static a -> P a) -> LIBH m'.
Proof using GP.
ltac2:(KReplay.run1 (kr_t_Lept_env ()) ["Env"] "h01ah11Hh22AGh32H1h42H2h52H3h62H4h72HPh81Ph91mh:2m'p;1p;2p;3p;4p;8p;7g0000j12Tg000Uj1LTg0013j1KTg001Vj1STg00a_j1;Tg005Ij1MTg006ij2BTg00:@j1ITg008Gj1OTg008gj3>Tg00kSj3<Tg00lMj1RTg006Dj17Tg004Nj16Tg007Oj1QTg009Gj44Tg00;8R0j2CTg00mOj2PTg003Xj31Tg00>Ej23Tg00?`j2?Tg00o\j3FTg00moj3DTg015oj8=Tg0170j7ATg010Sj38Tg00MMj4JTg0133j4NTf0R1#2#2p=0g00RRR2f1R3g00cYP1C4p=GP2P3g00SJP1C4p=HP2P3g00TLP1C4p=E%71#2p=5%71#2#7#2p=:%21#7p=9g00UPR4P4P3P1CNp=@p-0\4g00Y3R5#0R6#2R7#2#0#LR8#K%L7#K#S[R9%;3P0f2R:#Mg00[>R;g00d`,B8#I%O;R<3>R=,G:f4R>f3R?;<:%R1R@f7RAP3O1[^04%;>[[P1%M>P0P2f5RBg00Z6RC%75#6,B8#Q=>;<RDC4g00\6,B8#I=>;<RE,HBg00]3,B8#I=>;<R<,EB'Cf6RB/G=f8R;?<ABf;RBP3O1\@^04%;;[[[P1P2PAPCPDC41H;E1E;<'CP0f9R0/HE1E0<f:R0/G=f<RC?<B0f?R0P3O1\@^04%;C[[[P11HBE1EC<f=RC/G=f>=<0CfBP3O1\@^04P2P0%25#0#5#:#9#9#7#7#5#0#0#6R@PDC4RCP2P0%25#0#5#:#9#5#9#5#0#0#6RBPEC4RAP2P0%25#0#5#:#9#:#0#0#0#6R8P<C4RF'CRG'CP2P0%25#0#5#:#9#5#0#0#0#0#6R5P=C4PCPGP2f@RGP0P@PDP;fAR;PGP0P3P1P@%66R61P44R41@@6R6;16%67R7,@5R@=1461@B7RD=1461@87RC=146g014LRH'3'3'31?463Fg014iRI9D46eG=FAPAPFP2PGP0PBPEP>P;PGP0P3P1PBP7A146DA14@DRBA14DDR>A14CD/3HRE'3RF'31?4D9F>E98BF38AD4DIeG=FAP2PGP0P8P<P?P;PGP0P3P1P8P7A146CA14@CR8A14DCR?A14CCR</3HRF'3RB'31?4C9F<H98?F988B38AD4CIeG=FACJCJP2PGP0P5P=P:P;PGP0P3P1P5P7A146@A14@@R6A14D@A14C@/3H'3RH'31?4@9F6H38AD4@IeG=FACJ%;0eW7W2W6W5W4P3P1O2n2001000000121000000W1W3P3P1O2n2001000000121000000W1P3P1O2n2001000000121000000W1X:9W9W8o"). Qed.

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
