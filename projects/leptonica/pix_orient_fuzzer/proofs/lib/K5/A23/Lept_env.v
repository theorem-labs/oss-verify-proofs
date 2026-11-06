(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.K5.Lib Require Import Tac.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.K5.A23 Require Import ImageA.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.K5.Lib Require Import RzCPS StoreFast.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.K5.PG Require Import Str_tac Startup_glue.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.K5.A23 Require Import Layout.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.K5.AG Require Import Shadow.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.K5.A23 Require Import RT_iface RT_traces RT_gaps_iface LeptTac D_kit Lept_kit Lept_iface.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.K5.Lib Require Import FarStep.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib Require KReplay.
Ltac2 kr_t_Lept_env () := "K47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00I47Corelib4Init9Datatypes6option00I47Corelib4Init9Datatypes4list00C47Corelib4Init9Datatypes6lengthC56Stdlib6ZArith6BinInt1Z6of_natI47Corelib4Init5Logic2eq00C56Stdlib6ZArith6BinInt1Z2leK47Corelib7Numbers7BinNums1Z02C56Stdlib6ZArith6BinInt1Z3powC69OSSVerify5KrLib2K53A23:Lept_iface4LIB0C1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive01C45stdpp9bitvector;definitions7Z_to_bvK69OSSVerify5KrLib2K53Lib5Cells4cell02C1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes4list01K47Corelib4Init9Datatypes4list02C69OSSVerify5KrLib2K53Lib4Step8rw_cellsC1?~~~~~~~~~~~~~~~K69OSSVerify5KrLib2K53Lib5Cells4cell01C1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic3and00C56Stdlib6ZArith6BinInt1Z3addC69OSSVerify5KrLib2K53Lib3Mem2waC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics<write_to_memK47Corelib4Init9Datatypes3nat02I47Corelib4Init5Logic2or00C47Corelib4Init5Logic8iff_reflC46Stdlib9micromega;ZifyClasses3injK47Corelib4Init5Logic2eq01C46Stdlib9micromega;ZifyClasses6eq_iffC46Stdlib9micromega;ZifyClasses8or_morphC56Stdlib6ZArith4Znat5Nat2Z9is_nonnegC56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z2ltC56Stdlib6ZArith6BinInt1Z:pow_nonnegC56Stdlib6ZArith6BinInt1Z7compareK46Stdlib9micromega6VarMap1t02K46Stdlib9micromega6VarMap1t01K46Stdlib9micromega6VarMap1t03I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr02K46Stdlib9micromega7EnvRing5PExpr03K47Corelib4Init9Datatypes6option02C46Stdlib9micromega5Tauto8BFormulaC46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundC46Stdlib9micromega;ZifyClasses;rew_iff_revC69OSSVerify5KrLib2K53Lib5Cells:cells_sizeC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib9StoreFast@rw_cells_frame_nC1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic3and01C46Stdlib9micromega;ZifyClasses5mkappC46Stdlib9micromega;ZifyClasses6mkapp2C46Stdlib9micromega;ZifyClasses5mkrelK46Stdlib9micromega7EnvRing5PExpr01K46Stdlib9micromega=RingMicromega7Formula01K46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega5Tauto8GFormula06K46Stdlib9micromega5Tauto8GFormula08C69OSSVerify5KrLib2K53A236ImageA5asegsC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A23:Lept_iface;g_pix_allocC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A23:Lept_iface=g_pix_deallocC1?~~~~~~~~~~~~~~~I47Corelib7Numbers7BinNums1Z00I47Corelib4Init9Datatypes3nat00K46Stdlib9micromega=RingMicromega3Op203C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K47Corelib4Init9Datatypes4unit01K47Corelib7Numbers7BinNums8positive03K47Corelib7Numbers7BinNums1Z01C69OSSVerify5KrLib2K53A23:Lept_ifaceAg_LeptMsgSeverityC1?~~~~~~~~~~~~~~~I69OSSVerify5KrLib2K53Lib5Cells4cell00C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A238RT_iface8e_mallocC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A238RT_iface6e_freeC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes3nat01C46Stdlib9micromega8ZifyInst7Inj_Z_ZI47Corelib4Init5Logic4True00I47Corelib4Init9Datatypes:comparison00I46Stdlib9micromega:ZMicromega;ZArithProof00I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01C69OSSVerify5KrLib2K53A23:Lept_iface4LIBHC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2K53A238Lept_env:LIB0_writeC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A23:Lept_iface@g_stderr_handlerC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A23:Lept_iface9e_devnullC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A238RT_iface6io_sspC1?~~~~~~~~~~~~~~~K46Stdlib9micromega5Tauto8GFormula03C69OSSVerify5KrLib2K53Lib9StoreFast@ro_cells_frame_nC1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic2ex01C69OSSVerify5KrLib2K53Lib4Step8ro_cellsC1?~~~~~~~~~~~~~~~K46Stdlib9micromega5Tauto8GFormula05I47Corelib4Init5Logic2ex00C69OSSVerify5KrLib2K53A238RT_iface8SEGTOP_AC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A235D_kit8agree_onC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A238RT_iface=client_staticC1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes4prod00C46Stdlib5Lists4List2InC47Corelib4Init9Datatypes3fstC47Corelib4Init9Datatypes3sndC47Corelib5Lists7ListDef3mapK47Corelib4Init5Logic2or01C47Corelib4Init5Logic7and_indK47Corelib4Init5Logic2or02C69OSSVerify5KrLib2K53A23=RT_gaps_ifaceAgp_globals_clientC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A235D_kit9agree_subC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes4prod01C47Corelib4Init5Logic7f_equalC47Corelib4Init5Logic6eq_indI47Corelib4Init5Logic5False00C69OSSVerify5KrLib2K53A23=RT_gaps_iface<LEPT_GLOBALSC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2K53A238Lept_env<static_agreeC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A235D_kitArw_cells_agree_nwC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A238RT_iface3rtsC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A238RT_iface3ARTC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitions;bv_unsignedC69OSSVerify5KrLib2K53A23=RT_gaps_iface;gp_ssp_keepC1?~~~~~~~~~~~~~~~".   (* [comment removed for export] *)
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
Lemma LIB0_write : forall (m : mem) a bs (n : Z), Z.of_nat (length bs) = n -> 0 <= a -> a + n <= 2^64 ->
  LIB0 m -> (a + n <= 0x216080 \/ 0x216128 <= a) -> LIB0 (write_to_mem m (wa a) bs).
Proof.
ltac2:(KReplay.run1 (kr_t_Lept_env ()) [] "h06__sat5h14__x1h24__x2h32Hah47__arithh54__ffh66__sat4h78__varmaph85__with94cstrh:1xh;1Hh<1mh=1nh>2H1h?2H2h@2H3hA2HdhB2HlhC2HnhD1ahE2bshF1yp;1p;2p;3p;4p;6p;<p;Bp;7p;8g0000j13Tg000Uj1]Tg0013j1VTg001Vj1zTg0028j1\Tg002Xj2YTg0038R0j18Tg003Xj3WTg0042R1j20Tg004Nj16Tg004lj2`Tg005Ij1ETg006Dj1NTg006ij2QTg007Oj1oTg008Gj1ZTg008gj3MTg009Gj4=Tg00:@j1UTg00;8R2j2RTg00;SR3j22Tg00<0j1KTg00<bj3JTg00=fj19Tg00>Ej2>Tg00>_j1bTg00?=j4aTg00?`j2@Tg00@:j3ITg00@`j6STg00AHj1yTg00Amj2xTg00BUj2^Tg00C1j3wTg00CUj2vTg00D6j2rTg00DTj1qTg00E2j4pTg00EPj1nTg00Enj1mTg00FYj2[Tg00G<j3ATg00G_j1lTg00HAj2jTg00Hcj2iTg00IOj3hTg00Inj4kTg00J`j4OTg00KKj1HTg00LGl<GTg00MMj4XTg00Mhl<gTg00NMlBfTg00O3l<eTg00OXj2dTg00P;j4sTg00Pfj7tTg00QJj7cTg00Qnj8uTf0R4#3#3p=1f2R5f1R6'2/04p=_g00RRR7P6g00SJP4C=p=CP7P6g00TLP4C=p=D%34#Np=4%N4#3p=71056/>4p=5g00UPR8/@4p=:g00UnR9P8P8P8P0P0f5R0f4R:f3R;P5P6P4M<gp=TP8P8P8P8P8P8P3P4P6P5P3P;P:P0f6R3f7R<f8R=f9R>MBfp=PP8P8P1P<P1P3P0P:P;P5P6P4M<ep=F1d84p=?P8P6g00VMP4Csp=<P6g00W4R1g00WSR?P?g00X3R@P4g00XSFtp=;P5P1P?P?P@P6P4Fcp=BP;P1P?P?P@P5P6P4Gup=Lg00Y3R1#3RA#3RB#3RC#3#1RD#]RE#V%]C#VRF#z[%\F1YF6#8=W84g00YXRG/0;%6AR;%6DRD'`RH9_:5%E3P2P7P<g00Z6R:g00[>RI%N1#6,QE#o%ZIRJ3MRKC=g00\6,QE#U=MIJRL,C<g00]3,QE#U=MIJRJ,D<'R12<0%31#1#4#4#7#1#1#7#1#1#1#6RI%31#1#4#4#7#1#4#1#7#7#1#6RE/0<35%K==J><#E[P4P7P>P:PKC=f:R:/CL1D:J'RP2f;R2/CL1D2J122>10E275If=R>f<R<#K;J2#E[P41C>Lf>R=/DJ12=<10E=75IP7f@RMf?RN#K;J=ROPIPKC=P7PO%31#1#4#4#7#1#4#1#1#1#1#6RPPLC=RQP7PO%31#1#4#4#7#1#4#1#7#1#1#6RRPJC=RS'RP7PMPIPKPNP=P>P<P2P:P3g00]n#9#9#9#9R3#8RT,2IRU/0NRV12N>RW/0IRX'>%6BRB,2IRY/0NRZ/>XPVPXPZPXP4X:8RZ1064#bXF8X:8RVPUPYPZPZPZP8P8g00^M1264Ca#:X<8X=8RUPIPI%:IPTPBPZPZ%84#:X:9R9P3PB%:BETM:PPNPN%:NRTGFp-0R[/@X9IXXES1YF=RF#yR\%8F,0GRF1x;DR]1^G;R^10GD1^GH[R_[R`10G;Rag00_1RbAw;D6UW3RD10GH\b^3aRaP6g00_M1vG;'@P^eO1R^P_g00`3R;#ZRb%\;R;P81r85P6%q8CpRH%n8Rc%m8Rd1[81R11[8A5A8RA%?IRe'<,;dRf%?E/<1,;d5BdRg%l?R?%?B9A8e/<1,;d=BdfCL1jd@R@P4P5g00`_Rfg00a?Re'@1i45=WfedAh8G6CkRGb5b7b8X18X28124610E475IRE1265Re/0I95Y6[^18^28P4fBfDP0O3R0b4b0b6b0b9CO%HK#8,2I?5NXeM<GPQPSP7PMPPPLPNP=P>P<P2P:P5%93#9#9#9R3#8R5,2PRS/0NRQ10WPRX'>%6CRC,2PRI/0NRK/>XPQPXPKPXPZPVPSPIPZPZPZPUPPPP%:PP5PCPZPZP9P3PC%:CETR3M:PPNPNPTGF1@[X9IXXESP\PFP]P`PDPaP^P_PbP;PHPcPdPgP?%?PR9%?CRS5A8/<1,;d1<A9,;d5BdCLP@PGb5b7b8X18X2810eP95I6\E^18^28P0b4b0b6b0b9CO%HL#8,2P?5NXeM<GP7PMPRPJPNP=P>P<P2P:P612R5R:/0NR210WRRW'>12RCR</0NR>/>WP2PWP>PWPZPVP:P<PZPZPZPUPRPR%:RP5PCP3M:PPNPNPTGF1@[W9IWWESP\PFP]P`PDPaP^P_PbP;PHPcPdPgP?%?RR?=A8S/<1,;d1<A?,;d5BdCLP@PGb5b7b8X18X2810eR95<6\E^18^28P0b4b0b6b0b9CO%HJ#8,2R?5NWeM<GCXCX%EOeWAW@W?P6P4O2n2001000000121000000W;W>P6P4O2n2001000000121000000W;WBW3WCX=8WEXD8W<o"). Qed.
Lemma LIBH_write : forall (m : mem) a bs (n : Z), Z.of_nat (length bs) = n -> 0 <= a -> a + n <= 2^64 ->
  LIBH m -> (a + n <= 0x216080 \/ 0x216128 <= a) -> LIBH (write_to_mem m (wa a) bs).
Proof.
ltac2:(KReplay.run1 (kr_t_Lept_env ()) [] "h02Hah11xh26__sat3h34__x1h44__x2h51mh61nh71Hh82H0h92H1h:2Hdh;2Hlh<2Hnh=7__arithh>4__ffh?6__sat2h@8__varmaphA5__withB1ahC2bshD4cstrhE1yp;1p;2p;3p;9p;4p;<p;6p;8p;Bp;7g0000j13Tg000Uj1DTg0013j1ATg001Vj1sTg0028j1FTg002Xj2LTg0038R0j1:Tg003Xj3BTg0042R1j20Tg00;SR2j22Tg004Nj19Tg004lj2NTg00a_j1MTg005Ij1>Tg006ij2jTg00:@j1hTg008Gj1GTg008gj3`Tg00>Ej28Tg00<0j1CTg00<bj3ETg00bZl9ZTg00=fj14Tg00>_j1YTg00?=j4XTg00?`j25Tg00O3l<UTg00@:j3TTg00@`j6OTg00AHj1PTg00Amj2QTg00BUj2@Tg00C1j3RTg00CUj2STg00D6j2rTg00DTj1qTg00E2j4pTg00EPj1oTg00Enj1nTg00FYj2JTg00G<j3ITg00OXj2<Tg00G_j1gTg00Qnj8fTg00HAj2eTg00Hcj2aTg00IOj3bTg00Inj4cTg00J`j4dTg00KKj1_Tg00LGl<^Tg00MMj4iTg009Gj4]Tg006Dj1KTg00Mhl<kTg00NMlB\Tg00P;j4lTg00Pfj7mTg00QJj7[Tf0R3#3#3p=1g00RRR4f1R5g00cYP3C]p=?%33#Kp=7%K3#3p=6g00UnR6g00UPR7P7P7P0P0f5R0f4R8f3R9f2R:P5P3M<kp=WP7P7P7P7P7P7P2P3P5P:P2P9P8P0f6R2f7R;f8R<f9R=MB\p=VP7P5g00VMP3Clp=;P5g00W4R>g00WSR?P?g00X3R@P3g00XSFmp==P:P>P?P?P@P5P3F[p=Hg00Y3RA#3RB#1RC#3#1RD#DRE#A%DC#ARF#s[%FF1LF5#:=B73g00YXRG/09128:%9BR8%9DRD'NR9'0%M2g00;8%>;g00[>RHg00d`,jE#h%GH3`RH,?;12;0%3A#1#7#7#6#1#1#6#1#1#1#9RE'0%3A#1#7#7#6#1#7#1#6#6#1#9RI/0;'8%C<=E=;#M[P3%>=f:RJ/?H12J</0E10IJ'8f<RKf;RL#C;EJRM#>1?MHRMPKPLPJP=P<P;P2P:P3M9ZP4PK%3A#1#7#7#6#1#1#6#6#1#1#9RKPHPLPJP=P<P;P2P5g00]n#4#4#4#4#4#4#4#4R2#:R;,2KR</0LR412L=/0KR='8%9CRC,2KRN/0LRO/8=P4P=POP=P7P7P1P3X17ROP11053#YXE7X17P<PNPOPOPOP7P7g00^M1253CX,57X57X67PKPK157KP;PCPOPO%:3,57X16P2PC157CEWM:VPLPL157LM<Up-0/5=9T==EO1LFJRJ#P%:J,0G1Q8D1@G8RJ10GD1@G9[RF[10G8R2g00_1R6AR8D5UW010G9\6^02P5g00_M1SG8'5PJeO1PFg00`3RF#G%FFP71r7:P5%q7Cp%o7%n7RFP>P?P?P@1J7ARA1J7B5I7RB1<7E';,=F1<7I/;A,=F5HF%g?1<7KR?1<7C5I7/;A,=F1;B?,=F5HFGf1eF@P3P:g00`_RFg00a?R@'51a3:=BF@dAb7G5Ccb>b@bAX37X471235/0E10I3'810N5125:/0K'8[^37^47P3f>f@P0O3b=b2b?b2bDCd%_H#:,2K/0L/8=eM<^PMeCiW:W9W8P5P3O2n2001000000121000000W7W;W0W<X67WCXB7W5o"). Qed.
(* [comment removed for export] *)
Lemma io_ssp_write : forall (m : mem) a bs (n : Z), Z.of_nat (length bs) = n -> 0 <= a -> a + n <= 2^64 ->
  io_ssp m -> (a + n <= 0x10000 \/ SEGTOP_A <= a \/ (0x216080 <= a /\ a + n <= 0x216128)) -> io_ssp (write_to_mem m (wa a) bs).
Proof.
ltac2:(KReplay.run1 (kr_t_Lept_env ()) [] "p'0h04__p1h16__sat4h24__x1h34__x2h42Hah51gh61xi001xh71Hh87__arithh94__ffh:6__sat3h;8__varmaph<5__with=4cstrh>1mh?1nh@2H1hA2H2hB2HdhC2HlhD2HnhE1ahF2bshG1yp;1p;2p;3p;4p;6p;<p;Bp;7p;8g0000j11Tg000Uj1PTg0013j1NTg001Vj1}Tg0028j1WTg002Xj2UTg0038R0j1ATg003Xj3[Tg0042R1j20Tg00;SR2j22Tg004Nj17Tg004lj2^Tg00e`j1KTg006ij2mTg00:@j1DTg008Gj1ZTg008gj3BTg00;8R3j2<Tg00<0j1HTg00<bj3GTg00=fj18Tg00>Ej26Tg00>_j1aTg00?=j4`Tg00?`j2CTg00@:j3LTg00@`j6RTg00AHj1]Tg00Amj2|Tg00BUj2\Tg00C1j3{Tg00CUj2zTg00D6j2yTg00DTj1xTg00E2j4uTg00EPj1tTg00Enj1qTg00FYj2YTg00G<j3JTg00f[j6pTg00G_j1oTg00HAj2lTg00Hcj2kTg00IOj3jTg00Inj4iTg00J`j4TTg00KKj1STg00g?l<XTg00MMj4hTg00hEj4nTg006Dj1FTg00h_j4gTg00Mhl<fTg00NMlBeTg00O3l<rTg00OXj2sTg00P;j4dTg00Pfj7vTg00iXj7wTg00QJj7cTg00Qnj8bTf0R4#1#1p=:%14#Fp=3%F4#1p=E%F4#1#1#1p=>%F4#Fp=I%14#1#1#1p=;g00RRR5f2R6f1R7P4Cgp=41067/64p=5g00UPR8/C4p=?g00UnR9P8P8P8P0P0f5R0f4R:f3R;P6P7P4M<fp=_P8P8P8P8P8P8P2P4P7P6P2P;P:P0f6R2f7R<f8R=f9R>MBep=MP8P8P1P<P1P2P0P:P;P6P7P4M<rp=Q1s84p==P6g00W4R1g00WSR?P?g00X3R@P8P7g00VMP4Cdg00XSFvp=9P6P1P?P?P@P7P4Fwp=OP6P1P?P?P@P7P4Fcp=@P;P1P?P?P@P6P7P4Gbp=Vg00Y3RA#1RB#:RC#1#:RD#PRE#NRF%PC#NRG#}[%WG1UG7#A=[84g00YXRH/0;12:6%7BR;%7DRI'^RJ'0%K2g00j<PF%1A#:#3#:#E#3#>#E#>#7RKg00[>RL%IA#E#;#I#3#I#3#3#>#7RM,mE#D%ZLRE3BRN54=%D4=BLERO94=M'<X5F12<0RP%:D#;#;#7RDg00jVRQ%1A#:#3#3#E#;#>#;#7RR/0<%1A#:#3#3#>#3#:#E#>#7RS,0P'<75<35%H==G><#K[P4f:R<?4KNA4<MO'<P3f;R3?4KN%D7=BLE943M123>R>10R310>S'<95Q375Df=R>f<R=#H;G3#K[P4A4>KNf>RP%D:=BLE74M12P=RT10RP10TS'<95QP75DPFfAf@RQ#Hf?RT3GRU?4KNA4UMO'<X5FP2%HT=GQPRU?4KN%D2=BLERE94UMP5PQPKPNPTPPP>P=P3P<P6g00]n#8#8#8#8#8#8#8#8RU#ARL,2KR2/0TRO12T>RV/0KRW'6%7CRC,2KRX/0TRY/6WPOPWPYPWP4X68RY1074#aXG8X68ROP2PXPYPYPYP8P8g00^M1274C`#?X>8X?8R2PKPK%?KPLPCPYPY%A4#?X69PUPC%?CE_RUM:MPTPT%?TR9GQp-0RZ/CW9LWWER1UGPRG#]R[%AG,0HRG1|;IR\1\H;R]10HI1\HJ[R^[R_10H;R`g00_1RaA{;I7UW4RI10HJ\a^4`R`P7g00_M1zH;'CP]eO1R]P^g00`3R;#ZRa%W;R;P81y86P7%x8CuRJ%t8Rb%q8Rc1Y8ARd1Y8B5J8RB%=D59cRe%IA#>#3#3#;#;#;#7RA#==9cdRf%=R=9cdPcP1P?P?P@P:EpR:5Oc5@c5@c%o?R?%=KR1%=CRg5J8=9cdA9cB15@cCV1lc@R@P4P6g00`_R1g00a?Rh'C1k46=[1hdAj8H7CiRHb9b;b<X28X38X0Z1247Rh/0DRD10A4RA10R4/<6'6'61276R1/0K95X7[^28^38^0ZP4fDRXfBRi'2/0SPiPXP0O4b8b1b:b1b=CT%SN#A,2K?5TWeM<XP5PQPMPEPTPPP>P=P3P<P712MLR</0TR310VMRV'612MCR=/0TR>/6VP3PVP>PVPYPOP<P=PYPYPYP2PMPM%?MPLPCPUM:MPTPTP9GQ1CZV9LVVERP[PGP\P_PIP`P]P^PaP;PJPbPc%=S99cB9Oc:9@cf9@ceP?%=MR?=J8g=9cdA9cB?5@cCVP@PHb9b;b<X28X38X0Z10hS,<6,6A,6D101M95=7[^28^38^0ZP410RXPiPXP0O4b8b1b:b1b=CT%SE#A,2M?5TVeM<XChCnWBWAW@P7P4O2n2001000000121000000W7X5FP7P4O2n2001000000121100000W7WCW4WDX?8WFXE8W>o"). Qed.

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
ltac2:(KReplay.run1 (kr_t_Lept_env ()) ["Env"] "p'0h01Hh12Hxh22loh33Hinh41nh51Eh62H0h71xh81eh92hih:2AGh;2HPh<1Ph=1ah>1mh?2m'h@1ri001pi011zp;1p;3p;2p;4p;5p;6p;7g0000j17Tg000Uj1NTg0013j1MTg001Vj1`Tg00kSj3ZTg00lMj1XTg00mOR0j2WTg00moj3FTg00nFj3VTg00ncj3UTg00o@j4PTg00BUj23Tg00;8j2GTg00j<j2YTg00;Sj29Tg004Nj1ETg003Xj30Tg0042j2CTg00>ER1j26Tg00?`j2KTg00o\j3HTg0106j5JTg010Sj3BTg008Gj1STg008gj3LTg00MMj4_Tg00hEj4RTg010mj4^Tg0128j6]Tg0133j4QTg006Dj1OTg013Sj6[Tg0140j7\Tf0R2#7#7p=;g00UPR3P3f1R4P2CQp=1f4R5f3R6'Cf2R71942'3'Gp=<P3P3P71942CQp=81C74/G2p=A%72#Op=:%O2#7p==%72#7#7#7p=@A0742g014LR8'6p=Df6R9f5R:;05A0674/62'6p=5A0:56A0742/68'6p=4P5P3P6P7P4P2E[p=>A0342p=21342,G7p=IP3P:P5P6P7P4P2F\p=?1628p=Tp-0\3g00Y3R;#;R<#7R=#7#;#N#M%N=#M#`[R>AZ742%X2P:P4O1[^=31W33R?1142R@g014iRA3Ff7RBP6P2P2P6P7D<RCX73P9P:P5P:P4p,2RTp,2GPP4P3P?P?AV332RDAU33278DX@?RDPACPRA9F?@13629A46'GX93,Y3X23P5P311:2=F?A13729A:7'GX931956R@115@RE=F?ARA134@9A54P1%7;#;#:#:#=#@#=#;#@#ER@%E<R<'1RF1156R650?P?%7;#;#:#:#=#@#=#=#@#ERG%E=R='1RHP6P?%7;#;#:#:#=#;#:#@#@#ERI/1=RJP6%7;#;#:#:#=#;#:#;#=#@#ER;/1=RK=D?6F5P?19@<R6,1@RLA8::5RMP?19G=RN,1GROPMP?19I=RP,1IRQPMP?19;=RR,1;RSPME4F5P711:5R590?FP?P0P3P3P3P2P2n2001100000120101101X8?RMPF119:RTP2D>12<:P?P0P3P3P3P2P4n2001100000120101101X8?R0PF11B9RUP4D>12@Bf8RV,2@P@P2PBPBP2f9RWD<f:RX,2<P?PLf;RY9877RZP?POPZP?PQPZP?PSPZE4F5[]1X23P@P9P9P@PVD<12<WP<1C@WR<19@27IWP?PLA8@@4RZP?POPZP?PQPZP?PSPZE4F5]1X4313V69A@VP<13W6A0?LLR@P?POPLP?PQPLAD?SLF5RZ'613X61K?L9H@ZW6X0<P2DJW1PXP2P4E?W0W1PWP2P:E?W0P2O1b0P2O1b0W5P2O1P?PHP5P?PJP5AD?K5F5P1A0?HTP?PJPTP?PKPTE4P?PLA8BB9R9P?POP9P?PQP9P?PSP9E4F5P2A0?HUP?PMPH11VBR9P2D>12=BP?P0PH11WVRTP4D>12GW12GXPGP2PWPWP2PYD<f<R5,2=P?PLf=R:9877R<P?POP<P?PQP<P?PSP<E4F5[]1X23PGPVPVPGPXD<12=YR<P=1CGYRZ19G27IYP?PLA8GG4R@P?POP@P?PQP@P?PSP@E4F5]1X4313XN9AGXPZ13YNA0?LORGA0?OOR@P?PQPOP?PSPOE4R6'6R['6135N1K?O9H@69BG[W6X0ZP2DJW1P5P2P4E?W0W1PYP2PBE?W0P2O1b0P2O1b0W5P2O1P?PJPUP?PKPUE4P1A0?J9AD?K9P?PLA8WWVRVP?POPVP?PQPVP?PSPVE4F5P2A0?JTP?PMPJ11XWRVP2D>12=WP?P0PJ11YXR9P4D>12IY12I5PIP2PYPYP2P:D<f>RU,2=P?PLf?RB9877RZP?POPZP?PQPZP?PSPZE4F5[]1X23PIPXPXPIP5D<12=:P=1CI:RZ19I27I:P?PLA8II4R[P?POP[P?PQP[P?PSP[E4F5]1X43135P9AI5PZ13:PA0?LQRIA0?OQR[A0?QQRGAD?SQR6'6R@'6RN'613UP1K?Q9HG69B[@9BINW6X0ZP2DJW1PUP2P4E?W0W1P:P2PWE?W0P2O1b0P2O1b0W5P2O1AD?KTP1A0?KVP8P?PLA8YYXRXP?POPXP?PQPXP?PSPXE4F5P2A0?K9P?PMPK115YP2D>P<P?P0PK11:5P4D>12;:12;UP;P2P:P:P2PBD<f@R0,2=P?PLfA9877R7P?POP7P?PQP7P?PSP7E4F5[]1X23P;P5P5P;PUD<12=BP=1C;BR=19;27IBP?PLA8;;4R7P?POP7P?PQP7P?PSP7E4F5]1X4313UR9A;UP=13BRA0?LSRUA0?OSR;A0?QSR7A0?SSR<#TRM'6R9'6RX'6130R1K?S9H<89B7M9B;99BUXW6X0=P2DJW1P0P2P4E?W0W1PBP2PYE?W0P2O1b0P2O1b0W5P2O1P8P?PLA8::5R:P?POP:P?PQP:P?PSP:E4F5P2n010000100X38P2O1n200100001021100011000W3P2O1n200100001021100011000W3P2O1n200100001021100011000W3P2O1n200100001021100011000P?P?PD%S?9L?K9L?J9L?H9L?FCP9F?EePAeP2C_CRCRC^O2X1CX73PWP4O1\C^73eE]W3X43X23W;W:X?>W>W<o"). Qed.

Lemma LIBH_agree : forall (P : Z -> Prop) (m m' : mem), LIBH m -> agree_on P m m' -> (forall a, client_static a -> P a) -> LIBH m'.
Proof using GP.
ltac2:(KReplay.run1 (kr_t_Lept_env ()) ["Env"] "h01ah11Hh22AGh32H1h42H2h52H3h62H4h72HPh81Ph91mh:2m'p;1p;2p;3p;4p;8p;7g0000j11Tg000Uj1LTg0013j1KTg001Vj1STg00a_j1:Tg005Ij1MTg006ij2ATg00:@j1HTg008Gj1OTg008gj3=Tg00kSj3;Tg00lMj1RTg006Dj1JTg004Nj18Tg007Oj1QTg009Gj45Tg00;8R0j2BTg00mOj2PTg003Xj30Tg00>Ej22Tg00?`j2>Tg00o\j3DTg00moj3GTg015oj8<Tg0170j7@Tg010Sj39Tg00MMj4ITg0133j4NTf0R1#1#1p=4g00RRR2f1R3g00cYP1C5p=EP2P3g00SJP1C5p=FP2P3g00TLP1C5p=C%11#Jp=3%J1#1p=6%11#1#1#1p=7g00UPR4P4P3P1CNp=?p-0\4g00Y3R5#4R6#1R7#1#4#LR8#K%L7#K#S[R9%:3P0f2R:#Mg00[>R;g00d`,A8#H%O;R<3=R=,E:f4R>f3R?;;:%R1R@f7RAP3O1[^04%:>[[P1%M>P0P2f5RBg00Z6RC%J5#8,A8#Q==;<RDC5g00\6,A8#H==;<RE,FBg00]3,A8#H==;<R<,CB'Bf6RB/E=f8R;?;ABf;RBP3O1\@^04%:;[[[P1P2PAPCPDC51F;E1C;<'BP0f9R0/FE1C0<f:R0/E=f<RC?;B0f?R0P3O1\@^04%:C[[[P11FBE1CC<f=RC/E=f>=;0CfBP3O1\@^04P2P0%15#4#3#3#6#7#6#4#7#8R@PDC5RCP2P0%15#4#3#3#6#4#3#7#7#8RBPEC5RAP2P0%15#4#3#3#6#4#3#4#6#7#8R8P<C5RF'BRG'BP2P0%15#4#3#3#6#7#6#6#7#8R5P=C5PCPGP2f@RGP0P@PDP;fAR;PGP0P3P1P@%86R61P44R41?@6R6;06%87R7,?5R@=0461?B7RD=0461?87RC=046g014LRH'2'2'21>463Dg014iRI9G46eG<F@PAPFP2PGP0PBPEP>P;PGP0P3P1PBP7A046DA04@DRBA04DDR>A04CD/2HRE'2RF'21>4D9D>E99BF39AG4DIeG<F@P2PGP0P8P<P?P;PGP0P3P1P8P7A046CA04@CR8A04DCR?A04CCR</2HRF'2RB'21>4C9D<H99?F998B39AG4CIeG<F@CICIP2PGP0P5P=P:P;PGP0P3P1P5P7A046@A04@@R6A04D@A04C@/2H'2RH'21>4@9D6H39AG4@IeG<F@CI%:0eW7W2W6W5W4P3P1O2n2001000000121000000W1W3P3P1O2n2001000000121000000W1P3P1O2n2001000000121000000W1X:9W9W8o"). Qed.

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
