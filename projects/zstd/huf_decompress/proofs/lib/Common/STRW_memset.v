(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Lib Require Import Tac Arr Bytes.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Common Require Import StrFun.
From OSSVerify.Proofs.zstd.huf_decompress.lib Require KReplay.
Ltac2 kr_t_STRW_memset () := "I47Corelib4Init9Datatypes4list00K47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00I47Corelib4Init9Datatypes6option00C59OSSVerify5KrLib3Lib3Arr5u8arrC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes6lengthC56Stdlib6ZArith6BinInt1Z6to_natI47Corelib4Init5Logic2eq00c59OSSVerify5KrLib6Common;STRW_memset8ms_factsC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z6of_natK47Corelib7Numbers7BinNums1Z02C56Stdlib6ZArith6BinInt1Z3powI47Corelib4Init5Logic3and00C56Stdlib6ZArith6BinInt1Z3addC59OSSVerify5KrLib3Lib3Mem2waC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics8store_okC56Stdlib6ZArith6BinInt1Z3maxC56Stdlib6ZArith4Znat5Nat2Z7inj_iffC47Corelib4Init5Logic7iff_symK47Corelib4Init5Logic2eq01C46Stdlib9micromega;ZifyClasses5mkrelC46Stdlib9micromega;ZifyClasses7rew_iffC56Stdlib6ZArith4Znat5Nat2Z9is_nonnegC56Stdlib6ZArith6BinInt1Z8max_specC56Stdlib6ZArith6BinInt1Z2ltC56Stdlib6ZArith6BinInt1Z2leI47Corelib4Init5Logic2or00K47Corelib4Init9Datatypes4list01K46Stdlib9micromega6VarMap1t02I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr01K46Stdlib9micromega7EnvRing5PExpr02K47Corelib4Init9Datatypes6option02C46Stdlib9micromega5Tauto8BFormulaC46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundC47Corelib4Init5Logic8iff_reflK47Corelib4Init9Datatypes3nat02K46Stdlib9micromega=RingMicromega5Psatz02K47Corelib7Numbers7BinNums1Z03K46Stdlib9micromega7EnvRing3Pol01K46Stdlib9micromega=RingMicromega5Psatz04K46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega:ZMicromega;ZArithProof02K47Corelib4Init9Datatypes4list02K46Stdlib9micromega6VarMap1t01K46Stdlib9micromega6VarMap1t03K46Stdlib9micromega5Tauto8GFormula03K47Corelib7Numbers7BinNums8positive01K46Stdlib9micromega=RingMicromega7Formula01K46Stdlib9micromega5Tauto8GFormula06K46Stdlib9micromega7EnvRing5PExpr03C46Stdlib9micromega;ZifyClasses;rew_iff_revC47Corelib4Init5Logic8eq_ind_rC59OSSVerify5KrLib6Common6StrFun@u8arr_store_ok_nC1?~~~~~~~~~~~~~~~C46Stdlib9micromega;ZifyClasses5mkappK46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega5Tauto8GFormula08K46Stdlib9micromega5Tauto8GFormula05K47Corelib7Numbers7BinNums1Z01I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01I47Corelib7Numbers7BinNums1Z00I47Corelib4Init9Datatypes3nat00C46Stdlib9micromega8ZifyInst@of_nat_to_nat_eqK46Stdlib9micromega=RingMicromega3Op203C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K47Corelib4Init9Datatypes4unit01I4ELinuxProcessSemantics?LinuxProcessSem<MemImageType7Segment00K47Corelib7Numbers7BinNums8positive03I46Stdlib9micromega:ZMicromega;ZArithProof00K47Corelib4Init9Datatypes3nat01K46Stdlib9micromega:ZMicromega;ZArithProof01K46Stdlib9micromega=RingMicromega3Op201C59OSSVerify5KrLib6Common6StrFun6filledC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib3Mem7mem_invC1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes4prod00C59OSSVerify5KrLib3Lib5Frame5munchC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Frame5wmonoC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib6Common;STRW_memset;ms_store_okC1?~~~~~~~~~~~~~~~C47Corelib5Lists7ListDef6repeatC46Stdlib5Lists4List=repeat_lengthC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics<write_to_memC59OSSVerify5KrLib3Lib3Mem9upd_bytesC1?~~~~~~~~~~~~~~~C47Corelib4Init3Nat3addI47Corelib4Init5Peano2le00C59OSSVerify5KrLib6Common6StrFunAu8arr_write_bytesC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common6StrFun;filled_updZC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib3Mem@upd_bytes_lengthC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib3Mem=mem_inv_storeC1?~~~~~~~~~~~~~~~K46Stdlib9micromega7EnvRing5PExpr07K47Corelib4Init5Logic2or01C59OSSVerify5KrLib3Lib5Frame6insideC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Frame;munch_writeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Frame;wmono_writeC1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic3and01K47Corelib4Init9Datatypes4prod01C46Stdlib9micromega;ZifyClasses6mkapp2C56Stdlib5Arith8PeanoNat3Nat3addC56Stdlib6ZArith4Znat5Nat2Z7inj_addC56Stdlib6ZArith4Znat5Nat2Z6inj_leI47Corelib4Init5Logic5False00".
Import ListNotations.
Open Scope bv_scope.

(* [comment removed for export] *)
Definition ms_facts (A n i : Z) (k : nat) : Prop :=
  (0 <= i /\ i + Z.of_nat k <= n /\ 0 <= A /\ A + n <= 2^64)%Z.

Lemma ms_store_ok : forall segs m A n bs i k a,
  u8arr segs m A bs -> length bs = Z.to_nat n -> ms_facts A n i k -> a = wa (A + i) ->
  store_ok segs m a k = true.
Proof.
ltac2:(KReplay.run1 (kr_t_STRW_memset ()) [] "h01xh14__x1h21Hh32H1h44LEN0h57__arithh64__ffh74__p1h88__varmaph95__with:4__x2h;4__x3h<4__x4h=4cstrh>5cstr0h?1nh@1yhA2z1hB1AhC3ARRhD2HahE2HihF2HkhG3LENhH2_HhI1ahJ2bshK1ihL1khM1mhN4segsp;1p;4p;2p;3p;<p;6p;7p;;p;8g0000j1?Tg000Pj16Tg0015j1TTg001Sj1HTg0026j1wTg002Xj4jTg003Jj2@Tg003jR0j1STg004Jj30j1RTg004dj4[Tg005dR1j11Tg006Dj1UTg006bj2uTg007?R2j24Tg007Zj29Tg0087j1CTg008fj4NTg009fj2=Tg00:Cj2aTg00:fj3^Tg00;Cj28Tg00;]l<MTg00<Bj4\Tg00<ij1ITg00=Nj2ZTg00>0j2KTg00>LR3j25Tg00>hj2GTg00?Bj1YTg00?bj2>Tg00@@j1XTg00@^j1WTg00AIj2VTg00Alj2:Tg00BOj1vTg00C1j2tTg00CSj2sTg00D?j3pTg00D^j4oTg00EPj1nTg00Enj1DTg00FMj2;Tg00G6j1iTg00GTj2hTg00H5j3gTg00H^j3BTg00IGj2OTg00J3j3PTg00JSj1fTg00K1j4QTg00KOj6eTg00L3j1dTg00LXj4ETg00MCj7cTg00Mgj3bTg00NJj4lTg00O5j6mTg00OSl;`Tg00PVl<JTg00Q;j7_Tg00Q_j8qTg00RCj7rTg00RgR4f0R5'5p=3f2R6f1R7'9/55p=2g00SER8g00SeR9705p=Ag00TER:g00TcR;P:P:P0f4R0P1f3R<g00UBP6P7P5M<Jp=]P:P7g00UoP5CEp=<P7g00VVR=g00W5R>P>g00WUR?P5g00X5F_p=7P<P=P>P>P?P6P7P5Gqp=FP;P:P:P:P1P1f5R@P0P<P6P7P5M<Jp=kP6P=P>P>P?P7P5Frp=Lg00XU#?g00YTRA#6RB#6RC#6RD#6#6#6RE#T#HRF%TD#HRD#w[%?Df7RGf6RHP@P<Cj1@D0%S@50;PGPHP0P<C[P2%3@%10=2@Gf8RI#3%UB%UE'uRE92IG'4'4f9RJ/9H#C90F0f<RKf;RLP@PHCN#A[P5%3G%1Gf:RG52I%3LA2LGE'4'4P2%1I=2JL%3KA2KLE'4f=R2/9G#C90FIf@R@f?RMPJPGCN#A[P5%1G=2L2%3Mf>RJ=2ME'419@2#C90FLfCREfBfARNPMPJP2PKPL1@DMRL%S@RO50;%1LRP1=4@RQ50:RRP;P:%R;P1%R:%17%15R150:A0;751a753^X@;X0;PLPP18:PPO1=45X0:RPP@O1P5X0:RSPPP@P@18:@D]R@M<MPGC\RPPR%IJRT%1JRU#3RV1@DNRN#IRD%1N#3RN1Z4ERW1K4E1=4ERX=0:E'415E4A0:X4'4'GRXfDRY,=4RZP:g00Z9R[#YR\%?[R]1>:7%X:R^%W:R_1V:4R`1::ARa'<,7_Rb%v>RcPbCF1t_?RbP5P618891s56#AdAp:47CoR9b6b8b9X1:%35%37[^1:P5PYPKO2b5bAb3b>b=b4P;POA2MU1X?;%12,9JRJ%1OR2'515JQP:P:P3PSP31575#nX@:X0:PJPJ18:JP2PQPSPS18:1X0;POPQP@EkM<MPPPRPTPVPDPNPWPXPZP:p-0RZg00ZeRX#DRW#DRN#D,;:%iA,h:1;:N5g:1;:W1;:X5B:5B:RX5B:g00[DRW'O1OXW=P[\5P[P]P:P:1>:0P6%f:CQP71>:<CQP^P_P_P=P>P>P?P_P=P>P>P?PHEeP:%dA,::RAg00\0RH1::CRCCE,7_5L_1<C`,7_P:PAPHP`CE,7_5L_FcPcP_1::B9b:aRa/<C,7_Pc1<aA,7_CFCFPbP9b6b8b9X1:X::X;:X<:W7A0:6<,4015<4A0:64'4'GA2760A26<0[[^1:^::^;:^<:^7ZP5fFRZ,K4PZP7%1EPYP6PIO7b5bAb3b>b=b4ClPLPGEmP5M;`WDWHWFP7P5O2n2001000000121000000W2WEP7P5O2n2001000000121000000W2WGWCXIFXL;XK:WJX?:XB:WMWNo"). Qed.

Lemma ms_store : forall segs m0 m A n bs cb (Q : Z -> Prop) i k a,
  u8arr segs m A bs -> filled cb bs Q -> length bs = Z.to_nat n ->
  mem_inv segs m -> munch [(A, A + n)]%Z m0 m -> wmono segs m0 m ->
  ms_facts A n i k -> a = wa (A + i) ->
  u8arr segs (write_to_mem m a (repeat cb k)) A (upd_bytes bs (Z.to_nat i) (repeat cb k)) /\
  filled cb (upd_bytes bs (Z.to_nat i) (repeat cb k)) (fun j => Q j \/ (i <= j < i + Z.of_nat k)%Z) /\
  length (upd_bytes bs (Z.to_nat i) (repeat cb k)) = Z.to_nat n /\
  mem_inv segs (write_to_mem m a (repeat cb k)) /\ munch [(A, A + n)]%Z m0 (write_to_mem m a (repeat cb k)) /\
  wmono segs m0 (write_to_mem m a (repeat cb k)).
Proof.
ltac2:(KReplay.run1 (kr_t_STRW_memset ()) [] "h04__x1h14__x2h21nh34__x3h44__x4h52H1h64LEN0h77__arithh84__ffh98__varmaph:5__with;4cstrh<5cstr0h=1jh>2z1h?3SOKh@1xhA1HhB4__p1hC4__p2hD4__p3hE4__x5hF1ahG1AhH2A0hI3ARRhJ2AnhK3FILhL2H2hM2HahN2HihO2HkhP3LENhQ2MFhR2MIhS2MUhT1QhU2WMhV2bshW2cbhX1ihY1khZ1mh[2m0h\4segsh]1yh^2z2p%0p&0p;1p;4p;3p;2p;<p;9p;8p;6p;7p;Bg0000j1bTg000Pj1DTg0015j1gTg001Sj1cTg0026k10NTg002Xj4FTg00\Wj3GTg003Jj25Tg003jR0j1>Tg00]Pj2ITg00^Dj2vTg007ZR1j20Tg00?Bj1qTg00J3j39Tg00^dj3HTg00_Xj3ETg004dk40ETg0087j1`Tg004Jj3Sj1rTg008fj4]Tg00`Lm<06Tg00aOj3@Tg00anj3fTg005dR2j12Tg006Dj1pTg006bj2{Tg007?R3j21Tg00bPj3NTg00cTj3YTg00>0j2;Tg00>LR4j24Tg00:Ck20MTg00:fk30LTg00;Cj2XTg00;]l<nTg00<Bk40KTg00<ij1mTg00=Nj2lTg00?bj2VTg00@@k10HTg00@^k10GTg00AIj2jTg00Alj2UTg00BOk10DTg00C1k20CTg00CSk20ATg00D?k30@Tg00D^k40?Tg00dJj2_Tg00daR5j2aTg00Enj1QTg00FMj2CTg00G6k105Tg00GTk204Tg00H5k302Tg00IGj2PTg00JSk101Tg00K1j4LTg00L3j1dTg00Mgj3MTg00NJj4~Tg00e;l9}Tg00f?k803Tg00g=j4|Tg00h:k608Tg00i4k309Tg00iWk30:Tg00j1k30;Tg00jfm90<Tg00k`j6zTg00lZj4WTg00O5j7yk60>Tg00m5j4xTg00>hj2hTg009fj2wTg00PVm<0BTg00LXj4kTg00Q;j7iTg00Q_j8uTg00mUmB0FTg00H^j3tTg00KOk60ITg00RCk70JTg00MCj7sTg00TcR6f1R7f0R83Sp=<g00TER9P9P7P8Cxp=Jg00SER:g00SeR;7S8p=RP6f4R<f3R=f2R>P7P8J0>p=Bg00RgR?/48p=310>7/48p=714>7/18p=T14>7/18,h=p==1178,1>p=?1w?8p=AAS978p=KP9P6P9P9P0P<P2P=g00UBP>P7P8N<0Bp=oAS98?p=\P>g00VVR0g00W5R@P@g00WURAP9P7g00UoP8Ckg00X5RBFip=6P=P0P@P@PAP>P7P8Gup=8P6P6P6P9P9P9g00n;P2P2P2P1g00n[f5R1P<P=P>P7P8NB0Fp>0=P6P9P5P2P4g00o>P1P<P=P>P7P8M<np>07At978p=:P7P0P@P@PAP8J0Ip=^P9P7g00\0P8Ckp=ZP7P0P@P@PAP8PBFip=[P>P0P@P@PAP7P8K0Jp=OP>P0P@P@PAP7P8Fsp=e1178,h>p>00g00XU#bg00YTR0#DRB#DR4#DR5#D#D#DRC#gS00#cRD%g5#cR5$0N[S01Q01%b5p-0RE\9f:RFf8RGf7RHP1CFf6RI=G1<155H%>G'<f=RJf;RK'I1v99RL10KF,JK%qLRM39f<RN7HJf?ROf>RP;EJPJPNPGPHH0Ef9RQ,0P#`9SDHPQfCRRfARSPQP8C]#RX26fBRTf@RUPOPPPJPFPQPGPHP1P7P8N<06A@5NQ,55RVAf5NQDBPTPUPGPVC]#RP3%3K%2F,0K%3U%pBRV%pC'{RC97UO'17TOfDRWA@5PKRK9NTFRFPS%>N=YOKRKCFPPP8O1PJP8%2N,0J,;8C=X=99GPK155K%>URK'<1IWF10SU,JS=9LM?HRFAEWRF'13?3?P>%3J%2J,0P%3RA7RTC'17TTP3%2P=7OR%3WA7WRC'1fHRFfFRXA@5TORO7NPRYfERZAYRKOROCFPTP8O1PSP8%2U,0SRK,;8C=X=99GTO155O%>WRO'<1IFY10ZW,JZ=9LMfGR[;HYAEF[Y'13?3?P814KZ%3[A7[XC'1P3%3FA7F[CfLR3fJRKA@5XRRY7NTR\fIR]AY[OYRYCFPXP8O1PZP8%2W,0Z,;8C=X=99GXY155Y%>FRY'<1I3\10]F,J]=9LMfKRO;H\AE3O\'13?3?P8%3KA7OKCPD103[#`R\fPR^fNR_P8A@5K[R`,55RaC]#RfQRbfORcA@5OFRd7N7ReP_%>]Rf=Y3dRdCFPOP8O1PKP8%2],0K,;8C=X=99GOd155dfMRd#>Rg'<1Ibe10_dRh,J_=9LM?H^eAEb^e'13?3?]?XFDPcPdP\A@5]X,55C]#RP^10dFRX#`R\=N_`RePdAYOY`RbCFPKP8O1P]P8%2FRi,0],;8C=X=99GKbS02155bS03%>3Rb'<S041I^eS0510d3Rj,Jd=9LMRM?HceS06AE^ceS07'1S08'1S09'1S0:'1P^P_PdPOPFP`PZ155ORe/<b%2eRL%A3Rk'KRlP6P9%r6P2%r9%27%28R2'K1<7820M7840LX]6X@6PePL1X9LPb%A8X@9RLP3O1P8X@9RmPLP3P31X93DoS0;M<nPRH0KRnPl%mFRo%3iRi155dRp#mRq%2p#3Rp1l?cRr1;?c%AcRs/Kc'1PcP?%\sC=Rs%A^RtP9g00Z9Ru#qRv%buRw1V97&0H9Rx&0G9Ry1j9?Rz1U90R{56yR|&0D@R@P|C820CyARAP8P>1X:;20A8>#RdB0@9?7H0?R;b8b9b:X09%38R:%37[^09P8P_PUO2b7b>b5b<b;b6S0<P[1_f81553'aX26Pb1_fF/a8X261_Y[Rf/ab%AFR3%2[R}'0R~/4kPfP~PYP3PmPLPFPF1X9FDoP[P}1X9}J0=PbPkQ0;J07PnPlPoPiPqPpPrPsPtP91l?d1;?d%AdRk/Kd'1PdP?%\kC=%A_P9g00ZeRk#QRb#QR}#QRL#QRm#Q,C9R31C9mRm&050-0491C9L6029RL1C9}R}1C9b1C9kRk':':Rb':':R~':g00[DRf'P1P~f1:}k,:L,:mRm/Pf1:3m/Pf=9uv59u59u59uPwP9P91V9<P>&019RmCLR3P7P91V91P=PmCLCLPxPy1^yH1U94R4,Z{,[y5Oy1^yG1Z{z,[y5Oy5eyP@Py1^yQ%d0,U9R0%dB,U9RQ'Z,[y5OyA6yQz1Z0z,[y5Oy5eyP@Py1U9BRB9M94=6yQP@PyA6yz4P@AM9{BRQ=6y0C8C8C8C8PAP;b8b9b:X09X19X39X49XE9XBEXCEXDE1K8=,11%\8800I1K=1,1GP1P?%\=C=A71=I%3IA7<1I[[[[^09^19^39^49^E9^BE^CE^DEP8fTRE,;?14^?1;?^PEP^P=%2cP7P>P<PPPTO<b7b^bLb>b5b<b;b6C~PePRDBRPPaAf5K[REDBR?M9}Q02Q0:PKPOP]PFP[PWQ0<PPL03Q04Q09Pe1<8gX26PRQ03POPYP`P?C|DBQ05Q08P^P_P\P`PTP8J08Q06Q07PMPcP_PXP`PSPnPlPoPiPqPpPrPsPtP91Pbf=9uvRuPwP91V9>P7PmCLPxPyP|P@PyA6yzBR|P@A6yzQC8C8PAP;b8b9b:X09X19%3>Rz10>=Rm#3[\:^09^19P8P_fSR:PGPUO4b7b>b5b<b;b6P[10_]R]/02R2/4CX26PnPlPoPiPqPpPrPsPtP9PuPwP9P3P71V9=CLR3PxPyAM9{4Ru1j9VQ006099RV56yP@PyAM9B0=6y4R4P@AM9Q0R0=6yVC8C8PAP;b8b9b:X09X19X39X49A78=C14m<10m<R</4C[[^09^19^39^49P8fRRC%2dRVP_P:PHPNO6b7b>b5b<b;b6PaPEDB%2aRH=7Xj9TdXg00o`P[142h9T_]X26PnPlPoPiPqPpPrPsPtP9PvPwP3PxPyP4P@PyP|P@A6y{QA6y0u5OyC8C8PAP;b8b9b:X09X19X39X49A77>=10>1,4<9T>m\z[^09^19^39^49P8PCPVP_P:PNPUO6b7b>b5b<b;b6PaPEDB40:B0;MXHeN90<P^PcP_P\P`PUEzCWCWCWCWCWW?PZPJPNFyWJWHP7P8O2n2001000000121000000WAWOP7P8O2n2001000000121000000WAWNP7P8O2n2001000000121000000b?WMWQWUWSWRWPWKWIXFDXY6XX9WTXW5WVX29XG9WZW[W\o"). Qed.

(* [comment removed for export] *)
Ltac ms_arr_store MF bytes_tac :=
  lazymatch goal with
  | ARR : u8arr ?segs ?m ?A ?bs, FIL : filled ?cb ?bs ?Q, LEN : length ?bs = Z.to_nat ?n,
    MI : mem_inv ?segs ?m, MU : munch _ ?m0 ?m, WM : wmono ?segs ?m0 ?m
    |- evt _ _ (MS _ _ _ _ _ (write_to_mem ?m ?a ?bs0) _) =>
    lazymatch type of MF with ms_facts _ _ ?i ?k =>
     let xs := eval cbv beta iota delta [repeat] in (repeat cb k) in
     let kz := eval vm_compute in (Z.of_nat k) in
     replace (write_to_mem m a bs0) with (write_to_mem m (wa (A + i)%Z) xs)
       by (apply (f_equal2 (write_to_mem m)); [ unfold wa; first [ reflexivity | f_equal; lia | rewrite ?Z.add_0_r; apply Z_to_bv_bv_unsigned ] | bytes_tac ]);
     let ARR' := fresh "ARR" in let FIL' := fresh "FIL" in let LEN' := fresh "LEN" in
     let MI' := fresh "MI" in let MU' := fresh "MU" in let WM' := fresh "WM" in
     destruct (ms_store segs m0 m A n bs cb Q i k _ ARR FIL LEN MI MU WM MF eq_refl)
       as (ARR' & FIL' & LEN' & MI' & MU' & WM');
     change (repeat cb k) with xs in ARR', FIL', LEN', MI', MU', WM';
     change (repeat cb k) with xs;
     cbv beta in FIL'; change (Z.of_nat k) with kz in FIL';
     clear ARR FIL LEN MI MU WM MF;
     repeat match goal with
     | H : store_ok segs m _ _ = true |- _ => clear H
     | H : ov_read_bytes segs m _ _ = Some _ |- _ => clear H
     end;
     let m' := fresh "m" in remember (write_to_mem m (wa (A + i)%Z) xs) as m' eqn:Heqm; clear Heqm; try clear m;
     let bs' := fresh "bs" in remember (upd_bytes bs (Z.to_nat i) xs) as bs' eqn:Heqbs; clear Heqbs; try clear bs;
     rename ARR' into ARR; rename FIL' into FIL; rename LEN' into LEN;
     rename MI' into MI; rename MU' into MU; rename WM' into WM
    end
  end.

Ltac mst i k bytes_tac :=
  lazymatch goal with
  | ARR : u8arr ?segs ?m ?A ?bs, LEN : length ?bs = Z.to_nat ?n |- _ =>
    let MF := fresh "MF" in let SOK := fresh "SOK" in
    assert (MF : ms_facts A n i k) by (unfold ms_facts; lia);
    pose proof (ms_store_ok segs m A n bs i k (wa (A + i)) ARR LEN MF eq_refl) as SOK; unfold wa in SOK;
    zstep; [ ms_arr_store MF bytes_tac | .. ]
  end.

