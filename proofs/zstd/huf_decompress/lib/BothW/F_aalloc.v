(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)


From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Lib Require Import ITree Nodes Decode Arr.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Spec Require Import STree AsanCtrl AsanEmbed.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.BothW Require Import BImg AProto ABase ADepot_iface.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.LibA Require Import StepF.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.BothW Require Import AKit AKit2 AModelFacts F_apoison F_aalloc_s F_aalloc1 F_aalloc2 F_aalloc3.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Common Require Import RunDraw.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib Require KReplay.
Ltac2 kr_t_F_aalloc () := "C4ELinuxProcessSemantics5Riscv7Prelude5bvmapC47Corelib4Init5Logic8eq_ind_rK47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00I47Corelib4Init9Datatypes6option00I47Corelib4Init9Datatypes4list00C5ARocqVerifyHarness?AgentSubmission5BothW9F_apoison<poison_cellsC5ARocqVerifyHarness?AgentSubmission3Lib5Frame5munchC5ARocqVerifyHarness?AgentSubmission3Lib5Frame5wmonoI47Corelib4Init9Datatypes4prod00C56Stdlib6ZArith6BinInt1Z2leI47Corelib4Init5Logic2or00I47Corelib5Lists7ListDef6Forall00C5ARocqVerifyHarness?AgentSubmission3Lib5Frame=disjoint_fromK47Corelib4Init9Datatypes4list01K47Corelib4Init9Datatypes4list02K47Corelib4Init9Datatypes4prod01K47Corelib4Init9Datatypes3nat02K46Stdlib9micromega=RingMicromega5Psatz02K46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega:ZMicromega;ZArithProof02K46Stdlib9micromega6VarMap1t02K46Stdlib9micromega6VarMap1t03K46Stdlib9micromega6VarMap1t01I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr02K47Corelib7Numbers7BinNums8positive01K47Corelib4Init9Datatypes6option02C46Stdlib9micromega5Tauto8BFormulaK47Corelib4Init5Logic2eq01C46Stdlib9micromega:ZMicromega=ZTautoCheckerI47Corelib4Init5Logic2eq00C46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundK47Corelib4Init5Logic3and01C47Corelib5Lists7ListDef:Forall_indK47Corelib7Numbers7BinNums1Z02C45stdpp9bitvector;definitions7Z_to_bvK5ARocqVerifyHarness?AgentSubmission3Lib5Cells4cell04I47Corelib4Init5Logic3and00C5ARocqVerifyHarness?AgentSubmission3Lib5Cells8cells_wfC5ARocqVerifyHarness?AgentSubmission3Lib5Cells;cells_bytesC5ARocqVerifyHarness?AgentSubmission3Lib5Cells7cell_wfC47Corelib4Init9Datatypes6lengthC56Stdlib6ZArith6BinInt1Z3powC47Corelib4Init5Peano2ltC56Stdlib6ZArith6BinInt1Z6of_natC5ARocqVerifyHarness?AgentSubmission3Lib4Step8rw_cellsC5ARocqVerifyHarness?AgentSubmission3Lib5Cells8cells_atC5ARocqVerifyHarness?AgentSubmission3Lib3Mem5wr_atC5ARocqVerifyHarness?AgentSubmission3Lib5FrameBrw_cells_transportC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics5wviewC56Stdlib6ZArith6BinInt1Z3addC5ARocqVerifyHarness?AgentSubmission3Lib3Mem8bytes_atC5ARocqVerifyHarness?AgentSubmission3Lib3Mem3mrdC47Corelib4Init9Datatypes3fstC47Corelib4Init9Datatypes3sndK46Stdlib9micromega7EnvRing5PExpr03K46Stdlib9micromega=RingMicromega7Formula01K46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega5Tauto8GFormula06K46Stdlib9micromega5Tauto8GFormula08K5ARocqVerifyHarness?AgentSubmission3Lib5Cells4cell01C5ARocqVerifyHarness?AgentSubmission3Lib5Cells:cells_sizeC5ARocqVerifyHarness?AgentSubmission3Lib3Mem2waC46Stdlib5Lists4List9nth_errorC56Stdlib6ZArith6BinInt1Z2ltC47Corelib4Init5Logic3notK46Stdlib9micromega7EnvRing5PExpr01I47Corelib7Numbers7BinNums1Z00C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K46Stdlib9micromega=RingMicromega3Op203K47Corelib4Init9Datatypes4unit01I5ARocqVerifyHarness?AgentSubmission3Lib5Cells4cell00C5ARocqVerifyHarness?AgentSubmission5BothW4BImg5bsegsK47Corelib4Init5Logic4True01K47Corelib7Numbers7BinNums1Z01K47Corelib7Numbers7BinNums8positive03C5ARocqVerifyHarness?AgentSubmission3Lib5Frame3ivlC5ARocqVerifyHarness?AgentSubmission5BothW5ABase7AIMG_HIC5ARocqVerifyHarness?AgentSubmission5BothW5ABase7AIMG_LOI46Stdlib9micromega:ZMicromega;ZArithProof00K47Corelib4Init9Datatypes3nat01K46Stdlib9micromega:ZMicromega;ZArithProof01I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01I47Corelib4Init9Datatypes3nat00I4ELinuxProcessSemantics?LinuxProcessSem<MemImageType7Segment00C56Stdlib6ZArith6BinInt1Z4log2C56Stdlib6ZArith6BinInt1Z6eq_decI47Corelib4Init6Specif7sumbool00C56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z;log2_nonnegC56Stdlib6ZArith6BinInt1Z;lt_ge_casesC56Stdlib6ZArith6BinInt1Z<log2_le_monoC56Stdlib6ZArith6BinInt1Z9log2_pow2C47Corelib4Init5Logic6eq_indK46Stdlib9micromega5Tauto8GFormula03C47Corelib4Init5Logic9False_indK46Stdlib9micromega=RingMicromega3Op205I47Corelib4Init5Logic5False00C56Stdlib6ZArith6BinInt1Z4landC56Stdlib6ZArith6BinInt1Z3lorC56Stdlib6ZArith6BinInt1Z:lor_nonnegC56Stdlib6ZArith6BinInt1Z;land_nonnegK47Corelib4Init5Logic2or01K47Corelib4Init5Logic2or02C56Stdlib6ZArith6BinInt1Z3maxC56Stdlib6ZArith6BinInt1Z9log2_landC56Stdlib6ZArith6BinInt1Z3minC56Stdlib6ZArith6BinInt1Z8max_specC56Stdlib6ZArith6BinInt1Z8min_specC56Stdlib6ZArith6BinInt1Z8log2_lorc5ARocqVerifyHarness?AgentSubmission5BothW8F_aalloc?lt_pow2_of_log2C5ARocqVerifyHarness?AgentSubmission5BothW9F_aalloc2:hdr_b1_midK46Stdlib9micromega5Tauto8GFormula05K46Stdlib9micromega=RingMicromega3Op201".
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Local Ltac band_lin :=      
  repeat match goal with H : iclr ?a ?n |- _ => unfold iclr, AIMG_LO, AIMG_HI in H end.
Local Ltac with_band H tac :=
  let H' := fresh H in pose proof H as H'; unfold sclr, iclr, ablk, KLS, AIMG_LO, AIMG_HI in H'; tac; try clear H'.


Section CANSEC1. Context {rc : runConstT}.

Lemma poison_cells_frame_b : forall m m' W,
  poison_cells m -> munch W m m' -> wmono bsegs m m' ->
  Forall (fun iv => AIMG_HI <= fst iv \/ snd iv <= AIMG_LO) W -> poison_cells m'.
Proof.
ltac2:(KReplay.run1 (kr_t_F_aalloc ()) ["CANSEC1"] "p'0h01Hh12H0h22H1h31Wh41Ah51mh62m'h72csh84segsh91ih:2H2h;7__arithh<4__ffh=8__varmaph>5__with?4__x1h@4__x2hA4__x3hB4__x4hC4__x5hD4__x6hE1nhF1DhG2HAhH2HBhI2HWhJ2IHhK2MUhL2P1hM2P2hN2P3hO2P4hP2P5hQ2P6hR2P7hS2PChT2WMhU2hihV2ivhW1lhX2lohY1xi001pi011zp%0p&0p;1p;3p;2p;4p;7p;:p;8p10000p4p7210p1000\p4p710p8g001:j12Tg001_k101Tg002=j1|Tg002`k10TTg003Bj1gTg003bk105Tg004ck303Tg005Wk300Tg006KR0k20DTg006kj20Tg007Gj2cTg007ak308Tg008Bj3NTg009>j1zTg009^j3fTg00:>k406Tg00:^j1kTg00;=j2dTg00;fj3jTg00<Ok202Tg00=;j2vTg00=Yj4uTg00>7k10GTg00>Uk10ETg00?3k10CTg00?^j2^Tg00@Aj11Tg00@fj1}Tg00AHk20<Tg00Ajk20;Tg00BDk209Tg00C0j3mTg00CJk30STg00Cik40RTg00D[j4:Tg00E6k70QTg00EYj1ATg00F7j2xTg00F]k10KTg00GRR1j23Tg00Gmj1DTg00Hdj1@Tg00I^j1<Tg00JTj2GTg00K4k20FTg00KQj2JTg00Kij1rTg00LIj4UTg00M?j4sTg00N6j4qTg00Nhm:0BTg00Oij3pTg00Pfj2BTg00QCj4oTg00R8j3nTg00Rhk30@Tg00SEk30?Tg00Sbk30>Tg00TEk40HTg00U0k70=Tg00UTk70ITg00V8k80JTg00V\k107Tg00WQk10LTg00XJk10MTg00Y9k30:Tg00YWk20NTg00Z3k10OTg00ZLk20PTf0R2#2#2p=\g00ZoR3@0@32p=tB0?332p={f2R4f1R5'B/02p=>B0>352p=OP4g00[MR6g00[lR7P7g00\LR8P3P5g00\lP2H0Hg00]SK0=p=5P4P6P7P7P8P5P2K0Ip=~f3R9P6P7P7P8P4P5P2L0Jp=y%22#1p=9%12#2p=6%22#2#2#2p=E%12#1p=b%22#2#2#Ap=R%22#1#1#1p=F%12#1#2#2p=h%22#1#2#2p=a%22#A,x5$07p=S%12#1#2#1p=`%22#1#2#1p=l%12#1#1#1p=Q1x52$07p=eg00^3R6?f52p=;g00^hR:P4P5P2CUp=4%12#1#1#1#1#1#1#1p=_%22#Ap>04P:f5R;f4R<P9CUP:P4P5P2CU'3p=]P:f6R=P;P<CUP:P9P4P5CU/32'3p=8P:P9P4P5CU/32p=wP:P4P5P2Csp=Y&0L2#rp=?P:P4P5P2Cqp=XP:P4P5P2Cop=WP5P2g00_]R>P>C:p=TP4%D5P>P2C:p=Pg00`9R?/02p=C%r5,B4/02p=M1B52$0Mp=7An:52p=[B0:4529m<9p=L20N52,34p=KAm452$0Op=H20P32p==f7R@13=;P<P9P4P5P2C:C:p=IAp:52p=VP=P;P<P9P4P5C:P2C:p=ZP=P;P<P9P4P5P2C:C:p=iP<1394P5P2C:p>0Ag00`WRA#2RB#2RC#2S00#2S01#\RD$01RE#|Q00$01RF#|RG$0TRH[RIg00a<#gRJ&054B03594B00:<920D33RKg00anRL%t2'0%{2g00bfRM'0'cXVKRN<08910M5ROA>45LRPPKPN%gKRQAN2<9W3P>%zK?N94eP0P3P3%t5,0L%{5/0M'cB08KN5RNf8R0=N4@AfK<9f9R>;N0[[[^WQP2P3P3P4P5H06RR#t,0L%{R/0M'cf;RRf:RS5N4f<RT?>R;10<T'cAN9TRg00c^RUg00dJRV#kRW#kRX#kRY,d31d3XRX1d3V5j35j3g00diRV+02%kY,d31d3W9j3X5j3002V%zURV5fU3f%gURUP3P31v3<P41v3=CuP5P31v3;P9&0G3RXCuCu&0E3RW&0C3RY1^3ARZ1^3B'OR[%1B,^3R\55Y%}7R7PY%1AR]#2R^,^3R_=5YZP7PY1^3]R`95Y\1^3CRC=5Y_5~YP7A5Y[`A5YCZ5~YCyCyCy20<Y8R8P2P4g00eURCg00f5RZ+0;20924=mCZdB0S3?5H0RRZb<b=b>X?3X@3XA3XB3XC3XD3A>25<10=510=<10;@'cA>9<;10=9'c[[[^?3^@3^A3^B3^C3^D3P2PMPLP;P=PTf=S02PSPRP9O9b;P2C:P3P3P;P<H06=fK9?NTReWJX:NW2X3QXU3XX3P5P2O2n2001100000121101101XYKP0P<K0QWHWGXE3X43AN094\P\O^E3^43P1%9A#6#9#E#6#\#b#RRO%2A#6#9#F#h#9#a,SERP%9A#6#b#`#F#h,SERK%FA#a#l#Q#RRQ,eERN%9A#`#F#Q#a,SERL%9A#`#F#Q#6#\,SERM%FA#l#Q#h#RRC,eER`%z6R[';R7';R_';R\';Ra';Rb';Rc54@RdP@%9A#6#9#E#6#6#9#RRe%9A#6#9#Q#`#a,SES03/;[RfP@%9A#6#F#Q#a#RRg%9A#l#6#6#\#6#h,SES04%lA#F#E#6#b#6,SES05/;[S06';RhP@PQ%b]#Q#_R]#\#E#E#E,SES07/;[RiP@PC%1]#b#Q#_#_#_R]#A,eES081eE?S09Q09/;[S0:';S0;';R?P@%9A#h#`#6#6#b#6$04Rj%AAS0<,xF$0KS0=/;[RFP@%2A#6#9#F#`#a#RRk%1]#_#_#A,eES0>/;[REE]F8F8R]13d]P<A4>OcPSPePfPSPgPhPSPQPiPSPCP?PSPjPFPSPkPEE]F8F8P1A4RefR]PRPgPhPRPQPiPRPCP?PRPjPFA4RkEF8F8RdPRPOPc13]dCwP2Q02?4eff>RdPgPhPdPQPiPdPCP?PdPjPFA4dkEF8F8P1f?Rd?4ghR]PdPQPiPdPCP?PdPjPFPdPkPEE]F8RlPdPOPcPdPePf13]lF8P2fAS0??4ghfBRlPQPiPlPCP?PlPjPFPlPkPEE]F8P1fCRl?4QiR]PlPCP?PlPjPFA4lkEF8RmPlPOPcPlPePfPlPgPh13]mCwF8P2fES0@?4QifFRmPCP?PmPjPFA4mkEF8P1fGRm?4C?R]PmPjPFPmPkPEE]RnPmPOPcPmPePfPmPgPhPmPQPi13]nF8F8P2fIS0A?4C?fJRnPjPFPnPkPEE]P1fKR]?4jFRoA4]kERpP]POPcP]PePfP]PgPhP]PQPiP]PCP?13opCwF8F8P2fMRp?4jFfNRo?4kES0BA4oOcA4oefS0CA4oghS0DA4oQiS0EA4oC?S0FA4ojFS0GQ0B'3S0H'3S0I'3S0J'3S0KAYoOc%?cRq9XoO%Dc%@cRr9WoO%<P%<K%<N%<L%<M%<`%D[R['T7P77P_7P\7Pa7Pb%COS0L1GGrRb%AB%AD+0FRB5MORag00fUR\1J2bPHfPRb%r5R_,7O'[PGPrP5DL[]9Rrg00g4#gR7%g6R6P;P9P5P2CUR`B03;<9RMB00@;<RL%?99N@<RNP1P>P=P;P<CsRKP>P=P;%?<RPCqRsPSP@P=%?;RtCqP>P0P@P=P;P<P9P4P5P2N:0BRuP2n2001000000120000000UUUUW7X43X6IX5IX3JW8RvPs\N\L\M\`^76^43^6I^5I^3J^87RwP1%C;S0MA>;PBS0N%C2RP?K2t17@59pR0%}GRx5HH[^93S0O'3S0P%C=PSP>P0P@P=P;P<P9P4P5P2O:RyP5n2001000000120000000VNVLVMV`X76X43X6IX5IX3JX87S0QQ0M\N\L\M\`^76^43^6I^5I^3J^87S0RP2P:fORzfQR{PbPOPcPmPpfLRmPnPOPqPVPUPXPW%2D#\#E#RRD#=R|%=OR}55YP8PZb<b=b>10DOR~P2b;P~eS0SPVPUPXPW%\^S0T$04R^#=,O}%1A#E#F#6#E#E#RRA#=R}55YP8PZb<b=b>A>O^AP2b;1BOqS0U/0AeS0VO4O:b1b0S0WPaPrP1PKPsPSP@P=P;CsPuP5n2001000000120000000VNVLVMV`X76X43X6IX5IX3JX87RuPK\N\L\M\`^76^43^6I^5I^3J^87RKP1%D<P>P=P;%@<RsCoRrPSP@P=%@;RSCoPyP2n2001000000120000000VNVLVMV`X76X43X6IX5IX3JX87RaPr\N\L\M\`^76^43^6I^5I^3J^87RrP1Q0M1GGs=M;BRs1GGSRS,J2PH17@_9nR0PG%@=R^P5DL[^9\S0X'3R~AM=SBRS1GG^,J2PH170_9nT>PG%@@P5DL[^9\S0Y'3PyP2n2001000000120000000VNVLVMV`X76X43X6IX5IX3JX87R^P~\N\L\M\`^76^43^6I^5I^3J^87R~P1PsQ0XPSPyP5n2001000000120000000VNVLVMV`X76X43X6IX5IX3JX87S0ZPs\N\L\M\`^76^43^6I^5I^3J^87S0[P2P:P{fSS0\fRRSPOPcQ0APzPoPmPOPqQ0SQ0VO4O:S0Ab:b2b1b0PuPKPaPrP^P~P1PsQ0XQ0YPyP2n2001000000120000000VNVLVMV`X76X43X6IX5IX3JX87S0YQ0X\N\L\M\`^76^43^6I^5I^3J^87S0XQ0Ab:b2b1b0GIQ0LQ0U/0BS0UAKP2q17O5,Vb=HHx[^93RsQ0WQ0UPsPvPwP1Q0MQ0PA>=tBS0M%?=9KP217059pT>=HHx[^93S0U'3PyP2n2001000000120000000VNVLVMV`X76X43X6IX5IX3JX87RtQ0P\N\L\M\`^76^43^6I^5I^3J^87RsP1Q0NQ0OQ0MPyP5n2001000000120000000VNVLVMV`X76X43X6IX5IX3JX87S0MQ0N\N\L\M\`^76^43^6I^5I^3J^87S0PP2P:PbPSP{POPcfHPoPpP]POPqQ0SQ0VO4O:Rqb2b1b0PvPwPtPsP1Q0NQ0OQ0UPyP2n2001000000120000000VNVLVMV`X76X43X6IX5IX3JX87RyQ0O\N\L\M\`^76^43^6I^5I^3J^87R7Pqb2b1b0GIFZQ0CQ0KAYoef%?fRq9Xoe%Df%@fRJ9WoeQ03#</T[%CeR61GGJR`=MeBRM1J2`PH17e_,[bPGPJP5DL[^9\RJ'3PvPwQ0QQ0RP2P:PzP{PbPePfPlPpPmPnPePqPVPUPXPW%=eRl95Y|P8PZb<b=b>10DeR`P2b;P`eR`PVPUPXPWQ00#ARL#=RN,Ol=5Y}P8PZb<b=b>A>eLAP2b;1BeqRl/0AeR1O4O:b1b0ROPMPJPuPKPaPrP^P~Q0ZQ0[P2P:P{Q0\PSPePfQ0@PzPoPmPePqP`P1O4O:RJb:b2b1b0PuPKPaPrP^P~Q0YQ0XPJb:b2b1b0C:FiP610lBRlAKP2q17e5,Vb=HHx[^93R6POPlP6PvPwPtPsQ0MQ0PP2P:PbPSP{PePffDPoPpP]PePqP`P1O4O:R1b2b1b0PvPwPtPsPyP7P1b2b1b0GIQ0DQ0JAYogh%?hR19Xog%Dh%@hR`9WogQ04#<Q06Q05#</T[3P%CgRq1GG`Re=MgBRf1J2ePH17g_,[bPGP`P5DL[^9\R`'3PvPwQ0QQ0RP2P:PzP{PbPgPhPdPpPmPnPgP1PVPUPXPW%=gRd95Y|P8PZb<b=b>10DgReP2b;PeeRePVPUPXPWQ01#AR6#=,Od=5Y}P8PZb<b=b>A>g6AP2b;1Bg1R6/0AeRdO4O:b1b0RlPfP`PuPKPaPrP^P~Q0ZQ0[P2P:P{Q0\PSPgPhQ0?PzPoPmPgP1PePdO4O:R`b:b2b1b0PuPKPaPrP^P~Q0YQ0XP`b:b2b1b0C:FiPq106BR6AKP2117g5,Vb=HHx[^93RqPlP6PqPvPwPtPsQ0MQ0PP2P:PbPSP{PgPhf@PoPpP]PgP1PePdO4O:Rdb2b1b0PvPwPtPsPyP7Pdb2b1b0GIQ0EQ0IAYoQi%?iRd9XoQ%Di%@iRe9WoQQ07#</T[%CQR11GGeRg=MQBRh1J2gPH17Q_,[bPGPeP5DL[^9\Re'3PvPwQ0QQ0RP2P:PzP{PbPQPiPRPpPmPnPQPdPVPUPXPW%=QRR95Y|P8PZb<b=b>10DQRgP2b;PgeRgPVPUPXPW1ORN=5Y}P8PZb<b=b>A>QLAP2b;1BQdRR/0AeRqO4O:b1b0R6PhPePuPKPaPrP^P~Q0ZQ0[P2P:P{Q0\PSPQPiQ02PzPoPmPQPdPgPqO4O:Reb:b2b1b0PuPKPaPrP^P~Q0YQ0XPeb:b2b1b0C:FiP110RBRRAKP2d17Q5,Vb=HHx[^93R1P6PRP1PvPwPtPsQ0MQ0PP2P:PbPSP{PQPiPTPoPpP]PQPdPgPqO4O:Rqb2b1b0PvPwPtPsPyP7Pqb2b1b0GIQ0FQ0HAYoC?%??Rq9XoC%D?%@?Rg9WoCQ08#<Q0;Q09#<RdQ0:1Td[3P3P%CCRd1GGgRQ=MCBRT1J2QPH17C_,[bPGPgP5DL[^9\Rg'3PvPwQ0QQ0RP2P:PzP{PbPCP?P@PpPmPnPCPqPVPUPXPW%=CR@95Y|P8PZb<b=b>10DCRQP2b;PQeRQPVPUPXPWQ0T#ARi#=,O@=5Y}P8PZb<b=b>A>CiAP2b;1BCqRi/0AeR@O4O:b1b0R1PTPgPuPKPaPrP^P~Q0ZQ0[P2P:P{Q0\PSPCP?P>PzPoPmPCPqPQP@O4O:R>b:b2b1b0PuPKPaPrP^P~Q0YQ0XP>b:b2b1b0C:FiPd10iBRiAKP2q17C5,Vb=HHx[^93RdP1PiPdPvPwPtPsQ0MQ0PP2P:PbPSP{PCP?P0PoPpP]PCPqPQP@O4O:R@b2b1b0PvPwPtPsPyP7P@b2b1b0GIQ0GQ0BAYojF%?FR@9Xoj%DF%@FRQ9WojQ0=#</T[%CjRq1GGQRC=MjBR01J2CPH17j_,[bPGPQP5DL[^9\RQ'3PvPwQ0QQ0RP2P:PzP{PbPjPFP9PpPmPnPjP@PVPUPXPW%=jRC95Y|P8PZb<b=b>10DjR?P2b;P?eR?PVPUPXPWQ0<#=,OC=5Y}P8PZb<b=b>Q0<=>jAP2b;1Bj@RC/0AeRdO4O:b1b0RiP0PQPuPKPaPrP^P~Q0ZQ0[P2P:P{Q0\PSPjPFP;PzPoPmPjP@P?PdO4O:R;b:b2b1b0PuPKPaPrP^P~Q0YQ0XP;b:b2b1b0C:FiPq10CBRCAKP2@17j5,Vb=HHx[^93RqPiPCPqPvPwPtPsQ0MQ0PP2P:PbPSP{PjPFP<PoPpP]PjP@P?PdO4O:Rdb2b1b0PvPwPtPsPyP7Pdb2b1b0GIAYokE%?ERd9Xok%DE%@ER?9WokQ0>#</T[%CkR[1GG?R@=MkBRj1J2@PH17k_,[bPGP?P5DL[^9\R\PvPwQ0QQ0RP2P:PzP{PbPkPEP4PpPmPnPkPdPVPUPXPW%=kRn95Y|P8PZb<b=b>10DkRDP2b;PDeRDPVPUPXPW1OnN=5Y}P8PZb<b=b>A>kLAP2b;1BkdRL/0AeRAO4O:b1b0RZPjP\PuPKPaPrP^P~Q0ZQ0[P2P:P{Q0\PSPkPEP<PzPoPmPkPdPDPAO4O:Rmb:b2b1b0PuPKPaPrP^P~Q0YQ0XPmb:b2b1b0GIP[10LBRLAKP2d17k5,Vb=HHx[^93R3PZPLP3PvPwPtPsQ0MQ0PP2P:PbPSP{PkPEP9PoPpP]PkPdPDPAO4O:RAb2b1b0PvPwPtPsPyP7PAb2b1b0GIFZFZFZFZFZFZI0AWRWQP5P2O2n2001000010121000000W0WPP5P2O2n2001000010121000000W0WOP5P2O2n2011000010121000000W0WNP5P2O2n2011000010121000000W0WMP5P2O2n2011000010121000000W0WLP5P2O2n2111000010121000000&05=ebFWIWTWKWSW3X6IW5o"). Qed.
Lemma lt_pow2_of_log2 : forall a k, 0 <= a -> Z.log2 a < k -> a < 2 ^ k.
Proof.
ltac2:(KReplay.run1 (kr_t_F_aalloc ()) ["CANSEC1"] "p'0h04__x1h17__arithh24__ffh38__varmaph45__with54__x2h62Hah72Hlh81Hh94__p1h:1ah;1kh<1Gh=1Kh>1Lh?1ei001eh@1ni011nhA1ohB1si021sp;2p;1p;3p;4p;8p;6p;7p10000p4p7210g000\R0p4p710p8g006kj20Tg00h3j12Tg00YWj21Tg00hQj2FTg00Z3j1:Tg00i1R1j2UTg001:j1NTg00EYj1ITg00K4j25Tg009>j1ETg003Bj1DTg00>7j1CTg00>Uj1`Tg00?3j1[Tg00ZLj2BTg00AHj2VTg00Ajj2TTg00BDj2QTg00C0j3=Tg00CJj3MTg00Cij4LTg00=;j2>Tg00?^j29Tg00@fj1HTg00iQj4GTP0j8JTg00j9j1KTg00:^j1@Tg00;=j28Tg00;fj3?Tg00<Oj2OTg009^j3PTg00=Yj4;Tg00@Aj1RTg00j^j2STg007GR0j2_Tg00kCj3^Tg00kij2]Tg00lLj6ZTg00lhj6YTg00mLj2XTg00TEj4ATg00U0j7WTg00V8j8\Tg00ZoR2f0R3g00`9R43=p=<P2f1R5g00mkP3CAp=7P5g00[MR6g00[lR7P7g00\LR8P3g00]SFWp=3P2P5g00\lP3CAp=6f3R9P6P7P7P8f2R:P5P3G\p=41045R;%2:/151F94%<9R<%:<'UP1f4R1#<R<%:<f5R<g00`WR=#NR>#IR?/51'1P3%<<R@P2P41043RA%25f7RB'1f8RC,5?RD,1:]7]6X:21044%24f6RE'1P?PBg00c^RF#ERG%DFRH%C2RI%`2RJ%[2RK1B24RL1B2?'7'31VK8RMP3P:g00eURNg00f5RO'T1Q3:==NOdAM245CLROb2b3b4114?P3b1PGPH1>25RNPJPK192=RP,7L,3K%H7RQ16LP,3KRRC4PMPOb2b3b4X021143P;[^02P3PCP5O2b1CGW7W6PEP3P1P9GJW?P3O1%:@%KE%2E,04g00dJR@#@R9#@,821829182@5?25?2g00di'O=PFGPHP2PIP51>2:RFC;PJPK%R=,92R=,6L,3KPQPK17=P,3KPQPRC4C4PMPOb2b3b4X02X5211:5104:[\;^02^52P3%2CPBP5P<O4b1b8104<15?ERE,SB11BE10EB'_P015?BRB,1C10BCf9RB/1DRCP3P3X>CP3O110DBf:RD15?BRC'1P2%2Cf;R0#2,03X;2PGPHP2PFP5PIC;PJPK192>R>,6P,3KRPPQPPC4PMPOb2b3b4X02X521035105:[^02^52P3P015?DP5O3b19^CDPBPGPHPNPJPKPRPQPRC4PMPOb2b3b4X02P;\A^02P3PDP1O2b1,]BEZ%2D,0Bp-0RDPGPHP2PNP:PFC;PJPK16=>,3KPQPK17>=,3KPQPKP6P7P7P8P1EYC4C4PMPOb2b3b4X02X52W91053115:P1[[^02^52^9DP3g00nRP0f<#2P5PBO5b1b8'XW<P3O1n200100000021000011000bAb=W@P3O1n200110200021010011101bBW7W6X;2X:2o"). Qed.
Lemma hdr_b1_mid_range : forall b1, 0 <= b1 -> 0 <= hdr_b1_mid b1 < 256.
Proof.
ltac2:(KReplay.run1 (kr_t_F_aalloc ()) ["CANSEC1"] "h07__arithh11Hh24__ffh38__varmaph45__with54__x1h65heq_xh71ah81bh91zh:2L1h;4__p1h<4__p2h=4__p3h>4__x2h?4__x3h@4__x4hA2A0hB2H2hC2H3hD2HbhE2X0hF2b1hG1xhH2z2hI2z3p;1p;2p;3p;4p;6p;7p;8p10000p4p7210g000\R0p4p710p8g00@Aj11Tg001:j15Tg00EYj19Tg00noj22Tg00oMj28Tg00GRR1j2ATg00ojj2]Tg007Gj2<Tg010Nj2XTg009>j1VTg003Bj1qTg00=;j2MTg00>Uj1nTg00?3j1gTg00ZLj2RTg00?^j2LTg00@fj1bTg00AHj2`Tg00Ajj2>Tg00BDj2_Tg00C0j3NTg00CJj3^Tg00Cij4\Tg0113j3[Tg00>7j1ZTg00D[j4PTg011Mj3WTg00YWj26Tg00h3j13Tg011gj2FTg012Dj4pTg012gj2ETg006kj27TP0j6UTg013Dj2oTg013fj2mTg00:^j1KTg00;=j2CTg00;fj3GTg00<Oj2TTg009^j3STg00=Yj4JTg00TEj4HTg00lLj6fTg014Hj4eTg014jj4dTg015mj1hTg00U0j7cTg00V8j8iTg016lj7jTg00lhj6kTg00UTj7lTg00`9R0f0R2'7p=0%12#1p=a%12#1#1#1#1#1#1#1p=;g00ZoR3f1R4g00\lP2CHp=@P4g00[MR5g00[lR6P6g00\LR7P2g00]SFcp=4f3R8P5P6P6P7f2R9P4P2Gip=B1R32p==%12#1#1#1p=YAN342p=?P9P5P6P6P7P4P2Fjp=DAN342,A9p=:P3P4g017PP2CHp=IP4P5P6P6P7P2Ekp=OP9P5P6P6P7P4P2Flp=Q%02R5g00`WR:#1R;#1R<#1#a#;#;#;#;#;#;#;#5#5#9R=,24%9:R>'8P3P11842#0%09R?%04R@'ARA[1A@51894#0[RB1889#0\A1]42P2n2001000000120000000X83X73RAPB^83^73RBP2128=RCP>%0C%0>RCP11242#01<?@R1[1<@51294#0[RD1289#0\11X42P2n2001000000120000000X83X73R1PD^83^73RDP2f4REP=%0E%0=g00c^RF#VRG%qFRH1M34RI%n3RJ%g3RK1R30RL1L3:RM'@,4KRN%b6R6PNCB1`K7R7P2P9g00eUROg00f5RP'>1_29=NOPdA^304C\R0b2b3b4X53RPP@\5^53ROP2f5RQPEO2b03[O3b1PGPH%Z3RRPJ%=>,@L,4KP7P0b2b3b4PCP2b0CPO3b1P5P1PDP2P9%5:R:#5RD#5R1#Y#9RC%0CRS12E=/8>RT,>31?9TRTeRUPTPGPHPRPJ%=C,@L,4KP7P0b2b3b4PSP2b0b6RS5W?O3b1124C#0129CR?%51RV#9RW'8RX#0%5V#5#5#5#9RV,6XPAPBP2128CPW12Q=/8>RB,>31?8BRBePBPGPHPIPJPKPNP6%=W,@L,4KRL9DKNCBP7P0b2b3b4X53%0WRN,A@\5^53P212QCR5P8O2b0b6O3b1R@PX%91RIP@P3%3?R@%3WRB'F162IX93P9PCP4PSCp%39%3CRS'E,7@1>3S%9<R</?SP3PS%35%3Q/E2'7X93P4P<P2EU12ECRQ#3%3E/E<'71>3B%9DRD/?BP3PDf7R5/2C#3RS/F2/6IX93f8R@/2=/8>R>,>3f6R=/?>R>eP>1oSD16SD1FSDR>;:D17DS?:>S'<12@C#3/FDP3f9#3R>/m<16><1E><RS;:>17<>?:S<'<f:#3/E<P3p-0RSg00dJR>#KRA#KRY#KRZ,C31C3Y1C3A1C3>5G35G35G3R>g00diRA'T%KZ,C3=G3>/TA=SFG5SFPHP3P3P31M3EPEPRCJPE1M38CJP4P31M39PEPRCJCJPJPKP31L31R1g00mkRF%=<RACH,4K%5;,L3R;/I1,4K5DK1OK=1I;A,4K5DK5QKP6PK1OK5%=D,IM,4K5DK1OK@%1:,L3R:,IM,4K5DK5QKP6PK1@:;,4KP6P3PMPF%=ICH,4KCBCBCBP7P0b2b3b4X53X>3X?3X@3X;SX<SW=168<?:98A:E9<'<A:=4DA:549'<178E168I[[[^53^>3^?3^@3^;S^<S^=SP2f<RS/2C#3RC,7D16CD%3SRS,7<PSP4PCP8P9PEP5O:b0bIbCbHbBb6PBP2Efb1b:b1b:%3XP?PWPUPTPPPOP2PQP9O2b0b6PUPTPGPHPRPJPLP7P0b2b3b4PNP2b0b6CeEUCdCPbAbEbG%h4R4#0164V'AeWDXF3o"). Qed.


End CANSEC1.
Ltac ub H := let X := fresh "Y" in pose proof H as X; unbox X.

Section CANSEC2. Context {rc : runConstT}.
Section WithDepot.
Variable DI : ADepotIface.


Notation allocate_W L sp t c AB UB PG pgw n :=
  ([(bv_unsigned sp - 1152, bv_unsigned sp); (t + 208 + c * 80, t + 208 + c * 80 + 4); (t + 2784, t + 2792);
    (t + 2800, t + 3168); (UB - 16, UB + n); (AB, AB + 16);
    (shad UB, shad UB + shlen (n - n mod 8)); (PG, PG + pgw);
    (ADEPOT_LO, ADEPOT_HI); (al_nodes L, al_nodes L + 1048576); (al_store L, al_store L + 8388608)]%Z) (only parsing).

Definition allocate_post (L : alayout) (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (n t c cnt AB UB PG pgw lo b1 : Z) (maxc csz : word) (m : amem) : machine_state -> Prop :=
  fun ms' => exists (id : Z) t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m' (sj' : list word) (stj' : word),
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 UB) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom bsegs)
    /\ munch (allocate_W L sp t c AB UB PG pgw n) m m' /\ wmono bsegs m m' /\ mem_inv bsegs m'
    /\ stk bsegs m' lo (bv_unsigned sp)
    /\ 0 < id < 2^31
    
    /\ rw_cells bsegs m' (t + 208 + c * 80) [C4 (Z_to_bv 64 (cnt - 1)); C4 maxc; C8 csz]
    /\ rw_cells bsegs m' (t + 2784) [C8 stj']
    /\ u64arr bsegs m' (t + 2800) sj' /\ length sj' = 46%nat
    
    /\ rw_cells bsegs m' (UB + -16) [C1 (Z_to_bv 8 2); C1 (Z_to_bv 8 (Z.lor (Z.land (hdr_b1_mid b1) 243) 0)); C2 (Z_to_bv 64 0); C4 (Z_to_bv 64 n); C8 (Z_to_bv 64 id)]
    /\ rw_cells bsegs m' UB [CB (Z.to_nat n) (repeat (Z_to_bv 8 0xbe) (Z.to_nat n))]
    /\ (16 < rz_size n -> rw_cells bsegs m' AB [C8 (Z_to_bv 64 0xCC6E96B9CC6E96B9); C8 (Z_to_bv 64 (UB + -16))])
    /\ rw_cells bsegs m' (shad UB) [CB (Z.to_nat (shlen (n - n mod 8))) (repeat (Z_to_bv 8 0) (Z.to_nat (shlen (n - n mod 8))))]
    /\ (n mod 8 <> 0 -> rw_cells bsegs m' PG [C1 (Z_to_bv 8 (n mod 8))])
    /\ ADEPOT DI L m'.

Lemma allocate_fast_spec : forall (L : alayout) RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : amem)
    (n S t c cnt spacebeg AB UB PG pgw lo b0 b1 szh szl ctxj sz pc : Z) (maxc csz stj idxw j1 j2 : word) (pj : byte)
    (chunks sj : list word) (sjunk uj : list byte) (tb : list word) (tr : list Z),
  let ctx := al_ctx L in
  stk bsegs m lo (bv_unsigned sp) -> ATOP <= lo -> lo <= bv_unsigned sp - 1152 ->
  mem_inv bsegs m ->
  tp = Z_to_bv 64 ATP ->
  a0 = Z_to_bv 64 AINSTANCE -> a1 = Z_to_bv 64 n -> a2 = Z_to_bv 64 8 -> a3 = Z_to_bv 64 S -> a4 = Z_to_bv 64 1 -> a5 = Z_to_bv 64 1 ->
  1 <= n <= 448 ->
  
  allocA_cells m ctx t -> poison_cells m ->
  rw_cells bsegs m 0xb7b4d [C1 (Z_to_bv 8 1)] ->
  rw_cells bsegs m 0xb7b24 [C4 (Z_to_bv 64 0x1000); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0xbe)] ->
  rw_cells bsegs m 0xb2d80 [C8 (Z_to_bv 64 0x10)] -> rw_cells bsegs m 0x5ed2a0 [C4 (Z_to_bv 64 0)] ->
  rw_cells bsegs m 0x14bdc0 [C8 (Z_to_bv 64 0)] ->
  rw_cells bsegs m 0xb6cb8 [C8 (Z_to_bv 64 spacebeg)] ->
  
  rw_cells bsegs m (ctx + 8) [C4 (Z_to_bv 64 0)] -> rw_cells bsegs m t [C8 (Z_to_bv 64 ctx)] ->
  u64arr bsegs m (t + 2800) sj -> length sj = 46%nat ->
  AIMG_HI <= ctx -> ctx + 4096 <= ATOP -> sclr ctx 65536 ->
  iclr t 4096 -> t + 4096 <= ATOP -> t mod 4096 = 0 -> sclr t 4096 ->
  (ctx + 4096 <= t \/ t + 4096 <= ctx) ->
  
  Z.shiftr (needed_size n + 31) 5 = c ->
  rw_cells bsegs m (t + 208 + c * 80) [C4 (Z_to_bv 64 cnt); C4 maxc; C8 csz] ->
  u32arr bsegs m (t + 208 + c * 80 + 16) chunks -> length chunks = 16%nat ->
  0 < cnt <= 16 -> nth_error chunks (Z.to_nat (cnt - 1)) = Some idxw -> bv_unsigned idxw < 2^32 ->
  rw_cells bsegs m (t + 2784) [C8 stj] ->
  0 <= spacebeg < 2^47 ->
  
  AB = spacebeg + c * 2^32 + 16 * bv_unsigned idxw ->
  UB = AB + rz_size n -> 0x10007fff8000 <= AB -> UB + (size_of_class (class_id (needed_size n)) - rz_size n) <= ATOP -> AB mod 16 = 0 ->
  needed_size n <= size_of_class (class_id (needed_size n)) <= 65536 ->
  PG = shad UB + shlen (n - n mod 8) -> pgw = (if n mod 8 =? 0 then 0 else 1) ->
  0x2008fff7000 <= shad AB -> shad AB + 2 <= shad UB -> 0 <= shlen (n - n mod 8) <= 56 -> PG + 1 <= 0x10007fff8000 ->
  rw_cells bsegs m (UB + -16) [C1 (Z_to_bv 8 b0); C1 (Z_to_bv 8 b1); C2 (Z_to_bv 64 szh); C4 (Z_to_bv 64 szl); C8 (Z_to_bv 64 ctxj)] ->
  0 <= b1 < 256 ->
  rw_cells bsegs m UB [CB (Z.to_nat n) uj] ->
  (16 < rz_size n -> rw_cells bsegs m AB [C8 j1; C8 j2]) ->
  rw_cells bsegs m (shad AB) [C1 (Z_to_bv 8 0xfa)] ->
  rw_cells bsegs m (shad UB) [CB (Z.to_nat (shlen (n - n mod 8))) sjunk] ->
  (n mod 8 <> 0 -> rw_cells bsegs m PG [C1 pj]) ->
  
  (t + 4096 <= AB \/ AB + 65536 <= t) -> (ctx + 4096 <= AB \/ AB + 65536 <= ctx) ->
  (al_nodes L + 1048576 <= AB \/ AB + 65536 <= al_nodes L) -> (al_store L + 8388608 <= AB \/ AB + 65536 <= al_store L) ->
  (t + 4096 <= al_nodes L \/ al_nodes L + 1048576 <= t) -> (t + 4096 <= al_store L \/ al_store L + 8388608 <= t) ->
  (ctx + 4096 <= al_nodes L \/ al_nodes L + 1048576 <= ctx) -> (ctx + 4096 <= al_store L \/ al_store L + 8388608 <= ctx) ->
  sclr (al_nodes L) 1048576 -> al_nodes L + 1048576 <= ATOP -> sclr (al_store L) 8388608 -> al_store L + 8388608 <= ATOP ->
  
  rw_cells bsegs m S [C8 (Z_to_bv 64 (S + 16)); C8 (Z_to_bv 64 sz)] ->
  sz = 1 + Z.of_nat (length tr) -> sz <= 255 ->
  u64arr bsegs m (S + 16) tb -> length tb = 255%nat -> map bv_unsigned (firstn (Datatypes.S (length tr)) tb) = pc :: tr ->
  In (pc :: tr) (al_U L) -> bv_unsigned sp <= S -> S + 2056 <= 2^47 ->
  ADEPOT DI L m ->
  
  rng_aimg RNG -> rng RNG lo (bv_unsigned sp - lo) -> rng RNG S 2056 -> rng RNG ctx 4096 -> rng RNG t 4096 ->
  rng RNG (al_nodes L) 1048576 -> rng RNG (al_store L) 8388608 ->
  rng RNG (UB - 16) (n + 16) -> rng RNG AB 16 -> rng RNG (shad AB) 1 -> rng RNG (shad UB) (shlen (n - n mod 8)) -> (n mod 8 <> 0 -> rng RNG PG 1) ->
  AIMG_HI <= al_nodes L -> AIMG_HI <= al_store L ->      
  evtF bsegs RNG (allocate_post L ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc n t c cnt AB UB PG pgw lo b1 maxc csz m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 allocate_entry) fc None m (seg_rom bsegs)).
Proof.
  intros until tr. cbv zeta.
  intros ST CEIL LO MI TP Ha0 Ha1 Ha2 Ha3 Ha4 Ha5 N AC PC PP FLG LS1 LS2 HK SB CT8 TT0 STATS LSJ CX0 CX1 CXS T0 T1 TAL TS CT2
         HC CR CH LCH CNT NTH IXS STS SBR HAB HUB ABLO UBHI AB16 NSZ HPG HPW SB1 SB2 SB3 SB4 HDR B1 UJ LH SHA SHU SHP
         DJT DJC DJN DJS DTN DTS DCN DCS N0 N1 R0 R1 SS SZ SZB TB LTB TRF TRU SPS S47 DEP
         RIMG RSTK RS RCTX RT RNO RST RU RAB RSA RSU RSP NI SI. band_lin.
 assert (PW01 : 0 <= pgw <= 1) by (rewrite HPW; destruct (n mod 8 =? 0); lia).
  pose proof (small_facts n N) as (PRIM & NS & RZR & RZE & RSR & RSM & NSR).
  assert (C16 : 1 <= c <= 16) by (rewrite <- HC; rewrite Z.shiftr_div_pow2 by lia; clear -NSR; Z.div_mod_to_equations; lia).
  pose proof AC as AC'. destruct AC' as (INI & RSS & IMAX & TI & TK & T88 & TSD & CT).
  unfold AIMG_HI, AINSTANCE, ATP88, ATSD, ATSDI, ATSDK, AINITED, ARSSLIM in *.
  word_range sp SPR.
  box DJT. box DJC. box DJN. box DJS. box DTN. box DTS. box DCN. box DCS. box CT2.
  eapply evtF_cut.
  { eapply (allocA_spec RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
              F fc m n S (al_ctx L) t c cnt spacebeg lo maxc csz stj chunks idxw);
      try eassumption; try reflexivity; try (unfold AIMG_HI; lia).
    all: try (with_box CT2 lia). all: try solve_rng. }
  cbv beta. intros ms1 PA. unfold allocA_post in PA. destruct_exs PA.
  destruct PA as (-> & MUa & WMa & MIa & STa & [fr0 FRa] & CRa & [stja STSa]).
  rewrite <- HAB.
  xport HDR MUa WMa ltac:(with_box DJT lia). xport SHA MUa WMa ltac:(with_band TS lia). xport SHU MUa WMa ltac:(with_band TS lia).
  xport PP MUa WMa ltac:(lia). xport CT8 MUa WMa ltac:(with_box CT2 lia). xport TT0 MUa WMa ltac:(lia).
  xport SS MUa WMa ltac:(lia). xport TB MUa WMa ltac:(rewrite LTB; lia).
  xport STATS MUa WMa ltac:(rewrite LSJ; lia). xport CT MUa WMa ltac:(with_box CT2 lia).
  xport UJ MUa WMa ltac:(with_box DJT lia).
  xport FLG MUa WMa ltac:(lia). xport LS1 MUa WMa ltac:(lia). xport LS2 MUa WMa ltac:(lia). xport HK MUa WMa ltac:(lia).
  xport TI MUa WMa ltac:(lia). xport TK MUa WMa ltac:(lia). xport T88 MUa WMa ltac:(lia). xport TSD MUa WMa ltac:(lia).
  assert (PC1 : poison_cells x13).
  { eapply poison_cells_frame_b; [exact PC | exact MUa | exact WMa |]. unfold AIMG_HI, AIMG_LO.
    repeat (apply Forall_cons; [cbn [fst snd]; lia|]). apply Forall_nil. }
  assert (SHP1 : n mod 8 <> 0 -> rw_cells bsegs x13 PG [C1 pj]).
  { intros NE. specialize (SHP NE). xport SHP MUa WMa ltac:(with_band TS lia). exact SHP. }
  assert (LH1 : 16 < rz_size n -> rw_cells bsegs x13 AB [C8 j1; C8 j2]).
  { intros RZ. specialize (LH RZ). xport LH MUa WMa ltac:(with_box DJT lia). exact LH. }
  assert (DEP1 : ADEPOT DI L x13).
  { eapply (adi_frame DI); [exact DEP | exact MUa | exact WMa |].
    repeat (apply Forall_cons; [cbn [fst snd]; intros a Ha; pose proof DTN as X1; unbox X1; pose proof DTS as X2; unbox X2; lia|]).
    apply Forall_nil. }
  clear SHP LH PC DEP.
  eapply evtF_cut.
  { eapply (allocBC_spec DI L RNG sp gp tp _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc x13 n S t AB UB PG pgw lo b0 b1 szh szl ctxj sz pc pj sjunk tb tr fr0 _ _ _ _ _ _ _ _ _ _ _ _ _).
    all: try lazymatch goal with
         | |- stk _ _ _ _ => exact STa
         | |- mem_inv _ _ => exact MIa
         | |- poison_cells _ => exact PC1
         | |- ADEPOT _ _ _ => exact DEP1
         | |- @eq word _ _ => first [reflexivity | exact TP]
         | |- u64arr _ _ _ _ => exact TB
         | |- _ \/ _ => first [unboxed DJT | unboxed DJC | unboxed DJN | unboxed DJS]
         | |- rng _ _ _ => solve_rng
         | |- ~ _ -> _ => exact SHP1
         | |- _ -> rw_cells _ _ _ _ => exact LH1
         end.
    all: try eassumption. all: try (unfold AIMG_HI; lia).
    all: match goal with |- ?G => idtac "REMBC" G end. }
  cbv beta. intros ms2 PB. unfold allocBC_post in PB. destruct_exs PB.
  destruct PB as (-> & MUb & WMb & MIb & STb & IDR & HDRb & SHUb & SHPb & DEPb).
  xport FRa MUb WMb ltac:(lia).
  xport STATS MUb WMb ltac:(ub DJT; ub DTN; ub DTS; with_band TS lia).
  xport TI MUb WMb ltac:(lia). xport TK MUb WMb ltac:(lia). xport T88 MUb WMb ltac:(lia). xport TSD MUb WMb ltac:(lia).
  xport CT MUb WMb ltac:(ub DJC; ub DCN; ub DCS; with_band CXS lia).
  xport FLG MUb WMb ltac:(lia). xport LS1 MUb WMb ltac:(lia). xport LS2 MUb WMb ltac:(lia). xport HK MUb WMb ltac:(lia).
  destruct PC1 as (GOT & GOT80 & REAL & PC4 & PC5 & PC6 & PC7).
  xport GOT MUb WMb ltac:(lia). xport GOT80 MUb WMb ltac:(lia). xport REAL MUb WMb ltac:(lia).
  xport UJ MUb WMb ltac:(ub DJN; ub DJS; lia).
  xport CRa MUb WMb ltac:(ub DJT; ub DTN; ub DTS; with_band TS lia). xport STSa MUb WMb ltac:(ub DJT; ub DTN; ub DTS; with_band TS lia).
  assert (LH2 : 16 < rz_size n -> rw_cells bsegs x32 AB [C8 j1; C8 j2]).
  { intros RZ. specialize (LH1 RZ). pose proof (rz_size_small_cases n N) as RZC.
    xport LH1 MUb WMb ltac:(ub DJN; ub DJS; lia). exact LH1. }
  clear LH1 SHP1.
  pose proof (hdr_b1_mid_range b1 ltac:(lia)) as B1M.
  eapply evtF_mono.
  { eapply (allocD_spec L RNG sp gp tp F fc x32 n t c AB UB lo b0 (hdr_b1_mid b1) x14 S sj uj j1 j2 fr0 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _).
    all: try lazymatch goal with
         | |- stk _ _ _ _ => exact STb
         | |- mem_inv _ _ => exact MIb
         | |- @eq word _ _ => first [reflexivity | exact TP]
         | |- u64arr _ _ _ _ => exact STATS
         | |- _ \/ _ => first [unboxed DJT | unboxed DJC | unboxed DJN | unboxed DJS]
         | |- rng _ _ _ => solve_rng
         | |- _ -> rw_cells _ _ _ _ => exact LH2
         | |- rw_cells _ _ (_ + 152) _ => exact CT
         | |- rw_cells _ _ (_ + -16) _ => exact HDRb
         end.
    all: try eassumption. all: try (unfold AIMG_HI; lia).
    all: match goal with |- ?G => idtac "REMD" G end. }
  cbv beta. intros ms3 PD. unfold allocD_post in PD. destruct_exs PD.
  destruct PD as (-> & MUd & WMd & MId & STd & STATSd & LSJd & UFd & HDRd & LHd).
  xport CRa MUd WMd ltac:(ub DJT; lia). xport STSa MUd WMd ltac:(ub DJT; lia).
  xport SHUb MUd WMd ltac:(with_band TS lia).
  assert (SHPd : n mod 8 <> 0 -> rw_cells bsegs x47 PG [C1 (Z_to_bv 8 (n mod 8))]).
  { intros NE. specialize (SHPb NE). xport SHPb MUd WMd ltac:(with_band TS lia). exact SHPb. }
  assert (DEPd : ADEPOT DI L x47).
  { eapply (adi_frame DI); [exact DEPb | exact MUd | exact WMd |].
    repeat (apply Forall_cons; [cbn [fst snd]; intros a Ha; first [clear -Ha SPR S47 CEIL LO T0 T1 TAL NI SI N0 N1 R0 R1 HUB ABLO UBHI AB16 NSZ NS RZR RSR NSR HPG PW01 SB1 SB2 SB3 SB4 C16 LSJ N DTN DTS DJN DJS; ub DTN; ub DTS; ub DJN; ub DJS; lia | ub DTN; ub DTS; ub DJN; ub DJS; lia]|]). apply Forall_nil. }
  assert (MU : munch (allocate_W L sp t c AB UB PG pgw n) m x47).
  { eapply munch_trans; [| eapply munch_weaken; [| exact MUd]].
    eapply munch_trans; [| eapply munch_weaken; [| exact MUb]].
    eapply munch_weaken; [| exact MUa].
    all: first [clear -N C16 PW01; unfold sub_fp; cbn [outside]; intros q Hq; lia | unfold sub_fp; cbn [outside]; intros q Hq; lia]. }
  assert (WM : wmono bsegs m x47).
  { eapply wmono_trans; [| exact WMd]. eapply wmono_trans; [exact WMa | exact WMb]. }
  unfold allocate_post. do 18 eexists. split; [reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; [exact MId|]. split; [exact STd|]. split; [exact IDR|].
  split; [exact CRa|]. split; [exact STSa|]. split; [exact STATSd|]. split; [exact LSJd|].
  split; [exact HDRd|]. split; [exact UFd|]. split; [exact LHd|]. split; [exact SHUb|]. split; [exact SHPd|]. exact DEPd.
  Unshelve. all: try exact STb.
Qed.
End WithDepot.
End CANSEC2.

