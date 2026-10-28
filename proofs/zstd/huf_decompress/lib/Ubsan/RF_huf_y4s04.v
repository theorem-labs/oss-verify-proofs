(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Spec Require Import FseNCount FseLemmas HufPure_FseDecomp HufPure_HufBits HufPure_HufX1 HufPure_HufX2.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Lib Require Import Tac Arr Bytes ZBridge Walk RunConst Image.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Lib Require PropExec InitMem.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Common Require Import FseWalkKit FseWalkMem FseRdKit FseRdKit2 HufWalkKit HufWalkKit2 HufWalkKit3.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Ubsan Require Import UImg RunDraw RF_huf_iface RF_huf_h_iface RF_huf_dec_iface RF_huf_x4s
  RF_huf_fa_iface RF_huf_y4s RF_huf_y4s_iface RF_huf_y4s1.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib Require KReplay.
Ltac2 kr_t_RF_huf_y4s04 () := "I47Corelib4Init9Datatypes4list00K47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1Z02C56Stdlib6ZArith6BinInt1Z2ltI47Corelib4Init5Logic3and00I47Corelib5Lists7ListDef6Forall00I5ARocqVerifyHarness?AgentSubmission4Spec9FseNCount3res00C5ARocqVerifyHarness?AgentSubmission4SpecAHufPure_FseDecomp<init_dstreamI47Corelib4Init5Logic2eq00C46Stdlib6ZArith:ZArith_dec;Z_lt_le_decC56Stdlib6ZArith6BinInt1Z2leI47Corelib4Init6Specif7sumbool00K47Corelib7Numbers7BinNums8positive01C47Corelib4Init9Datatypes6lengthK47Corelib4Init9Datatypes4list01C46Stdlib5Lists4ListClength_zero_iff_nilC56Stdlib6ZArith6BinInt1Z6of_natC56Stdlib6ZArith4Znat5Nat2Z7inj_iffC47Corelib4Init5Logic7iff_symK47Corelib4Init5Logic2eq01C46Stdlib9micromega;ZifyClasses5mkrelC56Stdlib6ZArith4Znat5Nat2Z9is_nonnegK46Stdlib9micromega6VarMap1t02I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr01K46Stdlib9micromega7EnvRing5PExpr02K47Corelib4Init9Datatypes6option02K46Stdlib9micromega=RingMicromega7Formula01C46Stdlib9micromega5Tauto8BFormulaC46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundC46Stdlib9micromega;ZifyClasses;rew_iff_revK5ARocqVerifyHarness?AgentSubmission4Spec9FseNCount3res02C47Corelib4Init5Logic6eq_indC47Corelib4Init5Logic7f_equalK46Stdlib9micromega6VarMap1t01C47Corelib4Init5Logic8eq_ind_rC56Stdlib6ZArith6BinInt1Z3eqbC5ARocqVerifyHarness?AgentSubmission4Spec9FseNCount9highbit32C5ARocqVerifyHarness?AgentSubmission6Common:HufWalkKit7lesmallC56Stdlib6ZArith6BinInt1Z3subC5ARocqVerifyHarness?AgentSubmission6Common:HufWalkKitBinit_dstream_smallC5ARocqVerifyHarness?AgentSubmission4Spec9FseNCount4ZnthC47Corelib4Init5Logic3notC56Stdlib6ZArith6BinInt1Z7eqb_neqK46Stdlib9micromega7EnvRing5PExpr04C5ARocqVerifyHarness?AgentSubmission6Common:HufWalkKit9byte_ZnthC56Stdlib6ZArith6BinInt1Z4log2K5ARocqVerifyHarness?AgentSubmission4Spec9FseNCount3res01C56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z3powC56Stdlib6ZArith6BinInt1Z:pow_nonnegC56Stdlib6ZArith6BinInt1Z7compareK46Stdlib9micromega5Tauto8GFormula07K47Corelib7Numbers7BinNums1N02K46Stdlib9micromega7EnvRing5PExpr07C5ARocqVerifyHarness?AgentSubmission6Common:HufWalkKit<highbit32_okC56Stdlib6ZArith6BinInt1Z3mulC56Stdlib6ZArith6BinInt1Z3addC47Corelib4Init5Logic9False_indC56Stdlib6ZArith6BinInt1Z6eq_decK47Corelib7Numbers7BinNums1Z03K46Stdlib9micromega7EnvRing3Pol01K47Corelib4Init9Datatypes3nat02K46Stdlib9micromega=RingMicromega5Psatz02K46Stdlib9micromega=RingMicromega5Psatz04K46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega:ZMicromega;ZArithProof02K47Corelib4Init9Datatypes4list02C5ARocqVerifyHarness?AgentSubmission6Common:HufWalkKitDinit_dstream_big_errK5ARocqVerifyHarness?AgentSubmission4SpecAHufPure_FseDecomp4bitD01C5ARocqVerifyHarness?AgentSubmission6Common:HufWalkKitCinit_dstream_big_okK46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega5Tauto8GFormula08K46Stdlib9micromega5Tauto8GFormula05C5ARocqVerifyHarness?AgentSubmission4Spec9FseNCount4bindK47Corelib7Numbers7BinNums1Z01I5ARocqVerifyHarness?AgentSubmission4SpecAHufPure_FseDecomp4bitD00I47Corelib7Numbers7BinNums1Z00I47Corelib4Init9Datatypes3nat00K47Corelib4Init9Datatypes3nat01C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K46Stdlib9micromega=RingMicromega3Op203K47Corelib4Init9Datatypes4unit01K46Stdlib9micromega=RingMicromega3Op205K47Corelib4Init9Datatypes4bool02I47Corelib4Init9Datatypes4bool00K47Corelib7Numbers7BinNums8positive03C46Stdlib5Lists4List8nil_consI46Stdlib9micromega:ZMicromega;ZArithProof00K46Stdlib9micromega=RingMicromega3Op201K47Corelib4Init9Datatypes4bool01C5ARocqVerifyHarness?AgentSubmission4SpecAHufPure_FseDecompHZSTD_error_srcSize_wrongC5ARocqVerifyHarness?AgentSubmission6Common:HufWalkKitBinit_dstream_emptyC5ARocqVerifyHarness?AgentSubmission4Spec9FseNCountNZSTD_error_corruption_detectedI47Corelib4Init5Logic4True00I47Corelib4Init9Datatypes:comparison00I47Corelib4Init5Logic5False00K47Corelib4Init5Logic4True01C5ARocqVerifyHarness?AgentSubmission4Spec9FseNCountBZSTD_error_GENERICK46Stdlib9micromega:ZMicromega;ZArithProof01C5ARocqVerifyHarness?AgentSubmission4SpecAHufPure_FseDecomp6bd_ptrC5ARocqVerifyHarness?AgentSubmission4SpecAHufPure_FseDecomp7bd_bitsC56Stdlib6ZArith6BinInt1Z;log2_nonnegK46Stdlib9micromega5Tauto8GFormula03C56Stdlib6ZArith6BinInt1Z<log2_le_monoK47Corelib4Init5Logic3and01K46Stdlib9micromega=RingMicromega5Psatz07K46Stdlib9micromega=RingMicromega5Psatz05K46Stdlib9micromega6VarMap1t03K46Stdlib9micromega7EnvRing5PExpr05K46Stdlib9micromega7EnvRing5PExpr03K47Corelib4Init5Logic2or02K47Corelib4Init5Logic2or01I47Corelib4Init5Logic2or00C45stdpp9bitvector;definitions8bv_swrapC56Stdlib6ZArith6BinInt1Z6moduloC56Stdlib6ZArith6BinInt1Z4landC5ARocqVerifyHarness?AgentSubmission6Common;HufWalkKit2>neg_desc_shiftK46Stdlib9micromega:ZMicromega;ZArithProof03C56Stdlib6ZArith6BinInt1Z9mod_smallI45stdpp9bitvector;definitions2bv00C45stdpp9bitvector;definitions7Z_to_bvC5ARocqVerifyHarness?AgentSubmission6Common:FseWalkKit=swrap32_smallC45stdpp9bitvector;definitions;bv_unsignedC5ARocqVerifyHarness?AgentSubmission3Lib6MState<unsigned_litC5ARocqVerifyHarness?AgentSubmission3Lib3Mem4sx32I47Corelib4Init9Datatypes6option00C56Stdlib6ZArith6BinInt1Z3divK5ARocqVerifyHarness?AgentSubmission3Lib5Cells4cell01K5ARocqVerifyHarness?AgentSubmission3Lib5Cells4cell05C5ARocqVerifyHarness?AgentSubmission5Ubsan?RF_huf_fa_iface6jt_lenC5ARocqVerifyHarness?AgentSubmission5Ubsan:RF_huf_x4s3X4FC5ARocqVerifyHarness?AgentSubmission5Ubsan<RF_huf_y4s015Y0HDIC47Corelib5Lists7ListDef3mapI47Corelib4Init5Logic2ex00I47Corelib4Init9Datatypes4prod00K47Corelib4Init9Datatypes4prod01C5ARocqVerifyHarness?AgentSubmission5Ubsan>RF_huf_h_iface<huf_dec_postC5ARocqVerifyHarness?AgentSubmission3Lib5Frame3mkRC5ARocqVerifyHarness?AgentSubmission3Lib8PropExec7seg_romC5ARocqVerifyHarness?AgentSubmission3Lib5Frame5munchC5ARocqVerifyHarness?AgentSubmission3Lib3Tac>rw_cells_mergeC5ARocqVerifyHarness?AgentSubmission3Lib5Cells:cells_sizeC5ARocqVerifyHarness?AgentSubmission3Lib5Cells;cells_bytesC47Corelib4Init9Datatypes3appC5ARocqVerifyHarness?AgentSubmission3Lib5Cells8cells_atC5ARocqVerifyHarness?AgentSubmission3Lib5Cells8cells_wfC47Corelib4Init5Logic6or_indC47Corelib4Init5Logic7and_indC4ELinuxProcessSemantics?LinuxProcessSem6BvBase@le_bytes_to_wordC5ARocqVerifyHarness?AgentSubmission3Lib3Mem3le8C5ARocqVerifyHarness?AgentSubmission5Ubsan;RF_huf_y4s1?y4_le8_of_bytesC5ARocqVerifyHarness?AgentSubmission3Lib6MStateCZ_to_bv_bv_unsignedC5ARocqVerifyHarness?AgentSubmission3Lib7InitMem?rw_cells_recastC5ARocqVerifyHarness?AgentSubmission5Ubsan:RF_huf_y4s4SPLYK47Corelib4Init5Logic2ex01C46Stdlib9micromega9SatDivModCZ_mod_nonneg_nonnegC46Stdlib9micromega9SatDivModCZ_div_nonneg_nonnegC56Stdlib6ZArith6BinInt1Z7div_modC56Stdlib6ZArith6BinInt1Z=mod_pos_boundC56Stdlib6ZArith6BinInt1Z=mod_neg_boundC56Stdlib5omega8PreOmega1Z;div_0_r_extC56Stdlib5omega8PreOmega1Z;mod_0_r_extC5ARocqVerifyHarness?AgentSubmission3Lib9LiaTuning9zify_doneC5ARocqVerifyHarness?AgentSubmission5Ubsan;RF_huf_y4s38y4s3_allC56Stdlib6ZArith6BinInt1Z7add_0_rC46Stdlib9micromega;ZifyClasses7rew_iffC5ARocqVerifyHarness?AgentSubmission5Ubsan:RF_huf_x4s3BD4C5ARocqVerifyHarness?AgentSubmission3Lib3Arr5u8arrC5ARocqVerifyHarness?AgentSubmission3Lib4Step8rw_cellsC5ARocqVerifyHarness?AgentSubmission3Lib3Mem7mem_invC5ARocqVerifyHarness?AgentSubmission3Lib5Frame5wmonoC5ARocqVerifyHarness?AgentSubmission3Lib5Frame3stkC5ARocqVerifyHarness?AgentSubmission3Lib3Mem8bytes_atC5ARocqVerifyHarness?AgentSubmission3Lib6MState2MSC5ARocqVerifyHarness?AgentSubmission3Lib4Exec3evtC5ARocqVerifyHarness?AgentSubmission3Lib3Mem5wr_atI5ARocqVerifyHarness?AgentSubmission3Lib5Cells4cell00C5ARocqVerifyHarness?AgentSubmission5Ubsan4UImg5usegsC5ARocqVerifyHarness?AgentSubmission3Lib3Mem:length_le8C56Stdlib6ZArith6BinInt1Z:mul_div_leC5ARocqVerifyHarness?AgentSubmission5Ubsan<RF_huf_y4s1k9y4s1_loopC5ARocqVerifyHarness?AgentSubmission5Ubsan;RF_huf_y4s15Y1OPSC5ARocqVerifyHarness?AgentSubmission5Ubsan;RF_huf_y4s15Y1HDIC45stdpp9bitvector;definitionsDbv_unsigned_in_range".
Import ListNotations.
Open Scope Z_scope.
Set Warnings "-notation-for-abbreviation".
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Ltac zto pc := repeat (lazymatch goal with |- evt _ _ (MS _ _ (Z_to_bv 64 pc) _ _ _ _) => fail | _ => zstep end).

(* [comment removed for export] *)
Lemma y4_init_dstream_err_range : forall bs e, Forall (fun c => 0 <= c < 256) bs -> init_dstream bs = Err e -> 1 <= e <= 119.
Proof.
ltac2:(KReplay.run1 (kr_t_RF_huf_y4s04 ()) [] "p'0h01Hh14__x1h27__arithh34cstrh44__ffh58__varmaph65__with72H0h82EZh92hbh:1ri001rh;2e0h<2BYh=2L0h>1si011sh?1xh@1yhA1AhB2HahC2YBhD6__sat3hE2bshF1ei021ehG1li031lhH2L1hI2LBhJ2LShK6__sat2hL1bi041bhM1ci051ni061zp%0p&0p;1p;2p;3p;<p;4p;6p;9p;7p;8g0000j1RTg000Pj11Tg0015j13Tg001Sj22Tg001oR0j2BTg002Jj3_Tg002kR1j1iTg003dj1OTg004lj30j1fTg005Fj2dTg005mj25Tg006IR2j2bTg006ij1KTg007Nj2[Tg007nj1XTg008Nk20;Tg0096R3j1<Tg009Vj2}Tg00:9j3xTg00:Vj2UTg00;0l<vTg00;Uj1ETg00<:j2sTg00<Xj1rTg00=6j1pTg00=aj2lTg00>Dj2nTg00>gj1mTg00?Ij4cTg00@4k20ETg00@Vk20DTg00ABk30CTg00Aak40BTg00BSk40ATg00C>j2\Tg00D7j6=Tg00DSj6aTg00E0k10=Tg00ENm90<Tg00Elj2HTg00FIj1ZTg00GFj1WTg00HDj24Tg00Hak20:Tg00Ijj2MTg00Jbj1JTg00K;k204Tg00K\k303Tg00L?j4hTg00M?j1YTg00M]j2gTg00NVk202Tg00O>j2ITg00O[k300Tg00P?j2~Tg00P`j6|Tg00QDj1{Tg00Qbj3yTg00REj2zTg00SHj2TTg00Sej2VTg00TBj2eTg00Taj2wTg00UAk101Tg00U_j2uTg00V@k105Tg00V_j2jTg00WHj3tTg00X1k306Tg00XZk207Tg00YFk308Tg00Yfk309Tg00[1j4]Tg00\3j3qTg00]=j7kTg00]ak80?Tg00^Ek70@Tg00^ij4oTg00_aR4f0R5'5p=6g00`?R6/\5p=?g00aAR7/[5#<p=7f3R8f2R9'5f1R:/55'Bp=8g00a_R;g00b>R<705p=`1[75p=FA0754p=CP9g00b]R=g00c<R>P>g00c\R?P7P:g00d<P5Ccg00dcR@Fkp=:1l75p=AP7P:g00eCP5Ccp=LP:P=P>P>P?P5P@Fkp=GP8P=P>P>P?P9P:P5L0?p=;15:5,B9p>0>P9P=P>P>P?P:P5K0@p=@149:/M5p=91T:5,V9p=QP:P5P4g00ejR@C]p=P1g65p=DP7P6P:P5Cop=Sg00fJRA?05@p=^149:/M5,T8p=>1V9:/V5p=N%R7RB%65RCg00fjRD#1RE#1RF#1RG#1S00#1RH#1#1#1#3RI,25'BRJXM7RK=_7:%i6RL%O9%?:30%78RM%3DRN'd12MN15NM'bP2f4RM#7RO/2N15NOPNPMPM%KDRO#KRP#1S01#K#K#K#3RQC8P5f5RR#7RS/2Ng00gOp4p710RT%R5RUP01[:5#`%R9%X970:[RV%R:%X:7051[9:#`RW[%R8%X8709\W20;:5P:n2001000000120000000WGWAPV^GU^ATP5P7f7RT%FTRU#`%<URV#CP;P7%f;P3%f7%<:%<5507A0;:51}:53xX@;X?;PUPV1U7VP<P41U74M<v%EU%6Vg00glRU#XR;%RUR31s7:RW%r7RX%p7RY1l74RZ1n7DR[5:YR\%m>R]PY%ANR^,L[,GYP]P7P[g00hXPZCc,GYR_C;C;20EY?R`P5P9g00i?Ra,UA20D59=0AadB0C74:H0BRbb4b5b6X1712:N%C9[\C^17P5f9RC#FRc#<RdP:P8O3b2b3H0AO3b7f6Re%X7Rf50BPBPfA_7K5%O:f8Rg#?Rh50L%79/2NPNf:RiPiPQC8S02]=]0]<XEBA_7Kf%OfRK%?T50L%7f/2NPLPK%?iRK90L5X:LP:g00i_Rf,\6RBg00k3E=%?CRj90LBPLP7P1P6P7P5%KF#1#1#1#3RkP5PkPkn101100000410104101060000X;LPBPKP5EaA07fif;RK907fP7Pf15N5RB@0>5QXF7S03P;P3&0=7S04PX%AkRl9:Y^%AQRm9:Yl5@YP`Pbb4b5b6PNPkPkPQC8P5b2PNPfPfPQC8ef<RfP5E=W0P5O1b7b0W=W0W<PTP5PRPMP:N90<b7W=P5O115NS%7eRS%3GRG'd12SG15GS'bP212VG15GVPNPTPTPQC8P5%7gRT/2GPL%OCA0L5jX:LPePAPLA9dNCRj/H4g00l<RV,\6RS%Zj%Wi14G5RM%7iRk,4G;QG'P#DX97'Sn0100000020000Rl%Ec%6dP;P3PWPXPY%AGRd,L[,GYP]PYA:Y^[RcP]%3PRP#A9:Y[9@YcC;C;P`Pbb4b5b6X17125G15N:PNP9P9PPC8[[^17P5%7KRnP9PRO3b2b3-0:CE=A0LlhA9kNiRk/H4PA1UA5A9nNKRn/H4=0A5PAf=Rl#FS05#<Rh?9NlRo/H4=0A5PAPLP:PSf>Rp#7Rq?9NpRr#Zf?Rs#W%FsRt#<Ru,4G=QMG'P#DX97'Sn0100000020000%?lRv50LPNPpPpPQC8S06]0]8P:%FfRw#<Rx/4NS07/MfRy/H4Rz=0Aa%?fRa90LSPLP7P1P6P7P5%KERA#1#1R{#3R|P5P|P|n101100000410104101060000X;LPSPvP5EaA07VlA07VpP7PVQ03f@RS#FR}#ES08%<}R}#6S09P;P3Q04PX%A|R~9:Y^A:Y~m5@YP`Pbb4b5b6PNP|P|PQC8P5b2b3PNPVPVPQC8ePsP5E=W0P5O1b7W0W8%^z%Zo%Wp14Gq=QMG'P#DX97'S=0LaP01H:5#^A079:#J[R0A07:5#J1H9:#^Rz[A0789#J\z204:5P:n2001000000120000000X@7X?7P0^@7^?7P5A9uNsRsP4P9O3%Cs#JPS14}NR}PpQ08Q09P;P3PWPXPYPcP]B037[^Rc9:YZ1Lc[,GY5@YC;P`Pbb4b5b6X17S0914:NRc#612c:'B\B^17S08P5fBRB#7RcPfO2b2b3Ch1M}SR}#612}I'B%i7R}fAR0#FRz#<RV?9N0R|#ZfCR~#W%7~,4G=QMG'P#DX97,S5%?0S0:50LX:}P8%Y|,g7R}%Ez%6V%3ERE%3HRV+02124ES0;%6V1IEVRz,24[S0<[%6ER0g00mNR~B00EV:UWB%6z\~^B0P:g00mj1~4E'UQ0;eO1Q0<P;P3PWPXPY%AI,L[,GYR09@Y\S0<P]PYPYP=P>P>P?P_E|R?P]1LZ[,GYRZ%AE%{H5y7,L[,GY5@YC;C;P`Pbb4b5b6X17%C:RHg00nPR>[R=1249R\129z'B[\J^17P5fFRV#7?9NVPRPeO3b2bDbKbDb3,z|E=%WBR|14Gc/TGRV,VM'P#DX97,S}%?S50LPLA9cNB#Y,4G/VV,P|#DP1P6p-0P5P~P>P>P>n101100000410000100000000X;LR~g00nmR|Q0:P5E=P>PNPBPBPQC8/e5b7b0bCb8b7W0W8n0110400020101P5P9O2b8bLb0WJP5O115GT1wj4%CjRj%Jj'bP2%CkRk%JkQ02P5%CnRnPL%OfA0L5aX:LPCg00oIRC,\6Rk%EwRw%6xRxP;P3PWPXPYA:Yd[RdP]PdC;P`Pbb4b5b6X17Rd15G515G:[^17R:P5PqPRO2b2b3PwPx&01D,u7&05<,j75t71j7<6067g010O+07>08U;P3PWPXPYP_P]P_C;P`Pbb4b5b6X17%C5PH[^17P5PrP9O2b2b3609fE=%?K90LkPLP7P1P6P7P5PNP5PNPNn101100000410104101060000X;LPkPaP5EaA07CfA07ClP7PCQ03%Et%6uP;P3Q04PXA:Y^^A:Y^m5@YP`Pbb4b5b6PNPNPNPQC8P5b2b3PNPCPCPQC8ePpP5E=W0P5O1b7b0W8P5O1%JnPfQ07PiPwPxQ09Q08P5PqPgO2b2b3Ch%6y12yI'BPL%OlA0L5vX:LPi14hGRi/Ml1IEGRyA9hPl3QQ00#3,IERgPh%1ORx#3RwPlC>%1x#1Rx#3,IERfPh%3ARAPlC>3NPzPh%3FRFPlC>%1{#3,IER{Ph%3OROPlC>3N%1x#3,IERxPhPEPlC>Q01#1#1#3,IERn/To3N%Yo,4GPiP@C]#DRiQ05#ERo%6hRhPdP:P5PuPeO2b2b3PoPhP;P3PWPXPYQ0<P]PYP?P]A@YZ0C;C;P`Pbb4b5b6X17129I,B\\=\J^17P5PsP9P8O3b2b35qlE=A0LiaPL14qGRL/MpA9qPp7QyPgPqPwPpC>PfPqPAPpC>3NPzPqPFPpC>P{PqPOPpC>3NPxPqPEPpC>1Tnr3N%Yr,4GPLP@C]#DP~P|PvP5E=P>Q06/e5b7b0bCW8P5O1n200110100021110211105b>WIP5O1n200110100021110311103b>WHP5O1n200110100021110311103b>W0W<XF7WEo"). Qed.

Lemma y4_init_dstream_shape : forall bs d, Forall (fun c => 0 <= c < 256) bs -> init_dstream bs = Ok d ->
  (8 <= zlen bs /\ bd_ptr d = zlen bs - 8 /\ 1 <= bd_bits d <= 8) \/ (1 <= zlen bs <= 7 /\ bd_ptr d = 0 /\ 0 <= bd_bits d <= 64).
Proof.
ltac2:(KReplay.run1 (kr_t_RF_huf_y4s04 ()) [] "p'0h04__x1h11Hh27__arithh34cstrh44__ffh58__varmaph65__with72H0h82EZh92hbh:1ri001rh;4__x2h<2BYh=2L0h>1dh?1ei011eh@1si021shA1xhB1yhC1AhD2HahE2LGhF2YBhG4__p1hH6__sat3hI2bshJ1li031lhK2L1hL2LBhM2LShN6__sat2hO1bi041bhP1ci051ni061zp%0p&0p;1p;2p;3p;<p;4p;6p;9p;7p;8g0000j1UTg000Pj15Tg0015j19Tg001Sj24Tg001oR0j23Tg002Jj3oTg002kS00k100Tg003dj1WTg004lj30j1uTg005Fj2~Tg005mj21Tg006IS01j2tTg011;j1DTg012=j1HTg006ij1KTg007Nj2eTg007nj1^Tg008Nk20OTg0096R1j1@Tg009Vk20@Tg00:9k30>Tg00:Vj2ZTg00;0m<0;Tg00;Uj1OTg00<:j2}Tg00<Xk107Tg00=6k106Tg00=ak205Tg00>Dk202Tg00>gk10]Tg00@4k20\Tg00@Vk20[Tg00ABk30ZTg00Aak40YTg00BSk40XTg00C>j2rTg00D7j6ATg00TBj2pTg00ENm90WTg00HDj22Tg00Elj2RTg00FIj1gTg00GFj1XTg00SHj2>Tg00Hak20RTg00Ijj2GTg00Jbj1QTg00K;k20QTg00K\j3dTg00L?j4|Tg00M?j1CTg00M]j2{Tg00NVk20NTg00O>j2PTg00O[k30MTg00P?k20LTg00P`k60FTg00QDk10ETg00Qbk30DTg00REk20BTg00DSj6zTg013@j1yTg013ek60ATg014Ij3vTg014oj4xTg00V@j1bTg00V_j2\Tg015Jk20?Tg0163j3wTg00X1j3[Tg00XZj2jTg00YFj3kTg00E0k10CTg016\k40=Tg017:k30<Tg017]k30GTg018@k30:Tg00Tak20JTg00UAk10KTg00U_k209Tg00WHk308Tg00Yfk30PTg00[1j4`Tg00\3k30TTg018Zk30UTg0194k204Tg00?Ij4qTg00]=k703Tg00]ak80`Tg00Sej2NTg00^ik40_Tg00^Ek70^Tg00_aR2f0R3'1p=8g00`?R4/{3p=6g00aAR5/e3#@p=<f3R6f2R7'1f1R8/13'3p=V12789056/33p=SA056211271183'3'3p=F1178,36/33p>011167/380043p=Mg00a_R9g00b>R:703p=m1e53p=JA0532p=IA0583p=cP7g00b]R;g00c<R<P<g00c\R=P5P8g00d<P3Cqg00dcR>K03p=?20553p=TP5P8g00eCP3Cqp=YP8P;P<P<P=P3P>K03p=EP5P8g00hXP3Cqp=sP6P;P<P<P=P7P8P3L0`p=7f4R>/161178'3/33p=BA0567/38,3>0043p>0V1278/G3p=;P71N83P2g00ejR?C`p=LP5P4P8P3H0_p=_P7P;P<P<P=P8P3K0^p==1183,37p>0SA05>61178/33'3p=ag00fJR@?03?p=n1128/33p=l1178/33p=i11271183'3p>0H1>83,N7p=]1383,37p>0I1278/G3,>6p=:1G78,>6,N>/N3p=h1N>6/N7/N8/N3p=f%U5RA%83RBg00fjRC#5RD#5S02#5RE#5S03#5RF#5RG#5#5#9RH,43S04'3RIXP5RJ=o58&004RK%W7%6830%<6RL%9CRM'~14LM11MLRN'tQ01%<>RO/4M11MO%9EREf5RO#<RP%D>RQPPPEPM%H>RRPRPECVCS11MPS05PP%KCRS#KRT#9RUPQPRPR%9GRGCFH01CMP314PMg00gOp4p710RP%U3RRP01e83#m%U7%^7708[RQ%U8%^87031e78#mRV[%U6%^6707\V20O83P8n2001000000120000000WJWCPQ^JR^CPP3P5f7RP%JPRR#m%@RRQ#IP9P5%u9P1%u5%@8%@3'cA098320@8340>XB9XA9PRPQ1Z5QP:P21Z52N<0;%OR%8Qg00glRR#^R9%URR11}58RV&075RW&065RX20552RY2025CRZ5?XS06&0]<R[PX%TMR\,YZ,EXP[1sZY,EXS07C7C720\X=R]P3P7g00i?R^,Z@20[37=0@^dB0Z528H0YR_b4b5b6X05148M%I7[\B^05P3f9RB#JR`#@RaP8P6O3b2b3H0XO3b7f6Rb%^5Rc50APAPcAo5J3%W8f8S08#6Rd50K%<7/4MPEPLf:Re#DS09PLPEPM%HeRfPfPECVS0:CSPNPLPUQ09PfPfPGCFS0;H01CM]=]1]<XIAAo5Jc%WcRJ%6P50K%<cRc/4MPKPJ%6eRJ90K3X:KP8g00i_,r4RAg00k3EA%6BRf90KAPKPAQ00P4p-0RAP3g00nPRLg00mNRNPLPLn101100000410000100000000X?KS0<g00nmS0=PJP3EAPLPEPcf;RJ#DRgPcPEPM%HJRhPhPECVCSPMPcPcPUPgPhPhPGCFDBCM/p3b7b1W=W1W<PPP3POP>P8N90Wb7W=P3O1Q05%<bRh/~E14hE11Eh'tQ0114QE11EQQ08#<RQ,1ES0>%DPRh12QEPM%HPRPPPPECVPMPQPQPUPhPPPPPGCFDBI0VP314QEPK%WBA0K3fX:KPbP@PKA;aMBRf/R2g00l<,r4RQ%gf%Xe12E3RP%<eRh,2E/>E3L#6X95'_n0100000020000Rg%O`%8aP9P1PVPWPX%TERa,YZ,EXS0?P[PXA?X\ZR`P[%TUS0@9?XZ9=X`S0AC7C7P]P_b4b5b6X05143E11M811M7S0B@0S7U[[^05P3%<JRcP7POO3b2b3-0RBEAA0KgdA;hMeS0C/R2P@1Z@3A;cMJS0D/R2=0@3P@f=Rh#JS0E#@Rg?;MhRd/R2=0@3P@PKP8PQf>Ri#<Rj?;MiRk#gf?Rl#X%<lRm,2E/>E7LP#6X95'_n0100000020000%6hRn50KPEPm%DiRo12mERpPM%HiRq11qEDaPMPmPmPUPoPqPqPGCFDBCMRq]1]8P8f<Ro#JS0F#@S0G/2MS0H/GoRr/R2Rs=0@^%6oR^90KQPKPQQ0<Q0=PnP3EAPL1pq3b7W1W8%ns%gd%Xi12Ej/>E7LP#6X95'_=0K^P01R83#n1c78#Q[R01c83#Q1R78#nRs[1c67#Q\s20Q83P8n2001000000120000000XB5XA5P0^B5^A5P3A;mMlR0P2P7O3%I0#Qf@Rs%JsRq#@RQ/2MR@Pi%OqS0I%8QS0JP9P1PVPWPXP`P[Ad5Z\Rq9?XY1YqZ,EX5=XC7P]P_b4b5b6X05S0K11M3128MRq14q8'l[^05S0LP3fBRq#<RtPoO2b2b3C|1G@sR@14@H'l&005RufARv#JRw#@Rx?;MvRy#gfCRz#XS0M%<zR{,2E/>ES0N7LP#6X95,_3%6vS0O50KX:uP6%Cy,{5Ru%OwS0P%8xS0Q%9DRw%9FR|+0N142wS0R%8|1Pw|R},42[S0S[%8wR~B0Mw|8VNWD%8}\N^D~P8g00mj20L2w'ZQ0ReO1Q0SP9P1PVPWPXQ06%TH,YZ,EXR~5=XS06P[PXPXP;P<P<P=Q07J0FS0SP[1YYZ,EXS0R%Tw&0EF60D5,YZ,EX5=XC7C7P]P_b4b5b6X05%I8S0TPL[S0U1427S0V147}'3[\I^05P3fFRF#<?;MFRFPOPbO3b2bHbNbHb3-0ByEA%XqS0W12Et/>ES0X7LP#6X95,_u%6s50KPKP4Q00P4P4P3P3fDRu#X%JuS0Y#@RP?;MuRu#CRy,2E12EP/>E3LRNQ0MA;{Mz#CS0Z,2EQ0N3LR|P|n101100000410104101060000X?KQ0WA;tMqRt#C,2EQ0X3LS0X#6Q0OP3EzQ0X=04vA04|qP4PNPEfE#JS0X#@R|%D3S0OP|PEPM%H3RqPqPECVS0WCSPMP|P|PUQ0OPqPqPGCFS0NDBCMX>4%DNRqPPPEPM%HNRNPNPECVCS9iEPPMPPPPPUPqPNPNPGCFDBS0M%8yRN11yURy%yu%KT#K#K#K#K#9RqQ0Y#O%8PP9P1PVPWPXPXP;P<P<P=P6J0A==X~P[%Tq9?XZC7P]P_b4b5b6X05XGAR=Q04,38118q[^05^GARAP3%8FPFPOO3b2b35vuCx13NyQ0X#O%8|%b:R|#bRy#bRN#b,\520?5ERu1\5|R|5w51\5:R:5[55[5g010ORF'j1\5N1\5y9w5u=[5:5[5/jF=kR95kRP1P51}57P8&0C5H0=RuPWPX2025DRy9?XYQ0@9?Xy5=XRNP[PXQ0?P[PXP`P[Q0A1sYY,EXAd5ayRyAd5aZ>0<5a60G5R`9?XY%TG9?X`5=X5=X5=XC7C7C7P]P_b4b5b6X05X;5B0H88UR`148EQ0BPMP6P6PUA052212E>12E6R>;]ERY#811YG40IDB[[[^05^;5P3fGRY#<R<?;MY#CP<P7PiPvO5b2b3bEQ0Me40:PzP3EAW1P3O1b7b1bFb8b7W1W8n0110400020001P3P7O2b8bOb1WMP3O1Q0>20Jf2%IfRf%Qf'tQ01Q0C#IRf%QfPEPcQ09PcPEQ0:CSPMPcPcPUQ0;DBCMP3Q0D#IRcPK%WoA0K3^X:KPBg00oI,r4RBQ0F#ORfQ0G#8R2P9P1PVPWPXA?XaZRzP[PzC7P]P_b4b5b6X05Rv11E311E8R8[^05R<P3PjPOO2b2b3PfP2&0KC-095>085|=[5:/jF=kR9P1PVPWPXQ07P[Q07C7P]P_b4b5b6X05%I3Q0T[^05P3PkP7O2b2b360PoEA%6J90KBPKPBQ0<Q0=P^P3EAPLPEPj%DhRL12jERBPM%HhRJ11JEDaPMPjPjPUPLPJPJPGCFDBCM/p3b7b1W8P3O1%QcPoQ0HPePfP2Q0KQ0LP3PjQ08O2b2b3C|14rH,lrPK%WhA0K3nX:KPe12gERr/Gh1PwER2A;gUh3]Q03#9,PwRf%5SRo#9Rc,2gPh%5o#5Ro#9,PwRJPg%KDRD#9RLPhC:DhP}PgQ02#9RRPhC:%5D#5#5#9,PwRDPg%9SRSPhC:%5o#9,PwRoPgPwPhC:%5T#5#5#9,PwRT/>dDf%Cd,2EPrP?C`#6RrQ0E#ORd%8gRgPvP<P3PmPbO2b2b3PdPgP9P1PVPWPXQ06P[PXQ0SP[Q0R==X~C7C7P]P_b4b5b6X05Q0UQ0V147H'3[\I^05P3P0P7P6O3b2b360ThEAA0Kr^PKP4Q00P4P4P3P312QERr/GsA;QUs7]2Pf12QcPsPJPQPLPsC:DhP}PQPRPsC:PDPQPSPsC:PoPQPwPsC:1>T@Df%C@Rs,2EPrP?C`R^1GplA;mUl7]2Pf12mcPlPJPmPLPlC:DhP}PmPRPlC:PDPmPSPlC:PoPmPwPlC:1>T0Df%C0,2EPpP?C`RpPpn101100000410104111060101X?K1GBiA;jUi7]2Pf12jcPiPJPjPLPiC:DhP}PjPRPiC:PDPjPSPiC:PoPjPwPiC:1>TkDf%Ck,2EPBP?C`R?#6PnP3EzA04?hA04piP4P^PEPxQ0OPxPEQ0WCSPMPxPxPUQ0NDBCMX>4%D^RxPrPM%H^R^11^EDa9iEQRrPMPQPQPUPxP^P^PGCFDB%8sRG11sURs%y@Q0IQ0JP=PAP3%8tPtPOO3b2b39v@qCx13GsQ0PQ0QP9P1PuPWPXPNP[PXPzP[Ad5ZaRZ/sZ,EXA?X\yA?Xya5=X5=X9=XzC7C7P]P_b4b5b6X05X;5127ER_P_PMP>11>EDa9iE7\8\`^05^;5P3Q0ZP{P7PeO4b2b3bEPre40UPlP3EAW1P3O1b7b1bFW8P3O1n200110200021110111105b@WLP3O1n200110200021110311103b@WKP3O1n200110200021110311103b@W1W<X>4WIo"). Qed.

(* [comment removed for export] *)
Lemma y4_neg_desc_shift2 : forall tl mtl, 1 <= tl <= 12 -> 0 <= mtl <= 255 ->
  Z.land (bv_swrap 32 (0 - (tl + 256 * mtl) mod 18446744073709551616) mod 18446744073709551616) 63 = 64 - tl.
Proof.
ltac2:(KReplay.run1 (kr_t_RF_huf_y4s04 ()) [] "h04__x1h17__arithh24__ffh38__varmaph45__with54__x2h62H1h72H2h83mtlh92tlh:1zp;1p;2p;3p;4p;6p;7p;8g0015j13Tg005mj21Tg006ij15Tg001oj2:Tg000Pj10Tg00SHj2ATg00Sej2?Tg00QDj1QTg00HDj2CTg019Nj2JTg01:5j2HTg01:Uj2bTg004lj3FTg007nj1YTg0000j1WTg00<:j2DTg00<Xj1UTg00=6j1TTg00=aj27Tg00>Dj2@Tg00>gj1RTg00@4j2PTg00:Vj2OTg00@Vj2NTg00ABj3LTg00Aaj4KTg01;3j4MTg00V@j18Tg00V_j29Tg00X1j3=Tg00XZj2BTg01<9j2ITg015Jj2STg0163j3dTg00YFj3GTg00E0j1cTg016\j4aTg017:j3`Tg017]j3\Tg00?Ij4ETg001Sj2ZTg01<ej3[Tg00ENj6XTg00]=j7]Tg00^Ej7^Tg00]aj8_Tf0R0#0#0p=>%00#0#0#0p=V%00#0#0#0#0#0#0#0p=4g00aAR1f1R2g00d<P0CEp=6P2g00b]R3g00c<R4P4g00c\R5P0g00dcF]p=2f2R6P3P4P4P5P2P0F^p=<f3R7P3P4P4P5P6P2P0G_p=;g00fjR3#3R8/12%53R9#>#3R:,12':R;g00_aR</12%59#5#5#5R9#5#5#3R=,12':R>P1%03R?#VR@#0RA#>RB#3RC/A6,?7RD%Q@1C<0'J%4B#4#4#4#4#4#4#3RB'H%39'b%3Af4RA'C5F1X:1P7P6g00glR9#YR@%W9RE1D12RF%U1RG%T1RH17181@13R3'6,2H171:,63,2H5<HRI%R4R4PIC;1PH5R5P0P6g00fJRJg00i?RK'O1N06=FJKdAL1<2CKRKb2b3b4X011180110:':P;[^01P0PAP6O2b1P@PEPFPGPH171<RF/63,2H171=R:,63,2H5<HR8P4P8C;P5PKb2b3b4X0111<0110=':P>[^01P0P7P2O2b1CM1HDBg00b>R=#8R8#8RJ,91191=R=5=1%8JRJ#8#8,919=1=g010ORL'B'I1S1C191J5d11918==1=5=1/BL=G9@5G9PEP11D16P2%c1CaPGPH1@1?R?,6F,2H16?:,2H5<HP4PHPIP4171C=`1?9\13R3,6F,2HP1P3g00eC171BCE,2H5<HC;C;P5PKb2b3b4X01X511AC7,?6RC,1<1ZCB':\;\>^01^51P0P7PAP2P6O4b19[DBEXW7W6X81X91o"). Qed.

(* [comment removed for export] *)
Lemma y4_sx32_lit : forall x, 0 <= x < 2^31 -> sx32 (Z_to_bv 64 x) = Z_to_bv 64 x.
Proof.
ltac2:(KReplay.run1 (kr_t_RF_huf_y4s04 ()) [] "h04__x1h17__arithh24__ffh38__varmaph45__with51zh62Hxh71xp;2p;1p;3p;4p;6p;7p;8g005mj2=Tg000Pj10Tg0015j13Tg006ij17Tg00O>j2DTg001Sj2<Tg001oj2;Tg00QDj19Tg01=Hj1ITg019Nj2BTg01=kj26Tg004lj35Tg00:Vj2CTg007nj1WTg0000j1VTg00<:j2UTg00<Xj1TTg00=6j1QTg00=aj24Tg00>Dj2OTg00?Ij4>Tg00Qbj3@Tg00>gj1MTg00UAj1LTg00@4j2JTg00@Vj2KTg00ABj3HTg00Aaj4GTg01>Qj2NTg00ENj6ATg01?Uj2FTg01@?j2PTg01A;j1ETg00]=j7RTg00^Ej7STg00]aj8XTf0R0#0#0#0#0p=1f1R1g00b]R2g00c<R3P3g00c\R4P0g00dcFRp=2g00aAR5P1g00eCP0C>p=:f2R6P2P3P3P4P1P0FSp=8f3P2P3P3P4P6P1P0GXp=?g00_aR2/=0g00fjR7#0R8#3R9%77#7#7#7R:#3'D,<0';R;P5P1%18R8#0R<#9R=#IR>%98R8/B0,6=16=6R?35X55P5P116=0=5>?X5516=1R?,C>1B81g00glR8#WR@%V8R81U51RA%T5RB%Q5RCP51452g00d<RD1O57R7C>,2CRE1459RF%9:5@5,:7,2C58CR:%M3R3P5%0<#1#1#1#1#1#1RG#LRH,45PDP7C>,2C%3GRG,45,:7,2C58CC?1JC4R4P0P6g00fJRDg00i?RI'C1K06=5DIdAH521CGRIb2b3b4X051=H11<1G';\;^05P0P6P1O2R6b1,N1EA1F=?P@P8PAPBPCP:P3A@5F=,:7,2C98CEC?P4PIb2b3b4X051=21%3<,D9,<1';\;^05P6b1,P1EA%E?=5>?eW6X75o"). Qed.

Ltac xo2 := repeat (lazymatch goal with
  | |- evt _ _ (MS _ _ (if _ then _ else _) _ _ _ _) => fail
  | |- evt _ _ (MS _ _ (Z_to_bv 64 ?z) _ _ _ _) =>
      let d := eval vm_compute in ((z =? PY4_BODY + 700) || (z =? PY4_BODY + 3044)) in lazymatch d with true => fail | false => zstep end
  | _ => zstep end).
Ltac w2 := xo2; repeat (lazymatch goal with |- evt _ _ (MS _ _ (if _ then _ else _) _ _ _ _) =>
  let K := fresh "K" in if_cases K; zify_cond K end; xo2).

Lemma y4j_desc_sh : forall tl mtl, 1 <= tl <= 12 -> 1 <= mtl <= 12 ->
  Z.land (bv_swrap 32 (0 - (tl + 256 * mtl)) mod 2^64) 63 = 64 - tl.
Proof.
  intros tl mtl T M.
  assert (HT : In tl [1;2;3;4;5;6;7;8;9;10;11;12]) by (cbn; lia).
  assert (HM : In mtl [1;2;3;4;5;6;7;8;9;10;11;12]) by (cbn; lia).
  cbn in HT, HM.
  repeat match goal with H : _ \/ _ |- _ => destruct H as [<- | H] | H : False |- _ => contradiction end;
  vm_compute; reflexivity.
Qed.

Section CANSEC1. Context {rc : runConstT}.
Section Y4S04.
  Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (m0 : fmem).
  Variables (DST dcap SS DT mtl tl lo : Z) (src : list Z) (cells : list deltX2) (cbs : list byte).
  Notation SP := (bv_unsigned sp).
  Notation n := (zlen src).
  Hypothesis TOK : x2_table_ok cells tl.
  Hypothesis ECB : cbs = firstn (Z.to_nat (4 * 2^tl)) (x2_bytes' cells).
  Hypothesis LCB : zlen cbs = 4 * 2^tl.
  Hypothesis MTL : 1 <= mtl <= 12.
  Hypothesis TLM : tl <= mtl.
  Hypothesis D0 : 0 <= DST.
  Hypothesis DP : 0 < dcap -> 8 <= DST.
  Hypothesis DC : 0 <= dcap < 2^32.
  Hypothesis DL : DST + dcap <= lo.
  Hypothesis S0 : 16 <= SS.
  Hypothesis SL : SS + n <= lo.
  Hypothesis NSM : n < 2^26.
  Hypothesis BYS : Forall (fun c => 0 <= c < 256) src.
  Hypothesis DT0 : 0 < DT.
  Hypothesis CBL : DT + 4 + 4 * 2^tl <= lo.
  Hypothesis DJ1 : DT + 4 + 4 * 2^tl <= DST \/ DST + dcap <= DT.
  Hypothesis DJ3 : DST + dcap <= SS \/ SS + n <= DST.
  Hypothesis LOS : lo <= SP - 4096.
  Hypothesis SP16 : SP mod 16 = 0.
  Hypothesis SP47 : SP <= 2^47.
  Hypothesis DT4 : DT mod 4 = 0.

  (* [comment removed for export] *)
  Notation POST := (huf_dec_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc DST dcap lo m0).
  Notation Y4F' mm spl b4 b3 b2 b1 :=
    (Y4F ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m0 DST dcap SS DT lo src cbs mm spl b4 b3 b2 b1).
  Notation L1 := (jt_len src 0). Notation L2 := (jt_len src 2). Notation L3 := (jt_len src 4).
  Notation L4 := (n - (6 + L1 + L2 + L3)).
  Notation O2 := (6 + L1). Notation O3 := (6 + L1 + L2). Notation O4 := (6 + L1 + L2 + L3).
  Notation SEG := ((dcap + 3) / 4).
  Notation desc := (tl + 256 * mtl).
  Notation SPLL w64 k4 k2 p2 k1 j0 :=
    (SPLB desc (DST + 3 * SEG) dcap (SS + O4 + 8) (SS + O3 + 8) (SS + O2 + 8) (DST + dcap - 7) w64 k4 k2
          (SS + O2 + p2) (DST + SEG) (DST + 2 * SEG) k1 (DST + dcap) (DT + 4) j0).
  Notation SPLX v24 v32 v40 v48 v64 v72 v80 v88 v112 j0 :=
    (SPLB desc (DST + 3 * SEG) v24 v32 v40 v48 (DST + dcap - 7) v64 v72 v80 v88
          (DST + SEG) (DST + 2 * SEG) v112 (DST + dcap) (DT + 4) j0).
  Notation BDS c b p O jp := (BD4 c b (SS + O + p) (SS + O) jp).

  Hypothesis LOOP : (1 <= L1 /\ 1 <= L2 /\ 1 <= L3 /\ 1 <= L4 /\ 6 + L1 + L2 + L3 + L4 <= n) -> (0 < SEG /\ 3 * SEG <= dcap /\ dcap <= 4 * SEG) -> 2 <= SEG ->
    forall q1 q2 q3 q4 b1 b2 b3 b4 p1 p2 p3 p4 c1 c2 c3 c4 w64 mm j0 jp1 jp2 jp3 jp4
                           (xt2 xs0 xa0 xa2 xa3 xa4 xs5 xs6 xs8 xs10 xt5 : word),
    Y4F' mm (SPLL w64 c4 c2 p2 c1 j0) (BDS c4 b4 p4 O4 jp4) (BDS c3 b3 p3 O3 jp3) (BDS c2 b2 p2 O2 jp2) (BDS c1 b1 p1 6 jp1) ->
    Y1OPS SEG q1 q2 q3 q4 -> q4 + 8 <= dcap ->
    Y1HDI L1 p1 b1 -> Y1HDI L2 p2 b2 -> Y1HDI L3 p3 b3 -> Y1HDI L4 p4 b4 ->
    0 <= c1 < 2^64 -> 0 <= c2 < 2^64 -> 0 <= c3 < 2^64 -> 0 <= c4 < 2^64 -> 0 <= w64 < 2^64 ->
    evt usegs POST (MS (mkR (Z_to_bv 64 b2) (Z_to_bv 64 (SP + -912)) gp tp (Z_to_bv 64 (SS + O3 + p3)) (Z_to_bv 64 (DT + 4))
                            xt2 xs0 (Z_to_bv 64 b1) xa0 (Z_to_bv 64 (DST + q1)) xa2 xa3 xa4 (Z_to_bv 64 (2^61))
                            (Z_to_bv 64 (64 - tl)) (Z_to_bv 64 (- DT - 5)) (Z_to_bv 64 (DST + q4)) (Z_to_bv 64 c3)
                            (Z_to_bv 64 (DST + q3)) xs5 xs6 (Z_to_bv 64 b3) xs8 (Z_to_bv 64 b4) xs10 (Z_to_bv 64 (DST + q2))
                            (Z_to_bv 64 (SS + O4 + p4)) (Z_to_bv 64 (SS + 6 + p1)) xt5 (Z_to_bv 64 (DST + dcap)))
                        F (Z_to_bv 64 0x1aaf4) fc None mm (seg_rom usegs)).

  Hypothesis EXIT : (1 <= L1 /\ 1 <= L2 /\ 1 <= L3 /\ 1 <= L4 /\ 6 + L1 + L2 + L3 + L4 <= n) -> (0 < SEG /\ 3 * SEG <= dcap /\ dcap <= 4 * SEG) -> 2 <= SEG ->
    forall q1 q2 q3 q4 b1 b2 b3 b4 p1 p2 p3 p4 st1 st2 st3 st4 c1 c2 c3 c4
                           v24 v32 v40 v48 v64 v72 v80 v88 v112 mm j0 jp1 jp2 jp3 jp4
                           (xra xt0 xt2 xs0 xs1 xa0 xa2 xa3 xa4 xa5 xa6 xa7 xs3 xs5 xs6 xs7 xs8 xs9 xt3 xt4 xt5 : word),
    Y4F' mm (SPLX v24 v32 v40 v48 v64 v72 v80 v88 v112 j0)
         (BDS c4 b4 p4 O4 jp4) (BDS c3 b3 p3 O3 jp3) (BDS c2 b2 p2 O2 jp2) (BDS c1 b1 p1 6 jp1) ->
    0 <= q1 <= dcap -> 0 <= q2 <= dcap -> 0 <= q3 <= dcap -> 0 <= q4 <= dcap ->
    Y1AFT L1 p1 b1 st1 -> Y1AFT L2 p2 b2 st2 -> Y1AFT L3 p3 b3 st3 -> Y1AFT L4 p4 b4 st4 ->
    0 <= c1 < 2^64 -> 0 <= c2 < 2^64 -> 0 <= c3 < 2^64 -> 0 <= c4 < 2^64 ->
    evt usegs POST (MS (mkR xra (Z_to_bv 64 (SP + -912)) gp tp xt0 (Z_to_bv 64 (DT + 4)) xt2 xs0 xs1 xa0
                            (Z_to_bv 64 (DST + q1)) xa2 xa3 xa4 xa5 xa6 xa7 (Z_to_bv 64 (DST + q4)) xs3 (Z_to_bv 64 (DST + q3))
                            xs5 xs6 xs7 xs8 xs9 (Z_to_bv 64 dcap) (Z_to_bv 64 (DST + q2)) xt3 xt4 xt5 (Z_to_bv 64 (DST + dcap)))
                        F (Z_to_bv 64 0x1b41c) fc None mm (seg_rom usegs)).

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma y4s04_entry : forall mm c1 c2 c3 c4 b1 b2 b3 b4 p1 p2 p3 p4 j0 jp1 jp2 jp3 jp4
                             (v8 v16 v24 v32 v40 v48 v56 v64 v72 v80 v88 v112 : Z)
                             (xra t0 t1 t2 x9 a0 a1 a2 a3 a4 a5 a6 a7 x18 x19 x20 x21 x22 x23 t3 t4 t5 t6 : word),
    Y4F' mm (SPLB v8 v16 v24 v32 v40 v48 v56 v64 v72 v80 v88 (DST + SEG) (DST + 2 * SEG) v112 (DST + dcap) (DT + 4) j0)
         (BD4 c4 b4 (SS + O4 + p4) (SS + O4) jp4) (BD4 c3 b3 (SS + O3 + p3) (SS + O3) jp3)
         (BD4 c2 b2 (SS + O2 + p2) (SS + O2) jp2) (BD4 c1 b1 (SS + 6 + p1) (SS + 6) jp1) ->
    6 <= dcap -> 1 <= L1 -> 1 <= L2 -> 1 <= L3 -> 1 <= L4 ->
    Y1HDI L1 p1 b1 -> Y1HDI L2 p2 b2 -> Y1HDI L3 p3 b3 -> Y1HDI L4 p4 b4 ->
    0 <= c1 < 2^64 -> 0 <= c2 < 2^64 -> 0 <= c3 < 2^64 -> 0 <= c4 < 2^64 ->
    evt usegs POST (MS (mkR xra (Z_to_bv 64 (SP + -912)) gp tp t0 t1 t2 (Z_to_bv 64 DST) x9 a0 a1 a2 a3 a4 a5 a6 a7
                            x18 x19 x20 x21 x22 x23 (Z_to_bv 64 desc) (Z_to_bv 64 (DST + 2 * SEG)) (Z_to_bv 64 dcap)
                            (Z_to_bv 64 (DST + 3 * SEG)) t3 t4 t5 t6)
                        F (Z_to_bv 64 0x1aa48) fc None mm (seg_rom usegs)).
  Proof using All.
    intros until t6. intros XF D6 HL1 HL2 HL3 HL4 H1 H2 H3 H4 C1 C2 C3 C4.
    destruct XF as ((buf & BUFA & BUFL) & SRC & CBS & ST & SPC & L0 & B4 & LB4 & B3 & LB3 & B2 & LB2 & B1 & LB1 &
                    (u0 & u1 & u2 & u3 & u4 & u5 & u6 & u7 & u8 & u9 & u10 & u11 & SV) & (jl & JL) & FR & MI & MU & WM).
    unfold BD4 in B1, B2, B3, B4. unfold SPLB in SPC. rewrite <- (Z_to_bv_mod64 v64) in SPC.
    pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
    pose proof TOK as (TL & _). unfold HUF_TABLELOG_MAX in TL.
    assert (SG2 : 2 <= SEG) by (apply Z.div_le_lower_bound; lia).
    assert (SG4 : 3 * SEG <= dcap <= 4 * SEG) by (Z.div_mod_to_equations; lia).
    assert (HLp : 1 <= L1 /\ 1 <= L2 /\ 1 <= L3 /\ 1 <= L4 /\ 6 + L1 + L2 + L3 + L4 <= n) by lia.
    assert (HQp : 0 < SEG /\ 3 * SEG <= dcap /\ dcap <= 4 * SEG) by lia.
    w2.
    all: try (exfalso; lia).
    all: replace (DST + dcap + -7) with (DST + dcap - 7) in * by lia.
    all: lazymatch goal with
         | |- evt _ _ (MS _ _ (Z_to_bv 64 ?z) _ _ _ _) =>
             let d := eval vm_compute in (z =? PY4_BODY + 3044) in
             lazymatch d with
             | true =>
                 replace (Z_to_bv 64 DST) with (Z_to_bv 64 (DST + 0)) by (f_equal; lia);
                 eapply EXIT with (q1 := 0) (q2 := SEG) (q3 := 2 * SEG) (q4 := 3 * SEG) (st1 := 3) (st2 := 3) (st3 := 3) (st4 := 3);
                 [ exact HLp | exact HQp | exact SG2 | .. ];
                 [ unfold Y4F; repeat match goal with |- _ /\ _ => split | |- exists _, _ => eexists end;
                   first [ reflexivity | eassumption ] | .. ];
                 try lia; try (unfold Y1AFT, Y1HDI in *; lia)
             | false => idtac
             end
         end.
    all: pose proof H1 as H1u; pose proof H2 as H2u; pose proof H3 as H3u; pose proof H4 as H4u;
         unfold Y1HDI in H1u, H2u, H3u, H4u.
    all: rewrite ?sx32_small by lia.
    all: rewrite ?y4j_desc_sh by lia.
    all: lazymatch goal with |- context [Z_to_bv 64 (Z.lxor (DT + 4) ?c)] =>
           replace (Z_to_bv 64 (Z.lxor (DT + 4) c)) with (Z_to_bv 64 (- DT - 5))
             by (rewrite zb_lxor_ones by lia; rewrite <- (Z_to_bv_mod64 (- DT - 5)); f_equal;
                 first [ apply (Z.mod_unique _ _ (-1)) | symmetry; apply (Z.mod_unique _ _ (-1)) ]; lia) end.
    all: replace (Z_to_bv 64 DST) with (Z_to_bv 64 (DST + 0)) by (f_equal; lia).
    all: eapply LOOP with (q1 := 0) (q2 := SEG) (q3 := 2 * SEG) (q4 := 3 * SEG);
         [ exact HLp | exact HQp | exact SG2 | .. ].
    all: try (unfold Y1OPS; lia).
    all: try lia.
    all: try assumption.
    all: try (unfold Y4F; repeat match goal with |- _ /\ _ => split | |- exists _, _ => eexists end;
              first [ reflexivity | eassumption ]).
    all: try lia.
    all: apply Z.mod_pos_bound; lia.
  Qed.
End Y4S04.
End CANSEC1.
