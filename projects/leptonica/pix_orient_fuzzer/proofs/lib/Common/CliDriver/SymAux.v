(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.Common Require Import PropExec CatExec CatSim SeqExec StoreOk SymExec RefMemcpyLib AgentLib.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.Common.Leptonica Require Import PortLib.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.Common.Leptonica Require Import Frame.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.Common.CliDriver Require Import SymExec2 SymExec2Sound SymRun.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib Require KReplay.
Ltac2 kr_t_SymAux () := "c69OSSVerify5KrLib6Common9CliDriver6SymAux7sregionC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List2InC47Corelib5Lists7ListDef3mapC47Corelib4Init9Datatypes8list_indI47Corelib4Init9Datatypes4list00K47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00c69OSSVerify5KrLib6Common9CliDriver6SymAux<regions_flatC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z6of_natC79OSSVerify5KrLib6Common9CliDriver=SymExec2Sound4SX2S4flatC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib6Common9CliDriver=SymExec2Sound4SX2S6estartC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitions;bv_unsignedI47Corelib4Init9Datatypes4prod00I47Corelib4Init5Logic2eq00K47Corelib4Init9Datatypes4list01C47Corelib4Init5Logic6eq_indC47Corelib4Init5Logic9False_indC47Corelib4Init5Logic3notC79OSSVerify5KrLib6Common9CliDriver8SymExec23SX25a_offC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3addc69OSSVerify5KrLib6Common9CliDriver6SymAux=entry_coveredC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes3orbK79OSSVerify5KrLib6Common9CliDriver8SymExec23SX25saddr01C1?~~~~~~~~~~~~~~~C46Stdlib4Bool4Bool8orb_propI47Corelib4Init5Logic2or00c69OSSVerify5KrLib6Common9CliDriver6SymAux6rdenotC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic3and00C56Stdlib6ZArith6BinInt1Z3lebC47Corelib4Init9Datatypes9andb_propC79OSSVerify5KrLib6Common9CliDriver8SymExec23SX26a_baseC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib6Common9CliDriver=SymExec2Sound4SX2S;expr_eqb_eqC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z2leC56Stdlib6ZArith6BinInt1Z6leb_leC45stdpp9bitvector;definitions7Z_to_bvK47Corelib4Init5Logic2eq01K47Corelib4Init5Logic2or01C79OSSVerify5KrLib6Common9CliDriver8SymExec23SX26edenotC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums1Z02C56Stdlib6ZArith6BinInt1Z3powC56Stdlib6ZArith6BinInt1Z2ltC47Corelib4Init5Logic8eq_ind_rC56Stdlib6ZArith4Znat5Nat2Z9is_nonnegC56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z:pow_nonnegK47Corelib4Init9Datatypes3nat02K46Stdlib9micromega=RingMicromega5Psatz02K46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega:ZMicromega;ZArithProof02K47Corelib4Init9Datatypes4list02K46Stdlib9micromega6VarMap1t02K46Stdlib9micromega6VarMap1t03K46Stdlib9micromega6VarMap1t01I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr02K47Corelib7Numbers7BinNums8positive01K47Corelib4Init9Datatypes6option02C46Stdlib9micromega5Tauto8BFormulaC46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundK46Stdlib9micromega7EnvRing5PExpr01K46Stdlib9micromega7EnvRing5PExpr07K46Stdlib9micromega5Tauto8GFormula03C59OSSVerify5KrLib6Common8AgentLib7u64_litC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common9Leptonica5Frame6in_rngC1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic2or02C69OSSVerify5KrLib6Common9Leptonica5Frame7outsideC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes4prod01C79OSSVerify5KrLib6Common9CliDriver8SymExec23SX28expr_eqbC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes4andbC47Corelib4Init9Datatypes3fstC47Corelib4Init9Datatypes3sndK46Stdlib9micromega7EnvRing5PExpr03K46Stdlib9micromega=RingMicromega7Formula01K46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega5Tauto8GFormula05K46Stdlib9micromega5Tauto8GFormula08I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01I79OSSVerify5KrLib6Common9CliDriver8SymExec23SX25saddr00C1?~~~~~~~~~~~~~~~I47Corelib7Numbers7BinNums1Z00K47Corelib7Numbers7BinNums1Z01K46Stdlib9micromega=RingMicromega3Op203C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K47Corelib4Init9Datatypes4unit01K46Stdlib9micromega=RingMicromega3Op205I79OSSVerify5KrLib6Common9CliDriver8SymExec23SX23env00C1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes3nat00K47Corelib7Numbers7BinNums8positive03K47Corelib4Init9Datatypes4bool02I47Corelib4Init5Logic4True00I47Corelib4Init5Logic5False00K47Corelib4Init5Logic4True01I79OSSVerify5KrLib6Common9CliDriver8SymExec23SX24expr00C1?~~~~~~~~~~~~~~~I46Stdlib9micromega:ZMicromega;ZArithProof00K47Corelib4Init9Datatypes3nat01K46Stdlib9micromega:ZMicromega;ZArithProof01I47Corelib4Init9Datatypes6option00C79OSSVerify5KrLib6Common9CliDriver=SymExec2Sound4SX2S6flat_uC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib6Common9CliDriver8SymExec23SX26adenotC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics@word_to_le_bytesC59OSSVerify5KrLib6Common7CatExec6wbytesC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes6lengthC59OSSVerify5KrLib6Common7CatExecDlength_N_to_le_bytesC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib6Common9CliDriver6SymAux@entry_covered_inC1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic3and01C69OSSVerify5KrLib6Common9Leptonica5Frame@frame_mod_wbytesC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common9Leptonica5Frame@frame_mod_weakenC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib6Common9CliDriver=SymExec2Sound4SX2S8log_flatC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib6Common9CliDriver=SymExec2Sound4SX2S9mem_denotC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common9Leptonica5Frame>frame_mod_reflC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common9Leptonica5Frame9frame_modC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib6Common9CliDriver6SymAux;log_coveredC1?~~~~~~~~~~~~~~~I47Corelib4Init5Peano2le00c69OSSVerify5KrLib6Common9CliDriver6SymAux;frame_layerC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib6Common9Leptonica5FrameDframe_mod_trans_sameC1?~~~~~~~~~~~~~~~K79OSSVerify5KrLib6Common9CliDriver8SymExec23SX26sentry01C1?~~~~~~~~~~~~~~~I79OSSVerify5KrLib6Common9CliDriver8SymExec23SX26sentry00C1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics5Riscv7Prelude5bvmapC79OSSVerify5KrLib6Common9CliDriver=SymExec2Sound4SX2S7regs_okC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib6Common9CliDriver8SymExec23SX26sr_getC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common8PropExec4getrC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib6Common9CliDriver6SymAux9same_regsC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib6Common9CliDriver6SymAux<regs_ok_sameC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib6Common9CliDriver6SymAux?same_regs_soundC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common<RefMemcpyLib8keeps_csC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common<RefMemcpyLib<callee_savedC1?~~~~~~~~~~~~~~~K79OSSVerify5KrLib6Common9CliDriver8SymExec23SX29sym_state01C1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib6Common9CliDriver8SymExec23SX28sym_execC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib6Common9CliDriver=SymExec2Sound4SX2S7know_okC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib6Common9CliDriver=SymExec2Sound4SX2S9scs_denotC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common8PropExec4mkstC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib6Common9CliDriver8SymExec23SX24s_pcC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib6Common9CliDriver8SymExec23SX25s_logC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib6Common9CliDriver8SymExec23SX26s_regsC1?~~~~~~~~~~~~~~~C79OSSVerify5KrLib6Common9CliDriver8SymExec23SX26s_knowC1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic2ex01C79OSSVerify5KrLib6Common9CliDriver=SymExec2Sound4SX2S;sym_exec_exC1?~~~~~~~~~~~~~~~I4ELinuxProcessSemantics?LinuxProcessSem<MemImageType7Segment00I79OSSVerify5KrLib6Common9CliDriver8SymExec23SX27scripts00C1?~~~~~~~~~~~~~~~I79OSSVerify5KrLib6Common9CliDriver8SymExec23SX26kentry00C1?~~~~~~~~~~~~~~~I79OSSVerify5KrLib6Common9CliDriver8SymExec23SX29sym_state00C1?~~~~~~~~~~~~~~~I79OSSVerify5KrLib6Common9CliDriver8SymExec23SX28sidecond00C1?~~~~~~~~~~~~~~~I4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=machine_state00".
Import ListNotations.
Open Scope bv_scope.
Import SX2. Import SX2S.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition sregion : Type := (saddr * Z)%type.

Definition rdenot (E : env) (r : sregion) : word * Z :=
  (Z_to_bv 64 (estart E (fst r)), snd r).

(* [comment removed for export] *)
Fixpoint entry_covered (rs : list sregion) (a : saddr) (w : nat) : bool :=
  match rs with
  | [] => false
  | (SA rb rk, n) :: rest =>
      (expr_eqb (a_base a) rb && Z.leb rk (a_off a) && Z.leb (a_off a + Z.of_nat w) (rk + n))%bool
      || entry_covered rest a w
  end.

Fixpoint log_covered (rs : list sregion) (log : list sentry) : bool :=
  match log with
  | [] => true
  | SE a w _ :: rest => entry_covered rs a w && log_covered rs rest
  end.

Definition regions_flat (E : env) (rs : list sregion) : Prop :=
  forall r, In r rs -> flat E (fst r) (snd r).

Section VP1. Context {fx : FPState}.   (* [comment removed for export] *)
Lemma entry_covered_in : forall E rs a w (x : word),
  entry_covered rs a w = true -> regions_flat E rs -> flat E a (Z.of_nat w) ->
  (estart E a <= bv_unsigned x < estart E a + Z.of_nat w)%Z ->
  ~ outside x (map (rdenot E) rs).
Proof.
ltac2:(KReplay.run1 (kr_t_SymAux ()) ["VP1"] "p'0h02Hch11Hh22rbh34__x1h44__x2h51li001lh63Hrfh71ah81ni011nh92H1h:2H2h;2H3h<2Hah=3Hfah>3Hfrh?3Hnoh@2HxhA2_HhB7__arithhC4__ffhD4__p1hE6__sat4hF6__sat5hG8__varmaphH5__withI4__x3hJ4__x4hK4__x5hL4__x6hM4cstrhN1mhO2rshP1zi021zhQ1EhR2H0hS4HouthT2HrhU2IHhV2a0hW1ehX1rhY4resthZ2rkh[1si031sh\1wh]1xi042Ini056a_basei065a_offi071bi082l'i091pp%0p&0p;1p;2p;3p;6p;4p;5p;7p;8g0000R0p606000R1g0014R2p4p710p8P1g001KR3p4p710p8P1g001gR1p4p710p8g002IR4j1pTg002ij1QTg003Nk106Tg003lj1wTg004Oj2<Tg005Xj16Tg0068j3BTg007Ej27Tg008Tj21Tg009>R5j2rTg009^j3PTg00:8j1qTg00:Xj6nTg00;4k20BTg00;Sj1FTg00;lj14Tg00=4j20Tg00=Qj3_Tg00>[k204Tg00?8j2KTg00@Bj3yTg00@^R6j2kTg00A8j2Wj1DTg00B;R7j23Tg00BVj2CTg00C3j3bTg00CVj1ATg00D_k30ETg00F3j29Tg00FOk20DTg00Foj2=Tg00GUj2oTg00Gok30CTg00HIj2JTg00IRj1lTg00J0k20ATg00JMj2LTg00Jij6\Tg00KGk10?Tg00Klk20>Tg00LTk30=Tg00M8j1[Tg00MWj2VTg00N@j3ZTg00Nij2iTg00OUj3YTg00P5j2]Tg00PSj4^Tg00Q1k10:Tg00QOk109Tg00Qmk108Tg00RXj2RTg00S;j1fTg00S`k105Tg00TBk203Tg00Tdk202Tg00UPk301Tg00Uoj4|Tg00Vaj2dTg00WDj3}Tg00Wgj6{Tg00XKk200Tg00YGj3cTP2j3eTg00ZIj3zTP1k507TP3j4hTg00Zcj2mTg00[fj4gTg00\Fj2xTg00]Qk20;Tg00]oj3vTg00^Lj3uTg00^ik30<Tg00_Lj4jTg00`7j7tTg00`[k70@Tg00a?j8sTg00acR3f2R1f1R2f0R83_g00bCR93Pp=@f4R:f3R;'91028,L1'3p=5P0P1%D2P8Ch,m;#Fp=GAY028p=ag00bcR<g00cmR=P1P2Cg=Y08p=H%A2/x8p=?1C28-0;1p=>AP389p=2%68,02p=NP<P=1K12P8Cgp=8Ac128#Fp=:P0P1P2P8Ch,m;p=IAv<=8p=OAu<=8p=Mg00dKR>/98p=;B0<=28p=SP=P2g00diP8Cjp=TP2g00ePR?g00eoR@P@g00fORAP8g00foFtp=EP=P2g00gOP8Cjp=`P1P?P@P@PAP2P8K0@p=UP;P?P@P@PAP1P2P8Gsp=X1L28,31p=~g00h6%p0RBg00i>g00i]RC#QRD#QRE#Q#Q#Q#QRF$06RG#wRHP0A@8;1f6RI/<2f7RJf5RK%6:RL3Bf8RM/7IRN11G:ROPOPN%6KD5PK1rH=RNf9ROP:CG[[[[XOBg00jBRP=P39%q0RQ,<KRR%6;9BI:RS17JKRT11G;RUPUPTPLD5RLg00jbRTP3PPP3p-0RPP8g00k>RUPTn0110700020000XW3g00k[P9P:EnPU20BU8bRW1%FTeW@W=W6W0A@Q12P:PNPMPQCG\L\S\R[eP5P<P=A@8K:1<M2%6I9BOJf:RR/7MRS11GIRLPLPS%6JRSD5PJPNf;RLP:CG[[[[1a12?@IK1a;1,<OABRMS17LORS11GJRQPQPS%6MD5PMPNf<RS1aIKCG[[[[[^5BP8P<A@8OM1<S2f=RQ%6R7BLf>RV/7SRW11GRRXPXPW%6LRWD5PLPNf?RXP:CG[[[[AH;12?@ROAH:;1,<QABVSW17XQRW11GLRYPYPW%6SRWD5PSPNf@RYAHJIKCG[[[[[^5B^P=P8g00l7RZA@8SL1<X2%6Q9BYVfAR[/7XR\11GQR]P]P\%6VR\D5PVPNfBR]P:CG[[[[1?Q:%4QR^7>;10^W10;13>A_2QS+04#21KK:?H;1,<YR^AB[X\R\17]YRW11GVR_P_PW%6XD5RW1?[M%4[R_7>J1N_Y10JI3>R_A_K[YR`;y;%2_%2`'kP61?]O%4]R67>M1N6[10MJ3>#2A@I][P5PHP=PPfER6A8ROM'WfCR`?:28P`PNfGR_#DPOCIS00'3n2001109000120107101#FP81?`R%4`Ra7>O1Na]10OM3>#2fDRa/?L%4aRb7>RRc1Nb`10RO'CRb;b8%2c%2b'3P71?6S%46Rb7>L#21Nba10LR'C#2P5PHP=PPfHRbA8QSL'WfFRc?:28PcPNfJRd#DPSCIRe'3n2001109000120107101#FP81?_V%4_7>Q#2%4b/N_10VQ'C#2fIRf/?YRg%4f,CXRh;b2%2g%2h'3P71?d[#2%4d,CY#2P5PHP=PPfMRhA8][YRY'WfKRg?:28PgPNfORi#DP[CI'3n2001109000120107101#FP8fLR[/?`#2%4h,C`#2fNRj#ARk@0E62APZk6P71C28#21912[Rk19281C12#2Rl[19;1\l20D28P2n2001000000120000000XN=X8=RlPk^N=^8=RkP8PcfPRm#4RnP1O319cnPlPkP8fRRk#4fQRl'NRn10b_RoPOO319noP5PHP=PPfURoA8dfb'WfSRn?:28PnPNfWRn#DPfCI'3n2001109000120107101RpP7fVRqA8gdfRd#O'7,=G%Md5:kPkPN%DqPbCIPUP8fTfXRdA8h[gRr#O'7,=G%Mr3:PoPNfYRr#DPgCIP2PfA8ijhRhAP0hhPP^5B^70P4P0PPP8PUAP02;P:P;P8O2'kn10110000020020107108X5BX70p?1001104PhP[O21o0h40CO2fZR4%OhRs%MhRh3BPZ%ArRtf\Ru/J8,1G/0mRv,=G,1GRw11GdRxPxPwPiD5X2ZPZPm%;v%lDRw%lFRF+0ARx,Lv%;i10vi/9x'3'3'3X2ZP8PtPRE\f[Rv/Jt,1G/0iRt#;1Ltx%;j10tj/9x'3'3'3PZPlf]RtA88lmRy#ORz#A'J,1G%4z'0,=G%My5:rX2ZP;%A4RrPLE\A8rmiRr#ORy#A,Ju,1G%4y'0,=G%Mr5:dPZPkf^Rd1K8k?Hlm'<X2ZP[%AvR[PSE\1K[l?Hmi,<tP=%Au,Jd,1G/0kRuP811GvRtPtP8PkD5XP=&0?vS01%6v#;Rk20>wFRt1L>w%;F1L>x[[R[%;wRlB0=wF2VTW<RF%;x\T^<lRlg00m@RTg00mlRZ#[Rr#[Ry#[Rz,V=1V=y1V=ZRZ5Z=5Z=g00nKRy'i%[z,V=1V=r=Z=Z5Z=/iy%qTRy5YT3Y%pTRTP=P=1]=:P11]=IC^P2P=1]=KP;&0:=RZC^C^&09=Rr&08=Rz1R=CR{%fD,R=R|'SR}%fCRC,R=R~'T,Ez%QC,R=RC,S},`~,Ez5Uz&05@R}Pz1S|C1R=DRD1R=ERE'S'T,EzP}Pz1TD|,EzP}1S{DRD/T~,Ez1SDE,`~,Ez5UzCXCXCX203zAR~P8P11o3920281#2dB01=>2C|R9bCbGbHX3=X4=XI=XJ=XK=XL=108:R3P1P1P3PKD510KI101:'919;I10;:R3PKPKP3PID5[[[^3=^4=^I=^J=^K=^L=P8f_#6f`R3#4Po11GdPqfb%A3'J,1GR3PiPQPXO9bBbEbFbM1=Gu,1GQ01PkPtP[PFPlPyPTP=1]=1P2PZC^PrPz1d=>/TD,EzR>1d=w=}=G,`D,EzRDPzP?P@P@PAP:E{5Uz5UzP}AUz>DCXP~P9bCbGbHX3=X4=XDP1082R9#;1L9x/31'31021R9#;?~9x[^3=^4=^DPP8%;o103q/0o/9x'3PqP3PIO4bBbEbFbM-00uE\b6b?b>PmPREn1KmiRm#A,Jv,1G%4m'0,=G,1GRi11GnRnPnPiPjD5e17vm,=G,1GRmPnPnPmPjD5eb>174s,=GRs,1GR411GqRjPjP4PhD5eAcqsheO1WAW?P2P8O2n2001000000121000000W1%Fpeb;b1b:b1b9W:W9P2P8O2n2001000000121000000b0W;W0P2P8O2n2001000000121000000b0W0P8O1A@J`]P5PHP=PPA8LRO,WcA:a28PaPN%DbPRCI'3n2001109000120107101RbP7A8SLRRL#O,7_,=G%ML5:`Q00PUP8A8VQSRU#O,7f,=G%MU5:6PSPKAe08VPSP2AP0Y2Ae02X;z8O2WTXX01<gQePOPMP8O5XSeWAP2P8O2n2001000000120000000W1%FbeW0P8O1n200100000021100011000b0W@W=W6W01K:;?H12?@QSPXPNP`1KMJ?HIKCG\W\\\^[eWUXYBX8=XZ=W2P2P8O2n01103000121105106X[<P2P8O2n2001109000121103102XV0P;I07W]W\X7<WOWQo"). Qed.
End VP1.

Section VP2. Context {fx : FPState}.   (* [comment removed for export] *)
Lemma frame_layer : forall E rs m a w (v : word),
  entry_covered rs a w = true -> regions_flat E rs -> flat E a (Z.of_nat w) ->
  frame_mod m (wbytes m (adenot E a) (word_to_le_bytes w v)) (map (rdenot E) rs).
Proof.
ltac2:(KReplay.run1 (kr_t_SymAux ()) ["VP2"] "h03Hinh12H0h22H1h32Hah44__x1h54__x2h61mh71nh81zh91Eh:1Hh;2H2h<2Hch=3Hfah>4Houth?3Hrfh@2HuhA7__arithhB4__ffhC6__sat3hD6__sat4hE8__varmaphF5__withG1ahH2rshI1vhJ1whK1xp;1p;3p;2p;4p;6p;:p;7p;8g002Ij1KTg002ij19Tg003Nj1DTg003lj1>Tg00o7j1lTg00=Qj3[Tg009^j3=Tg004Oj2TTg005Xj10Tg0068j3QTg00oYj4PTg010hj28Tg008Tj26Tg007Ej21Tg0121j2;Tg0139j3fTg009>j2ZTg0143j2<Tg00[fj4ITg00:8j1JTg00OUj3FTg00A8j1ETg001Kj4BTg00Zcj2ATg00YGj3STg00;Sj1RTg00F3j27Tg00=4j2:Tg00JMj24Tg00B;R0j25Tg014Sj2@Tg00:Xj6?Tg015[l:OTg016hj4NTg00IRj1CTg00J0j2MTg00Klj2LTg00LTj3UTg00P5j2kTg00Q1j1jTg00PSj4iTg00QOj1hTg00Qmj1gTg00RXj2HTg00^ij3eTg00Vaj2bTg00WDj3_Tg00_Lj4\Tg00`7j7]Tg00S`j1^Tg00a?j8YTg00TBj2`Tg00GUj2aTg00Tdj2XTg00UPj3cTg00Uoj4dTg00Jij6GTg017Cj4WTg018Oj6VTf2R1f1R2':f0R3'7p=2g00dKR4/73p=3g00h6g0000R5#Kg00i]R6#9R7#9#9R8#9#9#9R9#DR:#>R;%D8#>R8#lR<[g00bcg00i>R=g00acR>f4R??[12g00bCR@3=f6RAf5RB'Tf7RCf3RD#07Q?f8REPB%0?P3CPg00cmRF18EB,6:11EB3=PCf9RG/8ARH1;B?RI5fC1Z;FRJP;PFPH1<8IRK#0CI%JJRL3FP5PJ%EGPECBP5PJf:R5#EPGCB,A3f;RM/8ERN1;CA,<8#0RO5S2RP#RRQg00jbRRP=1;EC,<8f=R8/85,6:RS16:DRT'7%03RU,:S,4T'5X7=P3PE1@ECE?f<RV/8G,6:RW16:1RX'7%0ERY,:W,4X'5PFPS16:?RS,73%05RX,:3,4S'5X8FP31185RSP?E?17ST%0GRW,:SRZ,4T'5f>RTP8PMP5P?PEPCPAP3PDM:Ob0b0X0PPQeg00k[CNP;PFPNPOCI=FJL,A2eW>XK;PCPHPIP=PB185C,6:%C7RI%C9R9'MRL72UX7=PF11GAR=%0ARA=23LX8FP0%3=14=L%0BRU#3A2=UL'5'5115C?2ALP211ME#311VGRG/4L%3YA2GYL'5'5P014SL%3W17ZL'511TM?2XLP3f?RX/1V/4L%0VRV#3f@RM/18?2VL'5P0%08R8#3fAR0/1T?28LfBR8/1X%0T;2LP3%0X#3fD/10%0M;2L1LI9144I%39144L[[%3IRMAUI92VRW3%3L\R^3MfERMP8O1P<g00m@R<#J%K<PF1kF1P2%jFCi%hF%gFR<g00ePR8g00eoRRPRg00fOR9P<P8PRPRP9PF1HF61HF75eFg00di1bFI=_F:C\g00foF]RI%^RPIGY1`<9P3P11a>@1X31==>@dAcF42CdbBbEbFX4FX5FA232LA221L[^4F^5FP3%0MfIfF'1P?O3bAb6bCbDW;W2P2P3O2n2001000000121000000W2W1P2P3O2n2001000000121000000W1W:P2P3O2n200100000012100000016:HP3EGPK1@B?EGCWEVb@W=W?W<XI;WJWGW6WHW9o"). Qed.
End VP2.

Section VP3. Context {fx : FPState}.   (* [comment removed for export] *)
Theorem log_covered_frame : forall E base rs log,
  log_covered rs log = true -> regions_flat E rs -> log_flat E log ->
  frame_mod base (mem_denot E base log) (map (rdenot E) rs).
Proof.
ltac2:(KReplay.run1 (kr_t_SymAux ()) ["VP3"] "p'0h02Hch13Hlfh23Hrfh33logh41Eh51Hh62H1h72H2h83Hfah94Hlf'h:2Hwh;2IHh<1ah=2a0h>4baseh?1lh@4resthA2rshB1vhC1wi006e_addri015e_vali027e_widthi031sp;1p;2p;3p;9p;6p;5p;4g002ij17Tg003Nj1JTg003lj1FTg00o7j1PTg002Ij1KTg004Oj25Tg019[j20Tg01:lj31Tg009>j2QTg009^j3BTg01<>j2UTg00:8j1TTg01=Hj3HTg00=Qj3>Tg01>Mj2DTg00]Qj2STg00M8j13Tg01?Uj2CTg005Xj18Tg0068j3;Tg00B;R0j29Tg00C3j3RTg010hj2?Tg00HIj2@Tg0121j2=Tg0139j3<Tg01?ol9OTg01A7j6NTg01BGj3ATg001gj5MTg00A8j1ETg001Kj4ITg00OUj3LTg00acR1f1R2f0R3'Dg00bCR43Bp=2f4R5f3R6g0000R7f2R8%E2P3CI3Hp=4P7P8%E2P3CIp=Gg01CRR9?L23p=6AB134p=:g00h6g00i]#7#7#7R:#7#7#7#J#FR;%J:#F#P[%K7%K9R7P91283f5R:/56f6R</08P<f7R=?1<6g00cm,Q;R;P=P:D4[[[X37AB1441558R4g00jbAG;<5R1,U:W1W2W0%T9R>,2210:>A1<:>=H:1[\4[eP9125315=:f8R4/08P4f9R1?146P;P1P=D4[[[1682,2:154<1656,01P1f:R>16:5711P;P>P4D4[[[[^?7P3g00bcg00i>g00l71213f<R?/5>f=R@/08P@f>RA?1@6P;PAP?D4[[[A>>561D>2'S#:f;RB,5@RCg00ml#3#3#3#3#3#3#3#3RD,C:%8:9;A<10A6'9'9A>@=<RE1D@5RF;R8%:E%:F'9P0A>A4=#:12A:f@RFfARE?1F<1?E11@E=,=43<P;PEf?RGD4P3A>F>1#:12E4P01CBDfDRH%8B7;?10H1'9PHfERI?1H>1?I@1@IB,=?3<P;PIfCRID4P:1C@DfGRD%8A7;G10D?'9P0fHR0%8G7;F100@P0fIR??10A1??E1@?G,=F3<P;P?PDD4P3fJRDfBR?%8E3;fKR0/0FP0fLRB?10ER01?BH1@B?R?,=I5<0AG;BDPFP4PAP3O3PBPDP0PHPIP?P1PAP2M9OENW9W8P2P3O2n2001000000120000000W5W:P2P3O2n2001000000120000000W7W6P2P3O2n2001000000120000000b0W1W2W0AA568/62,2>AA<:5/66,0APAAA=<:/6591GAP;PGP@D4[\C[eW;X@7WBWCW<P8P2P3O3n01103000131100102101X=9P3DMW3WAW>W4o"). Qed.
End VP3.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Section VP4. Context {fx : FPState}.   (* [comment removed for export] *)
Lemma regs_ok_same : forall E sr sr' R R' (r : reg),
  regs_ok E sr R -> regs_ok E sr' R' -> sr_get sr' r = sr_get sr r -> getr R' r = getr R r.
Proof.
ltac2:(KReplay.run1 (kr_t_SymAux ()) ["VP4"] "h01bh11Eh22HRh33HR'h42Hsh51Rh62R'h71eh81rh92srh:3sr'p;1p;2p;3p;6g002Ij1<Tg002ij10Tg00S;j1:Tg003Nj16Tg003lj18Tg01D]j2;Tg01EIj37Tg01FYj21Tg009^j33Tg00HIj22Tg01Gbj24Tg00GUj29Tg00Jij65Tg00h6g00l7R0#<R1g00i]#0R2#:#6R3%02#0#0#0#0#6#8R2';R4%83f5R3f4R5f2R637f6R7?75611361176530P2f8R8f7f3R9'1R:'2R;1435f0R<532X02P21179R7,28f9R=1185'2R8932<X02P0P:12=<=328X70192;P7P<E51459f1P9O1E51439P6P9O1E5W4W3W2W8X64W5X:1W9W1o"). Qed.
End VP4.

(* [comment removed for export] *)
Fixpoint same_regs (sr sr' : list expr) (rs : list reg) : bool :=
  match rs with
  | [] => true
  | r :: rest => expr_eqb (sr_get sr' r) (sr_get sr r) && same_regs sr sr' rest
  end.

Section VP5. Context {fx : FPState}.   (* [comment removed for export] *)
Lemma same_regs_sound : forall E sr sr' R R' rs,
  same_regs sr sr' rs = true -> regs_ok E sr R -> regs_ok E sr' R' ->
  forall r, In r rs -> getr R' r = getr R r.
Proof.
ltac2:(KReplay.run1 (kr_t_SymAux ()) ["VP5"] "h01rh13Hinh22Hsh32HRh43HR'h52rsh61Eh71Hh82H1h92H2h:2IHh;1Rh<2R'h=2r0h>4resth?2srh@3sr'p;1p;2p;3p;9p;6p;5g002Ij1;Tg002ij16Tg00S;j1?Tg003Nj19Tg003lj1<Tg01D]j2ETg01H[j34Tg01EIj35Tg0014j37Tg01Gbj20Tg009^j31Tg00:8j1=Tg01FYj23Tg00\Fj28Tg00]Qj2FTg00OUj3:Tg00C3j3DTg00B;R0j2CTg00D_j3@Tg01Ial9ATg00:Xj6BTg001gj5>Tg00acR1f0R2g00bCR331p=2g00h6g00l7#;R4g00i]#6R5#?#9R6%65#6#6#6#6#9#<R5'ER7%<6R6#;R8P6f5R9f4R:;42#2f7R;f6R<;5:f8R=?5<:A762:R>f1R?,0;R@10=?RA515[^06[[[X58A1133f3R395<9R1A5;93RB%=6RC9762RDg00k>f2RE,0;10=E515P2n010000000W1X06W4W3W2A4:3C#210<?=15@\D^06\B\1[eA4<92#2A5=;9f9R1?5;9101?RB915A\>^06[[[13<E13;E'8A4;<?'F#2A51=<R>f:RA?5=<RDA:6<99762R@f;RC/3;f<RF/3;'8RGA4FC<RH;D:%2G%2H'CP013F=f=R0/3='8#2A40F;#210C310F3515P2f>RH/3Af?RG/3A'8#2f@R:?4GA#2g00@^A16F<A76<C10G;10:;515P9A160;P6PHfAR0/02fBR9/02515X06fDfCRGP9P0P:PHPAP1139H13GH;@3M9AP=P2EBW7P2O1A76;FPFPEPAP1P=P2O5W1P2O1n200100000021000010000W9W8P?P2O2n2001000000120000000b2W1X06W4W3W2A:6E?94;<#210A?915B\@^06\D\>[eW:X>8X=6P2D>W5X<7W;X@4W?W6o"). Qed.
End VP5.

Section VP6. Context {fx : FPState}.   (* [comment removed for export] *)
Lemma keeps_cs_of_same : forall E sr sr' R R',
  same_regs sr sr' callee_saved = true -> regs_ok E sr R -> regs_ok E sr' R' -> keeps_cs R R'.
Proof.
ltac2:(KReplay.run1 (kr_t_SymAux ()) ["VP6"] "h01Eh12HRh23HR'h33Hinh42Hsh51Rh62R'h71rh82srh93sr'p;1p;2p;3p;;g002Ij1;Tg002ij10Tg00S;j16Tg003Nj11Tg003lj13Tg01D]j2:Tg01H[j39Tg009^j35Tg01EIj32Tg0014j37Tg01Jjl;4Tg01L6j28Tg00h6g00l7#;R0g00i]#0R1#6#1R2%01#0#0#0#0#1#3':R1g00acf3R3f2R4g01M7R539g00bC35f5R6f4R7;24f6R8?274%32R2f0R9=725f9f8f7P8P6P5P7P3P4f1P9M;4W3W71873eW2W1W4X61W5X90W8W0o"). Qed.
End VP6.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section VP7. Context {fx : FPState}.   (* [comment removed for export] *)
Theorem run_sound_log : forall segs fuel stops scr pc sr log kn nx ss' scs scr' E base rom regs,
  sym_exec segs fuel true stops scr (SS pc sr log kn nx) [] = (ss', scs, scr') ->
  regs_ok E sr regs -> log_flat E log -> know_ok segs E base kn ->
  scs_denot segs base E scs ->
  exists R, regs_ok E (s_regs ss') R
         /\ log_flat E (s_log ss')
         /\ msteps segs (mkst regs (Z_to_bv 64 pc) (mem_denot E base log) rom)
                        (mkst R (Z_to_bv 64 (s_pc ss')) (mem_denot E base (s_log ss')) rom).
Proof.
ltac2:(KReplay.run1 (kr_t_SymAux ()) ["VP7"] "h04regsh11Eh22HKh32HRh43Hexh53Hlfh63Hsch74baseh84fuelh92knh:3logh;2nxh<2pch=3romh>3scrh?4scr'h@3scshA4segshB2srhC3ss'hD5stopsp;1p;2p;5p;7p;4p;3p;Bg002Ij12Tg002ij11Tg003Nj1<Tg003lj1>Tg00o7j1LTg00S;j1KTg01D]j2HTg009>j2ATg01N<j5:Tg00:8j1ETg01OJj7DTg00[fj4=Tg009^j38Tg01EIj39Tg019[j23Tg01PUj47Tg01Qej4JTg00Foj25Tg01:lj34Tg01S7j56Tg01T0j1CTg01U7j1BTg01V?j1@Tg01WHj1?Tg00B;j20Tg00GUj2GTg016hj4;Tg01XQj4FTg01XklBITg01Z?#2g00i>R0g00cmR1#2g01[>R2g00l7#2g01CR#2g01\J#2g01]UR3g01^cR4#2R5g00h6g00i]#1R6#1#1R7#1#1#1#<R8#>R9%<7#>#L[R7%K6#</H9R91A35R6/A2f?R:f>R;g00bCR<f=R=f<R>f;R?f:R@f9RAf8RBf7RCD:%E4R4FDP6P2P3P5f6R5f5R3C=f4R6C=38f1RD996?133?fBREP5P3P?C7fCRFP5PCPACJp,2fxRGfDRHPFP<PEfAREf@R<P:P;P=P>D:R>P4P?P@PAPBPCP5PGP3158<A4BC;P5D6R@P6f0R6P9g01`0R?PGP5158EA4AB:PCD6PGP6PEP<P:P;P=D:R<#C,58%B<RE94ABPCD638%@<=9A613AEfEPAPB%?<C7'0'0'0X09P3A8?@@A9B:3R:13B;R;PHPBPCP=C7R='0R9'01G?@P:P9f3P;P=f2PDC;C;C;PGP3%C>,58%B>R894BCP5D698?@%@>=9B313B8PHPBPC%?>C7'0'0'0eCFMBIW6W2W5W3W4W0X=7W7W1X?2W@WCX;0W9W:WBX<1W>WDW8WAo"). Qed.
End VP7.
