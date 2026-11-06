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
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.CJ.Lib Require Import Tac Image ZBridge SysStep SFModel Arr.
(* [comment removed for export] *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.CJ.Agent Require Import F_syscalls MallocRep F_malloc_free MallocTree.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.CJ.Spec Require Import STree Malloc MallocCtrl.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.CJ.Agent Require Import MallocKit_B MallocModel_B MallocKit_B3 F_ntf_B.
Import ListNotations.
Open Scope Z_scope.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.CJ.Lib Require Import RunP.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require KReplay.
Ltac2 kr_t_F_am_K () := "C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc4aptrC13~~~I35stdpp9countable9Countable00C35stdpp8fin_maps:map_insertC35stdpp4base;RelDecisionC35stdpp4gmap;gmap_lookupC35stdpp4gmapBgmap_partial_alterC35stdpp4base4fmapC35stdpp4base6LookupC35stdpp4base6InsertC99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc4optrC13~~~C35stdpp6option;from_optionC47Corelib4Init9Datatypes2IDC46Stdlib5Lists4List=repeat_lengthC47Corelib4Init5Logic8eq_ind_rK47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ5Agent9MallocRep2b8C13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ5Agent9MallocRep5zerosC13~~~C47Corelib4Init9Datatypes6lengthI47Corelib4Init5Logic2eq00I47Corelib4Init9Datatypes3nat00K47Corelib7Numbers7BinNums8positive03K47Corelib7Numbers7BinNums1Z01I47Corelib4Init9Datatypes6option00C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib3Mem8bytes_atC13~~~C56Stdlib6ZArith6BinInt1Z6of_natK47Corelib7Numbers7BinNums1Z02C56Stdlib6ZArith6BinInt1Z3powC47Corelib4Init5Peano2ltC56Stdlib6ZArith6BinInt1Z3addC46Stdlib5Lists4List9nth_errorI47Corelib4Init5Logic3and00c99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ5Agent6F_am_K<zeros_lengthC13~~~C47Corelib4Init5Logic6eq_indC56Stdlib6ZArith4Znat5Nat2Z9is_nonnegC56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z:pow_nonnegC56Stdlib6ZArith6BinInt1Z7compareK47Corelib4Init5Logic2eq01K47Corelib4Init9Datatypes3nat02K46Stdlib9micromega=RingMicromega5Psatz02K46Stdlib9micromega:ZMicromega;ZArithProof02K47Corelib4Init9Datatypes4list01I47Corelib4Init9Datatypes4list00K46Stdlib9micromega6VarMap1t02K46Stdlib9micromega6VarMap1t01I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr01K46Stdlib9micromega7EnvRing5PExpr02K47Corelib4Init9Datatypes6option02C46Stdlib9micromega5Tauto8BFormulaC46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundK47Corelib7Numbers7BinNums8positive01K46Stdlib9micromega7EnvRing5PExpr07C56Stdlib6ZArith6BinInt1Z6to_natC47Corelib4Init3Nat3addC47Corelib4Init5Logic8iff_reflC46Stdlib9micromega;ZifyClasses3injC46Stdlib9micromega;ZifyClasses5mkrelC56Stdlib6ZArith6BinInt1Z2ltC46Stdlib9micromega;ZifyClasses7rew_iffC56Stdlib6ZArith6BinInt1Z8max_specC56Stdlib6ZArith6BinInt1Z2leI47Corelib4Init5Logic2or00K47Corelib7Numbers7BinNums1Z03K46Stdlib9micromega7EnvRing3Pol01K46Stdlib9micromega=RingMicromega5Psatz04C46Stdlib9micromega;ZifyClasses;rew_iff_revK47Corelib4Init9Datatypes6option01C47Corelib5Lists7ListDef6repeatC46Stdlib5Lists4List@nth_error_repeatK47Corelib4Init5Logic3and01C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib3Mem2waC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib3Mem3mrdC13~~~K46Stdlib9micromega=RingMicromega5Psatz06K47Corelib4Init9Datatypes4list02K46Stdlib9micromega6VarMap1t03K46Stdlib9micromega=RingMicromega7Formula01K46Stdlib9micromega7EnvRing5PExpr03K46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega5Tauto8GFormula08C56Stdlib6ZArith6BinInt1Z3maxC46Stdlib9micromega;ZifyClasses5mkappC46Stdlib9micromega;ZifyClasses6mkapp2K46Stdlib9micromega5Tauto8GFormula03K46Stdlib9micromega5Tauto8GFormula05K46Stdlib9micromega5Tauto8GFormula06C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ5Agent:F_syscalls5asegsC13~~~I47Corelib7Numbers7BinNums1Z00I46Stdlib9micromega:ZMicromega;ZArithProof00K46Stdlib9micromega=RingMicromega3Op203C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K47Corelib4Init9Datatypes4unit01C46Stdlib9micromega8ZifyInst@of_nat_to_nat_eqC56Stdlib5Arith8PeanoNat3Nat3addC56Stdlib6ZArith4Znat5Nat2Z7inj_addC56Stdlib6ZArith4Znat5Nat2Z6inj_ltK46Stdlib9micromega=RingMicromega3Op201K46Stdlib9micromega=RingMicromega3Op205I47Corelib4Init5Logic4True00I47Corelib4Init9Datatypes:comparison00K47Corelib4Init9Datatypes3nat01K46Stdlib9micromega:ZMicromega;ZArithProof01I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01C46Stdlib9micromega8ZifyInst7Inj_Z_ZC99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib3Mem5wr_atC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib5Cells8cells_wfC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib5Cells;cells_bytesC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib5Cells:cells_sizeC13~~~c99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ5Agent6F_am_KBbytes_at_zeros_subC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ5Agent=F_malloc_free9wr_at_subC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ5Agent=F_malloc_freeArw_cells_of_bytesC13~~~I99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib5Cells4cell00C13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ5Agent9MallocRep2wzC13~~~K99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib5Cells4cell01C13~~~K99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib5Cells4cell02C13~~~I99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc6mstate00C13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc1MC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc7am_takeC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc8am_carveC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc4aaddC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6MallocDset_avail_meta_countC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc>set_avail_metaC13~~~c99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ5Agent6F_am_K8carve_stC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc7upd_ctxC13~~~I99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc4mctx00C13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc8AREA_HDRC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc6NSLOTSC13~~~".
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Section CEIL_WRAP_1.
Context {RUNp : RunP}.


(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma zeros_length n : length (zeros n) = n.
Proof.
ltac2:(KReplay.run1 (kr_t_F_am_K ()) ["CEIL_WRAP_1"] "h01np;1p;3p;2p10000p4p70R0p1001>p4p710p8P0p1001\R1p4p710p8P0p10028R2p4p710p8P0P2p4p7210p8P0p1002QR2p4p710p8P0p1002jR3p4p710p8P0p1003Jp4p73110p8P0p1003\R4p4p710p8P0p10040R0p4p710p8p1004Dp4p70R5P1p4p7210p8P5P1p4p73110p8P5p1005RR1p4p710p8P5P1p4p7210p8P5p1005mp5p710p8P5P2p4p741110p8P5P3p4p741110p8P5P4p4p7210p8P5P4p4p73110p8P5P0p4p7210p8P5P0p4p73110p8g006IR0p4p710p1006kp4p710p8g007Ij10Tg007nj17Tg008Lj12Tg008oj11TP0j36Tg00:?j15Tg00;Rj23Tg00<2j34Tg00<LR0g00<k#0#0#0#7#2R5g00=P#1f0R436%54,35=404eX00P4O1W0o"). Qed.

Lemma bytes_at_zeros_sub m A n off k :
  bytes_at asegs m A (zeros n) -> 0 <= off -> off + Z.of_nat k <= Z.of_nat n -> bytes_at asegs m (A + off) (zeros k).
Proof.
ltac2:(KReplay.run1 (kr_t_F_am_K ()) ["CEIL_WRAP_1"] "h04__x1h14__x2h21ih36__sat3h44__x3h54__x4h61nh77__arithh84__ffh98__varmaph:5__with;4cstrh<5cstr0h=4__p1h>6__sat4h?1xh@1HhA3Hi0hB6__sat2hC5cstr1hD1mhE1ohF1AhG2H1hH2H2hI2HBhJ2HahK4__p2hL4__x5hM1khN3offhO2z2hP2H0hQ2HihR2HkhS4HoffhT1yhU1zp%0p&0p;1p;4p;2p;3p;6p;<p;5p;7p;8p;Bg007Ij1DTg007nj1uTg008Lj1fTg00=nj1~Tg00:?j13Tg00>Pj4^Tg00;Rj2:Tg00?^R0j11Tg00@>j1eTg00@\j2}Tg00A9R1j27Tg00AQR2j20Tg00Anj35Tg00BLR3j26Tg00Bgj1pTg00D>j6\Tg00DZj1=Tg00E?k20?Tg00Egk309Tg00FKk208Tg00Flj2RTg00GFj1PTg00Gej2LTg00HNj2MTg00I:k102Tg00IZj1|Tg00J:j2TTg00JXj1zTg00K6j1wTg00KTj1vTg00L?j2`Tg00Lbj2ETg00MEk10ITg00Mgk20HTg00NIk20GTg00<2j3Ck10BTg00O5k30FTg00OTk40ETg00PFj1rTg00Pkk30CTg00QNR4j1qTg00Qnj2oTg00REk10ATg00Rck40@Tg00SFl<iTg00SkR5j2<Tg00TGj4hTg00Tnj2gTg00UPj2ITg00Ulj2UTg00VFk107Tg00Vdk206Tg00WEk305Tg00Wnj4VTg008ok104Tg00XYk203Tg00Y;j3WTg00YZj5bTg006kj6NTg00Z?j4aTg00ZZj1sTg00[bj3jTg00\kk300Tg00]Tk30:Tg00^4k40;Tg00^Rj4STg00_=k30<Tg00_`j7]Tg00`Dj8mTg00`hj2{Tg00aEl<nTg00ajlBtTg00bPk60DTg00c4j7yTg00cXj7xTg00=PR6f0R7'Ip=2f2R8f1R9'0/I7p=4f3R:g00d<R;%s97j8;C7p=91<67p=Fg00ePR<@0097p=;g00enR=@0:97p=GP<P8P9P7H0;p=JP<P9g00fZR>P7CSp=@B0<<97p=BP8g00gAR?g00g`R@P@g00h@RAP<P9P>P7CSg00h`R>F]p=_f4RBP?P@P@PAP:P?P@P@PAP8P>F]P9P7Gmp=>AC<97p=?1{67p=H1R<7p=8P<g00<LRCP<P<P4PBP0P:g00i@P8P9P7M<np=lPCPCPCP<P<P<g00imP0P0P0P2g00jMf5R4PBP:P8P9P7MBtp=kPCP<P<P<P0P0P4PBP:P8P9P7M<np>0>P<P<P<P<P<P<P2P7P9P8P2P:PBP4f6R2f7RDf8REf9RFMBtp>0=PCP<P1P0P5g00k0P4PBP:P8P9P7M<ip=[AC<76p=QP9P?P@P@PAP7J0Dp=ZP<P9g00kRP7CSp=KP9P?P@P@PAP7P>F]p=AP8P?P@P@PAP9P7Fyp=OP8P?P@P@PAP9P7Fxp=dP:P?P@P@PAP8P9P7Gmp=XA58979CB:p=cP<P9g00l9P7CSp=Y%s79j;9p>01g00<kR?#DR>#DR5#DR0#D#D#DR1#uRG#f%u0#fR0#~RH[RIP;PBP:%38C^P3%2BRJ%3:,:0#1%e>RK%e1R1'}RL54B%3BRM,:0,77PHPD%19RN,02%34=509C9[^2C'6%2:%1:RO%1454BP;PE10D4PMC^[[P7%22RM%32,:0#1=4DL%3D,:0RP,77PHf:RQ10FN%3ERR=509C9[^2C'6P3%1P=4EL1:0R,77PHf;RP10QN%3FR3=509C9[^2C%2D%1D%1F54EP;f<R;10PFPRC^[[P71:03#1=4QL%3P,:0,77PHf>R3f=RR/0N%3;=509C9[^2C%2Q%1QS00%1;S0154PPC%3R,:0R;f?RQ%17RS;4LX6CP:PR%pRS02E\%1RRT=43LPC%33,:0RU1779RVPHfCRWfBRX/0NfARY#3RZ=509C9[^2CX6CP:P3%p3E\177QPHPX10YNf@R[#3S03=509R\C9[^2C10[3R]#2%1;=4]L177UPHPW10X[/0NRU%3Q=509C9R^[^2C'6%=RR_%2TR`%=[Ra%1[Rb#2Rc20?K1Rd%FKRe%21%FL[Rf[Rg%2KRhg00l`RiB09K19UWJR1%2L\i^JhRhP9g00m<2086K'RPeeO1RePfg00mbRi#PRj#PRk,L<Rl1L<j1L<iRi';';Rjg00nARm'MRn&02=Ro'GRp%|=R=1T<8%z<Rq7J9S04%w<Rr%v<RsPs1`<6Rt1E<>Ru'@&0I@R@PsPs1E<?Rv,@tP@1BvuRw9_stD>D>20HsARAP7P8g00nmRxg00oMRy'R20G78=CxydB0F<69H0ERyb8b9b:X0<X1<%29Rx108:Rz#2\x[^0<^1<P7fDRxfFR{PFPQO4b7b3bBb3b<b;PCPR10YQ?4SLPHPx10WYRR/0NP\C9\V^2C'6X6CA4]TL1773R3P^[^2CP_P`PaPcPdPgP1PhPePfPpP=1T<BRp?J8q1T<:7J9RcPrPsPs%r?Ra,E<R`,BuR_1E<5R5'@P@PsPs1Bv5R^1`<K>0C<GRG'@P@1Bw`=_sGD>D>PAPyb8b9b:X0<X1<X4<X5<A498:A49BLA4zBL[[^0<^1<^4<^5<P7fERz#1RL%1WPxP{PEPDO6b7b3bBb3b<b;%q[RG/o9RK#1R],0XRT/?US05%H[RV/0NR\,0XR|/?UP<P<&0B<R}P7X?<R~P}1?97$0AXT<X?<PTP|P~P~P~P<P<g00om1097H0@#8XD<X6<PXPX%8XP]P\P~P~%8SX?CPKP\PGPVP~%H7X?<RVP[P[%8[DlP9PN%8NRGEkJ0>N:0=PUPU%8UM<i179Q%1QRU,<NR\P9PNPGPQPU%8UE[P7ChP\%=8%18R\#2%=Y%1Y#2%=x%1x#21g6x%Fx%HxRU/?x'61Ix6%QU'6'U%HzRUP<PdPgP1PhPePfp-0RG%PkRk,L<RN&07?-06<>05<l/;iR?';/Mm1M?m/Go'G,GnP=PcPrPs1Zs21Ku5,As5OsA_s5t1Kut,As5Os5dsP@PsPs1@t5P@1Bv_1B^`'K,AsD>CXPAPyb8b9b:X0<X1<X4<X5<W=1?9:,6B1I:6%Q9'6'U10:B,081084/0B'?\J[^0<^1<^4<^5<^=GP7fJRJ#FPJ%1PPBfLRPP4PQO7b7b>b3b>bObHbCb<b;bACVQ05P<%qYR^/o8R_#1,0WRWPHPzP7A50Z:RZC9XU<PH%3X=50_R5ACH7ZXEHPH&046RZ-030RcPHP7P0AW0ZYP:DcXEHPHPcACHc7XEH1RHcAW0Z[=508P0PZP[P8178[Rc1<\bRnP8P\%8\R?P[Pb%8bE[RbPcPnPbP9ChRbPn%=:Rc%2ORO%=XRK%1XRS#2R]%=zR|%2LRLPdPgP1PhPePfPoP=Q04PrPs1Yvu,AsRTP@PTCXPAPyb8b9b:X0<X1<1<791<98[^0<^1<P7fH#1Q00PDO3b7b3bBb3bCb<b;bACVDbENAW0ZX=50_P0PZPXP_17_X%HYRZ/0\RT/<SP_PTP^PZP~PVPYPY%8YDlP8P\P?EkPXPS%8SE[PbPnPcPOPKP]P|PL1g6z%Fz1?Uz'61Iz6%QU'6'U%H{P<PdPgP1PhPePf%Pk,L<Rk1;Nj';/Mm1;li,;N,;k/Mm/Go'GP=1T<49Jq8AJp:q7J9PrPs1ZsD%r>,E<R>,Kv,As5Os1ZsE1Kvt,As5Os5dsP@PsPs%Da,E<Ra,YuP@PsPs1B>a/@`P@PsPs1@t>P@1Yw`,AsD>D>D>CXPAPyb8b9b:X0<X1<X4<X5<XL<X=GXKG1?7:,64%Q7,62'U1<84A442B10B4/<2\M[[[^0<^1<^4<^5<^L<^=G^KGP7fKRG/I6%FG%1JPG%1PQ01PBP4PFPQP[O;b7b>b3b>bObHbCb<b;bACVR[DbENPHP5P0Q03P8Dce201xWP:P_P[O2EN10R\P7E\b@XQ3X2CCaP;Q02ENCabIbGWRWSWIWGP9P7O2n2001000000121000000W@WPP9P7O2n2001000000121000000W@XMCXN<X6CXF<XDIPBP:P8P9P7O5XMCXN<X6CXF<WDo"). Qed.

(* [comment removed for export] *)
Lemma rw_cells_of_zeros m A n off cs :
  bytes_at asegs m A (zeros n) -> wr_at asegs m A (Z.of_nat n) ->
  cells_wf cs -> cells_bytes cs = zeros (cells_size cs) ->
  0 <= off -> off + Z.of_nat (cells_size cs) <= Z.of_nat n ->
  rw_cells asegs m (A + off) cs.
Proof.
ltac2:(KReplay.run1 (kr_t_F_am_K ()) ["CEIL_WRAP_1"] "h04__x1h14__x2h21Ah37__arithh44__ffh58__varmaph65__with74__x3h84__x4h92csh:4cstrh;5cstr0h<1mh=1nh>3offh?1Eh@2HBhA2HWhB4HoffhC3HszhD2WFhE1lp;1p;4p;3p;2p;8p;6p;9p;7g007Ij12Tg007nj1CTg008Lj1>Tg00=nj1GTg00IZj1<Tg00:?j1;Tg00>Pj4?Tg00?^j10Tg010Qj4JTg011\j1HTg012lj1BTg014?j18Tg00<2j3@Tg00UPj21Tg00AQj23Tg015Qj8WTg006kj6VTg00DZj1ATg00I:j1UTg00J:j2:Tg00JXj1RTg00^4j49Tg00K6j1MTg00KTj1LTg00L?j2KTg00Lbj25Tg00MEj1ITg00_=j37Tg00Mgj2FTg00Flj2NTg00NIj2OTg00O5j3ETg00OTj4PTg00PFj1QTg016nl9DTg018Ij7STg00^Rj4TTg00_`j7YTg00`Dj8XTg00ePR0f1R1g00fZf0R2CTp=6P1g00gAR3g00g`R4P4g00h@R5P2g00h`FYp=4f3R6P3P4P4P5f2R3P1P2GXp==g00<kR7#2R8#2R9#2R:#2#2#2#C#>%C:#>R:#G[R;g00<LR<g019l#<R=g00d<R>f4R?P6%;3C?P>f5R@P?%06CJ%H3%<:R:%B6%86#;3@g00=PRA/1@f6RB%8@#0'3f7RC#0'1P>f:RDf9RE/3CRFPBP6P:%8BRG#;P>f;RHf8RI,3DP2C?XE:PDPEPIPCPGP@P1P2GW%BBP3EVP>PDPE%0IPF%0GRFP?%AGRG11AFRF%AERI%0E,1AR>g00enRB#UR@%<BRBP01:03P1%R0RCC9%M0R:%L0RJ1K0A1508R8'6,4J%I4R41507RKA70K8RL'6,4JC=1FJ5R5P2P3g00nmRMg00oMRN'N1O23=@MNdAE0A1CPRNb4b5b6X00X1011A11313RA,11[^00^10P2PDf<RMP?O3b3b;b:PGPFPIP>P@PBP0P01:0?P3PCC9P11:06C9P:PJ%Q7,50R797081509R9'6,4JP4A70L7A70K9'6,4JC=P5PNb4b5b6X00X10X70X8011A613A6131?'1[^00^10^70^80P2%0H%8E#0PDPMP6O5b3b;b:M9DFSWCWBW?WDWAW@X9=X>0X=<X20X<;P?P6P3P1P2O5W9X>0W=X20W<o"). Qed.

Lemma le8_zero : le8 (wz 0) = zeros 8.
Proof.
ltac2:(KReplay.run1 (kr_t_F_am_K ()) ["CEIL_WRAP_1"] "p;1p;2g007Ij11Tg007nj16Tg008Lj13Tg00IZj12Tg00GFj10Tg00:?j15Tg00Flj24Tg00<k#1#1#1#6#3#2g00mb#0#0#0#0#0#0#0#0#5'4o"). Qed.
Lemma le4_zero : le4 (wz 0) = zeros 4.
Proof.
ltac2:(KReplay.run1 (kr_t_F_am_K ()) ["CEIL_WRAP_1"] "p;1p;2g007Ij11Tg007nj16Tg008Lj13Tg00IZj12Tg00GFj10Tg00:?j15Tg00Flj24Tg00<k#1#1#1#6#3#2g00mb#0#0#0#0#5'4o"). Qed.

Lemma meta_cells_meta0 st : meta_cells st meta0 = [C8 (wz 0); C8 (wz 0); C8 (wz 0); C4 (wz 0); C4 (wz 0); C8 (wz 0)].
Proof.
ltac2:(KReplay.run1 (kr_t_F_am_K ()) ["CEIL_WRAP_1"] "h02stp;1p;2p;3g00IZj17Tg01;:j16Tg01<Jj12Tg01=Xj11Tg00I:j15Tg00Flj23Tg00]Tj34Tg019lR0f1f0R134p=0g01>fR2%70g00=P#6R3#2R4%13R3%50,04,03'0,04,04'0'3X02P1O1W0o"). Qed.
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)

Definition carve_st (st : mstate) (p : aptr) : mstate :=
  let st1 := upd_ctx (fun c => set_avail_meta_areas (Some (aadd p 4096)) (set_avail_meta_area_count (c_avail_meta_area_count c - 1) c)) st in
  let st2 := match c_meta_area_tail (ctx st1) with
             | Some tl => set_areas (<[tl := match (s_areas st1) !! tl with
                                              | Some a => mkArea (a_check a) (Some p) (a_nslots a)
                                              | None => mkArea 0 (Some p) 0 end]> (s_areas st1)) st1
             | None => upd_ctx (set_meta_area_head (Some p)) st1
             end in
  let st3 := upd_ctx (set_meta_area_tail (Some p)) st2 in
  let old := default (mkArea 0 None 0) ((s_areas st3) !! p) in
  set_areas (<[p := mkArea (c_secret (ctx st3)) (a_next old) NSLOTS]> (s_areas st3)) st3.

Lemma am_carve_eq {R} st p (k : mstate -> optr -> M R) bail :
  am_carve st p k bail = am_take (upd_ctx (fun c => set_avail_meta (Some (aadd p AREA_HDR)) (set_avail_meta_count NSLOTS c)) (carve_st st p)) k bail.
Proof.
ltac2:(KReplay.run1 (kr_t_F_am_K ()) ["CEIL_WRAP_1"] "h01Rh14bailh21kh31ph42sth51cp;1p;2p;4p200R0g01@8R1p4p710p8P0g01ACR2p4p710p8P0p101BTp4p710p8P1j10Tg01Cfj28Tg00XYj22Tg01E4j21Tg01FRj27Tg01Gjj26Tg01I=j23TP2j44Tg00Flj25Tg01>fR2g0000R1g004Df4R3#0R4[\2R5f3R6#0R7P3g01JNg01K^,86,21g01M0f0R8'1'7W5f2R9,66'3f1R:P8C4,54X17X25X31X42X00P3P6P9P:P8O5W1W2W3W4X00o"). Qed.
End CEIL_WRAP_1.

(* [comment removed for export] *)
