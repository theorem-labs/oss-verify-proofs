(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Spec Require Import FseNCount FseLemmas HufPure_FseDecomp HufPure_HufStats HufPure_HufX2
  HufPure_HufTableX2.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Lib Require Import Arr Bytes ZBridge.
From OSSVerify.Proofs.zstd.huf_decompress.lib.LibA Require Import Shadow.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Plain Require Import RF_huf_tbl_iface.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Plain Require RF_huf_tbl_kit RF_huf_fdw_kit RF_huf_bdt_model RF_huf_x2t_model RF_huf_x2t_c1 RF_huf_x2t_fr
  RF_huf_x2t_c2.
From OSSVerify.Proofs.zstd.huf_decompress.lib.AsanW Require Import AImg ABase RtCells Stdio_kit AHarness_iface AF_huf_tbl_iface AF_huf_bdt_kit
  AF_huf_tbl_iface2 AF_huf_fdw_kit AF_huf_x1t_cls AF_huf_x2t_kit.
From OSSVerify.Proofs.zstd.huf_decompress.lib.AsanW Require AF_fse_rd_base.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Common Require Import RunDraw FseRdKit HufWalkKit StrFun.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Common Require Import FseWalkKitF.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Common Require FseWalkKit FseRdKit2.
From OSSVerify.Proofs.zstd.huf_decompress.lib Require KReplay.
Ltac2 kr_t_AF_huf_x2t_kit2 () := "C56Stdlib6ZArith6BinInt1Z2leK47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1Z02C56Stdlib6ZArith6BinInt1Z2ltI47Corelib4Init5Logic3and00C56Stdlib6ZArith6BinInt1Z3mulC56Stdlib6ZArith6BinInt1Z3addC56Stdlib6ZArith6BinInt1Z3lorI47Corelib4Init5Logic2eq00K47Corelib4Init9Datatypes4list01I47Corelib4Init9Datatypes4list00K46Stdlib9micromega6VarMap1t02I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr01K46Stdlib9micromega7EnvRing5PExpr02K46Stdlib9micromega=RingMicromega7Formula01K46Stdlib9micromega5Tauto8GFormula05K47Corelib4Init9Datatypes6option02K46Stdlib9micromega5Tauto8GFormula08C46Stdlib9micromega5Tauto8BFormulaK47Corelib4Init5Logic2eq01C46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundc69OSSVerify5KrLib5AsanW?AF_huf_x2t_kit24X2C26d2_valC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib5AsanW?AF_huf_x2t_kit24X2C27d2_baseC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic8eq_ind_rK46Stdlib9micromega5Tauto8GFormula04C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K47Corelib4Init9Datatypes4unit01I47Corelib7Numbers7BinNums1Z00K47Corelib7Numbers7BinNums1Z01K47Corelib7Numbers7BinNums8positive03I46Stdlib9micromega:ZMicromega;ZArithProof00K46Stdlib9micromega=RingMicromega3Op203K46Stdlib9micromega=RingMicromega3Op205I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01K46Stdlib9micromega6VarMap1t01K46Stdlib9micromega5Tauto8GFormula06I47Corelib4Init5Logic2or00c69OSSVerify5KrLib5AsanW?AF_huf_x2t_kit23X2M?build_x2_fieldsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4SpecBHufPure_HufTableX28build_x2C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec=HufPure_HufX26x2_seqC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3eqbC59OSSVerify5KrLib4Spec=HufPure_HufX29x2_nbBitsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec=HufPure_HufX26x2_lenC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00C45stdpp9bitvector;definitions7Z_to_bvC56Stdlib6ZArith6BinInt1Z3divC56Stdlib6ZArith6BinInt1Z6shiftrC45stdpp9bitvector;definitions;bv_unsignedC56Stdlib6ZArith6BinInt1Z6moduloC56Stdlib6ZArith6BinInt1Z7div_modC47Corelib4Init5Logic3notC56Stdlib6ZArith6BinInt1Z=mod_pos_boundC56Stdlib6ZArith6BinInt1Z=mod_neg_boundC56Stdlib5omega8PreOmega1Z;div_0_r_extC56Stdlib5omega8PreOmega1Z;mod_0_r_extK47Corelib7Numbers7BinNums1Z03K46Stdlib9micromega7EnvRing3Pol01K47Corelib4Init9Datatypes3nat02K46Stdlib9micromega=RingMicromega5Psatz02K46Stdlib9micromega=RingMicromega5Psatz07K46Stdlib9micromega:ZMicromega;ZArithProof03K46Stdlib9micromega5Tauto8GFormula07K47Corelib7Numbers7BinNums8positive01K46Stdlib9micromega7EnvRing5PExpr07C56Stdlib6ZArith6BinInt1Z3powC59OSSVerify5KrLib3Lib6MState<unsigned_litC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib5AsanW?AF_huf_x2t_kit23X2C;le2_lo_cellC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic6eq_indC56Stdlib6ZArith6BinInt1Z?shiftr_div_pow2c69OSSVerify5KrLib5AsanW?AF_huf_x2t_kit23X2C;le2_hi_cellC1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic3and01c59OSSVerify5KrLib5AsanW?AF_huf_x2t_kit26v2_valC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes4list02C59OSSVerify5KrLib3Lib3Mem3le2C1?~~~~~~~~~~~~~~~K46Stdlib9micromega=RingMicromega5Psatz04K46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega=RingMicromega5Psatz05K46Stdlib9micromega:ZMicromega;ZArithProof02K46Stdlib9micromega6VarMap1t03K46Stdlib9micromega7EnvRing5PExpr05K46Stdlib9micromega7EnvRing5PExpr03K46Stdlib9micromega=RingMicromega3Op201K46Stdlib9micromega:ZMicromega;ZArithProof01K47Corelib4Init9Datatypes3nat01I47Corelib4Init5Logic5False00".
Import ListNotations.
Open Scope Z_scope.
Set Warnings "-notation-for-abbreviation".
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module X2M := OSSVerify.Proofs.zstd.huf_decompress.lib.Plain.RF_huf_x2t_model.
Module X2C := OSSVerify.Proofs.zstd.huf_decompress.lib.Plain.RF_huf_x2t_c1.
Module X2C2 := OSSVerify.Proofs.zstd.huf_decompress.lib.Plain.RF_huf_x2t_c2.

Section CANSEC1. Context {rc : runConstT}.

(* [comment removed for export] *)
Definition x2l2offs : list Z :=
  [4; 19; 12; 27; 20; 35; 28; 11; 4; 4; 19; 12; 11; 4; 4; 11; 8; 7; 4; 4; 7; 4; 4; 19; 12; 27; 20; 35; 28; 11; 4; 4; 4].

Definition x2l2cells (DT st sym1 : Z) : list cell :=
  map (fun k => C8 (Z_to_bv 64 (DT + k + 4 * st))) x2l2offs ++ [C8 (Z_to_bv 64 (Z.lor sym1 33554432))].

Definition x2l2frA (m : amem) (SPA DT st sym1 : Z) : Prop := rw_cells asegs m (SPA + 296) (x2l2cells DT st sym1).

(* [comment removed for export] *)
Definition x2next2A (SP SPA : Z) (gp tp : word) (F : bvmap 5 word) (fc : bv 32) (m2 : amem)
    (y1 y5 y6 y7 y10 y11 y12 y13 y14 y15 y16 y17 y18 y19 y20 y21 y22 y23 y25 y26 y27 y28 y29 y30 y31 : word) : machine_state :=
  MS (mkR y1 (Z_to_bv 64 SPA) gp tp y5 y6 y7 (Z_to_bv 64 SP) (Z_to_bv 64 SPA) y10 y11 y12 y13 y14 y15 y16 y17 y18 y19
          y20 y21 y22 y23 (Z_to_bv 64 2147450880) y25 y26 y27 y28 y29 y30 y31)
     F (Z_to_bv 64 0x82728) fc None m2 (seg_rom asegs).

(* [comment removed for export] *)
Definition x2c2A_stmt (pc : Z) (P : Z -> Prop) : Prop :=
  forall (SP SPA : Z) (gp tp : word) (F : bvmap 5 word) (fc : bv 32) (RNG : footprint)
         (x1 x5 x6 x7 x14 x15 x17 x18 x19 x20 x21 x22 x23 x26 x27 x28 x29 x30 x31 : word)
         (m0 m1 : amem) (DT WK T nbb maxW minB scl st off sym1 b e tb tl len : Z) (sorted : list (option Z))
         (js jt : list byte) (ncells : nat) (dt : list (option deltX2)) (r : list (option deltX2) * Z)
         (Q : machine_state -> Prop),
  P len -> len = 2 ^ (tl - tb) -> 1 <= tb <= tl -> tl <= 12 -> 0 <= sym1 < 256 ->
  fill_for_weight (S (Z.to_nat (e - b))) dt (st + off) b e tb tl sym1 2 sorted = Ok r ->
  0 <= b <= e -> e <= 256 -> 0 <= st -> 0 <= off ->
  length jt = (4 * ncells)%nat -> length js = length sorted -> length sorted = 256%nat ->
  (forall i v, nth i sorted None = Some v -> 0 <= v < 256) ->
  x2placeA RNG m0 SPA DT WK js ncells ->
  x2l2frA m1 SPA DT st sym1 ->
  x2fA_inv m0 m1 SPA DT WK T nbb maxW minB scl js jt sorted ncells dt ->
  (forall m2 dt' (y1 y5 y6 y7 y10 y11 y12 y13 y14 y15 y16 y17 y18 y19 y20 y21 y22 y23 y25 y26 y27 y28 y29 y30 y31 : word),
     r = (dt', st + off + (e - b) * len) -> x2fA_inv m0 m2 SPA DT WK T nbb maxW minB scl js jt sorted ncells dt' ->
     x2l2frA m2 SPA DT st sym1 ->
     munch [(DT + 4, DT + 4 + 4 * Z.of_nat ncells)] m1 m2 -> wmono asegs m1 m2 ->
     evtF asegs RNG Q (x2next2A SP SPA gp tp F fc m2 y1 y5 y6 y7 y10 y11 y12 y13 y14 y15 y16 y17 y18 y19 y20 y21 y22 y23
                         y25 y26 y27 y28 y29 y30 y31)) ->
  evtF asegs RNG Q
    (MS (mkR x1 (Z_to_bv 64 SPA) gp tp x5 x6 x7 (Z_to_bv 64 SP) (Z_to_bv 64 SPA) (Z_to_bv 64 tb) (Z_to_bv 64 len)
             (Z_to_bv 64 b) (Z_to_bv 64 (WK + 736 + b)) x14 x15 (Z_to_bv 64 e) x17 x18 x19 x20 x21 x22 x23
             (Z_to_bv 64 2147450880) (Z_to_bv 64 (4 * off)) x26 x27 x28 x29 x30 x31)
        F (Z_to_bv 64 pc) fc None m1 (seg_rom asegs)).

(* [comment removed for export] *)
Lemma v2_val : forall tb sym1 sym2, 0 <= tb < 256 -> 0 <= sym1 < 256 -> 0 <= sym2 < 256 ->
  Z.lor (sym2 * 256) (tb * 65536 + Z.lor sym1 33554432) = (sym1 + sym2 * 256) + 65536 * (tb + 256 * 2).
Proof.
ltac2:(KReplay.run1 (kr_t_AF_huf_x2t_kit2 ()) ["CANSEC1"] "h07__arithh14__x1h22H1h32H2h42Hth54__ffh68__varmaph75__with84sym1h94sym2h:2tbh;1zp;2p;1p;3p;4p;7p;8p;6g0000j27Tg000Lj10Tg0011j14Tg001Oj25Tg001kj26Tg002Fj23Tg002cj21Tg003@j2;Tg003]j38Tg0047j1>Tg004Wj1=Tg0057j2OTg005Uj1NTg0063j1MTg006^j2<Tg007Aj2LTg007dj49Tg008Oj7ITg0093j1HTg009Uj8BTg00:9j2DTg00:[j2ETg00;5j2ATg00;aj3FTg00<@j4GTg00=2j6@Tg00>8j4JTg00??j6KTg00?]j7?Tf0R0#0#0p=C%00#0#0#0p=2f1R1g00@AR2g00@`R3P3g00A@R4P0g00A`F?p=:g00B@R5g00B^R6f2R7'7g00C<R8#0R9#0#C#2R:#4R;,57'6R<P5f4R=f5R>%2:#2R:#4R?'3R@'1%0:#2#2#4R:'113=;RA/;011>Af6RA%49,3;'1,3?'1585X;5P>P=f3R?g00CaR9#>%=91O51%N5%M5R9P2P3P3P4P9P2P3P3P4P51<56g00DM1L58R8C9,:9P5P8g00E41<5;C9,:9FIR8%H3P8GB1D94P0P7g00E[R9g00F;R4'E1A07=894dAF561CGb5b6b7X15R41760150;'61761151;'6[^15R;P0PAP?O2b0P4P;P0P>P7O2b0P4P;P0P=P1O2b0E@1;=:,1@P>P=P7P1CJEKX3<X2<W4X95X85W:o"). Qed.

Lemma v2_cells : forall tb sym1 sym2, 0 <= tb < 256 -> 0 <= sym1 < 256 -> 0 <= sym2 < 256 ->
  le2 (Z_to_bv 64 (Z.lor (sym2 * 256) (tb * 65536 + Z.lor sym1 33554432)))
    = [Z_to_bv 8 (x2_seq (build_x2 sym2 tb sym1 2)); Z_to_bv 8 (x2_seq (build_x2 sym2 tb sym1 2) / 256)]
  /\ le2 (Z_to_bv 64 (Z.lor (sym2 * 256) (tb * 65536 + Z.lor sym1 33554432) ≫ 16))
    = [Z_to_bv 8 (x2_nbBits (build_x2 sym2 tb sym1 2)); Z_to_bv 8 (x2_len (build_x2 sym2 tb sym1 2))].
Proof.
ltac2:(KReplay.run1 (kr_t_AF_huf_x2t_kit2 ()) ["CANSEC1"] "h04__x1h11zh27__arithh34__ffh48__varmaph55__with64__x2h74__x3h81Hh94__x4h:4__x5h;4__x6h<2H0h=2H3h>2H4h?2H5h@1qhA1rhB2F1hC2F2hD2F3hE2H1hF2H2hG2HthH1ahI4sym1hJ4sym2hK2tbp%0p&0p;1p;2p;7p;3p;4p;8p;6p;5g000Lj1NTg0011j1OTg0047j1sTg004Wj1pTg00F[k10BTg005Uk10=Tg0063k106Tg006^j2RTg00G9j7wTg00:9j2vTg00:[j2uTg00;5k20GTg003]j3[Tg00;ak30ETg00<@k40DTg00G]k20ATg00H7k80>Tg00IEj45Tg00JJj1MTg00KHk209Tg00Kej1@Tg00Lfj1BTg001kR0j2;Tg002Fj23Tg002cj22Tg00Mdj1iTg00NBj1|Tg003@j2UTg00Nej26Tg00OKj28Tg00Ohj2YTg00PHj2\Tg00Q2j24Tg00QRj2tTg00R3k10FTg00RLj2rTg001Oj2XTg00S3j2qTg0000j2aTg00SZj2oTg00T@j2nTg00Tfj1mTg00UDj2lTg00Uej1ETg00VDj2kTg00Vmj2jTg00WVj2WTg0057j2ZTg0093k10;Tg007Aj2STg00XBk608Tg00Xfk107Tg00YKk305Tg00Ynj2hTg00ZKj2gTg00[Gk303Tg00\Qk602Tg00\mk301Tg00]Vk500Tg00^`k404Tg00_;j6~Tg007dj4]Tg00?]j7_Tg00`<j3cTg00`\j1}Tg00??k60:Tg00aLj3{Tg00b5j3`Tg00b^j3zTg00cGj2yTg00d3k40?Tg008Ok70@Tg009Uj8eTg00dQj3xTg00e4k30CTf0R1#N#Np=>g00B^R2f2R3'af1R4/X1';p=?P3g00@AR5g00@`R6P6g00A@R7g00B@R8P4g00eWP1C]g00A`R9F_p=<A[841p=01341,23p=11334/21p=df3R:1634;c1p=If5R;f4R<#}1634=c:13[p=KP8P<P:P3P4P1J0:p==A[812p=f12419[83p=F1k81p=CA{841p=VA`8419`83p=9Az841p=HA`841p=TA`841g00f>'yp=Jg00CaR=?c41p=LP8P3P4P1H0?p=PP3P5P6P6P7P8P4g00E4R>P1C]P9F_p>0<P3P5P6P6P7P8P4g00DMP1C]P9F_p=DP<P5P6P6P7P:P3P5P6P6P7P8P4P>P1C]P9F_K0@p=AP:P5P6P6P7P3P4P1Gep=:Ax841p=GB0C841p=7f6R9P5P6P6P7P;P<P:P5P6P6P7P3P4P1GeGep=Q1a21p=b1X41,;3p=^g00C<R>#NR?#NR@#NRA#NRB#>RC#>RD#ORE9?33RFP:P;P<%O?RGP1P4P3%s=RH%p=R=&0B8RI&0=8RJ&068RKP5P6P6P71R8GRL%O>RM,R85<KA<KLLFw1vK7RNP1P3g00E[ROg00F;RP'u20G13=[OPdB0E824H0DRPb3b4b510GM10GG+0AP1b2L0>P:P;P<PGC5RQ#MPOP8209GMRMP:A1<:En0100000020000'0%@Q/0;%BQ/0G';';P0P<P9P;PGC5RQ#MPOP8PMP<13<ERR,2;n0100000020000'0%@Q/09%BQ/0G';%iARQ#|RS#pRT%iCRU13;ES00f7RV%>D#>#>#>RD#ORW%ND#>#>#>#>#ORX,U93d'URY'6PSPQP;PVP9PGC5RZ#MR[PSPQ18[E%sSR[CIEKPT%OBRB,YY,6UPSPQ%@ZPSPQ%BZP[CIEK';P1P9f8RZPVPGC5#MPOP8PMP9A1V9En0100000020000'0PVf9RYPZPGC5R\#@/0Y%B\/0G';P0PZf:RZPYPGC5R0#@/0Z%B0/0GPT13YEf;R01UZX7dW'UR\,6UPSPQPYP0PZPGC5RY#MR]PSPQ18]EP[CIEKPT1Y\B,6UPSPQ%@YPSPQ%BYP[CIEK';P1PZf<RZP0PGC5#@/0ZP0f=RYPZPGC5#B/0GPOP8PMPZA1YZER\n0100000020000R],u810\]POP8PMPYf>RM?1YEROn0100000020000PMf@R]f?R\PGC5R^#MR_/01X18P9POP1D=PYP\PMPGC5#M/0O13MES01,2\RO13EGR`,2]S0271WRaPT16U1S03PSPQP\fARbP]PGC5Rc#MRdPSPQ18dEP[CIEKPT1Y1B,6UPSPQ%@cPSPQ%BcS04P[CIEK';X18PT16UaRcPSPQP_PSPQ18_EP[CIEKPT1YaBS05,6US06PSPQ%@^S07PSPQ%B^S08P[CIEKPOA1]\ERO12b`R[71WRQ,6U,\U/4W/01X18Pa141WS09/0OX181taWS0:%fWRO$0FS0;18QWS0<,3W14QW5FQ[S0=1rQWS0>1X2WRSA1b]EfBRT/2`Rd71WRe/4WRf??fW[S0?1qeWS0@1XW2S0AA1TbEfCRe/2`Rf71WRg/4WRh,XW1ah2';[S0B1ogWS0CA1eTEfDRg/2`Rh71WRi/8W#f\OS0D1niWS0EA1geEfERi/2`Rj71WRk/4W/0k\OS0F18kWS0GP8A1igEfFRi/2`Rk71W/4WS0HP8%m>,l8Rlg00fjRm#ERn#ERo#ERp#ERq#ERr#ERs#CRt'VS0I%mD,l8RD%CrRr'VS0J1k8mRm39%EsRs#ERu#CS0K%CsRs1j8WRv/Ht%CpRp'T391j8ERw%CnRn'HS0L1Tmt'J'W'W1Hvr=9tm1HvmRx%Eu#C1Vls1VDt%CqRq,HwS0M%CoRo3939'J'W/LH'LP=1Z89?P<I1Z8;7P31Z8:RD7P4S0NPJPKPK1R82Ru1R8WRy60<KS0O&0;6RzPK1S8>R{9DKuS0PPKP{PyDAC:S0QPzPKPKPKP5P6P6P7A<KyuJ08S0RPz1S8?R?&07>R>,S8R71R8ER6'G'7R51S8@R@1G6LR|'7,Gy'71S8ARA,Gy/7{S0S5<KC:PzPK%N>,S8R>=<K@PzPKPKADKu7PKP7P6DAS0TPzPKPKADKu?PKP?P6DAS0UPzA<K{5C:FQFQPNPPb3b4b5X08X68X78X98X:8X;8%b4R5?^4W\SS0Vg00gI\OR}12:R12;`S0W71WRR13WV;F3[109;A?;;ER~13VE9F;9\~[[[[^08^68^78^98^:8^;8P1P3PifHR~fGR;PGC5#@S0XP~PiP;P4P9PVP0PePgO;b2bAb@b?b>b=b<b81\Uc1Hwr1Hvn=9pm'J1HwtRw1Hvo=9qm'J/LH'LP=1Z83?P4DPJPKQ0UPzPKPKQ0PPKP{P6DARvPzPKQ0TPzPK1G?6,7{177|,Gy'7S0P9DKuPKQ0PB058LUS0PDAC:FQPNPPb3b4b5X08X68X78A^54ER5A?<<E%OC,hGRC9?RR[\5[^08^68^78P1PbP\P]PZPYPMO6b2,gaD=P_P1D=:03c^Q06P^P]1YQB,6U,\U/4WRQQ04,3E7F1X18PG13E19FQbX181hGB,8aQ03,\U/4WRQ/0[X18Q0:Q0=Q0>Q0?Q0@Q0BQ0CQ0DQ0EQ0FQ0GP8Q0HP8Q0M1Tox59t,JsQ0KQ0IQ0J/Tn39Q0L99wq,Jm'W/LH'LP=Q0NPJPKPKQ0OPzPKADKuAPKPAPyDAC:PzPKPKQ0RPz1G@6,7717{|R7,Gy'71Gy?/7A5<KC:PzPKA<K>{PzPKPKADKu@PKP@P6DAPzPKQ0TPzA<K7?C:FQFQPNPPb3b4b5X08X68X78X98X:8X;8%b9R@?^9W\SQ00,2<123`71W13W:;FV\}1093A^@9ER@Q0W/09\@[[[[^08^68^78^98^:8^;8P1P4Q0XPiP;P3P~P9PVP0PePgO;b2bAb@b?b>b=b<b8Q0218aW'0P8P[10QdX18P[Q09/0dX181t[WQ0;18dW,3W14dW5Fd[1rdW14fWRd??dW\S1qfWQ0A14hWRf,XW1af2';[1ohW18jW#f\O1njW14kW/0k\O18kWP812;`/4WP81Vlp/TmA9rqp,Jx'W1Tpm1Vlq=9to,Jx'W/LH'LP=APD:I?P3I?P4IPJPKQ0QPzPKPKQ0RPz17?|R|Q0S5<KC:PzPKQ0UPzA<K{|C:FQPNPPb3b4b5X08X68X78Q0V12:`13W<;F3\}A?::EAF:<`[[[^08^68^78P1P3fIP4P9PVPiO6b2bAb@b?b>b=b<b816U[,\UPHP=1Z84RUPJPKPvPzPKADKu7PKP7Q0PDAC:PNPPb3b4b5X08A?11ER7124`R`??`C[^08P1PTP\O2b2,g[D=Q0<P1J02b8Q05PHP=PIPJ1R8B9DKuPNPPb3b4b5%bBP1b2:01aBD=Q08P3D=Q07P:D=P]P7X18RaPHP=PUPJPKPvPzPvC:PNPPb3b4b5X08P5\7^08P1PbPMO2b2Q07P:D=PGPaPHP=PIPJPKADKuLPKPLP6DAPNPPb3b4b5A?GGEP1b2Q08P3D=I00H04Q011U\X9d]W'UP]P\PMPYPZP0E~D=bBb8WDWCP4P1O2n2001000010121000000W8WBP4P1O2n2001000010121000000bHXFFXEFWGXJ8XI8XK8o"). Qed.

End CANSEC1.
