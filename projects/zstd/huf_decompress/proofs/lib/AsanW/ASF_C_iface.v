(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From Stdlib Require Import Sorting.Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame Arr Tac ITree Nodes Decode.
From OSSVerify.Proofs.zstd.huf_decompress.lib.LibA Require Import ExecF ITreeA StepF.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Spec Require Import STree AsanCtrl AsanEmbed.
From OSSVerify.Proofs.zstd.huf_decompress.lib.AsanW Require Import AImg AProto ABase ABytes AQConst AKitQ AMalloc_iface ADepot_iface ARep ARepQ ARepQP ALayout AHeapP
     ASec AFreeModel AFreeRep AFreeRead F_afree_tail F_afree_icpt F_afreeC_iface F_afree_arep ASecRecycle_iface
     ASF_kit ASF_fast ASF_refill AFreeC_kit_iface.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Common Require Import RunDraw.
From OSSVerify.Proofs.zstd.huf_decompress.lib Require KReplay.
Ltac2 kr_t_ASF_C_iface () := "C35stdpp4base6LookupC59OSSVerify5KrLib4Spec8AsanCtrl4aptrC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List2hdC35stdpp8fin_maps:map_deleteC35stdpp4gmap;gmap_lookupC35stdpp4gmapBgmap_partial_alterC35stdpp4base6DeleteC59OSSVerify5KrLib5AsanW7ALayout4aobjC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1Z02C56Stdlib6ZArith6BinInt1Z2leC59OSSVerify5KrLib6Common7RunDraw:atop_rangeC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive01C59OSSVerify5KrLib3Lib8RunConst4ATOPC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z6moduloC56Stdlib6ZArith6BinInt1Z3addC56Stdlib6ZArith6BinInt1Z3mulI47Corelib4Init5Logic3and00C46Stdlib9micromega9SatDivModCZ_mod_nonneg_nonnegC56Stdlib6ZArith6BinInt1Z7div_modC47Corelib4Init5Logic3notC56Stdlib6ZArith6BinInt1Z3divI47Corelib4Init5Logic2eq00C56Stdlib6ZArith6BinInt1Z=mod_pos_boundC56Stdlib6ZArith6BinInt1Z2ltC56Stdlib6ZArith6BinInt1Z=mod_neg_boundC56Stdlib5omega8PreOmega1Z;div_0_r_extC56Stdlib5omega8PreOmega1Z;mod_0_r_extC59OSSVerify5KrLib3Lib9LiaTuning9zify_doneC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z7compareK47Corelib4Init5Logic2eq01K47Corelib4Init9Datatypes3nat02K46Stdlib9micromega=RingMicromega5Psatz02K46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega:ZMicromega;ZArithProof02K47Corelib4Init9Datatypes4list01K47Corelib4Init9Datatypes4list02I47Corelib4Init9Datatypes4list00K46Stdlib9micromega6VarMap1t01K46Stdlib9micromega6VarMap1t02K46Stdlib9micromega6VarMap1t03I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr02K47Corelib4Init9Datatypes6option02K46Stdlib9micromega7EnvRing5PExpr03K46Stdlib9micromega5Tauto8GFormula06C46Stdlib9micromega5Tauto8BFormulaC46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundK46Stdlib9micromega7EnvRing5PExpr01K46Stdlib9micromega7EnvRing5PExpr05K47Corelib4Init5Logic2ex01K46Stdlib9micromega5Tauto8GFormula03K47Corelib4Init5Logic3and01I47Corelib4Init5Logic2or00I47Corelib4Init5Logic2ex00K46Stdlib9micromega=RingMicromega7Formula01K46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega5Tauto8GFormula05K46Stdlib9micromega5Tauto8GFormula08I47Corelib7Numbers7BinNums1Z00K47Corelib7Numbers7BinNums1Z01C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K46Stdlib9micromega=RingMicromega3Op203K47Corelib4Init9Datatypes4unit01K47Corelib7Numbers7BinNums8positive03K47Corelib4Init5Logic4True01I47Corelib4Init9Datatypes:comparison00I46Stdlib9micromega:ZMicromega;ZArithProof00K47Corelib4Init9Datatypes3nat01K46Stdlib9micromega:ZMicromega;ZArithProof01I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01".
Import ListNotations.
Set Keyed Unification.   (* [comment removed for export] *)
Open Scope Z_scope.

Section CANSEC1. Context {rc : runConstT}.
(* [comment removed for export] *)
Local Lemma aobj_int : forall a n, aobj a n -> 0x10000 <= n ->
  6344704 <= a /\ a + n <= ATOP /\ exists k, 0 <= k <= 1 /\ a + n <= 2147446784 + k * 18446744073709551616 /\ 17594333495296 * k <= a.
Proof.
ltac2:(KReplay.run1 (kr_t_ASF_C_iface ()) ["CANSEC1"] "h04__x1h14__x2h21Hh31kh47__arithh54__ffh68__varmaph75__with84__x3h92H6h:4__p1h;2H0h<2H1h=3H10h>2H2h?2H3h@2H4hA2H5hB2H7hC2H8hD2H9hE2HnhF6__sat6hG1ahH1np;3p;1p;2p;4p;7p;6p;8p-1p10000R0p4p7210p8p1000Dp4p70R1p1001;p4p710p8P1p1001Rp4p710p8P1p1001np4p710p8P1p1002Gp4p710p8P1P0p4p710p8P1p1002gp4p710p8g003;j3zTg0042j11Tg004Wj1<Tg0055j20Tg005Qj1pTg006Oj17Tg0074j1aTg007jj2@Tg008Jj22Tg008gj2ATg009DR1j28Tg009_j2fTg00:Pj2eTg00;1j1dTg00;Jj2TTg00;gj3MTg00<Aj2cTg00<hj2ETg00=Dj2bTg00=kj2`Tg00>Qj2_Tg00?7j2^Tg00@3j2]Tg00@Tj2STg00@nj1KTg00AMj2JTg00B6j3QTg00B_j2\Tg00CKj1yTg00Ckj3[Tg00DKj1xTg00Dkj1wTg00EIj2ZTg00Egj4DTg00FEj1tTg00Fcj1sTg00GNj2LTg00H1j1rTg00HSj3OTg00I6j7qTg00IZj2oTg00J<j2nTg00Jhj3mTg00KGj4lTg00L9j2WTg00L\j3NTg00M?j4XTg00MYj6jTg00N=j4VTg00NXR0j2YTg00O2j2iTg00OLj4hTg00P7j7uTg00P[j7gTg00Q?j8vTf0R2#1#1p=I%12#1#1#1#1#1#1#1p=5%72#7#7#7p=9%72#7p=U%12#1#1#1p=Cf2R3f1R4/02'8p=Fg00QcR5g00RAR67M2p=Pf3R7/031042'Yp=41842,83p=R1034/82,87p=;1062p=?1234/02p=H1042,83,87p=G1i52p=B1034/82p=61W52p=>P3g00R_R8g00S>R9P9g00S^R:P5P4g00T>P2Chg00TeFup=3P3P8P9P9P:P4P2Fgp==P7P8P9P9P:P3P4P2Gvp=:1Y42,83p=kp,2rcR;?z42g00UER<#1R=#1R>#I#5R?#1R@#1#IRA#<RB/04RC%p;%7<RD#7#9#9#9RE#1#7#URF#7#9#1#I#C#5#5#<%a;R;'0RG%7E#9#9#1#I#C#5#5#<RE7F;P1f4RH%<?R?'@#P10?HRI12H7RJP;PJ%CF#5#<RF%9@#9#9#9#1#I#C#5#<R@PHC4PJPB%7<#1#C#U#1#7#C#5#<RJPHC47RIC;f5RI12IH%?2%<<RK7F2RLf6RM%5A#5#5#5#5#5#<RA,A2,2FRN7HI1A@2ROPMCGX35#B76;56JP31@M?#Pf7RP,0?RQ12PMRRP;PRPFP@PPC4PRPBPJPPC47RQC;P1f8RQ,0?RR12QPRPPPPFP@PQC4PPPBPJPQC47RR76;f9RR12RQPLf:RP?HRNPOPPCGX35#B76;56JP210?Pf;RS/2PRPPPPFP@PSC4P?PSPPPBPJPSC4C;76;P1f<RP/2SRS/0;PSPFP@PPC4P?PPPSPBPJPPC4C;f=RS12SPPLf>RT/2SRSPN10OTC;X35#B76;56JP210S;f?RS/2TRTPFP@PSC4P?PSPTPBPJPSC4C;P1f@R1/2SRSPFP@P1C4PSPBPJP1C496?1fARS12S1PLfBR1/2SRSPN10O1C;X35#B76;56JP2PSPFP@P1C4fCRS12S1PBPJPSC456?fDRT,0J12TSRU/0;RVPLfERW/2TRXPN10OWC;X35#BRY'81fT?%?T%??fFRZ/@?R[#?[[1eW?%P?R\#d1TZ?,A?/2[9M5Z[1cZ?1E6?R[fGR]/@?R^#?1E^?'8[1b]?1E?6fHR^/@?R_,E??F_6[1`^?fIR^/T?#P\\1_^?fJR^/@?=M5^\\g00Uj1^^?R\eP\PHg00VF1]6?'SP[eO1fKR[/@?R\#?1E\?'8g00VlR\g00WXR_#KR`#KRa#KRb#K,J51J5`R`1J5a5Q55Q5g00X7Ra'\%y\Rc3[%x\RdP5%w5ReP41Z53RfCD%t5Rg%s5Rh%>BRi1L5DRD53h%r9RjPh%>?1L5<R<53hRkPhP8P9P9P:AO5<D=3hi%>J=3h<RiFq5=hPjPhPkPjPiC:C:C:1oh:RiP2P3g00XcRlg00YCRm'S1n23=MlmdAm564ClRmb5b6b7X05X1510?4Rl1243Rn/0B10J43k10?310J7[[\C^05^15P2fLfMP^PRP1O5b4b910J[eb=bDbCbBb9b2bFPVPYPcPdP5PfP41Z57RYCDPgPh1L5=9O5<R==3hDRDPjPDC:PiPmb5b6b7X05X15X851224RD/0310n7[^05^15^85P2P;PTPWPMO4b4P010UF10@TPLAHZWNPOPZCGX35#BP410XFP5PLAH]ZNPOP]CGX35ROP6PcPdP5PfP4PeCDPgPh%>FRf93h=PjPhPkPj1W56Rk=3hk%>KRN93hkRL5=h%>ARX9N5k9O5f93h=%>@RT=N5k=3h<5=h5=hC:C:PiPmb5b6b7X05X1510DF%?KRD96661237Rk1A6A,2F1A@6/03C;\l[^05^15P2PZP]P4PPO4b4CXW2P2O110@WP5POPKp-0RO1J5b1J5_9Q5`5Q5/\a=[\cPdP5P5PYP3PeCDP4PeCDPgPhPhP8P9P9P:PIEj1L5>R>%>E53h5=hPjPhA3hT<PjPhA3h=>PjA3hNN9=hLAN5NX9O5f93h=AN5TN=3h<5=h5=hC:C:C:PiPmb5b6b7X05X15X85W:AF73E10@410kHAFDKK1AKA,2F9H7H1A@KP7CG[[[^05^15^85^:OP2PGP;PZP]PSP4PQO7b4CXW2P2O1n200100001021100011000CVCVWAW@P4P2O2n2001000010121000000W2W?P4P2O2n2001000010121000000W2W>P4P2O2n2011000010121000000W2W<P4P2O2n2011000010121000000b;WEW2XH5XG5o"). Qed.
Local Lemma aobj4_int : forall a, aobj a 4096 ->
  4096 <= a /\ a + 4096 <= ATOP
  /\ (exists k, 0 <= k <= 1 /\ a + 4096 <= 2147446784 + k * 18446744073709551616 /\ 17594333495296 * k <= a)
  /\ (exists j, 0 <= j <= 1 /\ a + 4096 <= 65536 + j * 18446744073709551616 /\ 6344704 * j <= a).
Proof.
ltac2:(KReplay.run1 (kr_t_ASF_C_iface ()) ["CANSEC1"] "h04__x1h11jh21Hh31kh47__arithh54__ffh68__varmaph75__with84__x2h94__p1h:2H5h;2H0h<2H1h=2H2h>2H3h?2H4h@2_HhA1ap;1p;3p;2p;4p;6p;7p;8g0042j12Tg004Wj1>Tg003;j3mTg005Qj1lTg006Oj19Tg0074j1]Tg0055j20Tg007jj2UTg00;gj3ITg008Jj21Tg008gj2?Tg009DR0j26Tg00CKj1aTg00DKj1`Tg00EIj2OTg00FEj1_Tg00Fcj1^Tg00GNj2KTg00H1j1\Tg00IZj2[Tg00@Tj2ZTg00J<j2YTg00Jhj3XTg00KGj4WTg00Dkj1VTg00Egj4TTg00HSj3CTg00L9j2STg00M?j4GTg00@nj1NTg00AMj2JTg00B6j3RTg00B_j2kTg00Ckj3jTg00MYj6iTg00N=j4MTg00NXR1j2gTg00O2j2fTg00OLj4eTg00P7j7dTg00Q?j8cTg00P[j7hTg00L\j3bTf0R2#2#2p=F%22#2#2#2#2#2#2#2p=8%92#9#9#9p==%92#9p=P%22#2#2#2p=Af2R3f1R4/02'6p=Hf3R5/031042'gp=41642,63p=L1034/62,65p=D1034/62p=7f4R610531042'6'6p=5g00QcR7/f2p=:1S72p=@P3g00R_R8g00S>R9P9g00S^R:P7P4g00T>P2Ceg00TeFdp=3P5P8P9P9P:P3P4P2Gcp=;1134/02p=EP3P8P9P9P:P4P2Fhp=<Ab742p=B1042,63,65p=Qp,2rcR;g00UER<#2R=#2#F#8R>#>R?7m2%l;%9<R@#9#=#=#=RA#2#9#PRB#9#=#2#F#A#8#8#>%];R;'0RC%9A#=#=#2#F#A#8#8#>RA7H;P01U3?g00RARD5I710?3RE113?RFP;PF%AB#8#>RB%2>R>#=#=#=#=#2#F#A#8#>RGP3C4PF%2>#FR>#>RH%9<#2#A#P#2#9#A#8#>RIP3C47LECD115?RE%><RJ,0297D2RK116?RL%8>#8#8#8#8#8#>R>,?2RM,1BRN1?G2ROP6D5X37#:PKPL11HMRM1?I2RLP6D5X17#:'677;97?5P41U6?=I7Df5RP,0?RQ11P?RRP;PRPBPGPPC4PRPHPIPPC47LQCDP0f6RQ,0?RP11Q?RRPRPBPGPQC4PRPHPIPQC47LP77;f7RP11P?PKf8RP/1?RRPNPOPPD5X37#:PKPRPMPLPPD5X17#:'677;57?P210?Pf9RR/1?RSPSPBPGPRC4P?PRPSPHPIPRC4CD77;P0f:RR/1?RS/0;PSPBPGPRC4P?PRPSPHPIPRC4CDf;RS11S?PKf<RS/1?RTPNPOPSD5X37#:PKPTPMPLPSD5X17#:'677;57?P210T;f=RT/1?RUPBPGPTC4P?PTPUPHPIPTC4CDP0f>RT/1?RUPBPGPTC4PUPHPIPTC497?Tf?RT11T?PKf@RT/1?RUPNPOPTD5X37#:PKPUPMPLPTD5X17#:'677;57?P2PUPBPGPTC4fARU11U?PHPIPUC457?fBRU,0?RV11U?RW/0;RXPKfCRY/1?RZPNPOPYD5X37#:R[PKPZPMPLPYD5X17#:R\'6R]'6g00VlR^#aR_%`^R`1O74Ra%_7Rb%^7Rc%@?Rd1K7<R<53cRe%\9RfPeC;1[c:RgP2P3g00XcRhg00YCRi'Z1Y23=IhidAX7D4CWRib5b6b7X0710?210?4Rh[^07P2PYPRO2b4PXP]P_P`P71O73R]P4%V7RXCTPbPcAC7<dRd1K7=53cR=PfP=C;PgPib5b6b7X07X87112?R=/04AE4?3[^07^87P2P;PYPQO3b4P[P\P110WB10GUPKfDR\/1?R[PNPOP\D5X37#:P410ZBP7PKfERZ/1?RQPNPOPZD5X37ROPDP_P`PaPbPc%@BRN93cdPfPcPePf1S7DRR=3cR%@JRj93cRRk5<cRl%@>Rm,BRRn9C7N93cd%@GRo/BR=3c<5<c5<cC;C;PgPib5b6b7X0710=B10DJRp97DDRqPF1?D>Rr,1B1?GDP3D5\h[^07P2PZP4PSO3b4CGW2P2O110GYP7POPJp-0ROg00WXRs#NRt#N#N,J71J7t1J7s5R75R7g00X7'k=j^_R^P`P7PXP4P]CTR]PbPcPcP8P9P9P:P6Ei1K7@R@%@A53c5<cR6PfPcA3co<PfPcA3cd@R@PfA3cjj9<ckRk1BjmRm9C7N93cd1Boj=3c<5<c5<cC;C;C;PgPib5b6b7X07X87W9AH34ARA10G410F5RoAHpJJRpPE1?J>R>,1B1?GJP5D5[[[^07^87^9OP2PCP;PZPYP4PPO6b4CGW2P2O1n200100001021100011000P0PVPWPHPIPUC4PKP[PMPLP\D5X17#:P210?\PQPHPIPZC4P1fFR1?E?H10I1PKfHR1?E?MPLP1CQX17#:P2fGR1?E?HP7PKfIRK?E?MPLPKCQX17RLPDP_P`PaPbPc%@HRa93cdPfPcPePfAC7an93cd%@IRn/BR=3c<5<c9<clC;C;PgPib5b6b7X0710=HPqPF11Hr1?IDP3D5\h[^07P2PKP4PTO3b4CGW:P2O110I1P7PLPJP^P`P]PbPcP6PfPcA3cn<PfPcP@PfAC7am93cd1Bnj=3c<5<c9<ckC;C;C;PgPib5b6b7X07X87X9O10I4PpPE11H>1?IJP5D5\o[\A^07^87^9OP2PCP;PKP1P4PSO6b4CGW:P2O1n200100000021100011000W2W@P4P2O2n2001000000121000000CMCMCMW:W?P4P2O2n2001000010121000000W2W>P4P2O2n2011000010121000000W2W=P4P2O2n2011000010121000000W2W<P4P2O2n2011000010121000000b;W2XA7o"). Qed.

Section S.
Variable DI : ADepotIface.
Variable AFK : alayout -> list ablock -> amem -> Prop.
Variable CI : list (Z * Z).

(* [comment removed for export] *)
Definition store_freeSC_stmt : Prop :=
  forall (L : alayout) (RNG : footprint) (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
         (m : amem) (st : astate) (LB : list ablock) (X : aconc) (Q : qconc) (p : aptr) (mb ms n b1 ctx A lo k24 : Z)
         (stj : word) (chunks : list word),
  let ch := CSec mb ms n in
  let hm := mb + 6128 in
  let st1 := set_live (delete p (a_live st)) st in
  let st2 := st_enq st1 ch in
  let ek := ek_of L st X Q n k24 stj chunks in
  let g := g_of L st Q (ek_delta ek n) in
  alayout_ok L -> arng L RNG st -> AREP (AHQ DI ASEC_of AFK) L st X m -> AQUAR_at L st X Q m -> ablocks L st X LB -> AFK L LB m ->
  (a_live st) !! p = Some ch -> In (HB p A n) LB -> n <= Q_MAX ->
  rw_cells asegs m hm [C1 (Z_to_bv 8 2); C1 (Z_to_bv 8 b1); C2 (Z_to_bv 64 0); C4 (Z_to_bv 64 n); C8 (Z_to_bv 64 ctx)] ->
  0 <= b1 < 256 -> Z.land b1 3 = 1 -> 0 <= ctx < 2^31 ->
  (enq_is_app st = false ->
        nth_error (xc_cache (x_cls X K_BATCH_CLASS)) (Z.to_nat (c_count (get_cls st K_BATCH_CLASS) - 1)) = Some k24
     /\ busy_of X K_BATCH_CLASS k24 = None /\ 0 <= k24 < ndist st K_BATCH_CLASS
     /\ ~ In k24 (map qb_slot (q_loc Q ++ q_glob Q))
     /\ junk_at m (abatch_addr L k24) 8192 /\ fill_at m (shad (abatch_addr L k24)) (shlen 8192) 0xfa
     /\ a_cinit st = true /\ 0 < c_count (get_cls st K_BATCH_CLASS)) ->
  Q_CACHE < a_qloc_bytes st2 -> Q_MAX < a_qglob_bytes st2 + a_qloc_bytes st2 ->
  ek_pre ek RNG (al_t L) (Z.of_nat (length (a_qloc st))) (qlast L (q_loc Q)) n hm m ->
  dk_preC ek g RNG (al_t L) (qlast L (q_loc Q)) hm (a_qloc_bytes st + ek_delta ek n) m ->
  ATOP <= lo -> lo <= bv_unsigned sp - AFREE_STACK -> tp = Z_to_bv 64 ATP ->
  forall ms1,
    free_torec_post DI L ek g ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (al_t L) hm n
                    (Z.of_nat (length (a_qloc st))) (qfirst L (q_loc Q)) (qlast L (q_loc Q)) (a_qloc_bytes st) b1 ctx lo m ms1 ->
    storeC_post DI AFK CI L RNG ek g ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (st_after st2) (lb_remove p LB) (al_t L) lo m ms1.

(* [comment removed for export] *)
Definition store_freeSRC_stmt : Prop :=
  forall (L : alayout) (RNG : footprint) (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
         (m : amem) (s : astate) (LB : list ablock) (X : aconc) (Q : qconc) (cs : list achunk) (mb ms n b1 ctx lo k24 : Z)
         (stj : word) (chunks : list word),
  let ch := CSec mb ms n in
  let hm := mb + 6128 in
  let sq := st_enq s ch in
  let ek := ek_of L s X Q n k24 stj chunks in
  let g := g_of L s Q (ek_delta ek n) in
  alayout_ok L -> arng L RNG s -> AREP (AHSm DI AFK cs Q) L s X m -> ablocks L s X LB -> AFK L LB m ->
  Permutation cs (ch :: sec_chunks_of s) -> RSEC cs RNG -> ~ sec_live s ch -> n <= Q_MAX ->
  0 <= b1 < 256 -> Z.land b1 3 = 1 -> 0 <= ctx < 2^31 ->
  enq_is_app s = false ->
  nth_error (xc_cache (x_cls X K_BATCH_CLASS)) (Z.to_nat (c_count (get_cls s K_BATCH_CLASS) - 1)) = Some k24 ->
  busy_of X K_BATCH_CLASS k24 = None -> 0 <= k24 < ndist s K_BATCH_CLASS ->
  ~ In k24 (map qb_slot (q_loc Q ++ q_glob Q)) ->
  junk_at m (abatch_addr L k24) 8192 -> fill_at m (shad (abatch_addr L k24)) (shlen 8192) 0xfa ->
  a_cinit s = true -> 0 < c_count (get_cls s K_BATCH_CLASS) ->
  Q_CACHE < a_qloc_bytes sq -> Q_MAX < a_qglob_bytes sq + a_qloc_bytes sq ->
  ek_pre ek RNG (al_t L) (Z.of_nat (length (a_qloc s))) (qlast L (q_loc Q)) n hm m ->
  dk_preC ek g RNG (al_t L) (qlast L (q_loc Q)) hm (a_qloc_bytes s + ek_delta ek n) m ->
  ATOP <= lo -> lo <= bv_unsigned sp - AFREE_STACK -> tp = Z_to_bv 64 ATP ->
  forall ms1,
    free_torec_post DI L ek g ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (al_t L) hm n
                    (Z.of_nat (length (a_qloc s))) (qfirst L (q_loc Q)) (qlast L (q_loc Q)) (a_qloc_bytes s) b1 ctx lo m ms1 ->
    storeC_post DI AFK CI L RNG ek g ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (st_after sq) LB (al_t L) lo m ms1.
End S.
End CANSEC1.
