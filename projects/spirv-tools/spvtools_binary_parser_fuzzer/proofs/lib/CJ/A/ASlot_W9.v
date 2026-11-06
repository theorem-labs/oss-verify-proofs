(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.CJ.Lib Require Import Tac Image ZBridge SysStep SFModel ITree Nodes Decode Arr.
From OSSVerify.spirv_tools.spvtools_binary_parser_fuzzer.images Require Import Plain.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.CJ.A Require Import F_syscalls MallocRep F_malloc_free F_malloc_fast F_malloc_enframe MallocTree MallocKit_A.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.CJ.A Require Import MallocKit_AB.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.CJ.Spec Require Import STree Malloc MallocCtrl Monad Prog.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.CJ.A Require Import Malloc_fp MallocKit_A2.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.CJ.A Require Import MallocNat MallocFacts_AS MallocKit_A3 ASlot_W0 ASlot_W1 ASlot_W2 ASlot_W3 ASlot_W4 ASlot_W5 ASlot_W6 ASlot_W7 ASlot_W8.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import AllocCeil RunRandom.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require KReplay.
Ltac2 kr_t_ASlot_W9 () := "C69OSSVerify5KrLib2CJ4Spec6Malloc4aptrC1?~~~~~~~~~~~~~~~I35stdpp9countable9Countable00C47Corelib4Init5Logic8eq_ind_rC35stdpp4base;RelDecisionC35stdpp4gmap;gmap_lookupC35stdpp4base4fmapC35stdpp4base6lookupC69OSSVerify5KrLib2CJ4Spec6Malloc4optrC1?~~~~~~~~~~~~~~~I69OSSVerify5KrLib2CJ1A8ASlot_W06ta_rel00C1?~~~~~~~~~~~~~~~i69OSSVerify5KrLib2CJ1A8ASlot_W93gmf00C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2CJ1A8ASlot_W07tr_geomC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2CJ4Spec6Malloc<get_meta_recC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2CJ4Spec6Malloc:m_last_idxC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2CJ4Spec6Malloc:m_freeableC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2CJ1A9MallocRep9meta_slotC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2CJ4Spec6Malloc7m_availC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1Z02C56Stdlib6ZArith6BinInt1Z3powC69OSSVerify5KrLib2CJ4Spec6Malloc7m_freedC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z2ltC69OSSVerify5KrLib2CJ1A>MallocFacts_AS5mw_okC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2CJ4Spec6Malloc4concC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2CJ4Spec6Malloc;m_sizeclassC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2CJ1A8ASlot_W99gmf_availC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2CJ1A8ASlot_W99gmf_freedC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2CJ1A8ASlot_W09tr_mrangeC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2CJ1A8ASlot_W96gmf_mwC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive01C56Stdlib6ZArith6BinInt1Z2leC69OSSVerify5KrLib2CJ4Spec6Malloc8m_maplenC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic3and00C69OSSVerify5KrLib2CJ1A8ASlot_W08tr_areasC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2CJ1A8ASlot_W98gmf_slotC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2CJ1A<MallocKit_ABDmeta_slot_same_areasC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z:pow_nonnegK47Corelib4Init9Datatypes4list01I47Corelib4Init9Datatypes4list00K46Stdlib9micromega6VarMap1t02I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr02K46Stdlib9micromega=RingMicromega7Formula01K46Stdlib9micromega5Tauto8GFormula04C46Stdlib9micromega5Tauto8BFormulaK47Corelib4Init5Logic2eq01C46Stdlib9micromega:ZMicromega=ZTautoCheckerI47Corelib4Init5Logic2eq00C46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundI35stdpp4gmap4gmap00C69OSSVerify5KrLib2CJ4Spec6Malloc9s_regionsC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes3fstC69OSSVerify5KrLib2CJ4Spec6Malloc6r_baseC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes3sndC56Stdlib6ZArith6BinInt1Z3addC69OSSVerify5KrLib2CJ1A8ASlot_W0:tr_regionsC1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic3and01C69OSSVerify5KrLib2CJ4Spec6Malloc5m_memC1?~~~~~~~~~~~~~~~I47Corelib7Numbers7BinNums1Z00K47Corelib7Numbers7BinNums1Z01I47Corelib7Numbers7BinNums1N00I69OSSVerify5KrLib2CJ4Spec6Malloc6region00C1?~~~~~~~~~~~~~~~I69OSSVerify5KrLib2CJ4Spec6Malloc6mstate00C1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive03I47Corelib4Init5Logic4True00I46Stdlib9micromega:ZMicromega;ZArithProof00C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K46Stdlib9micromega=RingMicromega3Op201K47Corelib4Init9Datatypes4unit01I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01C45stdpp7numbers1N6eq_decC35stdpp9countable;N_countableI47Corelib4Init9Datatypes6option00I47Corelib4Init9Datatypes4prod00C46Stdlib5Lists4List2InC49OSSVerify5KrLib9AllocCeil=alloc_ceilingC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2CJ3Lib5Frame=disjoint_fromC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes4list02I47Corelib4Init5Logic2or00K47Corelib4Init5Logic2or01K47Corelib4Init9Datatypes3nat02K46Stdlib9micromega=RingMicromega5Psatz02K46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega:ZMicromega;ZArithProof02K46Stdlib9micromega6VarMap1t01K46Stdlib9micromega6VarMap1t03K47Corelib4Init9Datatypes6option02K46Stdlib9micromega5Tauto8GFormula03K46Stdlib9micromega5Tauto8GFormula06K47Corelib4Init5Logic2or02C47Corelib4Init9Datatypes8list_indK47Corelib4Init9Datatypes4prod01K46Stdlib9micromega5Tauto8GFormula08K46Stdlib9micromega=RingMicromega3Op203K47Corelib4Init5Logic4True01K47Corelib4Init9Datatypes3nat01K46Stdlib9micromega:ZMicromega;ZArithProof01C69OSSVerify5KrLib2CJ4Spec6Malloc?sc_in_seq_rangeC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3subC69OSSVerify5KrLib2CJ4Spec6Malloc7bouncesC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3eqbC47Corelib4Init9Datatypes4negbC47Corelib4Init9Datatypes4andbC69OSSVerify5KrLib2CJ4Spec6Malloc:set_bounceC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic2ex00K47Corelib4Init5Logic2ex01C69OSSVerify5KrLib2CJ4Spec6Malloc=decay_bouncesC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2CJ1A8ASlot_W9;decay_casesC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2CJ4Spec6Malloc6activeC1?~~~~~~~~~~~~~~~I69OSSVerify5KrLib2CJ4Spec6Malloc4meta00C1?~~~~~~~~~~~~~~~".
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Section AC_1. Context {ACEIL : AllocCeiling} {RRND : RunRandom}.

Definition ta_fp (st : mstate) (lo sp : Z) (a : Z) : Prop :=
  lo <= a < sp
  \/ CTX <= a < CTX + 928
  \/ (exists q, meta_slot st q /\ conc st q <= a < conc st q + 40)
  \/ (exists b gh, (s_groups st) !! b = Some gh /\ conc st b <= a < conc st b + 9).

Record gmf (st : mstate) (sc : Z) (g : aptr) : Prop := mkGMF {
  gmf_slot : meta_slot st g;
  gmf_avail : 0 <= m_avail (get_meta_rec st g) < 2^32;
  gmf_freed : 0 <= m_freed (get_meta_rec st g) < 2^32;
  gmf_mw : mw_ok (get_meta_rec st g);
  gmf_sc48 : m_sizeclass (get_meta_rec st g) < 48;
  gmf_cls : m_sizeclass (get_meta_rec st g) = sc;
  gmf_grp : exists b gh, m_mem (get_meta_rec st g) = Some b /\ (s_groups st) !! b = Some gh /\ g_meta gh = Some g
             /\ 0 <= g_active_idx gh <= m_last_idx (get_meta_rec st g)
             /\ (m_sizeclass (get_meta_rec st g) = 0 -> g_active_idx gh = m_last_idx (get_meta_rec st g))
             /\ (forall o, 0 <= o < 9 -> exists h, cell_read (get_shadow st (fst b)) (snd b + o) = Unknown h);
  gmf_fbits : forall i, 0 <= i -> Z.testbit (m_freed (get_meta_rec st g)) i = true -> i <= m_last_idx (get_meta_rec st g);
  gmf_abits : forall i, 0 <= i -> Z.testbit (m_avail (get_meta_rec st g)) i = true -> i <= m_last_idx (get_meta_rec st g);
  gmf_links : exists n p, m_next (get_meta_rec st g) = Some n /\ m_prev (get_meta_rec st g) = Some p
}.

Record taf (st : mstate) (sc : Z) : Prop := mkTAF {
  taf_head : forall g, active st sc = Some g -> gmf st sc g /\ m_sizeclass (get_meta_rec st g) = sc;
  taf_next : forall g n, gmf st sc g -> m_next (get_meta_rec st g) = Some n ->
               gmf st sc n /\ m_sizeclass (get_meta_rec st n) = m_sizeclass (get_meta_rec st g) /\ m_prev (get_meta_rec st n) = Some g;
  taf_prev : forall g p, gmf st sc g -> m_prev (get_meta_rec st g) = Some p ->
               gmf st sc p /\ m_next (get_meta_rec st p) = Some g;
  taf_bnc : forall i, 0 <= bounces st i < 256
}.

Lemma gmf_geom st st1 sc g : ta_rel sc st st1 -> gmf st sc g ->
  meta_slot st1 g /\ 0 <= m_avail (get_meta_rec st1 g) < 2^32 /\ 0 <= m_freed (get_meta_rec st1 g) < 2^32
  /\ mw_ok (get_meta_rec st1 g)
  /\ m_mem (get_meta_rec st1 g) = m_mem (get_meta_rec st g)
  /\ m_last_idx (get_meta_rec st1 g) = m_last_idx (get_meta_rec st g)
  /\ m_sizeclass (get_meta_rec st1 g) = m_sizeclass (get_meta_rec st g)
  /\ m_freeable (get_meta_rec st1 g) = m_freeable (get_meta_rec st g)
  /\ conc st1 g = conc st g.
Proof.
ltac2:(KReplay.run1 (kr_t_ASlot_W9 ()) ["AC_1"] "p'0h02Hah11zh21Hh37__arithh46__sat6h56__sat7h66__sat8h76__sat9h84__x1h91gh:2E1h;2E2h<2E3h=2E4h>2E5h?2GMh@2MWhA2RAhB2RFhC2TRhD4__ffhE8__varmaphF5__withG1ahH2g0hI2schJ2sthK3st1i001ri011xp;3p;5p;2p;1p;4p;7p;6g0000R0p4p70R1p1000hp4p710p8P1g001FR2p4p710R3p8P1p1001dR4p4p710p8P1P4p4p7210p8P1g002=R4p4p710p8P1p1002Vp4p73110p8P1g002hR1p4p710p8g003<R5p4p70R6P3p8P6P4p4p741110p8P6P1p4p7210p8P6P1p4p73110p8g0044j3{Tg004oj3zTg005gj5fTg006aj20Tg007aj13Tg008_j12Tg009]j2FTg00:Zj1?Tg00;Uj1DTg00<:j1KTg00<Xj2[Tg00=5j1=Tg00>0j2;Tg00>Lj1GTg00?Jj27Tg00@Bj1<Tg00AAj4bTg00B=j4aTg00C9j7`Tg00D5j4_Tg00Dnj1ITg00ESj26Tg00Eoj1LTg00FkR6j21Tg00GFj4wTg00HAj4vTg00I<j5uTg00JGj2\Tg00Joj3RTg00KSj1tTg00L3j1sTg00LSj2rTg00M1j1qTg00MOj1pTg00N:j2oTg00N]j4nTg00OHj7mTg00Olj2lTg00PNj2XTg00Phj2iTg00QTj38Tg00Qnj3hTg00RMj4jTg00S?j4kTg00SSj1PTP4j4gTg00TPj3YTg00Tmj1eTg00Ugj3WTg00VDj2ZTg00Vaj4dTP2j6MTg00W^j4CTg00X9j1]TP1j6cTf1R1#]f0R2#]585p=>g00Y2R5%31;82p=O%L1%L2585p=@f2R4#<%<1585/12p=9f4R3f3R7A8541/12'1'1p=AA8537A8541/12'1p=Sg00YPR8/641;12'1p=5A8512p=4%24=851/12p=H1684/11/12p=:1112,14p=B%21=852p=V%<1=852p=U1682p=J1641,17/12p=Q1112,14,17,13p=E1681/12p=T1612,14p=yA8541/12p=^1;12,14p=xg00YnR9g00ZLR:P7P4P1P2Ecp=Ng00[HR;A{174Az341P7f5R<P3P1P4Df1034R=10<4R>'>%3>,O=%2=%2>1@=>99=>DAP610<7R>f6R=/07R7'>%3>%37%2>%271@>799>7DS1F=310=3R7#?R>g00\DR?#DR@#KRA%D@#D#D#D#KR@'[RB75>%=7R>1;>B%G7f7R>/03RC,>7%37%3C%2C17=317>3'45H7997CDA3:3BP210><f8RC/0<'>10C=R<#3f9R7/0=R3#3%2<%231@<399<3DSP6107>R3f:R</0>RD#3'O%2D1@3D993D5H31F<C10<CR3#?RD?5DB%=3RD1;DB%G3f;RD/0CRE,>3%33%3E%2E17<C17DC'45H3993EDA3:3BP210D7f<RE/07#3'O10E<R7f=R3/0<R<#21@7<997<3HP6103DR<f>R7/0DRC#2'V1@<C99<C1F7E107ERC#?R<?5<B%=CR<1;<B%GCf?R</0ERF,>C%3C%3F%2F177E17<E'45HC99CFDA3:3BP210<3f@RF/03#2'V10F7R3fARC/07R71@3739P610C<R7fBR3/0<RE#<'U1@7E1F3F103FRE#?R7?57B%=ER71;7B%GEfCR7/0FRG,>E%3E%3G%2G173F177F'45HE99EGDA3:3BP2107CfDRG/0C#<'U10G3fERE/03'@PGfFRFPEP3P7PFPGP7PCCbPFPGP7PCCaF`10E7RC#?R31;3B%=CRC?5CB3:P610FGRG#?R6?56B%=GRG?5GBfGRG/FE10GER6#?RC?5CB%=6RC1;CB%G6fHRC/0ER3,>6%36%33%2317GE17CE'45H69963DA3:3BP210CF#?R3?53BfIR3/0G#=R6?56BfKR6P3PCPFC_106C#GP5fLRF/03RE#3RHfJRI,FFRJ10FIRK#?RL?5LBRL%=KRM?5MBRM%J2RNP2%I?RO#I#I#IRP#KRQ%2KRR%K?RS,6R%<KRT%IP#KRP,6T%LKRU%DO#I#D#D#KRO,[ARV75URU3:RW3:CQfMRX/0IRY,>KRK%3YRZ,42%<YR[,4TRT%2YRY,4R17FI17XI'4RRDEDEX15P5%2ER\PJPLPM16ZQ,TZR]AyN2S;BWPK14ZZRZPT142YPRDEDEX15P5%<ERTPJPLPM16YS,TYRWPNP2PPPUCQ5B]PKPZP2P[A^YYRRRDADEX15P5%LERYPJPLPM16[PAxN2V5:[9B]WPKPZP[P[PRDADEX151F63RR1063R[#?RZ?5ZBRZ%=[RK?5KBRK16HQ16\S16TPA5YYV5:T5:\5:HRY1>[ERE14HHRP14TTRS14\\RQ176317F3'4RW'1R]'1RN'1RM'1RL'1RJ'1RU'1PFP6P3PIPFP6PCCwPFPIP3PGCvDuPZPUP4PKPJP1PYPLP2PEPMP7PPPN1\AORN1;8ARP%JO1;8V[[R7%JARMg00\iRLARAO1UW0RO%JV\L^0MRV1\A@RY%J@1;8B[\PRPARA@1VLX0MR@%JB\L^0MRMg00]ERL#t%sL1r51%q5%p5RLg00^1g00^PRBPBg00_0RBP51o5?R?g00_PP?Cng00`7Fm1lLBP2P4g00`WRBg00a7RL'X1i24=8BLdAh581CjbDbEbFX85RL1422^85RBP2fQfN'0R4#3O1b3b4b5b6b7PSP]PNP7POPVPYPPP@PMPLPBP2%<4O1b3b4b5b6b7PQPWPNP7POPVPYPPP@PMPLPBP2%24O1b3b4b5b6b7P9g00aWR4g00b0RBP:CkRL%PFRMg00bNR@P:P5PLP9P4PBP:CgRBAY95IR4P2CN%e2RPAW956'ZRYP8n10110100021010000P@P:P5PLPBP4%PXCNPYP8n10110100021010000'4X9LP@P:P5PLPBAY953PMCNAW95I,ZPP8n10110100021010000,X5%P6PIPFP6PCCdEMPWeCCCCCCCCCCCCCCCC%L[P=EM%<[R=P>EM%2[R>PDEM%3[RDP<EMPRPZPK%G[PE14DHP=PTA^>\WDADEeb@WBWAP1P2O2n2001000000121000000bGW>W=P1P2O2n2001000000121000000W2W<P1P2O2n2001000000121000000W2W;P1P2O2n2001000000121000000W2W:P1P2O2n2001000000121000000bHW?WCX90XI5XK;WJo"). Qed.

Lemma disjoint_high W A n : (forall lo hi, In (lo, hi) W -> hi <= alloc_ceiling) -> alloc_ceiling <= A -> disjoint_from W A n.
Proof.
ltac2:(KReplay.run1 (kr_t_ASlot_W9 ()) ["AC_1"] "p'0h02hih12loh21Wh32HAh42HWh54__p1h64__x1h74__x2h84__x3h91Ah:1Hh;3Hinh<2IHh=7__arithh>4__ffh?8__varmaph@5__withA1ahB3hi'hC1lhD3lo'hE1ni001pi011zp;2p;1p;3p;4p;6p;7p;5p;8g00c0R0j2ZTg00L3j1DTg00cPj31Tg00cgj1YTg00ESj20Tg00dcj32Tg00KSj1=Tg00ebj34Tg00VDj2;Tg00fBj2>Tg00QTj37Tg00PNj2CTg00f\j3XTg00g6j1ATg00gUj29Tg00h>j3@Tg00hgj2RTg00LSj2?Tg00iSj1OTg00j1j4:Tg00M1j1NTg00MOj1MTg00;Uj1<Tg00N:j28Tg00Dnj1LTg00jOj1ITg00k1j6JTg00kUj7KTg00Olj2HTg00Phj2GTg00Qnj3FTg00RMj4PTg00l9j3QTg00W^j4ETg00lSj5STg00m5j4TTg00N]j4WTg00OHj7VTg00mUj8UTg00Y2R1P1f1R2f0R3CTp=3P1P2g00n9P3CWp=6P2g00^1R4g00^PR5P5g00_0R6P3g00`7FVp=5f3R7P4P5P5P6f2R8P2P3GUp=B1Z11R9#DR:P91323R;=198p,5ACEIL#YR<,02R=[^01^11R>10<7f4R?=287[[X2:%=9R@919;P=[^01^1110<8g00n`A2@78eW3W4P0P1P1f5R0,0<f6R@=280[\>A49?7RA919;P=[^01^1110<@f7RB=2A@[[[^C:P3f8RA,0<f9RC=28A[\>130?R>=497RD919;P=[^01^1110<Cf:R=/;C/0010?='>A27=CP2P0P?A79>>A19>71C9>3XO310?<p-0R>g00]EREg00o<RF#ARG#A,91191G191F5@15@1g00o['R%=E34%DEP1P11?18P7%O1REC:P2P11?17P7PEC:C:%N1%M1REg00\DRF#<RG#<,81RH%LG,81RG'6,5E%I5RIPE181FRF,6G,5EPIPEP4P5P5P6PEP4P5P5P6P0EJ16HF,5EFKCBCB1HE6P3P8g00`WREg00a7R6'C1G38=7E6dg00YP=F12CPb>b?b@X61X71X81W5102810721078,>0[[^61^71^81^5>P3f<R>f;';/0BP<P@P>P2P8O6b=b:P8A19;0P?P8P213AB1382RA579A19A@;Q3O3W;XB1XD1P3O2CEA2D=CeW3W4W<X2:X01X11P2P3O2n2001100000121101101XA9P8DSXE1X91W2o"). Qed.

Lemma decay_cases c st : decay_bounces c st = st \/ exists v, decay_bounces c st = set_bounce (c - 7) v st.
Proof.
ltac2:(KReplay.run1 (kr_t_ASlot_W9 ()) ["AC_1"] "p'0h01vh11bi001bh21ch32stp;1p;2p;3p;4g010Gj1ATg00Dnj19Tg00<:j16Tg011Jj21Tg011gj23Tg012bj2<Tg013?j1;Tg013]j2:Tg014;j32Tg0159j24Tg00fBj25Tg00PNj28Tg015Sj4@Tg00l9j3?Tg00f\j3>Tg015mj27Tg00QTj3=Tg00[HR0f1R1f0R23=p=0g00Y2R3%A1g00\DR4#9#9#6R5,11,32g00YP'<#;':g00`WR6P6P6P0P2f3R7/15R8f2R9/38%64R4'1;29R:P9n0100000020000/09P6P0P1f4/15R61376/14;27P7n0100000020000A2627'0X03,43'5P21195R51315/14R4;21R6/01A2829R8,0:X03R:,43P3P:P41806C@3?10111098X03,4318013>n0110000020000b11712/021791A2521'0X03,43'5eX30W2o"). Qed.
Lemma active_decay c st i : active (decay_bounces c st) i = active st i.
Proof.
ltac2:(KReplay.run1 (kr_t_ASlot_W9 ()) ["AC_1"] "p'0h01vh11Hh21mh31ch41ih51oh62sti001xp;2p;1p;3p;6g016nj2<Tg015mj22Tg00Dnj17Tg00<:j1;Tg011Jj24Tg014;j33Tg0159R0j26Tg00fBR1j2:Tg017lj20Tg00QTj35Tg00PNj28Tg001Fj69Tg00[HR2f1R3f0R435p=1g00Y2R5f2R6/<31263/13f3R7/26R8g00\D#7#7#;R9,47?346'1X05,65':P11186f4R8/27R11489?347'1X05,65g003<R:1016107635P41117P2P81048f5R1/08R655:X221087,8:1218R7P4E9W1P4O11419?348,17X05,65P0P5f6R0/21R71409?341'1X051078=5:6P4f8R6f7R7'21469?347'1P2f9R8/49?3361046108655:X221067,8:1286P4E9W1X05P3P4O2n2001000000120100000W1P4O1n200100000021000010000b5X45X62W3o"). Qed.
Lemma rec_decay c st q : get_meta_rec (decay_bounces c st) q = get_meta_rec st q.
Proof.
ltac2:(KReplay.run1 (kr_t_ASlot_W9 ()) ["AC_1"] "p'0h01vh11Hh21mh31ch41oh51qh62sti001xp;2p;1p;3p;6g016nj2<Tg015mj22Tg00Dnj17Tg00<:j1;Tg011Jj24Tg014;j33Tg0159R0j26Tg00fBR1j2:Tg006aj20Tg00QTj35Tg00PNj28Tg001Fj69Tg00[HR2f1R3f0R435p=1g00Y2R5g0000f2R6/<31263/13f3R7/26R8g00\D#7#7#;R9,47?346'1X05,65':P11186f4R8/27R11489?347'1X05,65g018fR:1016107635P41117P2P81048f5R1/08R655:X221087,8:1218R7P4E9W1P4O11419?348,17X05,65P0P5f6R0/21R71409?341'1X051078=5:6P4f8R6f7R7'21469?347'1P2f9R8/49?3361046108655:X221067,8:1286P4E9W1X05P3P4O2n2001000000120100000W1P4O1n200100000021000010000b4W5X62W3o"). Qed.
Lemma active_upd_meta g f st i : active (upd_meta g f st) i = active st i.
Proof.
ltac2:(KReplay.run1 (kr_t_ASlot_W9 ()) ["AC_1"] "h01fh11gh21ih32stp;2g017lj21Tg00PNj20Tg0000g018fR0P0[g00[Hg00Y2g003<f1f0'1'0W2W3W0W1o"). Qed.

Section PHASE.
Context {R : Type}.
Variables (K : mstate -> Z -> Malloc.M R) (bail : Malloc.M R).
Variables (o : mem) (s : PState) (Q : R -> PState -> machine_state -> Prop).
Variables (st : mstate) (m : mem) (sc lo : Z).
Variables (ra sp gp tp t0 t2 s0 s1 a1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32).
Hypothesis TAF : taf st sc.
Hypothesis SC : 0 <= sc < 48.
Hypothesis CLO : alloc_ceiling <= lo.
Hypothesis LO : lo <= bv_unsigned sp - 96.
Let spv := bv_unsigned sp.

Hypothesis HK1 : forall stX g3 msk k m' (t1' t3' t4' a2' a3' a4' a5' a6' a7' : word),
  ta_rel sc st stX -> active stX sc = Some g3 -> gmf st sc g3 ->
  msk = m_avail (get_meta_rec stX g3) -> 0 < msk < 2^32 -> lowbit msk = 2 ^ k -> 0 <= k < 32 ->
  mrep (upd_meta g3 (m_set_avail (msk - lowbit msk)) stX) m' -> mem_inv asegs m' -> stk asegs m' lo spv ->
  pres_except (ta_fp st lo spv) m m' ->
  implT o (K (upd_meta g3 (m_set_avail (msk - lowbit msk)) stX) (lowbit msk)) s Q
    (MS (mkR ra sp gp tp t0 t1' t2 s0 s1 (wz k) a1 a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5 t6)
        F (ret_pc ra) fc None m' (seg_rom asegs)).

Definition nclosed (stX : mstate) (P : aptr -> Prop) : Prop :=
  forall q, P q -> gmf st sc q /\ exists t, m_next (get_meta_rec stX q) = Some t /\ P t.

End PHASE.

End AC_1.
