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
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.CJ.Lib Require Import Tac Image ZBridge SysStep SFModel ITree Nodes Decode Arr.
(* [comment removed for export] *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.CJ.Agent Require Import F_syscalls MallocRep F_malloc_free F_malloc_fast F_malloc_enframe MallocTree MallocKit_A.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.CJ.Agent Require Import MallocKit_AB.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.CJ.Spec Require Import STree Malloc MallocCtrl Monad Prog.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.CJ.Agent Require Import Malloc_fp MallocKit_A2.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.CJ.Agent Require Import MallocNat MallocFacts_AS MallocKit_A3 ASlot_W0 ASlot_W1 ASlot_W2 ASlot_W3 ASlot_W4 ASlot_W5 ASlot_W6 ASlot_W7 ASlot_W8.
Import ListNotations.
Open Scope Z_scope.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.CJ.Lib Require Import RunP.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require KReplay.
Ltac2 kr_t_ASlot_W9 () := "C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc4aptrC13~~~I35stdpp9countable9Countable00C35stdpp4base;RelDecisionC35stdpp4gmap;gmap_lookupC35stdpp4base4fmapC35stdpp4base6lookupC99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc4optrC13~~~I99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ5Agent8ASlot_W06ta_rel00C13~~~i99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ5Agent8ASlot_W93gmf00C13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ5Agent8ASlot_W07tr_geomC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc<get_meta_recC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc:m_last_idxC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc:m_freeableC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ5Agent9MallocRep9meta_slotC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc7m_availC13~~~K47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1Z02C56Stdlib6ZArith6BinInt1Z3powC99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc7m_freedC13~~~C56Stdlib6ZArith6BinInt1Z2ltC99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ5Agent>MallocFacts_AS5mw_okC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc4concC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc;m_sizeclassC13~~~c99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ5Agent8ASlot_W99gmf_availC13~~~c99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ5Agent8ASlot_W99gmf_freedC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ5Agent8ASlot_W09tr_mrangeC13~~~c99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ5Agent8ASlot_W96gmf_mwC13~~~K47Corelib7Numbers7BinNums8positive01C56Stdlib6ZArith6BinInt1Z2leC99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc8m_maplenC13~~~I47Corelib4Init5Logic3and00C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ5Agent8ASlot_W08tr_areasC13~~~c99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ5Agent8ASlot_W98gmf_slotC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ5Agent<MallocKit_ABDmeta_slot_same_areasC13~~~C56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z:pow_nonnegK47Corelib4Init9Datatypes4list01I47Corelib4Init9Datatypes4list00K46Stdlib9micromega6VarMap1t02I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr02K46Stdlib9micromega=RingMicromega7Formula01K46Stdlib9micromega5Tauto8GFormula04C46Stdlib9micromega5Tauto8BFormulaK47Corelib4Init5Logic2eq01C46Stdlib9micromega:ZMicromega=ZTautoCheckerI47Corelib4Init5Logic2eq00C46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundI35stdpp4gmap4gmap00C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc9s_regionsC13~~~C47Corelib4Init9Datatypes3fstC99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc6r_baseC13~~~C47Corelib4Init9Datatypes3sndC56Stdlib6ZArith6BinInt1Z3addC99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ5Agent8ASlot_W0:tr_regionsC13~~~C47Corelib4Init5Logic8eq_ind_rK47Corelib4Init5Logic3and01C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc5m_memC13~~~I47Corelib7Numbers7BinNums1Z00K47Corelib7Numbers7BinNums1Z01I47Corelib7Numbers7BinNums1N00I99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc6region00C13~~~I99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc6mstate00C13~~~K47Corelib7Numbers7BinNums8positive03I47Corelib4Init5Logic4True00I46Stdlib9micromega:ZMicromega;ZArithProof00C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K46Stdlib9micromega=RingMicromega3Op201K47Corelib4Init9Datatypes4unit01I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01C45stdpp7numbers1N6eq_decC35stdpp9countable;N_countableI47Corelib4Init9Datatypes6option00I47Corelib4Init9Datatypes4prod00C46Stdlib5Lists4List2InC99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib4RunP=alloc_ceilingC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ3Lib5Frame=disjoint_fromC13~~~K47Corelib4Init9Datatypes4list02I47Corelib4Init5Logic2or00K47Corelib4Init5Logic2or01K47Corelib4Init9Datatypes3nat02K46Stdlib9micromega=RingMicromega5Psatz02K46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega:ZMicromega;ZArithProof02K46Stdlib9micromega6VarMap1t01K46Stdlib9micromega6VarMap1t03K47Corelib4Init9Datatypes6option02K46Stdlib9micromega5Tauto8GFormula03K46Stdlib9micromega5Tauto8GFormula06K47Corelib4Init5Logic2or02C47Corelib4Init9Datatypes8list_indK47Corelib4Init9Datatypes4prod01K46Stdlib9micromega5Tauto8GFormula08K46Stdlib9micromega=RingMicromega3Op203K47Corelib4Init5Logic4True01K47Corelib4Init9Datatypes3nat01K46Stdlib9micromega:ZMicromega;ZArithProof01C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc?sc_in_seq_rangeC13~~~C56Stdlib6ZArith6BinInt1Z3subC99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc7bouncesC13~~~C56Stdlib6ZArith6BinInt1Z3eqbC47Corelib4Init9Datatypes4negbC47Corelib4Init9Datatypes4andbC99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc:set_bounceC13~~~I47Corelib4Init5Logic2ex00K47Corelib4Init5Logic2ex01C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc=decay_bouncesC13~~~c99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ5Agent8ASlot_W9;decay_casesC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc6activeC13~~~I99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc4meta00C13~~~".
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Section CEIL_WRAP_1.
Context {RUNp : RunP}.

(* [comment removed for export] *)

(* [comment removed for export] *)
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

(* [comment removed for export] *)
Record taf (st : mstate) (sc : Z) : Prop := mkTAF {
  taf_head : forall g, active st sc = Some g -> gmf st sc g /\ m_sizeclass (get_meta_rec st g) = sc;
  taf_next : forall g n, gmf st sc g -> m_next (get_meta_rec st g) = Some n ->
               gmf st sc n /\ m_sizeclass (get_meta_rec st n) = m_sizeclass (get_meta_rec st g) /\ m_prev (get_meta_rec st n) = Some g;
  taf_prev : forall g p, gmf st sc g -> m_prev (get_meta_rec st g) = Some p ->
               gmf st sc p /\ m_next (get_meta_rec st p) = Some g;
  taf_bnc : forall i, 0 <= bounces st i < 256
}.

(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma gmf_geom st st1 sc g : ta_rel sc st st1 -> gmf st sc g ->
  meta_slot st1 g /\ 0 <= m_avail (get_meta_rec st1 g) < 2^32 /\ 0 <= m_freed (get_meta_rec st1 g) < 2^32
  /\ mw_ok (get_meta_rec st1 g)
  /\ m_mem (get_meta_rec st1 g) = m_mem (get_meta_rec st g)
  /\ m_last_idx (get_meta_rec st1 g) = m_last_idx (get_meta_rec st g)
  /\ m_sizeclass (get_meta_rec st1 g) = m_sizeclass (get_meta_rec st g)
  /\ m_freeable (get_meta_rec st1 g) = m_freeable (get_meta_rec st g)
  /\ conc st1 g = conc st g.
Proof.
ltac2:(KReplay.run1 (kr_t_ASlot_W9 ()) ["CEIL_WRAP_1"] "p'0h02Hah11zh21Hh37__arithh46__sat6h56__sat7h66__sat8h76__sat9h81gh94__x1h:2sch;2sth<3st1h=2E1h>2E2h?2E3h@2E4hA2E5hB2GMhC2MWhD2RAhE2RFhF2TRhG4__ffhH8__varmaphI5__withJ1ahK2g0i001ri011xp;3p;5p;2p;1p;4p;7p;6g0000R0p4p70R1p1001>p4p710p8P1p1001\R2p4p710p8P1P2p4p7210p8P1g0025R2p4p710p8P1p1002Np4p73110p8P1g002`R1p4p710p8g0034R3p4p70R4P2p4p741110p8P4P1p4p7210p8P4P1p4p73110p8g004Bj3{Tg005Wj3zTg006ij5fTg008=j20Tg009Sj13Tg00:gj12Tg00<;j2FTg00=Rj1?Tg00>cj1DTg00?Hj1KTg00?fj2[Tg00@Cj1=Tg00ATj2;Tg00B0j1GTg00CHj27Tg00DVj1<Tg00Ekj4bTg00GAj4aTg00HWj7`Tg00Imj4_Tg00K@j1ITg00Kej26Tg00LAj1LTg00MSR4j21Tg00Mnj4wTg00OCj4vTg00PXj5uTg00R=j2\Tg00Rej3RTg00SIj1tTg00Sij1sTg00TIj2rTg00Tgj1qTg00UEj1pTg00V0j2oTg00VSj4nTg00W>j7mTg00Wbj2lTg00XDj2XTg00X^j2iTg00YJj38Tg00Ydj3hTg00ZCj4jTg00[5j4kTg00[Ij1PTP2j4gTg00\\j3YTg00]9j1eTg00^Ij3WTg00^fj2ZTg00_Cj4dTg00`Zj6MTg00a8j4CTg00aSj1]TP1j6cTf1R1#]f0R2#]583p=>g00bbR3%31;82p=O%L1%L2583p=@f2R5#<%<1583/12p=9f4R6f3R7A8351/12'1'1p=AA8367A8351/12'1p=Sg00c@R8/651;12'1p=5A8312p=4%25=831/12p=H1685/11/12p=:1112,15p=B%21=832p=V%<1=832p=U1682p=J1651,17/12p=Q1112,15,17,16p=E1681/12p=T1612,15p=yA8351/12p=^1;12,15p=xg00c^R9g00d<R:P7P5P1P2Ecp=Ng00eNR;A{175Az651P7f5R<P6P1P5Df1065R=10<5R>'>%3>,O=%2=%2>1@=>99=>DAP410<7R>f6R=/07R?'>%3>%3?%2>%2?1@>?99>?DS1F=610=6R?#?R>g00f`R@#DRA#KRB%DA#D#D#D#KRA'[RC75>%=?R>1;>C%G?f7R>/06RD,>?%3?%3D%2D17=617>6'45H?99?DDA3:3BP210><f8RD/0<'>10D=R<#3f9R?/0=R6#3%2<%261@<699<6DSP410?>R6f:R</0>RE#3'O%2E1@6E996E5H61F<D10<DR6#?RE?5EC%=6RE1;EC%G6f;RE/0DRF,>6%36%3F%2F17<D17ED'45H6996FDA3:3BP210E?f<RF/0?#3'O10F<R?f=R6/0<R<#21@?<99?<3HP4106ER<f>R?/0ERD#2'V1@<D99<D1F?F10?FRD#?R<?5<C%=DR<1;<C%GDf?R</0FRG,>D%3D%3G%2G17?F17<F'45HD99DGDA3:3BP210<6f@RG/06#2'V10G?R6fARD/0?R?1@6?39P410D<R?fBR6/0<RF#<'U1@?F1F6G106GRF#?R??5?C%=FR?1;?C%GFfCR?/0GRH,>F%3F%3H%2H176G17?G'45HF99FHDA3:3BP210?DfDRH/0D#<'U10H6fERF/06'@PHfFRGPFP6P?PGPHP?PDCbPGPHP?PDCaF`10F?RD#?R61;6C%=DRD?5DC3:P410GHRH#?R4?54C%=HRH?5HCfGRH/FF10HFR4#?RD?5DC%=4RD1;DC%G4fHRD/0FR6,>4%34%36%2617HF17DF'45H49946DA3:3BP210DG#?R6?56CfIR6/0H#=R4?54CfKR4P6PDPGC_104D#GP3fLRG/06RF#3RIfJRJ,FGRK10GJRL#?RM?5MCRM%=LRN?5NCRN%J2ROP2%I@RP#I#I#IRQ#KRR%2LRS%K@RT,6S%<LRU%IQ#KRQ,6U%LLRV%DP#I#D#D#KRP,[BRW75VRV3:RX3:CQfMRY/0JRZ,>LRL%3ZR[,42%<ZR\,4URU%2ZRZ,4S17GJ17YJ'4RSDEDEX13P3%2FR]PKPMPN16[R,T[R^AyO2T;BXPL14[[R[PU142ZPSDEDEX13P3%<FRUPKPMPN16ZT,TZRXPOP2PQPVCQ5B^PLP[P2P\A^ZZSRSDADEX13P3%LFRZPKPMPN16\QAxO2W5:\9B^XPLP[P\P\PSDADEX131F46RS1046R\#?R[?5[CR[%=\RL?5LCRL16IR16]T16UQA5ZZW5:U5:]5:IRZ1>\FRF14IIRQ14UURT14]]RR174617G6'4RX'1R^'1RO'1RN'1RM'1RK'1RV'1PGP4P6PJPGP4PDCwPGPJP6PHCvDuP[PVP5PLPKP1PZPMP2PFPNP?PQPO1\BPRO1;8BRQ%JP1;8W[[R?%JBRNg00gERMARBP1UW0RP%JW\M^0NRW1\BARZ%JA1;8C[\QRQARBA1VMX0NRA%JC\M^0NRNg00gaRM#t%sM1r31%q3%p3RMg00hMg00hlRCPCg00iLRCP31o3@R@g00ilP@Cng00jSFm1lMCP2P5g00k3RCg00kSRM'X1i25=8CMdAh381CjbGbHbIX93RM1422^93RCP2fQfN'0R@#3O1b3b4b5b6b7PTP^POP?PPPWPZPQPAPNPMPCP2%<@O1b3b4b5b6b7PRPXPOP?PPPWPZPQPAPNPMPCP2%2@O1b3b4b5b6b7P9g00l3R@g00lLRCP:CkRM%PGRNg00ljRAP:P3PMP9P@PCP:CgRCAY93JR@P2CN%e2RQAW934'ZRZP8n10110100021010000PAP:P3PMPCP@%PYCNPZP8n10110100021010000'4X8MPAP:P3PMPCAY936PNCNAW93J,ZQP8n10110100021010000,X3%P4PJPGP4PDCdEMPXeCCCCCCCCCCCCCCCC%L\P=EM%<\R=P>EM%2\R>PEEM%3\REP<EMPSP[PL%G\PF14EIP=PUA^>]XDADEebCWEWDP1P2O2n2001000000121000000bJWAW@P1P2O2n2001000000121000000W2W?P1P2O2n2001000000121000000W2W>P1P2O2n2001000000121000000W2W=P1P2O2n2001000000121000000bKWBWFX80X:3X<;X;;P7P5P1P2O4X80X:3X<;W;o"). Qed.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma disjoint_high W A n : (forall lo hi, In (lo, hi) W -> hi <= alloc_ceiling) -> alloc_ceiling <= A -> disjoint_from W A n.
Proof.
ltac2:(KReplay.run1 (kr_t_ASlot_W9 ()) ["CEIL_WRAP_1"] "p'0h02hih12loh21Wh31Ah42HAh52HWh64__p1h74__x1h84__x2h94__x3h:1nh;1Hh<3Hinh=2IHh>7__arithh?4__ffh@8__varmaphA5__withB1ahC3hi'hD1lhE3lo'i001pi011zp;2p;1p;3p;4p;6p;7p;5p;8g00mLR0j2ZTg00Sij1DTg00mlj31Tg00nCj1YTg00Kej20Tg00oWj32Tg00SIj1=Tg010lj34Tg00^fj2;Tg011Lj2>Tg00YJj37Tg00XDj2CTg011fj3XTg012@j1ATg012_j29Tg013Hj3@Tg0141j2RTg00TIj2?Tg014]j1OTg015;j4:Tg00Tgj1NTg00UEj1MTg00>cj1<Tg00V0j28Tg00K@j1LTg015Yj1ITg016;j6JTg016_j7KTg00Wbj2HTg00X^j2GTg00Ydj3FTg00ZCj4PTg017Cj3QTg00a8j4ETg017]j5STg018?j4TTg00VSj4WTg00W>j7VTg018_j8UTg00bbR1P1f1R2f0R3CTp=3P1P2g019CP3CWp=6P2g00hMR4g00hlR5P5g00iLR6P3g00jSFVp=5f3R7P4P5P5P6f2R8P2P3GUp=B1Z11R9#DR:P91323R;=198p,4RUNp#YR<,02R=[^01^11R>10<7f4R?=287[[X2:%=9R@919;P=[^01^1110<8g019jA2@78eW4W5P0P1P1f5R0,0<f6R@=280[\>A49?7RA919;P=[^01^1110<@f7RB=2A@[[[^D:P3f8RA,0<f9RC=28A[\>130?R>=497RD919;P=[^01^1110<Cf:R=/;C/0010?='>A27=CP2P0P?A79>>A19>71C9>3XO310?<p-0R>g00gaREg01:FRF#ARG#A,91191G191F5@15@1g01:e'R%=E34%DEP1P11?18P7%O1REC:P2P11?17P7PEC:C:%N1%M1REg00f`RF#<RG#<,81RH%LG,81RG'6,5E%I5RIPE181FRF,6G,5EPIPEP4P5P5P6PEP4P5P5P6P0EJ16HF,5EFKCBCB1HE6P3P8g00k3REg00kSR6'C1G38=7E6dg00c@=F12CPb?b@bAX71X81X91W6102810721078,>0[[^71^81^91^6>P3f<R>f;';/0BP<P@P>P2P8O6b>b;P8A19;0P?P8P213AB1382RA579A19A@;Q3O3W<XC1XE1P3O2CEA2D=CeW4W5W=X2:X01X11P2P3O2n2001100000121101101XB9P8DSX:1X31X2:P8P2P3O3X:1X31W2o"). Qed.


(* [comment removed for export] *)
Lemma decay_cases c st : decay_bounces c st = st \/ exists v, decay_bounces c st = set_bounce (c - 7) v st.
Proof.
ltac2:(KReplay.run1 (kr_t_ASlot_W9 ()) ["CEIL_WRAP_1"] "p'0h01vh11ch22sth31bi001bp;1p;2p;3p;4g01;Qj1ATg00K@j19Tg00?Hj16Tg01<jj21Tg01=Gj23Tg01>Xj2<Tg01?5j1;Tg01?Sj2:Tg01@1j32Tg01AEj24Tg011Lj25Tg00XDj28Tg01A_j4@Tg017Cj3?Tg011fj3>Tg01B9j27Tg00YJj3=Tg00eNR0f1R1f0R23=p=0g00bbR3%A1g00f`R4#9#9#6R5,11,32g00c@'<#;':g00k3R6P6P6P0P2f3R7/15R8f2R9/38%64R4'1;29R:P9n0100000020000/09P6P0P1f4/15R61376/14;27P7n0100000020000A2627'0X03,43'5P21195R51315/14R4;21R6/01A2829R8,0:X03R:,43P3P:P41806C@3?10111098X03,4318013>n0110000020000b31712/021791A2521'0X03,43'5eX20X13P1P2O2X20W1o"). Qed.
Lemma active_decay c st i : active (decay_bounces c st) i = active st i.
Proof.
ltac2:(KReplay.run1 (kr_t_ASlot_W9 ()) ["CEIL_WRAP_1"] "p'0h01vh11Hh21ch31ih41mh52sth61oi001xp;2p;1p;3p;6g01CPj2<Tg01B9j22Tg00K@j17Tg00?Hj1;Tg01<jj24Tg01@1j33Tg01AER0j26Tg011LR1j2:Tg01Dhj20Tg00YJj35Tg00XDj28Tg00`Zj69Tg00eNR2f1R3f0R435p=1g00bbR5f2R6/<31263/13f3R7/26R8g00f`#7#7#;R9,47?346'1X05,65':P11186f4R8/27R11489?347'1X05,65g0034R:1016107635P41117P2P81048f5R1/08R;55:X421087,8:1218R7P4E9W1P4O11419?348,17X05,65P0P5f6R0/21R71409?341'1X051078=5:;P4f8R;f7R7'214;9?347'1P2f9R8/49?33;104;108;55:X4210;7,8:128;P4E9W1X05P3P4O2n2001000000120100000W1P4O1n200100000021000010000b6X35X52X25P6P3P4O3X35X52W2o"). Qed.
Lemma rec_decay c st q : get_meta_rec (decay_bounces c st) q = get_meta_rec st q.
Proof.
ltac2:(KReplay.run1 (kr_t_ASlot_W9 ()) ["CEIL_WRAP_1"] "p'0h01vh11Hh21ch31mh41qh52sth61oi001xp;2p;1p;3p;6g01CPj2<Tg01B9j22Tg00K@j17Tg00?Hj1;Tg01<jj24Tg01@1j33Tg01AER0j26Tg011LR1j2:Tg008=j20Tg00YJj35Tg00XDj28Tg00`Zj69Tg00eNR2f1R3f0R435p=1g00bbR5g0000R6f2R7/<31273/13f3R8/27R9g00f`#7#7#;R:,48?347'1X05,65':P11197f4R9/28R1149:?348'1X05,65g01F8R;1017108735P41118P2P91049f5R1/09R<55;X321098,8;1219R8P4E9W1P4O1141:?349,18X05,65P0P5f6R0/21R8140:?341'1X051089=5;<P4f8R<f7R8'214<:?348'1P2f9R9/4:?33<104<109<55;X3210<8,8;129<P4E9W1X05P3P4O2n2001000000120100000W1P4O1n200100000021000010000b6X46X52X25P7P3P4O3W4X52W2o"). Qed.
Lemma active_upd_meta g f st i : active (upd_meta g f st) i = active st i.
Proof.
ltac2:(KReplay.run1 (kr_t_ASlot_W9 ()) ["CEIL_WRAP_1"] "h01fh11gh21ih32stp;2g01Dhj21Tg00XDj20Tg0000R0g01F8R1P1[R1g00eNR2g00bbR3g0034f1R4f0R5'1'0X23X32X01X10f3f2P4P5O4W2W3W0W1o"). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
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
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition nclosed (stX : mstate) (P : aptr -> Prop) : Prop :=
  forall q, P q -> gmf st sc q /\ exists t, m_next (get_meta_rec stX q) = Some t /\ P t.
(* [comment removed for export] *)
(* [comment removed for export] *)
End PHASE.
End CEIL_WRAP_1.

