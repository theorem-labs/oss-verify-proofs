(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Lib Require Import Tac Image ZBridge SysStep Walk ITree Nodes Decode Arr.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Common Require Import SFModel.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Malloc Require Import MallocRep F_malloc_free F_malloc_fast F_malloc_enframe MallocTree MallocKit_A.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Malloc Require Import MallocKit_AB.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Spec Require Import STree Malloc MallocCtrl Monad.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Malloc Require Import ProgDeps.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Malloc Require Import Malloc_fp MallocKit_A2.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Malloc Require Import MallocNat MallocFacts_AS MallocKit_A3 ASlot_W0 ASlot_W1 ASlot_W2 ASlot_W3 ASlot_W4 ASlot_W5 ASlot_W6 ASlot_W7 ASlot_W8.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Common Require Import RunDraw.
From OSSVerify.Proofs.zstd.huf_decompress.lib Require KReplay.
Ltac2 kr_t_ASlot_W9 () := "C59OSSVerify5KrLib4Spec6Malloc4aptrC1?~~~~~~~~~~~~~~~I35stdpp9countable9Countable00C47Corelib4Init5Logic8eq_ind_rC35stdpp4base;RelDecisionC35stdpp4gmap;gmap_lookupC35stdpp4base4fmapC35stdpp4base6lookupC59OSSVerify5KrLib4Spec6Malloc4optrC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib6Malloc8ASlot_W06ta_rel00C1?~~~~~~~~~~~~~~~i59OSSVerify5KrLib6Malloc8ASlot_W93gmf00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc8ASlot_W07tr_geomC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc<get_meta_recC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc:m_last_idxC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc:m_freeableC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc9MallocRep9meta_slotC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc7m_availC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1Z02C56Stdlib6ZArith6BinInt1Z3powC59OSSVerify5KrLib4Spec6Malloc7m_freedC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z2ltC59OSSVerify5KrLib6Malloc>MallocFacts_AS5mw_okC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc4concC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc;m_sizeclassC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib6Malloc8ASlot_W99gmf_availC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib6Malloc8ASlot_W99gmf_freedC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc8ASlot_W09tr_mrangeC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib6Malloc8ASlot_W96gmf_mwC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive01C56Stdlib6ZArith6BinInt1Z2leC59OSSVerify5KrLib4Spec6Malloc8m_maplenC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic3and00C59OSSVerify5KrLib6Malloc8ASlot_W08tr_areasC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib6Malloc8ASlot_W98gmf_slotC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc<MallocKit_ABDmeta_slot_same_areasC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes4list01I47Corelib4Init9Datatypes4list00K46Stdlib9micromega6VarMap1t02I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr02K46Stdlib9micromega=RingMicromega7Formula01K46Stdlib9micromega5Tauto8GFormula04C46Stdlib9micromega5Tauto8BFormulaK47Corelib4Init5Logic2eq01C46Stdlib9micromega:ZMicromega=ZTautoCheckerI47Corelib4Init5Logic2eq00C46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundI35stdpp4gmap4gmap00C59OSSVerify5KrLib4Spec6Malloc9s_regionsC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes3fstC59OSSVerify5KrLib4Spec6Malloc6r_baseC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes3sndC56Stdlib6ZArith6BinInt1Z3addC59OSSVerify5KrLib6Malloc8ASlot_W0:tr_regionsC1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic3and01C59OSSVerify5KrLib4Spec6Malloc5m_memC1?~~~~~~~~~~~~~~~I47Corelib7Numbers7BinNums1Z00K47Corelib7Numbers7BinNums1Z01I47Corelib7Numbers7BinNums1N00I59OSSVerify5KrLib4Spec6Malloc6region00C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6Malloc6mstate00C1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive03I46Stdlib9micromega:ZMicromega;ZArithProof00C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K46Stdlib9micromega=RingMicromega3Op201K47Corelib4Init9Datatypes4unit01I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01C45stdpp7numbers1N6eq_decC35stdpp9countable;N_countableI47Corelib4Init9Datatypes6option00I47Corelib4Init5Logic2ex00C35stdpp9decidable;prod_eq_decC35stdpp9countable>prod_countableC59OSSVerify5KrLib4Spec6Malloc8s_groupsC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes6option01I47Corelib4Init5Logic2or00K47Corelib4Init5Logic2or01C59OSSVerify5KrLib6Malloc9MallocRep3CTXC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6Malloc4ghdr00C1?~~~~~~~~~~~~~~~C45stdpp7numbers1Z6eq_decC35stdpp9countable;Z_countableK47Corelib4Init5Logic2or02K47Corelib4Init5Logic2ex01I47Corelib4Init9Datatypes4prod00C46Stdlib5Lists4List2InC59OSSVerify5KrLib3Lib8RunConst4ATOPC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Frame=disjoint_fromC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes4list02C59OSSVerify5KrLib6Common7RunDraw:atop_rangeC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes3nat02K46Stdlib9micromega=RingMicromega5Psatz02K46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega:ZMicromega;ZArithProof02K46Stdlib9micromega6VarMap1t01K46Stdlib9micromega6VarMap1t03K47Corelib4Init9Datatypes6option02K46Stdlib9micromega5Tauto8GFormula03K46Stdlib9micromega5Tauto8GFormula06C47Corelib4Init9Datatypes8list_indK47Corelib4Init9Datatypes4prod01K46Stdlib9micromega5Tauto8GFormula08K46Stdlib9micromega=RingMicromega3Op203K47Corelib4Init5Logic4True01K47Corelib4Init9Datatypes3nat01K46Stdlib9micromega:ZMicromega;ZArithProof01C59OSSVerify5KrLib4Spec6Malloc?sc_in_seq_rangeC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3subC59OSSVerify5KrLib4Spec6Malloc7bouncesC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3eqbC47Corelib4Init9Datatypes4negbC47Corelib4Init9Datatypes4andbC59OSSVerify5KrLib4Spec6Malloc:set_bounceC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc=decay_bouncesC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib6Malloc8ASlot_W9;decay_casesC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc6activeC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6Malloc4meta00C1?~~~~~~~~~~~~~~~".
Import ListNotations.
Open Scope Z_scope.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Section CANSEC1. Context {rc : runConstT}.
Definition ta_fp (st : mstate) (lo sp : Z) (a : Z) : Prop :=
  lo <= a < sp
  \/ CTX <= a < CTX + 928
  \/ (exists q, meta_slot st q /\ conc st q <= a < conc st q + 40)
  \/ (exists b gh, (s_groups st) !! b = Some gh /\ conc st b <= a < conc st b + 9).

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
ltac2:(KReplay.run1 (kr_t_ASlot_W9 ()) ["CANSEC1"] "p'0h01zh11Hh27__arithh31gh44__x1h52sch62sth73st1h82E1h92E2h:2E3h;2E4h<2E5h=2GMh>2MWh?2RAh@2RFhA2TRhB4__ffhC8__varmaphD5__withE1ahF2g0i001ri011xp;3p;5p;2p;1p;4p;7p;6g0000R0p4p70R1p1000ep4p710R2p8P1g001CR3p4p710R4p8P1p1001aR5p4p710R6p8P1P5p4p7210R5p8P1g002:R7p4p710p8P1p1002Sp4p73110p8P1g002eR1p4p710p8g0039R8p4p70R9P4p8P9P7p4p741110p8P9P1p4p7210p8P9P1p4p73110p8P2P6p8P2P5p8g003nj3yTg004kj3xTg005ej5cTg006aj20Tg007^j13Tg008Yj12Tg009Tj2FTg00:Sj1=Tg00;Kj1DTg00<0j1JTg00<Nj2YTg00<kj1<Tg00=cj2BTg00>?j1ETg00??j26Tg00@4j1>Tg00A0j4`Tg00Anj4_Tg00Blj7^Tg00Cjj4]Tg00Dej1ITg00EJj27Tg00Efj1KTg00F_R5j21Tg00G:j4uTg00H7j4tTg00I4j5sTg00JAj1rTg00Jaj1qTg00KAj2pTg00K_j1oTg00L=j1nTg00Lhj2mTg00MKj4lTg00N6j7kTg00NZj2iTg00O<j2WTg00OVj2hTg00PBj38Tg00P\j3gTg00Q;j4fTg00Qmj4eTg00RAj1MTP7j4jTg00S;j3XTg00SXj1dTg00TOj3VTg00Tlj2ZTg00UIj4bTP3j6LTg00VHj4ATg00Vcj1UTP1j6aTf1R1#Uf0R3#U588p=;g00WYR8%31;83p=N%K1%K3588p=?f2R7#>%>1588/13p=:f4R2f3R6A8871/13'1'1p=@A8826A8871/13'1p=Qg00X7R9/771B13'1p=5A8813p=4%27=881/13p=H1797/11/13p=91113,17p=C%21=883p=S%>1=883p=R1793p=\1771,16/13p=P1113,17,16,12p=G1791/13p=T1713,17p=wA8871/13p=[1B13,17p=vg00XUR4g00Y3R:P6P7P1P3Eap=Og00YlR;Ay167Ax271P6f5R<P2P1P7Dc1027R=10<7R>';%3>,N=%2=%2>1?=>9:=>D@P510<6R>f6R=/06R?';%3>%3?%2>%2?1?>?9:>?DQ1F=210=2R?#=R>g00ZeR@#DRA#JRB%DA#D#D#D#J'YRA75>%<?R>1B>A%E?f7R>/02RC,;?%3?%3C%2C16=216>2'45H?9:?CD@393CP310><f8RC/0<';10C=R<#3f9R?/0=R2#3%2<%221?<29:<2DQP510?>R2f:R</0>RD#3'N%2D1?2D9:2D5H21F<C10<CR2#=RD?5DA%<2RD1BDA%E2f;RD/0CRE,;2%32%3E%2E16<C16DC'45H29:2ED@393CP310D?f<RE/0?#3'N10E<R?f=R2/0<R<#21??<9:?<3HP5102DR<f>R?/0DRC#2'S1?<C9:<C1F?E10?ERC#=R<?5<A%<CR<1B<A%ECf?R</0ERF,;C%3C%3F%2F16?E16<E'45HC9:CFD@393CP310<2f@RF/02#2'S10F?R2fARC/0?R?1?2?3:P510C<R?fBR2/0<RE#>'R1??E1F2F102FRE#=R??5?A%<ER?1B?A%EEfCR?/0FRG,;E%3E%3G%2G162F16?F'45HE9:EGD@393CP310?CfDRG/0C#>'R10G2fERE/02'?PGfFRFPEP2P?PFPGP?PCC`PFPGP?PCC_F^10E?RC#=R21B2A%<CRC?5CA39P510FGRG#=R5?55A%<GRG?5GAfGRG/FE10GER5#=RC?5CA%<5RC1BCA%E5fHRC/0ER2,;5%35%32%2216GE16CE'45H59:52D@393CP310CF#=R2?52AfIR2/0G#<R5?55AfKR5P2PCPFC]105C#EP8fLRF/02RE#3RHfJRI,FFRJ10FIRK#=RL?5LARL%<KRM?5MARM%\3RNP3%I@RO#I#I#IRP#JRQ%2KRR%J@RS,7R%>KRT%IP#JRP,7T%KKRU%DO#I#D#D#J,YBRB75URU39RO39CPfMRV/0IRW,;KRK%3WRX,43%>WRY,4TRT%2WRW,4R16FI16VI'4RRDGDGX08P8%2ERZPJPLPM17XQ,TXR[AwN3S;COPK14XXROPT143WPRDGDGX08P8%>ERTPJPLPM17WS,TWR\PNP3PPPUCP5C[PKPOP3PYA[WWRRRD@DGX08P8%KERUPJPLPM17YPAvN3B59Y9C[\PKPOPYPYPRD@DGX081F52RR1052RO#=RK?5KARK%<OR\?5\AR\17HQ17ZS17TPA5UUB59T59Z59HRU1;OERE14HHRB14TTRP14ZZRS165216F2'4RQ'1RA'1R['1RN'1RM'1RL'1RJ'1PFP5P2PIPFP5PCCuPFPIP2PGCtDsPKPJP7P\PLP1PUPMP3PEPNP?PBP[g00[JR[#r%q[1p81%o8%n8R[g00\6g00\URBPBg00]5RBP81m8@R@g00]UP@Clg00^<Fk1i[BP3P7g00^\RBg00_<R['W1h37=8B[dAg891CfbBbCbDX48R[1433^48RBP3PXO1b2PPPAP[PBP3PYO1b2PSPQP[PBP3PWO1b2P4g00_\RWg00`5RBP:CeR[%MFRSg00`SRYP:P8P[P4PWPBP:CjRBAX48IRWP3CO%d3RAAV485'ZRPP9n10110100021010000PYP:P8P[PBPW%MVCOPPP9n10110100021010000'4X3[PYP:P8P[PBAX482PSCOAV48I,ZAP9n10110100021010000,W8%M5PIPFP5PCCbELPQeCACACACACACACACA%KOP=EL%>OR=P>EL%2OR>PDEL%3ORDP<ELPRPKP\%EOPE14DHP=PTA[>ZQD@DGeb>W@W?P1P3O2n2001000000121000000bEW<W;P1P3O2n2001000000121000000W1W:P1P3O2n2001000000121000000W1W9P1P3O2n2001000000121000000W1W8P1P3O2n2001000000121000000bFW=WAX30X58X7;X6;P6P7P1P3O4X30X58X7;W6o"). Qed.

Lemma ta_fp_stack st lo sp a : lo <= a < sp -> ta_fp st lo sp a.
Proof.
ltac2:(KReplay.run1 (kr_t_ASlot_W9 ()) ["CANSEC1"] "h01ah12loh22sph32sth41bh52ghh61qp;2p;1p;4p;6p;3g00EJj24Tg00=cj23Tg00F_j21Tg00Dej12Tg00;Kj10Tg00<0j16Tg00Tlj27Tg009Tj2=Tg00??j28Tg00a5j25Tg00`Sj1<Tg00aOj4;Tg00amj6:Tg00Qmj4DTg002:j4CTg00bNj1BTg002ej6ATg00cGj2@Tg00PBj3?Tg00cij29Tg00dCj3>Tg00YlR0g00WYR1f2R2f0R3'4f1R4,33'1f3R5/441342'1g00d]R6/44g00ZeR7#2#2#0#2#0#0#0#0#0#6,76,34'1g0000R6f5R8/=31883R8/42%07R7#2#0#0#0#6,78,32'1'1X66'5g00eVR8%<8P6P8P6g00XUR9g00_\R:P1g00fMR;C;R<P9P:g00`5P1P;g00ffE:R;P8CDP6P<P;P8CCP4f6R;#BEA1@833?18;4R;/45%07#2#6,7;,35'1'1X58'5X46,56'9'9;>3UX01X21X11X30P5P2P4P3O4X01X21W1W3o"). Qed.
Lemma ta_fp_ctx st lo sp a : CTX <= a < CTX + 928 -> ta_fp st lo sp a.
Proof.
ltac2:(KReplay.run1 (kr_t_ASlot_W9 ()) ["CANSEC1"] "h01ah12loh22sph32sth41bh52ghh61qp;2p;1p;4p;6p;3g00EJj24Tg00Dej13Tg00;Kj10Tg00<0j15Tg00Tlj27Tg00=cj22Tg00F_j21Tg009Tj2=Tg00??j28Tg00a5j26Tg00`Sj1<Tg00aOj4;Tg00amj6:Tg00Qmj4ETg002:j4DTg00bNj1CTg002ej6ATg00cGj2@Tg00PBj3?Tg00cij29Tg00dCj3>Tg00gDj3BTg00YlR0g00WYR1g00d]R2f0R3'4g00ZeR4#3#3#0#3#0#0#0#0#0#5,72R5,23'1f3R6f1R7'4f2R8,27'114271275'1R5g0000R2f5R9/=31893R9/48%04R4#3#0#0#0#5,79,28'1'1X62'6g00eVR9%<9P2P9P2g00XUR:g00_\R;P1g00fMR<C;R=P:P;g00`5P1P<g00ffE:R<P9CEP2P=P<P9CDP7f6R<#CEA1@933?18<7R</46%04#3#5,7<,26'1'1X59'6X42,62'9R2'9A>5233BUX01X21X11X30P6P8P7P3O4X01X21W1W3o"). Qed.
Lemma ta_fp_meta st lo sp a q : meta_slot st q -> conc st q <= a < conc st q + 40 -> ta_fp st lo sp a.
Proof.
ltac2:(KReplay.run1 (kr_t_ASlot_W9 ()) ["CANSEC1"] "h01qh11ah22loh32sph42sth51bh62ghp;2p;1p;4p;6p;3g009Tj29Tg00??j26Tg00EJj23Tg00;Kj10Tg00Dej15Tg00<0j18Tg00Tlj24Tg00=cj22Tg00F_j21Tg00a5j27Tg00`Sj1>Tg00aOj4=Tg00amj6<Tg00Qmj4GTg002:j4FTg00bNj1ETg002ej6DTg00cGj2CTg00PBj3BTg00cij2;Tg00VHj4@Tg00g^j4ATg00dCj3?Tg00gDj3:Tg00YlR0g00WYR1g0000R2f4R3f0R4'9f5R5f1R6'6R7f2R8'3g00ZeR9#0R:#5#0#0#0#8R;,47,28'1f3R7,351273'1g00d]R</37%59#5#0#5#0#0#0#0#0#8,4<,27'1R<f7R9/941694R9/33149;,23'1'1X02R9,72R=g00eVR>%>>P2P>P2g00XUR?g00_\R@P1g00fMRAC=RBP?P@g00`5P1PAg00ffE<RAP>CGP2PBPAP>CFP6f8RA#EED1C>43B16A6RA/35%0:#5#8,4A,25'1'1X6>'7X52,72R>';R5';P2P9P8f6R9/981698R9/37149;,27'1P6P4C@CA9?=>9:<53:UUX02X11X31X21X40P3P7P8P6P4O5W0X11X31W2W4o"). Qed.
Lemma ta_fp_grp st lo sp a b gh : (s_groups st) !! b = Some gh -> conc st b <= a < conc st b + 9 -> ta_fp st lo sp a.
Proof.
ltac2:(KReplay.run1 (kr_t_ASlot_W9 ()) ["CANSEC1"] "h02ghh11bh21ah32loh42sph52sth61qp;1p;4p;6p;2p;3g00`Sj1GTg00aOj4FTg00amj6BTg00Qmj4@Tg002:j4ETg00bNj17Tg00cGj2?Tg00PBj38Tg00??j25Tg00EJj23Tg00;Kj10Tg00Dej16Tg00<0j1<Tg00Tlj24Tg00=cj22Tg00F_j21Tg009Tj2DTg00a5j2;Tg00cij2>Tg00VHj4CTg00g^j4=Tg00gDj3:Tg002ej6ATg0000R0g00eVR1f3R2f2R3f1R4f0R5EAp=9g00YlR6g00WYR7%G1R8P0g00XUR9g00_\R:P7g00fMR;CFR<P9P:g00`5P7P;g00ffEBR;P1C@R:P0P<P;P1CER;P4f5R<#7C91?15R938f6R=/53R>/32g00ZeR?#0R@#0#6#<RA,4>,22'1f4R>,3=12><'1g00d]RB/3>%6?#6#0#6#0#0#0#0#0#<,4B,2>'1RBf8R?/D515?5RC/3<%6@#0#0#0#<,4C,2<'1'1X60,;0RCP:P;P4f9R@#7C9=88915@4R@/3=14@A,2='1'1X01,;1X10R=,;0R@'>RD'>P0P=P2P1P:P;P>%7?C9=88915?>R?/3<14?A,2<'1'1X01P3P:P;P2f7R;#7C91?1358815;2R;/3>14;A,2>'1P4P5CCC=C=9:C@9:BD3:UUX01X10X27X47X37X56P<P>P2P3P4P5O6X01X10X27X47W3W5o"). Qed.

(* [comment removed for export] *)
Lemma disjoint_high W A n : (forall lo hi, In (lo, hi) W -> hi <= ATOP) -> ATOP <= A -> disjoint_from W A n.
Proof.
ltac2:(KReplay.run1 (kr_t_ASlot_W9 ()) ["CANSEC1"] "p'0h02hih12loh21Wh31Ah42HAh52HWh64__p1h74__x1h84__x2h94__x3h:1nh;1Hh<2H0h=3Hinh>2IHh?7__arithh@4__ffhA8__varmaphB5__withC1ahD3hi'hE1lhF3lo'i001pi011zp;2p;1p;3p;4p;6p;7p;5p;8g00h8R0j2bTg00Jaj1JTg00hXj34Tg00hoj1aTg00EJj21Tg00iej33Tg00JAj1DTg00jaj3=Tg00Tlj2?Tg00cij2@Tg00PBj3<Tg00O<j2HTg00dCj3`Tg00kAj1VTg00;Kj10Tg00<0j1ETg00Dej12Tg00F_j2QTg00l?j1CTg00l^j29Tg00mGj3BTg00n0j2PTg00KAj2ATg00n\j1OTg00o:j48Tg00K_j1NTg00L=j1MTg00Lhj2:Tg00oXj1LTg010:j6KTg010^j7RTg00NZj2_Tg00OVj2^Tg00P\j3]Tg00Q;j4WTg00gDj3XTg00VHj4YTg011Bj5ZTg011dj4[Tg00MKj4\Tg00N6j7TTg012Dj8STg00WYR1P1f1R2f0R3C[p=6%23#2p=U%23#2#2#2p=5%03#0p=G%03#0#0#0p=F%03#0#0#0#0#0#0#0p=7P1P2g012hP3C\p=;P2g00\6R4g00\UR5P5g00]5R6P3g00^<FTp=>f3R7P4P5P5P6f2R8P2P3GSp=I1b11R9#JR:P91623R;=498p,2rcR<#aR=,12R>[^01^11R?11=7f4R@=387[[X2:%D9RA949;P>[^01^1111=8g013OA3A78eW4W5P0P1P1f5R0,1=f6RA=380[\?A=9@7RB949;P>[^01^1111=Af7RC=3BA[[[^E:P3f8RB,1=f9RD=38B[\?160@R?==97RE949;P>[^01^1111=Df:R>/?D/1011@>'@A37>DP2P0P@A<9??A49?71H9?3`O311@=%V<g00ZeR<#U#5#5#5R?#0#5#5#0#G#F#7#7#E/1=%2?#5#5#0#G#F#7#7#E,1='Qp-0R?g00[JRFg013kRG#CRH#C,91191H191G5B15B1g014J'P%DF3=%JFP1P11A18P7%O1RFC8P2P11A17P7PFC8C8%N1%M1RF%0<RG#0,:1RH%2G,:1RG';,>F%L5RIPF1:1<R<,;G,>FPIPFP4P5P5P6PFP4P5P5P6P0EK1;H<,>FFRCICI1_F6P3P8g00^\RFg00_<R6'H1^38=<F6dg00X7=]12CWb@bAbBX71X81X91W6112811721178,@0[[^71^81^91^6?P3f=R?f<'?/1BP=PCP?P8P7O6b?b<b;P8A49;0P@P8P216BC1682RB5<9A49BA;X3O3W=XD1XF1P3O2CYA3E>DeW4W5W>X2:X01X11P2P3O2n2001100000121101101XC9P8DZX:1X31X2:P8P2P3O3X:1X31W2o"). Qed.


(* [comment removed for export] *)
Lemma decay_cases c st : decay_bounces c st = st \/ exists v, decay_bounces c st = set_bounce (c - 7) v st.
Proof.
ltac2:(KReplay.run1 (kr_t_ASlot_W9 ()) ["CANSEC1"] "p'0h01vh11ch22sth31bi001bp;1p;2p;3p;4g0156j1ATg00Dej19Tg00<0j16Tg0166j21Tg016Sj23Tg017Kj2<Tg017hj1;Tg018Fj2:Tg018dj32Tg00a5j24Tg00cij25Tg00O<j28Tg00g^j4@Tg00gDj3?Tg00dCj3>Tg019_j27Tg00PBj3=Tg00YlR0f1R1f0R23=p=0g00WYR3%A1g00ZeR4#9#9#6R5,11,32g00X7'<#;':g00^\R6P6P6P0P2f3R7/15R8f2R9/38%64R4'1;29R:P9n0100000020000/09P6P0P1f4/15R61376/14;27P7n0100000020000A2627'0X03,43'5P21195R51315/14R4;21R6/01A2829R8,0:X03R:,43P3P:P41806C@3?10111098X03,4318013>n0110000020000b31712/021791A2521'0X03,43'5eX20X13P1P2O2X20W1o"). Qed.
Lemma active_decay c st i : active (decay_bounces c st) i = active st i.
Proof.
ltac2:(KReplay.run1 (kr_t_ASlot_W9 ()) ["CANSEC1"] "p'0h01vh11Hh21ch31ih41mh52sth61oi001xp;2p;1p;3p;6g01:]j2<Tg019_j22Tg00Dej17Tg00<0j1;Tg0166j24Tg018dj33Tg00a5R0j26Tg00ciR1j2:Tg01;]j20Tg00PBj35Tg00O<j28Tg001Cj69Tg00YlR2f1R3f0R435p=1g00WYR5f2R6/<31263/13f3R7/26R8g00Ze#7#7#;R9,47?346'1X05,65':P11186f4R8/27R11489?347'1X05,65g0039R:1016107635P41117P2P81048f5R1/08R;55:X421087,8:1218R7P4E9W1P4O11419?348,17X05,65P0P5f6R0/21R71409?341'1X051078=5:;P4f8R;f7R7'214;9?347'1P2f9R8/49?33;104;108;55:X4210;7,8:128;P4E9W1X05P3P4O2n2001000000120100000W1P4O1n200100000021000010000b6X35X52X25P6P3P4O3X35X52W2o"). Qed.
Lemma rec_decay c st q : get_meta_rec (decay_bounces c st) q = get_meta_rec st q.
Proof.
ltac2:(KReplay.run1 (kr_t_ASlot_W9 ()) ["CANSEC1"] "p'0h01vh11Hh21ch31mh41qh52sth61oi001xp;2p;1p;3p;6g01:]j2<Tg019_j22Tg00Dej17Tg00<0j1;Tg0166j24Tg018dj33Tg00a5R0j26Tg00ciR1j2:Tg006aj20Tg00PBj35Tg00O<j28Tg001Cj69Tg00YlR2f1R3f0R435p=1g00WYR5g0000R6f2R7/<31273/13f3R8/27R9g00Ze#7#7#;R:,48?347'1X05,65':P11197f4R9/28R1149:?348'1X05,65g01<TR;1017108735P41118P2P91049f5R1/09R<55;X321098,8;1219R8P4E9W1P4O1141:?349,18X05,65P0P5f6R0/21R8140:?341'1X051089=5;<P4f8R<f7R8'214<:?348'1P2f9R9/4:?33<104<109<55;X3210<8,8;129<P4E9W1X05P3P4O2n2001000000120100000W1P4O1n200100000021000010000b6X46X52X25P7P3P4O3W4X52W2o"). Qed.
Lemma active_upd_meta g f st i : active (upd_meta g f st) i = active st i.
Proof.
ltac2:(KReplay.run1 (kr_t_ASlot_W9 ()) ["CANSEC1"] "h01fh11gh21ih32stp;2g01;]j21Tg00O<j20Tg0000R0g01<TR1P1[R1g00YlR2g00WYR3g0039f1R4f0R5'1'0X23X32X01X10f3f2P4P5O4W2W3W0W1o"). Qed.

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
Hypothesis CLO : ATOP <= lo.
Hypothesis LO : lo <= bv_unsigned sp - 96.
Let spv := bv_unsigned sp.

(* [comment removed for export] *)
Definition nclosed (stX : mstate) (P : aptr -> Prop) : Prop :=
  forall q, P q -> gmf st sc q /\ exists t, m_next (get_meta_rec stX q) = Some t /\ P t.
End PHASE.


End CANSEC1.
