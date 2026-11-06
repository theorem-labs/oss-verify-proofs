(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase State.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.Common Require Import LiaRel.
Local Ltac Stdlib.micromega.Lia.lia ::= lia_rel.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.Common.Lib Require NoCache.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib Require KReplay.
Ltac2 kr_t_PlacementSearch () := "C46Stdlib5Lists4List2hdC47Corelib5Lists7ListDef3mapC47Corelib4Init9Datatypes3fstC56Stdlib6ZArith6BinInt1Z3addK47Corelib7Numbers7BinNums1Z02C56Stdlib6ZArith6BinInt1Z3subC56Stdlib6ZArith6BinInt1Z3divC46Stdlib6ZArith4Zdiv:Z_mod_multC4ELinuxProcessSemantics?LinuxProcessSem5State?page_round_up_ZC56Stdlib6ZArith6BinInt1Z6moduloI47Corelib4Init5Logic2eq00I47Corelib7Numbers7BinNums1Z00C4ELinuxProcessSemantics?LinuxProcessSem5State9page_sizeK47Corelib7Numbers7BinNums8positive03K47Corelib7Numbers7BinNums1Z01K47Corelib7Numbers7BinNums8positive02K47Corelib4Init9Datatypes4list01I47Corelib4Init9Datatypes4list00K46Stdlib9micromega6VarMap1t01I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr01K46Stdlib9micromega=RingMicromega7Formula01K46Stdlib9micromega5Tauto8GFormula07C46Stdlib9micromega5Tauto8BFormulaK47Corelib4Init5Logic2eq01C46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundC56Stdlib6ZArith6BinInt1Z7div_modC56Stdlib6ZArith6BinInt1Z3mulC56Stdlib6ZArith6BinInt1Z2ltC56Stdlib6ZArith6BinInt1Z=mod_pos_boundI47Corelib4Init5Logic3and00C46Stdlib9micromega9SatDivModCZ_mod_nonneg_nonnegC46Stdlib9micromega9SatDivModCZ_div_nonneg_nonnegC47Corelib4Init5Logic3notC56Stdlib6ZArith6BinInt1Z=mod_neg_boundC56Stdlib6ZArith6BinInt1Z2leC56Stdlib5omega8PreOmega1Z;div_0_r_extC56Stdlib5omega8PreOmega1Z;mod_0_r_extK47Corelib4Init9Datatypes3nat02K46Stdlib9micromega=RingMicromega5Psatz02K46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega:ZMicromega;ZArithProof02K47Corelib4Init9Datatypes4list02K46Stdlib9micromega6VarMap1t02K46Stdlib9micromega6VarMap1t03K47Corelib4Init9Datatypes6option02K46Stdlib9micromega5Tauto8GFormula03K47Corelib7Numbers7BinNums8positive01K46Stdlib9micromega7EnvRing5PExpr02K46Stdlib9micromega5Tauto8GFormula05K46Stdlib9micromega7EnvRing5PExpr03K46Stdlib9micromega7EnvRing5PExpr04K46Stdlib9micromega7EnvRing5PExpr05K46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega5Tauto8GFormula08C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K47Corelib4Init9Datatypes4unit01I46Stdlib9micromega:ZMicromega;ZArithProof00K46Stdlib9micromega=RingMicromega3Op201I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01I47Corelib4Init5Logic5False00K46Stdlib9micromega=RingMicromega3Op205K47Corelib4Init9Datatypes3nat01K46Stdlib9micromega:ZMicromega;ZArithProof01K46Stdlib9micromega=RingMicromega3Op203C56Stdlib6ZArith6BinInt1ZBdiv_lt_upper_boundC56Stdlib6ZArith6BinInt1ZDmul_le_mono_nonneg_rK47Corelib7Numbers7BinNums1Z03K46Stdlib9micromega7EnvRing3Pol01K46Stdlib9micromega=RingMicromega5Psatz04C56Stdlib6ZArith6BinInt1Z8le_transC56Stdlib6ZArith6BinInt1Z3maxC56Stdlib6ZArith6BinInt1Z8max_specI47Corelib4Init5Logic2or00K46Stdlib9micromega5Tauto8GFormula06C47Corelib4Init9Datatypes8list_indC46Stdlib5Lists4List9fold_leftC46Stdlib5Lists4List2InC47Corelib4Init5Logic9False_indc59OSSVerify5KrLib6Common?PlacementSearch@fold_max_ge_seedC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic8eq_ind_rK47Corelib4Init5Logic2or01K47Corelib4Init5Logic2or02K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00I47Corelib4Init9Datatypes4prod00C45stdpp9bitvector;definitions7Z_to_bvC4ELinuxProcessSemantics?LinuxProcessSem5State;region_freeC45stdpp9bitvector;definitions:bv_modulusC45stdpp9bitvector;definitions7bv_wrapC45stdpp9bitvector;definitions=bv_wrap_smallC45stdpp9bitvector;definitions;bv_unsignedC45stdpp9bitvector;definitions@Z_to_bv_unsignedC56Stdlib6ZArith6BinInt1Z3lebc59OSSVerify5KrLib6Common?PlacementSearch>fit_candidatesC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List6filterC46Stdlib5Lists4List9filter_InC47Corelib4Init5Logic3iffC56Stdlib6ZArith6BinInt1Z6leb_lec59OSSVerify5KrLib6Common?PlacementSearch;fold_max_leC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib6Common?PlacementSearchCfold_max_in_or_seedC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes3sndC47Corelib4Init5Logic5proj1C56Stdlib6ZArith6BinInt1Z7add_modC47Corelib4Init5Logic6eq_indI47Corelib4Init5Logic2ex00C46Stdlib5Lists4List:in_map_iffc59OSSVerify5KrLib6Common?PlacementSearchGpage_round_up_Z_alignedC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes4prod01C4ELinuxProcessSemantics?LinuxProcessSem5State>region_free_InC4ELinuxProcessSemantics?LinuxProcessSem5State:iv_overlapC56Stdlib6ZArith6BinInt1Z3ltbC46Stdlib4Bool4Bool>andb_false_iffC56Stdlib6ZArith6BinInt1Z;le_gt_casesK47Corelib4Init5Logic3and01K47Corelib4Init5Logic2ex01c59OSSVerify5KrLib6Common?PlacementSearchBpage_round_up_Z_leC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib6Common?PlacementSearch>fold_max_ge_inC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib6Common?PlacementSearchBpage_round_up_Z_geC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z6ltb_geC56Stdlib6ZArith6BinInt1Z7le_reflC56Stdlib6ZArith6BinInt1Z;add_le_monoC4ELinuxProcessSemantics?LinuxProcessSem5StateAregion_free_introC46Stdlib5Lists4List7existsbC46Stdlib5Lists4List>existsb_existsC56Stdlib6ZArith6BinInt1Z3eqbC47Corelib4Init9Datatypes4andbC47Corelib4Init5Logic5proj2C56Stdlib6ZArith6BinInt1Z6eqb_eqc59OSSVerify5KrLib6Common?PlacementSearch<higher_fit_bC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes4bool02C4ELinuxProcessSemantics?LinuxProcessSem5State:two_pow_64C46Stdlib5Lists4List8map_consC46Stdlib4Bool4Bool=andb_true_iffc59OSSVerify5KrLib6Common?PlacementSearch=no_higher_fitC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib6Common?PlacementSearchEhigher_fit_b_completeC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib6Common?PlacementSearchBhigher_fit_b_soundC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic4True00K47Corelib4Init5Logic4True01I47Corelib4Init9Datatypes6option00c59OSSVerify5KrLib6Common?PlacementSearch5placeC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes6option01c59OSSVerify5KrLib6Common?PlacementSearch:place_fitsC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib6Common?PlacementSearchAsearch_candidatesC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List9find_someC46Stdlib5Lists4List4findC47Corelib4Init9Datatypes3orbC46Stdlib6ZArith4Zdiv:Zminus_modc59OSSVerify5KrLib6Common?PlacementSearchEhigher_fit_b_as_placeC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib6Common?PlacementSearch<existsb_findC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib6Common?PlacementSearch>place_in_modelC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem5State9alloc_topc59OSSVerify5KrLib6Common?PlacementSearch;place_soundC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem5State<alloc_top_ltC56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z3powC56Stdlib6ZArith6BinInt1Z:pow_nonnegK46Stdlib9micromega7EnvRing5PExpr07C56Stdlib6ZArith6BinInt1Z4of_NC4ELinuxProcessSemantics?LinuxProcessSem5State;vm_reservedC4ELinuxProcessSemantics?LinuxProcessSem5State7vm_mapsC47Corelib4Init9Datatypes3appI4ELinuxProcessSemantics?LinuxProcessSem5State6VmMaps00C45stdpp9bitvector;definitions4BvWfK45stdpp9bitvector;definitions2bv01C4ELinuxProcessSemantics?LinuxProcessSem5State8mkVmMapsc59OSSVerify5KrLib6Common?PlacementSearch>place_completeC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib6Common?PlacementSearch>witness_ledgerC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib6Common?PlacementSearch8demo_topC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem5StateBalloc_top_mkVmMapsI47Corelib4Init9Datatypes:comparison00K47Corelib4Init9Datatypes:comparison02c59OSSVerify5KrLib6Common?PlacementSearch;full_ledgerC1?~~~~~~~~~~~~~~~".   (* [comment removed for export] *)
Import ListNotations.
Open Scope bv_scope.

(* [comment removed for export] *)
Definition no_higher_fit (maps : list (word * word)) (aZ nZ baseZ : Z)
    : Prop :=
  forall g : Z,
    (g mod page_size = 0)%Z ->
    (aZ + nZ <= g)%Z ->
    (g + nZ <= baseZ)%Z ->
    region_free maps (Z_to_bv 64 g) (Z_to_bv 64 nZ) = false.

(* [comment removed for export] *)
Definition fit_candidates (maps : list (word * word)) (aZ nZ : Z)
    : list Z :=
  (aZ + nZ)%Z
    :: map (fun p => page_round_up_Z (bv_unsigned (fst p)
                                      + bv_unsigned (snd p))%Z)
           maps.

Definition higher_fit_b (maps : list (word * word)) (aZ nZ baseZ : Z)
    : bool :=
  existsb (fun g => (g mod page_size =? 0)%Z
                    && (aZ + nZ <=? g)%Z && (g + nZ <=? baseZ)%Z
                    && region_free maps (Z_to_bv 64 g) (Z_to_bv 64 nZ))
          (fit_candidates maps aZ nZ).

Lemma page_round_up_Z_aligned : forall z,
  (page_round_up_Z z mod page_size = 0)%Z.
Proof.
ltac2:(KReplay.run1 (kr_t_PlacementSearch ()) [] "h01zp;2p;1p;3p-1R0p10000p4p710p8P0p1000Gp4p710p8P0p1000cR1p4p710p8P0P1p4p7210p8g001@j27Tg001]j16Tg002;j20Tg002Xj21Tg0035j25Tg003Uj12Tg004Sj23Tg0053j34Tg005MR1f0R0g005kR2'7g006c#6'0/12/52%20/32g007H541eW0o"). Qed.

Lemma page_round_up_Z_ge : forall z, (z <= page_round_up_Z z)%Z.
Proof.
ltac2:(KReplay.run1 (kr_t_PlacementSearch ()) [] "h07__arithh14__ffh28__varmaph35__with42H0h54__p1h64__x1h74__x2h84__x3h91Hh:2H1h;2H2h<2H3h=2H4h>6__sat0h?6__sat1h@1qhA1rhB1zp;1p;2p;4p;6p;3p;7p;8g007fj1=Tg001]j1BTg008Kj1hTg008kj1YTg009Kj1UTg009ij1STg00:Gj1RTg00;2j2?Tg00;Uj45Tg00<@j6HTg00<dj2gTg00=Fj2`Tg00=`j2[Tg0053j33Tg00>Lj3WTg00>kj4VTg00?]j3Tj2LTg002Xj2<Tg00@>j29Tg004Sj21Tg001@j2;Tg00@[j24Tg00A7j3Qj2JTg00A^j2:Tg00B9j2OTg00Bjj2NTg00C[j1KTg00D4j2MTg00D[j28Tg00E7j2ITg00E]j2PTg00FCj1ETg00Fbj2@Tg00GKj3CTg00H4j2fTg00H`j3eTg00I@j2GTg00I^j4_Tg00J<j1^Tg00J^j6]Tg00KBj1ZTg00Kgj2ATg00LJj7\Tg00Lnj3DTg00MQj3XTg00N4j3FTg003Uj1aTg002;j2bTg00NWj7cTg00O;j8dTf0R0#=#=p=7f2R1f1R2';/b0p=0P2g00O_R3g00P>R4P4g00P^R5P0g00Q>Fcp=6g007HR6/80p=2f3R7P3P4P4P5P1P2P0Gdp=>g005MR8g006cR9#=R:#=#7#7#7#7#7#BR;%B9R<500R=g00Q^R>#hR?%Y>R@%U8RA%S8RB%R8RCP3P4P4P5P81?8;RDg00RJRE1?86RFC5,6CEHRG1gC5RHP0P1g00S1RIg00SQRJ'`1[01=3IJdAW862CVRJb1b2b3A38;6RIg00T1[RKP0b07T;1<=;,9;11=;';938=A02;<R=P?P@PAPBP8PFg00TNRFPDC5,6CRAPHPJb1b2b3146;RLP0b07Q;11=;R=#214=;':A01;<R=/O;%2=%2;RMf4RN?0;<RO/1;#2[[A07;<RP/N;%2Pf5RP?0;<RQ/<;RR#2\M[1LO;%KI19;R11Q;';938Q[1JQ;f6RQ?0;<RR/1;RO#214O;':\L1MR;14;6f7RR?0;<RO/1;RM,4;18M6':[1IO;f8?0;<RO/<;=386\I1PO;f9?0;<RO/1;=38O\I1<O;P8f:?0;</1;P8p-0ROg00U5RI#ER6#E,@81@861@8I5C85C8g00UT'f=e>?P@P81G81P21G87C_PBPCPCPA%^4RAPCP3P4P4P5PCP3P4P4P5PPE]P8%Z9,A8RPPFPDC5,6CF\C>PAPCPCPGPAP81A89R9=D8D1?8<5X8PE1A8:R:9F8D=D8PC5,6CC>PAP8P9g00V@AF8:DC5,6CC>C>PHPJb1b2b3X68X78X88W5147;,:N\L19;7/;N938=\K197;,81[[^68^78^88^5OP0%22P2P1f<PQPRO6b0bAb@b=b<b;b:b4b>b?b4b9%a0,80eWBo"). Qed.

(* [comment removed for export] *)
Lemma page_round_up_Z_le : forall z b,
  (z <= b)%Z -> (b mod page_size = 0)%Z -> (page_round_up_Z z <= b)%Z.
Proof.
ltac2:(KReplay.run1 (kr_t_PlacementSearch ()) [] "h07__arithh14__ffh28__varmaph35__with44__x1h54__x2h64__x3h71Hh82H0h92H1h:2H2h;2H3h<6__sat0h=6__sat1h>1qh?1rh@2H4hA2H5hB2H6hC2H7hD2H8hE4__p1hF6__sat2hG4__x4hH2q0hI2r0hJ2HbhK3HbmhL2HqhM3HzbhN1bhO1zp;2p;1p;6p;3p;4p;5p;7p;8g00D[j29Tg004Sj20Tg007fj1FTg001]j1TTg008Kj1_Tg008kj1[Tg009Kj1ZTg009ij1YTg00:Gj1XTg00;2j2MTg00<@j6rTg00<dj2qTg00=Fj2dTg00=`j2cTg0053j3RTg00>Lj3^Tg00>kj4]Tg00?]j3\j2BTg002Xj21Tg00@>j27Tg001@j2:Tg00@[j23Tg00B9j2STg00Bjj2NTg00C[j1WTg00A7j2ETg00A^j28Tg00D4j2?Tg00E7j2DTg00E]j2CTg00FCj1LTg00Fbj2JTg00GKj3=Tg00H4j2VTg00H`j3UTg00I@j2QTg00I^j4@Tg00J<j1pTg00KBj1oTg00Kgj2GTg00N4j3ITg00Lnj3HTg00MQj3bTg00Vgj5aTg00WSj5`Tg00XAj1eTg00X_j2fTg00Y@j3gTg00J^j6hTg00LJj7iTg00Yij5jTg003Uj1kTg00;Uj4PTg00NWj7lTg002;j2mTg00O;j8nTg005MR0f0R1g007HR23Rp=<%F1#Fp=>P0f1R3g00RJP1CPp=KP3g00O_R4g00P>R5P5g00P^R6P1g00Q>Flp=5AR031p=6f2R7/:3/m1p=2P0P3g00TNP1CPp=O1921p=4f3R8P4P5P5P6P7P3P1Gnp=;P0P3g00V@P1CPp=A1931g005k,03#<g006cR9#FR:#FR;#>#>#>#>#>#TR<g00Q^R=#_R>%[=R?%Z0R@%Y0RA%X0RBP4P5P5P61M0<RC1M02RD'K,5BErRE1qB6RFP1P7g00S1RGg00SQRH'd1c17=RGHdA^023C]RHb1b2b3%<<RGg00T1[RIP1b05\7117<,7<107<':,67f4RJ%T9RK72<RLP<118</:KRMP>P?P@PA1ODC,5BRNPFPHb1b2b3132<ROP1b01S8<%48RP%4<RQf5RR/0<#4[[1NJ<%4JRSf6RT/1<RU#4\Q[1BR<%WGRV17<U10T<RU':,6T[1ET<f7RT/0<RW#413W<'8\O1?T<13<2RWf8RX/0<RY,3<19Y2'8[1DX<f9RZ/1<#<\G1CZ<f:R[/0<R\/6[\G11[<P0f;R]/0<P0g00U5R^#LR_#LR`#L,J01J0`R`1J0_R_1J0^R^5=05=05=0g00UTRa'V=U=>P?P0P01Q0JP7P@C@P31Q08RbC@PAPBPBPE%p5Rc%o9,G0Rd1G0:R:9I0C1G0;R;5H0'K,5BC;PcPB1K;D,5BPcPB1G09Re/Ad,5BPcAH0eC1M0KRd5b0AH0:dRd9I0C'O,5BC;C;C;PFPHb1b2b3X40X50X60XG017<7/:J,68\IRI%<J197JA28<K1:JK,7<'3[[[^40^50^60^G0P1P3f=RfP7f>RgPTP]f<RhO7b0b?b>b;b:b9b8b7b<b=Da11L</3MA2R<K/1<RM/7<11J<RL/7<PJPMPLP<P>P?P@PA1ADC,5BPFPHb1b2b3PQP1b01SJ<RL%4U\Q\SRS1NR<RU%4R11T<#4\Q[RMA2T<KRi/N<Rj%4iA2Z<KRi/1<Rk#4\Q[RQA2X<K/B<17<k10i<':,6i\V1Ei<A2[<KRi/0<Rk#413k<'8\O1?i<A2]<KRi/0<Rk,3<19k2'8\W1Di<A2h<KRi/1<#<\G1Ci<A2f<KRi/0</6i\G11i<P0A2g<K/0<P01Bg<f?Ri11i<,7<10i<':'6\V1Ei<f@Rk/0<Rl#413l<'8\O1?k<fARl/0<Rm,3<19m2'8\W1Dl<fBRm/1<#<\G1Cm<fCRn/0</6n\G11n<P0fDRo/0<P0P>P?P01Q07P3P@C@PAPB1Oed,5BPc1Ae:,5BC;PFPHb1b2b3X40X501:3K,311937[^40^50P1P7PZPmO3b0bIbHbDbCbBbAb@b?b>b;b:b9b8b7b<b=bFD`PLPSPUPMPjPQ1BT<11X<,7</:Y,6X\V1EX<10Z<RY#413Y<'8\O1?Z<13<\19\2'8\W1D[<11]<#<\G1C]<10h</6h\G11h<P010f<P0A2i<K/B<A2k<KRk11k<,7<10k<':'6\V1Ek<A2l<KRl/0<Rk#413k<'8\O1?l<A2m<KRm/0<Rl,3<19l2'8\W1Dm<A2n<KRn/1<#<\G1Cn<A2o<KRo/0</6o\G11o<P0fE?2<K/0<P0p-0RK%e9,f0=g0_==0^9=0`/Va=U=>P?P0P0PbP7P@C@P3P@C@PAPBPBPNPcPBP4P5P5P61AD;,5BPBP4P5P5P6PREhFiC;PcPBPBPEPcAI0Ce=H0;,K:,5BC;PcAI0eC/A:,5BC;C;PFPHb1b2b3X40X50X60WE18PJ\O177</98\I[^40^50^60^EKP113X<PXfFPZPfPgO6b0bIbHbDbCbBbAb@b?b>b;b:b9b8b7b<b=bFDjbLbK%k8/97eWJWMXN0XO0o"). Qed.

Lemma fold_max_ge_seed : forall l s, (s <= fold_left Z.max l s)%Z.
Proof.
ltac2:(KReplay.run1 (kr_t_PlacementSearch ()) [] "h04__x1h11lh21sh37__arithh44__ffh54__p1h68__varmaph75__with84__x2h94__x3h:4__x4h;1Hh<2H0h=2IHh>1xh?2z0p;1p;2p;3p;4p;6p;7p;5p;8g008kj1FTg00D[j20Tg008Kj1ATg00I@j2=Tg009ij1UTg00:Gj1OTg00Kgj27Tg00<dj2JTg00=Fj2HTg00=`j2GTg0053j33Tg00>Lj3XTg00>kj4VTg00ZKR0j2<Tg00Zhj2TTg00@[j2BTg00A^j25Tg00[Jj2@Tg00XAj1NTg00X_j2MTg00FCj1;Tg00Fbj24Tg00Y@j3LTg00GKj38Tg00H4j2?Tg00H`j3:Tg009Kj1KTg00I^j4>Tg007fj1ETg00;Uj46Tg00KBj1ITg00J^j6PTg00[dj7QTg00J<j1RTg00\Hj5STg00\jj5[Tg00NWj7ZTg00LJj7YTg00O;j8WTg005MR1P1P0f1R0f0R2D[p=2P1P0g00V@P2C6p=9P0g00O_R3g00P>R4P4g00P^R5P2g00Q>FZp=1f2R6P3P4P4P5P0P2FYp=Cf3R7P3P4P4P5P6P0P2GWp=D%F1R8P11202,02^21R9X18g00Q^R:#AR;%F:R<1=10%U1R=%O1R>g006cR?,71R@/9@'11J>5RAP2P6g00S1RBg00SQRC'H1G26=3BCdg007H=X10CVRCb4b6b7X011022^01P2P0O1b3%A1/22,02eX21P01<27RBO1126B,0Bf4RB,T01B0B1<0BRD=31B'510B0A31D0'5'@f5,<6P1p-0RD%N?,M1g00U5RE#;RF#;RG,415L1141F141E581581REg00UTRF'?%;G,41=81E/?F=::;5::P<P1P11=1BP6%K1C>P01=17C>P=P>P>P3P4P4P5P1P@g00TN%E?R=#E,71R<C6,1>P1%I?,71R?g00RJR:P<C6,1>5C>P>P3P4P4P5f6R5EPP1P?P:P@C6,1>5C>FQ%R4R4P>171=R=,9?,1>P419@=,1>CDCDPAPCb4b6b7X01X81X91X:1W51B27A3167'5A3162,5B'@10761067[[^01^81^91^:1^5DP2f7RD/0BPDP01250PBP6P7O7b3b?b<b;A:176/22,02eX21X=9X18X>1P2DSW1o"). Qed.

Lemma fold_max_ge_in : forall l s x,
  In x l -> (x <= fold_left Z.max l s)%Z.
Proof.
ltac2:(KReplay.run1 (kr_t_PlacementSearch ()) [] "h03Hinh11lh21sh31xh41Hh54__p1h64__x1h74__x2h84__x3h94__x4h:1yh;2H0h<2IHh=7__arithh>4__ffh?8__varmaph@5__withA2z0p;1p;3p;2p;4p;6p;7p;5p;8g008kj1ETg00]Hj34Tg00D[j20Tg008Kj1DTg00]_j2XTg00H`j32Tg00ZKR0j29Tg00^>j2LTg00Zhj2KTg00@[j2@Tg00A^j28Tg00[JR1j2GTg00FCj1=Tg00Fbj26Tg00XAj1WTg00X_j2VTg00Y@j3UTg00GKj3<Tg00H4j2CTg00I@j2BTg009Kj1RTg00I^j4ATg009ij1QTg00:Gj1OTg00J^j6NTg00KBj1MTg00Kgj27Tg00;Uj4;Tg007fj1?Tg00[dj7JTg00J<j1PTg00<dj2ITg00=Fj2STg00=`j2TTg0053j3HTg00>Lj3`Tg00>kj4_Tg00_Jj6^Tg00\Hj5]Tg00\jj5\Tg00NWj7YTg00LJj7ZTg00O;j8[Tg005MR2P2P0f1R0f0R3D\p=1AH203p=3P0g00O_R4g00P>R5P5g00P^R6P3g00Q>FYp=5f2R7P4P5P5P6P0P3FZp=>P2P0g00V@P3C;p=:f3R8P4P5P5P6P7P0P3G[p=F%E2R9P2A42371187,00[^32^22R:X19%D2R;942311;7,00/X3W0X32X22f4R;=2289423P1f5R1/30A420;f6R<=221/18,07P313<7P2P8f7R=9223/11,0;X:219;8R>,L<11<>,0>1K1;1@1;191;R>/3;'810;113>1'8'G19<1P2p-0R>g00Q^R?g00U5R@#=RA#=RB#=,62g006cRC#W,V2162B5U2162A162@5<25<2R@5<2g00UTRA'C1C@A%D?52?32%E?P2P21B2;P7%R2CAP01B28CA%Q2%O2R?P?P4P5P5P6P?P4P5P5P6P<ENP2%MC,72R4g00RJRA172CR@C;,5?5>?%?CRC#?,72RB,:@,5?P2P4PAPBC;,5?5>?FJ%P5R5P?172CRC,:4,5?P51:@C,5?CFCF1I?6P3P7g00S1R?g00SQR6'S1T37=H?6dg007H=`20C_b>b?b@X62X72X82X92W51373,8;10381378'8'G10871078[[^62^72^82^92^5>P3f8R>/@=P>P0f:/10P=P7P8O7b=bAb;b4A228</1;,08eP=P3E^W4P3O1A4271P119;=P8P3O3A22=</1;,08eW0P3O1n200100000021100010000W0X32X22X<:X19X:2P3D]W1o"). Qed.

Lemma fold_max_le : forall l s b,
  (s <= b)%Z -> (forall x, In x l -> (x <= b)%Z) ->
  (fold_left Z.max l s <= b)%Z.
Proof.
ltac2:(KReplay.run1 (kr_t_PlacementSearch ()) [] "h01xh11bh21lh31sh42Hlh52Hsh64__p1h74__p2h84__x1h94__x2h:4__x3h;4__x4h<1Hh=2H0h>2Hxh?2IHh@7__arithhA4__ffhB8__varmaphC5__withD1yhE2z0p;1p;2p;3p;4p;7p;5p;6p;8g008kj1JTg00D[j20Tg008Kj1DTg00H`j3=Tg00ZKR0j2<Tg00=Fj2BTg00_hj3RTg00Zhj2NTg00@[j2@Tg00A^j27Tg00[Jj2ITg00FCj1>Tg00Fbj26Tg00GKj35Tg00H4j2HTg00I@j2GTg009Kj1WTg00I^j4ETg009ij1VTg00:Gj1STg00Kgj24Tg007fj1FTg00;Uj4:Tg00KBj1QTg00[dj7PTg00J<j1MTg00<dj2LTg00=`j2OTg0053j3?Tg00>Lj3KTg00>kj4TTg00`Bj3UTg00\Hj5^Tg00]Hj3]Tg00\jj5\Tg00J^j6[Tg00NWj7ZTg00LJj7YTg00O;j8XTg005MR1f1R2f0R33]p=2P1P1P0P2P3D\p=8A?123p=1P2g00O_R0g00P>R4P4g00P^R5P3E[p=CP2P0P4P4P5P3g00Q>FZp=3f2R6P0P4P4P5P2P3FYp=AP1P2g00V@P3C:p=;f3R7P0P4P4P5P6P2P3GXp=9%J1R8P11023R9f4R:,231027R;[^0118:7/06[[^11^31R<X28%D1R=,23P;[^01P218=7/06eW4X59X11X31f6R=f5R>5=1R?,23P;[^01P:1<7=P6P3P=11==12=>1B1=3RO210=6f7R;,N:1@:;1<:;R@/1;'710;:11@:'7'If8R@,<>P1p-0RAg00Q^RBg00U5RC#>RD#>RE#>,61RF161D161CRC551551g00UTRD'H161E=51C951F/HD%DB5=B3=%JBP1P11G1:P6%W1CEP21G17CE%V1%S1RBPBP0P4P4P51CB=P1g006cR0,41RDg00RJRF%F0RC#F,41REC:,3B5AB1CB;P1PDPF%Q0,41R0C:,3B5ABFP%M4R4PB141CRC,;E,3BP4PB1;0C,3BP41;DC,3BC9C9C91LB5P3P6g00S1RBg00SQR5'B1O36=?B5dg007H=K12CTbAbBbCX81X91X:1X;1X6AW71137,7:1136,7>'I10:610:7107:[[[^81^91^:1^;1^6A^7AP3f:RA/0;1@;APAP;P=P2P6P7P>O9b@bEb=b<123=P6P211@2122;;U3O2W>X01O418?7/06eW4X59X11X31X?<X28XD1P3D^W2o"). Qed.

Lemma fold_max_in_or_seed : forall l s,
  fold_left Z.max l s = s \/ In (fold_left Z.max l s) l.
Proof.
ltac2:(KReplay.run1 (kr_t_PlacementSearch ()) [] "h01Hh11lh21sh32_Hh41oh51zh63Heqh73Hinh82IHh91yp;1p;2p;3p;6p;5g008kj1FTg00=Fj2?Tg00_hj3:Tg008Kj1CTg00ZKR0j21Tg00Zhj2@Tg00@[j26Tg00A^R1j25Tg00D[j28Tg00[JR2j23Tg00`Bj3>Tg00_Jj6=Tg00H`j3DTg00\Hj5BTg00\jj5ATg0053j3<Tg00]Hj3;Tg005MR3P3P0f1R0f0R4DAp=4f3R5f2R65<3A;304'3p=2A<304p=0A;304p=9A<360/34p=7A;304,36p=E%F3R7P31404R8P4P8P0C2^23R8X171044g00T11?343:%C3R9/44R:P4P:P9C2eX23P01145R9O11469R:P9P:P6C2P2f4R:,10R9,45R;/0919;5f5R;,16R9,4:R<19<:R=97;<776P410<9P3f6R<,15R9f7R>P4P4P<C2974:X531@5<165<109<'518<51095'5'3P216:>11:>R2/0>'518>:102:'5f8R2,1;R:/0;R?P2P:P:P>C2'3P416;210:2'5P1f9R:,6<11<:R@/0:f:RA,1>RBPAPBPBP:C277>R>P4f;RB,62f<RC,1:RD/0CP3f=REf>P4P4PEC2974BX53RF10EARG10EERH19ECRI'31?3E9:HI3>11AEREP4E=W0W3P0P4O2n2001000000120000000W0P4O1182;/5?P118:<10@<P>P418B210D:P3PAPF10AAAEGAC1?3A3:PEP4E=W0W3P0P4O2n2001000000120000000W0P4O1n200100000021000010000b414;9R9P4E=W6P4O1109510<9R<199;R9'3A><943>X7=P4O1n200100000021100010000b4AD356R6/44R5P4P5P6C2eX23X88X17X93P4DBW1o"). Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma higher_fit_b_complete : forall maps aZ nZ baseZ g,
  (0 <= aZ + nZ)%Z -> (0 < nZ)%Z ->
  (aZ mod page_size = 0)%Z -> (nZ mod page_size = 0)%Z ->
  (baseZ < two_pow_64)%Z ->
  (g mod page_size = 0)%Z ->
  (aZ + nZ <= g)%Z ->
  (g + nZ <= baseZ)%Z ->
  region_free maps (Z_to_bv 64 g) (Z_to_bv 64 nZ) = true ->
  higher_fit_b maps aZ nZ baseZ = true.
Proof.
ltac2:(KReplay.run1 (kr_t_PlacementSearch ()) [] "p'0h01xi001xh11Hh24__x1h34__x2h44__x3h51zh63Hnoh71yh81Ah97__arithh:4__ffh;8__varmaph<5__with=4__x4h>4__x5h?4__x6h@1fhA1lhB1BhC3HinhD1bhE2b1hF2b2hG1mhH1nhI3HeqhJ2HxhK2g'hL6heq_g'hM4HendhN2_HhO4__p1hP4__x7hQ1chR1ghS1ohT1phU2H0hV2H1hW3H10hX3H11hY3H12hZ3H13h[3H14h\3H15h]3H16h^3H17h_3H18h`2H2ha2H3hb2H4hc2H5hd2H6he2H7hf2H8hg2H9hh4HaAlhi5HaPoshj5Hbasehk2Hchl5Hcandhm4Hcg'hn4Hcleho3Hcshp4Heq'hq5Hg'Alhr4Hg'Whs7Hg'baseht7Hg'freehu4HgAlhv3HgWhw6Hgfreehx4Hghihy4Hglohz3Hhih{3Hloh|4Hmodh}4HnAlh~5HnPosi013HnWi026Hroundi031Si046__sat0i056__sat1i066__sat2i076__sat3i082aZi095baseZi0:2csi0;5heq_Bi0<5heq_Si0=4mapsi0>2nZi0?1qi0@2q0i0A2q1i0B2q2i0C1ri0D2r0i0E2r1i0F2r2i0G1si0H2x0p%0p&0p;1p;2p;3p;7p;4p;5p;6p;8g007fj1`Tg00`\k10VTg00a:k10ITg00a]k20lTg008kj1_Tg001@j20Tg00@[j26Tg00D[j23Tg00b=j2<Tg00bcj3aTg00c]k10^Tg0053j3?Tg00dFj2yTg00FCj1TTg00Fbk209Tg00H4j2\Tg008Kk10RTg00H`j3[Tg009Kk10JTg009ik10HTg00:Gk10GTg00KBj1eTg00J<k10@Tg00Kgk205Tg00;2k20=Tg00LJk70cTg00<dk20_Tg00=Fj2|Tg00=`k20]Tg00>Lk30\Tg00>kk40[Tg00A^R0j27Tg00dlj3{Tg00eXj25Tg00fBj2zTg00g1j2BTg00gNj3ETg00hXk30ZTg00i3k40YTg00iQk20XTg00^>k20WTg00ijj2xTg00jJk50UTg00kQk20TTg00[JR1j2XTg000cj3^Tg00l`j3]Tg003Uj1DTg000Gj4UTg00_hk307Tg00m=k30STg00_Jj6iTg001]k10QTg00<@k60PTg00C[k10OTg00mXk40NTg00n9j6fTg00]Hj38Tg00nUS00j2WTg00nok50MTg00oNk10LTg010ak404Tg011Ak70KTg012>k403Tg0137j2=Tg013Tk20FTg0146k20DTg014[j4uTg0156k402Tg00`Bk301Tg015Pk40CTg016^k40BTg017hk10ATg0196k20ETg00Yij5wTg00B9j2oTg00?]j2lTg00@>j2gTg00A7j2jTg00D4j2dTg00E7j2hTg00E]j2nTg00J^k60?Tg019Vk106Tg01:7k608Tg01:\k40>Tg01;\S01j3}Tg01<8k30kTg01<[j2kTg01=8j2GTg01=Vk400Tg01>1k20iTg01>Qk40hTg004Sk20fTg00GKk30eTg00I@k20dTg00I^k40bTg00;Uj4pTg00NWj7~Tg00Lnk30aTg00O;j8mTg00\jk50gTg002Xk20`Tf0R2#`#`p=cg007HR3/32p=;g005kR4-0f2p=2g005MR5??23p=@f2R6f1R7'0/32p=Jg00S1R8g00SQR97?2p=91|52p=LA?572p=120952p=OB0e572p=>20d52p=VP5P6P7P2H0bp=H20552p=NP5P7g00RJP2Cpp=tP7g00O_R:g00P>R;P;g00P^R<P2g00Q>R=F~p=sB0a572p=QP6P:P;P;P<P5P7g00V@R>P2CpP=F~p=rP5P7g00TNP2Cpp=YP5P7P>P2Cpp=Sf4R>P:P;P;P<f3R?P:P;P;P<P6P=F~P7P2Gmp=AP?P:P;P;P<P6P7P2Gmp>0<f6R=P:P;P;P<f5R@P>P?P:P;P;P<P6P7P2GmGmp>0;P5P>P?P6P7P2Eip=RP5P5g00ZKP7P2I0gp=KA8572p=4A85?61B72=?89'7p=F1B72=?89p=P1572,06p=bg01?YRA9?82p=:1072,=6,G?=?8Ap=I1072,=6p=M1G72=?8Ap=v20`24p=CA?829,77p>0:1G67/G2p=ZA8567/72p>0jP8P9P?P6P7P2Eip=qg006cRA#`RB#`RC#c#cS02$0VRD$0IRE00lERF#_10?6RG#;163?%2@#@RHg01@9RI,6@f9RJf8RK'0S03/3=f7RL?JJKf<RM1<DKS04f:RN,<DRO3a#9&0^DRP#LA?5IP1yDNf;RQ,12X55g00Q^RRg00U5RS#TRT#TRU#TRV#TRW#ORX%OT2095SRS'>RT'>g00UTRY'\%TWRW#TS05#ORZ%OWRW%OVRV%OU/>S'>RS'>'>/\Y&0RRRU5[R3[%_RR[%V>%V=7H6S06%V@R\&0J5R]7H?7H7R^&0H5R_&0G5R`%eARa#`#NRb%NBRc't,s`S07&0@;RdP`2055ARA%NCRC'Q%eBS08#NRB5r`PdP`%NaRe/QCRf=r`AS09PdP`P`1YBbPdP`P`20=53Rg/YCPdP`P`1SgfPdP`P:P;P;P<Ar`gA1YAc,s`K0cRfDADADAS0:H0<K0;20_`<RhP2P61|89S0;20]26#9dB0\537H0[Rib:b;b<X25X35X45X=5X>5X?511@7AJ7>@AJ>@616LKRj163L10LK#;%;=16=LRk'7Rl[[[[[[^25^35^45^=5^>5^?5P2PIPMf=Rmf>RnPPPQP7P?P>P=PJPNO<b99{DN15DORo1zDNDR11oN1yDm112nX551>VT,>X,>W,>Z/\Y=[RUP[P^P_P`P`1tBcPdP`P`1QbA/SCPdP`P`1QeAR^/SbPdP`P`1YCBPdP`P`1YgAPdP`P`1Sg^PdPfDADADADADADAPhPib:b;b<X25X35X45X=5X>5X?511>7AJ=7>AJ>6L163>10L@#;Pl[[\k[[[^25^35^45^=5^>5^?5P2PMPIPmf?RkPPPnP6P>P@PLPNPQO<b99{Dm1<Dm,5DRl1zDmDR11lm1B2mXQ5f@Rl?Ekn60Z5%_510lk,K2P5P51B2lXQ5P2fCRffBR^fARb3ERVH0Y1426P2PVP2PkCF+0XRVeZ0H5PV^0510^bRV-0W613V7RVePVP?10f^RVPl1K?VRV#L116VRVePVPUP[%V6%V?S0<7H7P_P`1QAc=r`eRVPdPVH0<PhPib:b;b<X25X35X451027S0=/36AJ76?S0>[^25^35^45P2P^fDRVfERoPQO4b9bL142>P0142=P7fHRpfGRqfFRr3ERsP7PVCF[RtP2AEqroRuP2PfCF147LRv[P6fIRw?EpqRxP6PoCF\vP>P2O1RvP7n2001000000120000000X05Pt^05P2P6P7O2P6PuP6PfCFP014?s1P?V13>oP2fJRs?EwpRt,4@1P=qP01P721367S0?[S0@13721P67Ry[S0A13?6\y1x72S0BP7n2001000000120000000XG5XH5Q0@^G5^H5P2PKPwP7O3b1WJWNP7P2O2n2001000000120000000bJb1WJX05I0U136lRlePl10VfRl-0T>1K>lRy/1l14y>'XP110oVRy,K@Rl/1y14l@14@uP210roRu,K=Ry/1uP210qrRz,1=10pqR{142tXK511{{PFP5A^EE2,5DA]EE27bD#DR|XTFR}PwCU,4{%L{407PLP2DRbpWIP2O114y=P0142KP7PtP7PrCF[S0CP2PxP2PoCF147JRy[P6fKR~?EswS0DP6PqCF\yP=P2O1P7n2001000000120000000X05Q0C^05P21KK{RyP7O2PyPxPyPoCF10wpS0C,KJRy/4t1Pyr<0S2bCb1WCP2O1n200100000021000010000bSAEoVf,4?1yD>112@X55%Ll11>lRlePlQ05#T#O1>XS,>W'>/\Y1>ZT/\Y=[RU5[RP[Q06%VL9H\?7H7P_P`P`%ea#NRa,SAPdP`Q09PdP`Q07PdP`P`1QaC/SBPdQ0:DAK0;DAPhPib:b;b<X25X35X45X=5X>5X?5XP5132=AJ?>711L?AJJ=L16KJ163K10KJ#;%;L/7j[[[[[[[^25^35^45^=5^>5^?5^P5P2PVPIPoPrPqPPP=P?P>PNPMPkP^PfO>b9bL9{D>1<D>,5DRf1zD>DR11f>P111u@PFP5P}PqCU,4@%2=#@P711z=P5P{%22S0:#@XK5Rz%2pRu%2qRf'0#2%@2X55P5P3102u#2#@X55P5P31032#2#@X551|53PfPbEiPuP^Ei%2{PpPqP4PUP[P]P_P`P:P;P;P<Q02#c#c#c$0QR{-0=5/tg,s`J0PPhPib:b;b<%@{g00T1[P2b9A?543R{$0ORgeH0NDRPLP2EfWIP2O1PFP5P}PpCU,4=g01A2Rup4p710RfPup4p7210RuP7\7RP%_6RIP0P>P?P6P7CU98?2A?@v6A8=2?'7X0@,W@Rv[RjP?P2O1S02=?>7A8@26'7X0>,W>P@P>P?P6CU98>7RB[RaP@P2O1=?=?A8L2>'7X0=,W=\BP>P?P6P7P2I0MS07P7n2001000000120000000X76WAW@WBW8Pj^76^AI^@P^Bu^8fP2PFP5P}PsPKP7O611|JA8F2~'7X0F,WFQ00PF11|NfLRB98F2'7X0F%2NS00#@S09P211|MfNRC98F2'7P0A^EE7,5DA]EE77bD#D/1mfORA98F7%2n#@P2A^EE?,5DA]EE?7bD#D/1kfRR\98F>P5A^EE@,5DA]EE@7bDRR#DPz&0LRPbP7EfWNWIP7P2O2n2001000000121000000W1XTFP7P2O2n2001000000121100000bCb1WCP2O1n200100000021000011000PHPp1<D=RR1<DrRzPEPEP7P2H04=8FsP~1<DqRY1<DwRZP6P7PnP2K0KPYPZP6P7H03#:P51<DpS06,5D15D>RY15D?RT'0RW,=2PYP21<D~,5DRSCIX55P2PpPmEf15D69MpTPTPp1<DsS05,5DCIP5PS15D@RS=MsYPSPsP2CIX55P2P~PmEf1=wWPYPwP~CIPM15D=RY/0SRS,=2PYP2fMRW,<D,5DCIX55PB1=mSPYPmP2CIX55P01v72%:6RT%:7RX'XRl[Ry%:2,XX1v67RX[Rx%:?/XT\X20F72RXP7n2001000000120000000XF8XE8Py^F8^E8P21=~SRSAMY~WRWP7O3%:S%:W'X15DLRWP5PWP51072RW00DC13WC16CW'XP11067RW/3A16AW1=^GP?P^P\CIP2fPR^,3GfTRWfSRA'010>?RS#DRY'1PFP5P}fURTCU,4YP0PjPaP=P@P>P?CU98@6\vQ07P2n2001000000120000000X76XAIX@PXBuX8fPa^76^AI^@P^Bu^8fP2PFP5P}fVR}10@>Rf#DRuPF10=@#DRP,1|fWR|98F2'7X0FPEPEPmPMH04RmA^EEm,5DA]EEm7bD#D/1uA8Fm}%LuPQCuH02O6b1401AETWA,4YPfP\P7PBH0C13u\Pr10}TPPP0142qP7fYRufXRY;E|P7PTCFRQ[P2AEY|}RmP2PWCF147p[RF146w\QPoP2O1P2n2001000000120000000X05PF^05P210L=R=#DRF14Fm1PFWP6P0Q0@Q0AQ0?1P?6[Q0BP2n2001000000120000000XG5XH5Q0A^G5^H5P210KL#DPTP6O3b1CuO2b1H0B13PoRPePP&0A=13=FP0PyPx1v?6\lPXP2n2001000000120000000XF8XE8RXPx^F8^E8RxP2Q03,=pRlAMJpYRy%:lRF%:yRPP01=72#:1376Ro[Rm13271=67#:RQ[RI1=?6#:\o20E72RoP2n2001000000120000000X75X05RaPI^75^05RvP2Pw10NJRjPj%DjPwP6P?DwO3b1407O3b1c02bmbnbkWMP2O116^GP1fQR1/=S#:AM>1A#:1=VfP@PVPWCIP@1=\f#:P0PmPI136?\QPoP7n2001000000120000000X75X05RoPm^75^05RmP2PWP=P7O313=W15DkRk#L11LkRkePk15DbRb#L11JbRbePbfZRb/0u,KsRk#L11wkRkePk1ob4%;b1334Rkf\R=#2#;[[1o=4%;=f^RQ#2RI#;Rf\k[1oB4%;B%2C#;\k[f[RC/o4%;Cf]RV#2R1#;\k[1l=4%CV,g4/01,1V\g1jV41634RV16I4,7f[1dQ41643RQf_Rf#2RI,6413I3'7[1hf4f`Rf#C#@\{1nf4faRf#2/1f\{%CfP5fb#2P51lT4%C},g4%2}'0,1}\g1j}4%2|RT#;16T4'7\V1d|4%2YRT,6413T3'7\Q1hY4%Cu#@\{1nu4%2b/1b\{%CbP5%2CP5fm/l4fnRb%Cb,g4%2b'0'1\g1jb4foRb#2RT#;16T4'7\V1db4fpRb#2RT,6413T3'7\Q1hb4fqRb#C#@\{1nb4frRb#2/1b\{%CbP5fsRb#2P51lb4ftRb%Cb,g4%2b'0'1\g1jb4fuRb#2Rg#;16g4'7\V1db4fvRb#2RV,6413V3'7\Q1hb4fwRb#C#@\{1nb4fxRb#2/1b\{%CbP5fyRb#2P5p-0R{PUP[%V7Q0<?H?]9H]67H?P_P`P`Q08#e#NR_1QceRe'YPdP`P`1Se_PdP`P:P;P;P<P@J0?DADAPhPib:b;b<X25X35X45WOQ0=,66Q0>P@[[^25^35^45^O{P2fkR{?M=CP=P{f{CIPbPCP=PYPWO6b9c0Fc0Bb_b^b]b\b[c0Ec0AbZbYbXbWbgc0Dc0@bfbebdbcbbc0Cc0?bab`bVbUb1c04c05c06c07bLc0;c0<b6b1W6P2O1AM@\W#:PoPmP2PL10W}R}P7O313}LPXPxP2PlPyPaPvP2PN10wuRvPv10|uPNPwP|PuPuPr&06uJ08P6DwO3b1:01FPO3b1b6b1W6P2O1n200100000021100011000WMP2O1n200100000021100011000bSc03bBb6b11<DB,5DPnDR1<DM,5DPLDRb6b6POQ05P?P6H03#:eb6WCZ0GEXDEH0>AapRz#9Q01p4p710RzP8\2RR%_7REP0A}672#9A8>26Q02+0:X0?,W?R0[A8?27P6P2O1+0:X06,W6A}?67#9[ROA}>?6#9\0B0k672P2n2001000000120000000WAW@W8PO^AE^@R^8zP2P5Q0:/k310swRz/B2'G102w/Bp1<D2=a~Z3ZRRXR5PtP5Q0D%9R60j2X05PK14Kt%2K/k3Q0C/BK'G10KpRt/BqQ04Q065as3Z#9P>Pt10rpPqPKPrPpPpP@&06pJ08PnDw13tqQ00/k3Rt10~sRn/BNR@'G10NsRs/BwRK;Z2#9XD81G2@?ZK9#9XD81G92?ZK9#9XD81G99?Z29#9XD8Q0;10JwR8/BpR9%9913sw[138p%9K[1x8pP2H00Cq1BzJR2%9213nN[13zJ%9@[1xzJPLH00Cq%2JRL/k3Rz%9zQ09[%@L%9t[20iL3P?H00Cq1<DJ=a~ZP6CqbsCuH02O4b1PwPpPqPrH0h#9ebtbqbrblbzb{bobKc0:c01bvb|WwWxWyXuHWjX}HWhW~WiXR5Z095Z0>5Z085Y0=o"). Qed.

(* [comment removed for export] *)
Lemma higher_fit_b_sound : forall maps aZ nZ baseZ,
  higher_fit_b maps aZ nZ baseZ = true ->
  exists g, (g mod page_size = 0)%Z /\ (aZ + nZ <= g)%Z
            /\ (g + nZ <= baseZ)%Z
            /\ region_free maps (Z_to_bv 64 g) (Z_to_bv 64 nZ) = true.
Proof.
ltac2:(KReplay.run1 (kr_t_PlacementSearch ()) [] "p'0h01Hh11gh22Hgh31xi001xh41mh51nh61Ah72b1h82b2h91fh:1lh;2H0h<3Halh=5Hfreeh>3Hhih?3Hloh@2_HhA2aZhB5baseZhC4mapshD2nZp;1p;2p;4p;3g007fj1CTg00`\j1YTg00a:j1VTg00a]j2TTg008kj1OTg01>Qj4WTg01;\R0j3MTg00]Hj39Tg00nUR1j2GTg01<8j3RTg001@j22Tg00b=j23Tg00bcj3ITg00gNj3ATg0053j36Tg00A^R2j28Tg01AOj2STg00D[j2;Tg00g1j2<Tg01<[j2DTg01>1j2QTg00ijj2PTg014[j4KTg0156j4UTg004Sj2NTg01=8j2FTg00S1R3f0R4g00SQR536p=1f1R6A6345'8p=4g005kR7,N4p=Bg007HR8,D4p=Xf2R91<64'Fp=L1296/<4p=01F96/F4p=@g005MR:/G4p==f3R;13647I9p=H1296/;4p=EAI964=635p=51;96/84p=?1864,89p=>1N47/D8p=71F64=635p=:1D68/F4p=Jg006c#C#C#C#C#C#C#YR5#VR7/T7#OP;P9P6P4CW#1P0p4p710R0P3\4R7%O6R<P2AM964#1f4R=?949P;P4O1'4X3;,G;[R>A9;46P9P4O1'4X39,G9AM;96#1R?[f5R@?94;P=P4O1'4X3=,G=\?AR964P6n2001000000120000000W:W9W6P>^:<^97^60P4P:%B4R0#XR712@=;L4A04=;f6R<1354R>135=R?3I3@RAX1:AA@=;P6O4AA<@=99:4/4AX3:#=P1P:f7R1?A<@99:412<@=L74A04@=P1P>P5P@CH3@'4X3:A6:08R0AE1<4124<f8RA135<RB75>7?@3>X1:#=P4f9R@?AA199:412A1=L74A041<1351R79I@>3@'4P2f:RC?A@A99:6%76A0@A6A06A13@PC1356P5PACH':f;RA?EC4124Cf<RD135CRE75>7?@5>0X1:#=P4AADAC99:;%7=A0DA=A0=AC3@f=RCP?P5PACH':P21:64%19RA%16R?'8[R=14?41:96R?[%1;/8A\?1S64P6n2001000000120000000X83X73R?P=^83^73R3P4%7<f>R=?0C<A0<CD3@R<f?RAPBP5PCCHRBP6O3%1</4BP2%B1A0A=1'JA01=C':f@RB135=757fAR7/2BR=/;4124BfBR<135B75>7?A5>0X1:#=P4%B@1<=@'JA0@BA':fCR@135775EP?P3P4%BDfDRE?0@D'JR7A0D@<R=P9O3%17/4=P2%7CfER=?0EC':A0CE@#1fGREfFRC'2R7/;4124CfHRF135C75>7?=5>0X1:#=P4%7A1<7A':A0BEC#1P?P3P4%7<R3fJR?fI;0<R<P9O3%13/4<P2%7@#1fKR<?0?@#1fMR?fLR@;E4124@fNR3135@75>7?<5>0X1:#=P4%7=#1A03?C#1P:fPRCfOR='2R</;4124=fQ135=75>7?35>0X1:PE%BE=6:8AE=3ER0AEE3?R?135E135355CRC'8R5'8P21D64#1A6:96[REA6:641D96#1R>[A6:;9\>1Q64P6n2001000000120000000X4:X5:PE^4:^5:P4%BFP8P9O3b0P0P5P21<64#11;96[R21;641<96#1R5[1;;9\51P64P6n2001000000120000000X4:X5:R5P2^4:^5:R2P4P<PFP6O3b0P?PCP5P2P412F=P3P1O3b0PDCKCKCKCUW?W<P6P4O2n2001000000121000000b2b0W>W2P6P4O2n2001000000121000000b2b0W=W2P6P4O2n2001000000121000000b2b0W2W@P6P4O2n2001000000121000000W0X1:P6P4O2n2001000000121100000b0b;W0XB:XD:XA:WCo"). Qed.

(* [comment removed for export] *)
Lemma no_higher_fit_iff : forall maps aZ nZ baseZ,
  (0 <= aZ)%Z -> (0 < nZ)%Z ->
  (aZ mod page_size = 0)%Z -> (nZ mod page_size = 0)%Z ->
  (baseZ < two_pow_64)%Z ->
  (higher_fit_b maps aZ nZ baseZ = false <-> no_higher_fit maps aZ nZ baseZ).
Proof.
ltac2:(KReplay.run1 (kr_t_PlacementSearch ()) [] "p'0h02Hfh15Hfreeh22H0h31bi001bh41gh51Hh64HgAlh74Hghih84Hgloh94__x1h:4__x2h;1eh<4HaAlh=5HaPosh>5Hbaseh?4HnAlh@5HnPoshA7__arithhB4__ffhC8__varmaphD5__withE2aZhF5baseZhG4mapshH2nZi011xp;1p;2p;4p;3p;>p;6p;5p;7p;8g007fj18Tg00`\j1cTg00a:j1[Tg00a]j2PTg008kj1LTg00D[j29Tg00@[j2ATg004Sj2;Tg01>Qj47Tg01B0j4GTg00b=j20Tg00bcj35Tg00=Fj2BTg0053j31Tg00FCj1KTg00Fbj2@Tg00GKj3JTg00H4j2\Tg008Kj1ZTg00H`j3YTg00I@j2XTg009Kj1WTg00I^j4VTg009ij1UTg00:Gj1TTg00;2j2STg00Kgj2ITg00;Uj4>Tg00J<j1OTg00Lnj3NTg00<dj2QTg00>Lj3MTg00>kj4RTg001@j2?Tg01C9l>bTg00n9j6<Tg00]_j2FTg01DJj5aTg00nUR0j2`Tg014[j4_Tg00NWj7^Tg00O;j8]Tg00A^R1j2DTg005MR2f0R3g007HR431p=:g00S1R5g01?YR6713p=6f2R7f1R8'?/93p=3g00SQR99153p=CP8g00O_R:g00P>R;P;g00P^R<P3g00Q>F^p==f3R=P:P;P;P<P7P8P3G]p=HA5783=159p=41?=7/98/D3p=21D83,D7p=Eg006cR:#8R>#8#8#8#8#8#cR?#[R@/P@#L19471A47f4R@g005kRA';#:RBg01@9,A@f8RCf7RDf6REf5RFC7#6RGf9RHPCPDPECGRI[PCPDPEPFCGRJPHPCPDPEC7RK#6[1;3A#:RLf:RM?3H8A37MHf=RN10?=f;RO,0?RP35P51B53RQf>RR10?@RSf<RT,0?RU35=153P5f@RV10?E10?RRW35=153%68RX]1P8f?RY10?FRZ10?NR[35R\#CA1596R]P5PVPYPRPNC7%63X35PDP9PVPYPRPNPEg00Q^REg00U5R^#KR_#K,@21@2_1@2^5J25J2g00UT'\%ZE3Y%LEP21X27P8%W2CV%U2%T2REP21S24R^g00TN1I2>R>C>,=E%O;R;PEP2P^g00V@R_1I2:R:C>,=EP;P2P^P_AN2:>C>,=ECHCH1QE<P3P71B59AM248CRbBbCbDX92X:21A4819481?7=,94[[^92^:2P3PYPVPTPNO4bAPOPMPHPCPFP@P=P3M>bE<P]P5P9P5p-0R4P3g01EXR7g00T1REn0110000020000X;5g01F4R<P6P3E<PE1FE3R:b5b0'FW1%6\1B56R\W1n0110000020100P3O1b1b3W7W8W6X42PIeX0GPKP5PQPMPHPCPDC7=153P5PTPOPMPHC7=153PX]0P8POPMPHPCC7RX#CPTPOPMPHP3DaA3TO3P3POPM10?3RM=4NPC25ELX42,`2P0P2A3NT3P3PTPOA4RMUC25ELX42PEP3A3YR3P3PRPNA4VMWC25ELP11;8A#:PVPYP8P8PYPRfARR10?810?Y34C2C2PEP31;=A#:fCRAfBR=P@P@P=PRfDRR10?=74SC2C2P1A3RAFPFPAP=fER=10?A74ZC2PEP3fFRZ?3=DPCPZP=fHR=10?C10?Z34C2P1fGR1=3HZfIRZ10?H10?134PEP3A3OZ=fLfJ,0?74UP5fMfK,0?75[%C3X35P3P6PRPNPHPFP8O4E<A1569P5P6P5P4P3PEP7n0110000020000X;5P<P9P3E<PEP:b2b1W1W7P8P3O2n2001000000120000000W2W8P8P3O2n2001000000120000000W2W6P8P3O2n2001000000121000000W2X42P8P3O2n2001000000121101000b0,F]W0%6XP\W0n0110000020100P3O1b0b3X5JC_W>X?BW<W@W=XF2XH2XE2WGo"). Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)
Definition search_candidates (maps : list (word * word)) (loZ : Z)
    : list Z :=
  loZ :: map (fun p => page_round_up_Z (bv_unsigned (fst p)
                                        + bv_unsigned (snd p))%Z)
             maps.

(* [comment removed for export] *)
Definition place_fits (maps : list (word * word)) (loZ hiZ nZ : Z) (g : Z)
    : bool :=
  (g mod page_size =? 0)%Z && (loZ <=? g)%Z && (g + nZ <=? hiZ)%Z
  && region_free maps (Z_to_bv 64 g) (Z_to_bv 64 nZ).

Definition place (maps : list (word * word)) (loZ hiZ nZ : Z)
    : option Z :=
  find (place_fits maps loZ hiZ nZ) (search_candidates maps loZ).

(* [comment removed for export] *)

Lemma place_sound : forall maps loZ hiZ nZ a,
  place maps loZ hiZ nZ = Some a ->
  (a mod page_size = 0)%Z /\ (loZ <= a)%Z /\ (a + nZ <= hiZ)%Z
  /\ region_free maps (Z_to_bv 64 a) (Z_to_bv 64 nZ) = true.
Proof.
ltac2:(KReplay.run1 (kr_t_PlacementSearch ()) [] "h01Hh12Hfh21mh31nh42b1h52b2h63Halh75Hfreeh83Hhih93Hloh:2_Hh;1ah<3hiZh=3loZh>4mapsh?2nZp;1p;2p;4p;3p;5g007fj1;Tg00`\j1RTg00a:j1MTg00a]j2ITg008kj1QTg01FPj1PTg01G2j4OTg01H3j2LTg0053j39Tg01HUj4Jj5ETg01I[j2DTg01Jhj5GTg00]Hj3@Tg00D[j23Tg001@j22Tg00b=j21Tg00bcj38Tg01=8j2BTg00A^R0j27Tg01AOj2KTg00g1j25Tg01<[j2ATg01>1j2HTg00ijj2NTg014[j4CTg004Sj2FTf1R1g00S1R2f0R3g00SQR439'7p==A9234p=0g005kR4,F3p=:g005MR5g007HR6793p=<f2R7/31/73p=>1713,77p=?1F34/A6p=61513,B7p=4g006c#;#;#;#;#;#;#RR4#MR8/I8#Q%P5f4R8f3R9P7P1CO1L5339P5f5R:P8P9P7CJ1D:8R;P1P3DGA@51;P:P8P9P7P1DE'=P0f6R;/D:9@57P;P:P8P9P7DE#0%:9#<13;91298f7R<1149114838#07>:3?P3f8R=/D<9@58f9R8P=P<P;P:DE#0P01B13#0%07R:%01R;'7[R>1=;31B71#0R;[%09/7:\;1K13P1n2001000000120000000X52X42R;P>^52^42R2P3%6<f:R>;4<12<=;48R:f;R?114<114=R@38RAP1O3%0:/=AP0%6=?4?=12=8;4>#0f<R=1148RA78@#0%:8#<13=8128>f=R8114>78A#07>?3?P3%6>?48>12>?;4=#0f?R>114?114=38#0P;P2P3%68f@R?;48RAf>R@,28/5>R8P7O3%0A/=8P0%6@fAR8;4@#012@>/5?#0%:>#<fBR@/3>12>?fCRA114>114?38#07>83?P3%6??4A?#0128@/5A#0P;P2P3%6AR2fFR;/5ARAP7O3%02/=AP0fDRA#6#0fGR2/5A#0fERA#:#<fHR@/3A12A;fIR8114A114;38#07>23?P3%6;#0fJR;/52#0%:@#<fKR2/3@RA12@8/3;R?fLR>114@114838#0R4'7R@'7P01A13#0A9571[R:A95131A71#0RB[A9597\B1H13P1n2001000000120000000X25X35P:^25^35P3%:8P6P7O3b0PAP@P01513#01371[R013131571#0R@[1397\@1N13P1n2001000000120000000X25X35R@P0^25^35R0P3P>P8P1O3b0P?P4P@P0P3128;P2P<O3b0P=CCCCCCW9W6P1P3O2n2001000000121000000b1b0W8W1P1P3O2n2001000000121000000b1b0W7W1P1P3O2n2001000000121000000b1b0W1W:P1P3O2n2001000000121000000b0W0X;5X?5X<5X=5W>o"). Qed.

(* [comment removed for export] *)

Lemma existsb_find : forall {A} (f : A -> bool) l,
  existsb f l = true -> exists x, find f l = Some x.
Proof.
ltac2:(KReplay.run1 (kr_t_PlacementSearch ()) [] "p'0h01xh12Hyh21lh31Ah41Hh52H0h62IHh72_Hh81bi001bh91eh:1fh;1yp;1p;3p;2p;6p;4p;5p200R0g00\HR1p4p710p8P0g01;\R2p4p710p8g008kj17TP2j35Tg01FPj12Tg01KFj36Tg01H3j21Tg0053j30Tg00nUj24Tg00n9j6>Tg00J<j1=Tg00]_j2<Tg008Kj19Tg00=Fj2:Tg01K_j28Tg0156j4@Tg00H`j3;TP1j5?Tg00S1R1f0R2g00SQR330p=3P1\2f1R4#7f2R5%75f3R6?552#3f4R7f5R8#2R9A68751182R:30X07'4[W2g01?YR;=013P1P;P1p-0P2g00T1R<g01EXn0110000020000X91g01F4P3P2E>P<%=8=09:X07,47/<2b5W4%959554#3%27%979676117230X06,46[e%76A5762#3f6R:#2A6:8511:230X08,48[P7P5O1P11:12P8P6O1=012P1f7R9P8O1=012f9R<f8R=;58,84#3f:R>f;R?#2P1f<#2P611?=A6?>9n010000002000011?230X0>'4[]1P4P:P7O1R?#3A5=97R=,83#3P<%2>R311>911>2R@30X0<P:%2<11<:':C@W7W1A01?;P618;=#3A6><:=03@X0<,4<[eW1n0110000020000P2O1b1b8A;8549587#3%29A;976969:119230X0:,4:[eW6W2X;5P2D?W2W:X30o"). Qed.

(* [comment removed for export] *)
Lemma higher_fit_b_as_place : forall maps loZ hiZ nZ,
  higher_fit_b maps (loZ - nZ) nZ hiZ
  = existsb (place_fits maps loZ hiZ nZ) (search_candidates maps loZ).
Proof.
ltac2:(KReplay.run1 (kr_t_PlacementSearch ()) [] "h01gh14__x1h24__x2h31Hh47__arithh54__ffh68__varmaph75__with83hiZh93loZh:4mapsh;2nZh<1ph=1zp;1p;2p;4p;3p;7p;6g007fj11Tg00`\j1XTg00a:j1ETg00a]j2ATg008kj1>Tg008Kj1PTg00I@j2JTg009Kj1DTg00I^j4CTg009ij1BTg00:Gj1@Tg00Kgj2:Tg00MQj3?Tg00Lnj3WTg00;Uj4UTg00NWj7TTg00<dj2OTg00=Fj29Tg00=`j2NTg0053j33Tg00>Lj3ITg00>kj4HTg002;j26Tg001@j22Tg004Sj2FTg01<[j2GTg00g1j24Tg01=8j20Tg00b=j27Tg00bcj3;Tg000cj3KTg00eXj2<Tg00l`j3LTg003Uj1MTg000Gj4=Tg00H`j38Tg01;\j35Tg00n9j6QTg01>Qj4RTg01HUj4STg01I[j2VTg006cR0#1R1#1#1#1#1#1#XR2#ER3/A3R4#>g005MR5g00Q^R6#P%>6P5f2R6,J5f1R7%D5CC%B5%@5R8g00O_g00P>R9P9g00P^R9P51:50R0g00RJ1:51R19?50=W51CUg00Q>FT1O89f0R9P6g00S1R8g00SQR1'91N96=381dg007HR1=I57CHb5b6b7X15X251697/279359^15^25P9P7f3R0O2b41669R:/299356P5P0g005k,F9/G1R11479'01290f4R;'4R<'0f61729R=17203;R>'0X05P4P5AK339,<2AL339,<2'2#MX<4R3f5R?C=R@985955514?9,01/0</0>X05A85;@555538X=514;9,011296/40'017269;?='0X05P4P5P3P;C=9850555,981607/27P9EQb3P0P:P9P7CRP0P6P7P9CS1V06555538eX;5X85W9W:o"). Qed.

(* [comment removed for export] *)
Lemma place_complete : forall maps loZ hiZ nZ g,
  (0 <= loZ)%Z -> (0 < nZ)%Z ->
  (loZ mod page_size = 0)%Z -> (nZ mod page_size = 0)%Z ->
  (hiZ < two_pow_64)%Z ->
  (g mod page_size = 0)%Z -> (loZ <= g)%Z -> (g + nZ <= hiZ)%Z ->
  region_free maps (Z_to_bv 64 g) (Z_to_bv 64 nZ) = true ->
  exists a, place maps loZ hiZ nZ = Some a.
Proof.
ltac2:(KReplay.run1 (kr_t_PlacementSearch ()) [] "h04__x1h14__x2h21zh37__arithh44__ffh58__varmaph65__with74__x3h85Hfreeh94HgAlh:4Hghih;4Hgloh<3Hhih=4Hlo0h>5Hloalh?2Hnh@4HnalhA1bhB1ghC3hiZhD3loZhE4mapshF2nZp;1p;2p;3p;4p;6p;>p;7p;8g007fj12Tg00`\j1`Tg00a:j1LTg00a]j2FTg008kj1BTg00D[j21Tg00@[j2=Tg001@j2<Tg00b=j2?Tg00bcj3DTg01HUj4_Tg01I[j2YTg002;j24Tg01>Qj4UTg008Kj1TTg00I@j2>Tg009Kj1QTg00I^j4:Tg009ij1PTg00:Gj1KTg00;2j2JTg00Kgj27Tg00J<j1HTg00MQj3GTg00Lnj3ITg00<dj2ETg00=Fj2;Tg00=`j2MTg00>Lj3NTg00>kj4OTg00_Jj69Tg01L<j3CTg00KBj1RTg01C9l>STg01;\j3^Tg01L\j4]Tg00n9j6\Tg01Mmj4XTg004Sj2WTg0053j3ATg00;Uj4VTg00NWj7ZTg00O;j8[Tf0R0g005kR1'Wp=0g005MR2g007HR37A0p=3g00S1R4g00SQR57A0p=8P2f1R6g00V@P0CVp=5P6g00O_R7g00P>R8P8g00P^R9P0g00Q>FZp=6f3R:P7P8P8P9f2R7P6P0G[p=@g006cR;#2R<#2#2#2#2#2#`R=#LR>/F>#B113:1=37f5R>#0#3R?f4R@#0#3f6RAg01@9'=f9RB/1Af7RCf8RD'</1Bf<RE1?=D1?=B3D#8P2f=R=PEf;RDf:RFC_RG1Y=ERHP4P=14EFRIPFPDCU%80XA4P=PIPFPDPBg00Q^RJ#TRK%BJRJP21>27RLP6%Q2C:%P2RM%K2RN1J23RO172;RP'5,6N%H8R8172<R<9G2P=I2<R<,5O,6NC@1EN9R9P0P71;451M07#8dAN236COR5b4b5b6X02X1211301467/<7R4,13[^02^12P0PDP=PBO3b3PCP2%0ERC%0FRB'4#0%30X22P2P3%0D,40#0#3X22P2P31430#0#3X221;23PBP>E9PCPAE9%0IACEF1E9P>P@P:PKPJP2PLP61>2:C:PMPN%R;,72R;,5P,6NP815<;,6NC@P9P5b4b5b6X02X12X721107114:[^02^12^72P0PFPDP=P:O4b3P6P0M>SA^2GHP=PEPDPFC]E\CXW8W:W;X9?W<W@W>W?W=XB2XF2XC2XD2WEo"). Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)
Definition place_in_model (h : VmMaps) (nZ : Z) : option Z :=
  place (vm_reserved h ++ vm_maps h) page_size (alloc_top h) nZ.

(* [comment removed for export] *)
Lemma place_in_model_admissible : forall h nZ a,
  (0 <= nZ)%Z ->
  place_in_model h nZ = Some a ->
  bv_unsigned (Z_to_bv 64 a) = a
  /\ (bv_unsigned (Z_to_bv 64 a) mod page_size = 0)%Z
  /\ (0 < bv_unsigned (Z_to_bv 64 a))%Z
  /\ (bv_unsigned (Z_to_bv 64 a) + nZ <= alloc_top h)%Z
  /\ region_free (vm_reserved h ++ vm_maps h)
       (Z_to_bv 64 a) (Z_to_bv 64 nZ) = true.
Proof.
ltac2:(KReplay.run1 (kr_t_PlacementSearch ()) [] "h04__x1h12H0h22Hah37__arithh44__ffh58__varmaph65__with74__x2h84__x3h91zh:1Hh;3Halh<5Hfreeh=3Hhih>3Hloh?2Hnh@3HrthA4HtophB6__sat0hC6__sat1hD1ahE2a0hF1hhG2nZp;1p;2p;3p;6p;4p;7p;8g01FPj1zTg01O5j2fTg01H3j2]Tg0053j3?Tg007fj1FTg00`\j1eTg00a:j1bTg00a]j2_Tg01P?j11Tg01Q7j6XTg00D[j27Tg001@j2=Tg00b=j20Tg00eXj2ATg01R>j1aTg00@[j2<Tg00dFj2`Tg001]j1KTg01S9j2^Tg01Saj2NTg01T>j3[Tg00FCj1CTg00Fbj2GTg00GKj3ITg00H4j2ZTg008Kj1YTg00H`j3WTg008kj1VTg00I@j2HTg00I^j4yTg009ij1xTg00:Gj1wTg00KBj1uTg00Kgj2MTg00;2j2JTg01Tbj3tTg00J<j1sTg00Lnj3rTg00LJj7pTg00<dj2oTg00=Fj2QTg00=`j2nTg00>Lj3jTg00>kj4iTg00A^R0j24Tg01UEj1hTg00c]j1kTg00dlj3lTg00fBj2gTg00_Jj6PTg014[j4ETg01Ucj1OTg01V]j1RTg01WSj3STg004Sj2dTg00bcj3TTg00;Uj4UTg00NWj7cTg00O;j8vTg007HR1f0R2'7p=>%F2#Fp=Bf2R3f1R4#O%R23Sp=\g005MR5g005kR6,d2;?1p=5g00S1R7AT342g00SQR83?p=q1734/42p=:1442,43p=3f4R9f3R:#O%R33S?T42=?78p=2A?542p=91<12p=61=34/72p=8P5P4g00TNP2CUp=LP4g00O_R;g00P>R<P<g00P^R=P2g00Q>Fcp=;P5P4g00V@P2CUp=DP:P;P<P<P=P3P4P2Gvp=@A?728p=mg01X0%>4%z51f:31]543?g006cR>#FR?#F#B#BR@#eRA#bRB/_BRB?\99RCP6%19RDP:P3P2EX%5317631=3:10A310A:RE5qC7:D33P0%5:1=:9f5RD#1PBPDPDPE10A9RED23:9:6:1AAERC/99%5C%6Cf6RF#198CDPBPFPFPE10ADD23333P2%5Df7RE,=Ff8RC#1PBPCPC10AF10AERGD23:9:6FP0176E1=ECf9RE#1PBPEPEPG10ACRGD23:1AAGRF/9C%5F%6Ff:RH#198FEPBPHPHPG10AED23333P2176Ef;R6,=Hf<RG#1PBPGPG10AH10A6RHD23:P0f=R0#1986GPBP0P0PH10AGRHD21AAHRF/9G%5F%6Ff>RG#198F0PBPGPGPH10A0D23333P2f?RH#1980GPBf@R0P010AG10AHD2fARH#a%1Hg01@9'<P51`A0192HX95%K?RG%K@RF'^%6G%>F1NGFRI#6[[%>GRJg01EXRKA[GF4UW2%>I\K^2Jg00Q^RJg00U5RK#CRF#C#CRL#C,G51G5L1G5F1G5K5I55I55I5g00UT'Z%YJRK3W%VJRJP51H53P41H5:Cy%x5RF%w5RL%u>,M5RM1J5G=t5ARN'L,;L%s<ROPL1M5>R>1M5?R?5r5/DM,;LPOPL%B@#B#B#KR@,J5/D>,;LRMPOPL1J51RP/D?,;LPOPLP;P<P<P=1DP>,;L1L>N,;LFpC@C@C@C@1oL=R=P2P31Q781n23#mdAj514CiR1b4b5b6X05X75X851<3IA843:17@3%>9R81<9I,48[[[[^05^75^85P2fE#1fDR8fCRIP:PDPEfBREO7b3bBbC%>0RD%hA,NG,<0'4e%kA,<0,4De9lA010A0,AARD1gA0EP19D0P5PH192E%52%62%18982IPBP8P810AER810AID23333X9519HH%5HRD%6HR0%1I98HERGPBPIPI10AHRIP8D2R8'4RB'4R9'41Q5HPDP9P6P0PBPKPJ1H54PFPLPMPO1LP>,;LC@P=P1b4b5b6X0517@2%64[^05P2PEPCO2b3PGP8P:P3CECECECE1AAIP2EPb@bAW<W=P4P2O2n2001000000121000000W1W>P4P2O2n2001000000121000000W1W;P4P2O2n2001000000121000000bEW:W?XD5XG5WFo"). Qed.

(* [comment removed for export] *)
Example place_accepts_a_negative_length :
  place_in_model (mkVmMaps [] [] 0 0 0) (-4096) = Some 4096%Z.
Proof.
ltac2:(KReplay.run1 (kr_t_PlacementSearch ()) [] "p;1p;2p;3p;5g01FPj1?Tg001]j13Tg01H3j22Tg00=Fj2>Tg00`\j1;Tg00a:j1:Tg00a]j24Tg008Kj15Tg01Xgj26Tg01YJj37Tg01Ymj58Tg00XAj19Tg01O5j2=Tg0053j3<Tg007fj11Tf0#1#1p=0g005MR0#?R1g006c#0#0#0R2#0#0#0R3#3,20R0'>%;2R2#:R4/44#5R4P4g007HR4g01F41624d572R2P2P4D8%93'==<10do"). Qed.

Lemma place_in_model_complete : forall h nZ g,
  (0 < nZ)%Z -> (nZ mod page_size = 0)%Z ->
  (g mod page_size = 0)%Z -> (page_size <= g)%Z ->
  (g + nZ <= alloc_top h)%Z ->
  region_free (vm_reserved h ++ vm_maps h)
    (Z_to_bv 64 g) (Z_to_bv 64 nZ) = true ->
  exists a, place_in_model h nZ = Some a.
Proof.
ltac2:(KReplay.run1 (kr_t_PlacementSearch ()) [] "h05Hfreeh14HgAlh24Hghih34Hgloh42Hnh54Hnalh67__arithh74__ffh88__varmaph95__with:1ah;1gh<1hh=2nZp;2p;3p;1p;4p;7p;>g00@[j2STg004Sj28Tg0053j31Tg00D[j22Tg001@j2RTg01P?j17Tg00`\j1BTg00a:j1@Tg00a]j2?Tg01Ucj14Tg01V]j1:Tg01WSj39Tg00b=j2;Tg00bcj3QTg008Kj1PTg008kj1OTg009Kj1NTg009ij1LTg00:Gj1FTg00;2j26Tg001]j1ETg00;Uj4ATg00NWj7CTg00<dj2DTg00=Fj25Tg00=`j2GTg00>Lj3HTg00>kj4ITg01R>j1JTg01Zdl>KTg01FPj1>Tg01O5j2=Tg01H3j2MTg00nUj2<Tg007fj13Tf0R0#3#3p=0g01X0g005MR1g007HR2f1R3'Sf2R4g005kR5'8=112R6f3R7,25f4R8f5R9'Rf6R:#7'2g00S1R;g006c#0#0#0R<#BR=#@R>/?>R>f7R?#4%:?391;=91;=:3Qg00SQR=31f8R@#4%:@59>P5%7@P?P:g00Q^R:#P%O:%N1%L1%F1R:g00O_g00P>R?P?g00P^R?P11612g00V@%0<#0#0#ER<,61CAg00Q>FC1D:?P0P415;=1G04=1;=dAH123CIb7b8b9122<P0b61225eP915121855=112eP8%J@P7P4P3P0M>K%>1f9/=@1M1031X:1,<1eW0W2W3X16W5W4X;1W=W<o"). Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)

Definition witness_ledger : list (word * word) :=
  [(Z_to_bv 64 4096, Z_to_bv 64 8192)].

(* [comment removed for export] *)
Definition demo_top : Z := alloc_top (mkVmMaps [] [] 0 0 0).

(* [comment removed for export] *)
Example place_skips_the_occupied_floor :
  place witness_ledger page_size demo_top 4096 = Some 12288%Z.
Proof.
ltac2:(KReplay.run1 (kr_t_PlacementSearch ()) [] "p;1p;2p;4p;3g01FPj18Tg00KBj17Tg001]j12Tg01H3j26Tg00=Fj25Tg01G2j44Tg0053j33Tg007fj11Tf0#1#1#1#1p=0g005MR0#8R1g006cR2#7#0#0#0#2,60R0'5g01[ng005kg01]8%02#0#0#2C4=310do"). Qed.

(* [comment removed for export] *)
Example place_complete_premises_are_satisfiable :
  (0 <= page_size)%Z /\ (0 < 4096)%Z
  /\ (page_size mod page_size = 0)%Z /\ (4096 mod page_size = 0)%Z
  /\ (demo_top < two_pow_64)%Z
  /\ (12288 mod page_size = 0)%Z /\ (page_size <= 12288)%Z
  /\ (12288 + 4096 <= demo_top)%Z
  /\ region_free witness_ledger (Z_to_bv 64 12288) (Z_to_bv 64 4096) = true.
Proof.
ltac2:(KReplay.run1 (kr_t_PlacementSearch ()) [] "h07__arithh14__ffh28__varmaph35__with41zp;1p;2p;3p;4p;5p;6p;7g00KBj16Tg007fj10Tg001]j18Tg00D[j25Tg00@[j2;Tg004Sj27Tg01Saj2GTg001@j2ETg00`\j1DTg00b=j2CTg00bcj3WTg0053j3@Tg00A^j22Tg008Kj1BTg008kj1VTg009Kj1UTg009ij1TTg00:Gj1JTg00;2j2<Tg00<dj2ITg00=Fj2>Tg00=`j2HTg00>Lj3KTg00>kj4LTg00Lnj3FTg014[j43Tg00a:j1MTg00a]j2NTg01YJj3OTg01Ymj5PTg01P?j1QTg01^<j5RTg00_Jj6STg00;Uj4YTg00NWj7XTf0R0#6#6#6#6p=:%00#0p=A%00#0#0#0p=1g005MR1g007HR27@0p=9f2R3f1R4/20'2p=4P1P4g00V@P0CYp=?P4g00O_g00P>R5P5g00P^R5P0g00Q>FXp==P1g006cR6#6R7#6#:#:#:#0#:#:#0#A#1#1#1#1#1#8R8%06R6#0#1R9#A#1#8R:,52R;1;2:R<17::#9R=%86%89'GR6,;0%17#1#1#8R7/7:#9R>15:7R?1E7:R@/50g00S1RAg01[n%D9R9/C71C9:3Wg00SQRB3@RC343474=34X41P;1;86R615@8RD/2CRE,2?RF,2>RG'2RH,2=RI,2=RJ,2<g00Q^RK#BRL%VKRK%U1RM%T1RN%J1RO1<121<1:RP'?'=1IO5R5P0P31>ABRQ1H03=@ABdAK124CLR4b1b2b3P;P0b0P<PJg01_=g01_c'>RJP=PI1>12RIP=PHPIP6PGPJP>PFPIP?PEPLPKPMPN1<17RE,?P,=OP5P4b1b2b3P?P0b0PDPCPLPKPMPNAF1EP1<18'?,=OP5P4b1b2b3PDP0b0PQC3C3C3C3C3C3C3C3%M9RQ/NQ#BRQPQg01F49O92R9P9P2DP#QPQPQP9P9P2DRESg005kR9,521799#917:9#9g01]8R:g01@9';1779#9159715@:;4C343474<eo"). Qed.

(* [comment removed for export] *)
Definition full_ledger : list (word * word) :=
  [(Z_to_bv 64 4096, Z_to_bv 64 (demo_top - 4096))].

Example place_finds_nothing_when_full :
  place full_ledger page_size demo_top 4096 = None.
Proof.
ltac2:(KReplay.run1 (kr_t_PlacementSearch ()) [] "p;1p;2p;4p;3g01FPj17Tg00J<j16Tg00=Fj22Tg001]j15Tg01G2j44Tg0053j33Tg007fj11Tf0#1#1p=0g005MR0#7R1%60R0'2g01`Ig005kg01]8g006c#0#0#0#0#0#0#5C4=310do"). Qed.
