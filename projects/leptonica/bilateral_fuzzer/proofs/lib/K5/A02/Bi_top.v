(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Bool Lia.
Import ListNotations.
Open Scope Z_scope.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.K5.A02 Require Import Bi_topkit.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.K5.A02 Require Bi_addpix Bi_apply Bi_bbexact Bi_bcreate_336 Bi_bcreate_a Bi_bcreate_b Bi_bcreate_c Bi_bcreate_cut Bi_bcreate_cut2 Bi_bcreate_defs Bi_bcreate_defs2 Bi_bcreate_hpass.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.K5.A02 Require Bi_bcreate_kfrloop Bi_bcreate_kidxloop Bi_bcreate_ncloop Bi_bcreate_vpass Bi_bd_defs Bi_bdestroy Bi_bexact Bi_bgexact Bi_border Bi_copyres Bi_crgb Bi_expf.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.K5.A02 Require Bi_fktw Bi_fz_defs Bi_gausskernel Bi_getcount Bi_getdims Bi_getextreme Bi_getpars Bi_getpix Bi_getrgb Bi_iface Bi_iface2 Bi_iface3.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.K5.A02 Require Bi_kinvert Bi_lineptrs Bi_mborder Bi_pb_defs Bi_pbgray Bi_pbil Bi_pixacreate Bi_pixadestroy Bi_pixalineptrs Bi_pixcreate_nn Bi_rangekernel Bi_rasterop.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.K5.A02 Require Bi_rgb_defs Bi_ropn Bi_ropn_defs Bi_setorigin Bi_setrgb Bi_template Bi_verifydepth CfY_pixdestroy_null CfY_pixdestroy_rc Cf_boxacreate Cf_boxadestroy_empty Cf_clone.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.K5.A02 Require D_libiface Km_create Km_destroy Km_setelemF LeptC_cmapdeser LeptC_cmapdestroy LeptC_cmapvalid LeptC_padbits LeptC_setcmap LeptF_iface LeptM_destroy Lept_create.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.K5.A02 Require Lept_deser Lept_err Lept_gmax Lept_hdr Lept_iface Lept_stderr Lept_zero Pm_cmapcopy Pm_cmapvalid_stk Pm_copy Pm_copycmap Pm_hdr2.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.K5.A02 Require Pm_iface2 Pm_noinit Pm_strrepl Pm_tmpl RT_fk_iface RT_gaps_iface RT_iface RT_traces.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib Require KReplay.
Ltac2 kr_t_Bi_top () := "K47Corelib7Numbers7BinNums8positive01K47Corelib7Numbers7BinNums1Z02K47Corelib4Init9Datatypes4list01K47Corelib4Init9Datatypes4list02K47Corelib4Init5Logic2eq01I47Corelib4Init9Datatypes4list00C69OSSVerify5KrLib2K53A029Bi_topkit6zl_eqbC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List7existsbI47Corelib4Init5Logic2eq00C69OSSVerify5KrLib2K53A029Bi_topkit@in_zl_of_existsbC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive02I47Corelib7Numbers7BinNums1Z00K47Corelib7Numbers7BinNums8positive03C69OSSVerify5KrLib2K53A029RT_traces=CLIENT_TRACESC1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01I47Corelib4Init9Datatypes4prod00C47Corelib4Init9Datatypes3fstC56Stdlib6ZArith6BinInt1Z3eqbC69OSSVerify5KrLib2K53A029Bi_topkitAex_lit_of_existsbC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A02=RT_gaps_iface9LEPT_LITSC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes4prod01C47Corelib4Init9Datatypes3sndC47Corelib4Init9Datatypes4andbC69OSSVerify5KrLib2K53A029Bi_topkit@in_zz_of_existsbC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A028RT_iface8ACC_LITSC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List7forallbC69OSSVerify5KrLib2K53A029Bi_topkitGforall_in_zl_of_forallbC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A029RT_traces@DESTROY_FREE_RASC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A028Bi_iface>RA_PBG_DESTROYC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A028Bi_iface;BD_FREE_RASC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A028Bi_iface=BC_CALLOC_RASC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A028Bi_iface<PIXA_CALLOC1C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A028Bi_iface;PGLP_CALLOCC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A028Bi_iface>RA_BC_LINEPTRSC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A029Bi_iface2=RA_BC_DESTROYC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A029Pm_iface2>PMCOPY_CALLOC1C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A029Bi_iface29RA_BC_AMBC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2K53A026Bi_top3AFtC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2K53A026Bi_topDT_pixDeserialize_cpsC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2K53A026Bi_topAT_pixCopy_nn_cpsFC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2K53A026Bi_topCT_pixBilateral_cps2C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2K53A026Bi_topMT_pixBlockBilateralExact_cps2C1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2K53A026Bi_topAT_pixDestroy_cpsFC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2K53A026Bi_topFT_pixDestroy_null_cpsFC1?~~~~~~~~~~~~~~~".
(* [comment removed for export] *)
Section Top.
Variable RT : RT_iface.rt_sig.
Hypothesis RC : RT_iface.rt_contracts RT.
Hypothesis GP : RT_gaps_iface.rt_gaps RT.
Hypothesis FKC : RT_fk_iface.rt_fk_contracts RT.
Definition AFt : RT_iface.art_facts RT := RT_iface.rc_facts RT RC.
Lemma L_tr_1 : In [786576] RT_traces.CLIENT_TRACES.
Proof.
ltac2:(KReplay.run1 (kr_t_Bi_top ()) ["Top"] "p;1p;3p;2g0000j11Tg000Uj14Tg0013j13Tg001Sj3;Tg0023j2:Tg002Mj19Tg002mj15Tg003ij36Tg004Ej37Tg004_j38Tg005ej12Tf0#2#2p=0g006JR0g006h#1#0#0#0#0#0#1#0#1#0#0#4%303;R1g007MR2g008PR3g0090R4':%90%51;62=734d38o"). Qed.
Lemma L_tr_2 : In [786984] RT_traces.CLIENT_TRACES.
Proof.
ltac2:(KReplay.run1 (kr_t_Bi_top ()) ["Top"] "p;1p;3p;2g0000j12Tg005ej11Tg000Uj13Tg0013j1;Tg001Sj3:Tg0023j29Tg002Mj14Tg002mj15Tg003ij36Tg004Ej37Tg004_j38Tf0#1#1p=0g006JR0g006h#2#0#0#0#0#2#1#0#2#1#2#1#0#3%;03:R1g007MR2g008PR3g0090R4'9%40%51;62=734d38o"). Qed.
Lemma L_tr_3 : In [787008] RT_traces.CLIENT_TRACES.
Proof.
ltac2:(KReplay.run1 (kr_t_Bi_top ()) ["Top"] "p;1p;3p;2g0000j11Tg000Uj14Tg0013j13Tg001Sj3;Tg0023j2:Tg002Mj19Tg002mj15Tg003ij36Tg004Ej37Tg004_j38Tg005ej12Tf0#2#2p=0g006JR0g006h#1#0#0#0#0#1#0#1#0#0#0#4%303;R1g007MR2g008PR3g0090R4':%90%51;62=734d38o"). Qed.
Lemma L_lit_156512 : (exists l : Z, In (156384, l) RT_gaps_iface.LEPT_LITS).
Proof.
ltac2:(KReplay.run1 (kr_t_Bi_top ()) ["Top"] "h01pp;1p;2p;3g005ej10Tg0000j11Tg000Uj13Tg0023j22Tg009Pj29Tg00:0j38Tg00:Mj27Tg003ij34Tg004Ej35Tg00:jj36Tg006h#0#0#1#1#0#0#0#1#0#1#1#1#0#0#0#0#0#3R0g00<1R1g008PR2g0090R3'2g006JR4/94R5f09844/70X05;41=523d36o"). Qed.
Lemma L_lit_156544 : (exists l : Z, In (156416, l) RT_gaps_iface.LEPT_LITS).
Proof.
ltac2:(KReplay.run1 (kr_t_Bi_top ()) ["Top"] "h01pp;1p;2p;3g0000j11Tg005ej12Tg000Uj13Tg0023j2:Tg009Pj29Tg00:0j38Tg00:Mj24Tg003ij35Tg004Ej36Tg00:jj37Tf0R0#2#2p=0g006h#0#1#1#2#0#1#1#0#0#0#0#3R1g00<1R2g008PR3g0090R4':g006JR5/95R6A8550/41X06;52=634d37o"). Qed.
Lemma L_lit_166816 : (exists l : Z, In (166560, l) RT_gaps_iface.LEPT_LITS).
Proof.
ltac2:(KReplay.run1 (kr_t_Bi_top ()) ["Top"] "h01pp;1p;2p;3g005ej10Tg0000j11Tg000Uj13Tg0023j22Tg009Pj29Tg00:0j38Tg00:Mj27Tg003ij34Tg004Ej35Tg00:jj36Tg006h#0#1#0#0#0#1#0#1#0#1#0#1#0#0#0#0#0#3R0g00<1R1g008PR2g0090R3'2g006JR4/94R5f09844/70X05;41=523d36o"). Qed.
Lemma L_lit_166880 : (exists l : Z, In (166624, l) RT_gaps_iface.LEPT_LITS).
Proof.
ltac2:(KReplay.run1 (kr_t_Bi_top ()) ["Top"] "h01pp;1p;2p;3g005ej10Tg0000j11Tg000Uj13Tg0023j22Tg009Pj29Tg00:0j38Tg00:Mj27Tg003ij34Tg004Ej35Tg00:jj36Tg006h#0#1#0#0#0#1#0#1#0#1#1#1#0#0#0#0#0#3R0g00<1R1g008PR2g0090R3'2g006JR4/94R5f09844/70X05;41=523d36o"). Qed.
Lemma L_acc_167296_132 : In (167008, 132) RT_iface.ACC_LITS.
Proof.
ltac2:(KReplay.run1 (kr_t_Bi_top ()) ["Top"] "h01pp;1p;4p;2p;3g005ej12Tg0000j11Tg000Uj16Tg00=4j4=Tg0023j2;Tg009Pj2:Tg00:0j34Tg00:Mj23Tg00=Tj35Tg00>1j27Tg003ij38Tg004Ej39Tg00>Oj3<Tf0R0#2#2p=0g006JR1P1g006hR2#2#1#2#0#1#1#2#0#1#1#2#0#0#6%02#0#1#0#6C=R2g00?UR3g008PR4g0090R5';1:11R6A4110A4112'3A5110A5112'3'7X06;83=945d3<o"). Qed.
Lemma L_acc_167488_132 : In (167200, 132) RT_iface.ACC_LITS.
Proof.
ltac2:(KReplay.run1 (kr_t_Bi_top ()) ["Top"] "h01pp;1p;4p;2p;3g005ej12Tg0000j11Tg000Uj16Tg00=4j4=Tg0023j2;Tg009Pj2:Tg00:0j34Tg00:Mj23Tg00=Tj35Tg00>1j27Tg003ij38Tg004Ej39Tg00>Oj3<Tf0R0#2#2p=0g006JR1P1g006hR2#2#1#2#0#1#1#2#1#0#1#2#0#0#6%02#0#1#0#6C=R2g00?UR3g008PR4g0090R5';1:11R6A4110A4112'3A5110A5112'3'7X06;83=945d3<o"). Qed.
Lemma L_tr_10 : In [787496] RT_traces.CLIENT_TRACES.
Proof.
ltac2:(KReplay.run1 (kr_t_Bi_top ()) ["Top"] "p;1p;3p;2g0000j12Tg005ej11Tg000Uj13Tg0013j1;Tg001Sj3:Tg0023j29Tg002Mj14Tg002mj15Tg003ij36Tg004Ej37Tg004_j38Tf0#1#1p=0g006JR0g006h#2#1#0#0#0#2#0#0#2#1#2#1#0#3%;03:R1g007MR2g008PR3g0090R4'9%40%51;62=734d38o"). Qed.
Lemma L_tr_11 : In [787560] RT_traces.CLIENT_TRACES.
Proof.
ltac2:(KReplay.run1 (kr_t_Bi_top ()) ["Top"] "p;1p;3p;2g0000j12Tg005ej10Tg000Uj13Tg0013j1;Tg001Sj3:Tg0023j29Tg002Mj14Tg002mj15Tg003ij36Tg004Ej37Tg004_j38Tf0#0#0p=1g006JR0g006h#2#0#1#1#1#2#0#1#2#2#0#2#0#1#3%;03:R1g007MR2g008PR3g0090R4'9%40%51;62=734d38o"). Qed.
Lemma L_tr_12 : In [787568] RT_traces.CLIENT_TRACES.
Proof.
ltac2:(KReplay.run1 (kr_t_Bi_top ()) ["Top"] "p;1p;3p;2g0000j11Tg005ej12Tg000Uj13Tg0013j1;Tg001Sj3:Tg0023j29Tg002Mj14Tg002mj15Tg003ij36Tg004Ej37Tg004_j38Tf0#2#2p=0g006JR0g006h#1#2#0#0#0#1#2#0#1#1#1#0#0#3%;03:R1g007MR2g008PR3g0090R4'9%40%51;62=734d38o"). Qed.
Lemma L_lit_156832 : (exists l : Z, In (156704, l) RT_gaps_iface.LEPT_LITS).
Proof.
ltac2:(KReplay.run1 (kr_t_Bi_top ()) ["Top"] "h01pp;1p;2p;3g0000j11Tg005ej12Tg000Uj13Tg0023j2:Tg009Pj29Tg00:0j38Tg00:Mj24Tg003ij35Tg004Ej36Tg00:jj37Tf0R0#2#2p=0g006h#0#1#1#0#1#0#0#1#2#0#0#3R1g00<1R2g008PR3g0090R4':g006JR5/95R6A8550/41X06;52=634d37o"). Qed.
Lemma L_lit_156960 : (exists l : Z, In (156832, l) RT_gaps_iface.LEPT_LITS).
Proof.
ltac2:(KReplay.run1 (kr_t_Bi_top ()) ["Top"] "h01pp;1p;2p;3g005ej10Tg0000j11Tg000Uj13Tg0023j22Tg009Pj29Tg00:0j38Tg00:Mj27Tg003ij34Tg004Ej35Tg00:jj36Tg006h#0#0#1#1#0#0#1#0#0#1#0#1#0#0#0#0#0#3R0g00<1R1g008PR2g0090R3'2g006JR4/94R5f09844/70X05;41=523d36o"). Qed.
Lemma L_lit_157024 : (exists l : Z, In (156896, l) RT_gaps_iface.LEPT_LITS).
Proof.
ltac2:(KReplay.run1 (kr_t_Bi_top ()) ["Top"] "h01pp;1p;2p;3g005ej10Tg0000j11Tg000Uj13Tg0023j22Tg009Pj29Tg00:0j38Tg00:Mj27Tg003ij34Tg004Ej35Tg00:jj36Tg006h#0#0#1#1#0#0#1#0#0#1#1#1#0#0#0#0#0#3R0g00<1R1g008PR2g0090R3'2g006JR4/94R5f09844/70X05;41=523d36o"). Qed.
Lemma L_lit_156896 : (exists l : Z, In (156768, l) RT_gaps_iface.LEPT_LITS).
Proof.
ltac2:(KReplay.run1 (kr_t_Bi_top ()) ["Top"] "h01pp;1p;2p;3g0000j11Tg005ej12Tg000Uj13Tg0023j2:Tg009Pj29Tg00:0j38Tg00:Mj24Tg003ij35Tg004Ej36Tg00:jj37Tf0R0#2#2p=0g006h#0#1#1#0#1#2#0#1#1#2#0#0#3R1g00<1R2g008PR3g0090R4':g006JR5/95R6A8550/41X06;52=634d37o"). Qed.
Lemma L_tr_17 : In [618348] RT_traces.CLIENT_TRACES.
Proof.
ltac2:(KReplay.run1 (kr_t_Bi_top ()) ["Top"] "p;1p;3p;2g005ej11Tg0000j10Tg000Uj13Tg0013j12Tg001Sj3:Tg0023j29Tg002Mj18Tg002mj14Tg003ij35Tg004Ej36Tg004_j37Tg006JR0g006h#1#1#0#1#0#0#1#0#0#0#0#1#0#0#1#0#0#1#1#3%203:R1g007MR2g008PR3g0090R4'9%80%41;52=634d37o"). Qed.
Lemma L_tr_18 : In [625256] RT_traces.CLIENT_TRACES.
Proof.
ltac2:(KReplay.run1 (kr_t_Bi_top ()) ["Top"] "p;1p;3p;2g005ej10Tg0000j11Tg000Uj13Tg0013j12Tg001Sj3:Tg0023j29Tg002Mj18Tg002mj14Tg003ij35Tg004Ej36Tg004_j37Tg006JR0g006h#0#0#1#1#0#0#0#1#0#1#0#0#1#1#0#1#0#0#0#3%203:R1g007MR2g008PR3g0090R4'9%80%41;52=634d37o"). Qed.
Lemma L_tr_19 : In [641736] RT_traces.CLIENT_TRACES.
Proof.
ltac2:(KReplay.run1 (kr_t_Bi_top ()) ["Top"] "p;1p;3p;2g005ej10Tg0000j11Tg000Uj13Tg0013j12Tg001Sj3:Tg0023j29Tg002Mj18Tg002mj14Tg003ij35Tg004Ej36Tg004_j37Tg006JR0g006h#0#0#1#1#1#0#0#1#0#1#0#1#1#0#0#1#0#0#0#3%203:R1g007MR2g008PR3g0090R4'9%80%41;52=634d37o"). Qed.
Lemma L_lit_176736 : (exists l : Z, In (176224, l) RT_gaps_iface.LEPT_LITS).
Proof.
ltac2:(KReplay.run1 (kr_t_Bi_top ()) ["Top"] "h01pp;1p;2p;3g005ej10Tg0000j11Tg000Uj13Tg0023j2:Tg009Pj29Tg00:0j38Tg00:Mj24Tg003ij35Tg004Ej36Tg00:jj37Tf0R0#0#0p=2g006h#0#1#0#1#1#0#2#2#1#1#0#2#2#3R1g00<1R2g008PR3g0090R4':g006JR5/95R6A8550/41X06;52=634d37o"). Qed.
Lemma L_lit_176704 : (exists l : Z, In (176192, l) RT_gaps_iface.LEPT_LITS).
Proof.
ltac2:(KReplay.run1 (kr_t_Bi_top ()) ["Top"] "h01pp;1p;2p;3g005ej10Tg0000j12Tg000Uj13Tg0023j2:Tg009Pj29Tg00:0j38Tg00:Mj24Tg003ij35Tg004Ej36Tg00:jj37Tf0R0#0#0p=1g006h#0#2#0#2#2#0#1#1#2#1#1#1#3R1g00<1R2g008PR3g0090R4':g006JR5/95R6A8550/41X06;52=634d37o"). Qed.
Lemma L_tr_22 : In [619260] RT_traces.CLIENT_TRACES.
Proof.
ltac2:(KReplay.run1 (kr_t_Bi_top ()) ["Top"] "p;1p;3p;2g005ej11Tg0000j10Tg000Uj13Tg0013j12Tg001Sj3:Tg0023j29Tg002Mj18Tg002mj14Tg003ij35Tg004Ej36Tg004_j37Tg006JR0g006h#1#1#0#1#0#0#0#1#1#0#1#0#0#0#0#0#0#1#1#3%203:R1g007MR2g008PR3g0090R4'9%80%41;52=634d37o"). Qed.
Lemma L_tr_23 : In [619276] RT_traces.CLIENT_TRACES.
Proof.
ltac2:(KReplay.run1 (kr_t_Bi_top ()) ["Top"] "p;1p;3p;2g005ej10Tg0000j11Tg000Uj13Tg0013j12Tg001Sj3:Tg0023j29Tg002Mj18Tg002mj14Tg003ij35Tg004Ej36Tg004_j37Tg006JR0g006h#0#0#1#0#1#1#1#0#0#1#1#0#0#0#0#1#1#0#0#3%203:R1g007MR2g008PR3g0090R4'9%80%41;52=634d37o"). Qed.
Lemma L_trf_24 : Forall (fun f : Z => In [f; 619092] RT_traces.CLIENT_TRACES) RT_traces.DESTROY_FREE_RAS.
Proof.
ltac2:(KReplay.run1 (kr_t_Bi_top ()) ["Top"] "h01fp;1p;3p;2p;4g005ej10Tg0000j11Tg000Uj14Tg0013j13Tg001Sj32Tg0023j2;Tg002Mj1:Tg002mj15Tg003ij36Tg00@Rj37Tg004Ej38Tg00@nj49Tg006JR0f0g006h#0#0#1#0#1#1#1#0#0#1#0#0#1#0#1#0#1#0#0#4%30520520R1W0g007MR2g00B;R3g008PR4g0090R5';%:0%51;62X00=703=845dC9o"). Qed.
Lemma L_trf_25 : Forall (fun f : Z => In [f; Bi_iface.RA_PBG_DESTROY] RT_traces.CLIENT_TRACES) Bi_iface.BD_FREE_RAS.
Proof.
ltac2:(KReplay.run1 (kr_t_Bi_top ()) ["Top"] "h01fp;1p;3p;2p;4g0013j18Tg001Sj30Tg0023j22Tg002Mj11Tg002mj17Tg003ij36Tg00@Rj33Tg004Ej34Tg00@nj45Tg006JR0f0g00CA%80500500R1W0g007MR2g00DDR3g008PR4g0090R5'2%10%71;62X00=303=445dC5o"). Qed.
Lemma L_trf_26 : Forall (fun f : Z => In [f; 802420; Bi_iface.RA_PBG_DESTROY] RT_traces.CLIENT_TRACES) RT_traces.DESTROY_FREE_RAS.
Proof.
ltac2:(KReplay.run1 (kr_t_Bi_top ()) ["Top"] "h01fp;1p;3p;2p;4g0000j10Tg005ej11Tg000Uj14Tg0013j13Tg001Sj32Tg0023j2;Tg002Mj1:Tg002mj15Tg003ij36Tg00@Rj37Tg004Ej38Tg00@nj49Tg006JR0f0g006h#0#1#1#1#1#0#0#0#0#0#1#1#0#0#0#1#0#1#1#4g00CA%30520520520R1W0g007MR2g00B;R3g008PR4g0090R5';%:0%51;62X00=703=845dC9o"). Qed.
Lemma L_lit_175680 : (exists l : Z, In (175168, l) RT_gaps_iface.LEPT_LITS).
Proof.
ltac2:(KReplay.run1 (kr_t_Bi_top ()) ["Top"] "h01pp;1p;2p;3g005ej10Tg0000j11Tg000Uj13Tg0023j22Tg009Pj29Tg00:0j38Tg00:Mj27Tg003ij34Tg004Ej35Tg00:jj36Tg006h#0#1#0#1#0#1#1#0#0#0#1#0#0#0#0#0#0#3R0g00<1R1g008PR2g0090R3'2g006JR4/94R5f09844/70X05;41=523d36o"). Qed.
Lemma L_lit_175552 : (exists l : Z, In (175040, l) RT_gaps_iface.LEPT_LITS).
Proof.
ltac2:(KReplay.run1 (kr_t_Bi_top ()) ["Top"] "h01pp;1p;2p;3g005ej10Tg0000j11Tg000Uj13Tg0023j22Tg009Pj29Tg00:0j38Tg00:Mj27Tg003ij34Tg004Ej35Tg00:jj36Tg006h#0#1#0#1#0#1#0#1#1#1#1#0#0#0#0#0#0#3R0g00<1R1g008PR2g0090R3'2g006JR4/94R5f09844/70X05;41=523d36o"). Qed.
Lemma L_trf_29 : Forall (fun f : Z => In [f; 796368] RT_traces.CLIENT_TRACES) Bi_iface.BC_CALLOC_RAS.
Proof.
ltac2:(KReplay.run1 (kr_t_Bi_top ()) ["Top"] "h01fp;1p;3p;2p;4g0000j11Tg005ej10Tg000Uj14Tg0013j13Tg001Sj32Tg0023j2;Tg002Mj1:Tg002mj15Tg003ij36Tg00@Rj37Tg004Ej38Tg00@nj49Tg006JR0f0g006h#1#0#0#0#0#1#0#0#1#1#0#1#1#0#1#0#0#0#0#4%30520520R1W0g007MR2g00EDR3g008PR4g0090R5';%:0%51;62X00=703=845dC9o"). Qed.
Lemma L_tr_30 : In [Bi_iface.PIXA_CALLOC1; 796368] RT_traces.CLIENT_TRACES.
Proof.
ltac2:(KReplay.run1 (kr_t_Bi_top ()) ["Top"] "p;1p;3p;2g0000j11Tg005ej10Tg000Uj14Tg0013j13Tg001Sj32Tg0023j2:Tg002Mj19Tg002mj15Tg003ij36Tg004Ej37Tg004_j38Tg006JR0g00FFg006h#1#0#0#0#0#1#0#0#1#1#0#1#1#0#1#0#0#0#0#4%3052032R1g007MR2g008PR3g0090R4':%90%51;62=734d38o"). Qed.
Lemma L_tr_31 : In [Bi_iface.PGLP_CALLOC; Bi_iface.RA_BC_LINEPTRS; 796368] RT_traces.CLIENT_TRACES.
Proof.
ltac2:(KReplay.run1 (kr_t_Bi_top ()) ["Top"] "p;1p;3p;2g0000j11Tg005ej10Tg000Uj14Tg0013j13Tg001Sj32Tg0023j2:Tg002Mj19Tg002mj15Tg003ij36Tg004Ej37Tg004_j38Tg006JR0g00GGg00HGg006h#1#0#0#0#0#1#0#0#1#1#0#1#1#0#1#0#0#0#0#4%3052052032R1g007MR2g008PR3g0090R4':%90%51;62=734d38o"). Qed.
Lemma L_trf_32 : Forall (fun f : Z => In [f; Bi_iface2.RA_BC_DESTROY; 796368] RT_traces.CLIENT_TRACES) RT_traces.DESTROY_FREE_RAS.
Proof.
ltac2:(KReplay.run1 (kr_t_Bi_top ()) ["Top"] "h01fp;1p;3p;2p;4g0000j11Tg005ej10Tg000Uj14Tg0013j13Tg001Sj32Tg0023j2;Tg002Mj1:Tg002mj15Tg003ij36Tg00@Rj37Tg004Ej38Tg00@nj49Tg006JR0f0g00IJg006h#1#0#0#0#0#1#0#0#1#1#0#1#1#0#1#0#0#0#0#4%30520520520R1W0g007MR2g00B;R3g008PR4g0090R5';%:0%51;62X00=703=845dC9o"). Qed.
Lemma L_tr_33 : In [Pm_iface2.PMCOPY_CALLOC1; 651260; 652488; Bi_iface2.RA_BC_AMB; 796368] RT_traces.CLIENT_TRACES.
Proof.
ltac2:(KReplay.run1 (kr_t_Bi_top ()) ["Top"] "p;1p;3p;2g005ej12Tg000Uj17Tg0000j13Tg0013j1<Tg001Sj34Tg0023j2;Tg002Mj18Tg002mj19Tg003ij3:Tg004Ej3>Tg004_j3=Tf0R0#2#3p=5%30#3p=0%30#2p=6%20#2p=1g006JR0g00JMg006hR1#2#5#0#6#0#0#0#0#0#1#7%21#5#0#0#5#1#0#1#6#1#7g00KQ%31#1#1#6#5#6#0#5#1#1#7%<054054054054034R1g007MR2g008PR3g0090R4';%80%91;:2=>34d3=o"). Qed.
Definition T_lept_stderr_cps : Lept_iface.lept_stderr_cps RT :=
  Lept_stderr.lept_stderr_ok RT AFt RC GP FKC.
Definition T_lept_stderr_cpsF : Bi_fktw.lept_stderr_cpsF RT :=
  Lept_stderr.lept_stderr_okF RT AFt RC GP FKC.
Definition T_returnError_cps_e_returnErrorPtr : Lept_iface.returnError_cps RT Lept_iface.e_returnErrorPtr :=
  Lept_err.returnError_ok RT AFt GP T_lept_stderr_cpsF Lept_iface.e_returnErrorPtr (or_intror eq_refl).
Definition T_returnError_cpsF_e_returnErrorPtr : Bi_fktw.returnError_cpsF RT Lept_iface.e_returnErrorPtr :=
  Lept_err.returnError_okF RT AFt GP T_lept_stderr_cpsF Lept_iface.e_returnErrorPtr (or_intror eq_refl).
Definition T_pixCreateHeader_cps : Lept_iface.pixCreateHeader_cps RT :=
  Lept_hdr.pixCreateHeader_ok RT AFt GP FKC T_lept_stderr_cpsF T_returnError_cpsF_e_returnErrorPtr.
Definition T_pixCreateHeader_cpsF : Bi_fktw.pixCreateHeader_cpsF RT :=
  Lept_hdr.pixCreateHeader_okF RT AFt GP FKC T_lept_stderr_cpsF T_returnError_cpsF_e_returnErrorPtr.
Definition T_returnError_cpsF_e_returnErrorInt : Bi_fktw.returnError_cpsF RT Lept_iface.e_returnErrorInt :=
  Lept_err.returnError_okF RT AFt GP T_lept_stderr_cpsF Lept_iface.e_returnErrorInt (or_introl eq_refl).
Definition T_pixSetPadBits_cpsF : Bi_fktw.pixSetPadBits_cpsF RT :=
  LeptC_padbits.pixSetPadBits_okF RT AFt GP FKC T_lept_stderr_cpsF T_returnError_cpsF_e_returnErrorInt.
Definition T_pixCreate_cps : Lept_iface.pixCreate_cps RT :=
  Lept_create.pixCreate_ok RT AFt RC GP FKC T_pixCreateHeader_cpsF T_pixSetPadBits_cpsF T_returnError_cpsF_e_returnErrorPtr.
Definition T_pixcmapDestroy_cpsF : Bi_fktw.pixcmapDestroy_cpsF RT :=
  LeptC_cmapdestroy.pixcmapDestroy_okF RT AFt GP FKC.
Definition T_pixDestroy_cps : Lept_iface.pixDestroy_cps RT :=
  LeptM_destroy.pixDestroy_ok RT AFt GP FKC T_pixcmapDestroy_cpsF.
Definition T_pixcmapDeserialize_cps : Lept_iface.pixcmapDeserialize_cps RT :=
  LeptC_cmapdeser.pixcmapDeserialize_ok RT AFt GP.
Definition T_returnError_cps_e_returnErrorInt : Lept_iface.returnError_cps RT Lept_iface.e_returnErrorInt :=
  Lept_err.returnError_ok RT AFt GP T_lept_stderr_cpsF Lept_iface.e_returnErrorInt (or_introl eq_refl).
Definition T_pixZero_cpsF : LeptF_iface.pixZero_cpsF RT :=
  Lept_zero.pixZero_okF RT AFt GP.
Definition T_pixGetMaxColorIndex_cpsF : LeptF_iface.pixGetMaxColorIndex_cpsF RT :=
  Lept_gmax.pixGetMaxColorIndex_okF RT AFt GP FKC T_pixZero_cpsF.
Definition T_pixcmapIsValid_cps : Lept_iface.pixcmapIsValid_cps RT :=
  LeptC_cmapvalid.pixcmapIsValid_ok RT AFt GP FKC T_lept_stderr_cpsF T_returnError_cpsF_e_returnErrorInt T_pixGetMaxColorIndex_cpsF.
Definition T_pixSetColormap_cps : Lept_iface.pixSetColormap_cps RT :=
  LeptC_setcmap.pixSetColormap_ok RT AFt GP T_returnError_cps_e_returnErrorInt T_pixcmapIsValid_cps.
Definition T_pixDeserialize_cps : Lept_iface.pixDeserialize_cps RT :=
  Lept_deser.pixDeserialize_ok RT AFt RC GP T_lept_stderr_cps T_returnError_cps_e_returnErrorPtr T_pixCreateHeader_cps T_pixCreate_cps T_pixDestroy_cps T_pixcmapDeserialize_cps T_pixSetColormap_cps T_pixcmapIsValid_cps.
Definition T_pixCreateHeader_nn_cpsF : Bi_fktw.pixCreateHeader_nn_cpsF RT :=
  Pm_hdr2.pixCreateHeader_nn_okF RT AFt GP FKC.
Definition T_pixCreateNoInit_nn_cpsF_e_pixCreateNoInit_PM_NOINIT_MALLOC : Bi_fktw.pixCreateNoInit_nn_cpsF RT Lept_iface.e_pixCreateNoInit Pm_iface2.PM_NOINIT_MALLOC :=
  Pm_noinit.pixCreateNoInit_okF RT AFt GP FKC T_pixCreateHeader_nn_cpsF T_pixSetPadBits_cpsF.
Definition T_pixcmapIsValid_cpsF : Bi_fktw.pixcmapIsValid_cpsF RT :=
  LeptC_cmapvalid.pixcmapIsValid_okF RT AFt GP FKC T_lept_stderr_cpsF T_returnError_cpsF_e_returnErrorInt T_pixGetMaxColorIndex_cpsF.
Definition T_pixcmapIsValid_stk_cpsF : Bi_fktw.pixcmapIsValid_stk_cpsF RT :=
  Pm_cmapvalid_stk.pixcmapIsValid_stk_okF RT AFt GP FKC.
Definition T_pixcmapCopy_cpsF : Bi_fktw.pixcmapCopy_cpsF RT :=
  Pm_cmapcopy.pixcmapCopy_okF RT AFt RC GP FKC T_pixcmapIsValid_stk_cpsF T_returnError_cpsF_e_returnErrorPtr.
Definition T_pixCopyColormap_cpsF : Bi_fktw.pixCopyColormap_cpsF RT :=
  Pm_copycmap.pixCopyColormap_okF RT AFt GP FKC T_returnError_cpsF_e_returnErrorInt T_pixcmapIsValid_cpsF T_pixcmapCopy_cpsF.
Definition T_stringReplace_null_cpsF : Bi_fktw.stringReplace_null_cpsF RT :=
  Pm_strrepl.stringReplace_null_okF RT AFt GP.
Definition T_pixCreateTemplateNoInit_nn_cpsF : Bi_fktw.pixCreateTemplateNoInit_nn_cpsF RT :=
  Pm_tmpl.pixCreateTemplateNoInit_okF RT AFt GP T_pixCreateNoInit_nn_cpsF_e_pixCreateNoInit_PM_NOINIT_MALLOC T_pixCopyColormap_cpsF T_stringReplace_null_cpsF T_pixSetPadBits_cpsF T_returnError_cpsF_e_returnErrorInt.
Definition T_pixCopy_nn_cpsF : Bi_fktw.pixCopy_nn_cpsF RT :=
  Pm_copy.pixCopy_okF RT AFt RC GP FKC T_pixCreateTemplateNoInit_nn_cpsF.
Definition T_kernelCreate_cpsF : Bi_fktw.kernelCreate_cpsF RT :=
  Km_create.kernelCreate_okF RT AFt GP FKC L_tr_1 L_tr_2 L_tr_3.
Definition T_expf_cps : Bi_iface.expf_cps RT :=
  Bi_expf.expf_ok RT AFt GP.
Definition T_makeGaussianKernel_cps : Bi_iface.makeGaussianKernel_cps RT :=
  Bi_gausskernel.makeGaussianKernel_ok RT AFt GP FKC T_kernelCreate_cpsF T_expf_cps.
Definition T_kernelSetOrigin_cps : Bi_iface.kernelSetOrigin_cps RT :=
  Bi_setorigin.kernelSetOrigin_ok RT AFt GP.
Definition T_kernelSetElement_cpsF : Bi_fktw.kernelSetElement_cpsF RT :=
  Km_setelemF.kernelSetElement_okF RT AFt GP.
Definition T_makeRangeKernel_cps : Bi_iface.makeRangeKernel_cps RT :=
  Bi_rangekernel.makeRangeKernel_ok RT AFt GP FKC T_kernelCreate_cpsF T_kernelSetOrigin_cps T_expf_cps T_kernelSetElement_cpsF.
Definition T_kernelGetParameters_cps : Bi_iface.kernelGetParameters_cps RT :=
  Bi_getpars.kernelGetParameters_ok RT AFt GP.
Definition T_kernelInvert_cps : Bi_iface.kernelInvert_cps RT :=
  Bi_kinvert.kernelInvert_ok RT AFt GP FKC T_kernelCreate_cpsF.
Definition T_pixCreate_cpsF : Bi_fktw.pixCreate_cpsF RT :=
  Lept_create.pixCreate_okF RT AFt RC GP FKC T_pixCreateHeader_cpsF T_pixSetPadBits_cpsF T_returnError_cpsF_e_returnErrorPtr.
Definition T_pixCopyResolution_cps : Bi_iface.pixCopyResolution_cps RT :=
  Bi_copyres.pixCopyResolution_ok RT AFt GP.
Definition T_pixRasterop_cps2 : Bi_iface2.pixRasterop_cps2 RT :=
  Bi_rasterop.pixRasterop_ok RT AFt GP FKC T_returnError_cpsF_e_returnErrorInt L_lit_166816 L_lit_166880 L_acc_167296_132 L_acc_167488_132.
Definition T_pixAddBorderGeneral0_cps2 : Bi_iface2.pixAddBorderGeneral0_cps2 RT :=
  Bi_border.pixAddBorderGeneral0_ok RT AFt GP FKC T_returnError_cpsF_e_returnErrorPtr L_lit_156512 L_lit_156544 T_pixCreate_cpsF T_pixCopyResolution_cps T_pixCopyColormap_cpsF T_pixRasterop_cps2.
Definition T_pixRasterop_null_cps2 : Bi_ropn_defs.pixRasterop_null_cps2 RT :=
  Bi_ropn.pixRasterop_null_ok RT AFt GP FKC T_returnError_cpsF_e_returnErrorInt L_lit_166816 L_lit_166880.
Definition T_pixAddMirroredBorder_cps2 : Bi_iface2.pixAddMirroredBorder_cps2 RT :=
  Bi_mborder.pixAddMirroredBorder_ok RT AFt GP FKC T_pixAddBorderGeneral0_cps2 T_pixRasterop_cps2 T_pixRasterop_null_cps2.
Definition T_pixCreate_nn_cpsF : Bi_iface2.pixCreate_nn_cpsF RT :=
  Bi_pixcreate_nn.pixCreate_nn_ok RT AFt GP FKC T_pixCreateNoInit_nn_cpsF_e_pixCreateNoInit_PM_NOINIT_MALLOC.
Definition T_kernelDestroy_cpsF : Bi_fktw.kernelDestroy_cpsF RT :=
  Km_destroy.kernelDestroy_okF RT AFt GP FKC L_tr_10 L_tr_11 L_tr_12.
Definition T_pixDestroy_cpsF : Bi_fktw.pixDestroy_cpsF RT :=
  LeptM_destroy.pixDestroy_okF RT AFt GP FKC T_pixcmapDestroy_cpsF.
Definition T_pixBilateralGrayExact_cps2 : Bi_iface2.pixBilateralGrayExact_cps2 RT :=
  Bi_bgexact.pixBilateralGrayExact_ok RT AFt GP FKC T_kernelGetParameters_cps T_kernelInvert_cps T_pixAddMirroredBorder_cps2 T_pixCreate_nn_cpsF T_pixCopy_nn_cpsF T_kernelDestroy_cpsF T_pixDestroy_cpsF T_lept_stderr_cpsF T_returnError_cpsF_e_returnErrorPtr.
Definition T_pixGetRGBComponent_cps : Bi_iface.pixGetRGBComponent_cps RT :=
  Bi_getrgb.pixGetRGBComponent_ok RT AFt GP FKC T_pixCreate_nn_cpsF T_pixCopyResolution_cps.
Definition T_pixSetRGBComponent_cps2 : Bi_rgb_defs.pixSetRGBComponent_cps2 RT :=
  Bi_setrgb.pixSetRGBComponent_ok RT AFt GP FKC.
Definition T_pixCreateRGBImage_cps : Bi_iface.pixCreateRGBImage_cps RT :=
  Bi_crgb.pixCreateRGBImage_ok RT AFt GP FKC T_returnError_cpsF_e_returnErrorPtr L_lit_156832 L_lit_156960 L_lit_157024 L_lit_156896 L_lit_156512 T_pixCreate_cpsF T_pixCopyResolution_cps T_pixSetRGBComponent_cps2.
Definition T_pixDestroy_null_cpsF : Bi_fktw.pixDestroy_null_cpsF RT :=
  CfY_pixdestroy_null.pixDestroy_null_okF RT AFt GP FKC.
Definition T_pixBilateralExact_cps2 : Bi_iface3.pixBilateralExact_cps2 RT :=
  Bi_bexact.pixBilateralExact_ok RT AFt GP FKC T_pixBilateralGrayExact_cps2 T_pixGetRGBComponent_cps T_pixCreateRGBImage_cps T_pixDestroy_cpsF T_pixDestroy_null_cpsF T_returnError_cpsF_e_returnErrorPtr.
Definition T_pixBlockBilateralExact_cps2 : Bi_iface3.pixBlockBilateralExact_cps2 RT :=
  Bi_bbexact.pixBlockBilateralExact_ok RT AFt GP FKC T_makeGaussianKernel_cps T_makeRangeKernel_cps T_pixBilateralExact_cps2 T_kernelDestroy_cpsF T_returnError_cpsF_e_returnErrorPtr.
Definition T_pixClone_cpsF : Bi_fktw.pixClone_cpsF RT :=
  Cf_clone.pixClone_okF RT AFt GP.
Definition T_pixGetExtremeValue_cps : Bi_iface.pixGetExtremeValue_cps RT :=
  Bi_getextreme.pixGetExtremeValue_ok RT AFt GP FKC.
Definition T_pixDestroy_rc_cpsF : Bi_fktw.pixDestroy_rc_cpsF RT :=
  CfY_pixdestroy_rc.pixDestroy_rc_okF RT AFt GP FKC.
Definition T_boxaCreate_cpsF : Bi_fktw.boxaCreate_cpsF RT :=
  Cf_boxacreate.boxaCreate_okF RT AFt GP FKC.
Definition T_pixaCreate_n_cps : Bi_iface.pixaCreate_n_cps RT :=
  Bi_pixacreate.pixaCreate_n_ok RT AFt GP FKC T_boxaCreate_cpsF L_tr_17 L_tr_18.
Definition T_pixaAddPix_ins_cps : Bi_iface.pixaAddPix_ins_cps RT :=
  Bi_addpix.pixaAddPix_ins_ok RT AFt GP FKC.
Definition T_pixaGetPix_clone_cps : Bi_iface.pixaGetPix_clone_cps RT :=
  Bi_getpix.pixaGetPix_clone_ok RT AFt GP T_pixClone_cpsF.
Definition T_pixaGetPixDimensions_cps : Bi_iface.pixaGetPixDimensions_cps RT :=
  Bi_getdims.pixaGetPixDimensions_ok RT AFt GP FKC T_pixaGetPix_clone_cps T_pixDestroy_rc_cpsF.
Definition T_pixaVerifyDepth_cps : Bi_iface.pixaVerifyDepth_cps RT :=
  Bi_verifydepth.pixaVerifyDepth_ok RT AFt GP FKC T_pixaGetPixDimensions_cps.
Definition T_pixGetLinePtrs_cps : Bi_iface.pixGetLinePtrs_cps RT :=
  Bi_lineptrs.pixGetLinePtrs_ok RT AFt GP FKC L_tr_19.
Definition T_pixaGetLinePtrs_cps : Bi_iface.pixaGetLinePtrs_cps RT :=
  Bi_pixalineptrs.pixaGetLinePtrs_ok RT AFt GP FKC T_pixaVerifyDepth_cps T_pixaGetPix_clone_cps T_pixGetLinePtrs_cps T_pixDestroy_rc_cpsF.
Definition T_bc_nc_loop_stmt : Bi_bcreate_defs.bc_nc_loop_stmt :=
  Bi_bcreate_ncloop.bc_nc_loop_ok.
Definition T_bc_kidx_stmt : Bi_bcreate_defs.bc_kidx_stmt :=
  Bi_bcreate_kidxloop.bc_kidx_ok.
Definition T_bc_kfr_stmt : Bi_bcreate_defs.bc_kfr_stmt :=
  Bi_bcreate_kfrloop.bc_kfr_ok.
Definition T_bc_hpass_stmt : Bi_bcreate_defs2.bc_hpass_stmt :=
  Bi_bcreate_hpass.bc_hpass_ok.
Definition T_bc_vpass_stmt : Bi_bcreate_defs2.bc_vpass_stmt :=
  Bi_bcreate_vpass.bc_vpass_ok.
Definition T_bc_cutB320_stmt : Bi_bcreate_cut2.bc_cutB320_stmt RT :=
  Bi_bcreate_c.bc_cutB320_ok RT AFt GP FKC T_pixClone_cpsF T_pixAddMirroredBorder_cps2 T_pixGetExtremeValue_cps T_pixDestroy_rc_cpsF T_pixDestroy_cpsF T_returnError_cpsF_e_returnErrorPtr T_expf_cps T_pixaCreate_n_cps T_pixCopy_nn_cpsF T_pixCreate_nn_cpsF T_pixaAddPix_ins_cps T_pixaGetLinePtrs_cps T_bc_hpass_stmt T_bc_vpass_stmt L_lit_176736 L_lit_176704.
Definition T_bc_cutA320_stmt : Bi_bcreate_cut.bc_cutA320_stmt RT :=
  Bi_bcreate_b.bc_cutA320_ok RT AFt GP FKC T_expf_cps T_pixaCreate_n_cps T_bc_cutB320_stmt.
Definition T_bc_twin336_stmt : Bi_bcreate_cut.bc_twin336_stmt RT :=
  Bi_bcreate_336.bc_twin336_full RT AFt GP FKC T_pixClone_cpsF T_pixAddMirroredBorder_cps2 T_pixGetExtremeValue_cps T_pixDestroy_rc_cpsF T_pixDestroy_cpsF T_returnError_cpsF_e_returnErrorPtr T_expf_cps T_pixaCreate_n_cps T_pixCopy_nn_cpsF T_pixCreate_nn_cpsF T_pixaAddPix_ins_cps T_pixaGetLinePtrs_cps L_lit_176736 L_lit_176704 T_bc_nc_loop_stmt T_bc_kidx_stmt T_bc_kfr_stmt T_bc_hpass_stmt T_bc_vpass_stmt.
Definition T_bilateralCreate_cps2 : Bi_iface2.bilateralCreate_cps2 RT :=
  Bi_bcreate_a.bilateralCreate_ok RT AFt GP FKC T_pixClone_cpsF T_pixAddMirroredBorder_cps2 T_pixGetExtremeValue_cps T_pixDestroy_rc_cpsF T_pixDestroy_cpsF T_returnError_cpsF_e_returnErrorPtr T_expf_cps T_pixaCreate_n_cps T_pixCopy_nn_cpsF T_pixCreate_nn_cpsF T_pixaAddPix_ins_cps T_pixaGetLinePtrs_cps L_lit_176736 L_lit_176704 T_bc_nc_loop_stmt T_bc_kidx_stmt T_bc_kfr_stmt T_bc_cutA320_stmt T_bc_twin336_stmt.
Definition T_pixaGetCount_cps : Bi_iface.pixaGetCount_cps RT :=
  Bi_getcount.pixaGetCount_ok RT AFt GP.
Definition T_pixCreateTemplate_cps : Bi_iface.pixCreateTemplate_cps RT :=
  Bi_template.pixCreateTemplate_ok RT AFt GP FKC T_pixCreateTemplateNoInit_nn_cpsF.
Definition T_bilateralApply_cps : Bi_iface.bilateralApply_cps RT :=
  Bi_apply.bilateralApply_ok RT AFt GP FKC T_pixaGetCount_cps T_pixCreateTemplate_cps.
Definition T_boxaDestroy_empty_cpsF : Bi_fktw.boxaDestroy_empty_cpsF RT :=
  Cf_boxadestroy_empty.boxaDestroy_empty_okF RT AFt GP FKC.
Definition T_pixaDestroy_n_cps : Bi_iface.pixaDestroy_n_cps RT :=
  Bi_pixadestroy.pixaDestroy_n_ok RT AFt GP FKC T_boxaDestroy_empty_cpsF T_pixDestroy_cpsF L_tr_22 L_tr_23 L_trf_24.
Definition T_bilateralDestroy_cps2 : Bi_bd_defs.bilateralDestroy_cps2 RT :=
  Bi_bdestroy.bilateralDestroy_ok RT AFt GP FKC T_pixDestroy_rc_cpsF T_pixDestroy_cpsF T_pixaDestroy_n_cps L_trf_25 L_trf_26.
Definition T_pixBilateralGray_cps : Bi_iface.pixBilateralGray_cps RT :=
  Bi_pbgray.pixBilateralGray_ok RT AFt GP FKC T_bilateralCreate_cps2 T_bilateralApply_cps T_bilateralDestroy_cps2 T_returnError_cpsF_e_returnErrorPtr L_lit_175680 L_lit_175552 L_trf_29 L_tr_30 L_tr_31 L_trf_32 L_tr_33.
Definition T_pixBilateral_cps2 : Bi_pb_defs.pixBilateral_cps2 RT :=
  Bi_pbil.pixBilateral_ok RT AFt GP FKC T_pixBilateralGray_cps T_pixGetRGBComponent_cps T_pixCreateRGBImage_cps T_pixDestroy_cpsF T_pixDestroy_null_cpsF T_returnError_cpsF_e_returnErrorPtr T_lept_stderr_cpsF T_pixCopy_nn_cpsF.

(* [comment removed for export] *)
Hypothesis FUZZ_OK : RT_iface.art_facts RT -> RT_gaps_iface.rt_gaps RT -> RT_fk_iface.rt_fk_contracts RT -> Lept_iface.pixDeserialize_cps RT -> Bi_fktw.pixCopy_nn_cpsF RT -> Bi_pb_defs.pixBilateral_cps2 RT -> Bi_iface3.pixBlockBilateralExact_cps2 RT -> Bi_fktw.pixDestroy_cpsF RT -> Bi_fktw.pixDestroy_null_cpsF RT -> Bi_fz_defs.bi_fuzz_one_cps2 RT.
Hypothesis ADAPT : Bi_fz_defs.bi_fuzz_one_cps2 RT -> D_libiface.fuzz_one_cps RT D_libiface.LIB_A.

Theorem bi_cone_of_open : D_libiface.fuzz_one_cps RT D_libiface.LIB_A.
Proof.
ltac2:(KReplay.run1 (kr_t_Bi_top ()) ["Top"] "p,5ADAPTp,7FUZZ_OKg00LPp,2GPp,3FKCg00MFg00NMg00OQg00PWg00Qgg00RkO9O1o"). Qed.
End Top.
