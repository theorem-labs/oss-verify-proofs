(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (3 recorded proofs replaced by written proofs (REFILLS, afree_sec_norecycle, afree_sec)). *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame Arr Tac ITree Nodes Decode.
From OSSVerify.Proofs.zstd.huf_decompress.lib.LibA Require Import ExecF ITreeA StepF.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Spec Require Import STree AsanCtrl AsanEmbed.
From OSSVerify.Proofs.zstd.huf_decompress.lib.BothW Require Import BImg AProto ABase ABytes AQConst AKitQ AMalloc_iface ADepot_iface ARep ARepQ ARepQP ALayout AHeapP
     ASec AFreeModel AFreeModelR AFreeRep AFreeRead ARefill_iface ARefillP F_afree_arep
     ASF_kit ASF_fast ASF_store ASF_refill ASF_mid ASF_storeR ASF_big.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Common Require Import RunDraw.
From OSSVerify.Proofs.zstd.huf_decompress.lib Require KReplay.
Ltac2 kr_t_ASF_all () := "I47Corelib5Lists7ListDef6Forall00C47Corelib4Init9Datatypes3fstI35stdpp9countable9Countable00C35stdpp4base;RelDecisionC59OSSVerify5KrLib4Spec8AsanCtrl4aptrC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List2hdC35stdpp8fin_maps:map_deleteC35stdpp4gmap;gmap_lookupC35stdpp4gmapBgmap_partial_alterC35stdpp4base6LookupC35stdpp4base6DeleteI35stdpp4gmap4gmap00C35stdpp4base4fmapC59OSSVerify5KrLib5BothW7ALayout4aobjC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1Z02C56Stdlib6ZArith6BinInt1Z2leC59OSSVerify5KrLib6Common7RunDraw:atop_rangeC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive01C59OSSVerify5KrLib3Lib8RunConst4ATOPC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z6moduloC56Stdlib6ZArith6BinInt1Z3addC56Stdlib6ZArith6BinInt1Z3mulI47Corelib4Init5Logic3and00C46Stdlib9micromega9SatDivModCZ_mod_nonneg_nonnegC56Stdlib6ZArith6BinInt1Z7div_modC47Corelib4Init5Logic3notC56Stdlib6ZArith6BinInt1Z3divI47Corelib4Init5Logic2eq00C56Stdlib6ZArith6BinInt1Z=mod_pos_boundC56Stdlib6ZArith6BinInt1Z2ltC56Stdlib6ZArith6BinInt1Z=mod_neg_boundC56Stdlib5omega8PreOmega1Z;div_0_r_extC56Stdlib5omega8PreOmega1Z;mod_0_r_extC59OSSVerify5KrLib3Lib9LiaTuning9zify_doneC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z7compareK47Corelib4Init5Logic2eq01K47Corelib4Init9Datatypes3nat02K46Stdlib9micromega=RingMicromega5Psatz02K46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega:ZMicromega;ZArithProof02K47Corelib4Init9Datatypes4list01K47Corelib4Init9Datatypes4list02I47Corelib4Init9Datatypes4list00K46Stdlib9micromega6VarMap1t01K46Stdlib9micromega6VarMap1t02K46Stdlib9micromega6VarMap1t03I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr02K47Corelib4Init9Datatypes6option02K46Stdlib9micromega7EnvRing5PExpr03K46Stdlib9micromega5Tauto8GFormula06C46Stdlib9micromega5Tauto8BFormulaC46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundK46Stdlib9micromega7EnvRing5PExpr01K46Stdlib9micromega7EnvRing5PExpr05K47Corelib4Init5Logic2ex01K46Stdlib9micromega5Tauto8GFormula03K47Corelib4Init5Logic3and01I47Corelib4Init5Logic2or00I47Corelib4Init5Logic2ex00K46Stdlib9micromega=RingMicromega7Formula01K46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega5Tauto8GFormula05K46Stdlib9micromega5Tauto8GFormula08I47Corelib7Numbers7BinNums1Z00K47Corelib7Numbers7BinNums1Z01C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K46Stdlib9micromega=RingMicromega3Op203K47Corelib4Init9Datatypes4unit01K47Corelib7Numbers7BinNums8positive03K47Corelib4Init5Logic4True01I47Corelib4Init9Datatypes:comparison00I46Stdlib9micromega:ZMicromega;ZArithProof00K47Corelib4Init9Datatypes3nat01K46Stdlib9micromega:ZMicromega;ZArithProof01I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01C59OSSVerify5KrLib5BothW:ASF_refill4AHSmC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW:ASF_refill9AHSm_lawsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW8ARefillP8arefillPC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec8AsanCtrl6achunk00C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib5BothW5ARepQ5qconc00C1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List2InC35stdpp4base6lookupC35stdpp4base6deleteK47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00C4ELinuxProcessSemantics5Riscv7Prelude5bvmapI47Corelib4Init9Datatypes6option00C59OSSVerify5KrLib4Spec8AsanCtrl6a_liveC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec8AsanCtrl6achunk02C1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes6option01C59OSSVerify5KrLib5BothW:AFreeModel6st_enqC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl<a_qloc_bytesC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW4ASec7ASEC_ofC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW<F_afree_arep3AHQC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW6AHeapP7AHEAP_PC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib5BothW5ABase6abkind01C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib5BothW5ABase6ablock01C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib3Mem7mem_invC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitions;bv_unsignedC59OSSVerify5KrLib3Lib5Frame3stkC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3subC45stdpp9bitvector;definitions7Z_to_bvC59OSSVerify5KrLib5BothW=AMalloc_iface4aunwC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4LibA5ExecF3rngC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z;lt_ge_casesC59OSSVerify5KrLib4LibA6NodesA8at_nodeAC1?~~~~~~~~~~~~~~~I69OSSVerify5KrLib3Lib5ITree3Exc3exc00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl5afreeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec9AsanEmbed6aembedC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW=AMalloc_iface:afree_postC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4LibA6ITreeA6epostFC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Frame3mkRC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib8PropExec7seg_romC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib6MState2MSC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW9ASF_store?afree_sec_fastPC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW9AFreeRead:enq_is_appC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW9AFreeRead?enq_is_app_specC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic5proj1C59OSSVerify5KrLib5BothW:AFreeModel7enq_appC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic6eq_symC47Corelib4Init5Logic8eq_transC47Corelib4Init5Logic6eq_indC47Corelib4Init5Logic9False_indI59OSSVerify5KrLib5BothW7ALayout:alayout_ok00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW6AHeapP4arngC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW6AHeapP7ablocksC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW4ARep7ah_fakeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW4ARep4AREPC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW4ARep3awfC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW4ARep7arep_rtC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW4ARep9ainstanceC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW4ARep7athreadC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW4ARep=aregion_cellsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW4ARep:afreearrayC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW4ARep6aslotsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW4ARep<aslot_shadowC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW4ARep7ah_quarC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW4ARep6ah_secC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW4ARep8ah_depotC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW4ARep6arelroC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW4ARep8arep_rt2C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW4ARep=ashadow_availC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW4ARep8arep_rt3C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl;a_space_begC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW5ABase<al_space_begC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl;a_ptr_arrayC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW5ABase<al_ptr_arrayC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl7get_clsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW4ARep5x_clsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl=size_of_classC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl@c_allocated_userC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl=c_mapped_userC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl;c_num_freedC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrlCc_mapped_free_arrayC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW4ARep7xc_freeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW4ARep8xc_cacheC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl7c_countC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW4ARep8xb_classC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW4ARep5xb_stC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW4ARep4xb_nC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl<rounded_sizeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl7rz_sizeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW4ARep5xb_b1C1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z4landC59OSSVerify5KrLib5BothW4ARep6xb_ctxC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3powK59OSSVerify5KrLib4Spec8AsanCtrl6achunk01C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW4ARep6x_busyC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib5BothW4ARep6bstate01C1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic5proj2C59OSSVerify5KrLib5BothW:AFreeModel7enq_newC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl=a_qglob_bytesC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW:AFreeModel<enq_new_coreC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW:AFreeModel9same_coreC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl7a_qglobC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl:chunk_sizeC1?~~~~~~~~~~~~~~~C35stdpp8fin_maps:map_insertc59OSSVerify5KrLib5BothW7ASF_allAafree_sec_refillPC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl8set_liveC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4LibA6ITreeA5implFC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes6lengthC56Stdlib6ZArith6BinInt1Z6of_natC59OSSVerify5KrLib5BothW4ARep:busy_slotsC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes3appC59OSSVerify5KrLib5BothW4ARep5ndistC1?~~~~~~~~~~~~~~~I46Stdlib5Lists4List5NoDup00C59OSSVerify5KrLib4Spec8AsanCtrl9max_countC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl6a_nextC1?~~~~~~~~~~~~~~~C56Stdlib6NArith6BinNat1N2ltC59OSSVerify5KrLib4Spec8AsanCtrl5a_clsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl=cls_set_countC1?~~~~~~~~~~~~~~~C35stdpp4base6insertC59OSSVerify5KrLib4Spec8AsanCtrl6a_qlocC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec8AsanCtrl6abatch01C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl5Q_MAXC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl7Q_CACHEC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl=K_BATCH_CLASSC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib3Lib5Nodes4node00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW4BImg5bsegsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW6AProto6fstepSC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib5BothW4ARep5aconc00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl7K_ALIGNC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl=K_FREEARR_OFFC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl:K_USER_MAPC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl=K_FREEARR_MAXC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl=K_FREEARR_MAPC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec8AsanCtrl6aclass00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl7aclass0C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib5BothW4ARep5xbusy00C1?~~~~~~~~~~~~~~~I47Corelib7Numbers7BinNums1N00C59OSSVerify5KrLib4Spec8AsanCtrl<K_SPACE_SIZEC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl=K_SPACE_EXTRAC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec8AsanCtrl=Q_BATCH_BYTESC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec8AsanCtrl6abatch00C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib5BothW5ABase7alayout00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4LibA5ExecF9footprintC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec8AsanCtrl6astate00C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib5BothW5ABase6ablock00C1?~~~~~~~~~~~~~~~C45stdpp7numbers1N6eq_decC35stdpp9countable;N_countableC59OSSVerify5KrLib5BothW5ABase;AFREE_STACKC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW5ABase3ATPC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW5ABase8AFREE_PCC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW5ABase9AFREE_SYMC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic5False00I47Corelib4Init5Logic4True00K47Corelib4Init9Datatypes4bool02C59OSSVerify5KrLib4Spec8AsanCtrl=K_NUM_CLASSESC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib5BothW4ARep6xclass00C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib5BothW4ARep6bstate00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW5ABase7AREQMAXC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW9AFreeRead3K24C1?~~~~~~~~~~~~~~~K46Stdlib9micromega=RingMicromega3Op201C45stdpp7numbers1Z6eq_decC35stdpp9countable;Z_countableK46Stdlib9micromega=RingMicromega3Op205C56Stdlib6ZArith6BinInt1Z;le_gt_casesc59OSSVerify5KrLib5BothW7ASF_allCafree_sec_norecycleC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW7ASF_big=afree_sec_bigC1?~~~~~~~~~~~~~~~".
Import ListNotations.
Open Scope Z_scope.

Section CANSEC1. Context {rc : runConstT}.
(* [comment removed for export] *)
Local Lemma aobj_int : forall a n, aobj a n -> 0x10000 <= n ->
  6352896 <= a /\ a + n <= ATOP /\ exists k, 0 <= k <= 1 /\ a + n <= 2147446784 + k * 18446744073709551616 /\ 17594333495296 * k <= a.
Proof.
ltac2:(KReplay.run1 (kr_t_ASF_all ()) ["CANSEC1"] "h04__x1h14__x2h21Hh31kh47__arithh54__ffh68__varmaph75__with84__x3h92H6h:4__p1h;2H0h<2H1h=3H10h>2H2h?2H3h@2H4hA2H5hB2H7hC2H8hD2H9hE2HnhF6__sat6hG1ahH1np;3p;1p;2p;4p;7p;6p;8p-1R0p10000p4p710p8P0p1000QR1p4p710p8P0P1p4p7210p8p1000np4p710R1p1001LR0p4p710R2p8P1P0p4p7210R0p8p1001ep4p70R3p1002\p4p710p8P3p10033p4p710p8P3p1003Op4p710p8P3p1003hp4p710p8P3p1004Hp4p710p8P3p1004\p4p710p8p10050p4p710R3P1p8P3P2p8P3P0p8P3p1005Dp4p73110p8g005Vj3zTg006Mj12Tg0072j1<Tg007Pj20Tg007lj1pTg008jj17Tg009Oj1`Tg00:Ej2ATg00:ej21Tg00;Bj2@Tg00;_R3j28Tg00<:j2fTg00<kj2eTg00=Lj1cTg00=ej2TTg00>Bj3LTg00>\j2bTg00?Cj2ETg00?_j2aTg00@Fj2_Tg00@lj2^Tg00ARj2]Tg00BNj2\Tg00Boj2STg00CIj1KTg00Chj2JTg00DQj3QTg00E:j2[Tg00Efj1yTg00FFj3ZTg00Ffj1xTg00GFj1wTg00Gdj2YTg00HBj4DTg00H`j1tTg00I>j1sTg00Iij2MTg00JLj1rTg00Jnj3OTg00KQj7qTg00L5j2oTg00LWj2nTg00MCj3mTg00Mbj4lTg00NTj2VTg00O7j3NTg00OZj4WTg00P4j6jTg00PXj4UTg00Q3R0j2XTg00QMj2iTg00Qgj4hTg00RRj7uTg00S6j7gTg00SZj8vTf0R2#2#2p=H%22#2#2#2#2#2#2#2p=5%72#7#7#7p=9%72#7p=d%22#2#2#2p=Cf2R1f1R4/02'8p=Gg00T>R5g00T\R67L2p=Pf3R7/011042'Xp=31842,81p=R1014/82,87p=;1062p=?1114/02p=I1042,81,87p=F1i52p=B1014/82p=61V52p=>P1g00U:R8g00UYR9P9g00V9R:P5P4g00VYP2Chg00W@Fup=4P1P8P9P9P:P4P2Fgp==P7P8P9P9P:P1P4P2Gvp=:1X42,81p=kp,2rcR;?z42g00W`R<#2R=#2R>#H#5R?#2R@#2#HRA#<RB/04RC%p;%7<RD#7#9#9#9RE#2#7#dRF#7#9#2#H#C#5#5#<%`;R;'0RG%7E#9#9#2#H#C#5#5#<RE7G;P3f4RH%<?R?'A#P10?HRI11H7RJP;PJ%CF#5#<RF%9@#9#9#9#2#H#C#5#<R@PHC3PJPB%7<#2#C#9#C#5#<RJPHC37RIC;f5RI11IH%?2%<<RK7G2RLf6RM%5A#5#5#5#5#5#<RA,@2,1FRN7II1@@2ROPMCFX35#B76;56JP11AM?#Pf7RP,0?RQ11PMRRP;PRPFP@PPC3PRPBPJPPC37RQC;P3f8RQ,0?RR11QPRPPPPFP@PQC3PPPBPJPQC37RR76;f9RR11RQPLf:RP?IRNPOPPCFX35#B76;56JP210?Pf;RS/1PRPPPPFP@PSC3P?PSPPPBPJPSC3C;76;P3f<RP/1SRS/0;PSPFP@PPC3P?PPPSPBPJPPC3C;f=RS11SPPLf>RT/1SRSPN10OTC;X35#B76;56JP210S;f?RS/1TRTPFP@PSC3P?PSPTPBPJPSC3C;P3f@R3/1SRSPFP@P3C3PSPBPJP3C396?3fARS11S3PLfBR3/1SRSPN10O3C;X35#B76;56JP2PSPFP@P3C3fCRS11S3PBPJPSC356?fDRT,0J11TSRU/0;RVPLfERW/1TRXPN10OWC;X35#BRY'81fT?%?T%??fFRZ/A?R[#?[[1eW?%P?R\#c1TZ?,@?/1[9L5Z[1bZ?1E6?R[fGR]/A?R^#?1E^?'8[1a]?1E?6fHR^/A?R_,E??G_6[1_^?fIR^/T?#P\\1^^?fJR^/A?=L5^\\g00XE1]^?R\eP\PHg00Xa1\6?'SP[eO1fKR[/A?R\#?1E\?'8g00YGR\g00Z3R_#KR`#KRa#KRb#K,J51J5`R`1J5a5Q55Q5g00ZRRa'[%y\Rc3Z%x\RdP5%w5ReP41Y51RfCD%t5Rg%s5Rh%>BRi1M5DRD54h%r9RjPh%>?1M5<R<54hRkPhP8P9P9P:AO5<D=4hi%>J=4h<RiFq5=hPjPhPkPjPiC:C:C:1oh:RiP2P1g00[>Rlg00[^Rm'S1n21=LlmdAm564ClRmb5b6b7X05X1510?4Rl1141Rn/0B10J43k10?110J7[[\C^05^15P2fLfMP^PRP3O5b4b910J[eb=bDbCbBb9b2bFPVPYPcPdP5PfP41Y57RYCDPgPh1M5=9O5<R==4hDRDPjPDC:PiPmb5b6b7X05X15X851124RD/0110n7[^05^15^85P2P;PTPWPMO4b4P010UF10@TPLAIZWNPOPZCFX35#BP410XFP5PLAI]ZNPOP]CFX35ROP6PcPdP5PfP4PeCDPgPh%>FRf94h=PjPhPkPj1V56Rk=4hk%>KRN94hkRL5=h%>ARX9N5k9O5f94h=%>@RT=N5k=4h<5=h5=hC:C:PiPmb5b6b7X05X1510DF%?KRD96661117Rk1@6A,1F1@@6/01C;\l[^05^15P2PZP]P4PPO4b4CWW2P2O110@WP5POPKp-0RO1J5b1J5_9Q5`5Q5/[a=Z\cPdP5P5PYP1PeCDP4PeCDPgPhPhP8P9P9P:PIEj1M5>R>%>E54h5=hPjPhA4hT<PjPhA4h=>PjA4hNN9=hLAN5NX9O5f94h=AN5TN=4h<5=h5=hC:C:C:PiPmb5b6b7X05X15X85W:AG71E10@410kHAGDKK1@KA,1F9I7H1@@KP7CF[[[^05^15^85^:OP2PGP;PZP]PSP4PQO7b4CWW2P2O1n200100001021100011000CUCUWAW@P4P2O2n2001000010121000000W2W?P4P2O2n2001000010121000000W2W>P4P2O2n2011000010121000000W2W<P4P2O2n2011000010121000000b;WEW2XH5XG5o"). Qed.
Local Lemma aobj4_int : forall a, aobj a 4096 ->
  4096 <= a /\ a + 4096 <= ATOP
  /\ (exists k, 0 <= k <= 1 /\ a + 4096 <= 2147446784 + k * 18446744073709551616 /\ 17594333495296 * k <= a)
  /\ (exists j, 0 <= j <= 1 /\ a + 4096 <= 65536 + j * 18446744073709551616 /\ 6352896 * j <= a).
Proof.
ltac2:(KReplay.run1 (kr_t_ASF_all ()) ["CANSEC1"] "h04__x1h11jh21Hh31kh47__arithh54__ffh68__varmaph75__with84__x2h94__p1h:2H5h;2H0h<2H1h=2H2h>2H3h?2H4h@2_HhA1ap;1p;3p;2p;4p;6p;7p;8p-1R0p10000p4p710p8P0p1000QR1p4p710p8P0P1p4p7210p8p1000np4p710R1p1001LR0p4p710R2p8P1P0p4p7210R0p8p1001ep4p70R3p1002\p4p710p8P3p10033p4p710p8P3p1003Op4p710p8P3p1003hp4p710p8P3p1004Hp4p710p8P3p1004\p4p710p8p10050p4p710R3P1p8P3P2p8P3P0p8P3p1005Dp4p73110p8g006Mj12Tg0072j1>Tg005Vj3mTg007lj1lTg008jj1:Tg009Oj1\Tg007Pj20Tg00:Ej2TTg00>Bj3ITg00:ej21Tg00;Bj2?Tg00;_R3j26Tg00Efj1aTg00Ffj1_Tg00Gdj2OTg00H`j1^Tg00I>j1]Tg00Iij2JTg00JLj1[Tg00L5j2ZTg00Boj2YTg00LWj2XTg00MCj3WTg00Mbj4VTg00GFj1UTg00HBj4STg00Jnj3ETg00NTj2RTg00OZj4GTg00CIj1NTg00Chj2KTg00DQj3QTg00E:j2kTg00FFj3jTg00P4j6iTg00PXj4MTg00Q3R0j2gTg00QMj2fTg00Qgj4eTg00RRj7dTg00SZj8cTg00S6j7hTg00O7j3bTf0R2#2#2p=F%22#2#2#2#2#2#2#2p=8%:2#:#:#:p=<%:2#:p=`%22#2#2#2p=Bf2R1f1R4/02'6p=Hf3R5/011042'gp=41642,61p=L1014/62,65p=D1014/62p=7f4R610511042'6'6p=5g00T>R7/f2p=91R72p=@P1g00U:R8g00UYR9P9g00V9R:P7P4g00VYP2Ceg00W@Fdp=3P5P8P9P9P:P1P4P2Gcp=;1114/02p=CP1P8P9P9P:P4P2Fhp==Ab742p=A1042,61,65p=Pp,2rcR;g00W`R<#2R=#2#F#8R>#>R?7m2%l;%:<R@#:#<#<#<RA#2#:#`RB#:#<#2#F#B#8#8#>%\;R;'0RC%:A#<#<#2#F#B#8#8#>RA7H;P31T1?g00T\RD5I710?1RE111?RFP;PF%BB#8#>RB%2>R>#<#<#<#<#2#F#B#8#>RGP1C4PF%2>#FR>#>RH%:<#2#B#<#B#8#>RIP1C47LECD115?RE%><RJ,0297D2RK116?RL%8>#8#8#8#8#8#>R>,?2RM,1BRN1?G2ROP6D5X37#9PKPL11HMRM1?I2RLP6D5X17#9'677;97?5P41T6?=I7Df5RP,0?RQ11P?RRP;PRPBPGPPC4PRPHPIPPC47LQCDP3f6RQ,0?RP11Q?RRPRPBPGPQC4PRPHPIPQC47LP77;f7RP11P?PKf8RP/1?RRPNPOPPD5X37#9PKPRPMPLPPD5X17#9'677;57?P210?Pf9RR/1?RSPSPBPGPRC4P?PRPSPHPIPRC4CD77;P3f:RR/1?RS/0;PSPBPGPRC4P?PRPSPHPIPRC4CDf;RS11S?PKf<RS/1?RTPNPOPSD5X37#9PKPTPMPLPSD5X17#9'677;57?P210T;f=RT/1?RUPBPGPTC4P?PTPUPHPIPTC4CDP3f>RT/1?RUPBPGPTC4PUPHPIPTC497?Tf?RT11T?PKf@RT/1?RUPNPOPTD5X37#9PKPUPMPLPTD5X17#9'677;57?P2PUPBPGPTC4fARU11U?PHPIPUC457?fBRU,0?RV11U?RW/0;RXPKfCRY/1?RZPNPOPYD5X37#9R[PKPZPMPLPYD5X17#9R\'6R]'6g00YGR^#aR_%_^R`1O74Ra%^7Rb%]7Rc%@?Rd1J7<R<53cRe%[9RfPeC;1Zc:RgP2P1g00[>Rhg00[^Ri'Y1X21=IhidAW7D4CVRib5b6b7X0710?210?4Rh[^07P2PYPRO2b4PXP]P_P`P71O71R]P4%U7RXCSPbPcAE7<dRd1J7=53cR=PfP=C;PgPib5b6b7X07X87112?R=/04AC4?1[^07^87P2P;PYPQO3b4P[P\P010WB10GUPKfDR\/1?R[PNPOP\D5X37#9P410ZBP7PKfERZ/1?RQPNPOPZD5X37ROPDP_P`PaPbPc%@BRN93cdPfPcPePf1R7DRR=3cR%@JRj93cRRk5=cRl%@>Rm,ARRn9E7N93cd%@GRo/AR=3c<5=c5=cC;C;PgPib5b6b7X0710=B10DJRp97DDRqPF1?D>Rr,1B1?GDP1D5\h[^07P2PZP4PSO3b4CGW2P2O110GYP7POPJp-0ROg00Z3Rs#NRt#N#N,K71K7t1K7s5Q75Q7g00ZR'k=j^_R^P`P7PXP4P]CSR]PbPcPcP8P9P9P:P6Ei1J7@R@%@A53c5=cR6PfPcA3co<PfPcA3cd@R@PfA3cjj9=ckRk1AjmRm9E7N93cd1Aoj=3c<5=c5=cC;C;C;PgPib5b6b7X07X87W9AH14ARA10G410F5RoAHpJJRpPE1?J>R>,1B1?GJP5D5[[[^07^87^9OP2PCP;PZPYP4PPO6b4CGW2P2O1n200100001021100011000P3PVPWPHPIPUC4PKP[PMPLP\D5X17#9P210?\PQPHPIPZC4P0fFR0?C?H10I0PKfHR0?C?MPLP0CPX17#9P2fGR0?C?HP7PKfIRK?C?MPLPKCPX17RLPDP_P`PaPbPc%@HRa93cdPfPcPePfAE7an93cd%@IRn/AR=3c<5=c9=clC;C;PgPib5b6b7X0710=HPqPF11Hr1?IDP1D5\h[^07P2PKP4PTO3b4CGW:P2O110I0P7PLPJP^P`P]PbPcP6PfPcA3cn<PfPcP@PfAE7am93cd1Anj=3c<5=c9=ckC;C;C;PgPib5b6b7X07X87X9O10I4PpPE11H>1?IJP5D5\o[\A^07^87^9OP2PCP;PKP0P4PSO6b4CGW:P2O1n200100000021100011000W2W@P4P2O2n2001000000121000000CMCMCMW:W?P4P2O2n2001000010121000000W2W>P4P2O2n2011000010121000000W2W=P4P2O2n2011000010121000000W2W<P4P2O2n2011000010121000000b;W2XA7o"). Qed.

Section S.
Variable DI : ADepotIface.
Variable AFK : alayout -> list ablock -> amem -> Prop.
Hypothesis HL : ahole_laws (AHQ DI ASEC_of AFK).
Variable CI : list (Z * Z).
Hypothesis CI_OK : Forall (fun iv => 0x10000 <= fst iv /\ (snd iv <= ADEPOT_LO \/ ADEPOT_HI <= fst iv) /\ snd iv <= AIMG_HI
                                  /\ (snd iv <= 0xb6f70 \/ 0xb7030 <= fst iv)
                                  /\ (snd iv <= 0xbb500 \/ 0x13c530 <= fst iv)
                                  /\ (snd iv <= 0x149d88 \/ 0x149d8c <= fst iv)) CI.
Hypothesis CI_OK2 : Forall (fun iv => snd iv <= AINSTANCE \/ AINSTANCE + 728 <= fst iv) CI.

Lemma REFILLS : forall cs Q1, refill_stmt (AHSm DI AFK cs Q1).
Proof. intros cs Q1. exact (arefillP (AHSm DI AFK cs Q1) (AHSm_laws DI AFK HL cs Q1)). Qed.

Definition afree_sec_refillP :=
  afree_sec_refill DI AFK HL CI CI_OK CI_OK2 (mid_kitS DI AFK HL CI CI_OK) (store_freeRS DI AFK HL CI CI_OK) REFILLS.

(* [comment removed for export] *)
Theorem afree_sec_norecycle : forall (L : alayout) (RNG : footprint)
    (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : amem) (st : astate) (LB : list ablock) (p : aptr) (A n lo : Z) (tr : list Z) (mb ms : Z),
  (a_live st) !! p = Some (CSec mb ms n) -> n <= Q_MAX ->
  let st1 := set_live (delete p (a_live st)) st in
  let st2 := st_enq st1 (CSec mb ms n) in
  (Q_CACHE < a_qloc_bytes st2 -> a_qglob_bytes st2 + a_qloc_bytes st2 <= Q_MAX) ->
  (* [comment removed for export] *)
  AHEAP_P (AHQ DI ASEC_of AFK) L RNG st LB m -> In (HB p A n) LB ->
  mem_inv bsegs m ->
  stk bsegs m lo (bv_unsigned sp) -> ATOP + 4096 <= lo -> lo <= bv_unsigned sp - AFREE_STACK ->
  tp = Z_to_bv 64 ATP ->
  a0 = Z_to_bv 64 A ->
  aunw m L RNG lo AFREE_PC sp s0 ra tr ->
  bv_unsigned s0 <> bv_unsigned sp + 8 -> 4096 <= bv_unsigned ra -> bv_unsigned ra <> AFREE_PC ->
  bv_unsigned sp mod 16 = 0 ->
  rng RNG lo (bv_unsigned sp - lo) ->
  implS bsegs RNG (aembed ATOP (afree st (Some p)))
        (epostF (afree_post CI (AHEAP_P (AHQ DI ASEC_of AFK)) L RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc st LB p lo m))
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 AFREE_SYM) fc None m (seg_rom bsegs)).
Proof.
  intros until ms. intros LIVE NQM st1 st2 NOREC. intros.
  destruct (Z.lt_ge_cases 0 (c_count (get_cls st K_BATCH_CLASS))) as [POS|Z0].
  - eapply (afree_sec_fastP DI AFK HL CI CI_OK); try eassumption. intros _. exact POS.
  - destruct (enq_is_app st) eqn:EA.
    + eapply (afree_sec_fastP DI AFK HL CI CI_OK); try eassumption. intros E. exfalso.
      assert (EA1 : enq_is_app st1 = true) by exact EA. destruct (proj1 (enq_is_app_spec st1 (CSec mb ms n)) EA1) as [s Hs].
      change (enq_app st1 (CSec mb ms n) = None) in E. congruence.
    + assert (CNT0 : c_count (get_cls st K_BATCH_CLASS) = 0).
      { pose proof H as AH. destruct AH as (_ & _ & [X [AR _]] & _). destruct AR as (WF & _).
        destruct WF as (_ & _ & _ & _ & _ & PERC & _). destruct (PERC K_BATCH_CLASS (K24)) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & CNTB & _). lia. }
      eapply afree_sec_refillP; try eassumption.
      (* [comment removed for export] *)
      intros LT. subst st2 st1.
      assert (EAPP : enq_app (set_live (delete p (a_live st)) st) (CSec mb ms n) = None).
      { destruct (enq_app _ _) as [s'|] eqn:E; [exfalso| reflexivity].
        assert (EA1 : enq_is_app (set_live (delete p (a_live st)) st) = true) by (apply (proj2 (enq_is_app_spec _ (CSec mb ms n))); eexists; exact E).
        change (enq_is_app (set_live (delete p (a_live st)) st)) with (enq_is_app st) in EA1. congruence. }
      unfold st_enq in NOREC. rewrite EAPP in NOREC.
      pose proof (enq_new_core (CSec mb ms n) (set_live (delete p (a_live st)) st)) as (_ & G1 & G2 & _ & _ & L2 & _).
      rewrite G2, L2 in NOREC. cbn [chunk_size] in NOREC.
      change (a_qloc_bytes (set_live (delete p (a_live st)) st)) with (a_qloc_bytes st) in NOREC.
      change (a_qglob_bytes (set_live (delete p (a_live st)) st)) with (a_qglob_bytes st) in NOREC.
      unfold Q_BATCH_BYTES in NOREC. generalize NOREC LT; clear; intros; lia.
Qed.

(* [comment removed for export] *)
Hypothesis DEPD : depot_frameD_law (ADEPOT DI).
Hypothesis AFKD : fake_frameD_law AFK.

Theorem afree_sec : forall (L : alayout) (RNG : footprint)
    (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : amem) (st : astate) (LB : list ablock) (p : aptr) (A n lo : Z) (tr : list Z) (mb ms : Z),
  (a_live st) !! p = Some (CSec mb ms n) ->
  let st1 := set_live (delete p (a_live st)) st in
  let st2 := st_enq st1 (CSec mb ms n) in
  (n <= Q_MAX -> Q_CACHE < a_qloc_bytes st2 -> a_qglob_bytes st2 + a_qloc_bytes st2 <= Q_MAX) ->
  (* [comment removed for export] *)
  AHEAP_P (AHQ DI ASEC_of AFK) L RNG st LB m -> In (HB p A n) LB ->
  mem_inv bsegs m ->
  stk bsegs m lo (bv_unsigned sp) -> ATOP + 4096 <= lo -> lo <= bv_unsigned sp - AFREE_STACK ->
  tp = Z_to_bv 64 ATP ->
  a0 = Z_to_bv 64 A ->
  aunw m L RNG lo AFREE_PC sp s0 ra tr ->
  bv_unsigned s0 <> bv_unsigned sp + 8 -> 4096 <= bv_unsigned ra -> bv_unsigned ra <> AFREE_PC ->
  bv_unsigned sp mod 16 = 0 ->
  rng RNG lo (bv_unsigned sp - lo) ->
  implS bsegs RNG (aembed ATOP (afree st (Some p)))
        (epostF (afree_post CI (AHEAP_P (AHQ DI ASEC_of AFK)) L RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc st LB p lo m))
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 AFREE_SYM) fc None m (seg_rom bsegs)).
Proof.
  intros until ms. intros LIVE st1 st2 NOREC. intros.
  destruct (Z.le_gt_cases n Q_MAX) as [LE|GT].
  - eapply afree_sec_norecycle; try eassumption. exact (NOREC LE).
  - eapply (afree_sec_big DI AFK HL DEPD AFKD CI CI_OK CI_OK2); try eassumption; lia.
Qed.
End S.
End CANSEC1.
