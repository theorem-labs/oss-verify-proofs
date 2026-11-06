(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.K5.Lib Require Import Tac.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.K5.A23 Require Import ImageA.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.K5.Lib Require Import RzCPS NodesA.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.K5.A23 Require Import Layout.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.K5.AG Require Import Shadow.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.K5.A23 Require Import RT_iface RT_traces RT_gaps_iface LeptTac D_kit Lept_kit Lept_iface Lept_env Lept_objkit LeptC_kit Lept_leaf Pm_okit Pm_iface Km_kit Cf_iface Po_rows Po_iface Po_kit.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib Require KReplay.
Ltac2 kr_t_Po_pma1_defs () := "I47Corelib4Init9Datatypes4prod00I47Corelib4Init9Datatypes4list00K47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00I47Corelib4Init9Datatypes6option00C69OSSVerify5KrLib2K53A23:Lept_iface7pix_objC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A23:Lept_iface9pix_cellsC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums1Z02C69OSSVerify5KrLib2K53A23:Lept_iface:pix_hdr_okC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A23:Lept_iface6p_dataC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A23:Lept_iface6p_cmapC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A23:Lept_iface5c_arrC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A238Cf_iface<pix_cells_rcC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive01K47Corelib4Init9Datatypes4list01K47Corelib4Init9Datatypes4list02C69OSSVerify5KrLib2K53A23;Lept_objkit:keeps_liveC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A238Cf_iface:pix_obj_rcC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A23:Lept_iface5chunkC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic3and00C69OSSVerify5KrLib2K53A23:Lept_iface8cmap_objC1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic2or01C69OSSVerify5KrLib2K53A23:Lept_iface:cmap_cellsC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic2ex00C69OSSVerify5KrLib2K53A23:Lept_iface8c_nallocC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3mulC69OSSVerify5KrLib2K53A23:Lept_iface7cmap_okC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List2InC56Stdlib6ZArith6BinInt1Z6moduloK46Stdlib9micromega6VarMap1t02I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr01K46Stdlib9micromega7EnvRing5PExpr02K46Stdlib9micromega=RingMicromega7Formula01K47Corelib4Init9Datatypes6option02K46Stdlib9micromega5Tauto8GFormula07K46Stdlib9micromega5Tauto8GFormula08C46Stdlib9micromega5Tauto8BFormulaK47Corelib4Init5Logic2eq01C46Stdlib9micromega:ZMicromega=ZTautoCheckerI47Corelib4Init5Logic2eq00C46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundC69OSSVerify5KrLib2K53A237Pm_okit>cmap_obj_keep1C1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic3and01K47Corelib4Init5Logic2or02C69OSSVerify5KrLib2K53Lib4Step8rw_cellsC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A23:Lept_iface5rsizeC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic3notI47Corelib4Init5Logic2or00K47Corelib4Init9Datatypes4prod01C56Stdlib6ZArith6BinInt1Z2ltK46Stdlib9micromega5Tauto8GFormula04C69OSSVerify5KrLib2K53A236ImageA5asegsC1?~~~~~~~~~~~~~~~I47Corelib7Numbers7BinNums1Z00K47Corelib7Numbers7BinNums1Z01C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K47Corelib4Init9Datatypes4unit01K47Corelib7Numbers7BinNums8positive03I69OSSVerify5KrLib2K53A23:Lept_iface4pixv00C1?~~~~~~~~~~~~~~~I69OSSVerify5KrLib2K53A23:Lept_iface5cmapv00C1?~~~~~~~~~~~~~~~I46Stdlib9micromega:ZMicromega;ZArithProof00K46Stdlib9micromega=RingMicromega3Op205K46Stdlib9micromega=RingMicromega3Op201I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01I47Corelib4Init5Logic5False00C69OSSVerify5KrLib2K53A238Po_iface5pix1cC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A23:Lept_iface3p_dC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A238Po_iface4res0C1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A238Po_iface6pix1rcC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2K53A23<Po_pma1_defsApix_obj_rc_of_objC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A23;Lept_objkit<pix_obj_keepC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A237Pm_okit<pix_obj_monoC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A237Pm_okit:chunk_monoC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A237Pm_okit=cmap_obj_monoC1?~~~~~~~~~~~~~~~c69OSSVerify5KrLib2K53A23<Po_pma1_defs?pix_obj_rc_monoC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A23:Lept_iface3p_wC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A23:Lept_iface3p_hC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A23:Lept_iface5p_wplC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A237Pm_okit@pix_obj_retargetC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3eqbC46Stdlib5Lists4List9in_or_appC69OSSVerify5KrLib2K53A238Pm_iface<pm_copy_liveC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes3appC56Stdlib6ZArith6BinInt1Z7eqb_neqC47Corelib4Init5Logic5proj2C47Corelib4Init5Logic8eq_ind_rK47Corelib4Init9Datatypes4bool02C69OSSVerify5KrLib2K53A238Po_iface7sel_objC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A238Po_iface9sel_cellsC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A238Po_iface6s_dataC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A238Po_iface4s_syC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitions7Z_to_bvC69OSSVerify5KrLib2K53A238Po_iface6s_rowpC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A238Po_iface6s_rowsC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A238Po_iface4s_sxC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z2leC69OSSVerify5KrLib2K53A238Po_iface4s_cyC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A238Po_iface4s_cxC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes6lengthC56Stdlib6ZArith6BinInt1Z6of_natC47Corelib4Init5Logic5proj1C56Stdlib6ZArith4Znat5Nat2Z9is_nonnegC56Stdlib6ZArith6BinInt1Z3addC47Corelib4Init5Logic8iff_reflC46Stdlib9micromega;ZifyClasses3injC46Stdlib9micromega;ZifyClasses5mkrelK46Stdlib9micromega7EnvRing5PExpr03C46Stdlib9micromega;ZifyClasses;rew_iff_revC69OSSVerify5KrLib2K53Lib5Cells:cells_sizeC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53A23;Lept_objkit@keeps_live_cellsC1?~~~~~~~~~~~~~~~K46Stdlib9micromega=RingMicromega5Psatz02K46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega:ZMicromega;ZArithProof02K46Stdlib9micromega:ZMicromega;ZArithProof03K46Stdlib9micromega6VarMap1t03K46Stdlib9micromega7EnvRing5PExpr05C46Stdlib5Lists4List:length_mapC69OSSVerify5KrLib2K53A236Km_kitAkeeps_live_u64arrC1?~~~~~~~~~~~~~~~K46Stdlib5Lists4List7Forall201C69OSSVerify5KrLib2K53A236Km_kitAkeeps_live_u32arrC1?~~~~~~~~~~~~~~~K46Stdlib5Lists4List7Forall202C46Stdlib5Lists4List;Forall2_indC47Corelib5Lists7ListDef3mapC69OSSVerify5KrLib2K53Lib3Arr6u64arrC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2K53Lib3Arr6u32arrC1?~~~~~~~~~~~~~~~I46Stdlib5Lists4List5NoDup00I46Stdlib5Lists4List7Forall200K47Corelib4Init9Datatypes3nat02C46Stdlib9micromega;ZifyClasses5mkappC46Stdlib9micromega;ZifyClasses6mkapp2K46Stdlib9micromega=RingMicromega3Op203I47Corelib4Init9Datatypes3nat00I69OSSVerify5KrLib2K53A238Po_iface4selv00C1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes3nat01C46Stdlib9micromega8ZifyInst7Inj_Z_ZK46Stdlib9micromega:ZMicromega;ZArithProof01".
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
Definition pma1_sc : Z := e_processMorphArgs1 + 0x124.   (* [comment removed for export] *)
Definition pma1_br : Z := e_processMorphArgs1 + 0x184.   (* [comment removed for export] *)
Definition pma1_pA : Z := e_processMorphArgs1 + 0x34c.   (* [comment removed for export] *)
Definition pma1_st : Z := e_processMorphArgs1 + 0x36c.   (* [comment removed for export] *)
Definition pma1_ep : Z := e_processMorphArgs1 + 0x29c.   (* [comment removed for export] *)
Definition pma1_fl : Z := e_processMorphArgs1 + 0x2dc.   (* [comment removed for export] *)
Definition pma1_fs : Z := e_processMorphArgs1 + 0x2e0.   (* [comment removed for export] *)
Definition pma1_fz : Z := e_processMorphArgs1 + 0x2e4.   (* [comment removed for export] *)

(* [comment removed for export] *)
Lemma pix_obj_rc_of_obj : forall live (m m' : mem) pix v cv rc,
  pix_obj live m pix v cv -> rw_cells asegs m' pix (pix_cells_rc v rc) ->
  (p_cmap v <> 0 -> keeps_live [(p_cmap v, 24)] m m') ->
  pix_obj_rc live m' pix v cv rc.
Proof.
ltac2:(KReplay.run1 (kr_t_Po_pma1_defs ()) [] "h01Hh14__x1h23padh32CHh42COh52H0h63HCMh72HDh83HOKh91Kh:2P0h;2PCh<3PC'h=1Rh>2_Hh?3_H0h@3_H1hA3_H2hB7__arithhC4__ffhD8__varmaphE5__withF2cvhG4livehH1mhI2m'hJ3pixhK2rchL1vp;2p;1p;5p;3p;6p;4p;8p;7g0000j2wTg000Pj1STg0010j1;Tg001Uj1WTg0023j1\Tg002Vj1sTg0038j5fTg0046j1YTg0056j1OTg005Tj1@Tg006Uj13Tg007Rj10Tg008Oj12Tg009Kj2FTg00:Lj1cTg00;1j1]Tg00;Qj3MTg00<1j3LTg00=3j6PTg00>2j3>Tg00>nR0j21Tg00?Ij4?Tg00@Hj3_Tg00@bj2VTg00Acj2UTg00B=j1BTg00C<j2HTg00CYj1ITg00DWj3^Tg00Dnj2QTg00ENj2vTg00Elj1uTg00FJj1tTg00G5j2rTg00GXj2qTg00H;j4[Tg00Hfj1pTg00IHj6oTg00Ilj8kTg00JPj2jTg00K2j2hTg00KLj2eTg00L8j34Tg00LRj3gTg00M1j4dTg00Mcj7iTg00Nej4NTg00O@j3lTg00OZj4mTg00PSj1nTg00QOj15Tg00QhR1j2TTg00RBj4bTg00Rbj2aTg00S>j7`Tg00Sbf2R2f1R3f0R4Cmp=7g00TZR5f5R6g00U8R734f4R8f3R9%n23>A4534#5'1'Tp==A4568#5A4592#5A4534#5'1'1p=<f7R:=457f6R;P6P8P9C?A4523#5/14'1'Tp=81134,12p=EA>923/14p=6A4547#5p=:P5P5P3P4Cbp=AA4547p=9A4592#5A4534#5'1p=KA4589#5A4523#5/14'1p=J1134,T2p=XP8P9P2P3C?/14p=RA4534p=C%54,13p=D1a74p=GP3g00UVR<g00V5R=P=g00VUR>P4g00W5F`p=Z1w55R?#Sg00WUR@#;#;RA#;RB#;RC#;#;RD#W#\%WB#\RB#s[REg00X:g00Y7P;P6P9P2P3DfP0%Y997;8P:P8%ODRD%@9%39RFP:PFP9PFP8E=%09RGP:P;PGP2PGP8%22RHP8PGPFPHPFE<G83EC61F8297;6%06#:%0;RF%c@#;#;#;#ORH'A%]?RG5M?f9RIf8RJ3L[f:RKPJP:P;P6P8EP[[P4%Y697J;PKP:PD%@;%3;R8PKP8P;P8P:E=PFPKPIPFP6PFP:%26R6P:PFP8P6P8E<G83EC6P0f;R8?>JD%@:%3:R6P8P6P:P6PJE=%0:RFP8PKPFP;PFPJ%2;RLPJPFP6PLP6E<G83E1FJ;97KI%0I#:%0KR6/AH=M?Gf=RLf<RF3L[f>RMPFP8PKPIPJEP[[P4A>LKD%@K%3KRJPMPJPKPJP8E=P6PMPLP6PIP6P8%2IRIP8P6PJPIPJE<G83EP0%@8%38RJf?RIPJP8PJPFE=%08R6PIPMP6PKP6PF%2KRNPFP6PJPNPJE<G8'11FFK97ML%0L#:%0MRK/AH=M?GfARJf@RN3L[fBR6PNPIPMPLPFEP[[P4%@L%3MRFP6PFPMPFPIE=PKP6PJPKPLPKPI%2LRLPIPKPFPLPFE<G8'1P0%3IRFfCRLPFPIPFPNE=%0IRIPLP6PIPMPIPN%2MRKPNPIPFPKPFE<G81FNM976J%0J#:%06RM/AH=M?GfERFfDRK3L[fFRIPKPLP6PJPNEP[[P4%3JRNPFPNPJPNP6E=PMPIPFPMPJPMPL%2JRNPLPM%36R6PNP6E<G81FLJ97FK%0K#:%0FRJ/AH=M?GfHRGfGR63L[1FFL976IfIRL?>IDRD%@FRN%3FRMPLPMPFPMPIE=RO%9JRPPLP6PJPKC?PJPI%2KRQPIPJPMPQPMCKDJRM3XRQ'1RR'1RS'1P3PDPSP8PNPRP:POPQP9P1PPPLPGPJPKPMDR%0IRM#9RKfJRJPGPMPFC?PMP6%2FRPP6PM%3IR1PPP1CKDJR13XP2%06RP#9fKRQPLPPPIPPPG%2IROPGPP%36R:POP:CKDJR:DR;_4X5KP4O1PJPLPMPFP1DRP0PQPJPPPIC?P:%0GR:fLRIPJP:P6P:PL%26R6PLP:%3GR:P6P:E<G8P4fMR:PI%0LPGC?%0JRGPQ%2LRLPQPG%3JRGPLPGCKDJ%0QRG#9fORLP:PGPJC?R6PGPI%2JRPPIPG%3QR1PPP1CKDJR1'1P6P1PLfNR1P:PGPJP;P0%SBRB%0IRI1VQ457LX2B'UPLPGPHPLPP%OARA%BJ'H%IJ1CPG'DC6C6%:IP3fQRI%01RP1V:437X2B,UBfRRBPPPHPB%2:RG%B:,HA%I:1CGP'DC6C6P0fSRG%0LRL;>HPG%21RP%B1,HA%I11CPL'DC6fP#0#:P4fURP%0I;>HP0%0BRI/AHfVRL5^?%GI%OCRC,QI#9%GHRI3EfWR1%2BR:%BB,HA%IB%0G,C:'DC6fT#0R:#:[P41A:HfXR:5^?%0PRP#G1QPC#9;EIP0%0LR0#G1Q0C#9/1If[%2LR0%BL,HA%IL%01,C0'DC6%0:R:#:[P4%G:fYR:#0/QC#9/1If^%2:RI%B:,HA%I:fZ#0,CI'DC6g00Z5RI#]%SI1v53%u5%t5RIP<P=P=P>P51r57R:g00Za1q5@R@C[,ZI%p=PIP<P=P=P>P5P@g00[HP:C[,ZIEoGk1jI>P4P2g00[oRIg00\OR>'h1e42=4I>dAg573CdbCbDbEX15%G4%93g00\o[[^15P4f\#0P9O2bBWAW@W:P3P4O2n2001000000120000000W0W?P3P4O2n2001000000121000000W0P3P4O2n2001000000121000000W0W>P3P4O2n2001000000121000000O1P3FiP4CN3lW=W4P3P4O2n2001000000121000000W0P4O1n200100000021000011000CNCNCNCNW9W<W6W7P3P4O2n2001000000121000000W0W8P3P4O2n2001000000121000000W0W3P3P4O2n2001000000121000000W0W;P3P4O2n2001000000121000000W0XK5WFWLXJ5XIEWHWGo"). Qed.

(* [comment removed for export] *)
Lemma pix1rc_of_1c : forall live (m m' : mem) pix v cv rc,
  pix1c live m pix v cv -> rw_cells asegs m' pix (pix_cells_rc v rc) ->
  (p_cmap v <> 0 -> keeps_live [(p_cmap v, 24)] m m') ->
  pix1rc live m' pix v cv rc.
Proof.
ltac2:(KReplay.run1 (kr_t_Po_pma1_defs ()) [] "h01Hh12D1h22DNh31Kh41Ph53PC'h62R0h72cvh84liveh91mh:2m'h;3pixh<2rch=1vp;2p;1p;5p;3p;4p;6p;:g0000j2LTg000Pj1KTg0010j11Tg001Uj1?Tg0023j1BTg002Vj1JTg00]Lj5GTg0038j5@Tg00^Fj17Tg0056j1ATg00L8j36Tg006Uj14Tg00_@j15Tg00>nR0j23Tg009Kj2<Tg00OZj48Tg007Rj12Tg00:Lj1ITg00;1j1FTg00;Qj39Tg00<1j3:Tg00`9j6>Tg00=3j6ETg00a4l:DTg00Nej4=Tg00QOj1HTg00RBj4CTg00TZR1f0R2g00U836#Hp=0P1P1f1R3P2CCp=;1L11R4#Kg00WUR5#1#1#1R6#1#1#1#?#B%?6#B#J[R6g00X:g00Y7f6R7f5R8f3R9f2R:P3DGP0f7R;P7f4R<P9P:D@%79%A5R=561%49#0%59'3'3g00SbR>P7P81<<:C8%28#0%27%I5#1#1#1#AR5';%F4R?594f9R@f8RA3:[f:RBPAP;P7P8P<E>[[P2P@PAP7P8P<D@%77=61=%47#0%57'3'3P0%7;=61=%4;#0%5;'3P>PBP@1<A7C8%2@#0%2B/;5=94?f=R7f<R<3:[f>R8P<f;RCPBP@PAE>[[P2%7@=61=%4B#0%5B'3P0%4C#0%5CP>P8P71<<BC8%27#0%28/;5=94?fARBf@R03:[fBR@P0f?RAP8P7P<E>[[P2%47#0%58P>PBP01<A7C8%20#0%2B/;5=94?fDR?fCR43:[fER5P4P@PBP0PAEE%7B=61=R=%4B#0R7%5BR>'3R8'3P5P?P4P@PBP0PAPCP3P2M:DP=P8P;P7P>P9P:C=C=C=W3W5W6W2P3P2O2n2001000000120000000W0W1P3P2O2n2001000000120000000W0W4P3P2O2n2001000000121000000W0X<1W7W=X;1X:6W9W8o"). Qed.

(* [comment removed for export] *)
Lemma pix1c_keep : forall live (m m' : mem) pix v cv, keeps_live live m m' -> pix1c live m pix v cv -> pix1c live m' pix v cv.
Proof.
ltac2:(KReplay.run1 (kr_t_Po_pma1_defs ()) [] "h01Hh11Kh21Ph31Rh42cvh54liveh61mh72m'h83pixh91vp;2p;1p;3p;5p;8p;4g0000j2BTg000Pj1ATg0010j11Tg001Uj19Tg0023j1;Tg002Vj1@Tg00<1j3=Tg00]Lj5:Tg0038j54Tg00^Fj16Tg0056j1<Tg00L8j32Tg006Uj17Tg00QOj13Tg00_@j15Tg00>nR0j20Tg00b>j8?Tg00Nej4>Tg00TZR1f0R2g00U832p=81B11#Ag00WUR3#1#1#1R4#1#1#1#9#;%94#;#@[R4g00X:g00Y7f5R5f4R6f3R73=f6R8P5P7f2R9f1R:D:P0f7R0P8P6P7P9D4%67%<3R3521%77#8#3%57'0'0f8R9P8P5P6P7D:P2f9R7P9P8P5P6D4%68=213%78#8#3%58'0'0f;R6P7P9P0P8D4%60=213%70#8#3%50'0'0P6f:P7P9P0P8P5P:G?P2C>W3W2P:P2O2n2001000000120000000W0W1W4W9X81X74W6W5o"). Qed.
(* [comment removed for export] *)
Lemma pix1c_mono : forall live live' (m : mem) pix v cv, (forall e, In e live -> In e live') -> pix1c live m pix v cv -> pix1c live' m pix v cv.
Proof.
ltac2:(KReplay.run1 (kr_t_Po_pma1_defs ()) [] "h01Hh11Ph21Rh31Sh42cvh51eh64liveh75live'h81mh93pixh:1vp;2p;1p;3p;5p;8p;4g0000j2BTg000Pj1ATg0010j11Tg001Uj19Tg0023j1<Tg002Vj1@Tg00DWj3;Tg00]Lj5:Tg0038j54Tg00^Fj16Tg0056j1=Tg00L8j32Tg006Uj17Tg00QOj13Tg00_@j15Tg00>nR0j20Tg00cBj8?Tg00Nej4>Tg00TZR1f0R2g00U832p=81B11R3#AR4g00WUR5#1#1#1R6#1#1#1#9#<%96#<#@[g00X:g00Y7f6R69;32f1R7=;36[^53P6f4R3f3R8f2R9P7D:P0f7R0f5R:P3P8P9D4%68%=5R5521%78#8#3%58'0'0P0P6P:P3P8D:P2f9R8P0P6P:P3D4%66=215%76#8#3%56'0'0f:R3P8f8R9P0P6D4%60=215%70#8#3%50'0'0f;P3P8P9P0P6P:P7G?P2C>W2W1P7P2O2n2001000000120000000W0W3W4W:X91W8X74W6o"). Qed.
(* [comment removed for export] *)
Lemma pix_obj_rc_mono : forall live live' (m : mem) pix v cv rc, (forall e, In e live -> In e live') ->
  pix_obj_rc live m pix v cv rc -> pix_obj_rc live' m pix v cv rc.
Proof.
ltac2:(KReplay.run1 (kr_t_Po_pma1_defs ()) [] "h01Hh13HCMh22HDh31Rh41Ch52CHh63HOKh71Sh82cvh91eh:4liveh;5live'h<1mh=3pixh>2rch?1vp;2p;1p;3p;6p;4p;7g0000j2VTg000Pj1UTg0010j1=Tg001Uj1LTg0023j1PTg002Vj1TTg00DWj3OTg00=3j6CTg009Kj2JTg00OZj4ITg0056j1STg005Tj1<Tg006Uj11Tg007Rj12Tg008Oj13Tg00>2j35Tg00>nR0j20Tg00PSj1>Tg00?Ij4;Tg00dBj6NTg00@Hj3MTg00Nej4?Tg00O@j3KTg00e@j7QTg00L8j34Tg00QOj16Tg00QhR1j2GTg00TZR2f5R3g00U8R434f4R5f3R6f2R7#>35f1R8f0R9542#6'0'Gp=9A4235#6A4267#6A4289#6'0'0p=8f7R:=424f6R;P3P5P6C;A4278#6/09'0'Gp=71089,07p=FA5678/09p=DA4294p=:A4289#6p=@1089,G7p=EA4267#6A4289#6'0p=BA4256#6A4278#6/09'0p=A%>99578p=RP5P6P7P8C;/09p=H1V22R4#UR<g00WU#=#=#=R=#=#=#=R>#L#P%L=#P#T[g00X:g00Y7AO49:AO48:[^94P:P3P5P6P7P8ECP0g00SbR4P;P31J57CIf8R7P3%S>R>%<5%15R=P7P=P5P=P3E9%25R?P7P;P?P6P?P3%36R@P3P?P=P@P=E8G73FCDP7P:P;P3P5P6ECP9P4P7P:1J;5CIf;R5P7P>%<:%1:R6P5P6P:P6P7E9%2:R=P5f9R@P=P;P=P7%3;R;P7P=P6P;P6E8G73FCDP0f<R6?5@>%<7%17R;P6P;P7P;P@E9%27R=P6f:R?P=P:P=P@%3:RAP@P=P;PAP;E8G73FP6P5P?P@P7P:ECP9f>R:?55>%<5%15R7f?R;P7P5P7P6E9%25RAP;f=R=PAP?PAP6%3?R?P6PAP7P?P7E8G73FP0%<6%16R7f@R?P7P6P7P=E9%26RAP?P:PAP5PAP=%35RBP=PAP7PBP7E8G7'0P?P;P:P=P6P5ECP9%<:%1;R5fCR6P5P;P5P?E9%2;R7P6fARBP7P:P7P?%3:R:P?P7P5P:P5E8G7'0P0%1?R5fDR:P5P?P5PBE9%2?R7P:fBRAP7P;P7PB%3;RCPBP7P5PCP5E8G7P:P6PAPBP?P;ECP9%1AR;fFR?P;PAP;P6E9%26R;fGR5fERCP;PAP;P:%3AR7P:P;%16R;P7P;E8G7P4P?PC1J:ACIA55C>RA%<:R4%1:R;#:R7%>:RD955;1@;CRE3ERF%2:RG#:RHP5P?PGP6C;PGPC%36RIPCPGP;PIP;CBDARI3ERJ'0RK'0RL'0P=PAPLfHRLP5PCP>PBP@ENP4PKP3PFPJP1P7PLP;PDPECD%1CRE#:RD%>CR;95LE1@E?R73EP8%1?RJ#:fIRFPJ%>?R31@J5RKCD;M9X2DP9O1PFPEP;P7CDP0fJR7?5J3PK%15RKP7PKP5PKPLE9P9fLR3%1L;RL%1FR;/@7%17RD#:fMR4%>7R@75DRBfKR>,@DRA'0PBPAfNRAP4PDP@P5P8ENP9C?3KW3W2P8P9O2n2001000000120000000W0P9O1n200100000021000010000P1PHPLP?PGP6PIDH%2CRI#:R6PLP5PIP:C;PIP?%3:RGP?PIPEPGPECBDARE3EP9%2?RG#:PFPLPGPCPGP5%3CRHP5PGPJPHPJCBDARJDH;M9X16P9O1PFP5PIP:PEDHP0P7PLPGPCC;PJ%25RJP7PFPJP?PJPL%3?R?PLPJPKP?PKE8G7P9P3P7%2LP5C;%2FRKP7%3LRLP7PKP;PLP;CBDA%27R7#:P4P3P7PFC;R;P7P>%3FRLP>P7PDPLPDCBDARD'0P;PDPAP4P3P7PFP5P8FQP9C?3KW3W1P8P9O2n2001000000120000000W0P9O1n200100000021000011000C?C?C?C?W1W2P8P9O2n2001000000121000000W0W6P8P9O2n2001000000121000000W0W5P8P9O2n2001000000121000000W0W4P8P9O2n2001000000121000000W0W7X>2W8W?X=2W<X;<W:o"). Qed.
Lemma pix1rc_mono : forall live live' (m : mem) pix v cv rc, (forall e, In e live -> In e live') ->
  pix1rc live m pix v cv rc -> pix1rc live' m pix v cv rc.
Proof.
ltac2:(KReplay.run1 (kr_t_Po_pma1_defs ()) [] "h01Hh11Ph21Rh31Sh42cvh51eh64liveh75live'h81mh93pixh:2rch;1vp;2p;1p;3p;6p;9p;4g0000j2BTg000Pj1ATg0010j11Tg001Uj19Tg0023j1<Tg002Vj1@Tg00DWj3;Tg00`9j6:Tg00=3j64Tg00^Fj16Tg0056j1=Tg00L8j32Tg006Uj17Tg00QOj13Tg00_@j15Tg00>nR0j20Tg00fAl9?Tg00Nej4>Tg00TZR1f0R2g00U832p=81B11R3#AR4g00WUR5#1#1#1R6#1#1#1#9#<%96#<#@[g00X:g00Y7f7R69;32f1R7=;36[^53P6f5R3f4R8f3R9f2R:P7E:P0f8R0f6R;P3P8P9P:E4%68%=5R5521%78#8#3%58'0'0P0P6P;P3P8P9E:P2f:R9P0P6P;P3P8E4%66=215%76#8#3%56'0'0f;R8P9f9R:P0P6P;E4%60=215%70#8#3%50'0'0f<P8P9P:P0P6P;P3P7M9?P2C>W2W1P7P2O2n2001000000120000000W0W3X:1W4W;X91W8X74W6o"). Qed.
(* [comment removed for export] *)
Lemma pix1c_retarget : forall live (m m' : mem) pix v cv,
  pix1c live m pix v cv -> rw_cells asegs m' pix (pix_cells v) -> (p_cmap v <> 0 -> keeps_live [(p_cmap v, 24)] m m') ->
  pix1c live m' pix v cv.
Proof.
ltac2:(KReplay.run1 (kr_t_Po_pma1_defs ()) [] "h01Ch11Hh22Heh31Kh41Ph51Rh62cvh71eh84liveh91mh:2m'h;3pixh<1vp;2p;1p;5p;3p;4p;Bg0000j2OTg000Pj1NTg0010j10Tg001Uj1<Tg0023j1CTg002Vj1MTg00]Lj5?Tg0038j58Tg00^Fj19Tg0056j1;Tg00L8j36Tg006Uj17Tg00QOj14Tg00_@j1:Tg00>nR0j21Tg0046j1BTg00OZj4ATg007Rj15Tg00:Lj1LTg00RBj4@Tg00;1j1KTg00;Qj3>Tg00<1j3=Tg00gIj1GTg00hCj1FTg00i=j1HTg00DWj3ETg00j9lBITg00Nej4JTg00K2j2DTg00TZR1f0R2g00U836p=31D12p=21O11R3#Ng00WUR4#0#0#0R5#0#0#0#<#C%<5#C#M[R5g00X:g00Y7f5R6f4R7f2R8f1R9P2D?P0f6R0P6f3R:P8P9D8%98%;4R;561%78#3#4%:8'1'1g00SbR<P6P7%B:CA%57#3#4P1P1%56%L4#0#0#0#;R4C@%K3R=5>3f8R>f7R?3=[f9R@P?P0P6P7D?[[P2P>P?P6P7P:D8%96=61;%76#3#4%:6'1'1P<P>P?%B0CA%5?#3#4P1P1%5>R0P4C@=>3=f;R=f:R43=[f<R<P4P@P>P?D8%9>R6=61;%7>R;#3#4%:>'1'1P<P<P=P4P@P>P>P?P:P9%G>#2%F>#2%26%H>#2%2;%20f=9E32P2W2X73P2MBIP8CJW3W0W5W4P9P2O2n2001000000120000000W1W6W<X;1X:5W9W8o"). Qed.
(* [comment removed for export] *)
Lemma pm_copy_live_sub : forall pixd v cv live e, In e live -> In e (pm_copy_live pixd v cv live).
Proof.
ltac2:(KReplay.run1 (kr_t_Po_pma1_defs ()) [] "h01Hh12cvh21eh34liveh44pixdh51vp;2p;1p;3p;5p;4g0000j2DTg000Pj1CTg00DWj31Tg007Rj17Tg00k=j2BTg00;1j1<Tg008Oj1;Tg0010j10Tg0056j14Tg00B=j19Tg00C<j28Tg00:Lj1:Tg00;Qj32Tg006Uj1ATg00PSj1=Tg00L8j36Tg00O@j35Tg00kZj5>Tg00l8j4?Tg00RBj4@Tg00TZR0P0f1R1f0R2C@p=3g00X:g00Y71D00R3#CR4A1321P3g00[oP4f4R4#7R5g00U8'B%<3R6f3R7#;g00WUR8#0#0R9#4%97'8'3%:8#0#0#0#4,35=236523n0100000020000R6%A4%=4'3R5f5R8%09#0#0#0#4'3R9f2R:523R;523R<P1A1316A131<A6351A131;A6391A131:;523535D>P8P4P7P:C?9131eW0X23W3W1W5X40o"). Qed.
Lemma pm_copy_live_pix : forall pixd v cv live, In (pixd, 64) (pm_copy_live pixd v cv live).
Proof.
ltac2:(KReplay.run1 (kr_t_Po_pma1_defs ()) [] "h02cvh14liveh24pixdh31vp;2p;1p;3p;5p;4g0000j2FTg000Pj1ETg007Rj1<Tg00k=j27Tg00;1j1DTg008Oj1@Tg0010j10Tg0056j14Tg00B=j1:Tg00C<j29Tg00:Lj18Tg00;Qj33Tg006Uj1CTg00PSj1BTg00DWj31Tg00L8j35Tg00K2j2?Tg00@Hj3>Tg00O@j36Tg00kZj5=Tg00l8j4ATg00RBj4;Tg00TZR0P0f1R1f0R2C;p=2g00X:g00Y71F00R3#ER4P3g00[oP4f2R4#<R5g00U8'7%D3R6%@1g00WUR7#0#0R8#4%:1'9'2%87#0#0#0#4,25=336533n0100000020000R6%C4%B4'2R5f3R7%08#0#0#0#4'2R8=332R9533R:P8A1386A138:A5358A1389A5388A13821?383>3636D=P7P4P1P2CA9138eW1W0W3X20o"). Qed.
Lemma pm_copy_live_data : forall pixd v cv live, In (p_data v, rsize v) (pm_copy_live pixd v cv live).
Proof.
ltac2:(KReplay.run1 (kr_t_Po_pma1_defs ()) [] "h02cvh14liveh24pixdh31vp;2p;1p;3p;5p;4g0000j2FTg000Pj1ETg007Rj1:Tg00k=j25Tg00;1j1DTg008Oj1<Tg0010j10Tg0056j14Tg00B=j17Tg00C<j26Tg00:Lj18Tg00;Qj33Tg006Uj1CTg00PSj1BTg00DWj31Tg00L8j3=Tg00K2j2>Tg00@Hj3?Tg00O@j3;Tg00kZj5@Tg00l8j4ATg00RBj49Tg00TZR0P0f1R1f0R2C9p=2g00X:g00Y71F00R3#ER4P3g00[oP4f2R4#:R5g00U8'5%D3R6%<1g00WUR7#0#0R8#4%71'6'2%87#0#0#0#4,25=336533n0100000020000R6%C4%B4'2R5f3R7%08#0#0#0#4'2=332R8533R9P5A1356A1359A=355A13581>353?3;D@P7P4P1P2CA9135eW1W0W3X20o"). Qed.
Lemma pm_copy_live_cmap : forall pixd v cv live, p_cmap v <> 0 -> In (p_cmap v, 24) (pm_copy_live pixd v cv live).
Proof.
ltac2:(KReplay.run1 (kr_t_Po_pma1_defs ()) [] "h02NZh11bh22cvh34liveh44pixdh51vp;2p;1p;3p;5p;4p;6g0000j2LTg000Pj1KTg007Rj17Tg00QOj18Tg00:Lj1JTg0010j10Tg0056j16Tg00;1j1@Tg008Oj1;Tg00B=j1:Tg00C<j29Tg00;Qj32Tg006Uj1?Tg00PSj1>Tg00m9j3ITg00DWj33Tg00L8j34Tg00K2j2ETg00@Hj3<Tg00O@j3DTg00kZj5CTg00k=j2=Tg00mVj2BTg00n7j4ATg00nRj6FTg00l8j4GTg00RBj4HTg00TZR0f0R1g00U8R234p=5P0P0f1R3P1CHp=1g00X:g00Y71L00R4#KR5f2R6#7#5#8g00[oR7g00o0R8f4R9#7R:g00WUR;#J#0#0#0#6R<'1R=P7P5P1%@4R5f3R>#;%0;#0R;#6R?%:>'9'1A24=5524n0100000020000%?9%>9'1f5%0;#0#0#0#6R;'1=2465245I4534X17P4%;6%:6,9?'1R?%7>R=/1<R<=245R@524RA%?>%>>'1119;=243524R;P<A34<AA34<;A44?<A34<@A44<<A34<51E4<3<3D3<DC1==2R5A4758%5:#8[%5=#81=:2=478[1B=2P1CAEFP9P>P6P3CG934<eW0W3W2W5X40o"). Qed.

(* [comment removed for export] *)
Lemma sel_obj_keepP : forall live (m m' : mem) sel sv, keeps_live live m m' -> sel_obj live m sel sv -> sel_obj live m' sel sv.
Proof.
ltac2:(KReplay.run1 (kr_t_Po_pma1_defs ()) [] "h03rowh12rph21Hh34__x1h47__arithh54cstrh64__ffh78__varmaph85__with94__x2h:4__x3h;5cstr0h<1nh=1xh>1lh?2l0h@1mhA2ARhB3ARRhC2B1hD2B2hE2B3hF2B4hG2CHhH3CHDhI3CHRhJ2HFhK2IHhL1KhM2L1hN2L2hO2LRhP2NDhQ4ROWShR2SChS4livehT2m'hU4rowshV3rpshW3selhX2svhY1yp%0p&0p;2p;1p;3p;4p;<p;6p;9p;5p;7p;Bp;8g0000k20ZTg000Pj1dTg0010j1PTg001Uj1wTg0023k107Tg002Vk10UTg00<1k30TTg00oPj4ATg010Lj1eTg00OZj4sTg0056j1STg011Jj1<Tg012Ej13Tg013>k10YTg013dj17Tg014_j1:Tg015Zj10Tg00:Lj1hTg016SR0j21Tg016oj16Tg017hj15Tg00>2j3JTg018aj2HTg00Rbj2DTg00C<j2>Tg019AR1j1GTg00>nR2j22Tg00DWj3qTg00Dnj2pTg019aj3mTg01:<j1lTg00;1k10STg00ENj2jTg00Elk10RTg00FJk10QTg00GXj2iTg00JPk20PTg00K2j2ZTg00KLk20OTg00L8j3ITg00LRk30NTg00M1k40MTg01:aR3j2?Tg01;>k10LTg01;\k40KTg01<?m<0HTg00G5j2fTg01<dj3_Tg01=Gk40GTg01>2k10FTg01>nm<0ETg01@6j2|Tg01@_k30DTg01AHk20CTg01B4k20BTg00;Qj3FTg01B`k40ATg00H;j4yTg00Hfk10@Tg01C>j3aTg01Cak400Tg00nRj6{Tg01D@m<0?Tg01EDk30>Tg01Ebm<0=Tg01Ffm90<Tg01GDm90;Tg00Nej4gTg01Gdk401Tg01H@j4uTg01I6j4cTg01Ilj2nTg01JHk503Tg00RBk40:Tg00S>k709Tg01Jfj1WTg01KEm<08Tg01KjmB0VTg00Ilk80XTg00SbR4f4R5f3R6g00TZR7f2R8f1R9f0R:H01Cup=O1H79#G=I7:p==P7P8P9P:H01p=N1H7:#Gp=]P4P5P6P8CcAI79:'2p=81>899J56/2:p=4AF79:9F78,n7p=Mg00U8R;/161D89'2/2:p=9f7R<f6R='1f5R>/15'211;61D89'2/2:'2p=;P7P<P=P>P5I031168/29/2:'2p=@1H68#G=I79/2:p=E129:,28p=CAJ689/2:p=`1>9:9J68p=[AI789/2:p=~%<9=F7:9F78,n7p=U%G9=I7:p=tP7P6P8P9P:I03p=B11561189'2/2:p>06%<9%7:5F79F78,n7p=K1189/2:p=Y11;=1D>5'211;61D89'2/2:'2p>0511;9/2:p=XP4P8P9P:Cup>0W1H7:p>04AI79:p=^P7P7P9P:H0:p=r1D;:p=VAI7:;p=o11;:p=kP7P9g01LPP:Cyp=bP9g00UVR?g00V5R@P@g00VURAP:g00W5K09p=\%W:#Wp>02%W:#W#W#Wp=Qg01M7RBP7P7P7P1P1P>P5P6P8P9P:N<08p>0JP7P7P7P7P7P7P3P:P9P8P3P6P5P>P=P<f8R3f9R1NB0Vp>0IP6P?P@P@PAP8P9P:L0Xp=xP4P8P9P:Ccp=LAJ=>5P4P6P8P9Cc/2:'2p=zP4P6P8P9Cc/2:p=vAI79:,28p=TAF79:p=}P=P>P5P6P8P9P:CgCgp=R20Z77R?#dg00WURC#PRD#PRE#PRF#PRG#PRH#P#wRI$07RJ%wF$07$0U[RKg01MVB0T568P>P5P8P9CAP2P4P>P6%e8CsP=P6%SHRHP=%<8RL%SFRF%38RMP>PLPJ&0YIRI%78RNDO1=NM%d7RO%:8RPPMPOP3P9%SERE%05RQP<P9ANJI:RR%]:RSPQD8D4X0OX17PNPP%SCRPPM%hCRQ#h#h#P#SRT,1MPP%08RUPUPT%68RVPVPM%58RMPMPUAM6LNC9G;G@CE3CD4C`P<P>P5P6CAP:P4P<P>%e5CsP1P=PHP1%<>RNPF%3>RLP3PNPJPI%7>RUDO1=ULPO%:>RMPLPOf;RVP9PE%0<RWf:RXP9PRPSPWD8D4X0OX17PUPMPPPL11LTPP%0>RMPMPT%6>RWPWPL%5>RLPLPMAM=NUC9G;G@CE3CD4C`P2AJX<HPX%<=RUPF%3=RNP1PUPJPI%7=RMDO1=MNPO%:=RLPNPOf<RWP9PE%03RYPVP9PRPSPYD8D4X0OX17PMPLPPPN11NTPP%0=RLPLPT%6=RYPYPN%5=RNPNPLAM<UMC9G;G@CE3CD4PVP1P3P<CAP:AJW1Hf=RM%<1RUPF%31RLPWPUPJPI%71RNDO1=NLPO%:1RYPLPOf?RZP9PE%0VR[f>R\P9PRPSP[D8D4X0OX17PNPYPPPL11LTPP%01RYPYPT%61R[P[PL%51RLPLPYAMXUNC9G;G@CE3CD4P2P\%<XRNPF%3XRUC[PMPNPJPI%7XRYDO1=YUPO%:XRLPUPOf@R[P9PE%0WR]PZP9PRPSP]D8D4X0OX17PYPLPPPU11UTPP%0XRLPLPT%6XR]P]PU%5XRUPUPLAMVNYC9G;G@CE3CPZPMPWPVCAP:P[%<WPF%3WC[P[%<MRYPJPI%7MRNDO%3MRL,=NPO%:MRUPLPOfCR]P9PE%0ZR^fBR_P9PRPSP^D8D4X0OX17PNPUPPPL11LTPP%0MRUPUPT%6MR^P^PL%5MRLPLPUAM\YNC9G;G@CE3CP2fARN%<\RYPJPI%7\RUDO%]U%3\RLPO%:\R^PLPOfDR`P9PE%0[RaP]P9PRPSPaD8D4X0OX17PUP^PPPL11LTPP%0\R^P^PT%6\RaPaPL%5\RLPLP^AMZYUC9G;G@CE3~P]PNP[PZCAP:P]%<[PJPI%7[DO%7NRU#]%3NRYPO%:NR^PYPOfGRLP9PE%0]RafFRbP9PRPSPaD8D4X0OX17PUP^PPPY11YTPP%0NR^P^PT%6NRaPaPY%5NRYPYP^AU_NUC9G;G@CE3~P2%7_RU%3_RN'=PO%:_R^PNPOfHRYP9PE%0`RaPLP9PRPSPaD8D4X0OX17PUP^PPPN11NTPP%0_R^P^PT%6_RaPaPN%5_RNPNP^AU]_UC9G;G@CEPLfERUP`P]CAP:%7`%3`'=PO%:UR`%3UR_POfKR^P9PE%0LRNfJRaP9PRPSPND8D4X0OX17%7URNP`PPP_11_TPP%0UR`P`PT%6URcPcP_%5UR_P_P`AUbUNC9G;G@CEP2%:bRN,HO%3bR`'tPOfLR_P9PE%0YRcP^P9PRPSPcD8D4X0OX17%7bRcPNPPP`11`TPP%0bRNPNPT%6bRdPdP`%5bR`P`PNAULbcC9G;G@P^fIRcPYPLCAP:%:Y,HO%3Y'tPOfORYP9PE%0^RLfNRbP9PRPSPLD8D4X0OX17%7cRL%:cPP%3cRN11NTPP%0cR`P`PT%6cRdPdPN%5cRNPNP`AUacLC9G;G@P2POfPRLP9PE%0_R`PYP9PRPSP`D8D4X0OX17%7aR`%:aCBPP%3aRNPNPTPP%0aRdPdPT%6aRePePN%5aRNPNPdAU^a`C9G;I06PYfMR`P_P^CAP:POfRR^P9PE%0bRafQRdP9PRPSPaD8D4X0OX17%7_%:_CBPP%3`RNPNPTPP%0`RePePT%6`RfPfPN%5`RNPNPeAKb``C9G;I06P2%3bRe11eT5YPPPPaPaPT%6bRNPNPe%5bRePePaAKYbbC9G;fSRbPdPLPYCAP:%3LRL11LT5YPPP%0dRLPLPT%6dRYPY%3d%5dRYPYPLAK^ddC9G;P2%0^RL11LT5YP%6^RYPY%3^%5^RYPYPLAKb^^K05fWR^fURLfTRYPbCAP:%0YRY11YT5YP%6LRYPY%3L%5LRYPY%0LfVRY?KLLK05P2%6YRb%3Y,Db'X%5YRbPb%0YAK^YYC9f[RYfYRbfXRaP^CAP:%6aR^%3a,D^'X%5bR^P^%0bfZR^?KbbC9P2%5^Ra%0^,Da'XAKY^^f_R^f]Raf\RePYCAP:%5eRY%0e,DY'Xf^RY?KaaP4f`R4P^%eYReCsfbRN?J^HS00%<YRf%3YRg,>FRh5JNS01%7YRi9NJIRj:0W4fS02&04iRk#GRl/^gS03%:YRm,HO/tgS04POfdRnP9PE%04RoPNP9PRPSPoD8D4X0OX17PiPmCBS0511gT9YPgS06%0YRo11oT5YPS07%6YRP1DPg'XS08%5YRY1DYo'XS09AM^fiS0:'2S0;'2S0<'2S0='2S0>'2S0?'2S0@'2S0A'2S0B'2S0C'2PNfaRYP4P^PHP^PePa1r^H=q?N%V^%SGRG,p^#o%VH3C;mL%lkRo%klRl%:^,HORP#lRg%GP#kRPg00Z5RT$0SRp%dTRq1j79Rr&0R7Rs&0Q7Rt1i7CRC/bC'\20PtARAP:P8g00[oRug00\ORv'Z20O:8=IuvdB0N7;9H0MR;b6b7b8X37Rv11::^37RuP:PNO1Rwb4b;b5g01NQRx$02Ry$02#Q#Q#Q#Q#Q#Q#QRz#GR{,?^R|1?^HR}'111}}P7P7P0P:X=7R~P0119:$0LXY7X=7P|P}P~P~P~P7P7g01O01?9:H0K,Z7X@7X<7P^P^1Z7^P{PHP~P~%G:R~,Z7X=BPzPH1Z7HJ0JN:0IP}P}1Z7}N<0HPoPlPgPPPpPqPrPs1f7H9_7CRr/br,\tPAP;b6b7b8X371?:HRH/1H^37Pwb4b;b5H0G&0Fe#G,?^/1}ePbN<0EQ00Q0CPLQ01Q0BPdQ02Q0APNPYP4PfPhPfPjPa1rfh=q?N%Vf1pfG#o%Vh3C;mdPoPlPgPPPvPuP:%<YRdO1b4b;b5PBPk%<^Rk1>F~'?%3^,>F,?k'1X<BPoPlPgPP1|7xRx1|7y:0D7xg01OT+0C+0B=FTpRpPqP71j78P91j76H0ARTPsPtP71i7DRDg00[H1i7QRQCy,\tRx&0@@R@1f7FRy=a7D9_7CAa7yQ9_7C'b,\tCxPAP;b6b7b8X37X97X:71^98Ry1>F8,?91>F6,?9'1[^37^97^:7P:%3Y%7Y#]PdP_O4b4b;b51HJjP7PJPIPiH00E{P`N<0?Q03Q0@PcQ04Q0?PUQ05Q0>Pm%dORm%7^POP7POffR^P9PE%0NRNC[RUfeRc?L9R1^SNRN3CX0OX17POfhR`P9%0nRi,>ERjP^P9PR1^SiFzX0OX17P9P:CBX>mX?OALn9R=CUNX0OX17:0>7OP`P6PjfgRjP6ANJI81=8iFzP2fiRiP5PE%0cRcC[P`P5ANJI61=6cCvPOflRcP9PE%0`R`fkRN?L9RRU?TS`D4X0OX17P6P8CBPOfmRnP9PE%0iRiATUSiD4X0OX17P5P6CBPOfnRUP9PEfj#0R^PcP9PRPSP^D8D4X0OX171}<>AFO=5CB[[P:PNP=PE%0jC[PNP<ANJI=1==`CvP2ANJI<9Lc31=<iPOfpRiP9PE%0cRcfoR2?L9RR`?TScD4X0OX17P<P=CBPOfqR=P9PE%0nRnAT`SnD4X0OX17P3P<CBPOfrRnP9PE%0UR`PiP9PRPSP`D8D4X0OX171}V1AFOX3CB[[P:ANJI19LUX1=XcPOfsRcP9%02R2,>ER3ALn9RR`?TS2C`X0OX17PXP1CBPOftP9%0iRi,>ERNAT`SiC`X0OX17PVPXCBP7POfuP9PE%0=RXPcP9PRPSPXD8D4X0OX17P\PMPWPVAJc\3ANJIMRV9L=\RW&04MRS#GRR/^2R2'2P<PWP2PcPnP=P\P3P\PVPU1r\3=q?c%V\1p\G#o%V33C;m<%lSR<%kRRRPvPuP:P[O1b4b5PBPS1>E~,?Z1?ZN'1X<BP<PRPpPqPTPsPtPxP@1f7ER@=a7D9_7CAa7@Q9_7C'b,\tCxPAP;b6b7b8X37X97X:71>E8,?91>E6,?9'1\y^37^97^:7P:PX%]ZP[P5O4b4b51HJVP7PJPIPMH00E{P6N<0=P8FRP:N90<WKWJWOWAP9P:O2n2001000000121000000W2WIP9P:O2n2001000000121000000W2XUmXVOX0OX17P:P9P]N90;b?b>Q06Q0=PMQ07Q0<P1Q08Q0;P>Q09Q0:P9P:CgFRFRFRFRFRWPWFP9P:O2n2001000000121000000W2WEP9P:O2n2001000000121000000W2WDP9P:O2n2001000000121000000W2WCP9P:O2n2001000000121000000W2WQP9P:O2n2001000000121000000W2WNP9P:O2n2001000000121000000W2WMP9P:O2n2001000000121000000W2WBP9P:O2n2001000000121000000W2WHP9P:O2n2001000000121000000W2WGP9P:O2n2011000000121000000W2WRP9P:O2n2011000000121000000W2WLWXXW7XTKW@WSo"). Qed.

(* [comment removed for export] *)
Ltac shbr_beqz :=
  lazymatch goal with
  | |- evt ?segs ?Q (MS ?R ?F (if ?c then Z_to_bv 64 ?FAST else Z_to_bv 64 ?SLOW) ?fc ?rv ?m ?ro) =>
      let b := shbyte_of c in
      lazymatch goal with
      | K : shk m b ?X |- _ =>
          let OK := fresh "SHOK" in
          first [ match goal with
                  | ACC : acc asegs m ?a ?n |- _ => assert (OK : sh_ok b (X + 8 - 1)) by (apply (shk_ok m a n X 8 b ACC K); lia)
                  end
                | fail 1 "shbr_beqz: cannot prove the 8-byte access addressable:" X ];
          apply sh_ok_8 in OK; [ | lia ]; rewrite ?(sxb_small b) by lia; brT; clear K OK
      | _ => fail "shbr_beqz: no shk fact for" b
      end
  end.

(* [comment removed for export] *)
Ltac frame_release_p RT AF GP MST Σ0 LV0 FRS0 fr k SZ PF AGF PFS usp lo LOW LOR pcstore pcafter ivt pft pre :=
  cps_stop;
  art_now RT AF ivt;
  lazymatch goal with AGFx : agree_on ?PFx _ ?mm, MUx : munch _ ?mm _ |- _ => is_var PFx; agf_munch AGFx MUx pft end;
  lazymatch goal with A : ART RT ?S ?mm |- cps _ (ASTA RT ?S _ (eq (MS _ _ _ _ _ ?mm _))) _ =>
    let FRSc := fresh "FRSc" in
    assert (FRSc : rt_frames RT S = (fr, k) :: rt_frames RT Σ0)
      by (repeat match goal with H : rt_frames _ _ = _ |- _ => rewrite H end; reflexivity);
    let S2 := fresh "S2" in let fl := fresh "fl" in let FLC := fresh "FLC" in let FLN := fresh "FLN" in let FL0 := fresh "FL0" in
    let FLHI := fresh "FLHI" in let FLP := fresh "FLP" in let REL := fresh "REL" in
    destruct (af_frame_release RT AF S mm fr k _ A FRSc) as (S2 & fl & FLC & FLN & FL0 & FLHI & FLP & REL);
    change (fs_size k) with SZ in FLP;
    let off := eval vm_compute in (SZ - 8)%Z in replace (fr + SZ - 8)%Z with (fr + off)%Z in FLP by lia;
    repeat match goal with H : rt_sp0 RT _ = _ |- _ => rewrite H in FLHI end; unfold STACK_WIN in FLHI;
    repeat match goal with
    | IN : In (?b, ?kk) _ |- _ =>
        lazymatch goal with
        | _ : fl < b \/ b + kk <= fl |- _ => fail
        | _ => let FA := fresh "FLA" in
               assert (FA : fl < b \/ b + kk <= fl)
                 by (apply (flag_apart _ _ fl b (b + kk) FLN); let x := fresh "x" in let Hx := fresh "Hx" in intros x Hx;
                     right; right; left; exists b, kk; split; [solve [in_live_tac] | exact Hx])
        end
    end;
    let FLG := fresh "FLG" in
    assert (FLG : forall b kk, In (b, kk) (rt_live RT S) -> fl < b \/ b + kk <= fl)
      by (let b := fresh "b" in let kk := fresh "kk" in let Hb := fresh "Hb" in intros b kk Hb;
          apply (flag_apart _ _ fl b (b + kk) FLN); let x := fresh "x" in let Hx := fresh "Hx" in intros x Hx;
          right; right; left; exists b, kk; split; [exact Hb | exact Hx]);
    pre fl FLN;
    let LHs := fresh "LHs" in let SSPs := fresh "SSPs" in
    lazymatch goal with LHx : LIBH mm |- _ => pose proof LHx as LHs; hide LHs end;
    lazymatch goal with SSPx : io_ssp mm |- _ => pose proof SSPx as SSPs; hide SSPs end;
    (* [comment removed for export] *)
    repeat match goal with H : LIBH mm |- _ => clear H | H : io_ssp mm |- _ => clear H end;
    repeat match goal with H : acc asegs mm _ _ |- _ => clear H | H : ro_cells asegs mm _ _ |- _ => lazymatch type of H with ro_cells _ _ (fr + _) _ => fail | _ => clear H end end;
    walk_to AF MST [(fl, fl + 1)] [pcstore];
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?ml _) => repeat match goal with H : ro_cells asegs ml (fr + _) _ |- _ => clear H end end;
    awalk [pcafter];
    cps_stop;
    lazymatch goal with MUx : munch [(fl, fl + 1)] mm ?m', WMx : wmono asegs mm ?m', FLC' : rw_cells asegs ?m' fl _ |- _ =>
      let ART2 := fresh "ART2" in let FRS2 := fresh "FRS2" in let LV2 := fresh "LV2" in let SP2 := fresh "SP2" in
      let CR2 := fresh "CR2" in let AL2 := fresh "AL2" in let AM2 := fresh "AM2" in let AGS := fresh "AGS" in
      destruct (REL m' MUx WMx FLC') as (ART2 & FRS2 & LV2 & SP2 & CR2 & AL2 & AM2);
      assert (AGS : agree_on client_static mm m')
        by (let a := fresh "a" in let Ha := fresh "Ha" in intros a Ha; apply MUx; cbn [outside]; split; [| exact I];
            let Hin := fresh "Hin" in intros Hin; apply FLN; replace fl with (bv_unsigned a) by (clear - Hin; lia); right; left; exact Ha);
      unfold hid in LHs, SSPs;
      let LH2 := fresh "LH" in let SSP2 := fresh "SSP" in
      assert (LH2 : LIBH m') by (exact (LIBH_agree RT GP client_static mm m' LHs AGS (fun a Ha => Ha)));
      assert (SSP2 : io_ssp m') by (exact (io_ssp_agree RT GP client_static S2 mm m' SSPs ART2 AGS (fun a Ha => Ha)));
      (* [comment removed for export] *)
      let FL1 := fresh "FL1" in let FL2 := fresh "FL2" in
      assert (FL1 : fl + 1 <= lo) by (clear - FLHI LOW; lia);
      assert (FL2 : lo <= usp) by (clear - LOR; lia);
      agf_munch AGF MUx ltac:(fun Hx => cbn [outside]; split; [| exact I]; let Hin := fresh "Hin" in intros Hin;
        lazymatch type of Hx with PF ?z =>
          apply (flag_not_client _ _ LV0 FRS0 fl lo usp FLN FL1 FL2);
          [ first [ solve [live_sub_tac] | solve [live_add_tac]
                  | solve [let e := fresh "e" in let He := fresh "He" in intros e He;
                           repeat match goal with H : rt_live _ _ = _ |- _ => rewrite H end; auto] ]
          | solve [frames_sub_tac] | replace fl with z by (clear - Hin; lia); first [exact Hx | exact (proj1 Hx)] ] end);
      clear FL1 FL2;
      let KEEPR := fresh "KEEPR" in
      assert (KEEPR : forall b kk, In (b, kk) (rt_live RT S) -> forall a : word, b <= bv_unsigned a < b + kk -> m' a = mm a)
        by (let b := fresh "b" in let kk := fresh "kk" in let Hb := fresh "Hb" in let a := fresh "a" in let Ha := fresh "Ha" in
            intros b kk Hb a Ha; apply MUx; cbn [outside]; split; [| exact I]; let HF := fresh "HF" in pose proof (FLG b kk Hb) as HF; clear - HF Ha; lia);
      apply (cps_ASTA_switch RT _ S2 _ _ _ AL2 AM2);
      clear REL LHs SSPs FLC FLN AGS FLG
    end
  end.
