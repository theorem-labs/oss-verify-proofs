(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Lib Require Import Tac Image ZBridge SysStep Walk Arr ITree Nodes Decode.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Common Require Import SFModel.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Malloc Require Import MallocRep F_malloc_free F_malloc_fast F_malloc_enframe MallocTree MallocBlocks MallocFacts_B.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Spec Require Import STree Malloc MallocCtrl Monad.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Malloc Require Import ProgDeps.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Malloc Require Import MallocKit_B MallocKit_B2 MallocModel_B F_ntf_A F_ntf_B F_ntf_C.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Malloc Require Import MallocKit_B3 F_ntf_D F_ntf_E F_ntf_F F_ntf_G F_ntf_H.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Malloc Require Import MallocFacts_Bpres.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Common Require Import RunDraw.
From OSSVerify.Proofs.zstd.huf_decompress.lib Require KReplay.
Ltac2 kr_t_F_ntf () := "C35stdpp4base6LookupC59OSSVerify5KrLib4Spec6Malloc4aptrC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec5STree5stree00C1?~~~~~~~~~~~~~~~I35stdpp9countable9Countable00C35stdpp4base;RelDecisionC35stdpp4gmap;gmap_lookupC35stdpp4base4fmapC59OSSVerify5KrLib4Spec6Malloc4optrC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic8eq_ind_rI35stdpp4gmap4gmap00C59OSSVerify5KrLib4Spec6Malloc5guardC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc1MC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib6Malloc=MallocFacts_B8gmeta_ok00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc=MallocFacts_B5go_liC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc<get_meta_recC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc:m_last_idxC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive01K47Corelib7Numbers7BinNums1Z02C56Stdlib6ZArith6BinInt1Z2leI47Corelib4Init5Logic3and00C59OSSVerify5KrLib6Malloc=MallocFacts_B;go_freeableC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc:m_freeableC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic2eq00C59OSSVerify5KrLib6Malloc=MallocFacts_B5go_scC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc;m_sizeclassC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive02C56Stdlib6ZArith6BinInt1Z2ltC59OSSVerify5KrLib4Spec6Malloc8m_maplenC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic2or00C59OSSVerify5KrLib6Malloc=MallocFacts_B9go_maplenC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3powK47Corelib4Init9Datatypes4list01I47Corelib4Init9Datatypes4list00K46Stdlib9micromega6VarMap1t02I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr01K46Stdlib9micromega7EnvRing5PExpr02K47Corelib4Init9Datatypes6option02C46Stdlib9micromega5Tauto8BFormulaK47Corelib4Init5Logic2eq01C46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundK47Corelib4Init5Logic3and01K47Corelib7Numbers7BinNums1Z03K46Stdlib9micromega7EnvRing3Pol01K47Corelib4Init9Datatypes3nat02K46Stdlib9micromega=RingMicromega5Psatz02K46Stdlib9micromega=RingMicromega5Psatz04K46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega:ZMicromega;ZArithProof02K47Corelib4Init9Datatypes4list02K46Stdlib9micromega=RingMicromega7Formula01C56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z:pow_nonnegC56Stdlib6ZArith6BinInt1Z7compareK47Corelib7Numbers7BinNums1N02K46Stdlib9micromega7EnvRing5PExpr07C59OSSVerify5KrLib6Malloc<MallocKit_B35mw_okC1?~~~~~~~~~~~~~~~K46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega5Tauto8GFormula03K46Stdlib9micromega5Tauto8GFormula05K46Stdlib9micromega5Tauto8GFormula08K46Stdlib9micromega5Tauto8GFormula06K47Corelib7Numbers7BinNums1Z01I47Corelib7Numbers7BinNums1Z00K46Stdlib9micromega=RingMicromega3Op203C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K47Corelib4Init9Datatypes4unit01K46Stdlib9micromega=RingMicromega3Op205I59OSSVerify5KrLib4Spec6Malloc6mstate00C1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive03I46Stdlib9micromega:ZMicromega;ZArithProof00I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01K47Corelib4Init9Datatypes3nat01K46Stdlib9micromega:ZMicromega;ZArithProof01K46Stdlib9micromega=RingMicromega3Op201I47Corelib4Init5Logic4True00I47Corelib4Init9Datatypes:comparison00C59OSSVerify5KrLib4Spec6Malloc5queueC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc>activate_groupC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc7decoderC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc:free_groupC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc?nontrivial_freeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc7F_ntf_H8ntf_condC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc6m_nextC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3ltbC59OSSVerify5KrLib4Spec6Malloc6activeC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes6option01C59OSSVerify5KrLib4Spec6Malloc8optr_eqbC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec6Malloc5lhead01C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc7dequeueC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc7m_freedC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc7m_availC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3lorC56Stdlib6ZArith6BinInt1Z3eqbC47Corelib4Init9Datatypes4negbC59OSSVerify5KrLib6Malloc=MallocModel_B6aor_stC1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes4prod00I47Corelib4Init9Datatypes3nat00C59OSSVerify5KrLib4Spec6Malloc7mapinfoC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6Malloc4meta00C1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes6option00C59OSSVerify5KrLib4Spec6Malloc9free_metaC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc=MallocModel_B;fg_usage_stC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc5m_memC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc:get_strideC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3addC59OSSVerify5KrLib4Spec6Malloc9del_groupC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc9del_slotsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc8step_seqC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc:record_seqC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3mulK47Corelib4Init9Datatypes4prod01K59OSSVerify5KrLib4Spec6Malloc2ev06C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec5STree5stree02C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6Malloc2ev00C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec6Malloc<undef_reason03C1?~~~~~~~~~~~~~~~I45stdpp9bitvector;definitions2bv00c59OSSVerify5KrLib6Malloc5F_ntf9oracle_okC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc9s_regionsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc8s_shadowC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc6r_kindC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc5r_lenC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc;round_up_pgC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc6r_baseC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z6moduloC59OSSVerify5KrLib4Spec6Malloc:get_shadowC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc9cell_readC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec6Malloc7cellval02C1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic6eq_indC47Corelib4Init9Datatypes2idC35stdpp4base6lookupC35stdpp6option;from_optionI47Corelib7Numbers7BinNums1N00I59OSSVerify5KrLib4Spec6Malloc6region00C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6Malloc6shadow00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc7shadow0C1?~~~~~~~~~~~~~~~C45stdpp7numbers1N6eq_decC35stdpp9countable;N_countableI59OSSVerify5KrLib4Spec6Malloc5rkind00C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec6Malloc5rkind03C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6Malloc7cellval00C1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib6MallocAMallocFacts_Bpres9ntf_frame00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc;MallocKit_B7free_fpC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6MallocAMallocFacts_Bpres:nf_regionsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6MallocAMallocFacts_Bpres9nf_shadowC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6MallocAMallocFacts_Bpres9nf_groupsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc;MallocKit_B<free_fp_monoC1?~~~~~~~~~~~~~~~C35stdpp9decidable;prod_eq_decC35stdpp9countable>prod_countableC59OSSVerify5KrLib4Spec6Malloc8s_groupsC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6Malloc4ghdr00C1?~~~~~~~~~~~~~~~C45stdpp7numbers1Z6eq_decC35stdpp9countable;Z_countableC47Corelib4Init9Datatypes3fstC47Corelib4Init9Datatypes3sndK59OSSVerify5KrLib4Spec6Malloc7cellval01C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc4concC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc:MallocTree8pans_memC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc@F_malloc_enframe3rdvC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc:MallocTree3memC1?~~~~~~~~~~~~~~~".
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)

Section CANSEC1. Context {rc : runConstT}.
Lemma gmeta_mw st g p : gmeta_ok st g p -> mw_ok (get_meta_rec st g).
Proof.
ltac2:(KReplay.run1 (kr_t_F_ntf ()) ["CANSEC1"] "h04__x1h14__p1h27__arithh34__ffh48__varmaph55__with64__p2h76__sat4h82Hah96__sat3h:1gh;1ph<2sth=2GOh>1Hh?2H0h@2H1hA2H2p;3p;4p;2p;1p;7p;6p;8p-1R0p10000R1p4p710R2p8P0P1p4p7210R0p8g000DR3p4p70R4p10019p4p710p8P4p10020p4p710R5p8P4p1002NR6p4p710R7p8P4P6p4p7210R6p8P4p1002gR8p4p710p8P4p1003@p4p73110R9p8P4P2p8p1003Rp4p70R2p1004Gp4p710p8P2P8p4p741110p8P2P0p8P2P1p4p73110p8P5P7p8P5P6p8p1004ep4p710R1P5p8P1P7p8P1P6p8P1P9p8p10059p4p710p1005op4p710p8g006aj3lTg007ej4kTg008dj28Tg009aj1=Tg00:\j16Tg00;Aj1;Tg00;_j23Tg00<;j20Tg00<Vj4STg00=[j1BTg00>Vj39Tg00?0j4MTg00?oj1ETg00@kj14Tg00APj22Tg00Alj1?Tg00Bej2CTg00C?j4]Tg00DBj2KTg00D_j1ZTg00E?j1YTg00E_j2XTg00F=j1WTg00F[j1VTg00GFj2<Tg00Gij2UTg00HLj1PTg00Hnj2OTg00IPj2FTg00Ijj2NTg00JVj3QTg00K5j4RTg00Kgj4:Tg00LBj1TTg00L`j2jTg00MAj1iTg00M`j2LTg00NIj3gTg00O2j3fTg00O[j2eTg00PGj3aTg00Pgj4ATg00QRj2`Tg00R:j3_Tg00R^j2^Tg00S?j1ITg00S]j3HTg00T@j1bTg00U>j7cTg00Ubj6dTg00VFj7\Tg00Vjj8[Tg00WNj7hTg00X2R9f0R1'3p=1g00XPR6f1R7g00XnP1CAp=@P7g00YUR5g00Z4R2P2g00ZTR0P1g00[4Fcp=5P7P5P2P2P0P1Edp=Gf2R8P5P2P2P0P7P1F\p=>f3R4P5P2P2P0P8P7P1G[p=7P8P5P2P2P0P7P1Fhp=JP6P7g00[TP1CAp=Dg00\;R5Al871P4P8P7P1Ck1848#=R:#1g00]4R;#6R<#6#6#6R=#;R>,3:'0f4R:P4P8P7CS18:4#B%;;R?596f5R@P:P4P8CM18@:RA#ERB#1%4<R<#4#4#4#;RC,2B'0%6=#;R=996B%=A=969%?A,29'0'0'Cf6RAP@P:P4C]18A@#?RB#1%4;RD#;RE%4D#4#6#6RD#;RF'KRG,2B'0f7RB/8ARA#=RH#1RI13H>RH'0%BARJ#1RK13J?RJ'0RL%EARM#1RN13M=RM'0RO%?ARP#1RQ%6<#4#4R<#;,KERR,2PRP'0RS'0RT'0PIPHp-0RHg00]YRI#ZRU%YIRV1X67RW%W6RX%V6RY1<691U6;RZ'@,5YR[1GY4R\5>YR]%P2R2P[C71OY0R0P1P8g00^ER^g00^eR_'F1N18=9^_dAQ697CRR_b3b4b5X06W1R^%11/07R`%17Ra[^06^1HRbP1f8/8BRB#=Rc/3>PcP:O3b2PUPVPWPXPY1<6>,@Z,5YRd9>Y\P2PdC7P0P_b3b4b5X06X1H131>,07137>[^06^1HP1%1cPcP:O3b2C:PLPTPKPJ%T;,j6g00_ER;#i,L65g61L6;5f6g00_d'e=aIURIPVPWPXPYP6PZg00`PR;1<6?RJCA,5YRKP2P[C7P0P_b3b4b5X06A961?RTPa[^06P1%BBP4O2R4b2PUPVPWPXPYPKP21@ZJ,5YC7P0P_b3b4b5X06137?\T^06P4b2C:POPSPNPM1`EFRM129ERN%1F129G[RS[RO%1ER4g00a7RTA_EF7UW8RF%1G\T^84R4P7g00aS1^9E'FPNeO1RNPSPIPVPWPXPYP6PZP;1<6=R;CA,5Y1GY:5>YR:9JY]P2P[C7P0P_b3b4b5X06X1HX6HA961=/08R[,C`Pa[^06^1H^6HP1f;f:'8Ra#==969%?a,29'0R9%EaRa/2CPaP@O4b2b7b9b7PMPOPFP4PNPSPUPVPWPXPY1<6C,DZ,5Y9>Y\=JY:P21@Z;,5YC7P0P_b3b4b5X06X1HX6H121C,07/C[137=[^06^1H^6HP1P9%1aPaP@O4b2b7b9b7C:PQPPP^PbP1%?BRB/2GPBP7O3b2PUPVPWPXPY1<6ERE%ID5H6,DZ,5Y9>Y\P2%I<9H6E,DZ,5YC7P0P_b3b4b5X06X1H121G,07127R[^06^1HP1%1BPBP7O3b2C:C:C:C:%bAebAb@b?b>W=X;3X:3X<5P8P7P1O3X;3X:3W<o"). Qed.

Lemma ntf_unfold {R} (dec : decoder R) f st g i (k : mstate -> mapinfo -> Malloc.M R) bail :
  nontrivial_free dec (S f) st g i k bail =
  let mr := get_meta_rec st g in
  let sc := m_sizeclass mr in
  if ntf_cond st g i then
    match m_next mr with
    | Some _ =>
      guard 50 (sc <? 48) (
        let activate_new := optr_eqb (active st sc) (Some g) in
        let st1 := dequeue (LActive sc) g st in
        match activate_new, active st1 sc with
        | true, Some a => activate_group a st1 (fun st2 _ => free_group R dec (nontrivial_free dec f) st2 g k bail) bail
        | _, _ => free_group R dec (nontrivial_free dec f) st1 g k bail
        end) bail
    | None => free_group R dec (nontrivial_free dec f) st g k bail
    end
  else if Z.lor (m_freed mr) (m_avail mr) =? 0 then
    guard 51 (sc <? 48) (
      if negb (optr_eqb (active st sc) (Some g)) then queue (LActive sc) g st (fun st0 => k (aor_st st0 g i) None) bail
      else k (aor_st st g i) None) bail
  else k (aor_st st g i) None.
Proof.
ltac2:(KReplay.run1 (kr_t_F_ntf ()) ["CANSEC1"] "p'0h01Rh14bailh23dech31fh41gh51ih61kh72sth8<activate_newi00<activate_newh92mrh:2sch;3st0h<3st1h=3st2i011ai021xp;1p;2p;3p;7p;5p;6p200R0g005oR1p4p710p8P0g0059R2p4p710p8P0g00b9R3p4p710p8P0g00boR4p4p710p8P0g00cnR5p4p710p8P0g00dfR6p4p710p8P0g00eaR7p4p710p8P5j1LTP1j11Tg008dj2ATg00?oj1=Tg00faj3KTg00g]j1ITg00:\j16Tg00@kj10Tg00;Aj12Tg00hTj2;Tg00i1j25Tg00ihj27Tg00jJj29Tg00kCj1<Tg00l;j3JTP7j33TP6j74TP4j5HTP2j5:Tg00m3j1ETg00mkj1DTg00ncj2BTg00o@j2@Tg00o]j1CTg010;j38Tg011;j2?Tg00HLj1FTP3j6GTg00IPj2>Tf0R3#LR2g011[R4g00\;R6g000DR7g00XPR1g012:f7R5#1R8[\6R9f6R:#1R;f4R<f3R='Ag0132%=3P1g00^ER>f:R?#1R@f5RA=K:<g013iRBP7P@f1RC#IP?g00]4#6#0#0RD#6RE#0#2%0D#0#2RD,;C155C177:'9P>f2RF#<f8RG7J5P6P>f=RH#1RIPCPBP7PI153=PHP3PCf?RIf>RBA3IBHPCf;RBf9RIPGF4V1X=6P:DHf<RHPBA3HB?P3PGP:PAF4RHn10110200021010100PHn0110000020000b<b8P=D:PIPGA3IG5P:PAP=PFF4n10110200021010100P>P@%EC%DC'Bg00X2'@PI%6E#21;3DP>P@15:3177A'9#CPI%<3PAP:P<A83:A1?71#FRIO2X;6PFEGP=A8:A<PIO2RIn0100000020000PFD:PIn0100000020000n0100000020000b:b9,>8X1;X69X51X47X76X34X22X00P5P:PAP<P=PFPCP3O8W1W6W5W4W7W3W2X00o"). Qed.

Lemma free_group_unfold {R} (dec : decoder R) rec st g (k : mstate -> mapinfo -> Malloc.M R) bail :
  free_group R dec rec st g k bail =
  let mr := get_meta_rec st g in
  let st1 := fg_usage_st st g in
  match m_mem mr with
  | None => SVis (EUndef UBadPtr) (fun _ => bail)
  | Some p =>
    let st1 := del_slots p (get_stride mr) (m_last_idx mr + 1) (del_group p st1) in
    if negb (m_maplen mr =? 0) then
      free_meta g (record_seq (m_sizeclass mr) (step_seq st1)) (fun st3 => k st3 (Some (p, m_maplen mr * 4096))) bail
    else
      dec st1 p (fun m idx => rec st1 m idx (fun st3 mi => free_meta g st3 (fun st4 => k st4 mi) bail) bail) bail
  end.
Proof.
ltac2:(KReplay.run1 (kr_t_F_ntf ()) ["CANSEC1"] "p'0h01Rh14bailh23dech31gh41kh53rech62sth73st1h83st3h93idxh:1mh;2mih<2mrh=3st4i001pi011xp;1p;2p;4p;5p200R0g005oR1p4p710p8P0g014KR2p4p710p8P0g00cnR3p4p710p8P0p100dfp4p710p8P3j1JTP1j11Tg008dj2<Tg015Ej26Tg016Jj1ITg017@j1CTg009aj1=Tg00;Aj13Tg018;j2:Tg018Xj28Tg019Rj47Tg00Alj12Tg00o@j29Tg00o]j1HTg00?oj1GTg01:Lj1FTg01;Ej2BTg011;j2>Tg01<@j2?Tg01<]j4@Tg00ihj2ATP2j54Tg01==j1;Tg01>2j5DTg00IPj2ETg00@kj15Tf0R2#5#5p=0%J2R1g00\;R3g000DR4g00XPR5g012:R6f6R7#1R8[\3R9f5R:#1R;P8[[[[[R<f3R=f2R>'<g0132f4R?/6=P3g013iP4f9R@#1f1RA#IP2%C>%=>g00]4RB#3':182AC7P3g00^Ef;#1%2=g00X2'9#Hf:RCP7%G=%F2'BP7P21>45P4P5P>%2?%0B#0#0#0#0#0#3'?C@'AO2X83P?D4P@P2PAPCP>PAP2f>PCPAPCP2PAO2X=3f8RCD4X;6X83P7O5X95X:4P?O4n0100000020000b7g01>iP5PCg01?^#;P=V5DDn10110100021010000b7b<,E8X1;X49X34X63X5<X21X00P7P:P?P=P>PAP2O7X1;X49X34X63W5W2X00o"). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition ntf_result (st' : mstate) (mi : mapinfo) (a0v a1v : word) : Prop :=
  match mi with
  | None => a1v = wz 0
  | Some (b, len) =>
      a0v = wz (conc st' b) /\ a1v = wz len /\ 0 < len < 2^64 /\ snd b = 0
      /\ (exists r, (s_regions st') !! (fst b) = Some r /\ r_kind r = RKGroup /\ len = round_up_pg (r_len r))
      /\ (forall b' gh, (s_groups st') !! b' = Some gh -> fst b' <> fst b)
  end.

(* [comment removed for export] *)
Definition oracle_ok (o m : word -> option byte) (st : mstate) : Prop :=
  forall rid r q h, (s_regions st) !! rid = Some r -> r_kind r = RKGroup -> 0 <= q < round_up_pg (r_len r) ->
    8 <= (r_base r + q) mod 16 ->
    cell_read (get_shadow st rid) q = Unknown h ->
    o (wa (r_base r + q)) = m (wa (r_base r + q)).

Lemma oracle_ok_frame o m st st' : oracle_ok o m st -> s_regions st' = s_regions st -> s_shadow st' = s_shadow st -> oracle_ok o m st'.
Proof.
ltac2:(KReplay.run1 (kr_t_F_ntf ()) ["CANSEC1"] "h02Hch12Hrh21gh31mh41oh52sth63st'h72ERh82ESh92Hkh:2Hqh;2M8h<2OKh=1hh>1qh?1rh@3ridp;1p;3p;4p;2p;6p;5g00@kj11Tg00S?j1@Tg01@]j1:Tg013ij19Tg01A@j3ATg004ej4<Tg01B;j12Tg00>Vj30Tg01C5j13Tg002gj4>Tg00ihj26Tg01Cnj1CTg00;_j2BTg01Dej1MTg01E[j1LTg00APj2KTg00<;j2JTg00;Aj1?Tg01FWj1ITg018;j2HTg01GNj2GTg01Gnj2FTg01Hij25Tg01Icj18Tg01J]j6;Tg01K9j1ETg01KUj67Tg01Kij5DTg01LDR0g01LbR1f3R2f2R3f1R4f0R5E7p=4g01M[R6P6P4g01NTP5DDp==g00]4#1#1#1R7#1R8#1#1#@#:%@7#:#9[R9g00\;R:AA234P0g01OLR;g01OeR<P1C<R=%24%2330P0P;P<P6C<R>%33%3230g00XPR?%91R@P=P0P;P<P1C>RAP2f7RB#2C4161330g01PC%C2g01Q;30g00X2/B2f4RC#M#L,K2'J%?7f5R7#I/HC%?8'G'Bg01R3R8f;/FB/57%8C30P=f<#2P=PAf9RDP5C4f8RE,6150@X2=PCf=RF#2RGf:RHE;P=PAPEPGC4161B50@P>%3F%E6R@P0P6P>P0P;P<P6C>R<PHP5E7'=/5E%8B508X2>P4f>#3R;PHE;P0P6P>P<PDP;E7,=@/5Bf6R@#8508PFPHPDPEPBP4P7PCP2P5O9b0b1W0W;W:W9W1X=?W>X?1X@0AA@72eW8W7W<X6:X5:X39X49P2P3P4P5O4X6:W5X39W4o"). Qed.

Lemma free_fp_frame st st' lo (sp sp' : Z) a : ntf_frame st st' -> sp' <= sp -> free_fp st' lo sp' a -> free_fp st lo sp a.
Proof.
ltac2:(KReplay.run1 (kr_t_F_ntf ()) ["CANSEC1"] "h01ah12loh22sph33sp'h42sth53st'h62FRh71Hh82HSp;2p;4p;3p;;g01Rmj26Tg00;_j25Tg01T6j40Tg01U5j31Tg01V=j34Tg01WDj32Tg01XKl;3Tg00\;R0g00XPR1f5R2f4R3'6f2R4f3R5'5f6R6P2P5P4C0f8R7f7R8P6P2P3P5A1784A4784A2784f1R8f0R7M;3W7W8W6X01X31X21X11X50X40P2P3P5P4P8P7O6X01X31X21W1X50W4o"). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma free_fp_same st st' lo (sp : Z) a :
  s_regions st' = s_regions st -> s_shadow st' = s_shadow st -> s_groups st' = s_groups st ->
  free_fp st' lo sp a -> free_fp st lo sp a.
Proof.
ltac2:(KReplay.run1 (kr_t_F_ntf ()) ["CANSEC1"] "h04__x1h11ah21bh32ghh42loh52sph62sth73st'h82EGh92ERh:2ESh;1Hh<2H0h=7__arithh>4__ffh?8__varmaph@5__withA1gp;4p;1p;3p;6p;2p;7p;;g004ej43Tg01B;j16Tg00>Vj30Tg01C5j15Tg01YOj4LTg01Ymj6@Tg01ZNj11Tg01T6j4;Tg013ij19Tg002gj48Tg00ihj24Tg004Gj67Tg00D_j1KTg00E?j1JTg00E_j2ITg00F=j1?Tg00F[j1=Tg00Gij2>Tg00Pgj4<Tg00U>j7ATg00Hnj2BTg00IPj2:Tg00Ijj2CTg00JVj3DTg00K5j4ETg00;_j2FTg01XKl;GTg01KUj6HTg000DR0g01[GR1f3R2f2R3f1R4f0R5EHp=2g00\;R6g00XPR7g01LDR8g01OLR9g01OeR:g01LbC3%62f4R;#630P8P9P:g01M[C3%5;f5R<#530P0P8P9P7g01\>R=CLR>P8P9P:P7P=g01\WE@R=P1C3R:%1<f6R9#130P9P<P;P2C;f8R8f7R?P9P<P<P;P2P3P:%18%91R8P:P0P>P=P1C8R=P4P3C21415R>30P:P=P3f<#1C21414508[^31^20XA:P:P=P4f:#1C2=08>P5W<X31X20%1?P4E7g00]YR?#K%J?1I74%?7%=7R?g00YUg00Z4R0P0g00ZTR0P7g00]4,>7R1g00XnP1C<g00[4FA1B?0P5P3g00^ER0g00^eR?':1C53=00?dg00X2=D74CEb>b?b@X071F55^07P5P9O1b=P5M;GW;W8W:W9X17X57X47X76X66P;P2P3P4P5O5X17X57W4X76W6o"). Qed.

Lemma rdv_known o st q v : cell_read (get_shadow st (fst q)) (snd q) = Known v -> rdv pans_mem o st q = v.
Proof.
ltac2:(KReplay.run1 (kr_t_F_ntf ()) ["CANSEC1"] "p'0h01oh11qh22sth31vi001vh41Hh51ci011hi021xp;2p;3p;1p;4p;6p;5g011;j2;Tg01]5j35Tg01Gnj22Tg01]Rj31Tg01Hij24Tg01]oj13Tg00>Vj30Tg01^ij2:Tg01_^R0j49Tg00IPj27Tg004Gj66Tg01`]j58Tg01a]R1g00\;R2g01LDR3g00XPR4';R5g01R3R6f2R7f1R89534'2A1348'4f0R9#330P6%38P6P4P9P9f6f4R:f5/::P9C9n0110200021010010101=047X561748f3R6A5347'2A1347'4P9E6P1P0P:P6P7D8=048eW4X34X15X22X01P6P7P8P9O4X34W1W2W0o"). Qed.

Section NTF.
Variables (ra0 : word) (gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32).
Variables (o : word -> option byte) (LB : list block) (lo : Z).
Hypothesis LO : ATOP <= lo.
Hypothesis GP : gp = Z_to_bv 64 0x1a800.
End NTF.


End CANSEC1.
