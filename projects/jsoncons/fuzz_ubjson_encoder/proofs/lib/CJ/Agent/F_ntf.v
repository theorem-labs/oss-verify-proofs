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
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.CJ.Lib Require Import Tac Image ZBridge SysStep SFModel Arr ITree Nodes Decode.
(* [comment removed for export] *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.CJ.Agent Require Import F_syscalls MallocRep F_malloc_free F_malloc_fast F_malloc_enframe MallocTree MallocBlocks MallocFacts_B.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.CJ.Spec Require Import STree Malloc MallocCtrl Monad Prog.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.CJ.Agent Require Import MallocKit_B MallocKit_B2 MallocModel_B F_ntf_A F_ntf_B F_ntf_C.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.CJ.Agent Require Import MallocKit_B3 F_ntf_D F_ntf_E F_ntf_F F_ntf_G F_ntf_H.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.CJ.Agent Require Import MallocFacts_Bpres.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.CJ.Lib Require Import RunP.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require KReplay.
Ltac2 kr_t_F_ntf () := "C35stdpp4base6LookupC99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc4aptrC13~~~I99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec5STree5stree00C13~~~I35stdpp9countable9Countable00C35stdpp4base;RelDecisionC35stdpp4gmap;gmap_lookupC35stdpp4base4fmapC99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc4optrC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc5guardC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc1MC13~~~I99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ5Agent=MallocFacts_B8gmeta_ok00C13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ5Agent=MallocFacts_B5go_liC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc<get_meta_recC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc:m_last_idxC13~~~K47Corelib7Numbers7BinNums8positive01K47Corelib7Numbers7BinNums1Z02C56Stdlib6ZArith6BinInt1Z2leI47Corelib4Init5Logic3and00C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ5Agent=MallocFacts_B;go_freeableC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc:m_freeableC13~~~I47Corelib4Init5Logic2eq00C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ5Agent=MallocFacts_B5go_scC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc;m_sizeclassC13~~~K47Corelib7Numbers7BinNums8positive02C56Stdlib6ZArith6BinInt1Z2ltC99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc8m_maplenC13~~~I47Corelib4Init5Logic2or00C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ5Agent=MallocFacts_B9go_maplenC13~~~C56Stdlib6ZArith6BinInt1Z3powC56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z:pow_nonnegC56Stdlib6ZArith6BinInt1Z7compareK47Corelib4Init5Logic2eq01K47Corelib4Init9Datatypes4list01I47Corelib4Init9Datatypes4list00K46Stdlib9micromega6VarMap1t02I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr01K46Stdlib9micromega7EnvRing5PExpr02K47Corelib4Init9Datatypes6option02C46Stdlib9micromega5Tauto8BFormulaC46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundK47Corelib4Init5Logic3and01K47Corelib7Numbers7BinNums1Z03K46Stdlib9micromega7EnvRing3Pol01K47Corelib4Init9Datatypes3nat02K46Stdlib9micromega=RingMicromega5Psatz02K46Stdlib9micromega=RingMicromega5Psatz04K46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega:ZMicromega;ZArithProof02K47Corelib4Init9Datatypes4list02K46Stdlib9micromega=RingMicromega7Formula01K47Corelib7Numbers7BinNums1N02K46Stdlib9micromega7EnvRing5PExpr07C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ5Agent<MallocKit_B35mw_okC13~~~K46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega5Tauto8GFormula03K46Stdlib9micromega5Tauto8GFormula05K46Stdlib9micromega5Tauto8GFormula08K46Stdlib9micromega5Tauto8GFormula06K47Corelib7Numbers7BinNums1Z01I47Corelib7Numbers7BinNums1Z00K46Stdlib9micromega=RingMicromega3Op203C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K47Corelib4Init9Datatypes4unit01K46Stdlib9micromega=RingMicromega3Op205I99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc6mstate00C13~~~K47Corelib7Numbers7BinNums8positive03I47Corelib4Init5Logic4True00I47Corelib4Init9Datatypes:comparison00I46Stdlib9micromega:ZMicromega;ZArithProof00I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01K47Corelib4Init9Datatypes3nat01K46Stdlib9micromega:ZMicromega;ZArithProof01K46Stdlib9micromega=RingMicromega3Op201C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc5queueC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc>activate_groupC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc7decoderC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc:free_groupC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc?nontrivial_freeC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ5Agent7F_ntf_H8ntf_condC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc6m_nextC13~~~C56Stdlib6ZArith6BinInt1Z3ltbC99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc6activeC13~~~K47Corelib4Init9Datatypes6option01C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc8optr_eqbC13~~~K99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc5lhead01C13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc7dequeueC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc7m_freedC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc7m_availC13~~~C56Stdlib6ZArith6BinInt1Z3lorC56Stdlib6ZArith6BinInt1Z3eqbC47Corelib4Init9Datatypes4negbC99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ5Agent=MallocModel_B6aor_stC13~~~I47Corelib4Init9Datatypes4prod00I47Corelib4Init9Datatypes3nat00C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc7mapinfoC13~~~I99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc4meta00C13~~~I47Corelib4Init9Datatypes6option00C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc9free_metaC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ5Agent=MallocModel_B;fg_usage_stC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc5m_memC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc:get_strideC13~~~C56Stdlib6ZArith6BinInt1Z3addC99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc9del_groupC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc9del_slotsC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc8step_seqC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc:record_seqC13~~~C56Stdlib6ZArith6BinInt1Z3mulK47Corelib4Init9Datatypes4prod01K99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc2ev06C13~~~K99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec5STree5stree02C13~~~I99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc2ev00C13~~~K99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc<undef_reason03C13~~~I45stdpp9bitvector;definitions2bv00c99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ5Agent5F_ntf9oracle_okC13~~~I35stdpp4gmap4gmap00C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc9s_regionsC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc8s_shadowC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc6r_kindC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc5r_lenC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc;round_up_pgC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc6r_baseC13~~~C56Stdlib6ZArith6BinInt1Z6moduloC99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc:get_shadowC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc9cell_readC13~~~K99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc7cellval02C13~~~C47Corelib4Init5Logic6eq_indC47Corelib4Init9Datatypes2idC35stdpp4base6lookupC35stdpp6option;from_optionI47Corelib7Numbers7BinNums1N00I99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc6region00C13~~~I99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc6shadow00C13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc7shadow0C13~~~C45stdpp7numbers1N6eq_decC35stdpp9countable;N_countableI99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc5rkind00C13~~~K99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc5rkind03C13~~~I99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc7cellval00C13~~~C47Corelib4Init9Datatypes3fstC47Corelib4Init9Datatypes3sndK99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc7cellval01C13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc4concC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ5Agent:MallocTree8pans_memC13~~~C47Corelib4Init5Logic8eq_ind_rC99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ5Agent@F_malloc_enframe3rdvC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ5Agent:MallocTree3memC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ5Agent<MallocKit_B2;implT_guardC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ5Agent:MallocTree5implTC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc6m_prevC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ5Agent;MallocKit_B8queue_stC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc8get_headC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc:m_set_prevC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc:m_set_nextC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc8upd_metaC13~~~C99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc8set_headC13~~~C47Corelib4Init5Logic9False_indI99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec6Malloc5lhead00C13~~~I99OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib2CJ4Spec4Prog6PState00C13~~~I4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=machine_state00I47Corelib4Init5Logic5False00K47Corelib4Init5Logic4True01".
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Section CEIL_WRAP_1.
Context {RUNp : RunP}.


(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma gmeta_mw st g p : gmeta_ok st g p -> mw_ok (get_meta_rec st g).
Proof.
ltac2:(KReplay.run1 (kr_t_F_ntf ()) ["CEIL_WRAP_1"] "h06__sat4h14__x1h24__p1h37__arithh46__sat3h54__ffh68__varmaph75__with82Hah94__p2h:6__sat6h;1gh<1ph=2sth>2GOh?1Hh@2H0hA2H1hB2H2hC6__sat5p;3p;4p;2p;1p;7p;6p;8p-1R0p10000R1p4p710p8P0P1p4p7210R0p8g000DR2p4p70R3p1001Rp4p710p8P3p1002bp4p710p8P3p1003@R4p4p710p8P3P4p4p7210p8P3p1003YR4p4p710p8P3p10042p4p73110p8p1004Dp4p70R3P4p4p741110p8P3P0p8P3P1p4p73110p8p1005Rp4p710p1006ap4p710p8g007lj3lTg009Hj4kTg00:_j29Tg00<5j1?Tg00=Ij16Tg00=nj1:Tg00>Lj23Tg00>hj21Tg00?Cj4VTg00@`j1BTg00B4j37Tg00BNj4OTg00Cej1ETg00E:j14Tg00E_j22Tg00F;j1>Tg00GMj2DTg00Ggj4^Tg00IBj2NTg00I_j2ITg00JGj3HTg00Jkj2[Tg00KLj2GTg00Kfj1ZTg00LFj1YTg00Lfj2XTg00MDj1WTg00Mbj1UTg00NMj2<Tg00O0j2TTg00OSj1PTg00P5j2QTg00PWj2RTg00QCj3STg00Qbj4jTg00RTj48Tg00Roj1iTg00SMj2gTg00Snj1fTg00TMj2LTg00U6j3bTg00U_j3aTg00VHj2`Tg00W4j3_Tg00WTj4ATg00X?j1JTg00X]j3MTg00Y@j1cTg00ZVj7dTg00[:j6eTg00[^j7]Tg00\Bj8\Tg00\fj7hTg00]JR1f0R3'3p=0g00]hR0f1R4g00^FP3CAp=@P4g00^mR5g00_LR6P6g00_lR7P3g00`LFdp=5P4P5P6P6P7P3Eep=Ff2R8P5P6P6P7P4P3F]p==f3R9P5P6P6P7P8P4P3G\p=;P8P5P6P6P7P4P3Fhp=KP0P4g00`lP3CAp=Cg00aSR5Al843P9P8P4P3Ck1998#?R:#0g00beR;#6R<#6#6#6R=#:R>,3:'1f4R:P9P8P4CV19:9#B%:;R?570f5R@P:P9P8CO19@:RA#ERB#0%4<R<#4#4#4#:RC,2B'1%6=#:R=970B%?A=701%>A,21'1'1'Df6RAP@P:P9C^19A@#>RB#0%4;RD#:RE%4D#4#6#6RD#:RF'NRG,2B'1f7RB/9ARH#?RI#0RJ13I>RI'1%BHRK#0RL13K?RK'1RM%EHRN#0RO13N=RN'1RP%>HRQ#0RR%6<#4#4R<#:RS,NERT,2QRQ'1RU'1RV'1PJPI1IEFRI121ERJ%0F121G[RW[RX%0ERYg00cJRZAHEF4UW8RF%0G\Z^8YR[P4g00cf1[1E'GPJeR\O1R]PWp-0R^g00dLR_#ZR`%Y_Ra1X04Rb%W0Rc%U0Rd1<011T0;Re'@,5dRf1Fd9R95=dRg%P6R6PfC;1Qd7R7P3P8g00e8Rhg00eXRi'G1R38=7hidAS014CjRib5b6b7X10W2Rh%03/14Rj%04Rk[^10^2^RlP3f;f:'9Rm#?Rn/3>PnPBO3b3b0b4b0PIPXPFP[P]PWP`PaPbPcPd1<0>,@e,5dRo9=d9P6PoC;P7Pib5b6b7X10X2^133>,14134>[^10^2^P3%0nPnPBO3b3b0b4b0C8PMPVPLPKPIPXPFP[P]PW%i;,g0g00f8R;#f,L05b01L0;5a0g00fW'`=__`R_PaPbPcPdP0Peg00gCR;1<0?RKCA,5dRLP6PfC;P7Pib5b6b7X10A703?RVPk[^10P3%BmPAO2RAb3b0b4b0PIPXPFP[P]PWP`PaPbPcPdPLP61@eK,5dC;P7Pib5b6b7X10134?\V^10PAb3b0b4b0C8PPPUPOPNPIPXPFP[P]PWP_PaPbPcPdP0PeP;1<0=R;CA,5d1Fd:5=dR_9KdgP6PfC;P7Pib5b6b7X10X2^X9^A703=/18Rf,DjPk[^10^2^^9^P3A70n1%>mRn,21'1Rk%EmRm/2CPmP@O4b3b0b4b0PIPXPFP[P]PWP`PaPbPcPd1<0C,Ce,5d9=d9=Kd_P61@e;,5dC;P7Pib5b6b7X10X2^X9^123C,14/Df134=[^10^2^^9^P3Pk%0mPmP@O4b3b0b4b0C8PRPQPIPXPFP[P]PWPhPlP312nGPnP:O3b3b0b4b01IES%0S121T[R1\JAHES4VZX8Y%0T\Z^8YPIPXPFP[P]PWP:P\O1P1P`PaPbPcPd1<0ERE%JD5M0,Ce,5d9=d9P6%J<9M0E,Ce,5dC;P7Pib5b6b7X10X2^123G,14124T[^10^2^P3f>f='9#>R^#0P^PBO3b3b:b0b4b0bCb:C8C8C8C8%cHebBbAb@b?W>X<2X;2X=5P8P4P3O3X<2X;2W=o"). Qed.

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
ltac2:(KReplay.run1 (kr_t_F_ntf ()) ["CEIL_WRAP_1"] "p'0h01Rh14bailh23dech31fh41gh51ih61kh72sth8<activate_newi00<activate_newh92mrh:2sch;3st0h<3st1h=3st2i011ai021xp;1p;2p;3p;7p;5p;6p200R0g006aR1p4p710p8P0g005RR2p4p710p8P0g00gjR3p4p710p8P0g00i9R4p4p710p8P0g00jQR5p4p710p8P0g00kbR6p4p710p8P0g00m6R7p4p710p8P5j1LTP1j11Tg00:_j2ATg00Cej1=Tg00nOj3KTg00ocj1ITg00=Ij16Tg00E:j10Tg00=nj12Tg0113j2;Tg011Pj25Tg012`j27Tg013Bj29Tg014Tj1<Tg015ej3JTP7j33TP6j74TP4j5HTP2j5:Tg0176j1ETg018Gj1DTg019Xj2BTg01:5j2@Tg01:Rj1CTg01;0j38Tg01<Hj2?Tg00OSj1FTP3j6GTg00KLj2>Tf0R3#LR2g01<hR4g00aSR6g000DR7g00]hR1g01=Gf7R5#1R8[\6R9f6R:#1R;f4R<f3R='Ag01>X%=3P1g00e8R>f:R?#1R@f5RA=K:<g01?hRBP7P@f1RC#IP?g00be#6#0#0RD#6RE#0#2%0D#0#2RD,;C155C177:'9P>f2RF#<f8RG7J5P6P>f=RH#1RIPCPBP7PI153=PHP3PCf?RIf>RBA3IBHPCf;RBf9RIPGF4V1X=6P:DHf<RHPBA3HB?P3PGP:PAF4RHn10110200021010100PHn0110000020000b<b8P=D:PIPGA3IG5P:PAP=PFF4n10110200021010100P>P@%EC%DC'Bg00]J'@PI%6E#21;3DP>P@15:3177A'9#CPI%<3PAP:P<A83:A1?71#FRIO2X;6PFEGP=A8:A<PIO2RIn0100000020000PFD:PIn0100000020000n0100000020000b:b9,>8X1;X69X51X47X76X34X22X00P5P:PAP<P=PFPCP3O8W1W6W5W4W7W3W2X00o"). Qed.

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
ltac2:(KReplay.run1 (kr_t_F_ntf ()) ["CEIL_WRAP_1"] "p'0h01Rh14bailh23dech31gh41kh53rech62sth73st1h83st3h93idxh:1mh;2mih<2mrh=3st4i001pi011xp;1p;2p;4p;5p200R0g006aR1p4p710p8P0g01@JR2p4p710p8P0g00jQR3p4p710p8P0p100kbp4p710p8P3j1JTP1j11Tg00:_j2<Tg01A]j26Tg01C:j1ITg01DIj1CTg00<5j1=Tg00=nj13Tg01E]j2:Tg01F:j28Tg01GMj47Tg00F;j12Tg01:5j29Tg01:Rj1HTg00Cej1GTg01H`j1FTg01J2j2BTg01<Hj2>Tg01KFj2?Tg01Kcj4@Tg012`j2ATP2j54Tg01LCj1;Tg01MQj5DTg00KLj2ETg00E:j15Tf0R2#5#5p=0%J2R1g00aSR3g000DR4g00]hR5g01=GR6f6R7#1R8[\3R9f5R:#1R;P8[[[[[R<f3R=f2R>'<g01>Xf4R?/6=P3g01?hP4f9R@#1f1RA#IP2%C>%=>g00beRB#3':182AC7P3g00e8f;#1%2=g00]J'9#Hf:RCP7%G=%F2'BP7P21>45P4P5P>%2?%0B#0#0#0#0#0#3'?C@'AO2X83P?D4P@P2PAPCP>PAP2f>PCPAPCP2PAO2X=3f8RCD4X;6X83P7O5X95X:4P?O4n0100000020000b7g01NaP5PCg01Oo#;P=V5DDn10110100021010000b7b<,E8X1;X49X34X63X5<X21X00P7P:P?P=P>PAP2O7X1;X49X34X63W5W2X00o"). Qed.

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
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma oracle_ok_frame o m st st' : oracle_ok o m st -> s_regions st' = s_regions st -> s_shadow st' = s_shadow st -> oracle_ok o m st'.
Proof.
ltac2:(KReplay.run1 (kr_t_F_ntf ()) ["CEIL_WRAP_1"] "h02Hch12Hrh21gh31mh41oh52sth63st'h72ERh82ESh92Hkh:2Hqh;2M8h<2OKh=1hh>1qh?1rh@3ridp;1p;3p;4p;2p;6p;5g00E:j11Tg00X?j1@Tg01QGj1:Tg01?hj19Tg01Qjj3ATg01S=j4<Tg01SQj12Tg00B4j30Tg01Tdj13Tg003Yj4>Tg012`j26Tg01V6j1CTg00>Lj2BTg01WFj1MTg01XUj1LTg00E_j2KTg00>hj2JTg00=nj1?Tg01Yjj1ITg01E]j2HTg01[:j2GTg01[Zj2FTg01\nj25Tg01^Aj18Tg01_Tj6;Tg01`0j1ETg01`Lj67Tg01``j5DTg01a;R0g01aYR1f3R2f2R3f1R4f0R5E7p=4g01bkR6P6P4g01d=P5DDp==g00be#1#1#1R7#1R8#1#1#@#:%@7#:#9[R9g00aSR:AA234P0g01eNR;g01egR<P1C<R=%24%2330P0P;P<P6C<R>%33%3230g00]hR?%91R@P=P0P;P<P1C>RAP2f7RB#2C4161330g01fE%C2g01gV30g00]J/B2f4RC#M#L,K2'J%?7f5R7#I/HC%?8'G'Bg01hgR8f;/FB/57%8C30P=f<#2P=PAf9RDP5C4f8RE,6150@X2=PCf=RF#2RGf:RHE;P=PAPEPGC4161B50@P>%3F%E6R@P0P6P>P0P;P<P6C>R<PHP5E7'=/5E%8B508X2>P4f>#3R;PHE;P0P6P>P<PDP;E7,=@/5Bf6R@#8508PFPHPDPEPBP4P7PCP2P5O9b0b1W0W;W:W9W1X=?W>X?1X@0AA@72eW8W7W<X6:X5:X39X49P2P3P4P5O4X6:W5X39W4o"). Qed.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma rdv_known o st q v : cell_read (get_shadow st (fst q)) (snd q) = Known v -> rdv pans_mem o st q = v.
Proof.
ltac2:(KReplay.run1 (kr_t_F_ntf ()) ["CEIL_WRAP_1"] "p'0h01oh11qh22sth31vi001vh41Hh51ci011hi021xp;2p;3p;1p;4p;6p;5g01<Hj2;Tg01j:j35Tg01[Zj22Tg01jWj31Tg01\nj24Tg01k4j13Tg00B4j30Tg01lGj2:Tg01mUR0j49Tg00KLj27Tg01nlj66Tg01oJj58Tg020bR1g00aSR2g01a;R3g00]hR4';R5g01hgR6f2R7f1R89534'2A1348'4f0R9#330P6%38P6P4P9P9f6f4R:f5/::P9C9n0110200021010010101=047X561748f3R6A5347'2A1347'4P9E6P1P0P:P6P7D8=048eW4X34X15X22X01P6P7P8P9O4X34W1W2W0o"). Qed.

(* [comment removed for export] *)
Lemma implT_queue {R} o h g st0 (k : mstate -> Malloc.M R) bail s Q ms :
  (m_next (get_meta_rec st0 g) = None -> m_prev (get_meta_rec st0 g) = None -> implT o (k (queue_st h g st0)) s Q ms) ->
  implT o (queue h g st0 k bail) s Q ms.
Proof.
ltac2:(KReplay.run1_chk (kr_t_F_ntf ()) ["CEIL_WRAP_1"] "p'0h01rh11Hh22G1h32G2h41ai001ah52o0h61Qh71Rh84bailh91gh:1hh;1kh<2msh=1oi011oh>1sh?3st0h@2H0hA1NhB1PhC1ei021bi034headi045hprevi052pvi061xp;1p;2p;3p;7p;5p;6p;;p200R0g0224R1p4p7210p8P0g006aR2p4p710p8P0g023PR3p4p7210p8P0g005RR4p4p710p8P0g00gjR5p4p710p8P2j1ATg00:_j24Tg00ocj19Tg00OSj1GTg024dj1;Tg0264j3:TP3j73Tg00=nj1ETg013Bj26Tg00E:j1FTg027Lj2BTg028^j1@j28Tg02:2j1?j27Tg02;Fj30Tg02<Xj3>TP4j5MTg01_Tj6LTg02=jj2KTg00KLj2JTP1l;CTP5j6ITg00B4j3DTg012`j2HTg004DR5f1R1f0R43Dp=1g000DR3/H4p=21414#;p=<f2R2/41#;/84p=5g00e8R6g00eXR77D4p==g020bR8g02>IR9g00aSR:f5R;#AR<\:R=g02?ZR>f7R?g02@jR@p-0RA[\>[RBf6RC,4;#9%G3RD'114C?RE#;RF/1Dp,4RUNpRGf;RHf:RIPCf9RJf8RK;:?O1f4RLf3RMP2F3[[PGPIPJg00beRN#E%9E/6DREPI%FN#ERN16FDg01?hRFP3%AH1BCKPC%2KRO#@PFP3P:1<?4%2JRP#?g01>XRQ%22RR/74RS95J2W0=0JK504%21RT/74RU95K1X0Q=0K?n10110400021010500504O1P;%2?17O4,8OX0Q=0?C5>KO1n10110600021010300PLDMPLPMP2P1%=EPGPHPIPN1<?K/6DRNPFP3f<RE#A1B?JP?%@PPFP3P:1<K4%2I#?A5I2SX0Q=0IJ504A5J1UX0Q=0JKn10110400021010500504O1PC17P4,8PX0Q=0K?9>JOO1n10110600021010300P;PLPMP2%=N14KJ#9RNP5PFP3114D14HERO#;/1DPGf@RPf?RVPHf>RWf=RX;:EO1PJPKP?F3RY[[161D#=RZ112DR[]2]1P4%24/1D14EXR\#;/1DPGfAR]PPPEA:VWXO1PIPJPKF3R^[[16TD#=R_P616RDP6PAP4g02B1RAg00cJn0110200020000XC6g02BNP7P4ELPA%2M/1D/K4b@RAW2W1X43P4O111DDR714IHR6#;/1DPGPVPWPIA:XEHO1PKP?PCF3[[16DD#=RR1J5DR`W2W1n10110100021010000PMP2O2b511ND1<JIRNP5PFP3%9O/1D111DP^[[P[^3Z]1P4%9\/1D11TDPGfBRTP]PXA:PVWO1PHPIPJF3[[PAX3_W1X43P4O1%96/1DPY\7[P`X3RW1n10110100021010000PLP2O2b511NDPLP1P4O2PGPWPXPJA:EHIO1P?PCP;F31BHXP5PFP3PGP]PPPEPFP3P:P4%2VR5#@PFP3P:1<W4%2PRN#?A5P2SX0Q=0PV504A5V1UX0Q=0VWn10110400021010500504RD%2WRR1754,85X0Q=0WX5>Vn10110600021010300O1PIPJPKF3PGPTP]PFP3fC#AP1PW%@NPFP3P:1<V4%2]#?A5]2SX0Q=0]P504A5P1UX0Q=0PVn10110400021010500504O1PX17N4,8NX0Q=0VW9>P5O1n10110600021010300PHPIPJF3]1P4PGPTP]PXPDO1PHPIPJF3P4W1X43P4O1PGPPPVPH%2X17R4,8RX0Q=0XE5>WO1PJPKP?F3P4W1n10110100021010000P1O1b5b1bBbAW3M;CW2M;CPGPIPJPIPKP?PCP;PLEIPMP2P1F3eW1X<@X6BX>>X8<X;=X?:X93X:9X=8X70PJPKP?PCP;PLPMP2P1P4O:X<@W6W>X8<W;W?X93W:W=X70o"). Qed.
End CEIL_WRAP_1.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
