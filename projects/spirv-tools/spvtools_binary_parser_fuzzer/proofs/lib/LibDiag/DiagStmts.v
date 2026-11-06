(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.spirv_tools.spvtools_binary_parser_fuzzer.images Require Import Plain.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import
  PropExec CatExec CatSim SeqExec StoreOk Hoare ShapeAlg SRealizes RefMemcpyLib LibIface LibBudget LibEff S1Layout.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibCont Require Import CRep ContStmts.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash Require Import HRep.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs Require Import PrsNeeds.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.Drv Require Import Overlay RunsLib.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibDiag Require Import DRep DiagS1 DsRoom.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import RunRandom.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require KReplay.
Ltac2 kr_t_DiagStmts () := "C46Stdlib5Lists4List6map_idC47Corelib4Init5Logic6eq_indC46Stdlib5Lists4List7map_mapC49OSSVerify5KrLib8LibIface2ASC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8LibIface4ainvC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive01K47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1Z02K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00C45stdpp9bitvector;definitions;bv_unsignedK47Corelib4Init9Datatypes3nat02C49OSSVerify5KrLib9RunRandom9rr_canaryC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitions7Z_to_bvC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics@word_to_le_bytesC47Corelib5Lists7ListDef3mapc59OSSVerify5KrLib7LibDiag9DiagStmts9dn_canaryC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8LibIface?ai_static_cellsC1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes4list00I47Corelib4Init9Datatypes6option00C47Corelib4Init9Datatypes6lengthK47Corelib4Init9Datatypes6option01I47Corelib4Init5Logic2eq00C49OSSVerify5KrLib7CatExecDlength_Z_to_le_bytesC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List:length_mapC47Corelib4Init5Logic8eq_ind_rC45stdpp9bitvector;definitions5bv_eqC45stdpp9bitvector;definitions7bv_wrapC45stdpp9bitvector;definitionsDbv_unsigned_in_rangeC45stdpp9bitvector;definitions=bv_wrap_smallC45stdpp9bitvector;definitions@Z_to_bv_unsignedC46Stdlib5Lists4List7map_extC59OSSVerify5KrLib7LibCont4CRep3fldC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8PropExec3rdnC1?~~~~~~~~~~~~~~~C69OSSVerify6KrSpec8ProblemscSrc_spirv_tools_spvtools_binary_parser_fuzzer_repro1M?loaded_segmentsC1@~~~~~~~~~~~~~~~~c69OSSVerify5KrLib7LibDiag9DiagStmts2Ly1LC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8LibIface3memC1?~~~~~~~~~~~~~~~I4ELinuxProcessSemantics?LinuxProcessSem5State5Model00i59OSSVerify5KrLib7LibDiag9DiagStmts:diag_needs00C1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive03I47Corelib7Numbers7BinNums1Z00K47Corelib4Init9Datatypes3nat01I47Corelib4Init9Datatypes3nat00I47Corelib7Numbers7BinNums1N00I47Corelib4Init5Logic3and00K47Corelib4Init5Logic2eq01C59OSSVerify5KrLib7LibDiag4DRep7ds_lawsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7LibDiag6DiagS14dcS1C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib7LibDiag4DRep8DS_VBOFFC1?~~~~~~~~~~~~~~~".
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Module Ly := S1Layout.
Abbreviation SEGS := Plain.M.loaded_segments.

Section Stmts.
Context {AC : AllocCeiling} {RRND : RunRandom}.
  Variable MI : MallocIface SEGS Ly.L.
  Variable ST : StaticsIface SEGS Ly.L.

  Record diag_needs : Prop := DIAG_NEEDS {
    dn_mstack : 0 <= MALLOC_STACK MI <= 8192;
    dn_new : new_rule_stmt SEGS Ly.L MI ST (ContStmts.NEW_STACK SEGS Ly.L MI);
    dn_statics : forall (s : SX ST) (M : mem), sx_inv ST s M -> pins D_DIAG M;

    dn_classes : DsRoom.classes_sep SEGS Ly.L MI;
    dn_round_big : DsRoom.round_big_add SEGS Ly.L MI;

    dn_canary : In (0x120928, map bv_unsigned (word_to_le_bytes 8 (Z_to_bv 64 rr_canary))) (static_cells MI)
  }.

  Lemma canary_fld : forall A M model, diag_needs -> ainv MI A M model -> fld SEGS M 0x120928 8 rr_canary.
Proof using AC RRND MI ST.
ltac2:(KReplay.run1 (kr_t_DiagStmts ()) ["Stmts"] "h02HCh11nh21lh31xh42b1h52b2h61Ah72AIh82DNh91Hh:2HLh;1Mh<5modelh=1zp;4p;7p;1p;2p;;p;3p;6p;5g0000R0p4p710g000KR1p4p710R2p8g000gR3p4p73110P2p8g001Cj4UTg0023j7TTg002ej18Tg003Jj15Tg003oj1LTg004Mj1<Tg004kj16Tg005Nj1Dj21Tg0068j13Tg006Wj1BTg007Oj2:j1GTg0085j2?Tg009=j4;Tg009Yj1STg00:Yl;RTg00;Vj1KTg00<6j1HTg00<Xj2>Tg00=8j27Tg00=Zj30Tg00>4j2ETg00?5j4FTg00?Tj6=TP1j69TP3j6CTg00@2j3ITg00@Vj2JTg00A<j2ATg00Aoj3MTg00B[j2NTg00CJj6@TP0j2OTg00Cfj5PTg00D[j4QTf0R0#5#5p=2g00ELR3f2R1f1R2P0CQp=4p,2ACR4P3g00GAR5p,2MIR6CUg00H<g00Hmg00IcP4P3P5P6f3R7P1P2FTP4P3P5P6f4R6P7P1g00JfR5#2#8#5#2#2#8#2#8#2#8#5#8#5#2#LR4%55#2R5#<R8#6R9g00KKR:%D8R;g00Ki#3#3#3#3#3#3#3#3R<%55#2#<R5p,4RRND#BR=':R>'?R?C;R@P0%S2M;R%K9RA#HRB1:54RC1>:@RD547P:P9%G8REP@C;R@,7ARF30g00LHRG1>9?A0G0<X1G115>,E<PDP9P:P;P?CFE=A0GD<PGPDf6RD?4C0=0BFX1GP2P<P0E9f5?4C<=0BFPAP@f7?4C<R@17A0RF50BX2AP0P9P91180,:8X39RGP?C;R>P9P:P9P;PEP?ECE9A4DC<17A>50BPAP>f8?4C<R>=0BFX2AP0P9P9P0X39RDP?C;REP9P9PGPDg00LgRD%60RG%62R;g00ME%61?0201171117250:R5[1112111050:%67?012[RH%66?071\5AI120P0n2001000000120000000W5W4W1PH^5;^4G^1DP0P81182RD,:8RGP2P:1J8D118190:0X=:1A829M8D118G1N8DE=O4b9X39P?E@E917AE90B@PAPEf9?4C<=0BFX2AP0P?1O9?E917A?90B>P0b0b0b0b0b:b0P3P7P4P<P=DPeW7W8W<W;W6o"). Qed.

  Definition diag_contract : Prop :=
    ds_rep_laws SEGS Ly.L MI ST dcS1 (ds_rep MI)
    /\ ds_ctor_stmt SEGS Ly.L MI ST dcS1 (ds_rep MI)
    /\ pdiag0_stmt SEGS Ly.L MI ST dcS1 (ds_rep MI)
    /\ pdiagE_stmt SEGS Ly.L MI ST dcS1 (ds_rep MI)
    /\ put_cstr_stmt SEGS Ly.L MI ST dcS1 (ds_rep MI)
    /\ put_u16_stmt SEGS Ly.L MI ST dcS1 (ds_rep MI)
    /\ put_u32_stmt SEGS Ly.L MI ST dcS1 (ds_rep MI)
    /\ put_u64_stmt SEGS Ly.L MI ST dcS1 (ds_rep MI)
    /\ put_int_stmt SEGS Ly.L MI ST dcS1 (ds_rep MI)
    /\ put_string_stmt SEGS Ly.L MI ST dcS1 (ds_rep MI)
    /\ ds_dtor_stmt SEGS Ly.L MI ST dcS1 (ds_rep MI).

  Definition diag_main_goal : Prop := diag_needs -> diag_contract.

  Theorem diag_laws : ds_rep_laws SEGS Ly.L MI ST dcS1 (ds_rep MI).
Proof using AC MI ST.
ltac2:(KReplay.run1 (kr_t_DiagStmts ()) ["Stmts"] "p;2p;5g00M`j21Tg00N:j50Tp,2ACp,2MIp,2STg00O3g00KKg00Ok'1D0o"). Qed.
End Stmts.
