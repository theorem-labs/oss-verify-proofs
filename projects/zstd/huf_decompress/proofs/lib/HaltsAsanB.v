(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence MustExit HaltsAllowed.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.zstd.huf_decompress.lib Require Import TopLevel AsanMain.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Lib Require Import ITree Nodes HaltsTreeB.
From OSSVerify.Proofs.zstd.huf_decompress.lib.LibA Require Import HaltsTrace HaltsTraceB HaltsShape.
From OSSVerify.Proofs.zstd.huf_decompress.lib.AS Require Import ShapeAlg SpinAlg MainExport MainFactsAsan MainEntry MainEntryH.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Spec Require Import Prog AsanInv ProgExits.
From OSSVerify.Proofs.zstd.huf_decompress.lib.AsanW Require Import AImg.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Lib Require Import Cfg.
From OSSVerify.Proofs.zstd.huf_decompress.lib Require KReplay.
Ltac2 kr_t_HaltsAsanB () := "C4ELinuxProcessSemantics?LinuxProcessSem2Fs2FsC47Corelib4Init5Logic6eq_indC47Corelib4Init5Logic8eq_ind_rC47Corelib4Init9Datatypes3appC56Stdlib6ZArith6BinInt1Z2leK47Corelib4Init9Datatypes4list01I47Corelib4Init9Datatypes4list00K46Stdlib9micromega6VarMap1t02I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr02K46Stdlib9micromega=RingMicromega7Formula01K46Stdlib9micromega5Tauto8GFormula04C46Stdlib9micromega5Tauto8BFormulaK47Corelib4Init5Logic2eq01C46Stdlib9micromega:ZMicromega=ZTautoCheckerI47Corelib4Init5Logic2eq00C46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundI47Corelib7Numbers7BinNums1Z00C4ELinuxProcessSemantics?LinuxProcessSem5StateBsource_alloc_limitI46Stdlib9micromega:ZMicromega;ZArithProof00C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K47Corelib7Numbers7BinNums8positive03K46Stdlib9micromega=RingMicromega3Op203K47Corelib4Init9Datatypes4unit01I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01K47Corelib7Numbers7BinNums1Z01C59OSSVerify5KrLib4Spec7AsanInv7LIMIT34C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec7AsanInv:LIMIT34_eqC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1Z02K47Corelib7Numbers7BinNums8positive01C56Stdlib6ZArith6BinInt1Z3powC47Corelib4Init5Logic9False_indI47Corelib4Init9Datatypes:comparison00K47Corelib4Init9Datatypes:comparison02K47Corelib4Init9Datatypes:comparison03I47Corelib4Init5Logic5False00I47Corelib4Init5Logic4True00K47Corelib4Init5Logic4True01K4ELinuxProcessSemantics?LinuxProcessSem<MemImageType5Image01C4ELinuxProcessSemantics?LinuxProcessSem3Run;valid_entryC4ELinuxProcessSemantics?LinuxProcessSem3Run;valid_inputC4ELinuxProcessSemantics?LinuxProcessSem3RunQvalid_input_either_of_valid_inputC4ELinuxProcessSemantics?LinuxProcessSem3RunBvalid_input_eitherI47Corelib4Init5Logic2or00K47Corelib4Init5Logic2or01C59OSSVerify5KrLib2AS9MainEntry9amain_atLC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8AsanMain>amain_atL_openC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8AsanMainCasan_main_srealizesC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics?LinuxProcessSem3Run6config01C49OSSVerify5KrLib8AsanMain2TAC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib2AS7SpinAlg9srealizes00C1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic2or02K4ELinuxProcessSemantics?LinuxProcessSem3Run4star01C59OSSVerify5KrLib2AS7SpinAlgCsrealizes_star_onlyC1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic3and01C47Corelib4Init5Logic3iffC59OSSVerify5KrLib2AS8ShapeAlg4t_eqC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib2AS7SpinAlg9srealizes03C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib2AS:MainEntryHAasan_boot_R_validC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem3Run5en_spC4ELinuxProcessSemantics?LinuxProcessSem3Run6en_brkC4ELinuxProcessSemantics?LinuxProcessSem3Run<en_mmap_baseC4ELinuxProcessSemantics?LinuxProcessSem3Run7en_drawI59OSSVerify5KrLib2AS8ShapeAlg8realizes00C1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00K4ELinuxProcessSemantics?LinuxProcessSem3Run9ExecEntry01I47Corelib4Init9Datatypes6option00K47Corelib4Init9Datatypes6option02K4ELinuxProcessSemantics?LinuxProcessSem5State5event04I69OSSVerify5KrLib3Lib5ITree3Exc3exc00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec7EquivPA3toPC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec4Prog4progC1?~~~~~~~~~~~~~~~C49OSSVerify5KrLib8TopLevel3mo0C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4LibA:HaltsTraceEtree_traces_no_killevC1?~~~~~~~~~~~~~~~C47Corelib4Init5Logic3notK4ELinuxProcessSemantics?LinuxProcessSem5State5event03C46Stdlib5Lists4List2InC59OSSVerify5KrLib4Spec9ProgExits;prog_texitsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4LibA;HaltsTraceBBtree_traces_exit_SC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4LibA:HaltsShapeFrealizes_must_exit_cfgC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemanticsEEquivalenceDefinition8MustExitAmust_exit_in_scfgC59OSSVerify5KrLib3Lib:HaltsTreeBLhaltsB_of_must_exit_may_failC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem3Run;init_configK47Corelib4Init9Datatypes4list02C59OSSVerify5KrLib5AsanW4AImg5asegsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5AsanW4AImg9a_init_pcC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5AsanW4AImg7a_phdrsC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem3Run<may_fail_cfgC59OSSVerify5KrLib4Spec9ProgExits7EXITS02C1?~~~~~~~~~~~~~~~I4ELinuxProcessSemantics?LinuxProcessSem5State5event00I4ELinuxProcessSemantics?LinuxProcessSem3Run;SpuriousCfg00C5ELinuxProcessSemanticsEEquivalenceDefinition;Equivalence>ShippedBudgets:lim_sourceI4ELinuxProcessSemantics?LinuxProcessSem3Run9ExecEntry00I4ELinuxProcessSemantics?LinuxProcessSem5State9ProcInput00I4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=machine_state00I4ELinuxProcessSemantics?LinuxProcessSem5State5Model00c49OSSVerify5KrLib:HaltsAsanB<lim31_sourceC1?~~~~~~~~~~~~~~~c49OSSVerify5KrLib:HaltsAsanB<lim34_sourceC1?~~~~~~~~~~~~~~~I4ELinuxProcessSemantics?LinuxProcessSem;StackLayout9EntryDraw00C59OSSVerify5KrLib5Plain4PImg5psegsC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5Plain4PImg;PREAD_STAGEC1?~~~~~~~~~~~~~~~".
Import ListNotations.
Open Scope Z_scope.
Section H.
Variable rsA : Z.
Hypothesis asan_impl : asan_impl_stmt rsA.
#[using="Type"] Lemma lim34_source : LIMIT34 <= source_alloc_limit.
Proof.
ltac2:(KReplay.run1 (kr_t_HaltsAsanB ()) ["H"] "h04__x1h17__arithh24__ffh38__varmaph45__with51zp;2p;1p;4p;7p;3p;6p10000p4p70R0p1000^p4p710p8P0g001:R1p4p710p8P0p1001Xp4p710p8g0025j20Tg002Qj1?Tg0031j12Tg003Qj21Tg003oj1>Tg004Mj1:Tg0058j23Tg005[j44Tg006Fj75Tg006jj26Tg007Lj27Tg007fj28Tg008Rj39Tg008lj3=Tg009Kj4<TP1j6;Tg00:=R1g00:[R0f0R2/00X51g00;\R3#?%23f1R3,11%>1%:1R4g00<Hg00<gR5P5g00=GR5P1g00=g,31R6g00>LP6C4g00?3F51645P2f2R5g00?SR4g00@3R6'71825=946dg00@S==13C<b2b3b4X011022^01P2P0O1b1g00A1g00AjE;o"). Qed.
#[using="Type"] Lemma lim31_source : 2^31 <= source_alloc_limit.
Proof.
ltac2:(KReplay.run1 (kr_t_HaltsAsanB ()) ["H"] "p'0h01Hh11eh21xh31zi001cp;1p;2p;3p;6g00Bfj17Tg00CKj11Tg00Cij10Tg00DNj24Tg0025j23Tg008Rj36Tg000^j62Tg00Dkj25Tg00:=R0g00A1R1g00=gR2#7#1%02#0#0#0#1'4R2f0R3'3X30g00EJR0g00F0R4g00FVR536P0P4P0p-0P3g00G<R4g00GYP4n011000003000000X10g00H5P5P3E2P41543b0W21321dg00:[g00AjE2o"). Qed.
#[using="rsA asan_impl"] Theorem halts_asanB_of_impl : forall cfg, cfg_le cfg ACFG -> halts_allowed_T_scfg_budgets cfg ShippedBudgets.lim_source EXITS02 (mkImage asegs a_init_pc a_phdrs).
Proof.
  intros cfg Hle. apply (haltsB_of_must_exit_may_fail cfg EXITS02 _ _ Hle). unfold ShippedBudgets.lim_source.
  intros en inp Hv Hi. pose proof (valid_input_either_of_valid_input _ Hi) as Hei.
  set (T := fun tr : list event => tr = [] \/ TA source_alloc_limit inp en tr).
  assert (HR : ShapeAlg.realizes asegs
    (init_config asegs a_init_pc a_phdrs (en_sp en) (en_brk en) (en_mmap_base en) (en_draw en) source_alloc_limit inp) T).
  { apply (asan_boot_R_valid en inp T Hv Hi); [left; reflexivity|].
    intros ms mo HM.
    assert (HS : SpinAlg.srealizes asegs (mkCfg ms mo) (TA source_alloc_limit inp en)).
    { apply (asan_main_srealizes rsA asan_impl source_alloc_limit lim31_source en inp Hv Hei ms mo).
      exact (amain_atL_open source_alloc_limit en inp ms mo lim34_source HM). }
    apply (SpinAlg.srz_conseq asegs _ _ _ HS). intros tr. subst T. cbv beta. split; [intros H; right; exact H|].
    intros [->|H]; [| exact H]. exact (SpinAlg.srealizes_star_only asegs _ _ HS [] _ (star_cfg_refl _ _ _)). }
  destruct en as [sp brk0 mbase rdraw]. cbn [en_sp en_brk en_mmap_base en_draw] in HR. unfold must_exit_in_scfg.
  apply (realizes_must_exit_cfg asegs EXITS02 _ T HR).
  - reflexivity.
  - intros tr sig fs [E|H]; [destruct tr; discriminate E|]. exact (tree_traces_no_killev _ _ tr sig fs H).
  - intros tr code fs [E|H]; [destruct tr; discriminate E|]. exact (tree_traces_exit_S EXITS02 _ _ tr code fs (prog_texits _ _ _ _) H).
Qed.
End H.
