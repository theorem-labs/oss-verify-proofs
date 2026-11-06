(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool Classical_Prop.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout State Monad Specs Run.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence MustExit HaltsAllowed.
From LinuxProcessSemantics.Riscv Require Import Prelude Sem.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Lib Require Import PropExec MState Frame Exec ITree Nodes RegsEquiv HaltsTree.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Lib Require Import Cfg.
From OSSVerify.Proofs.zstd.huf_decompress.lib Require KReplay.
Ltac2 kr_t_HaltsTreeB () := "C47Corelib7Classes?RelationClasses9ReflexiveC4ELinuxProcessSemantics?LinuxProcessSem2Fs4pathC47Corelib4Init5Logic6eq_indC47Corelib4Init5Logic8eq_transC47Corelib4Init5Logic7f_equalC47Corelib4Init5Logic8eq_ind_rC4ELinuxProcessSemantics?LinuxProcessSem2Fs2FsC4ELinuxProcessSemantics5Riscv7Prelude5bvmapC4ELinuxProcessSemantics?LinuxProcessSem5State7PipeBufC4ELinuxProcessSemantics?LinuxProcessSem3RunCinjected_family_offI47Corelib4Init9Datatypes4list00K4ELinuxProcessSemantics?LinuxProcessSem5Monad7outcome01C4ELinuxProcessSemantics?LinuxProcessSem5Specs<syscall_specC4ELinuxProcessSemantics?LinuxProcessSem5State7eff_retC4ELinuxProcessSemantics?LinuxProcessSem3Run9refusal_bI47Corelib4Init5Logic3and00I47Corelib4Init5Logic2ex00C46Stdlib5Logic>Classical_Prop7classicC47Corelib4Init5Logic3notI47Corelib4Init5Logic2or00K47Corelib4Init5Logic2or01K47Corelib4Init5Logic2eq01I47Corelib4Init5Logic2eq00K47Corelib4Init5Logic3and01K47Corelib4Init5Logic2ex01C47Corelib4Init5Logic9False_indK47Corelib4Init5Logic2or02C4ELinuxProcessSemantics?LinuxProcessSem3Run?refusal_decidedI47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01K47Corelib4Init9Datatypes4bool02I4ELinuxProcessSemantics?LinuxProcessSem3Run;SpuriousCfg00I4ELinuxProcessSemantics?LinuxProcessSem5State<SyscallInput00I4ELinuxProcessSemantics?LinuxProcessSem5State5Model00I4ELinuxProcessSemantics?LinuxProcessSem5State=SyscallEffect00I4ELinuxProcessSemantics?LinuxProcessSem5State5event00K47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00I4ELinuxProcessSemantics?LinuxProcessSem3Run4star00I47Corelib4Init9Datatypes6option00C4ELinuxProcessSemantics?LinuxProcessSem3Run6cfg_msC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics>ms_svc_pendingK47Corelib4Init9Datatypes6option01C4ELinuxProcessSemantics?LinuxProcessSem3Run9sys_inputC4ELinuxProcessSemantics?LinuxProcessSem3Run9cfg_modelc59OSSVerify5KrLib3Lib:HaltsTreeBGrefusal_decided_classicC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemanticsEEquivalenceDefinition8MustExit<decided_fromI4ELinuxProcessSemantics?LinuxProcessSem<MemImageType7Segment00I4ELinuxProcessSemantics?LinuxProcessSem3Run6config00K47Corelib7Numbers7BinNums8positive03C4ELinuxProcessSemanticsEEquivalenceDefinition8MustExit;run_decidedK4ELinuxProcessSemantics?LinuxProcessSem<MemImageType5Image01C4ELinuxProcessSemantics?LinuxProcessSem3Run;init_configc59OSSVerify5KrLib3Lib:HaltsTreeBDdecided_from_classicC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics?LinuxProcessSem3Run9ExecEntry01I4ELinuxProcessSemantics?LinuxProcessSem<MemImageType5Image00I47Corelib7Numbers7BinNums1Z00I4ELinuxProcessSemantics?LinuxProcessSem3Run9ExecEntry00I4ELinuxProcessSemantics?LinuxProcessSem5State9ProcInput00I47Corelib7Numbers7BinNums1N00I4ELinuxProcessSemantics?LinuxProcessSem<MemImageType8PhdrInfo00I4ELinuxProcessSemantics?LinuxProcessSem;StackLayout9EntryDraw00C4ELinuxProcessSemanticsEEquivalenceDefinition8MustExitAmust_exit_in_scfgC4ELinuxProcessSemantics?LinuxProcessSem3Run6cfg_lec59OSSVerify5KrLib3Lib:HaltsTreeBCrun_decided_classicC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemanticsEEquivalenceDefinition8MustExitFmust_exit_in_scfg_monoC4ELinuxProcessSemantics?LinuxProcessSem3Run?family_may_failC4ELinuxProcessSemantics?LinuxProcessSem3Run<may_fail_cfgI4ELinuxProcessSemantics?LinuxProcessSem3Run>SpuriousFamily00K4ELinuxProcessSemantics?LinuxProcessSem3Run>SpuriousFamily01K4ELinuxProcessSemantics?LinuxProcessSem3Run>SpuriousFamily02K4ELinuxProcessSemantics?LinuxProcessSem3Run>SpuriousFamily03K4ELinuxProcessSemantics?LinuxProcessSem3Run>SpuriousFamily04K4ELinuxProcessSemantics?LinuxProcessSem3Run>SpuriousFamily05K4ELinuxProcessSemantics?LinuxProcessSem3Run>SpuriousFamily06C4ELinuxProcessSemantics?LinuxProcessSem3Run;valid_entryC4ELinuxProcessSemantics?LinuxProcessSem3Run;valid_inputC4ELinuxProcessSemanticsEEquivalenceDefinition;EquivalenceIsource_within_budget_scfgc59OSSVerify5KrLib3Lib:HaltsTreeBMmust_exit_in_scfg_of_may_failC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemanticsEEquivalenceDefinition<HaltsAllowedLhalts_allowed_T_scfg_budgetsc59OSSVerify5KrLib3Lib:HaltsTreeB6texitsC1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic4True01I59OSSVerify5KrLib3Lib5ITree5itree00C1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List2InC59OSSVerify5KrLib3Lib5ITree4respC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5ITree9itree_indC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5ITree4bindC1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib3Lib5ITree5itree01C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib3Lib5ITree5itree02C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib3Lib:HaltsTreeB7tleavesC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic4True00C59OSSVerify5KrLib3Lib9HaltsTreeCmsteps_must_exit_inC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5ITreeHleaves_unreachable_m_retC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5ITree7tree_atC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5ITree<tree_at_stepC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5ITree4implC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5ITreeDleaves_unreachable_mC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem5State8m_haltedK47Corelib4Init9Datatypes6option02C59OSSVerify5KrLib3Lib5ITree5tsafeC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib3Lib4Exec6msteps00C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5ITree4nretC1?~~~~~~~~~~~~~~~K4ELinuxProcessSemantics?LinuxProcessSem3Run6config01C47Corelib4Init5Logic5proj1C59OSSVerify5KrLib3Lib5ITree;ns_progressC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5ITree8ns_soundC1?~~~~~~~~~~~~~~~I4ELinuxProcessSemantics?LinuxProcessSem3Run5sstep00C59OSSVerify5KrLib3Lib5ITree7ns_exitC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes4list01C59OSSVerify5KrLib3Lib5ITree;ns_completeC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem5State4m_fsK4ELinuxProcessSemantics?LinuxProcessSem3Run7step_to01I4ELinuxProcessSemanticsEEquivalenceDefinition8MustExit?must_exit_in_at00C4ELinuxProcessSemantics?LinuxProcessSem5State8m_killedK4ELinuxProcessSemanticsEEquivalenceDefinition8MustExit?must_exit_in_at01K4ELinuxProcessSemanticsEEquivalenceDefinition8MustExit?must_exit_in_at02K4ELinuxProcessSemantics?LinuxProcessSem5State5event03K47Corelib4Init9Datatypes4list02I4ELinuxProcessSemantics?LinuxProcessSem3Run7step_to00K4ELinuxProcessSemantics?LinuxProcessSem3Run7step_to02I4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics=machine_state00I47Corelib4Init5Logic5False00c59OSSVerify5KrLib3Lib:HaltsTreeBFtree_at_must_exit_in_SC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitions7Z_to_bvK47Corelib7Numbers7BinNums8positive01K47Corelib7Numbers7BinNums1Z02C45stdpp9bitvector;definitions6bv_andK59OSSVerify5KrLib3Lib5Nodes4node08C1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Nodes5nexitC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem5State;with_haltedI59OSSVerify5KrLib3Lib5Nodes4node00C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib3Lib5Nodes4node01C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib3Lib5Nodes4node02C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib3Lib5Nodes4node03C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib3Lib5Nodes4node04C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib3Lib5Nodes4node05C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib3Lib5Nodes4node06C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib3Lib5Nodes4node09C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib3Lib5Nodes4node0:C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib3Lib5Nodes4node0;C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib3Lib5Nodes4node0<C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib3Lib5Nodes4node0=C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib3Lib5Nodes4node07C1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem5State:in_va_sizeC59OSSVerify5KrLib3Lib5Nodes7at_nodeC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem3Run5en_spC4ELinuxProcessSemantics?LinuxProcessSem5State7in_argvC4ELinuxProcessSemantics?LinuxProcessSem5State7in_envpC4ELinuxProcessSemantics?LinuxProcessSem5State6in_uidC4ELinuxProcessSemantics?LinuxProcessSem5State8in_hwcapC4ELinuxProcessSemantics?LinuxProcessSem3Run7en_drawC59OSSVerify5KrLib3Lib9RegsEquiv7init_msC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem3RunAsegments_reservedC4ELinuxProcessSemantics?LinuxProcessSem3Run6en_brkC4ELinuxProcessSemantics?LinuxProcessSem3Run<en_mmap_baseC4ELinuxProcessSemantics?LinuxProcessSem5State:init_modelC4ELinuxProcessSemanticsEEquivalenceDefinition8MustExit<must_exit_inC4ELinuxProcessSemanticsEEquivalenceDefinition8MustExitJmust_exit_in_scfg_may_failC4ELinuxProcessSemantics?LinuxProcessSem3Run8valid_spC4ELinuxProcessSemantics?LinuxProcessSem3Run9valid_brkC4ELinuxProcessSemantics?LinuxProcessSem3Run?valid_mmap_baseC4ELinuxProcessSemantics?LinuxProcessSem3Run@entry_stack_fitsC47Corelib4Init5Logic3iffC47Corelib7Classes9MorphismsDiff_impl_subrelationC4ELinuxProcessSemantics?LinuxProcessSem3Run@valid_entry_sv48C59OSSVerify5KrLib3Lib5Nodes4minvC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitions;bv_unsignedC56Stdlib6ZArith6BinInt1Z2leC56Stdlib6ZArith6BinInt1Z6moduloK46Stdlib9micromega6VarMap1t02K46Stdlib9micromega6VarMap1t03I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr02K46Stdlib9micromega=RingMicromega7Formula01K46Stdlib9micromega5Tauto8GFormula05C46Stdlib9micromega5Tauto8BFormulaC46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundC59OSSVerify5KrLib3Lib5Nodes9minv_initC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Nodes;nodes_soundC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem3RunBinit_machine_stateC59OSSVerify5KrLib3Lib9RegsEquiv6ms_eqvC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib9RegsEquivFinit_machine_state_eqvC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib9RegsEquiv:ms_eqv_symC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib9HaltsTreeCmust_exit_in_at_eqvC1?~~~~~~~~~~~~~~~K46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega5Tauto8GFormula08C59OSSVerify5KrLib3Lib5Nodes5nstepC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib3Lib5Nodes5nsafeC1?~~~~~~~~~~~~~~~C4ELinuxProcessSemantics?LinuxProcessSem5State<sp_window_hiK47Corelib7Numbers7BinNums1Z01C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K47Corelib4Init9Datatypes4unit01C59OSSVerify5KrLib3Lib9HaltsTreeChx_nexit_not_killedC1?~~~~~~~~~~~~~~~I4ELinuxProcessSemantics?LinuxProcessSem5State6VaSize00K4ELinuxProcessSemantics?LinuxProcessSem5State6VaSize02C4ELinuxProcessSemantics?LinuxProcessSem5State<sp_window_loI46Stdlib9micromega:ZMicromega;ZArithProof00K46Stdlib9micromega=RingMicromega3Op203".
Import ListNotations.
Open Scope bv_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma refusal_decided_classic : forall cfg i m, refusal_decided cfg i m.
Proof.
ltac2:(KReplay.run1 (kr_t_HaltsTreeB ()) [] "p'0h04evs'h12m'h24eff'h31Eh41Hh52Hsh62_Hh71bi001bh83cfgh91ih:1mh;1op;2p;1p;4p;3p-1p10000p4p710p9p1000\p4p70R0p1001Lp4p710R1p8P0p1001hp4p710R2p8P0p1002Fp4p7210R3p8P0p1002cp4p710R0p8p1003Ap4p70R4P1p8P4P2p8P4P3p8P4P0p8p1003op4p7210R4P1p8P4P2p8P4P3p8P4P0p8p1004[p4p70R4P1p8P4P2p8P4P3p8P4P0p8g005Qj2DTg006Qj1>Tg0071j48Tg007ij33Tg008dj15Tg009Zj31Tg00:Pj24Tg00:kj20Tg00;Ej1=Tg00;kj19Tg00<DR0j2;Tg00<^j3CTg00=8j2<Tg00=Rj36Tg00=lj4BTg00>Gj4:Tg00>aj2ATg00?@j3?Tg00?Zj3@Tg00@VR4f0R3g00A6R236p=7g00AVR19643p=2g00B6g00C0g00CmR5f2R6f1R7'D#7g00DcR8g00Ea#>R9f5R:f4R;P8P6P7P3C8R<33%56R=91:;#2'4X09'0X15,05X28'0R>#=%9>,;>P0f6R0?3:<A10:=#2'4X09,09X15,05X28,08R>%9>f7R>?30<R?A1>0=#2'4X09,09X15,05X28,08R@f8RAf3RB#5RC71>#7\?^09^15^28';P3A3A><R?A1A>=#2'4X09,09X15,05X28,08RDf9RE?1ACRC#7\?^09^15^28RF;C3X4@P3O1%9@PCP41<43f:RC%5;71E=643P4f<REf;R@%5031RG=643%77]3P7%5:91@CRC#71<42W3%2CA6412P>P8f?R1f>R2;3<A112=#2'4X09,09X15,05X28P0P5f=R1P8PAP7P3C8532%5A9121#2'4X09,09X15P:P9P8P>P0P3C8931E%5>911E#2'4X09P;P8P0P:P;C893E@%2GPBP3CBC:C:C:O1'AW3n0110000020000P3O1b3b7X5?X09X15X289?DFW4P3O1n200100000021000011000b;W6A@673eW:W9W8o"). Qed.

Lemma decided_from_classic : forall cfg segs c, decided_from cfg segs c.
Proof.
ltac2:(KReplay.run1 (kr_t_HaltsTreeB ()) [] "h02_Hh13_H0h21ch32c'h43cfgh54segsh62trh72x8p;1p;4p;2p;3g006Qj12Tg00FWj10Tg00G<j14Tg00GZj13Tg00H=j4=Tg00I0j1;Tg00IRj11Tg00JEj15Tg00KKj26Tg00=Rj37Tg00Kmj38Tg00Lcj19Tg00MYj3:Tg00Ndj3<Tg00B6g00Oh#2g00PgR0g00Ea#2g00Q\#0#0#0#0#0#0#4#3R1f4f3R2f2R3f1R4C=%;1%13#5161437f7f6%12;83%923:W1W0W7X30W6f09<34eW2W5W4o"). Qed.

Lemma run_decided_classic : forall cfg img lim en inp, run_decided cfg img lim en inp.
Proof.
ltac2:(KReplay.run1 (kr_t_HaltsTreeB ()) [] "p'0h03inph12enh23limh34brk0h43cfgh53imgh65mbaseh72pch82phh93rndh:4segsh;2spi001ei016en_brki027en_drawi03<en_mmap_basei045en_spi051ii06;img_init_pci079img_phdrsi08<img_segmentsp;5p;1p;3p;9p;4g00RAj51Tg006Qj18Tg00SDj32Tg00FWj10Tg00G<j17Tg00GZj16Tg00TAl94Tg00U9j33Tg00VAj45Tg00B6g00W9R0P0g00X6R0g00XTR1g00YLR2f5R3f3R4f2R5f1R6f0R7D1]0]1]2P7g00Oh#8g00ZFg00ZdP1f;R8f6f4R9723P4P6P7D1^02P7g00Q\#0#0#0#0#0#0#7#6R3g00[dfBR:f=R;P;f<R<P8P9P4P5P6f:R=P7M9433P:A2;<8P=P9P4P5P6C5P7D1eX02W9X63X33W;P4P5P6P7O4n01100000140104101103102X11X20W8W7W:P5P6P7O3n01105000130108106107W5W4o"). Qed.

(* [comment removed for export] *)
Lemma must_exit_in_scfg_of_may_fail : forall cfg S img lim en inp,
  cfg_le cfg ACFG ->
  must_exit_in_scfg ACFG S img lim en inp -> must_exit_in_scfg cfg S img lim en inp.
Proof.
  intros cfg S img lim en inp Hle H.
  apply (must_exit_in_scfg_mono cfg ACFG S img lim en inp Hle).
  - apply run_decided_classic.
  - exact H.
Qed.

(* [comment removed for export] *)
Lemma haltsB_of_must_exit_may_fail : forall cfg S img lim,
  cfg_le cfg ACFG ->
  (forall en inp, valid_entry img en inp -> valid_input inp -> must_exit_in_scfg ACFG S img lim en inp) ->
  halts_allowed_T_scfg_budgets cfg lim S img.
Proof.
  intros cfg S img lim Hle H en inp Hve Hvi _.
  apply must_exit_in_scfg_of_may_fail; [exact Hle|]. exact (H en inp Hve Hvi).
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section TExits.
  Variable node : Type.
  Variable nexit : node -> Model -> word -> Model -> Prop.
  Variable S : list word.

  Fixpoint texits {R} (t : itree node R) : Prop :=
    match t with
    | Ret _ => True
    | Vis n k => (forall mo code mo', nexit n mo code mo' -> In code S) /\ (forall r, texits (k r))
    end.

  Lemma texits_ret : forall {R} (r : R), texits (Ret r).
Proof.
ltac2:(KReplay.run1 (kr_t_HaltsTreeB ()) ["TExits"] "h01Rh11rp200R0p100oBp6054111001p8f0g010<W1X00o"). Qed.

  Lemma texits_vis : forall {R} n (k : resp -> itree node R),
    (forall mo code mo', nexit n mo code mo' -> In code S) -> (forall r, texits (k r)) -> texits (Vis n k).
Proof.
ltac2:(KReplay.run1 (kr_t_HaltsTreeB ()) ["TExits"] "h04codeh12moh23mo'h31rh42Hkh52Hnh61Rh71kh81np;2p;1p;3p;4p,4nodeR0p4p300g010XR1p4p710p8p200R2g00oBR3p6054111001p8P1j26Tg00FWj10Tg00G<j13Tg00GZj12Tg011Nj35TP3j21Tg00=lj44Tg011eR3f2R1,60[g00CmR4g00Q\#0#0#0#0#0#0#3#2R5p,5nexitR6f4R7P1f1R8f0R9O4p,1S9551R:[^24]0]1P1P9O1,17^33P6f6P1P8P9O4P:[^24^05^14f5f3P9O1'1^33P8P9C4W4W5W7X80X62o"). Qed.

  Lemma texits_bind : forall {A B} (t : itree node A) (f : A -> itree node B),
    texits t -> (forall a, texits (f a)) -> texits (ITree.bind node t f).
Proof.
ltac2:(KReplay.run1 (kr_t_HaltsTreeB ()) ["TExits"] "h01rh14codeh21fh32moh43mo'h52Hfh62Hth71ah81th91Ah:1Bh;2Hkh<2Hnh=2IHh>1kh?1np;2p;5p;3p;4p;1p;6p200R0g012XR1p4p7210p8P0g013PR2p4p7210p8P0g00oBR3p6054111001R4p8p201R5P2p4p73110p8P5P4p8g010Xj23TP3j20TP2j51Tg014Cj34Tg0159j45Tg00FWj12Tg00G<j1;Tg00GZj1:Tg011Nj39Tg00:PR2j27Tg00=lj46TP1j68Tp,4nodeR1f1R3'3P1f2R41314f3R61316[R7f4R8/03f5R9P4f0R:O1R;,09]7R<P1f6R=P9P6P4D1,09[[]2W8A4183,08P:P6O1P1P=P9A41=6P4D1,09eX5<W6X27X04g011eR71318[1319\9R<P4P3O1,0=f7R>10>;]7R;P1f8R?P>P8P6O1P4D1,0>[[]2\7P1P=P6P4C5,0=P2g00CmR2g00Q\#2#2#2#2#2#2#;#:R6p,5nexitR@P?P4P3P:O4p,1S9964RA[^42]1]3f9RBP9P:O1'0^07P@PBP4P3P:O4PA[^42^16^32P1f:RCPBP=P:O1P8D1,0B^07'7P3P@PCP4P3P:O4PA[^42^16^32f<RCP?P:O1'0^07P@PCP4P3P:O4PA[^42^16^32P1f=PCPBP:O1P>D1,0C^07P3P?P:P>P3P:O1P9O4X07C6W;W<P3P:O2n2001000000120000000P1P?P>P1P?P9P8C5P4D1,0>eX5;W6X2<W=W>X?1P:E8W8X:5X90o"). Qed.

  (* [comment removed for export] *)
  Fixpoint tleaves {R} (P : R -> Prop) (t : itree node R) : Prop :=
    match t with
    | Ret r => P r
    | Vis n k => forall r, tleaves P (k r)
    end.

  Lemma tleaves_mono : forall {R} (P P' : R -> Prop) (t : itree node R),
    tleaves P t -> (forall r, P r -> P' r) -> tleaves P' t.
Proof.
ltac2:(KReplay.run1 (kr_t_HaltsTreeB ()) ["TExits"] "h01rh12HPh22Hth31th42IHh51Ph62P'h71Rh81kh91np;2p;3p;4p;6p200R0g012XR1p4p7210p8P0g015oR2p60521002p8g010Xj21TP2j30Tg014Cj33Tg0159j42TP1j64Tf0R1p-0R2[f1R3P2[p,4nodeR2f2R4'1P2f3R51125f4R6?051f5R7P7P1O1P7P3O1[]0R8f6R9?064[[W3A32619065P1P4P3O2A32949096eX18W2X05g011eR81127[P3P1O19097f7R:P:P1O1P:P3O1[]0R:f8R;P5P4O1709[[\8P2P9P4P3C29097P5P1P4P1O1P3O3X08P2P;P6P5C290;9eX1:W2W4W8X92P1E4W3W6W5X70o"). Qed.

  Lemma tleaves_true : forall {R} (t : itree node R), tleaves (fun _ => True) t.
Proof.
ltac2:(KReplay.run1 (kr_t_HaltsTreeB ()) ["TExits"] "h01th12IHh21Rh31kh41nh51rp;2p;3p;4p;6p200R0g012XR1p4p7210p8P0g015oR2p60521002p8g010Xj21TP2j30Tg014Cj33Tg0159j42TP1j64Tp,4nodeR1f0R2'1P1f1R31113f2R4g016jR5V4R6;02W0g010<A31429046eX53g011eR6f3,11[f4R7P5V7R5P3P2O130\6P2P1P7P4P3C29075eW1W3X41P2E4W0X20o"). Qed.

  Lemma tleaves_bind : forall {A B} (P1 : A -> Prop) (P : B -> Prop) (t : itree node A) (f : A -> itree node B),
    tleaves P1 t -> (forall a, P1 a -> tleaves P (f a)) -> tleaves P (ITree.bind node t f).
Proof.
ltac2:(KReplay.run1 (kr_t_HaltsTreeB ()) ["TExits"] "h01fh12Hfh22Hth31ah41rh51th61Ah71Bh82IHh91Ph:2P1h;1kh<1np;2p;3p;5p;4p;6p200R0g012XR1p4p7210p8P0g013PR2p4p7210p8P0g015oR3p60521002R4p8p201R5P2p4p73110p8P5P4p8g010Xj21TP3j30TP2j52Tg014Cj33Tg0159j44TP1j65Tf1R1p-0[R2p,4nodeR3f3R4'1P3f4R61136f5R71137[R8f6R9?061f7R:P9f0R;O1f8R<P4P1O1R=709[]3R>P3P<P:P4f2R?D290:7[[]0W5A33919096P;P4P1O2P3P<P:A33<4P?D290:7eX1>W2X08X46g011eR81139[113:\:R>P?P1O190<9f9R@P<P;O1f:RA?0<=[]3R=P3PAP@P6P4O1P?D290@:[[]0\8P3P<P4P?C490<9P6P;P4P?P;O1P1O4X48P3PAP@P3PAP7P6C4P?D290@:eX1=W2X0>W8W;X<3P;E5W5X92W:X75X60o"). Qed.

  (* [comment removed for export] *)
  Lemma texits_bind_P : forall {A B} (P : A -> Prop) (t : itree node A) (f : A -> itree node B),
    texits t -> tleaves P t -> (forall a, P a -> texits (f a)) -> texits (ITree.bind node t f).
Proof.
ltac2:(KReplay.run1 (kr_t_HaltsTreeB ()) ["TExits"] "h01rh14codeh21fh32moh43mo'h52Hfh62Hrh72Hth81ah91th:1Ah;1Bh<2Hkh=2Hnh>2IHh?1Ph@1khA1np;2p;3p;5p;4p;1p;6p200R0g012XR1p4p7210p8P0g013PR2p4p7210p8P0g00oBR3p6054111001R4p8P0g015oR5p60521002p8p201R6P2p4p73110p8P6P4p8g010Xj23TP3j20TP5j34TP2j52Tg014Cj36Tg0159j45Tg00FWj11Tg00G<j1<Tg00GZj1;Tg011Nj3:Tg00:PR2j27Tg00=lj48TP1j69Tf1R1p-0[p,4nodeR5f2R3'3P5f3R41354f4R71357[R8f5R9/01f6R:?473f7R;P:f0R<O1R=f8R>P7P1O1R?'0[]8R@P5P>P;P7P4D2,0;[[[]2W9A6591,09A65:394:7P<P7P1O2P5P>P;A65>7P4D2,0;eX5@W6W7X28X04g011eR81359[135:\:R@P3P1O1,0;P4P3O194>:f9RAP>P<O1f:RB/0?[]8R?P5PBPAP9P7O1P4D2,0A[[[]2\8P5P;P4P3C5,0;P5P>P7P4C594>:P2g00CmR2g00Q\#1#1#1#1#1#1#<#;R7p,5nexitRCPAP3P1P<O4p,1S9:73RD[^42]1]3f;RE/0=^08PCPBP3P1P<O4PD[^42^17^32P5f<PEP;P<O1P9D2,0E^08'7P3PCPEP3P1P<O4PD[^42^17^32f>REPAP<O1'0^08PCf=P3P1P<O4PD[^42^17^32P5f?PEPBP<O1P>D2,0E^08P1PAP<P>P1P<O1P=P9O5X08C8W<W=P1P<O2n2001000000120000000P5PBPAP5PBP:P9C5P4D2,0AeX5?W6W7X2@W>W@XA5P<E9W9W?X;6X:0o"). Qed.
End TExits.
Arguments texits {node} nexit S {R} t.
Arguments tleaves {node} {R} P t.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section BridgeS.
  Variable node : Type.
  Variable segs : list Segment.
  Variable at_node : node -> machine_state -> Prop.
  Variable nstep : node -> Model -> resp -> Model -> list event -> Prop.
  Variable nexit : node -> Model -> word -> Model -> Prop.
  Variable minv : Model -> Prop.
  Variable nsafe : node -> Model -> Prop.
  Hypothesis NS : node_sound node segs at_node nstep nexit minv nsafe.
  Hypothesis NK : forall n mo code mo', nexit n mo code mo' -> m_killed mo' = None.
  Variable S : list word.

  Theorem tree_at_must_exit_in_S : forall {R} (t : itree node R) Q ms mo,
    texits nexit S t ->
    tree_at segs at_node nstep minv nsafe t Q ms mo ->
    must_exit_in_at_cfg ACFG segs S (mkCfg ms mo).
Proof using NS NK S.
  intros R t. induction t as [r | n k IH]; intros Q ms mo HX HT.
  - destruct HT as (_ & Hl & _). destruct (leaves_unreachable_m_ret node nstep r mo Hl).
  - destruct HX as [HXn HXk].
    pose proof HT as (Ht & Hl & Hh & Hinv & Hsf).
    cbn in Ht. destruct Ht as (ms1 & Hm & Hat & Hk).
    apply (msteps_must_exit_in node segs at_node nstep nexit minv nsafe NS S ms ms1 mo Hm Hh Hinv).
    apply must_exit_in_at_cfg_running.
    + exact Hh.
    + destruct (ns_progress _ _ _ _ _ _ _ NS n ms1 mo Hat Hh Hinv (proj1 Hsf)) as [(rsp & mo' & evs & Hst) | (code & mo' & Hex)].
      * destruct (ns_sound _ _ _ _ _ _ _ NS n ms1 mo rsp mo' evs Hat Hh Hinv (proj1 Hsf) Hst) as (_ & _ & Hss). eauto.
      * destruct (ns_exit _ _ _ _ _ _ _ NS n ms1 mo code mo' Hat Hh Hinv (proj1 Hsf) Hex) as (_ & Hss). eauto.
    + intros evs Hss.
      destruct (ns_complete _ _ _ _ _ _ _ NS n ms1 mo evs SError Hat Hh Hinv (proj1 Hsf) Hss)
        as [(rsp & mo' & E & _) | (code & mo' & E & _)]; discriminate E.
    + intros evs c' Hss.
      destruct (ns_complete _ _ _ _ _ _ _ NS n ms1 mo evs (SNext c') Hat Hh Hinv (proj1 Hsf) Hss)
        as [(rsp & mo' & E & Hst) | (code & mo' & E & Hex & _)].
      * injection E as ->.
        destruct (tree_at_step node segs at_node nstep nexit minv nsafe NS n k Q ms1 mo rsp mo' evs Hat Hk Hl Hh Hinv Hsf Hst) as [HT' _].
        exact (IH rsp Q (nret ms1 rsp) mo' (HXk rsp) HT').
      * injection E as ->.
        destruct (ns_exit _ _ _ _ _ _ _ NS n ms1 mo code mo' Hat Hh Hinv (proj1 Hsf) Hex) as (Hh' & _).
        apply (must_exit_in_at_cfg_halted ACFG segs S _ code); cbn [cfg_model];
          [exact Hh' | exact (HXn mo code mo' Hex) | exact (NK n mo code mo' Hex)].
Qed.
End BridgeS.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma texits_NExit : forall S c {R} (k : resp -> itree node R),
  In (bv_and (Z_to_bv 64 c) (Z_to_bv 64 255)) S -> (forall r, texits nexit S (k r)) -> texits nexit S (Vis (NExit c) k).
Proof.
ltac2:(KReplay.run1 (kr_t_HaltsTreeB ()) [] "h04codeh11Hh22moh33mo'h41rh53Hinh62Hkh71Rh81Sh92_Hh:1ch;1kp;1p;2p;3p;5p;4p;6p101QVp4p710g00oBR0p4p710p8p200R1P0p4p741110p8g00FWj11Tg00G<j1@Tg00GZj1<Tg006Qj18Tg010Xj2?Tg01R`j22Tg01SFj10Tg01Skj1;Tg01TIj35Tg011Nj34TP0j57Tg01Tnj19Tg01UcR0j4:Tg00=Rj33Tg01VWj26Tg002cj6>Tg00=lj4=Tg00Q\R2#1#1#1#1#1#1#@R3#<R4#8g00X6g011eR5g01WQR6f1R7'?[f2R8,23%02#0#0#0#0#0#0#;,23R2553f3R9544P6P0f5R:P9P8f0R;O1D7^45g00CmR<f7R=#9P8P7P;C:R>f9R?9448[^3<^04]2P6P0f6R0f4R6P9P;O1D7^45g00:Pf8,23=5329348168993<7f:R89449P;1238=5329346P4f;,23=532R216;=93<:f>9447[X04162093<6P?W9P:P;E>W1P7P;O2n2001000000121000000X1>X3<X04X2<P;C=W6W5W;X71W:W8o"). Qed.

(* [comment removed for export] *)
Lemma texits_vis_noexit : forall S n {R} (k : resp -> itree node R),
  match n with NExit _ => False | _ => True end -> (forall r, texits nexit S (k r)) -> texits nexit S (Vis n k).
Proof.
ltac2:(KReplay.run1 (kr_t_HaltsTreeB ()) [] "p'0h01Hh12Hnh22fdi002fdh34addri014addrh43leni023lenh54codei034codeh62moh73mo'h84proti044proth91rh:3reqi053reqh;2Hkh<1Rh=1Sh>2bsi062bsh?3bufi073bufh@4bufsi084bufshA5code0hB5counti095counthC5flagsi0:5flagshD1khE1ni0;1nhF4pathi0<4pathp;1p;2p;5p;4p;3p200R0g00oBR1p4p741110p8g00FWj13Tg00G<j17Tg00GZj15Tg006Qj14Tg010Xj2ETP1j56Tg01UcR1j40Tg011Nj31Tg01XFj2;Tg00>aj22Tg01Y;j28Tg01Z0j19Tg01Zej3:Tg01[Zj1DTg01\Oj2CTg01Tnj1BTg01]Dj1=Tg01^9j4>Tg01^nj2?Tg01_cj3<Tg01`Xj2@Tg00=lj4ATg00Q\#3#3#3R2#3#3#3#7#5R3#4g01WQR4g011eR5f1R6,E4[P4p-0R7f2R8g016jR9P9P9P9P9P9P9g01Q9R:P9P9P9P9P9n0110;000=20100106201001081010<3010010710910100201001050010103101054010110210410:201011023010110210420101102P4P1f5R;f3R<P8f0R=O1D6^95g00CmR>f7R?P8P6P=C0R@f9RA9138[^7>^53]6P4P1f6R1f4RBP<P=O1D6^95P4P4P7P=P9P9P9P9P9P9P9P:P9P9P9P9P9n0110;000=20100106201001081010<3010010710910100201001050010103101054010110210410:201011023010110210420101102P6P;PBP<C0f<R7913;]0]1f8R4g00X6R5%72#5#4R21;86P4P?P1C0f?9134/2=RCW0X19W>W2P6P=O2%421886P4P?P1C0PCW0X19W@X25P6P=O2%96P1P;PBC0f=9131RD/2=REW0X19XF2P=O1A:<86f:R2PAP4C0fA9132/2=RFW0X19XB5X?5X25P8P6P=O3%D6P1P;PBC0PEW0X19X25P=O11C86P4P?P1C0PCW0X19X:5X25P6P=O2g01aMPBP<P8C0f;RG913B/2=W0X19%B6P1P;PBC012D6W0X1:XA5P=O1%=6P1P;PBC0PEW0X19X:5P=O1PBP<P8P6C>P7PGP2C0fC9137/2=W0X19XC5X85X45X35P<P8P6P=O41?86P4P?P1C0PCW0X19X45X35P6P=O2A<<86P2PAP4C0PFW0X19X85X45X35P8P6P=O31@86P4P?P1C0PCW0X19X45X35P6P=O2n0110;000=20100106201001081010<3010010710910100201001050010103101054010110210410:201011023010110210420101102P;P=O2X0@X7>X53X6>P=CAW;W1WDX<0WEW=o"). Qed.

Theorem halts_of_impl_tree_S : forall segs pc ph lim S {R} (t : itree node R) (Q : R -> machine_state -> Prop) en inp,
  valid_entry (mkImage segs pc ph) en inp ->
  in_va_size inp = Sv48 ->
  texits nexit S t ->
  impl segs (at_node segs) t Q
       (init_ms segs pc ph (en_sp en) (in_argv inp) (in_envp inp) (in_uid inp) (in_hwcap inp) (en_draw en)) ->
  leaves_unreachable_m nstep t (init_model (segments_reserved segs) (en_brk en) (en_mmap_base en) (en_sp en) lim inp) ->
  tsafe nstep nsafe t (init_model (segments_reserved segs) (en_brk en) (en_mmap_base en) (en_sp en) lim inp) ->
  must_exit_in_scfg ACFG S (mkImage segs pc ph) lim en inp.
Proof.
  intros segs pc ph lim S R t Q [sp brk0 mbase rnd] inp Hve Hsv48 HX Himpl Hleaves Hsafe.
  cbn [en_sp en_brk en_mmap_base en_draw] in Himpl, Hleaves, Hsafe.
  cbn [must_exit_in_scfg]. unfold init_config.
  set (mo := init_model (segments_reserved segs) brk0 mbase sp lim inp) in *.
  assert (Hminv : minv mo).
  { rewrite (valid_entry_sv48 _ _ _ Hsv48) in Hve. destruct Hve as (Vsp & _ & _ & _).
    apply minv_init. destruct Vsp as (L & H & _). lia. }
  apply (must_exit_in_at_eqv segs S
           (mkCfg (init_ms segs pc ph sp (in_argv inp) (in_envp inp) (in_uid inp) (in_hwcap inp) rnd) mo)).
  - apply (tree_at_must_exit_in_S node segs (at_node segs) nstep nexit minv nsafe (nodes_sound segs)
             hx_nexit_not_killed S t Q _ _ HX).
    split; [exact Himpl | split; [exact Hleaves | split; [reflexivity | split; [exact Hminv | exact Hsafe]]]].
  - split; [| reflexivity]. cbn [cfg_ms]. apply ms_eqv_sym. apply init_machine_state_eqv.
Qed.
