(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3: some recorded proofs replaced by tactic proofs; the new launch (process input, auxv, group id, exec file name); the read-only-backing form of the system-call steps; the run over the run's segments; the channel-reader premise of writev; imports; new lemmas. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require BvWfKernel.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Classical_Prop.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require Import BMode ShapeAlg SpinAlg ShapeEF KillFree Spec BigintSpec.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require Export UbjEncShapes.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require PropExec FrmInit.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.Common.Cfg Require SRomStable.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require KReplay.
Ltac2 kr_t_UbjEncGLink () := "C47Corelib7Classes9Morphisms6ProperC47Corelib7Classes?RelationClasses9ReflexiveC47Corelib7Program6Basics4flipC47Corelib7Classes9MorphismsKrespectful_per_obligation_1C4ELinuxProcessSemantics?LinuxProcessSem2Fs2FsC46Stdlib5Lists4List2hdC47Corelib4Init5Logic6eq_indC4ELinuxProcessSemantics?LinuxProcessSem3Run9is_prefixC47Corelib4Init5Logic8eq_transC47Corelib4Init5Logic7f_equalC47Corelib4Init5Logic8eq_ind_rC47Corelib4Init9Datatypes3appC47Corelib4Init5Logic3notC79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib7SpinAlgEsrealizes_bm_transferC13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib7SpinAlg=srealizes0_ofC13~~~I79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib7SpinAlg:srealizes000C13~~~I47Corelib4Init9Datatypes4list00I47Corelib4Init5Logic3and00I47Corelib4Init5Logic2ex00C4ELinuxProcessSemantics?LinuxProcessSem3Run=obs_trace_cfgC79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib7SpinAlgAsrealizes_obs_iffC13~~~C46Stdlib5Logic>Classical_Prop4NNPPC79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib5BMode;bm_off_instC13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib5BMode:bm_on_instC13~~~I4ELinuxProcessSemantics?LinuxProcessSem5State5event00I47Corelib4Init5Logic5False00K47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib4Spec?msg_cannot_openC13~~~K47Corelib4Init9Datatypes4list01K47Corelib4Init9Datatypes4list02C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib4Spec5t_dieC13~~~K46Stdlib7Strings5Ascii5ascii01K46Stdlib7Strings6String6string02C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib4Spec3s2bC13~~~K47Corelib7Numbers7BinNums8positive01K47Corelib7Numbers7BinNums1Z02C45stdpp9bitvector;definitions7Z_to_bvI47Corelib4Init5Logic2eq00C46Stdlib5Lists4List:app_eq_nilC47Corelib4Init5Logic9False_indK47Corelib4Init5Logic2eq01C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib4Spec1WC13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib4Spec9exit_codeC13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8ShapeAlg6t_exitC13~~~I47Corelib4Init5Logic2or00K4ELinuxProcessSemantics?LinuxProcessSem5State5event02C45stdpp9bitvector;definitions;bv_unsignedC45stdpp9bitvector;definitionsDZ_to_bv_obligation_1K45stdpp9bitvector;definitions2bv01C47Corelib5Lists7ListDef3mapc79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib;UbjEncGLink3ev0C13~~~K47Corelib7Numbers7BinNums8positive03K47Corelib4Init9Datatypes4bool01K47Corelib4Init9Datatypes4bool02K46Stdlib7Strings6String6string01I47Corelib4Init5Logic4True00K47Corelib4Init5Logic4True01I47Corelib7Numbers7BinNums1Z00K47Corelib7Numbers7BinNums1Z01I47Corelib7Numbers7BinNums8positive00K47Corelib4Init9Datatypes3nat02I47Corelib4Init5Peano2le00C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib4Spec:zero_linesC13~~~C56Stdlib6ZArith6BinInt1Z2leC46Stdlib9micromega;ZifyClasses7rew_iffK46Stdlib9micromega6VarMap1t01I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr01K46Stdlib9micromega=RingMicromega7Formula01K46Stdlib9micromega5Tauto8GFormula04K47Corelib4Init9Datatypes6option02K46Stdlib9micromega5Tauto8GFormula03K46Stdlib9micromega5Tauto8GFormula08C46Stdlib9micromega5Tauto8BFormulaC46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundK47Corelib4Init5Logic2ex01C46Stdlib9micromega;ZifyClasses5mkrelI47Corelib4Init9Datatypes3nat00C56Stdlib6ZArith6BinInt1Z6of_natC56Stdlib6ZArith4Znat5Nat2Z6inj_leK47Corelib4Init9Datatypes3nat01I46Stdlib9micromega:ZMicromega;ZArithProof00C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K46Stdlib9micromega=RingMicromega3Op203K47Corelib4Init9Datatypes4unit01I47Corelib4Init9Datatypes4bool00C47Corelib4Init9Datatypes6lengthC47Corelib4Init5Peano2ltI47Corelib4Init9Datatypes6option00C4ELinuxProcessSemantics?LinuxProcessSem2Fs9fs_lookupK47Corelib4Init9Datatypes6option01C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib<UbjEncShapes<ue_header_okC13~~~C56Stdlib6ZArith6BinInt1Z2ltC79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib<UbjEncShapes6ue_cfgC13~~~C56Stdlib6ZArith6BinInt1Z3addC79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib:BigintSpec4specC13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib<UbjEncShapes6spec_kC13~~~C56Stdlib5Arith8PeanoNat3Nat3lebC56Stdlib5Arith8PeanoNat3Nat6leb_gtC79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib4Spec=list_byte_eqbC13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib4Spec>msg_read_errorC13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8ShapeAlg6t_alt2C13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib:BigintSpec6t_bodyC13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib<UbjEncShapes8t_body_kC13~~~C56Stdlib6ZArith6BinInt1Z3mulC56Stdlib6ZArith4Znat5Nat2Z9is_nonnegC56Stdlib6ZArith6BinInt1Z=mod_pos_boundC56Stdlib6ZArith6BinInt1Z6moduloC56Stdlib6ZArith6BinInt1Z3lebC56Stdlib6ZArith6BinInt1Z6leb_gtC56Stdlib5Arith8PeanoNat3Nat3ltbC56Stdlib6ZArith6BinInt1Z6to_natC47Corelib4Init3Nat3addC79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8ShapeAlg6t_emitC13~~~C56Stdlib5Arith8PeanoNat3Nat6ltb_geK46Stdlib9micromega=RingMicromega5Psatz02K46Stdlib9micromega:ZMicromega;ZArithProof02K46Stdlib9micromega6VarMap1t02K46Stdlib9micromega6VarMap1t03K46Stdlib9micromega7EnvRing5PExpr02K46Stdlib9micromega7EnvRing5PExpr03C46Stdlib9micromega;ZifyClasses;rew_iff_revC56Stdlib6ZArith6BinInt1Z8max_specC46Stdlib9micromega9SatDivModCZ_mod_nonneg_nonnegC56Stdlib6ZArith6BinInt1Z7div_modC56Stdlib6ZArith6BinInt1Z3divC56Stdlib6ZArith6BinInt1Z=mod_neg_boundC56Stdlib5omega8PreOmega1Z;div_0_r_extC56Stdlib5omega8PreOmega1Z;mod_0_r_extK47Corelib7Numbers7BinNums1Z03K46Stdlib9micromega7EnvRing3Pol01K46Stdlib9micromega=RingMicromega5Psatz04c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib;UbjEncGLink?zero_lines_headC13~~~K47Corelib4Init5Logic3and01K47Corelib4Init5Logic2or01K47Corelib4Init5Logic2or02C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8ShapeAlg5t_nilC13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib;UbjEncGLink;ev0_not_dieC13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib<UbjEncShapesAlist_byte_eqb_neqC13~~~C47Corelib4Init5Logic6eq_symC47Corelib5Lists7ListDef3nthK46Stdlib9micromega=RingMicromega5Psatz06C56Stdlib6ZArith6BinInt1Z3maxC46Stdlib9micromega;ZifyClasses5mkappC46Stdlib9micromega;ZifyClasses6mkapp2K46Stdlib9micromega5Tauto8GFormula05K46Stdlib9micromega5Tauto8GFormula06C56Stdlib6ZArith4Znat5Nat2Z6inj_ltC46Stdlib9micromega8ZifyInst@of_nat_to_nat_eqC56Stdlib5Arith8PeanoNat3Nat3addC56Stdlib6ZArith4Znat5Nat2Z7inj_addK46Stdlib9micromega=RingMicromega3Op201C56Stdlib6ZArith4Znat5Nat2Z8inj_succC79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib4Spec8dot_pathC13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib4Spec9MAX_INPUTC13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8ShapeAlg4TSetC13~~~K46Stdlib9micromega=RingMicromega3Op205C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib4Spec;msg_refusedC13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib4Spec9msg_shortC13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib4Spec;msg_overrunC13~~~K46Stdlib9micromega:ZMicromega;ZArithProof01C4ELinuxProcessSemantics?LinuxProcessSem3Run8valid_spC4ELinuxProcessSemantics?LinuxProcessSem3Run9valid_brkC4ELinuxProcessSemantics?LinuxProcessSem3Run?valid_mmap_baseC4ELinuxProcessSemantics?LinuxProcessSem5State7in_argvC4ELinuxProcessSemantics?LinuxProcessSem5State7in_envpC4ELinuxProcessSemantics?LinuxProcessSem3Run@entry_stack_fitsC4ELinuxProcessSemantics?LinuxProcessSem3Run:valid_argvC4ELinuxProcessSemantics?LinuxProcessSem3Run:valid_envpC4ELinuxProcessSemantics?LinuxProcessSem5State5in_fsC4ELinuxProcessSemantics?LinuxProcessSem2Fs8valid_fsC4ELinuxProcessSemantics?LinuxProcessSem3Run;valid_credsC4ELinuxProcessSemantics?LinuxProcessSem3Run;init_configC4ELinuxProcessSemantics?LinuxProcessSem3RunJreaches_budget_refused_cfgC79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib<UbjEncShapes:ue_payloadC13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib7SpinAlg8frm_safeC13~~~C4ELinuxProcessSemantics?LinuxProcessSem3Run6cfg_msC4ELinuxProcessSemantics?LinuxProcessSem>RiscvSemantics7ms_fcsrC79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib7FPSteps8frm_zeroC13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib<UbjEncShapes;ue_reach_okC13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib;UbjEncGLink=shapes_differC13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib;UbjEncGLink:glink_coreC13~~~I4ELinuxProcessSemantics?LinuxProcessSem;StackLayout9EntryDraw00I4ELinuxProcessSemantics?LinuxProcessSem5State9ProcInput00K4ELinuxProcessSemantics?LinuxProcessSem<MemImageType5Image01C4ELinuxProcessSemantics?LinuxProcessSem3Run;valid_entryC4ELinuxProcessSemantics?LinuxProcessSem3RunAvalid_input_abortC4ELinuxProcessSemanticsEEquivalenceDefinition;EquivalenceIsource_within_budget_scfgC4ELinuxProcessSemanticsEEquivalenceDefinition;EquivalenceZstrong_equiv_error_free_budgets_scfg_abortK4ELinuxProcessSemantics?LinuxProcessSem3Run9ExecEntry01C4ELinuxProcessSemantics?LinuxProcessSem3RunIvalid_input_abort_va_sizeC47Corelib4Init5Logic3iffC47Corelib7Classes9MorphismsDiff_impl_subrelationC4ELinuxProcessSemantics?LinuxProcessSem3Run@valid_entry_sv48C4ELinuxProcessSemantics?LinuxProcessSem3Run=valid_sigmaskc79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib;UbjEncGLink8ue_glinkC13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib7SpinAlg9srealizesC13~~~C4ELinuxProcessSemantics?LinuxProcessSem3Run8run_scfgC4ELinuxProcessSemanticsEEquivalenceDefinition;EquivalenceCerror_free_unkilledC4ELinuxProcessSemantics?LinuxProcessSem3Run9bh_tracesC4ELinuxProcessSemanticsEEquivalenceDefinition;Equivalence;trace_equivC79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8KillFree>kill_free_specC13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8KillFreeMsrealizes_error_free_unkilledC13~~~C47Corelib7Classes9Morphisms?eq_proper_proxyC47Corelib7Classes9MorphismsMtrans_co_eq_inv_impl_morphismC79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib7ShapeEFDsrealizes_traces_iffC13~~~C47Corelib7Classes?RelationClasses?Equivalence_PERC47Corelib7Classes9MorphismsNtrans_sym_co_inv_impl_morphismC47Corelib7Classes?RelationClasses;reflexivityC4ELinuxProcessSemanticsEEquivalenceDefinition;Equivalence`strong_universal_error_free_T_scfg_budgets_abortC4ELinuxProcessSemantics?LinuxProcessSem5State:in_va_sizeC4ELinuxProcessSemantics?LinuxProcessSem5State;in_image_fsC4ELinuxProcessSemantics?LinuxProcessSem2Fs@fs_keys_relativeC4ELinuxProcessSemantics?LinuxProcessSem5State9in_nofileC4ELinuxProcessSemantics?LinuxProcessSem3Run<valid_nofileC4ELinuxProcessSemantics?LinuxProcessSem5State8in_hwcapC4ELinuxProcessSemantics?LinuxProcessSem3Run;valid_hwcapC4ELinuxProcessSemantics?LinuxProcessSem5StateAin_abort_terminalC4ELinuxProcessSemantics?LinuxProcessSem3Run=valid_urandomI4ELinuxProcessSemantics?LinuxProcessSem5State6VaSize00K4ELinuxProcessSemantics?LinuxProcessSem5State6VaSize02I4ELinuxProcessSemantics?LinuxProcessSem3Run9ExecEntry00I4ELinuxProcessSemantics?LinuxProcessSem<MemImageType5Image00C47Corelib7Classes?RelationClasses>iff_TransitiveC47Corelib7Classes?RelationClasses?iff_equivalenceC47Corelib7Classes?RelationClasses=iff_Reflexive".
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section Core.
Variable segs : list Segment.
Variable scfg : SpuriousCfg.
Variable c0 : config.
Variables Tn Tw : TSet.
Variable G : Prop.
Hypothesis FG : frm_guard segs c0.
Hypothesis NORM : @srealizes bm_on_inst segs scfg c0 Tn.
Hypothesis WEIRD : ~ G -> @srealizes bm_on_inst segs scfg c0 Tw.
Hypothesis PREM : ~ reaches_budget_refused_cfg segs scfg c0.
Hypothesis DIFF : exists tr, Tn tr /\ ~ Tw tr.

(* The budget-mode transfer turns each walk into an off-mode one (the source never reaches a
   budget refusal), the frm guard turns it into the bare [srealizes0], and two bare walks of the
   same start state have the same observable traces: a trace of [Tn] outside [Tw] refutes [~ G]. *)
Theorem glink_core : G.
Proof.
  apply NNPP. intros HnG.
  destruct DIFF as [tr [Htn Htw]]. apply Htw.
  pose proof (@srealizes_bm_transfer bm_on_inst segs scfg c0 Tn NORM PREM) as Nn.
  pose proof (@srealizes_bm_transfer bm_on_inst segs scfg c0 Tw (WEIRD HnG) PREM) as Nw.
  pose proof (@srealizes0_of bm_off_inst segs scfg c0 Tn FG Nn) as N0.
  pose proof (@srealizes0_of bm_off_inst segs scfg c0 Tw FG Nw) as W0.
  apply (proj1 (srealizes_obs_iff segs scfg c0 Tw W0 tr)).
  apply (proj2 (srealizes_obs_iff segs scfg c0 Tn N0 tr)). exact Htn.
Qed.
End Core.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section Shapes.

(* [comment removed for export] *)
Definition ev0 : event := WriteEv (Z_to_bv 64 1) (Z_to_bv 8 48).

Lemma ev0_not_die : forall path fs, ~ t_die (msg_cannot_open path) fs [ev0].
Proof.
ltac2:(KReplay.run1 (kr_t_UbjEncGLink ()) ["Shapes"] "p'0h01Eh13tr'h21Hh32EMh42NNh52_Hh61ei001eh72H0h82Hph91bi011bh:2NEh;2b0h<2fsh=1li021lh>3msgh?4pathi032b1i042chi054codei063fs0i071pi083sigi091xi0:1zp;1p;3p;8p;2p;4p;6g00Bbj10Tg00CGj1PTg00Cej1WTg00;2R0j1JTg00DHj1@Tg00EWj1NTg00F7j39Tg00FWj3VTg00G\j85Tg00H;j2HTg00H\j1STg00I_j13Tg00JDj12Tg00Jbj2ETg006Ej3ATg00KHj31Tg00Kbj4XTg00;RR1j2>Tg003Zj6MTg00LAj2UTg006bj1<Tg00L`j2LTg00M:j2BTg0046j3CTg00N;j1TTg00ODj38Tg00;mR2j2DTg00PNR3j2GTg00Phj24j1RTg00Q^j2ITg005Jj6KTg003Cj2Qj3OTg00RHj2[Tg00S;j3ZTg00S^j4YTf2R4f1R5f0R6'H'Hp=?f3R71[567Z4p=6f4R8A9456797p==g00AOR9?A569174p=7g00T:R:=196p=FP4P9P5P6CYp=:A9956p=;AA956p=\g00UDR;#0R<#0#0R=#PR>#WR?#JR@g002U%@5%N9999:RA7V6RBg00UiRCPCg00VIRDPDPDPCPCPDG5REPDPDPCPCPDPCPCPDG5PCPDPDPCPDPCPCPDG5PDPCPDPCPCPCPDPDG5PDPDPDPDPDPCPDPDG5RFPCPDPDPDPDPCPCPDG5PDPCPCPCPDPCPCPDG5RGPCPCPCPCPDPCPCPDG5RHPDPDPCPDPCPCPCPDG5PDPDPDPDPCPCPCPDG5PCPDPCPDPDPCPCPDG5g00Vi,HF7?G5?H7?F5?G3?7?E3?3?#SRE%3<#0#2,E>%N?RG59?RF9A?45A?=1@GRHP?PEAA?7FRDP6CXA1@EGREA1@DG'>P1PEAA?8F=1@Gg00BERDP6f7RC=A?F=1@GP@P?P>%3;RF#0RI#0RJ#0RK#3#3#2RLP>PLC6RLP?P>%3IRI#3RM#0#0#2RNP>PNC6P?P>%0I#0#3#2RIP>PIC6P?P>%3F#0RF#3#0RI#2RNP>PNC6P?P>%0=#0R=#2RNP>PNC6RNP?PLP?P>%0KRK#3#2RLP>PLC6P?P>%3MRM#0#2RLP>PLC6RLP?PLP?P>%3M#2RMP>PMC6RMP?P>%0I#2RIP>PIC6P?PNP?PMP?P>%0F#0#0#2RFP>PFC6P?P>%3J#0#3#2RJP>PJC6P?PLA9?NGD=D=D=D=D=D=D=D=P0P?p-0RNP6PDg00WJRLn10110200020020000000X6@g00WfRJPGP5EMPD1UD6RFb7W5X0EP5P6O2n2001000000121000000b0W0%<He%@4=1@G#<RHePH%@7P@1L@6%@8=1@6P0P?f6R0#@=1@6%2<R</B59C9A%J9RHPHPA1B<4P6C7%T<RE?8C6'>X1H'D'GA1@4G#<PD]4]2]3P5f5RM#@=1@G1B<GRI9C9APHPAPIP6C7A8E06'>X1H,DH'GA1@GG#<P61L@GO1W4W2W3f9RI#@A9?5651@A9?45,B<9C9APHPAA9?74RO,B<P6C7f:RP=8E6'>X1H,DH'GA1@OG#<%0=#PR=%2;R;'ERO%2K,E>'4R>1E=<RK/46RG519RQP9g00XBRRP9PRP6g00X`RS1I=5PSPSn01100000420104103201041032010510620108106X69P>14K5P6EK1I=O1I=K51RPRP;PRPNP6PDg00Y>PNP6PDPDPLn011070003100001000000PDn0110:0003001010710107X6RPJP<P6EMPDPFb7b0W0%<QeX9?%FG#<^9?RGePGP314KM%RKR3=:?8';9C9APHPA14K0A:?3M';RGP6C7f=RQ=8E6'>X1H,DHPDP4AC9AGP114KCRG#FPLPDP614KI#FP0f;RFP5O2X5LW8P5P6O2n2001000000120000000W8P6O1PHPAA:?30,;GP6C7f>RG=8E6'>X1H,DHP2PHPHPAf8,4KA:?3C';P6C7f?RC=8E6'>X1HPDP6PHPA14KPA:?3I';P6C7fA=8E6'>P1PHPA14KFA:?3P';P5C7fB=8E5PDP6PHPA14KQf<9:?3';P7C7fE=8E8PHP91Q9:PA14KCA:?3G/\M';RMP5EKAO9:AAO9:M519PFf@P6O2b0W5W0P5P6O2n2001000000120000000W2X1HP5P6O2n2001000000121109000W2P6O1n200100000021000011000b:W4W2W3X>@X;?P5P6O2n10110200020021101102P6P7P4O3b3b=b4W2%<BeW<W?o"). Qed.

Lemma zero_lines_head : forall n, (1 <= n)%nat -> exists tl', W 1 (zero_lines n) = ev0 :: tl'.
Proof.
ltac2:(KReplay.run1 (kr_t_UbjEncGLink ()) ["Shapes"] "p'0h03tl'h11Hh24__p1h32H0h47__arithh54__ffh68__varmaph75__with81kh91ni001np;1p;2p;3p;4p;7p;6p;8p;<g00Ycj17Tg00ZBR0j2:Tg00;2j1<Tg00JDj15Tg00Z\j14Tg00M:j29Tg00F7j32Tg00KHj31Tg00;mj26Tg00[fR1j2ETg00L`j23Tg00\Bj4ATg00EWj1TTg00\ij1STg00]Gj1RTg00]ej1OTg00^Pj2>Tg00_3j4NTg00_^j7MTg00`Bj1LTg00`dj6KTg00aHj8JTg00alj2ITg00bNj2HTg00c:j3FTg00cYj4GTg00Bbj10Tg00CGj1?Tg00Jbj28Tg00I_j1;Tg00Phj2=j1CTg00Cej1DTg00S^j4@Tg00dKj4PTg00del<QTg00eJR2g00XBR3P0g00eiP1g00fIf3f2R1f1R0g00fkR4g00X`R5f0R6M<Qp=BP2%74R7/:6g00AOR8#<R9g00UDR:#5R;%41R<'9g00T:R==286R>519X09'6[P61:74R?P?1E;5R?P7P;133;1335CBP6CAP?p-0R@g00gJRA#T%<A%S3%R3%O3RAg00h6RBg00hURCPCg00i5RDPAPBPCPCPDP31>3;g00iU1>35CNg00j<FM%LCPAPBPCPCPDP1EKGJ1IADP6P1g00j\RDg00UiRA'31H61=1DAdAF350CGb5b6b7W2P0\?^2@P6%44,9;=19>X09,69P0O2b4b3W1%76,:7P9%0:R7#0#0R4#0#0#0#?/8;R@%?4R4%;:#0#0#0#0#5'8'=%;7#0#5,84,=@R7%D4R4P8%C@R@P<C@528528=19>X09P4P8P@%40C@9287R7A28=7,39CP%71#4,9;=19>X09,69eW1X82P6O1n0110000020011100X92o"). Qed.

Lemma shapes_differ : forall (a0s path fdata : list byte) (fs0 : Fs.Fs),
  (length path < 4096)%nat -> path <> [] -> path <> dot_path ->
  fs_lookup fs0 path = Some fdata -> ue_header_ok fdata ->
  BigintSpec.spec [a0s; path] fs0 [ev0] /\ ~ spec_k t_nil [a0s; path] fs0 [ev0].
Proof.
ltac2:(KReplay.run1 (kr_t_UbjEncGLink ()) ["Shapes"] "p'0h01Hh11xi001xh24__x1h34__x2h41bh51yh65Hlen0h77__arithh84__ffh98__varmaph:5__with;4cstrh<5cstr0h=2H0h>4__p1h?3tl'h@2H1hA4__p2hB4__x3hC1ehD1ni011nhE2z1hF1EhG2H2hH2H3hI2H4hJ2H5hK2H6hL2HChM2HdhN4HhdrhO4HlenhP3HlkhQ4HmaxhR2HnhS3HndhT3HnehU6__sat2hV3a0shW5fdatahX3fs0hY1li021lhZ1oh[4pathh\1qh]1rh^3tr'i03:config_leni044datap%0p&0p;1p;2p;3p;4p;6p;<p;7p;8p;Bg00Bbj1FTg00CGk10pTg00Cek10QTg00;2S00j1sTg00k<j25Tg00YcR0j11Tg00k\R1j2ETg00EWj1bTg00KHj3=Tg006bj1VTg00l4R2k10hTg00lVj2yTg00mKk204Tg00mmk10_Tg00eiR3j16Tg00oAR4j22Tg00I_k10YTg00JDj1QTg00o]j18Tg010kR5j2<Tg00[fR6j23Tg00F7j3@Tg011Hk300Tg012Rj4}Tg013`j2^Tg014@k20FTg00DHj1HTg00FWj27j3rTg014cj2iTg0160k10@Tg017>j2wj39Tg018Hk20=Tg019Tk30;Tg00Jbk20jTg01:dk208Tg00\Bj4TTg01;Aj1[Tg00\ik10`Tg00]Gk10^Tg00]ek10]Tg00^Pj2mTg00_3j4lTg00alk20\Tg00L`j2xTg00bNk20[Tg00c:k30ZTg00cYk40XTg01;fk30Wk20BTg01<Mj2OTg00;RR7j2;Tg01<mj2MTg01=Jk20OTg01=jj2BTg01>JR8j1:Tg01>jj2vTg00Z\j1KTg00M:j2JTg00N;k10NTg00ODj2hk30ITg01?Aj2gk30ETg00ZBR9j2ITg01@Kk20JTg01@nj2eTg01AWj2XTg01BCj2~Tg01Baj4ZTg01C?j2]Tg00`Bk10HTg01Cbj3cTg01DEj4oTg01E0j2{Tg00PNS01j2_Tg0046j3dTg006Ek30DTg00;mS02k201Tg01ERk20LTg01FCk20MTg01Fdj2uTg01GAk20ATg01Ghk20RTg01HNk20STg01I4k10TTg01IRk20?Tg01J3k30UTg01J\k20VTg01L2k40>Tg005gj6kTg01LMk30oTg01Lgk30nTg01MAR:k10mTg01NJk30lTg003Zk60:Tg00LAk20iTg01O\k309Tg01Q5k40gTg01QQk405Tg00Q^k207Tg00dem<02Tg00_^k706Tg01Qmk30dTg00aHk80eTg01RVk20fTg01S3m<0<Tg01SXmB0cTg00`dk60bTg01T>k70aTg01Tbk70kTf0R;#1#1p>03%1;#1#1#1#1#1#1#1p>0P%1;#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1p>0K%1;#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1#1p=0g00AOR<g00T:R=;@;p=tf1R>%V;';p=>g00j\R?g00VIR@7=;p=CP?P>P@P;H0gp=aA=?@;p=jf4RAf3RBf2RCP>P;H05+07p=D%F;#Fp=\g00XBRD/x;p=?g00eJREPDP1P3P4g01UFf5R4PAPBPCP>P;N<02p=Wg00X`R1/3;p=4P>g00h6RFg00hURGPGg00i5RHP;g00j<RIK06p=Y121;p=RPAPBPCP>H05-074/O;p=APEPDP9P3P6g00fIP4PAPBPCP>P;N<02p=fB0dD>;p=PPCPFPGPGPHPDP>g00iUP;ClPIK06p=GPBPFPGPGPHPCP>P;L0ep=S20f1;p=LPDPEPDPDP8PAP3PBg01UhPCP>P;N<0<p=|PEPEPEPDPDPDg01VUP3P3P3P5g01W5P4PAPBPCP>P;NB0cp>0GA=D>;p=NA=D;1p=UP>PFPGPGPHP;J0bp=pPDP>g01WXP;Clp=qPCPFPGPGPHP>P;K0ap=`PCPFPGPGPHP>P;K0kp=zPEPEPDPDP0P3P3PBg01X?PCP>P;N<0<p>0CP?P@PBPCP>P;J0:p=ng00UDR3#FS03#FR0#FRF$0pR5$0QR8#sRIg002U158Cg00fkR6#1R9#1RJ#1S04#1$03RK$03$0P$0K#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0#0RL'E%b8RM9=IB#Vg01XcRN9=IA#V&0hIRO1yB4204IA3=&0_4P7f6RP,58#6RQg01YkRR'2&0Y3RS#FS05#QRT%8P'</3Qf9RQf8RU%bIS065@I5@IRV%b<S07#tRW800PP:PVPPPWC}'>P;158U#6/2R%8Q,<T158Q#6'3f;RV,58RX,^LRYP71^>;#C1E>CRZ[1E;>1^C>#C[R[1^BC#C\Z20F>;P;n2001000000120000000X5EX1EP[^5E^1EP;PLf<R[,58RZPQO3b0'a%jYP?g01[4RYP;f=R\#H/7VR]P?PY1i\MR^P]P?PY1i\NR_&0@\/7V,w]R`P2PIPY1yV\Raf>Rb#H/7[Rc20=;['wRdP]n10110000021010400Ren0100000020000Rfn0100000020000n0100000020000PWO1P?PYP;P]P?PYP^P]P?PYP_P`P2PIPYPaB0;:;[,wcRcP]n10110000021010400Ran0100000020000R_n0100000020000n0100000020000PWO1'>X4?P?P@P?PYP;P]Pfn0100000020000PWO1P?PYP;P]P_n0100000020000PWO1'>X4?P?P@P?PYP;P`Pen0100000020000PWO1P?PYP;P`Pan0100000020000PWO1'>X4?PO204IVP2PIPYP;PdP]n10110000021010400PWO1P2PIPYP;PcP]n10110000021010400PWO1'>XZOP5P8P6PV20j51RODD%FF#\#\RF#QP5P8P9PVPODD+08'<R]%\F#\RF#F#\#QRc1EZL%6ZR2%QFRF'2RdPZP2%?2PLPF%?FRaEWPQCTPd158\Rd#[R`%6dS08#4ReP`Peg00gJRe#bR`%seR@&0`DR_&0^DRf&0]DR^PD1mD1Rgg01\<S091mDcCl'Y20\^HRHP;PCg00UiRh,x?20[;C==?hdB0ZD1>H0XRhb8b9b:%RcP;b7b<b;b640W1O]cS0:#4Q0:/2c';1MR2R2P71M>;#C12>CR][12;>1MC>#C[Ri1MBC#C\]20O>;P;n2001000000120000000X5DX1DPi^5D^1DP;PRQ08PAO3b0'a%j2f?R2#H/7\RiP?PYP;g01\cS0;/7\R]P?PY158bRj/BKS0<g01]nRk/7\RlP?PY%8b#:Rm,vK,BjRng01_7Ro/7\Rp%Q3RqPEPEPmP9P5P8PJP2PO%Q0RmEA#:#1n0110300020010101#K'J&0N1Rr/h\'gn0100000020000S0=n0100000020000n0100000020000;9WP?PYP;P]P?PYQ0<PlP?PYPnPpP:n0100000020000S0>n0100000020000n0100000020000=9iW'>X4?1BdKRdP71B>;#C1I>CRp[1I;>1BC>#C[Rl1BBC#C\p20J>;P;n2001000000120000000X5EX1ES0?Pl^5E^1ES0@P;PjPK1IKj%6jRl,3TPKPT%?TS0APjPl%?lEf1582Rl/EL%6lRj/2FRpPlPj%?jS0BPLPFPaEWP[CTPpf@Rp,58R]#[Rs%6]Rt#4RuPsPuP7fARu#8Rs#412scfBRv,58S0C#6S0D,3TP4fCRw#8Rx#4S0EfDS0F#8Ry/2cS0G1eDJS0H1eD9S0I1eD6S0J'PS0K'PS0Lg01`BR6'X=@e`P@PDP_P>1~DCS0MCZPfP^1]DSRS9G^g&0HGRGP^1mDTRz=cDS1]D3RS5G^PGAG^zSCSCSPHPhb8b9b:X2DX3D%4>1<TC/3>13TC[[^2D^3DP;fFS0N#8R{Q0N,58#6PCP[O4b7W=W0P>P;O2n2001000000121000000b<b;b6CoO3b0'a%jd%HpS0O/7bRdP?PYP;17kbS0PP?PY%82R|#:S0Q,vKR},BlS0R17obS0SPEPEQ0QP9P5P8PJPpPOPmEA#:#1n0110300020010101S0T#K,JqR~1hrbS0U'gS0Vn0100000020000n0100000020000;9WP?PYP;Q0PP?PYQ0RQ0SP:n0100000020000n0100000020000=9dW'>X4?Q0?Q0@P;PlP}1I}l%L|S0@,<TS0?/3jP}Q0?PKPTQ0AQ0QQ0@P;X1DS0@%L;X1DS0AP|P|%?|D|J0GPlPjQ0BEf1E]L12tFRjP]Pt%?tPLPFPaEWP\CTPj158uRj#[Rt%6jR]#4RlPtPl%8vRl,{1%Rl%LlRt/Nl';13l1%Ut';'_%LxPDP7%4yQ0G1<T>fERt,58#6'3PU%4{fGS0G#8/2cp-0RlQ04,eDR|Q0L'P/X6Q0K,P|/X6=@e`5@eP@PDPD1~DBPCP_CZP>P_CZPfP^1p^41]D0R0,qS,Y^5`^1p^P1qSg,Y^R|5`^5z^PGP^AG^g0PGP^AcDz0Q03,]DR05G^PGAcDzS=G^0CSCSCSPHPhb8b9b:X2DX3DXBDX>lWA1N;C,;B%U;R0,;A'_%4B1<TA/3B1<TB/3A[[[^2D^3D^BD^>l^AlP;fIRT#8RB/31%RBPB158T#6P4PPPCP2O8b7W=W0P>P;O2n2001000000121000000bEb@b<b;b6CoO3b0,an%jn%HuS03/72RnP?PYP;17o2RBPEPE%8p#:P9P5P8PJPuPOPmEA#:#1n0110300020010101#K,JqRz1hr2'gn0100000020000;9WP?PYP;PBP:n0100000020000=9nW'>X4?Q0V=9dWA9d:WS0V#VS0KQ0O?rbWQ0U>0E~WAd<W~%s<R~B0D<z;9=~WB0Ir2;';X^~+01Q0TQ0QPEPEPEPEP;P9P5P8PJPvPOPmEARd#:S0Q#1Rnn0110300020010101,I9P;1I9913qqRBP9Pq%?qR}P9PqP}Ef1EjL12]FS0UPjP]%?]PLPFPaEWPbCTQ0UQ0C#[R]Q0D#4RjP]PjP7Q0E12xcPBf7Rj%8t#412{cP`P@P_Pf1mDqR{=G^{PHPhb8b9b:PBP;b7W=W0P>P;O2n2001000000120000000b<b;b6Co1I9n%LdRB/<qR],3qP9PqP}PnP]1<;qX1DQ0QPBQ0@Q0APdPd%?dD|H0CEf158wRd/EL%6dRB/2FR]PdPB%?BPLPFPaEWPpCTP]Q0F,58R]#[Ra%6]#4R]PaP]P5P8PJPtPOPmEARt,{1%Rt%LtR]/Nt';13t1%U]';'_P5P8PJQ0NPOPmEA#LPDP5P8PJQ0GPODDR]00Lm%4]%4mP5P8PJPTPODDRT/OmR]#4[[P5P8PJfHPODD00Mm%UmRa#V1uTm-08m/<],NT[20BTm%RmP5P8PJfJPODDRT/OmR]#412]m';[20ATm12m1P5P8PJfKPODDRT/OmR],2m13]1';[20RTmP5P8PJfLPODDRT/um#U\a20STmP5P8PJfMPODDRT/Om/NT\a1uTmPDP5P8PJfNPOPmEAPDP7fO#8R7#4127c1<Qq,3qPwfQ#8#4fR#8/2c&0T3-0?DQ0I60UDQ0J'PR3/X6Q0H/P3/X6=@e`5@eP@PDPDP_PCQ0MCZP>P_CZPfP^PDPgQ09Q05,]DRgCl,Y^1qSg,Y^5`^1p^A=`^|5z^PGAcDS{9G^{CSPHPhb8b9b:X2DX3DX>l%R>1N;>';1;C0'_1<>q,3q[^2D^3D^>lP;1341P4P\PbO4b7WKWJP>P;O2n2001000000121000000b]b\bIbHbGb=b0bUbEb@b<b;b6CoXDEP;O1n0110100020111101bD+0V%t;Rb9=~zX?~-01~Q02P~PEPE%:sP9Pnn0110300020010101#K,JqRn==~bX?~Ad<WnP;PEPE%:xP9P5P8PJQ0FPOPmEA#:#1n0110300020010101#K,Jq==~bP~%t>RbAd<W;XY~A=<==g00WJRx1x<=g00WfR=H0>Ad<WbePEPE%:yP9%:t#1n0110300020010101#K,JqP;EkWFX?~P>P;O2n2001000000120100000bC40o40nQ0VQ01Q03?r2W&0mWR2g00BERtP;%Hv?rpWB0lwu;WMP;O1P~PWQ00P<PlP;PtPxn10110200020020000000XC~P=Q07P;J0:Pt20it;b0XR2P;O1n200100000021000010000W0Q0KeH0>Q0RP;Cnb0Q0==9iWQ0>=9iW'>RiePieQ0<P;Cnb0Q08,MRP;Cnb0bL%H[f:Ri'7R2P?PY%6X,MRRRQ0;/7iRtP?PY1BXKR=17kiRkP?PYQ0:#:R~,vK,BXRX17oiRoPEPEP~P9P5P8PJP[POPmEA#:#1n0110300020010101#K,Jq1hri'gn0100000020000n0100000020001n0100000020001;9WP?PYPRPtP?PYP=PkP?PYPXPoP:n0100000020000n0100000020000n0100000020000=92W'>e20=Vi=92WB0;:Vi=92W'>e1yi[PPEk1i[NB09[NjEk1i[MB09[MUEk1^LZP;Cnb0Q069@IV9@I[R[@00QWP:P[PQPWC}'>eWNWQP>P;O2n2001000000121000000W0WPWSWTWOWXXWIX[IWVo"). Qed.
End Shapes.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [Run.valid_input_either]'s clauses, read by type, as the model's own
   [valid_input_either_of_valid_input] does.  The SIGPIPE disposition is not among them: at
   LPS 727298f3 it is free. *)
Lemma vie_parts : forall inp, valid_input_either inp ->
  valid_argv (in_argv inp) /\ valid_envp (in_envp inp) /\ valid_fs (in_fs inp)
  /\ valid_creds inp /\ valid_hwcap (in_hwcap inp) /\ in_va_size inp = Sv48
  /\ in_channel_reader inp = true /\ valid_launch inp.
Proof.
  intros inp H. red in H.
  repeat match goal with H' : _ /\ _ |- _ => destruct H' end.
  repeat match goal with |- _ /\ _ => split end; assumption.
Qed.

Section GLinkTop.
#[local] Existing Instance PropExec.fx0.
Variable segs : list Segment.
Variable pc : N.
Variable ph : PhdrInfo.
Variable scfg : SpuriousCfg.
Variable lim : Z.
Variable PayExport : list byte -> Prop.

(* The run reads the binary's segments with the run's vDSO appended ([Run.run_segments], LPS
   727298f3), and its start is pinned by the launch ([Run.valid_launch],
   [Run.entry_launch_ok_va]). *)
Definition plain_norm_stmt : Prop :=
  forall sp brk mbase (rdraw : EntryDraw) (inp : ProcInput),
    valid_sp sp -> valid_brk segs brk -> valid_mmap_base mbase ->
    valid_launch inp -> entry_launch_ok_va Sv48 (mkEntry sp brk mbase rdraw) inp ->
    valid_argv (in_argv inp) -> valid_envp (in_envp inp) -> valid_fs (in_fs inp) -> valid_creds inp ->
    in_channel_reader inp = true ->
    @srealizes bm_on_inst (run_segments segs inp sp mbase) scfg
      (init_config (run_segments segs inp sp mbase) pc ph sp brk mbase rdraw lim inp)
      (BigintSpec.spec (in_argv inp) (in_fs inp)).

Definition plain_g_stmt : Prop :=
  forall sp brk mbase (rdraw : EntryDraw) (inp : ProcInput),
    valid_sp sp -> valid_brk segs brk -> valid_mmap_base mbase ->
    valid_launch inp -> entry_launch_ok_va Sv48 (mkEntry sp brk mbase rdraw) inp ->
    valid_argv (in_argv inp) -> valid_envp (in_envp inp) -> valid_fs (in_fs inp) -> valid_creds inp ->
    in_channel_reader inp = true ->
    ue_reach_ok (fun p => ~ PayExport p) inp ->
    @srealizes bm_on_inst (run_segments segs inp sp mbase) scfg
      (init_config (run_segments segs inp sp mbase) pc ph sp brk mbase rdraw lim inp)
      (spec_k t_nil (in_argv inp) (in_fs inp)).

Hypothesis FS : frm_safe segs.
Hypothesis NORM : plain_norm_stmt.
Hypothesis WEIRD : plain_g_stmt.

Theorem ue_glink :
  forall sp brk mbase (rdraw : EntryDraw) (inp : ProcInput),
    valid_sp sp -> valid_brk segs brk -> valid_mmap_base mbase ->
    valid_launch inp -> entry_launch_ok_va Sv48 (mkEntry sp brk mbase rdraw) inp ->
    valid_argv (in_argv inp) -> valid_envp (in_envp inp) -> valid_fs (in_fs inp) -> valid_creds inp ->
    in_channel_reader inp = true ->
    ~ reaches_budget_refused_cfg (run_segments segs inp sp mbase) scfg
        (init_config (run_segments segs inp sp mbase) pc ph sp brk mbase rdraw lim inp) ->
    ue_reach_ok PayExport inp.
Proof.
  intros sp brk mbase rdraw inp Hsp Hbrk Hmb Hvl Hlau Hva Hve Hvfs Hcr Hrd PREM.
  apply NNPP. intros HnG.
  assert (W : exists a0s path fdata, in_argv inp = [a0s; path] /\ (length path < 4096)%nat /\ path <> [] /\ path <> dot_path
                /\ fs_lookup (in_fs inp) path = Some fdata /\ ue_header_ok fdata /\ ~ PayExport (ue_payload fdata)).
  { apply NNPP. intros HnW. apply HnG. intros a0s path fdata H1 H2 H3 H4 H5 H6.
    apply NNPP. intros HnP. apply HnW. exists a0s, path, fdata.
    exact (conj H1 (conj H2 (conj H3 (conj H4 (conj H5 (conj H6 HnP)))))). }
  destruct W as (a0s & path & fdata & Hargv & Hlen & Hne & Hnd & Hlk & Hhdr & HnP).
  assert (FG : frm_guard (run_segments segs inp sp mbase)
                 (init_config (run_segments segs inp sp mbase) pc ph sp brk mbase rdraw lim inp)).
  { unfold frm_guard. split; [apply SRomStable.frm_safe_run_segments; exact FS | apply FrmInit.init_fz]. }
  assert (WEIRD' : ~ ue_reach_ok PayExport inp ->
                   @srealizes bm_on_inst (run_segments segs inp sp mbase) scfg
                     (init_config (run_segments segs inp sp mbase) pc ph sp brk mbase rdraw lim inp)
                     (spec_k t_nil (in_argv inp) (in_fs inp))).
  { intros _. apply (WEIRD sp brk mbase rdraw inp Hsp Hbrk Hmb Hvl Hlau Hva Hve Hvfs Hcr Hrd).
    intros a0s' path' fdata' H1 H2 H3 H4 H5 H6.
    rewrite Hargv in H1. injection H1 as <- <-. rewrite Hlk in H5. injection H5 as <-. exact HnP. }
  apply HnG.
  apply (glink_core (run_segments segs inp sp mbase) scfg
           (init_config (run_segments segs inp sp mbase) pc ph sp brk mbase rdraw lim inp)
           (BigintSpec.spec (in_argv inp) (in_fs inp)) (spec_k t_nil (in_argv inp) (in_fs inp))
           (ue_reach_ok PayExport inp) FG
           (NORM sp brk mbase rdraw inp Hsp Hbrk Hmb Hvl Hlau Hva Hve Hvfs Hcr Hrd) WEIRD' PREM).
  exists [ev0]. rewrite Hargv.
  exact (shapes_differ a0s path fdata (in_fs inp) Hlen Hne Hnd Hlk Hhdr).
Qed.
End GLinkTop.

(* [comment removed for export] *)
Section Base.
#[local] Existing Instance PropExec.fx0.
Variable ssegs : list Segment. Variable spc : N. Variable sph : PhdrInfo.
Variable tsegs : list Segment. Variable tpc : N. Variable tph : PhdrInfo.
Variable scfg : SpuriousCfg.
Variables lim_s lim_t : Z.
Variable G : list byte -> Prop.

(* The target's walk, over the run's segments.  [valid_input_either] carries the input clauses
   both abort stances share (the launch, the channel reader, the recorded kernel, ...); it is
   discharged from the published binder [valid_input_abort]. *)
Definition tgt_g_stmt : Prop :=
  forall sp brk mbase (rdraw : EntryDraw) (inp : ProcInput),
    valid_sp sp -> valid_brk tsegs brk -> valid_mmap_base mbase ->
    entry_stack_fits sp (in_argv inp) (in_envp inp) ->
    entry_launch_ok_va Sv48 (mkEntry sp brk mbase rdraw) inp -> valid_launch inp ->
    valid_input_either inp ->
    ue_reach_ok G inp ->
    @srealizes bm_off_inst (run_segments tsegs inp sp mbase) scfg
      (init_config (run_segments tsegs inp sp mbase) tpc tph sp brk mbase rdraw lim_t inp)
      (BigintSpec.spec (in_argv inp) (in_fs inp)).

Hypothesis FSs : frm_safe ssegs.
Hypothesis FSt : frm_safe tsegs.
Hypothesis NORM : plain_norm_stmt ssegs spc sph scfg lim_s.
Hypothesis WEIRD : plain_g_stmt ssegs spc sph scfg lim_s G.
Hypothesis TGT : tgt_g_stmt.

Theorem ue_base_abort :
  strong_universal_error_free_T_scfg_budgets_abort scfg lim_s lim_t (mkImage ssegs spc sph) (mkImage tsegs tpc tph).
Proof.
  intros [rsp rbrk rmb rrnd] [asp abrk amb arnd] inp Hens Hent Hvalid Hwb.
  pose proof (valid_input_abort_va_size _ Hvalid) as Hsv48.
  rewrite (valid_entry_sv48 _ _ _ Hsv48) in Hens. rewrite (valid_entry_sv48 _ _ _ Hsv48) in Hent.
  destruct Hens as [Hrsp [Hrbrk [Hrmb [_ Hrlau]]]]. destruct Hent as [Hasp [Habrk [Hamb [Hafit Halau]]]].
  pose proof (valid_input_either_of_valid_input_abort inp Hvalid) as Hvi.
  destruct (vie_parts inp Hvi) as (Hargv & Henvp & Hfs & Hcreds & _ & _ & Hrd & Hvl).
  unfold source_within_budget_scfg, run_scfg_budget_refused in Hwb. cbv beta iota zeta in Hwb.
  pose proof (NORM rsp rbrk rmb rrnd inp Hrsp Hrbrk Hrmb Hvl Hrlau Hargv Henvp Hfs Hcreds Hrd) as SRC.
  pose proof (ue_glink ssegs spc sph scfg lim_s G FSs NORM WEIRD rsp rbrk rmb rrnd inp
                Hrsp Hrbrk Hrmb Hvl Hrlau Hargv Henvp Hfs Hcreds Hrd Hwb) as HG.
  pose proof (TGT asp abrk amb arnd inp Hasp Habrk Hamb Hafit Halau Hvl Hvi HG) as TG.
  pose proof (@srealizes_bm_transfer bm_on_inst _ _ _ _ SRC Hwb) as SRC'.
  assert (FGs : frm_guard (run_segments ssegs inp rsp rmb)
                  (init_config (run_segments ssegs inp rsp rmb) spc sph rsp rbrk rmb rrnd lim_s inp)).
  { unfold frm_guard. split; [apply SRomStable.frm_safe_run_segments; exact FSs | apply FrmInit.init_fz]. }
  assert (FGt : frm_guard (run_segments tsegs inp asp amb)
                  (init_config (run_segments tsegs inp asp amb) tpc tph asp abrk amb arnd lim_t inp)).
  { unfold frm_guard. split; [apply SRomStable.frm_safe_run_segments; exact FSt | apply FrmInit.init_fz]. }
  pose proof (@srealizes0_of bm_off_inst _ _ _ _ FGs SRC') as S0.
  pose proof (@srealizes0_of bm_off_inst _ _ _ _ FGt TG) as T0.
  unfold strong_equiv_error_free_budgets_scfg_abort.
  split; [| split].
  - eapply srealizes_error_free_unkilled; [exact S0 | apply kill_free_spec].
  - eapply srealizes_error_free_unkilled; [exact T0 | apply kill_free_spec].
  - intro tr.
    pose proof (srealizes_traces_iff scfg _ _ _ _ _ _ _ _ _ _ tr S0) as E1.
    pose proof (srealizes_traces_iff scfg _ _ _ _ _ _ _ _ _ _ tr T0) as E2.
    rewrite E1, E2. reflexivity.
Qed.
End Base.
