(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3: some recorded proofs replaced by tactic proofs; the new launch (process input, auxv, group id, exec file name); the BMode context. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require BvWfKernel.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.jsoncons.fuzz_ubjson_encoder.images Require Import Plain.
From OSSVerify.jsoncons.fuzz_ubjson_encoder.images Require Import Ubsan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require Import BMode ShapeAlg SpinAlg HeapIface LibIface LibIfaceE L5Defs
     UbjEncShapes UbjEncGLink FrmInit Es0DrvLibL Es0DrvG Es0DrvMain Es0HeapBridgeHe Eu0DrvLibL Eu0DrvG Eu0DrvMain Eu0HeapBridgeHe
     PeCSink PeCTopS PeCTopU PeCSExitCells PeCUExitCells.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.Heap Require Import HeIface HeInst0 HeInst1 HeV16.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.Spec Require Import UbjRef UbjRefFacts.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require PropExec.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require KReplay.
Ltac2 kr_t_UbjEncPmStated () := "K47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1Z02K47Corelib7Numbers7BinNums8positive01C56Stdlib6ZArith6BinInt1Z>pow_pos_nonnegC56Stdlib6ZArith6BinInt1Z2ltC56Stdlib6ZArith6BinInt1Z3powC56Stdlib6ZArith6BinInt1Z:pow_nonnegC56Stdlib6ZArith6BinInt1Z7compareK47Corelib4Init5Logic2eq01K47Corelib4Init9Datatypes4list01I47Corelib4Init9Datatypes4list00K46Stdlib9micromega6VarMap1t01I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr01K47Corelib7Numbers7BinNums1N02K46Stdlib9micromega7EnvRing5PExpr07K46Stdlib9micromega7EnvRing5PExpr05K46Stdlib9micromega=RingMicromega7Formula01K46Stdlib9micromega5Tauto8GFormula05C46Stdlib9micromega5Tauto8BFormulaC46Stdlib9micromega:ZMicromega=ZTautoCheckerI47Corelib4Init5Logic2eq00C46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundC56Stdlib6ZArith6BinInt1Z3mulC56Stdlib6ZArith6BinInt1Z2leI47Corelib4Init5Logic3and00K46Stdlib9micromega5Tauto8GFormula04K47Corelib7Numbers7BinNums1Z01C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K47Corelib4Init9Datatypes4unit01K47Corelib7Numbers7BinNums8positive03I47Corelib4Init5Logic4True00I47Corelib4Init9Datatypes:comparison00I46Stdlib9micromega:ZMicromega;ZArithProof00I47Corelib7Numbers7BinNums1Z00K46Stdlib9micromega=RingMicromega3Op203I47Corelib4Init9Datatypes4bool00K47Corelib4Init9Datatypes4bool01c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib>UbjEncPmStated3tbSC13~~~C47Corelib4Init5Logic6eq_indC47Corelib4Init5Logic9False_indK47Corelib4Init5Logic3and01C56Stdlib6ZArith6BinInt1Z3addC56Stdlib6ZArith6BinInt1Z3divC56Stdlib6ZArith6BinInt1Z3maxK47Corelib4Init9Datatypes:comparison02K47Corelib4Init9Datatypes:comparison03I47Corelib4Init5Logic5False00K47Corelib4Init5Logic4True01c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib>UbjEncPmStated3tbUC13~~~C4ELinuxProcessSemantics?LinuxProcessSem3Run8sc_allocC4ELinuxProcessSemantics?LinuxProcessSem3Run5sc_fsI45stdpp9bitvector;definitions2bv00C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib5BMode5bm_onC13~~~K47Corelib4Init5Logic2or01C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib?Es0HeapBridgeHeGsrc0_realizes_spec_heapC13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib>UbjEncPmStated4cfg0C13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib5BMode:bm_on_instC13~~~C5ELinuxProcessSemanticsEEquivalenceDefinition;Equivalence>ShippedBudgets:lim_sourcec79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib>UbjEncPmStated4LaySC13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib>UbjEncPmStated4LStSC13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib>UbjEncPmStated4DLLSC13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib>UbjEncPmStated3G_UC13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib>UbjEncPmStated4LSXSC13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib>UbjEncPmStated7BudgetSC13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib?Es0HeapBridgeHeDsrc0_realizes_G_heapC13~~~C5ELinuxProcessSemanticsEEquivalenceDefinition;Equivalence>ShippedBudgets:lim_targetC4ELinuxProcessSemantics?LinuxProcessSem3Run8valid_spC4ELinuxProcessSemantics?LinuxProcessSem3Run9valid_brkC4ELinuxProcessSemantics?LinuxProcessSem3Run?valid_mmap_baseC4ELinuxProcessSemantics?LinuxProcessSem5State7in_argvC4ELinuxProcessSemantics?LinuxProcessSem5State7in_envpC4ELinuxProcessSemantics?LinuxProcessSem3Run@entry_stack_fitsC4ELinuxProcessSemantics?LinuxProcessSem3Run:valid_argvC4ELinuxProcessSemantics?LinuxProcessSem3Run:valid_envpC4ELinuxProcessSemantics?LinuxProcessSem5State5in_fsC4ELinuxProcessSemantics?LinuxProcessSem2Fs8valid_fsC4ELinuxProcessSemantics?LinuxProcessSem3Run;valid_credsC4ELinuxProcessSemantics?LinuxProcessSem5State8in_hwcapC4ELinuxProcessSemantics?LinuxProcessSem3Run;valid_hwcapC4ELinuxProcessSemantics?LinuxProcessSem5State:in_va_sizeC79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib<UbjEncShapes;ue_reach_okC13~~~C47Corelib4Init5Logic8eq_ind_rK47Corelib4Init5Logic2or02C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib;UbjEncGLink:tgt_g_stmtC13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib?Eu0HeapBridgeHeGub0_realizes_spec_heapXC13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib5BMode;bm_off_instC13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib>UbjEncPmStated4LayUC13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib>UbjEncPmStated4LStUC13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib>UbjEncPmStated4DLLUC13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib>UbjEncPmStated4LSXUC13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib>UbjEncPmStated7BudgetUC13~~~I4ELinuxProcessSemantics?LinuxProcessSem;StackLayout9EntryDraw00I4ELinuxProcessSemantics?LinuxProcessSem5State9ProcInput00c89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib>UbjEncPmStated2EU?loaded_segmentsC13~~~I4ELinuxProcessSemantics?LinuxProcessSem5State6VaSize00K4ELinuxProcessSemantics?LinuxProcessSem5State6VaSize02c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib>UbjEncPmStated>lim_target_valC13~~~c89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib>UbjEncPmStated2EU7init_pcC13~~~c89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib>UbjEncPmStated2EU5phdrsC13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib;UbjEncGLink=ue_base_abortC13~~~c89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib>UbjEncPmStated2ES?loaded_segmentsC13~~~c89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib>UbjEncPmStated2ES7init_pcC13~~~c89OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib>UbjEncPmStated2ES5phdrsC13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib7FrmInit<frm_safe_Ms0C13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib7FrmInit<frm_safe_Mu0C13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib>UbjEncPmStated6norm_SC13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib>UbjEncPmStated7weird_SC13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib>UbjEncPmStated5tgt_UC13~~~".
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
Definition cfg0 : SpuriousCfg := mkSpuriousCfg false true true true true true.

(* [comment removed for export] *)
Definition GB_U : Z := 2 ^ 33.
Definition G_U (p : list byte) : Prop := UbjRefFacts.F (map bv_unsigned p) <= GB_U.

Module ES := Plain.M.
Module EU := Ubsan.M.

Section UbsanBaseStated.
#[local] Existing Instance PropExec.fx0.

(* [comment removed for export] *)
Definition tbS : Z := PECTS.TOPB0.                                            (* [comment removed for export] *)
Definition tbU : Z := PECTU.TOPB0 + (cszR (2 ^ 33) + cszR (2 ^ 34)).          (* [comment removed for export] *)
Definition LayS (sp : word) : lib_layout := PECTS.TopLay (HeInst0.L0 (bv_unsigned sp)) tbS.
Definition LayU (sp : word) : lib_layout := PECTU.TopLay (HeInst1.L1 (bv_unsigned sp)) tbU.
Definition LStS (_ : word) : lib_statics := PECTS.TopLS.
Definition LStU (_ : word) : lib_statics := PECTU.TopLS.
Lemma tbS_range : 0 <= tbS <= 2 ^ 36.
Proof.
ltac2:(KReplay.run1 (kr_t_UbjEncPmStated ()) ["UbsanBaseStated"] "h02Hah16__sat1h26__sat3h37__arithh44__ffh56__sat0h66__sat2h78__varmaph85__witp;1p;2p;3p;4p;7g0000j11Tg000Uj14Tg0013j12Tg001Xj27Tg002@j26Tg002\j2:Tg0039j3<Tg003]j2DTg004>j2>Tg004Xj1BTg0058j1ATg005Xj1@Tg0066j1NTg006Tj1MTg007?j25Tg007bj1?Tg008@j38Tg008cj3LTg009Fj4=Tg00:1j7KTg00:Uj2JTg00;7j2ITg00;cj3HTg00<=j3ETg00<\j4FTg00=Nj2GTg00=kj23Tg00>Gj29Tg00>bj7CTg00?FR0f0R1'3p=0f1R2g00?dR3g00@CR4P4g00@cR5P1g00ACFCp=;g00AcR6#1R7#4R8%17#2#1#1R7#4R9'71608R:%091:89R;,60[R<[%08R=g00BHR>A<892UW0%0;\>^0=%26R6#2#2#1R9#4R?,78%0?1:8?R@,60[RA\:A<8?2V>X0=%0@\>^0=P2g00Bd1D08'>P:eR:O1PAf4P:O1P<g00CJR<#B%A<g00D6R<#@%N<%M<R:P3P4P4P5P<15<0g00DTR4%46R6,5<15<8R8%?958<5L<R9C=,;:P<P9P4%?798<8C=,;:FK1J:5P1f2R:g00E;R5g00E[R8'>1I1:=H58dAE<02CFb4b7b81G6@R6#0136;'9P1b3b2b1b5b1b6b2g00F;R1,30131;'9eo"). Qed.
Lemma tbU_range : 0 <= tbU <= 2 ^ 36.
Proof.
ltac2:(KReplay.run1 (kr_t_UbjEncPmStated ()) ["UbsanBaseStated"] "p'0h01xh11Hh21ei001cp;3p;6p;2p;4p;1g00;cj3?Tg00GHj6>Tg00Gdj2=Tg00HCj4<Tg0013j12Tg000Uj10Tg0000j11Tg002\j25Tg00=Nj28Tg00H^j24Tg00I;j29Tg00IXj2;Tg00=kj27Tg00>Gj2:Tf0R0#2#2p=6%10#1p=3g00BdR1g00J5R2g00J[R33?R4g00KAR5]0R6P6P1P2P1p-0P0P5g00BHP5n011000003000000X21g00K^P3P0E>P51=50b1X04R4P4C<g00?FR4g00AcR5#2R0#0%15R5#0R3%60R0#1#0'5'8%25#3#0R1,53R2%15R5#1R6#1R7#2#0,53/41%60#6#6#6#0R0'4%37#3#3#3#0R7'9/87';%26#1#0,53/41/40/97/87,;2'4'4R2'7%25#3#0,53R3,72':dg00L:R2,741723':eo"). Qed.
Definition DLLS := PECTS.drv_lib_layout_top tbS (proj1 tbS_range).
Definition DLLU := PECTU.drv_lib_layout_top tbU (proj1 tbU_range).
Definition LSXS (sp : word) (_ : valid_sp sp) := PECSXC.top_lsx.
Definition LSXU (sp : word) (_ : valid_sp sp) := PECUXC.top_lsx.
Definition BudgetS := PECTS.budget_top tbS tbS_range.
Definition BudgetU := PECTU.budget_top tbU tbU_range.

(* [comment removed for export] *)
(* [comment removed for export] *)
Hypothesis LIBS : forall sp, valid_sp sp ->
  @lib_iface_ok_x (LayS sp) cfg0 bm_on_inst (@HeV16.HIV0 bm_on_inst (bv_unsigned sp) ShippedBudgets.lim_source) (LStS sp) (fun _ => True) G_U.
(* [comment removed for export] *)
Hypothesis LIBU : forall sp, valid_sp sp ->
  @lib_iface_ok_x (LayU sp) cfg0 bm_off_inst (@HeV16.HIV1 bm_off_inst (bv_unsigned sp) ShippedBudgets.lim_target) (LStU sp) G_U (fun _ => True).

(* [comment removed for export] *)
Lemma norm_S : @plain_norm_stmt ES.loaded_segments ES.init_pc ES.phdrs cfg0 ShippedBudgets.lim_source.
Proof.
  exact (src0_realizes_spec_heap (bmK := bm_on_inst) cfg0 eq_refl eq_refl ShippedBudgets.lim_source LayS LStS DLLS
           (fun _ => True) G_U LIBS LSXS BudgetS (or_introl eq_refl) (fun _ => I)).
Qed.

Lemma weird_S : @plain_g_stmt ES.loaded_segments ES.init_pc ES.phdrs cfg0 ShippedBudgets.lim_source G_U.
Proof.
  exact (src0_realizes_G_heap (bmK := bm_on_inst) cfg0 eq_refl eq_refl ShippedBudgets.lim_source LayS LStS DLLS
           (fun _ => True) G_U LIBS LSXS BudgetS (or_introl eq_refl) (fun _ => I)).
Qed.

Lemma lim_target_val : ShippedBudgets.lim_target = 2 ^ 39.
Proof.
ltac2:(KReplay.run1 (kr_t_UbjEncPmStated ()) ["UbsanBaseStated"] "p;1p;2p;3g0000j10Tg000Uj12Tg004>j26Tg0013j13Tg002\j25Tg00;cj34Tf0R0#0#0#0#0p=7%00#0#0#0#0#0#0#0p=1g00D6R0g00Ac#0R1#0R2#0#7#1#1#1#1#2'6g00_5%21%32#3#3#2'5540do"). Qed.

Lemma tgt_U : @tgt_g_stmt EU.loaded_segments EU.init_pc EU.phdrs cfg0 ShippedBudgets.lim_target G_U.
Proof.
  intros sp brk mbase rdraw inp Hsp Hbrk Hmb _ Hlau Hvl Hvi HG.
  destruct (vie_parts inp Hvi) as (Hva & Hve & Hvfs & Hcr & _ & _ & Hrd & _).
  exact (ub0_realizes_spec_heapX (bmK := bm_off_inst) cfg0 eq_refl eq_refl ShippedBudgets.lim_target LayU LStU DLLU
           G_U (fun _ => True) LIBU LSXU BudgetU (or_intror (Z.eq_le_incl _ _ (eq_sym lim_target_val)))
           sp brk mbase rdraw inp Hsp Hbrk Hmb Hvl Hlau Hva Hve Hvfs Hcr Hrd HG).
Qed.

(* [comment removed for export] *)
Theorem ue_ubsan_base_stated :
  strong_universal_error_free_T_scfg_budgets_abort cfg0 ShippedBudgets.lim_source ShippedBudgets.lim_target
    (mkImage ES.loaded_segments ES.init_pc ES.phdrs) (mkImage EU.loaded_segments EU.init_pc EU.phdrs).
Proof.
  exact (ue_base_abort ES.loaded_segments ES.init_pc ES.phdrs EU.loaded_segments EU.init_pc EU.phdrs cfg0
           ShippedBudgets.lim_source ShippedBudgets.lim_target G_U frm_safe_Ms0 frm_safe_Mu0 norm_S weird_S tgt_U).
Qed.
End UbsanBaseStated.
