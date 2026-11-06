(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase Fs State Monad Specs Run RiscvSemantics MemImageType StackLayout.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.Common Require Import BudgetBridgeCore BudgetBridgeMm BudgetBridgeStep BudgetBridgeRun BudgetBridgeMove BudgetBridgeInvArms.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
From OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib Require TCodec.
Ltac2 tcn__Common_BudgetBridge () := ([""; "Corelib.Init.Datatypes."; "Corelib.Init.Logic."; "Corelib.Numbers.BinNums."; "LinuxProcessSemantics.EquivalenceDefinition.Equivalence."; "LinuxProcessSemantics.EquivalenceDefinition.Equivalence.SanitizerBudgets."; "LinuxProcessSemantics.EquivalenceDefinition.Equivalence.ShippedBudgets."; "LinuxProcessSemantics.LinuxProcessSem.MemImageType."; "LinuxProcessSemantics.LinuxProcessSem.Run."; "LinuxProcessSemantics.LinuxProcessSem.StackLayout."; "LinuxProcessSemantics.LinuxProcessSem.State."; "OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.BudgetBridgeRun."; "OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.Common.BudgetBridgeStep."; "Stdlib.ZArith.BinInt.Z."; "stdpp.bitvector.definitions."], [["1list"; "2and"; "2eq"; "2not"; "3N"; "3Z"; "0L1"; "0L2"; "5lim_source"; "5lim_target"; "6lim_source"; "6lim_target"; "4strong_universal_T_budgets"; "4strong_universal_T_budgets_abort"; "4strong_universal_T_scfg_budgets"; "4strong_universal_T_scfg_budgets_abort"]; ["4strong_universal_error_free_T_budgets"; "4strong_universal_error_free_T_budgets_abort"; "4strong_universal_error_free_T_scfg_budgets"; "4strong_universal_error_free_T_scfg_budgets_abort"; "7Image"; "7PhdrInfo"; "7Segment"; "8ExecEntry"; "8SpuriousCfg"; "8behavior_equiv"; "8config"; "8init_config"; "8run"; "8run_budget_refused"; "8run_scfg"; "8run_scfg_budget_refused"]; ["9EntryDraw"; ":ProcInput"; "0Ls1"; "0Ls2"; "0Lt"; ";okl"; "<liftc"; "0S"; "=le"; "0T"; "0brk0"; "0cfg"; "0en"; "0img"; "0inp"; "0mbase"]; ["0pc"; "0ph"; "0rnd"; "0segs"; "0sp"; ">bv"]]).
Lemma init_config_setlim : ltac2:(TCodec.tc2 tcn__Common_BudgetBridge "Q7'0'F%211'4'E'QEyR0%211'Q0'5'Q1'2'J&Kr:r9r8r7r6r5r4r2r1%:9987654321&Q6r3%=9<;:987614%3261%A3@51pRNC1p@E1p>F1pS6H1pS0J1pRFK1pS:L1pS4Q01pS2Q21pS8Q41").
Proof. reflexivity. Qed.
Lemma init_config_okl : ltac2:(TCodec.tc2 tcn__Common_BudgetBridge "Q6'0'F%211'4'E'QEyR0%211'Q0'5'Q1&Q8r3r2%3221&Q5&Kr;r:r9r8r7r6r5r4%9987654321<%;2>1p0=1pRNB1p@D1p>E1pS6G1pS0I1pRFJ1pS:K1pS4O1pS2Q11pS8Q31").
Proof.
intros. split.
- change (vm_limit (m_vmmaps (cfg_model (init_config segs pc ph sp brk0 mbase rnd L1 inp)))) with L1.
exact H.
- change (vm_maps (m_vmmaps (cfg_model (init_config segs pc ph sp brk0 mbase rnd L1 inp))))
with (@nil (word * word)).
intros a sz [].
Qed.
Theorem run_scfg_budget_bridge : ltac2:(TCodec.tc2 tcn__Common_BudgetBridge "Q3'H'D'5'G'Q1&Q8r4r3%3221&3&Or7r6r5r2%5543281%711'1&I&Nr8%251:9?>%352;9@?%5221%>54=;BA%@11%9231p0;1p0D1pRNI1pRJK1p@M1p>N1pRLQ01pRHQ21").
Proof.
intros cfg [segs pc ph] L1 L2 [sp brk0 mbase rnd] inp Hle Hnr.
unfold run_scfg_budget_refused, run_scfg in *.
set (c0 := init_config segs pc ph sp brk0 mbase rnd L1 inp) in *.
assert (Hn : nref segs cfg c0).
{ intros tr c Hst Hb. apply Hnr. exists tr, c. split; assumption. }
pose proof (init_config_okl segs pc ph sp brk0 mbase rnd L1 L2 inp Hle) as Hl. fold c0 in Hl.
rewrite (init_config_setlim segs pc ph sp brk0 mbase rnd L1 L2 inp). fold c0.
split.
- unfold behavior_equiv. cbn [bh_traces bh_errors bh_all_errors bh_unmodeled].
split; [exact (traces_iff segs cfg L2 move_charge_le bounded_pres c0 Hn Hl)|].
split; [exact (errors_iff segs cfg L2 move_charge_le bounded_pres c0 Hn Hl)|].
split.
+ split.
* intros H. exact (all_errors_fwd segs cfg L2 move_charge_le bounded_pres c0 H Hn Hl).
* intros H. exact (all_errors_bwd segs cfg L2 move_charge_le bounded_pres _ H c0 eq_refl Hn Hl).
+ exact (unmodeled_iff segs cfg L2 move_charge_le bounded_pres c0 Hn Hl).
- intros (tr & c & Hst & Hb). exact (nref_lift segs cfg L2 move_charge_le bounded_pres c0 Hn Hl tr c Hst Hb).
Qed.
Theorem run_budget_bridge : ltac2:(TCodec.tc2 tcn__Common_BudgetBridge "Q0'D'5'G'Q1&Q8r4r3%3221&3&Mr6r5r2%443271%611'1&I&Lr7%2419>=%3429?>%5221%=44;A@%?11%9231p0;1p0C1pRNH1pRJJ1p@L1p>M1pRLO1").
Proof.
intros img L1 L2 en inp Hle Hnr.
assert (Hnr' : ~ run_scfg_budget_refused may_fail_cfg img L1 en inp)
by (rewrite <- run_scfg_budget_refused_may_fail; exact Hnr).
destruct (run_scfg_budget_bridge may_fail_cfg img L1 L2 en inp Hle Hnr') as [BE Hnr2].
split.
- pose proof (run_scfg_may_fail img L1 en inp) as E1.
pose proof (run_scfg_may_fail img L2 en inp) as E2.
destruct E1 as (T1 & R1 & A1 & U1). destruct E2 as (T2 & R2 & A2 & U2).
destruct BE as (T & R & A & U).
split; [intros tr; rewrite <- T1, <- T2; apply T|].
split; [rewrite <- R1, <- R2; exact R|].
split; [rewrite <- A1, <- A2; exact A|].
rewrite <- U1, <- U2; exact U.
- rewrite run_scfg_budget_refused_may_fail. exact Hnr2.
Qed.
Section Shrink.
Variables (Ls1 Ls2 Lt : Z) (S T : Image).
Hypothesis LE : Ls1 <= Ls2.
Theorem sue_budgets_abort_source_shrink_cfg : ltac2:(TCodec.tc2 tcn__Common_BudgetBridge "='H&Cr1vQ3vQ4vQ7vQ9%6554321r2vQ2%9521654p041pRH<1").
Proof.
intros cfg H en_s en_t inp Hs Ht Hv Hb.
destruct (run_scfg_budget_bridge cfg S Ls1 Ls2 en_s inp LE Hb) as [BE Hb2].
destruct (H en_s en_t inp Hs Ht Hv Hb2) as (Hsef & Htef & Htr).
split; [apply (error_free_unkilled_behavior_equiv _ _ BE); exact Hsef|].
split; [exact Htef|].
intros tr. rewrite ((proj1 BE) tr). apply Htr.
Qed.
Theorem sue_budgets_source_shrink_cfg : ltac2:(TCodec.tc2 tcn__Common_BudgetBridge "='H&Br1vQ3vQ4vQ7vQ9%6554321r2vQ2%9521654p041pRH<1").
Proof.
intros cfg H en_s en_t inp Hs Ht Hv Hb.
destruct (run_scfg_budget_bridge cfg S Ls1 Ls2 en_s inp LE Hb) as [BE Hb2].
destruct (H en_s en_t inp Hs Ht Hv Hb2) as (Hsef & Htef & Htr).
split; [apply (error_free_behavior_equiv _ _ BE); exact Hsef|].
split; [exact Htef|].
intros tr. rewrite ((proj1 BE) tr). apply Htr.
Qed.
Theorem su_budgets_source_shrink_cfg : ltac2:(TCodec.tc2 tcn__Common_BudgetBridge "='H&>r1vQ3vQ4vQ7vQ9%6554321r2vQ2%9521654p041pRH<1").
Proof.
intros cfg H en_s en_t inp Hs Ht Hv Hb.
destruct (run_scfg_budget_bridge cfg S Ls1 Ls2 en_s inp LE Hb) as [BE Hb2].
destruct (H en_s en_t inp Hs Ht Hv Hb2) as (Hm & He).
split; [apply (modeled_behavior_equiv _ _ BE); exact Hm|].
apply (equiv_behavior_equiv _ _ _ _ BE (behavior_equiv_refl _)). exact He.
Qed.
Theorem su_budgets_abort_source_shrink_cfg : ltac2:(TCodec.tc2 tcn__Common_BudgetBridge "='H&?r1vQ3vQ4vQ7vQ9%6554321r2vQ2%9521654p041pRH<1").
Proof.
intros cfg H en_s en_t inp Hs Ht Hv Hb.
destruct (run_scfg_budget_bridge cfg S Ls1 Ls2 en_s inp LE Hb) as [BE Hb2].
destruct (H en_s en_t inp Hs Ht Hv Hb2) as (Hm & He).
split; [apply (modeled_behavior_equiv _ _ BE); exact Hm|].
apply (equiv_behavior_equiv _ _ _ _ BE (behavior_equiv_refl _)). exact He.
Qed.
Theorem sue_budgets_abort_source_shrink_run : ltac2:(TCodec.tc2 tcn__Common_BudgetBridge "9&AvQ3vQ4vQ7vQ9%544321vQ2%741543p031").
Proof.
intros H en_s en_t inp Hs Ht Hv Hb.
destruct (run_budget_bridge S Ls1 Ls2 en_s inp LE Hb) as [BE Hb2].
destruct (H en_s en_t inp Hs Ht Hv Hb2) as (Hsef & Htef & Htr).
split; [apply (error_free_unkilled_behavior_equiv _ _ BE); exact Hsef|].
split; [exact Htef|].
intros tr. rewrite ((proj1 BE) tr). apply Htr.
Qed.
Theorem sue_budgets_source_shrink_run : ltac2:(TCodec.tc2 tcn__Common_BudgetBridge "9&@vQ3vQ4vQ7vQ9%544321vQ2%741543p031").
Proof.
intros H en_s en_t inp Hs Ht Hv Hb.
destruct (run_budget_bridge S Ls1 Ls2 en_s inp LE Hb) as [BE Hb2].
destruct (H en_s en_t inp Hs Ht Hv Hb2) as (Hsef & Htef & Htr).
split; [apply (error_free_behavior_equiv _ _ BE); exact Hsef|].
split; [exact Htef|].
intros tr. rewrite ((proj1 BE) tr). apply Htr.
Qed.
Theorem su_budgets_source_shrink_run : ltac2:(TCodec.tc2 tcn__Common_BudgetBridge "9&<vQ3vQ4vQ7vQ9%544321vQ2%741543p031").
Proof.
intros H en_s en_t inp Hs Ht Hv Hb.
destruct (run_budget_bridge S Ls1 Ls2 en_s inp LE Hb) as [BE Hb2].
destruct (H en_s en_t inp Hs Ht Hv Hb2) as (Hm & He).
split; [apply (modeled_behavior_equiv _ _ BE); exact Hm|].
apply (equiv_behavior_equiv _ _ _ _ BE (behavior_equiv_refl _)). exact He.
Qed.
Theorem su_budgets_abort_source_shrink_run : ltac2:(TCodec.tc2 tcn__Common_BudgetBridge "9&=vQ3vQ4vQ7vQ9%544321vQ2%741543p031").
Proof.
intros H en_s en_t inp Hs Ht Hv Hb.
destruct (run_budget_bridge S Ls1 Ls2 en_s inp LE Hb) as [BE Hb2].
destruct (H en_s en_t inp Hs Ht Hv Hb2) as (Hm & He).
split; [apply (modeled_behavior_equiv _ _ BE); exact Hm|].
apply (equiv_behavior_equiv _ _ _ _ BE (behavior_equiv_refl _)). exact He.
Qed.
End Shrink.
Theorem sue_budgets_abort_source_shrink : ltac2:(TCodec.tc2 tcn__Common_BudgetBridge "F'H'5'D&Q8r5r4%3221&Cr7r3r2%4537621r8%6515984p031p091pRD>1pR@?1pR:A1pR8B1pR6C1pRHE1").
Proof. intros cfg Ls1 Ls2 Lt S T LE. exact (sue_budgets_abort_source_shrink_cfg Ls1 Ls2 Lt S T LE cfg). Qed.
Theorem sue_budgets_source_shrink : ltac2:(TCodec.tc2 tcn__Common_BudgetBridge "F'H'5'D&Q8r5r4%3221&Br7r3r2%4537621r8%6515984p031p091pRD>1pR@?1pR:A1pR8B1pR6C1pRHE1").
Proof. intros cfg Ls1 Ls2 Lt S T LE. exact (sue_budgets_source_shrink_cfg Ls1 Ls2 Lt S T LE cfg). Qed.
Theorem su_budgets_abort_source_shrink : ltac2:(TCodec.tc2 tcn__Common_BudgetBridge "F'H'5'D&Q8r5r4%3221&?r7r3r2%4537621r8%6515984p031p091pRD>1pR@?1pR:A1pR8B1pR6C1pRHE1").
Proof. intros cfg Ls1 Ls2 Lt S T LE. exact (su_budgets_abort_source_shrink_cfg Ls1 Ls2 Lt S T LE cfg). Qed.
Theorem su_budgets_source_shrink : ltac2:(TCodec.tc2 tcn__Common_BudgetBridge "F'H'5'D&Q8r5r4%3221&>r7r3r2%4537621r8%6515984p031p091pRD>1pR@?1pR:A1pR8B1pR6C1pRHE1").
Proof. intros cfg Ls1 Ls2 Lt S T LE. exact (su_budgets_source_shrink_cfg Ls1 Ls2 Lt S T LE cfg). Qed.
Lemma sanitizer_le_shipped : ltac2:(TCodec.tc2 tcn__Common_BudgetBridge "4&Q8&8&:%3221").
Proof. pose proof sanitizer_source_budget_is_below_shipped. lia. Qed.
Theorem sue_scfg_abort_shipped_to_sanitizer : ltac2:(TCodec.tc2 tcn__Common_BudgetBridge "A'H'D&Cr3&:&;r2r1%6554321r4&8&9%:532196p051pRD=1pR@>1pRH@1").
Proof.
intros cfg S T H. rewrite sanitizer_budgets_target_is_shipped.
exact (sue_budgets_abort_source_shrink cfg _ _ _ S T sanitizer_le_shipped H).
Qed.
