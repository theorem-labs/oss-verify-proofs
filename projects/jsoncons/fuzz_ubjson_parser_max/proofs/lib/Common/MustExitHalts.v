(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
From Stdlib Require Import ZArith NArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase Fs State Monad Specs Run RiscvSemantics MemImageType StackLayout.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence MustExit HaltsAllowed.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import ShapeAlg SpinAlg.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.Common Require Import MustExitOfShape MustExitOfSpin MustExitCfg MustExitBudget.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Definition srealizes_top (segs : list Segment) (cfgF : SpuriousCfg) (pc : N) (ph : PhdrInfo) (LIM : Z)
(T : ProcInput -> TSet) : Prop :=
forall sp brk mbase (rdraw : EntryDraw) (inp : ProcInput),
valid_sp sp -> valid_brk segs brk -> valid_mmap_base mbase ->
entry_stack_fits sp (in_argv inp) (in_envp inp) ->
valid_argv (in_argv inp) -> valid_envp (in_envp inp) -> valid_fs (in_fs inp) -> valid_creds inp ->
valid_hwcap (in_hwcap inp) -> in_va_size inp = Sv48 ->
srealizes segs cfgF (init_config segs pc ph sp brk mbase rdraw LIM inp) (T inp).
Theorem halts_of_srealizes_top : forall segs cfgF pc ph LIM (S : list word) (T : ProcInput -> TSet),
ShippedBudgets.lim_source <= LIM ->
(forall inp, exits_in S (T inp)) ->
srealizes_top segs cfgF pc ph LIM T ->
halts_allowed_T_scfg_budgets forced_only_cfg ShippedBudgets.lim_source S (mkImage segs pc ph).
Proof.
intros segs cfgF pc ph LIM S T Hle HX TOP [sp brk mbase rdraw] inp Hen Hvalid Hwb.
pose proof Hvalid as Hvalid'.
destruct Hvalid as (Hargv & Henvp & Hfs & Hrel & Hcreds & Hnofile & Hsigmask & Hhw & Habrt & Hsv48 & _).
rewrite (valid_entry_sv48 _ _ _ Hsv48) in Hen. destruct Hen as [Hsp [Hbrk [Hmb Hfit]]].
assert (M2 : must_exit_in_scfg cfgF S (mkImage segs pc ph) LIM (mkEntry sp brk mbase rdraw) inp).
{ cbn [must_exit_in_scfg].
apply (srealizes_must_exit_init segs cfgF S pc ph sp brk mbase rdraw LIM inp (T inp)).
- exact (TOP sp brk mbase rdraw inp Hsp Hbrk Hmb Hfit Hargv Henvp Hfs Hcreds Hhw Hsv48).
- exact (HX inp). }
apply (must_exit_in_scfg_budget_transfer forced_only_cfg S (mkImage segs pc ph) ShippedBudgets.lim_source LIM
(mkEntry sp brk mbase rdraw) inp Hle).
- exact (must_exit_in_scfg_forced_only cfgF S _ LIM _ inp M2).
- exact Hwb.
Qed.
Corollary halts_of_srealizes_top' : forall (img : Image) cfgF LIM (S : list word) (T : ProcInput -> TSet),
ShippedBudgets.lim_source <= LIM ->
(forall inp, exits_in S (T inp)) ->
match img with mkImage segs pc ph => srealizes_top segs cfgF pc ph LIM T end ->
halts_allowed_T_scfg_budgets forced_only_cfg ShippedBudgets.lim_source S img.
Proof.
intros [segs pc ph] cfgF LIM S T Hle HX TOP. exact (halts_of_srealizes_top segs cfgF pc ph LIM S T Hle HX TOP).
Qed.
Lemma lim_source_le_source : ShippedBudgets.lim_source <= source_alloc_limit.
Proof. unfold ShippedBudgets.lim_source. lia. Qed.
Lemma lim_source_le_target : ShippedBudgets.lim_source <= target_alloc_limit.
Proof. unfold ShippedBudgets.lim_source, source_alloc_limit, target_alloc_limit. lia. Qed.
