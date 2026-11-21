(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: whole copy of projects/jsoncons/fuzz_ubjson_parser_max/proofs/lib/Common/MustExitHalts.v at theorem-labs/oss-verify-proofs@c5665593c2d8, with OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib renamed to OSSVerify.Proofs.jsoncons.fuzz_bigint.lib and its Common.MustExit* requires renamed to Corpus.Corpus*. *)
(* Modified by Theorem Labs, 2026-11: taken from ossv175b/bigint at b5b2fc487168 and adapted to this tree's srz_spin, which carries spin_site_present segs (see Corpus/CorpusSpin.v). halts_of_srealizes_top gains the premise ~ spin_site_present segs between its budget bound and its exits_in hypothesis, and passes it to srealizes_must_exit_init; halts_of_srealizes_top' gains the same premise, stated on an Image as match img with mkImage segs _ _ => ~ spin_site_present segs end. Nothing else in the file changes. *)
(* Modified by Theorem Labs, 2026-11: for LPS 727298f3, srealizes_top is stated over the run's segment list (run_segments) and takes the launch facts and the channel reader, the spin premise becomes spin_site_present segs -> sc_alloc cfgF = true -> False (Corpus/CorpusSpin.v), srealizes_top_either and halts_of_srealizes_top_either take valid_input_either's clauses read by type, with halts_of_srealizes_top their corollary, in the shape of srealizes_must_exit_init, lines 140-153 of projects/jsoncons/fuzz_json_cursor/proofs/lib/HaltsBridge.v as in the LPS 727298f3 update, and the cited source commit is named by its public id. *)
From Stdlib Require Import ZArith NArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase Fs State Monad Specs Run RiscvSemantics MemImageType StackLayout.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence MustExit HaltsAllowed.
From OSSVerify.Proofs.jsoncons.fuzz_bigint.lib Require Import ShapeAlg SpinAlg.
From OSSVerify.Proofs.jsoncons.fuzz_bigint.lib.Corpus Require Import CorpusShape CorpusSpin CorpusCfg CorpusBudget.
From OSSVerify.Proofs.jsoncons.fuzz_bigint.lib.Common.Cfg Require SRomStable.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Definition srealizes_top (segs : list Segment) (cfgF : SpuriousCfg) (pc : N) (ph : PhdrInfo) (LIM : Z)
(T : ProcInput -> TSet) : Prop :=
forall sp brk mbase (rdraw : EntryDraw) (inp : ProcInput),
valid_sp sp -> valid_brk segs brk -> valid_mmap_base mbase ->
entry_stack_fits sp (in_argv inp) (in_envp inp) ->
valid_launch inp -> entry_launch_ok_va Sv48 (mkEntry sp brk mbase rdraw) inp -> in_channel_reader inp = true ->
valid_argv (in_argv inp) -> valid_envp (in_envp inp) -> valid_fs (in_fs inp) -> valid_creds inp ->
valid_hwcap (in_hwcap inp) -> in_va_size inp = Sv48 ->
srealizes (run_segments segs inp sp mbase) cfgF
  (init_config (run_segments segs inp sp mbase) pc ph sp brk mbase rdraw LIM inp) (T inp).
(* The ASan target facts ([BigintTopA.as0_tgt_stmt], [BigintTopAB0.as0_tgt_stmt]) read the
   input through [valid_input_either], the clauses [valid_input] and [valid_input_abort] share;
   [srealizes_top_either] is [srealizes_top] with that binder, in that order. *)
Definition srealizes_top_either (segs : list Segment) (cfgF : SpuriousCfg) (pc : N) (ph : PhdrInfo) (LIM : Z)
(T : ProcInput -> TSet) : Prop :=
forall sp brk mbase (rdraw : EntryDraw) (inp : ProcInput),
valid_sp sp -> valid_brk segs brk -> valid_mmap_base mbase ->
entry_stack_fits sp (in_argv inp) (in_envp inp) ->
entry_launch_ok_va Sv48 (mkEntry sp brk mbase rdraw) inp -> valid_launch inp ->
valid_input_either inp ->
srealizes (run_segments segs inp sp mbase) cfgF
  (init_config (run_segments segs inp sp mbase) pc ph sp brk mbase rdraw LIM inp) (T inp).
(* [valid_input_either]'s clauses read by type, as [Run.valid_input_either_of_valid_input] does. *)
Lemma srealizes_top_either_of_top : forall segs cfgF pc ph LIM T,
srealizes_top segs cfgF pc ph LIM T -> srealizes_top_either segs cfgF pc ph LIM T.
Proof.
intros segs cfgF pc ph LIM T TOP sp brk mbase rdraw inp Hsp Hbrk Hmb Hfit Hlau Hvl Hvi.
red in Hvi. repeat match goal with G : _ /\ _ |- _ => destruct G end.
unfold srealizes_top in TOP. apply TOP; assumption.
Qed.
(* [Hns] is the premise [srz_spin] now needs: see Corpus/CorpusSpin.v. *)
Theorem halts_of_srealizes_top_either : forall segs cfgF pc ph LIM (S : list word) (T : ProcInput -> TSet),
ShippedBudgets.lim_source <= LIM ->
(spin_site_present segs -> sc_alloc cfgF = true -> False) ->
(forall inp, exits_in S (T inp)) ->
srealizes_top_either segs cfgF pc ph LIM T ->
halts_allowed_T_scfg_budgets forced_only_cfg ShippedBudgets.lim_source S (mkImage segs pc ph).
Proof.
intros segs cfgF pc ph LIM S T Hle Hns HX TOP [sp brk mbase rdraw] inp Hen Hvalid Hwb.
pose proof (valid_input_va_size _ Hvalid) as Hsv48.
pose proof (valid_input_launch _ Hvalid) as Hvl.
rewrite (valid_entry_sv48 _ _ _ Hsv48) in Hen. destruct Hen as [Hsp [Hbrk [Hmb [Hfit Hlau]]]].
assert (M2 : must_exit_in_scfg cfgF S (mkImage segs pc ph) LIM (mkEntry sp brk mbase rdraw) inp).
{ cbn [must_exit_in_scfg].
apply (srealizes_must_exit_init (run_segments segs inp sp mbase) cfgF S pc ph sp brk mbase rdraw LIM inp (T inp)).
- exact (TOP sp brk mbase rdraw inp Hsp Hbrk Hmb Hfit Hlau Hvl (valid_input_either_of_valid_input _ Hvalid)).
- intros Hsite Hal. exact (Hns (SRomStable.spin_site_run_segments segs inp sp mbase Hsite) Hal).
- exact (HX inp). }
apply (must_exit_in_scfg_budget_transfer forced_only_cfg S (mkImage segs pc ph) ShippedBudgets.lim_source LIM
(mkEntry sp brk mbase rdraw) inp Hle).
- exact (must_exit_in_scfg_forced_only cfgF S _ LIM _ inp M2).
- exact Hwb.
Qed.
Theorem halts_of_srealizes_top : forall segs cfgF pc ph LIM (S : list word) (T : ProcInput -> TSet),
ShippedBudgets.lim_source <= LIM ->
(spin_site_present segs -> sc_alloc cfgF = true -> False) ->
(forall inp, exits_in S (T inp)) ->
srealizes_top segs cfgF pc ph LIM T ->
halts_allowed_T_scfg_budgets forced_only_cfg ShippedBudgets.lim_source S (mkImage segs pc ph).
Proof.
intros segs cfgF pc ph LIM S T Hle Hns HX TOP.
exact (halts_of_srealizes_top_either segs cfgF pc ph LIM S T Hle Hns HX (srealizes_top_either_of_top segs cfgF pc ph LIM T TOP)).
Qed.
Corollary halts_of_srealizes_top' : forall (img : Image) cfgF LIM (S : list word) (T : ProcInput -> TSet),
ShippedBudgets.lim_source <= LIM ->
match img with mkImage segs _ _ => spin_site_present segs -> sc_alloc cfgF = true -> False end ->
(forall inp, exits_in S (T inp)) ->
match img with mkImage segs pc ph => srealizes_top segs cfgF pc ph LIM T end ->
halts_allowed_T_scfg_budgets forced_only_cfg ShippedBudgets.lim_source S img.
Proof.
intros [segs pc ph] cfgF LIM S T Hle Hns HX TOP. exact (halts_of_srealizes_top segs cfgF pc ph LIM S T Hle Hns HX TOP).
Qed.
Lemma lim_source_le_source : ShippedBudgets.lim_source <= source_alloc_limit.
Proof. unfold ShippedBudgets.lim_source. lia. Qed.
Lemma lim_source_le_target : ShippedBudgets.lim_source <= target_alloc_limit.
Proof. unfold ShippedBudgets.lim_source, source_alloc_limit, target_alloc_limit. lia. Qed.
