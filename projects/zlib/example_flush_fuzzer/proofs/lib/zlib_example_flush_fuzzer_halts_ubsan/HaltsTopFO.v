(** * HaltsTopFO — [HaltsTop] over the filtered run (forced-only port)

    The bundle's [HaltsTop] turns a node tree's facts into [MustExit.must_exit_in] through the
    unfiltered [Nodes.nodes_sound]; since the port the node relation is sound for
    [Run.sstep_cfg alloc_forced_cfg] instead ([Nodes.nodes_sound_fo]), and the same three facts give
    [MustExit.must_exit_in_scfg alloc_forced_cfg] through [ITreeFO.impl_run_must_exit2_cfg], with no
    budget premise ([FOCore.halts_core]). *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence MustExit HaltsAllowed.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Sem.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.Lib Require Import PropExec MState Frame Exec ITree Nodes RegsEquiv.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.Lib Require Import ITreeFO RegsEquivFO.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan Require Import TopLevel.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.FO Require Import FOCore.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Lemma nexit_any_exit_fo : forall n mo1 code mo2,
  nexit n mo1 code mo2 -> In code AnyExit.codes.
Proof.
  intros n mo1 code mo2 H. destruct n; cbn [nexit] in H; try contradiction.
  destruct H as [-> _]. apply any_exit_covers.
Qed.

(* at
   [must_exit_in_scfg] reads the run's list [run_segments segs inp sp mbase] = [segs ++ vdso_segments ..].
   The tree stays over [segs] and is carried to the run's list by TopLevel's [impl_lift] (the vDSO pair is never
   executable: [vdso_nonexec]); the model is still [mo0] (the run list reserves what [segs] reserves:
   [run_segments_reserved]).  NEW PREMISE: the launch's channel reader, which [mo0_minv] needs;
   [halts_core_of_trees] discharges it from [valid_input] by Run's [valid_input_channel_reader]. *)
Theorem must_exit_in_scfg_of_tree : forall {R : Type} segs pc ph lim (t : itree node R)
    (Q : R -> machine_state -> Prop) en inp (S : list word),
  valid_entry (mkImage segs pc ph) en inp ->
  in_va_size inp = Sv48 ->
  in_channel_reader inp = true ->
  impl segs (at_node segs) t Q (ms0 segs pc ph en inp) ->
  leaves_unreachable_m nstep t (mo0 segs lim en inp) ->
  tsafe nstep nsafe t (mo0 segs lim en inp) ->
  (forall n mo1 code mo2, nexit n mo1 code mo2 -> In code S) ->
  must_exit_in_scfg alloc_forced_cfg S (mkImage segs pc ph) lim en inp.
Proof.
  intros R segs pc ph lim t Q en inp S Hve Hsv48 Hrdr Himpl Hleaves Hsafe HS.
  pose proof (mo0_minv segs pc ph lim en inp Hve Hsv48 Hrdr) as Hminv.
  destruct en as [sp brk mb dr]. cbn [must_exit_in_scfg]. cbv zeta.
  assert (EC : init_config (run_segments segs inp sp mb) pc ph sp brk mb dr lim inp
               = mkCfg (init_machine_state (run_segments segs inp sp mb) pc ph sp mb dr inp)
                       (mo0 segs lim (mkEntry sp brk mb dr) inp)).
  { unfold init_config, mo0. rewrite run_segments_reserved. reflexivity. }
  rewrite EC. clear EC.
  unfold run_segments.
  apply must_exit_in_at_cfg_init_ms.
  pose proof (impl_lift segs (vdso_segments (in_kernel inp) sp mb) t Q (ms0 segs pc ph (mkEntry sp brk mb dr) inp)
                (vdso_nonexec _ _ _) Himpl) as Himpl'.
  rewrite set_rom_ms0 in Himpl'. cbn [en_sp en_mmap_base en_draw] in Himpl'.
  exact (impl_run_must_exit2_cfg alloc_forced_cfg node (segs ++ vdso_segments (in_kernel inp) sp mb)
           (at_node (segs ++ vdso_segments (in_kernel inp) sp mb)) nstep nexit minv nsafe
           (nodes_sound_fo (segs ++ vdso_segments (in_kernel inp) sp mb)) S t _ _ _ Himpl' Hleaves
           (mo0_not_halted _ _ _ _) Hminv Hsafe HS).
Qed.

(** The core claim (halting under the forced-only configuration, no budget premise) from tree facts at
    every valid entry and input. *)
Theorem halts_core_of_trees : forall {R : Type} segs pc ph (t : ProcInput -> ExecEntry -> itree node R)
    (Q : R -> machine_state -> Prop) (S : list word),
  (forall n mo1 code mo2, nexit n mo1 code mo2 -> In code S) ->
  (forall en inp, valid_entry (mkImage segs pc ph) en inp -> valid_input inp ->
      impl segs (at_node segs) (t inp en) Q (ms0 segs pc ph en inp)
      /\ leaves_unreachable_m nstep (t inp en) (mo0 segs source_alloc_limit en inp)
      /\ tsafe nstep nsafe (t inp en) (mo0 segs source_alloc_limit en inp)) ->
  halts_core alloc_forced_cfg source_alloc_limit S (mkImage segs pc ph).
Proof.
  intros R segs pc ph t Q S HS Hok en inp Hve Hvi.
  destruct (Hok en inp Hve Hvi) as (Himpl & Hleaves & Hsafe).
  exact (must_exit_in_scfg_of_tree segs pc ph source_alloc_limit (t inp en) Q en inp S Hve
           (valid_input_va_size _ Hvi) (valid_input_channel_reader _ Hvi) Himpl Hleaves Hsafe HS).
Qed.
