(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Sem.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Lib Require Import PropExec MState Frame Exec ITree Nodes RegsEquiv. From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.Lib Require Import Image.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW Require Import TopLevel.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.Spec Require Import Prog.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.FO Require Import FOCore.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.World Require Import SrcO_zlib_example_large_fuzzer_repro.
Module SrcP := SrcO_zlib_example_large_fuzzer_repro.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.World Require Import TgtO_example_large_fuzzer_ubsan.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.

(* [comment removed for export] *)
Definition run_ceiling (en : ExecEntry) : Ceiling := ceiling_of_sp (bv_unsigned (en_sp en)).
(* [comment removed for export] *)
Definition the_prog (segs : list Segment) (rstage : Z) : prog_tree (Exc.exc unit) :=
  fun inp en => @prog (run_ceiling en) segs rstage (in_argv inp).
Definition the_post : unit -> machine_state -> Prop := fun _ _ => True.

Record base_obligations : Type := {
  ob_impl_P : forall (en : ExecEntry) (inp : ProcInput),
      valid_entry (mkImage psegs SrcP.M.init_pc SrcP.M.phdrs) en inp ->
      valid_input inp ->
      impl psegs (at_node psegs) (the_prog psegs pstage inp en) (epost the_post)
           (ms0 psegs SrcP.M.init_pc SrcP.M.phdrs en inp)
      /\ leaves_unreachable_m nstep (the_prog psegs pstage inp en) (mo0 psegs source_alloc_limit en inp)
      /\ tsafe nstep nsafe (the_prog psegs pstage inp en) (mo0 psegs source_alloc_limit en inp);

  ob_impl_U : forall (en : ExecEntry) (inp : ProcInput),
      valid_entry (mkImage usegs TgtO_example_large_fuzzer_ubsan.M.init_pc TgtO_example_large_fuzzer_ubsan.M.phdrs) en inp ->
      valid_input inp ->
      impl usegs (at_node usegs) (the_prog usegs ustage inp en) (epost the_post)
           (ms0 usegs TgtO_example_large_fuzzer_ubsan.M.init_pc TgtO_example_large_fuzzer_ubsan.M.phdrs en inp)
      /\ leaves_unreachable_m nstep (the_prog usegs ustage inp en) (mo0 usegs target_alloc_limit en inp)
      /\ tsafe nstep nsafe (the_prog usegs ustage inp en) (mo0 usegs target_alloc_limit en inp);

  ob_equiv : forall (enP enU : ExecEntry) (inp : ProcInput),
      valid_entry (mkImage psegs SrcP.M.init_pc SrcP.M.phdrs) enP inp ->
      valid_entry (mkImage usegs TgtO_example_large_fuzzer_ubsan.M.init_pc TgtO_example_large_fuzzer_ubsan.M.phdrs) enU inp ->
      valid_input inp ->
      trace_equiv (tree_traces (the_prog psegs pstage inp enP) (mo0 psegs source_alloc_limit enP inp))
                  (tree_traces (the_prog usegs ustage inp enU) (mo0 usegs target_alloc_limit enU inp))
}.

(** Forced-only port: the trees describe the filtered run ([TopLevel.run_of_tree]), so the obligations give
    the error-free equivalence at the zlib re-issue's configuration. *)
Theorem base_ubsan_from_obligations :
  base_obligations ->
  strong_universal_error_free_T_scfg alloc_forced_cfg
    (mkImage SrcP.M.loaded_segments SrcP.M.init_pc SrcP.M.phdrs)
    (mkImage TgtO_example_large_fuzzer_ubsan.M.loaded_segments TgtO_example_large_fuzzer_ubsan.M.init_pc TgtO_example_large_fuzzer_ubsan.M.phdrs).
Proof.
  intros [HP HU HE].
  apply (error_free_from_trees (the_prog psegs pstage) (the_prog usegs ustage) the_post the_post).
  - exact HP.
  - exact HU.
  - exact HE.
Qed.

(* [comment removed for export] *)

