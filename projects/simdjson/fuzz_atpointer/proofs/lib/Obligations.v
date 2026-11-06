(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Sem.
From OSSVerify.Proofs.simdjson.fuzz_atpointer.lib.Lib Require Import Zg2 MState Frame Exec ITree Nodes Zp3 Image.
From OSSVerify.Proofs.simdjson.fuzz_atpointer.lib Require Import TopLevel.
From OSSVerify.Proofs.simdjson.fuzz_atpointer.lib.Spec Require Import Prog.
From OSSVerify.simdjson.fuzz_atpointer.images Require Import Plain.
Module SrcP := Plain.
From OSSVerify.simdjson.fuzz_atpointer.images Require Import Ubsan.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.

Definition run_ceiling (en : ExecEntry) : Ceiling := ceiling_of_sp (bv_unsigned (en_sp en)).

Definition the_prog (segs : list Segment) (rstage : Z) : prog_tree (Exc.exc unit) :=
  fun inp en => @prog (run_ceiling en) segs rstage (in_argv inp).
Definition the_post : unit -> machine_state -> Prop := fun _ _ => True.

Record base_obligations : Type := {
  ob_impl_P : forall (en : ExecEntry) (inp : ProcInput),
      valid_entry (mkImage psegs SrcP.M.init_pc SrcP.M.phdrs) en inp ->
      valid_input_either inp ->
      impl psegs (at_node psegs) (the_prog psegs pstage inp en) (epost the_post)
           (ms0 psegs SrcP.M.init_pc SrcP.M.phdrs en inp)
      /\ leaves_unreachable_m nstep (the_prog psegs pstage inp en) (mo0 psegs source_alloc_limit en inp)
      /\ tsafe nstep nsafeU (the_prog psegs pstage inp en) (mo0 psegs source_alloc_limit en inp);

  ob_impl_U : forall (en : ExecEntry) (inp : ProcInput),
      valid_entry (mkImage usegs Ubsan.M.init_pc Ubsan.M.phdrs) en inp ->
      valid_input_either inp ->
      impl usegs (at_node usegs) (the_prog usegs ustage inp en) (epost the_post)
           (ms0 usegs Ubsan.M.init_pc Ubsan.M.phdrs en inp)
      /\ leaves_unreachable_m nstep (the_prog usegs ustage inp en) (mo0 usegs target_alloc_limit en inp)
      /\ tsafe nstep nsafeU (the_prog usegs ustage inp en) (mo0 usegs target_alloc_limit en inp);

  ob_equiv : forall (enP enU : ExecEntry) (inp : ProcInput),
      valid_entry (mkImage psegs SrcP.M.init_pc SrcP.M.phdrs) enP inp ->
      valid_entry (mkImage usegs Ubsan.M.init_pc Ubsan.M.phdrs) enU inp ->
      valid_input_either inp ->
      forall tP tU, resolves tP (the_prog psegs pstage inp enP) -> resolves tU (the_prog usegs ustage inp enU) ->
      trace_equiv (tree_traces tP (mo0 psegs source_alloc_limit enP inp))
                  (tree_traces tU (mo0 usegs target_alloc_limit enU inp))
}.

Theorem base_ubsan_from_obligations :
  base_obligations ->
  strong_universal_error_free_T_scfg ACFG
    (mkImage SrcP.M.loaded_segments SrcP.M.init_pc SrcP.M.phdrs)
    (mkImage Ubsan.M.loaded_segments Ubsan.M.init_pc Ubsan.M.phdrs).
Proof.
  intros [HP HU HE].
  apply (error_free_from_trees (the_prog psegs pstage) (the_prog usegs ustage) the_post the_post).
  - exact HP.
  - exact HU.
  - exact HE.
Qed.

Theorem base_ubsan_scfg_from_obligations :
  base_obligations ->
  strong_universal_error_free_T_scfg ACFG
    (mkImage SrcP.M.loaded_segments SrcP.M.init_pc SrcP.M.phdrs)
    (mkImage Ubsan.M.loaded_segments Ubsan.M.init_pc Ubsan.M.phdrs).
Proof.
  intros [HP HU HE].
  apply (error_free_scfg_from_trees (the_prog psegs pstage) (the_prog usegs ustage) the_post the_post).
  - exact HP.
  - exact HU.
  - exact HE.
Qed.

