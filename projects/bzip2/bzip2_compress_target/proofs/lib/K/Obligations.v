(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Sem.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.Lib Require Import PropExec MState Frame Exec ITree Nodes RegsEquiv Image.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K Require Import TopLevel.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.Spec Require Import Prog.
From OSSVerify.bzip2.bzip2_compress_target.images Require Import Plain.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Module SrcP := Plain.
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
      valid_input_either inp ->
      impl psegs (at_node psegs) (the_prog psegs pstage inp en) (epost the_post)
           (ms0 psegs SrcP.M.init_pc SrcP.M.phdrs en inp)
      /\ leaves_unreachable_m nstep (the_prog psegs pstage inp en) (mo0 psegs source_alloc_limit en inp)
      /\ tsafe nstep nsafe (the_prog psegs pstage inp en) (mo0 psegs source_alloc_limit en inp)
}.

(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
