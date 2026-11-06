(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import NArith List ZArith Lia Bool.
Require OSSVerify.coturn.FuzzStunClient.images.Plain.
Require OSSVerify.coturn.FuzzStunClient.images.Ubsan.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common Require Import ShapeAlg ShapeEF.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib Require Import Spec BaseGlue.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module SRCM := OSSVerify.coturn.FuzzStunClient.images.Plain.M.
Module UBM := OSSVerify.coturn.FuzzStunClient.images.Ubsan.M.

(* [comment removed for export] *)
Definition ref_spec_stmt : Prop :=
  forall sp brk mb rnd inp,
    valid_entry (mkImage SRCM.loaded_segments SRCM.init_pc SRCM.phdrs) (mkEntry sp brk mb rnd) inp -> valid_input inp ->
    realizes SRCM.loaded_segments
      (init_config SRCM.loaded_segments SRCM.init_pc SRCM.phdrs sp brk mb rnd source_alloc_limit inp)
      (spec (in_argv inp) (in_fs inp)).

(* [comment removed for export] *)
Definition ub_spec_stmt : Prop :=
  forall sp brk mb rnd inp,
    valid_entry (mkImage UBM.loaded_segments UBM.init_pc UBM.phdrs) (mkEntry sp brk mb rnd) inp -> valid_input inp ->
    realizes UBM.loaded_segments
      (init_config UBM.loaded_segments UBM.init_pc UBM.phdrs sp brk mb rnd target_alloc_limit inp)
      (spec (in_argv inp) (in_fs inp)).

Theorem ubsan_base_of_specs : ref_spec_stmt -> ub_spec_stmt ->
  strong_universal_error_free_T
    (mkImage SRCM.loaded_segments SRCM.init_pc SRCM.phdrs)
    (mkImage UBM.loaded_segments UBM.init_pc UBM.phdrs).
Proof.
  intros H1 H2.
  exact (base_of_realizes SRCM.loaded_segments SRCM.init_pc SRCM.phdrs UBM.loaded_segments UBM.init_pc UBM.phdrs
           (fun inp => spec (in_argv inp) (in_fs inp)) H1 H2).
Qed.
