(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Sem.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Lib Require Import PropExec MState Frame Exec ITree Nodes RegsEquiv Image.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit Require Import TopLevel.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Spec Require Import Prog.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.World Require Import Src_zlib_compress_fuzzer_repro.
Module SrcP := Src_zlib_compress_fuzzer_repro.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.World Require Import Tgt_compress_fuzzer_ubsan.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.

Definition run_ceiling (en : ExecEntry) : Ceiling := ceiling_of_sp (bv_unsigned (en_sp en)).

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
      valid_entry (mkImage usegs Tgt_compress_fuzzer_ubsan.M.init_pc Tgt_compress_fuzzer_ubsan.M.phdrs) en inp ->
      valid_input inp ->
      impl usegs (at_node usegs) (the_prog usegs ustage inp en) (epost the_post)
           (ms0 usegs Tgt_compress_fuzzer_ubsan.M.init_pc Tgt_compress_fuzzer_ubsan.M.phdrs en inp)
      /\ leaves_unreachable_m nstep (the_prog usegs ustage inp en) (mo0 usegs target_alloc_limit en inp)
      /\ tsafe nstep nsafe (the_prog usegs ustage inp en) (mo0 usegs target_alloc_limit en inp);

  ob_equiv : forall (enP enU : ExecEntry) (inp : ProcInput),
      valid_entry (mkImage psegs SrcP.M.init_pc SrcP.M.phdrs) enP inp ->
      valid_entry (mkImage usegs Tgt_compress_fuzzer_ubsan.M.init_pc Tgt_compress_fuzzer_ubsan.M.phdrs) enU inp ->
      valid_input inp ->
      trace_equiv (tree_traces (the_prog psegs pstage inp enP) (mo0 psegs source_alloc_limit enP inp))
                  (tree_traces (the_prog usegs ustage inp enU) (mo0 usegs target_alloc_limit enU inp))
}.

