(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.simdjson.fuzz_implementations.lib.Lib Require Import PropExec MState Frame Exec ITree Nodes RegsEquiv Image Ceiling.
From OSSVerify.Proofs.simdjson.fuzz_implementations.lib Require Import TopLevel Obligations ProofBase.
From OSSVerify.Proofs.simdjson.fuzz_implementations.lib.Spec Require Import Prog ModelInv Canon ProgDetIface ProgDet.
From OSSVerify.Proofs.simdjson.fuzz_implementations.lib.Spec Require Import ModelInvN MallocSome.
From OSSVerify.simdjson.fuzz_implementations.images Require Import Plain.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Lemma run_ceiling_eqA : forall segs pc ph en inp,
  in_va_size inp = Sv48 ->
  valid_entry (mkImage segs pc ph) en inp ->
  bv_unsigned (en_sp en) - stack_max_size = @alloc_ceiling (run_ceiling en).
Proof.
  intros segs pc ph en inp Hsv48 Hve. rewrite (valid_entry_sv48 _ _ _ Hsv48) in Hve.
  destruct en as [sp brk mb rnd]. destruct Hve as (Hsp & _ & _ & _). destruct Hsp as (H1 & H2 & H3).
  cbn [en_sp]. unfold run_ceiling, sp_window_lo, sp_window_hi, stack_max_size in *. cbn [en_sp].
  rewrite ceiling_of_sp_eq; [reflexivity| lia| exact H3].
Qed.

Theorem P_canon_lim : forall lim,
  impl_P_stmt ->
  prog_no_enomem_stmt psegs pstage Plain.M.init_pc Plain.M.phdrs lim ->
  forall en inp,
    valid_entry (mkImage psegs Plain.M.init_pc Plain.M.phdrs) en inp -> valid_input_either inp ->
    trace_equiv (bh_traces (run_scfg ACFG (mkImage psegs Plain.M.init_pc Plain.M.phdrs) lim en inp))
                (canonT (argv_Z (in_argv inp)) (in_fs inp))
    /\ ~ bh_errors (run_scfg ACFG (mkImage psegs Plain.M.init_pc Plain.M.phdrs) lim en inp).
Proof.
  intros lim HP Hne en inp He Hi.
  destruct (prog_model_ok (CE__:=run_ceiling en) (raw_malloc_some (CE__:=run_ceiling en)) psegs pstage _ _ lim en inp segs_pu_P He Hi
              (run_ceiling_eqA _ _ _ _ _ (vie_va_size _ Hi) He) (Hne en inp He Hi)) as [Hl Hs].
  destruct (run_of_tree psegs Plain.M.init_pc Plain.M.phdrs lim
              (the_prog psegs pstage inp en) (epost the_post) en inp (HP en inp He Hi) Hl
              (tsafe_conj nstep nsafe unforced _ _ Hs (tsafe_mono nstep no_enomem unforced _ _ no_enomem_unforced (Hne en inp He Hi))))
    as (t' & Hres & Htr & Herr & _).
  split; [| exact Herr].
  intros tr. rewrite (Htr tr). exact (prog_det_gen psegs pstage _ _ lim segs_pu_P Hne en inp He Hi t' Hres tr).
Qed.

Theorem P_canon :
  impl_P_stmt ->
  prog_no_enomem_stmt psegs pstage Plain.M.init_pc Plain.M.phdrs source_alloc_limit ->
  forall en inp,
    valid_entry (mkImage psegs Plain.M.init_pc Plain.M.phdrs) en inp -> valid_input_either inp ->
    trace_equiv (bh_traces (run_scfg ACFG (mkImage psegs Plain.M.init_pc Plain.M.phdrs) source_alloc_limit en inp))
                (canonT (argv_Z (in_argv inp)) (in_fs inp))
    /\ ~ bh_errors (run_scfg ACFG (mkImage psegs Plain.M.init_pc Plain.M.phdrs) source_alloc_limit en inp).
Proof. exact (P_canon_lim source_alloc_limit). Qed.
