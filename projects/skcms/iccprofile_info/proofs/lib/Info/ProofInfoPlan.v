(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import NArith ZArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.skcms.iccprofile_info.images Require Import Plain.
From OSSVerify.skcms.iccprofile_info.images Require Import Ubsan.
From OSSVerify.Proofs.skcms.iccprofile_info.lib.Info Require Import PropExec ShapeAlg ShapeEF Spec.
Unset Nia Cache.  (* [comment removed for export] *)
Unset Lia Cache.
#[local] Existing Instance PropExec.fp0.

Abbreviation SSEGS := Plain.M.loaded_segments.
Abbreviation SPC := Plain.M.init_pc.
Abbreviation SPH := Plain.M.phdrs.
Abbreviation TSEGS := Ubsan.M.loaded_segments.
Abbreviation TPC := Ubsan.M.init_pc.
Abbreviation TPH := Ubsan.M.phdrs.

(* [comment removed for export] *)
Definition realizes_spec_stmt (segs : list Segment) (pc : N) (ph : PhdrInfo) (lim : Z) : Prop :=
  forall sp brk0 mbase (rnd : EntryDraw) (inp : ProcInput),
    valid_sp sp -> valid_brk segs brk0 -> entry_stack_fits sp (in_argv inp) (in_envp inp) ->
    valid_argv (in_argv inp) -> valid_envp (in_envp inp) -> valid_fs (in_fs inp) ->
    realizes segs (init_config segs pc ph sp brk0 mbase rnd lim inp) (spec (in_argv inp) (in_fs inp)).

Theorem info_ubsan_scfg :
  realizes_spec_stmt SSEGS SPC SPH source_alloc_limit ->
  realizes_spec_stmt TSEGS TPC TPH target_alloc_limit ->
  strong_universal_error_free_T_scfg CFG (mkImage SSEGS SPC SPH) (mkImage TSEGS TPC TPH).
Proof.
  intros REF UB [rsp rbrk rmb rrnd] [asp abrk amb arnd] inp Hens Hent Hvalid.
  (* [comment removed for export] *)
  pose proof (valid_input_va_size _ Hvalid) as Hsv48.
  rewrite (valid_entry_sv48 _ _ _ Hsv48) in Hens. rewrite (valid_entry_sv48 _ _ _ Hsv48) in Hent.
  destruct Hens as (Hrsp & Hrbrk & _ & Hrfit). destruct Hent as (Hasp & Habrk & _ & Hafit).
  destruct Hvalid as (Hargv & Henvp & Hfs & _).
  unfold strong_equiv_error_free_scfg.
  apply (shape_strong_equiv_ef SSEGS SPC SPH rsp rbrk rmb rrnd source_alloc_limit
                               TSEGS TPC TPH asp abrk amb arnd target_alloc_limit
                               (spec (in_argv inp) (in_fs inp)) inp).
  - exact (REF rsp rbrk rmb rrnd inp Hrsp Hrbrk Hrfit Hargv Henvp Hfs).
  - exact (UB asp abrk amb arnd inp Hasp Habrk Hafit Hargv Henvp Hfs).
Qed.
