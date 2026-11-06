(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import NArith ZArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.skcms.iccprofile_info.images Require Import Plain.
From OSSVerify.Proofs.skcms.iccprofile_info.lib.Info Require Import Amb PropExec ShapeAlg Spec RefStartup ProofInfoPlan RefLim.
Unset Nia Cache.  (* [comment removed for export] *)
Unset Lia Cache.
Import ListNotations.
Open Scope bv_scope.
#[local] Existing Instance PropExec.fp0.

Definition rsegs := Plain.M.loaded_segments.
Definition rpc := Plain.M.init_pc.
Definition rph := Plain.M.phdrs.

(* [comment removed for export] *)
Definition main_phase_stmt {AL : AllocLim} : Prop :=
  forall (AMB : Amb) (sp brk mbase : word) (rnd : EntryDraw) (argv envp : list (list byte)) (fs0 : Fs)
         (stdin0 : InputStream) (tid : word) (regs : bvmap 5 word) (mem : word -> option byte),
    valid_sp sp -> valid_brk rsegs brk -> entry_stack_fits sp argv envp -> valid_argv argv -> valid_envp envp -> valid_fs fs0 ->
    (0 < bv_unsigned tid < 2 ^ 22)%Z ->
    main_entry sp argv envp tid rnd regs mem ->
    realizes rsegs (mkCfg (mkst regs (0x12a88 : word) mem (seg_rom rsegs))
                          (with_tid tid (init_model (segments_reserved rsegs) brk mbase sp LIM
                                                    (mkProcInputC argv envp fs0 stdin0))))
             (spec argv fs0).

Theorem ref_realizes_spec {AL : AllocLim} : main_phase_stmt -> realizes_spec_stmt rsegs rpc rph LIM.
Proof.
  intros MP sp brk mbase rnd inp Hsp Hbrk Hfit Hva Hve Hfs.
  apply (ref_startup sp brk mbase rnd LIM inp (spec (in_argv inp) (in_fs inp)) Hsp Hbrk Hva Hve).
  intros tid regs mem Htid ME.
  rewrite (init_model_of _ _ _ _ _ inp).
  exact (@MP (amb_of inp) sp brk mbase rnd (in_argv inp) (in_envp inp) (in_fs inp) (in_stdin inp) tid regs mem
           Hsp Hbrk Hfit Hva Hve Hfs Htid ME).
Qed.
