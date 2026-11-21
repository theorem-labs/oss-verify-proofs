(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: for LPS 727298f3, the top reads the launch's channel reader, file-system image and private /tmp from the input, and the walks' ambient carries the launch's vDSO run (amb_set_vdso, main_entry_amb_of). *)
(* [comment removed for export] *)
From Stdlib Require Import NArith ZArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.skcms.iccprofile_info.images Require Import Plain.
From OSSVerify.Proofs.skcms.iccprofile_info.lib.Info Require Import Amb PropExec ShapeAlg Spec RefStartup ProofInfoPlan RefLim.
(* Not imported: a bare [Require] makes the module available for QUALIFIED
   reference and contributes nothing to unqualified name resolution, so it
   cannot shadow anything this file already resolves.  Needed because
   [vdso_run_init] ([c0dd863a:theories/LinuxProcessSem/Vdso.v:262]) is not in
   this file's import set while [with_vdso] is. *)
From LinuxProcessSemantics.LinuxProcessSem Require Vdso.
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
    valid_launch (mkProcInputC argv envp fs0 stdin0) ->
    (* LPS #38 (in 727298f3): the launch's channel reader.  [mkProcInputC] copies it from
       [Amb.a_channel_reader], so that is the form the walks see; the discharge is
       [Run.valid_input_channel_reader] at [ProofInfoPlan.info_ubsan_scfg]. *)
    @a_channel_reader AMB = true ->
    entry_launch_ok_va Sv48 (mkEntry sp brk mbase rnd) (mkProcInputC argv envp fs0 stdin0) ->
    (0 < bv_unsigned tid < 2 ^ 22)%Z ->
    main_entry sp (mkProcInputC argv envp fs0 stdin0) mbase rnd tid regs mem ->
    realizes rsegs (mkCfg (mkst regs (0x12a88 : word) mem (seg_rom rsegs))
                          (with_tid tid (with_vdso a_vdso (init_model (segments_reserved rsegs) brk mbase sp LIM
                                                    (mkProcInputC argv envp fs0 stdin0)))))
             (spec argv fs0).

(* LPS 727298f3: [ProcInput] carries the launch's file-system image and its private /tmp
   apart ([in_image_fs], [in_tmp]), and [mkProcInputC] puts the seeded file system in the
   image with an empty /tmp, so it does not rebuild a general input and [main_entry]
   (an inductive) does not convert between the two.  No field of [main_entry] reads
   [in_image_fs] or [in_tmp], the only projections where the two records differ, so
   each field converts and the record is rebuilt field by field. *)
Lemma main_entry_amb_of : forall sp inp mbase rnd tid regs mem (v : Vdso.VdsoRun),
  main_entry sp inp mbase rnd tid regs mem ->
  main_entry sp (@mkProcInputC (amb_set_vdso (amb_of inp) v) (in_argv inp) (in_envp inp) (in_fs inp) (in_stdin inp))
             mbase rnd tid regs mem.
Proof.
  intros sp inp mbase rnd tid regs mem v ME. destruct inp.
  destruct ME as [A1 A2 A3 A4 A5 A6 A7 A8 A9 A10 A11 A12 A13].
  (* [constructor] takes the record's parameters from the goal, so each field is checked
     against the [mkProcInputC] input by conversion (with [_] parameters they are
     inferred from [A6] instead, as the destructed input) *)
  constructor;
    [ exact A1 | exact A2 | exact A3 | exact A4 | exact A5 | exact A6 | exact A7 | exact A8
    | exact A9 | exact A10 | exact A11 | exact A12 | exact A13 ].
Qed.

Theorem ref_realizes_spec {AL : AllocLim} : main_phase_stmt -> realizes_spec_stmt rsegs rpc rph LIM.
Proof.
  intros MP sp brk mbase rnd inp Hsp Hbrk Hfit Hva Hve Hfs Hvl Hcr Hlau.
  (* the walks' ambient carries the launch's vDSO run, so their models after start-up keep the mkModelC
     shape (Amb.a_vdso); mkProcInputC ignores it.  [main_entry] is an inductive, so its input argument
     only converts once [inp] is a constructor *)
  pose proof (MP (amb_set_vdso (amb_of inp) (Vdso.vdso_run_init (ed_vdso rnd))) sp brk mbase rnd
                 (in_argv inp) (in_envp inp) (in_fs inp) (in_stdin inp)) as MP'.
  pose proof (main_entry_amb_of sp inp mbase rnd) as MEC.
  clear MP. destruct inp.
  apply (ref_startup sp brk mbase rnd LIM _ _ Hsp Hbrk Hva Hve Hvl Hlau).
  intros tid regs mem Htid ME.
  exact (MP' tid regs mem Hsp Hbrk Hfit Hva Hve Hfs Hvl Hcr Hlau Htid
           (MEC tid regs mem (Vdso.vdso_run_init (ed_vdso rnd)) ME)).
Qed.
