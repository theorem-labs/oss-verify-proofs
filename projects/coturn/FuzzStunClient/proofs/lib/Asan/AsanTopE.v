(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: the main trees are one per launch rseq layout, and for LPS 727298f3 the top reads the new valid_input clauses, applies the vDSO bridges (SpinBridges), takes the SIGPIPE default from the input and the launch's tmp filesystem, kernel build and exec file name, and asan_spec_T gives the launch at the flag true from the trees' dead-arm check. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
Require OSSVerify.coturn.FuzzStunClient.images.Plain.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.coturn.FuzzStunClient.images Require Import Asan.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common Require Import ShapeAlg SpinAlg.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common Require SpinBridges.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common.Cfg Require RomStable.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib Require Import Spec FPA_asan.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Asan Require Import
  AxSymExec3 AsanPlanCore AsanPlan AsanPlanSound AsanInit AsanPlanImages FContractAsan AsanMainLib
  StartupHSMainAsan MainGlueDefs MainGlue AsanMainClosedE AsanTopGlue DeadArm.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import AX2. Import AP. Import APS.
Open Scope Z_scope.
#[local] Notation LIM := target_alloc_limit.

Section TopE.
  (* the published claim covers both rseq layouts, so the main trees come ONE PER rseq_z rsb (main's
     argv nodes read e_str0/e_str1 of ASAN_at (rseq_z rsb)), and the proof uses the launch's own:
     TREES (kb_rseq (in_kernel inp)). *)
  Hypothesis FCA : F_contract_asan ASEGS FPA_asan.
  Variables KCm BFUELm FUELm : nat.
  Variable ITm : itab.
  Hypothesis ITm_ok : itab_sound ASEGS ITm.
  Variable TREE : bool -> nat -> nat -> mtree.
  Hypothesis TREES : forall rsb h ch i, (HS_mainA (rseq_z rsb)) h = Some ch -> (i < 6)%nat ->
    mtree_ok (rsb := rsb) KCm BFUELm FUELm ITm 0 0 (HSA rsb (HS_mainA (rseq_z rsb)) h) (root_class i) (TREE rsb h i) = true.

  Theorem asan_spec_E : asan_spec_stmt.
  Proof.
    intros sp brk mb rnd inp Hent Hvalid.
    pose proof (valid_input_va_size _ Hvalid) as Hsv48.
    rewrite (valid_entry_sv48 _ _ _ Hsv48) in Hent.
    destruct Hent as (Hsp & Hbrk & Hmb & Hfit & Hlau).
    (* [Run.valid_input] ([c0dd863a:theories/LinuxProcessSem/Run.v:4647-4659]) has sixteen
       clauses, among them [fs_image_real] after [fs_keys_relative], and
       [valid_launch], [in_channel_reader], [in_sigpipe_terminal] and the recorded
       kernel after [valid_urandom].  Named, not dropped: the [eassumption] below
       feeds them to [asan_realizes_spec_E]. *)
    destruct Hvalid as (Hargv & Henvp & Hfs & Hrel & Hreal & [Huid Hgid] & Hnofile & Hsig
                        & Hhw & Habort & Hva & Hur & Hlaunch & Hcrd & Hsgp & Hkb).
    (* LPS 727298f3: the run's segment index and its start configuration carry the
       launch's vDSO, which the image's own segments do not; [asan_realizes_spec_E] is
       stated over the image's.  The two bridges RefMain and UbMain already take on this
       branch ([RefMain]) carry it, over [srealizes] ([Common/SpinBridges.v]).
       They come BEFORE [init_config_inp]: their statements name one [inp] in both the
       segment index and the configuration, so the rewrite has to follow them. *)
    assert (Hnone : vdso_image ASANM.loaded_segments = None)
      by (apply RomStable.vdso_image_none_of_no_text; reflexivity).
    apply (SpinBridges.srealizes_run_segments ASANM.loaded_segments inp sp mb _ _ Hnone).
    apply (SpinBridges.srealizes_run_init ASANM.loaded_segments inp sp brk mb
             ASANM.init_pc ASANM.phdrs rnd _ _ Hnone).
    (* [comment removed for export] *)
    (* [init_config_inp] takes the four flags [valid_input] pins; the SIGPIPE disposition it
       leaves free becomes [AsanInit.inp]'s [sigpipe_default], the input's own value. *)
    rewrite (init_config_inp _ _ _ _ _ _ _ _ inp Habort Hva Hcrd Hsgp).
    change target_alloc_limit with LIM.
    (* LPS 727298f3: the launch carries three more declarations -- [in_tmp], [in_kernel]
       and [in_execfn] -- so [AsanInit.inp] takes fifteen arguments and the section's
       seventh is the IMAGE filesystem [imgfs], not the run's [in_fs].  [init_config_inp]
       above rebuilt the goal in exactly that form; this list matches it term for term, and
       [sigpipe_default] is named because the section takes it implicitly. *)
    eapply (asan_realizes_spec_E FCA sp rnd brk mb (in_argv inp) (in_envp inp) (in_image_fs inp) (in_stdin inp) (in_uid inp) (in_gid inp)
              (in_hwcap inp) (in_groups inp) (in_net inp) (in_nofile inp) (in_sigmask inp) (in_urandom inp)
              (in_tmp inp) (in_kernel inp) (in_execfn inp) (sigpipe_default := in_sigpipe_default inp));
      try eassumption;
      (* LPS 727298f3: the section's kernel is the launch's own, so beside the trees
         [eassumption] leaves [Hrs], the layout's rseq read against that kernel.  It is
         [AsanStartupE.Hrs] with [rsb] at [kb_rseq (in_kernel inp)] -- the same r the
         trees are given at -- and holds by computation there. *)
      first [ exact (TREES (kb_rseq (in_kernel inp)))
            | exact (eq_refl : a_rseq (ASAN_at (rseq_z (kb_rseq (in_kernel inp))))
                               = rseq_z (kb_rseq (in_kernel inp))) ].
  Qed.

  (* The launch at the flag [true]: as [asan_spec_E], with the main trees' dead-arm check
     ([MainGlue.mtree_dead hf26], computed per tree and per r). *)
  Theorem asan_spec_T :
    (forall rsb h ch i, (HS_mainA (rseq_z rsb)) h = Some ch -> (i < 6)%nat -> mtree_dead hf26 (TREE rsb h i) = true) ->
    asan_spec_stmt_T.
  Proof.
    intros Hdead sp brk mb rnd inp Hent Hvalid.
    pose proof (valid_input_va_size _ Hvalid) as Hsv48.
    rewrite (valid_entry_sv48 _ _ _ Hsv48) in Hent.
    destruct Hent as (Hsp & Hbrk & Hmb & Hfit & Hlau).
    destruct Hvalid as (Hargv & Henvp & Hfs & Hrel & Hreal & [Huid Hgid] & Hnofile & Hsig
                        & Hhw & Habort & Hva & Hur & Hlaunch & Hcrd & Hsgp & Hkb).
    assert (Hnone : vdso_image ASANM.loaded_segments = None)
      by (apply RomStable.vdso_image_none_of_no_text; reflexivity).
    apply (SpinBridges.srealizes_run_segments ASANM.loaded_segments inp sp mb _ _ Hnone).
    apply (SpinBridges.srealizes_run_init ASANM.loaded_segments inp sp brk mb
             ASANM.init_pc ASANM.phdrs rnd _ _ Hnone).
    rewrite (init_config_inp _ _ _ _ _ _ _ _ inp Habort Hva Hcrd Hsgp).
    change target_alloc_limit with LIM.
    eapply (asan_realizes_spec_M FCA sp rnd brk mb (in_argv inp) (in_envp inp) (in_image_fs inp) (in_stdin inp) (in_uid inp) (in_gid inp)
              (in_hwcap inp) (in_groups inp) (in_net inp) (in_nofile inp) (in_sigmask inp) (in_urandom inp)
              (in_tmp inp) (in_kernel inp) (in_execfn inp) (sigpipe_default := in_sigpipe_default inp));
      try eassumption;
      first [ exact (TREES (kb_rseq (in_kernel inp)))
            | exact (fun _ => Hdead (kb_rseq (in_kernel inp)))
            | exact (eq_refl : a_rseq (ASAN_at (rseq_z (kb_rseq (in_kernel inp))))
                               = rseq_z (kb_rseq (in_kernel inp))) ].
  Qed.
End TopE.
