(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (the SIGPIPE disposition the launch leaves free; the input's kernel build and exec file name; the start-up facts stated over the launch's ProcInput; the run's segment list with the vDSO/vvar pair; the channel-reader premise; the launch premises). *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence Classifier.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.openssl.pem.lib Require Import
  SimInv ExitSim CatSim ShapeAlg SpinAlg ShapeEF ShapeEFS ShapeLaws CfgStep ShapeEFC InpRec.   (* [comment removed for export] *)
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.

(* [comment removed for export] *)
(* At the revision a run reads [Run.run_segments segs inp sp mbase] (the binary's
   segments and the vDSO/vvar pair), and so does its initial configuration.  At
   LPS 727298f3 [Run.valid_input] leaves the SIGPIPE disposition free, so the
   realization is asked of every disposition [sd]. *)
Definition image_realizes (segs : list Segment) (pc : N) (ph : PhdrInfo) (lim : Z)
    (SPEC : list (list byte) -> Fs.Fs -> TSet) : Prop :=
  forall (sp : word) (rdraw : EntryDraw) (brk0 mbase : word) (argv envp : list (list byte)) (fs : Fs.Fs)
         (stdin : InputStream) (uid gid hw : word) (groups : list word) (net : NetQueue) (nofile sigmask : word)
         (urnd : InputStream) (kern : KernelBuild) (execfn : list byte) (sd : bool),   (* [comment removed for export] *)
    valid_sp sp -> valid_brk segs brk0 -> valid_mmap_base mbase ->
    valid_argv argv -> valid_envp envp -> entry_stack_fits sp argv envp -> valid_id uid ->
    valid_fs fs -> valid_hwcap hw ->
    entry_launch_ok_va Sv48 (mkEntry sp brk0 mbase rdraw)
      (InpRec.inp argv envp fs stdin uid gid hw groups net nofile sigmask urnd kern execfn sd) ->
    valid_launch (InpRec.inp argv envp fs stdin uid gid hw groups net nofile sigmask urnd kern execfn sd) ->
    srealizes (run_segments segs (InpRec.inp argv envp fs stdin uid gid hw groups net nofile sigmask urnd kern execfn sd) sp mbase)
      (init_config (run_segments segs (InpRec.inp argv envp fs stdin uid gid hw groups net nofile sigmask urnd kern execfn sd) sp mbase)
         pc ph sp brk0 mbase rdraw lim
         (InpRec.inp argv envp fs stdin uid gid hw groups net nofile sigmask urnd kern execfn sd))
      (SPEC argv fs).

Lemma image_realizes_at : forall segs pc ph lim SPEC,
  image_realizes segs pc ph lim SPEC ->
  forall en inp, valid_entry (mkImage segs pc ph) en inp -> valid_input inp ->
    srealizes (vsegs_of (mkImage segs pc ph) en inp) (init_cfg_of (mkImage segs pc ph) lim en inp)
      (SPEC (in_argv inp) (in_fs inp)).
Proof.
  intros segs pc ph lim SPEC H en inp Hen Hv.
  pose proof (valid_input_va_size _ Hv) as Hsv48.
  rewrite (valid_entry_sv48 _ _ _ Hsv48) in Hen.
  destruct en as [sp brk0 mbase rdraw]. cbn in Hen. destruct Hen as (Hsp & Hbrk & Hmb & Hfit & Hok).
  (* [comment removed for export] *)
  (* The facts this proof uses are taken BY NAME from the model's own accessors
     instead of by position: a positional pattern is correct only against one arity of
     [valid_input].  At LPS 727298f3 [valid_input] no longer pins the SIGPIPE
     disposition, so it is not read here: it is passed on as [sd]. Nothing about the
     lemma's type changes: it still takes [valid_input inp]. *)
  pose proof (valid_input_argv _ Hv) as Hva.
  pose proof (valid_input_envp _ Hv) as Hve.
  pose proof (valid_input_fs _ Hv) as Hfs.
  pose proof (proj1 (valid_input_creds _ Hv)) as Huid.
  pose proof (valid_input_hwcap _ Hv) as Hhw.
  pose proof (valid_input_abort_terminal _ Hv) as Habt.
  pose proof (valid_input_va_size _ Hv) as Hva48.
  pose proof (valid_input_urandom _ Hv) as Hur.
  pose proof (valid_input_launch _ Hv) as Hlau.
  pose proof (valid_input_channel_reader _ Hv) as Hcr.
  pose proof (valid_input_sigpipe_terminal _ Hv) as Hst.
  clear Hv.
  destruct inp as [argv envp ifs stdin uid gid groups net nofile sigmask hw abt va urnd tmp kern execfn cr sd st].
  cbn [in_argv in_envp in_uid in_hwcap in_abort_terminal in_va_size
       in_channel_reader in_sigpipe_terminal] in *.
  subst abt va cr st.
  exact (H sp rdraw brk0 mbase argv envp
           (in_fs (mkProcInput_full argv envp ifs stdin uid gid groups net nofile sigmask hw false Sv48 urnd tmp
                     kern execfn true sd false))
           stdin uid gid hw groups net nofile sigmask urnd kern execfn sd
           Hsp Hbrk Hmb Hva Hve Hfit Huid Hfs Hhw Hok Hlau).
Qed.

(* [comment removed for export] *)
Theorem budgets_base_of_realizes : forall ssegs spc sph tsegs tpc tph (ls lt : Z) SPEC,
  image_realizes ssegs spc sph ls SPEC ->
  image_realizes tsegs tpc tph lt SPEC ->
  strong_universal_error_free_T_scfg_budgets kit_cfg ls lt (mkImage ssegs spc sph) (mkImage tsegs tpc tph).
Proof.
  intros ssegs spc sph tsegs tpc tph ls lt SPEC HS HT.
  apply srz_universal_scfg_budgets. intros en_s en_t inp Hs Ht Hv.
  exists (SPEC (in_argv inp) (in_fs inp)), (SPEC (in_argv inp) (in_fs inp)).
  split; [apply srealizes_wb_of_srealizes; exact (image_realizes_at _ _ _ _ _ HS en_s inp Hs Hv) |].
  split; [exact (image_realizes_at _ _ _ _ _ HT en_t inp Ht Hv) |].
  apply t_eq_refl.
Qed.

(* [comment removed for export] *)
Theorem pinned_base_of_realizes : forall ssegs spc sph tsegs tpc tph SPEC,
  image_realizes ssegs spc sph source_alloc_limit SPEC ->
  image_realizes tsegs tpc tph target_alloc_limit SPEC ->
  strong_universal_error_free_T_scfg kit_cfg (mkImage ssegs spc sph) (mkImage tsegs tpc tph).
Proof.
  intros ssegs spc sph tsegs tpc tph SPEC HS HT.
  apply srz_universal_scfg. intros en_s en_t inp Hs Ht Hv.
  exists (SPEC (in_argv inp) (in_fs inp)), (SPEC (in_argv inp) (in_fs inp)).
  split; [exact (image_realizes_at _ _ _ _ _ HS en_s inp Hs Hv) |].
  split; [exact (image_realizes_at _ _ _ _ _ HT en_t inp Ht Hv) |].
  apply t_eq_refl.
Qed.
