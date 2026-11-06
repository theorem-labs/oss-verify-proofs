(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence Classifier.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.openssl.punycode.lib Require Import
  SimInv ExitSim CatSim ShapeAlg SpinAlg ShapeEF ShapeEFS ShapeLaws CfgStep ShapeEFC AsanInit.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.

(* [comment removed for export] *)
Definition image_realizes (segs : list Segment) (pc : N) (ph : PhdrInfo) (lim : Z)
    (SPEC : list (list byte) -> Fs.Fs -> TSet) : Prop :=
  forall (sp : word) (rdraw : EntryDraw) (brk0 mbase : word) (argv envp : list (list byte)) (fs : Fs.Fs)
         (stdin : InputStream) (uid gid hw : word) (groups : list word) (net : NetQueue) (nofile sigmask : word)
         (urnd : InputStream),   (* [comment removed for export] *)
    valid_sp sp -> valid_brk segs brk0 -> valid_mmap_base mbase ->
    valid_argv argv -> valid_envp envp -> entry_stack_fits sp argv envp -> valid_id uid ->
    valid_fs fs -> valid_hwcap hw ->
    srealizes segs
      (init_config segs pc ph sp brk0 mbase rdraw lim
         (AsanInit.inp argv envp fs stdin uid gid hw groups net nofile sigmask urnd))
      (SPEC argv fs).

Lemma image_realizes_at : forall segs pc ph lim SPEC,
  image_realizes segs pc ph lim SPEC ->
  forall en inp, valid_entry (mkImage segs pc ph) en inp -> valid_input inp ->
    srealizes segs (init_cfg_of (mkImage segs pc ph) lim en inp) (SPEC (in_argv inp) (in_fs inp)).
Proof.
  intros segs pc ph lim SPEC H en inp Hen Hv.
  pose proof (valid_input_va_size _ Hv) as Hsv48.
  rewrite (valid_entry_sv48 _ _ _ Hsv48) in Hen.
  destruct en as [sp brk0 mbase rdraw]. cbn in Hen. destruct Hen as (Hsp & Hbrk & Hmb & Hfit).
  (* [comment removed for export] *)
  destruct Hv as (Hva & Hve & Hfs & _ & (Huid & _) & _ & _ & Hhw & Habt & Hva48 & Hur).
  destruct inp as [argv envp ifs stdin uid gid groups net nofile sigmask hw abt va urnd tmp].
  cbn [in_argv in_envp in_uid in_hwcap in_abort_terminal in_va_size] in *. subst abt va.
  exact (H sp rdraw brk0 mbase argv envp
           (in_fs (mkProcInput_full argv envp ifs stdin uid gid groups net nofile sigmask hw false Sv48 urnd tmp))
           stdin uid gid hw groups net nofile sigmask urnd
           Hsp Hbrk Hmb Hva Hve Hfit Huid Hfs Hhw).
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
