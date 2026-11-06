(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib Require Import SimInv ExitSim CatSim ShapeAlg DivergeSim SpinAlg SpinAlgX VmLimitFrame.

Import ListNotations.
Open Scope bv_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Section WithCfg.
Variable scfg : SpuriousCfg.

Lemma srealizes_error_free : forall segs pc ph sp brk0 mb rnd lim inp T,
  srealizes segs scfg (init_config segs pc ph sp brk0 mb rnd lim inp) T ->
  Safe segs scfg (init_config segs pc ph sp brk0 mb rnd lim inp) ->
  error_free (run_scfg scfg (mkImage segs pc ph) lim (mkEntry sp brk0 mb rnd) inp).
Proof. intros. cbn. eapply srealizes_no_error; eassumption. Qed.

Lemma srealizes_traces_iff : forall segs pc ph sp brk0 mb rnd lim inp T tr,
  srealizes segs scfg (init_config segs pc ph sp brk0 mb rnd lim inp) T ->
  Safe segs scfg (init_config segs pc ph sp brk0 mb rnd lim inp) ->
  bh_traces (run_scfg scfg (mkImage segs pc ph) lim (mkEntry sp brk0 mb rnd) inp) tr <-> T tr.
Proof. intros. cbn. apply srealizes_obs_iff; assumption. Qed.

Lemma srealizes_error_free_big : forall segs pc ph sp brk0 mb rnd lim inp T,
  srealizes segs scfg (init_config segs pc ph sp brk0 mb rnd lim inp) T ->
  (nbr_limit <= lim)%Z ->
  error_free (run_scfg scfg (mkImage segs pc ph) lim (mkEntry sp brk0 mb rnd) inp).
Proof. intros. eapply srealizes_error_free; [eassumption | apply Safe_init_big; assumption]. Qed.

Lemma srealizes_traces_iff_big : forall segs pc ph sp brk0 mb rnd lim inp T tr,
  srealizes segs scfg (init_config segs pc ph sp brk0 mb rnd lim inp) T ->
  (nbr_limit <= lim)%Z ->
  bh_traces (run_scfg scfg (mkImage segs pc ph) lim (mkEntry sp brk0 mb rnd) inp) tr <-> T tr.
Proof. intros. apply srealizes_traces_iff; [assumption | apply Safe_init_big; assumption]. Qed.

Lemma srealizes_error_free_wb : forall segs pc ph sp brk0 mb rnd lim inp T,
  srealizes segs scfg (init_config segs pc ph sp brk0 mb rnd lim inp) T ->
  ~ run_scfg_budget_refused scfg (mkImage segs pc ph) lim (mkEntry sp brk0 mb rnd) inp ->
  error_free (run_scfg scfg (mkImage segs pc ph) lim (mkEntry sp brk0 mb rnd) inp).
Proof. intros. eapply srealizes_error_free; [eassumption | apply Safe_init_within_budget; assumption]. Qed.

Lemma srealizes_traces_iff_wb : forall segs pc ph sp brk0 mb rnd lim inp T tr,
  srealizes segs scfg (init_config segs pc ph sp brk0 mb rnd lim inp) T ->
  ~ run_scfg_budget_refused scfg (mkImage segs pc ph) lim (mkEntry sp brk0 mb rnd) inp ->
  bh_traces (run_scfg scfg (mkImage segs pc ph) lim (mkEntry sp brk0 mb rnd) inp) tr <-> T tr.
Proof. intros. apply srealizes_traces_iff; [assumption | apply Safe_init_within_budget; assumption]. Qed.

Lemma realizes_error_free : forall segs pc ph sp brk0 mb rnd lim inp T,
  realizes segs scfg (init_config segs pc ph sp brk0 mb rnd lim inp) T ->
  error_free (run_scfg scfg (mkImage segs pc ph) lim (mkEntry sp brk0 mb rnd) inp).
Proof. intros. cbn. eapply realizes_no_error; eassumption. Qed.

Lemma realizes_traces_iff : forall segs pc ph sp brk0 mb rnd lim inp T tr,
  realizes segs scfg (init_config segs pc ph sp brk0 mb rnd lim inp) T ->
  bh_traces (run_scfg scfg (mkImage segs pc ph) lim (mkEntry sp brk0 mb rnd) inp) tr <-> T tr.
Proof. intros. cbn. apply realizes_obs_iff. assumption. Qed.

Theorem shape_strong_equiv_efs :
  forall source_segs rpc rph rsp rbrk rmb (rrnd : EntryDraw) (rlim : Z)
         target_segs apc aph asp abrk amb (arnd : EntryDraw) (alim : Z)
         (T : TSet) (inp : ProcInput),
  srealizes source_segs scfg
    (init_config source_segs rpc rph rsp rbrk rmb rrnd rlim inp) T ->
  srealizes target_segs scfg
    (init_config target_segs apc aph asp abrk amb arnd alim inp) T ->
  Safe source_segs scfg (init_config source_segs rpc rph rsp rbrk rmb rrnd rlim inp) ->
  Safe target_segs scfg (init_config target_segs apc aph asp abrk amb arnd alim inp) ->
  error_free (run_scfg scfg (mkImage source_segs rpc rph) rlim (mkEntry rsp rbrk rmb rrnd) inp)
  /\ error_free (run_scfg scfg (mkImage target_segs apc aph) alim (mkEntry asp abrk amb arnd) inp)
  /\ trace_equiv (bh_traces (run_scfg scfg (mkImage source_segs rpc rph) rlim (mkEntry rsp rbrk rmb rrnd) inp))
                 (bh_traces (run_scfg scfg (mkImage target_segs apc aph) alim (mkEntry asp abrk amb arnd) inp)).
Proof.
  intros source_segs rpc rph rsp rbrk rmb rrnd rlim target_segs apc aph asp abrk amb arnd alim
    T inp Hsource Htarget Hss Hst.
  split; [| split].
  - eapply srealizes_error_free; [exact Hsource | exact Hss].
  - eapply srealizes_error_free; [exact Htarget | exact Hst].
  - intro tr.
    rewrite (srealizes_traces_iff source_segs _ _ _ _ _ _ _ _ T tr Hsource Hss).
    rewrite (srealizes_traces_iff target_segs _ _ _ _ _ _ _ _ T tr Htarget Hst).
    reflexivity.
Qed.

Theorem shape_strong_equiv_efs_big :
  forall source_segs rpc rph rsp rbrk rmb (rrnd : EntryDraw) (rlim : Z)
         target_segs apc aph asp abrk amb (arnd : EntryDraw) (alim : Z)
         (T : TSet) (inp : ProcInput),
  srealizes source_segs scfg
    (init_config source_segs rpc rph rsp rbrk rmb rrnd rlim inp) T ->
  srealizes target_segs scfg
    (init_config target_segs apc aph asp abrk amb arnd alim inp) T ->
  (nbr_limit <= rlim)%Z -> (nbr_limit <= alim)%Z ->
  error_free (run_scfg scfg (mkImage source_segs rpc rph) rlim (mkEntry rsp rbrk rmb rrnd) inp)
  /\ error_free (run_scfg scfg (mkImage target_segs apc aph) alim (mkEntry asp abrk amb arnd) inp)
  /\ trace_equiv (bh_traces (run_scfg scfg (mkImage source_segs rpc rph) rlim (mkEntry rsp rbrk rmb rrnd) inp))
                 (bh_traces (run_scfg scfg (mkImage target_segs apc aph) alim (mkEntry asp abrk amb arnd) inp)).
Proof.
  intros until inp. intros Hs Ht Hrl Hal.
  apply (shape_strong_equiv_efs _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ T inp Hs Ht); apply Safe_init_big; assumption.
Qed.

Corollary shape_strong_equiv_efs_eq :
  forall source_segs rpc rph rsp rbrk rmb (rrnd : EntryDraw) (rlim : Z)
         target_segs apc aph asp abrk amb (arnd : EntryDraw) (alim : Z)
         (T T' : TSet) (inp : ProcInput),
  srealizes source_segs scfg
    (init_config source_segs rpc rph rsp rbrk rmb rrnd rlim inp) T ->
  srealizes target_segs scfg
    (init_config target_segs apc aph asp abrk amb arnd alim inp) T' ->
  t_eq T T' ->
  Safe source_segs scfg (init_config source_segs rpc rph rsp rbrk rmb rrnd rlim inp) ->
  Safe target_segs scfg (init_config target_segs apc aph asp abrk amb arnd alim inp) ->
  error_free (run_scfg scfg (mkImage source_segs rpc rph) rlim (mkEntry rsp rbrk rmb rrnd) inp)
  /\ error_free (run_scfg scfg (mkImage target_segs apc aph) alim (mkEntry asp abrk amb arnd) inp)
  /\ trace_equiv (bh_traces (run_scfg scfg (mkImage source_segs rpc rph) rlim (mkEntry rsp rbrk rmb rrnd) inp))
                 (bh_traces (run_scfg scfg (mkImage target_segs apc aph) alim (mkEntry asp abrk amb arnd) inp)).
Proof.
  intros until T'. intros inp Hs Ht Heq Hss Hst.
  eapply shape_strong_equiv_efs; [| exact Ht | exact Hss | exact Hst].
  eapply srz_conseq; [exact Hs | exact Heq].
Qed.

Theorem shape_strong_equiv_ef :
  forall source_segs rpc rph rsp rbrk rmb (rrnd : EntryDraw) (rlim : Z)
         target_segs apc aph asp abrk amb (arnd : EntryDraw) (alim : Z)
         (T : TSet) (inp : ProcInput),
  realizes source_segs scfg
    (init_config source_segs rpc rph rsp rbrk rmb rrnd rlim inp) T ->
  realizes target_segs scfg
    (init_config target_segs apc aph asp abrk amb arnd alim inp) T ->
  error_free (run_scfg scfg (mkImage source_segs rpc rph) rlim (mkEntry rsp rbrk rmb rrnd) inp)
  /\ error_free (run_scfg scfg (mkImage target_segs apc aph) alim (mkEntry asp abrk amb arnd) inp)
  /\ trace_equiv (bh_traces (run_scfg scfg (mkImage source_segs rpc rph) rlim (mkEntry rsp rbrk rmb rrnd) inp))
                 (bh_traces (run_scfg scfg (mkImage target_segs apc aph) alim (mkEntry asp abrk amb arnd) inp)).
Proof.

  intros until T. intros inp Hs Ht.
  split; [| split].
  - eapply realizes_error_free; exact Hs.
  - eapply realizes_error_free; exact Ht.
  - intro tr.
    rewrite (realizes_traces_iff _ _ _ _ _ _ _ _ _ T tr Hs).
    rewrite (realizes_traces_iff _ _ _ _ _ _ _ _ _ T tr Ht).
    reflexivity.
Qed.

Corollary shape_strong_equiv_ef_eq :
  forall source_segs rpc rph rsp rbrk rmb (rrnd : EntryDraw) (rlim : Z)
         target_segs apc aph asp abrk amb (arnd : EntryDraw) (alim : Z)
         (T T' : TSet) (inp : ProcInput),
  realizes source_segs scfg
    (init_config source_segs rpc rph rsp rbrk rmb rrnd rlim inp) T ->
  realizes target_segs scfg
    (init_config target_segs apc aph asp abrk amb arnd alim inp) T' ->
  t_eq T T' ->
  error_free (run_scfg scfg (mkImage source_segs rpc rph) rlim (mkEntry rsp rbrk rmb rrnd) inp)
  /\ error_free (run_scfg scfg (mkImage target_segs apc aph) alim (mkEntry asp abrk amb arnd) inp)
  /\ trace_equiv (bh_traces (run_scfg scfg (mkImage source_segs rpc rph) rlim (mkEntry rsp rbrk rmb rrnd) inp))
                 (bh_traces (run_scfg scfg (mkImage target_segs apc aph) alim (mkEntry asp abrk amb arnd) inp)).
Proof.
  intros until T'. intros inp Hs Ht Heq.
  eapply shape_strong_equiv_ef; [| exact Ht].
  eapply rz_conseq; [exact Hs | exact Heq].
Qed.

Corollary srealizes_strong_equiv_error_free_scfg :
  forall (SRC TGT : Image) (en_s en_t : ExecEntry) (T : TSet) (inp : ProcInput),
  srealizes (img_segments SRC) scfg
    (init_config (img_segments SRC) (img_init_pc SRC) (img_phdrs SRC)
                 (en_sp en_s) (en_brk en_s) (en_mmap_base en_s) (en_draw en_s) source_alloc_limit inp) T ->
  srealizes (img_segments TGT) scfg
    (init_config (img_segments TGT) (img_init_pc TGT) (img_phdrs TGT)
                 (en_sp en_t) (en_brk en_t) (en_mmap_base en_t) (en_draw en_t) target_alloc_limit inp) T ->
  strong_equiv_error_free_scfg scfg SRC TGT en_s en_t inp.
Proof.
  intros [ssegs spc sph] [tsegs tpc tph] [ssp sbrk smb srnd] [tsp tbrk tmb trnd] T inp Hs Ht.
  unfold strong_equiv_error_free_scfg. cbn [img_segments img_init_pc img_phdrs en_sp en_brk en_mmap_base en_draw] in Hs, Ht.
  exact (shape_strong_equiv_efs_big ssegs spc sph ssp sbrk smb srnd source_alloc_limit
           tsegs tpc tph tsp tbrk tmb trnd target_alloc_limit T inp Hs Ht nbr_limit_source nbr_limit_target).
Qed.

End WithCfg.
