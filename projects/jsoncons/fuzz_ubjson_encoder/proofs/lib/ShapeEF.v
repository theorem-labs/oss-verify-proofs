(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3: recorded proofs replaced by tactic proofs; the new launch (process input, auxv, group id, exec file name); the run over the run's segments. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require BvWfKernel.
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require Import SimInv ExitSim CatSim ShapeAlg DivergeSim SpinAlg SpinAlgX.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require KReplay.
Ltac2 kr_t_ShapeEF () := "C47Corelib7Classes9Morphisms6ProperC47Corelib7Classes?RelationClasses9ReflexiveC47Corelib7Program6Basics4flipC47Corelib7Classes9MorphismsKrespectful_per_obligation_1I47Corelib4Init9Datatypes4list00K47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00C4ELinuxProcessSemantics?LinuxProcessSem3Run;init_configI79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib7SpinAlg:srealizes000C13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib7SpinAlgBsrealizes_no_errorC13~~~K4ELinuxProcessSemantics?LinuxProcessSem<MemImageType5Image01K4ELinuxProcessSemantics?LinuxProcessSem3Run9ExecEntry01C4ELinuxProcessSemantics?LinuxProcessSem3Run8run_scfgC4ELinuxProcessSemanticsEEquivalenceDefinition;Equivalence:error_freeI4ELinuxProcessSemantics?LinuxProcessSem<MemImageType7Segment00I47Corelib7Numbers7BinNums1N00I4ELinuxProcessSemantics?LinuxProcessSem<MemImageType8PhdrInfo00K47Corelib7Numbers7BinNums8positive03I4ELinuxProcessSemantics?LinuxProcessSem;StackLayout9EntryDraw00I47Corelib7Numbers7BinNums1Z00I4ELinuxProcessSemantics?LinuxProcessSem5State9ProcInput00C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8ShapeAlg4TSetC13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib5BMode;bm_off_instC13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib7SpinAlgAsrealizes_obs_iffC13~~~C4ELinuxProcessSemantics?LinuxProcessSem3Run9bh_tracesC47Corelib4Init5Logic3iffI4ELinuxProcessSemantics?LinuxProcessSem5State5event00I79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8ShapeAlg8realizes00C13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8ShapeAlgArealizes_no_errorC13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8ShapeAlg@realizes_obs_iffC13~~~C4ELinuxProcessSemanticsEEquivalenceDefinition;Equivalence;trace_equivI47Corelib4Init5Logic3and00c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib7ShapeEFDsrealizes_error_freeC13~~~C47Corelib7Classes9Morphisms?eq_proper_proxyC47Corelib7Classes9MorphismsMtrans_co_eq_inv_impl_morphismc79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib7ShapeEFDsrealizes_traces_iffC13~~~C47Corelib7Classes?RelationClasses?Equivalence_PERC47Corelib7Classes9MorphismsNtrans_sym_co_inv_impl_morphismC47Corelib7Classes?RelationClasses;reflexivityK47Corelib4Init5Logic3and01C47Corelib7Classes?RelationClasses>iff_TransitiveC47Corelib7Classes?RelationClasses?iff_equivalenceC47Corelib7Classes?RelationClasses=iff_ReflexiveC79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8ShapeAlg4t_eqC13~~~K79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib7SpinAlg:srealizes004C13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib7ShapeEFFshape_strong_equiv_efsC13~~~C79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib7SpinAlgFsrealizes0_of_realizesC13~~~K79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib8ShapeAlg8realizes03C13~~~c79OSSVerify6Proofs8jsonconsCfuzz_ubjson_encoder3lib7ShapeEFEshape_strong_equiv_efC13~~~C4ELinuxProcessSemantics?LinuxProcessSem<MemImageType<img_segmentsC4ELinuxProcessSemantics?LinuxProcessSem<MemImageType;img_init_pcC4ELinuxProcessSemantics?LinuxProcessSem<MemImageType9img_phdrsC4ELinuxProcessSemantics?LinuxProcessSem3Run5en_spC4ELinuxProcessSemantics?LinuxProcessSem3Run6en_brkC4ELinuxProcessSemantics?LinuxProcessSem3Run<en_mmap_baseC4ELinuxProcessSemantics?LinuxProcessSem3Run7en_drawC4ELinuxProcessSemanticsEEquivalenceDefinition;EquivalenceLstrong_equiv_error_free_scfgI4ELinuxProcessSemantics?LinuxProcessSem<MemImageType5Image00I4ELinuxProcessSemantics?LinuxProcessSem3Run9ExecEntry00C4ELinuxProcessSemantics?LinuxProcessSem5StateBsource_alloc_limitC4ELinuxProcessSemantics?LinuxProcessSem5StateBtarget_alloc_limit".

Import ListNotations.
Open Scope bv_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Section WithCfg.
Variable scfg : SpuriousCfg.

(* [comment removed for export] *)
Lemma srealizes_error_free : forall segs pc ph sp brk0 mb rnd lim inp T,
  srealizes0 (run_segments segs inp sp mb) scfg (init_config (run_segments segs inp sp mb) pc ph sp brk0 mb rnd lim inp) T ->
  error_free (run_scfg scfg (mkImage segs pc ph) lim (mkEntry sp brk0 mb rnd) inp).
Proof. intros. cbn. eapply srealizes_no_error; eassumption. Qed.

Lemma srealizes_traces_iff : forall segs pc ph sp brk0 mb rnd lim inp T tr,
  srealizes0 (run_segments segs inp sp mb) scfg (init_config (run_segments segs inp sp mb) pc ph sp brk0 mb rnd lim inp) T ->
  bh_traces (run_scfg scfg (mkImage segs pc ph) lim (mkEntry sp brk0 mb rnd) inp) tr <-> T tr.
Proof. intros. cbn. apply srealizes_obs_iff. assumption. Qed.

Lemma realizes_error_free : forall segs pc ph sp brk0 mb rnd lim inp T,
  realizes (run_segments segs inp sp mb) scfg (init_config (run_segments segs inp sp mb) pc ph sp brk0 mb rnd lim inp) T ->
  error_free (run_scfg scfg (mkImage segs pc ph) lim (mkEntry sp brk0 mb rnd) inp).
Proof. intros. cbn. eapply realizes_no_error; eassumption. Qed.

Lemma realizes_traces_iff : forall segs pc ph sp brk0 mb rnd lim inp T tr,
  realizes (run_segments segs inp sp mb) scfg (init_config (run_segments segs inp sp mb) pc ph sp brk0 mb rnd lim inp) T ->
  bh_traces (run_scfg scfg (mkImage segs pc ph) lim (mkEntry sp brk0 mb rnd) inp) tr <-> T tr.
Proof. intros. cbn. apply realizes_obs_iff. assumption. Qed.

Theorem shape_strong_equiv_efs :
  forall source_segs rpc rph rsp rbrk rmb (rrnd : EntryDraw) (rlim : Z)
         target_segs apc aph asp abrk amb (arnd : EntryDraw) (alim : Z)
         (T : TSet) (inp : ProcInput),
  srealizes0 (run_segments source_segs inp rsp rmb) scfg
    (init_config (run_segments source_segs inp rsp rmb) rpc rph rsp rbrk rmb rrnd rlim inp) T ->
  srealizes0 (run_segments target_segs inp asp amb) scfg
    (init_config (run_segments target_segs inp asp amb) apc aph asp abrk amb arnd alim inp) T ->
  error_free (run_scfg scfg (mkImage source_segs rpc rph) rlim (mkEntry rsp rbrk rmb rrnd) inp)
  /\ error_free (run_scfg scfg (mkImage target_segs apc aph) alim (mkEntry asp abrk amb arnd) inp)
  /\ trace_equiv (bh_traces (run_scfg scfg (mkImage source_segs rpc rph) rlim (mkEntry rsp rbrk rmb rrnd) inp))
                 (bh_traces (run_scfg scfg (mkImage target_segs apc aph) alim (mkEntry asp abrk amb arnd) inp)).
Proof.
  intros source_segs rpc rph rsp rbrk rmb rrnd rlim target_segs apc aph asp abrk amb arnd alim
    T inp Hsource Htarget.
  split; [| split].
  - eapply srealizes_error_free; exact Hsource.
  - eapply srealizes_error_free; exact Htarget.
  - intro tr.
    rewrite (srealizes_traces_iff source_segs _ _ _ _ _ _ _ _ T tr Hsource).
    rewrite (srealizes_traces_iff target_segs _ _ _ _ _ _ _ _ T tr Htarget).
    reflexivity.
Qed.

(* [comment removed for export] *)
Corollary shape_strong_equiv_efs_eq :
  forall source_segs rpc rph rsp rbrk rmb (rrnd : EntryDraw) (rlim : Z)
         target_segs apc aph asp abrk amb (arnd : EntryDraw) (alim : Z)
         (T T' : TSet) (inp : ProcInput),
  srealizes0 (run_segments source_segs inp rsp rmb) scfg
    (init_config (run_segments source_segs inp rsp rmb) rpc rph rsp rbrk rmb rrnd rlim inp) T ->
  srealizes0 (run_segments target_segs inp asp amb) scfg
    (init_config (run_segments target_segs inp asp amb) apc aph asp abrk amb arnd alim inp) T' ->
  t_eq T T' ->
  error_free (run_scfg scfg (mkImage source_segs rpc rph) rlim (mkEntry rsp rbrk rmb rrnd) inp)
  /\ error_free (run_scfg scfg (mkImage target_segs apc aph) alim (mkEntry asp abrk amb arnd) inp)
  /\ trace_equiv (bh_traces (run_scfg scfg (mkImage source_segs rpc rph) rlim (mkEntry rsp rbrk rmb rrnd) inp))
                 (bh_traces (run_scfg scfg (mkImage target_segs apc aph) alim (mkEntry asp abrk amb arnd) inp)).
Proof.
  intros until T'. intros inp Hs Ht Heq.
  eapply shape_strong_equiv_efs; [| exact Ht].
  eapply srz0_conseq; [exact Hs | exact Heq].
Qed.

(* [comment removed for export] *)
Theorem shape_strong_equiv_ef :
  forall source_segs rpc rph rsp rbrk rmb (rrnd : EntryDraw) (rlim : Z)
         target_segs apc aph asp abrk amb (arnd : EntryDraw) (alim : Z)
         (T : TSet) (inp : ProcInput),
  realizes (run_segments source_segs inp rsp rmb) scfg
    (init_config (run_segments source_segs inp rsp rmb) rpc rph rsp rbrk rmb rrnd rlim inp) T ->
  realizes (run_segments target_segs inp asp amb) scfg
    (init_config (run_segments target_segs inp asp amb) apc aph asp abrk amb arnd alim inp) T ->
  error_free (run_scfg scfg (mkImage source_segs rpc rph) rlim (mkEntry rsp rbrk rmb rrnd) inp)
  /\ error_free (run_scfg scfg (mkImage target_segs apc aph) alim (mkEntry asp abrk amb arnd) inp)
  /\ trace_equiv (bh_traces (run_scfg scfg (mkImage source_segs rpc rph) rlim (mkEntry rsp rbrk rmb rrnd) inp))
                 (bh_traces (run_scfg scfg (mkImage target_segs apc aph) alim (mkEntry asp abrk amb arnd) inp)).
Proof.
  intros until T. intros inp Hs Ht.
  apply (shape_strong_equiv_efs _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ T);
    apply srealizes0_of_realizes; assumption.
Qed.

Corollary shape_strong_equiv_ef_eq :
  forall source_segs rpc rph rsp rbrk rmb (rrnd : EntryDraw) (rlim : Z)
         target_segs apc aph asp abrk amb (arnd : EntryDraw) (alim : Z)
         (T T' : TSet) (inp : ProcInput),
  realizes (run_segments source_segs inp rsp rmb) scfg
    (init_config (run_segments source_segs inp rsp rmb) rpc rph rsp rbrk rmb rrnd rlim inp) T ->
  realizes (run_segments target_segs inp asp amb) scfg
    (init_config (run_segments target_segs inp asp amb) apc aph asp abrk amb arnd alim inp) T' ->
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

(* [comment removed for export] *)
Corollary srealizes_strong_equiv_error_free_scfg :
  forall (SRC TGT : Image) (en_s en_t : ExecEntry) (T : TSet) (inp : ProcInput),
  srealizes0 (run_segments (img_segments SRC) inp (en_sp en_s) (en_mmap_base en_s)) scfg
    (init_config (run_segments (img_segments SRC) inp (en_sp en_s) (en_mmap_base en_s)) (img_init_pc SRC) (img_phdrs SRC)
                 (en_sp en_s) (en_brk en_s) (en_mmap_base en_s) (en_draw en_s) source_alloc_limit inp) T ->
  srealizes0 (run_segments (img_segments TGT) inp (en_sp en_t) (en_mmap_base en_t)) scfg
    (init_config (run_segments (img_segments TGT) inp (en_sp en_t) (en_mmap_base en_t)) (img_init_pc TGT) (img_phdrs TGT)
                 (en_sp en_t) (en_brk en_t) (en_mmap_base en_t) (en_draw en_t) target_alloc_limit inp) T ->
  strong_equiv_error_free_scfg scfg SRC TGT en_s en_t inp.
Proof.
  intros [ssegs spc sph] [tsegs tpc tph] [ssp sbrk smb srnd] [tsp tbrk tmb trnd] T inp Hs Ht.
  unfold strong_equiv_error_free_scfg. cbn [img_segments img_init_pc img_phdrs en_sp en_brk en_mmap_base en_draw] in Hs, Ht.
  exact (shape_strong_equiv_efs ssegs spc sph ssp sbrk smb srnd source_alloc_limit
           tsegs tpc tph tsp tbrk tmb trnd target_alloc_limit T inp Hs Ht).
Qed.

End WithCfg.
