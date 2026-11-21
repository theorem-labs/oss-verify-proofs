(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: replaces the TCodec-encoded statements of srealizes_error_free, realizes_traces_iff, shape_strong_equiv_ef/efs and their _eq corollaries with plain Rocq statements over run_segments, dropping the TCodec import and name table; taken in part from projects/jsoncons/fuzz_bigint/proofs/lib/ShapeEF.v, lines 21-52, 66-78, 86-97, 104-116, 124-132. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require BvWfKernel.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import SimInv ExitSim CatSim ShapeAlg DivergeSim SpinAlg SpinAlgX.
Import ListNotations.
Open Scope bv_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Section WithCfg.
Variable scfg : SpuriousCfg.
Lemma srealizes_error_free : forall segs pc ph sp brk0 mb rnd lim inp T,
srealizes (run_segments segs inp sp mb) scfg (init_config (run_segments segs inp sp mb) pc ph sp brk0 mb rnd lim inp) T ->
error_free (run_scfg scfg (mkImage segs pc ph) lim (mkEntry sp brk0 mb rnd) inp).
Proof. intros. cbn. eapply srealizes_no_error; eassumption. Qed.
Lemma srealizes_traces_iff : forall segs pc ph sp brk0 mb rnd lim inp T tr,
srealizes (run_segments segs inp sp mb) scfg (init_config (run_segments segs inp sp mb) pc ph sp brk0 mb rnd lim inp) T ->
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
srealizes (run_segments source_segs inp rsp rmb) scfg
(init_config (run_segments source_segs inp rsp rmb) rpc rph rsp rbrk rmb rrnd rlim inp) T ->
srealizes (run_segments target_segs inp asp amb) scfg
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
Corollary shape_strong_equiv_efs_eq :
forall source_segs rpc rph rsp rbrk rmb (rrnd : EntryDraw) (rlim : Z)
target_segs apc aph asp abrk amb (arnd : EntryDraw) (alim : Z)
(T T' : TSet) (inp : ProcInput),
srealizes (run_segments source_segs inp rsp rmb) scfg
(init_config (run_segments source_segs inp rsp rmb) rpc rph rsp rbrk rmb rrnd rlim inp) T ->
srealizes (run_segments target_segs inp asp amb) scfg
(init_config (run_segments target_segs inp asp amb) apc aph asp abrk amb arnd alim inp) T' ->
t_eq T T' ->
error_free (run_scfg scfg (mkImage source_segs rpc rph) rlim (mkEntry rsp rbrk rmb rrnd) inp)
/\ error_free (run_scfg scfg (mkImage target_segs apc aph) alim (mkEntry asp abrk amb arnd) inp)
/\ trace_equiv (bh_traces (run_scfg scfg (mkImage source_segs rpc rph) rlim (mkEntry rsp rbrk rmb rrnd) inp))
(bh_traces (run_scfg scfg (mkImage target_segs apc aph) alim (mkEntry asp abrk amb arnd) inp)).
Proof.
intros until T'. intros inp Hs Ht Heq.
eapply shape_strong_equiv_efs; [| exact Ht].
eapply srz_conseq; [exact Hs | exact Heq].
Qed.
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
apply srealizes_of_realizes; assumption.
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
Corollary srealizes_strong_equiv_error_free_scfg :
forall (SRC TGT : Image) (en_s en_t : ExecEntry) (T : TSet) (inp : ProcInput),
srealizes (run_segments (img_segments SRC) inp (en_sp en_s) (en_mmap_base en_s)) scfg
(init_config (run_segments (img_segments SRC) inp (en_sp en_s) (en_mmap_base en_s)) (img_init_pc SRC) (img_phdrs SRC)
(en_sp en_s) (en_brk en_s) (en_mmap_base en_s) (en_draw en_s) source_alloc_limit inp) T ->
srealizes (run_segments (img_segments TGT) inp (en_sp en_t) (en_mmap_base en_t)) scfg
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
