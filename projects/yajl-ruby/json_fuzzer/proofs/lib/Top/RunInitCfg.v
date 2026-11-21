(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (run_init_ms0: a walk from ms0 lifted to the run's start over run_segments, with the premise that the binary carries no vDSO segment, and run_scfg_fields_ms0 dropped). *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Monad Specs Run.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Common Require Import ShapeAlgCfg.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Common.Cfg Require Import RomStable.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require Import PropExec MState RegsEquiv RegsEquivCfg RunInit.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Top Require Import GlueCfg.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.

Lemma init_config_eqv_ms0 : forall segs pc ph lim en inp,
  cfg_eqv (init_config segs pc ph (en_sp en) (en_brk en) (en_mmap_base en) (en_draw en) lim inp)
          (mkCfg (ms0 segs pc ph en inp) (mo0 segs lim en inp)).
Proof.
  intros. destruct (init_config_ms0 segs pc ph lim en inp) as [-> Heqv].
  split; [exact Heqv | reflexivity].
Qed.

Lemma realizes_cfg_init_of_ms0 : forall cfg segs pc ph lim en inp T,
  realizes_cfg cfg segs (mkCfg (ms0 segs pc ph en inp) (mo0 segs lim en inp)) T ->
  realizes_cfg cfg segs
    (init_config segs pc ph (en_sp en) (en_brk en) (en_mmap_base en) (en_draw en) lim inp) T.
Proof.
  intros cfg segs pc ph lim en inp T H.
  exact (realizes_cfg_eqv segs cfg _ T H _ (cfg_eqv_sym _ _ (init_config_eqv_ms0 segs pc ph lim en inp))).
Qed.

(* LPS 08b1429: the run starts from [init_config (run_segments ..) ..]; a walk over the binary's
   segments from [ms0] is a walk of the run ([RomStable.run_init]).  The binary carries no vDSO
   segment ([vdso_image segs = None]); each top row closes it on its concrete image. *)
Theorem run_init_ms0 : forall cfg segs pc ph lim en inp T,
  vdso_image segs = None ->
  realizes_cfg cfg segs (mkCfg (ms0 segs pc ph en inp) (mo0 segs lim en inp)) T ->
  realizes_cfg cfg (run_segments segs inp (en_sp en) (en_mmap_base en))
    (init_config (run_segments segs inp (en_sp en) (en_mmap_base en)) pc ph
       (en_sp en) (en_brk en) (en_mmap_base en) (en_draw en) lim inp) T.
Proof.
  intros cfg segs pc ph lim en inp T Hvi H.
  apply (run_init cfg segs inp (en_sp en) (en_mmap_base en) pc ph (en_brk en) (en_draw en) lim T Hvi).
  apply realizes_cfg_init_of_ms0. exact H.
Qed.

Section WithCfg.
Variable cfg : SpuriousCfg.

Lemma realizes_spec_cfg_of_ms0 : forall segs pc ph lim T,
  vdso_image segs = None ->
  (forall en inp,
     valid_entry (mkImage segs pc ph) en inp -> valid_input inp ->
     realizes_cfg cfg segs (mkCfg (ms0 segs pc ph en inp) (mo0 segs lim en inp)) (T inp)) ->
  realizes_spec_cfg cfg segs pc ph lim T.
Proof.
  intros segs pc ph lim T Hvi H. apply realizes_spec_cfg_intro.
  intros en inp HE HI. apply (run_init_ms0 cfg segs pc ph lim en inp (T inp) Hvi). apply H; assumption.
Qed.

End WithCfg.
