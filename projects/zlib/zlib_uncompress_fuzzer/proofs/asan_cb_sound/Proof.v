(* SPDX-License-Identifier: MIT *)
(** [Statements.asan_cb_sound], from a theorem of this proof library.  The library states that theorem over
    its own names for the memory images; the alias texts in its World folder make each of them the
    repository's image of the same build, which [world_*_is_images] below checks by computation.
    The library's theorem says that the classifier decides exactly the inputs on which each
    build agrees with its original; [ClassifierShapes.classifies_patch_diff_sound_of_exact]
    gives the sound form of the entry. *)
From Stdlib Require Import QArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import MemImageType.
Require LinuxProcessSemantics.LinuxProcessSem.Run LinuxProcessSemantics.EquivalenceDefinition.Equivalence.
Require OSSVerify.Core.Shapes OSSVerify.Core.ClassifierShapes.
From OSSVerify.zlib.zlib_uncompress_fuzzer Require Statements Images.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_agrees_alloc_forced_only.World Require Clb_zlib_uncompress_fuzzer_asan SrcO_zlib_zlib_uncompress_fuzzer_repro Src_zlib_zlib_uncompress_fuzzer_repro TgtO_zlib_uncompress_fuzzer_asan Tgt_zlib_uncompress_fuzzer_asan.
Require OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_agrees_alloc_forced_only.AgreeW.R27U OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_agrees_alloc_forced_only.BaseAsanU1.

Module SpuriousCfgM <: LinuxProcessSemantics.EquivalenceDefinition.Equivalence.SPURIOUS_CFG.
  Definition cfg := LinuxProcessSemantics.LinuxProcessSem.Run.mkSpuriousCfg false true true true true true.
End SpuriousCfgM.

Lemma world_plain_original_is_images :
  mkImage SrcO_zlib_zlib_uncompress_fuzzer_repro.M.loaded_segments SrcO_zlib_zlib_uncompress_fuzzer_repro.M.init_pc SrcO_zlib_zlib_uncompress_fuzzer_repro.M.phdrs = Images.plain_original.
Proof. reflexivity. Qed.

Lemma world_plain_is_images :
  mkImage Src_zlib_zlib_uncompress_fuzzer_repro.M.loaded_segments Src_zlib_zlib_uncompress_fuzzer_repro.M.init_pc Src_zlib_zlib_uncompress_fuzzer_repro.M.phdrs = Images.plain.
Proof. reflexivity. Qed.

Lemma world_asan_original_is_images :
  mkImage TgtO_zlib_uncompress_fuzzer_asan.M.loaded_segments TgtO_zlib_uncompress_fuzzer_asan.M.init_pc TgtO_zlib_uncompress_fuzzer_asan.M.phdrs = Images.asan_original.
Proof. reflexivity. Qed.

Lemma world_asan_is_images :
  mkImage Tgt_zlib_uncompress_fuzzer_asan.M.loaded_segments Tgt_zlib_uncompress_fuzzer_asan.M.init_pc Tgt_zlib_uncompress_fuzzer_asan.M.phdrs = Images.asan.
Proof. reflexivity. Qed.

Lemma world_classifier_b_asan_is_images :
  mkImage Clb_zlib_uncompress_fuzzer_asan.M.loaded_segments Clb_zlib_uncompress_fuzzer_asan.M.init_pc Clb_zlib_uncompress_fuzzer_asan.M.phdrs = Images.classifier_b_asan.
Proof. reflexivity. Qed.

Theorem asan_cb_sound_holds : Statements.asan_cb_sound.
Proof.
  unfold Statements.asan_cb_sound. rewrite <- world_plain_original_is_images, <- world_plain_is_images, <- world_asan_original_is_images, <- world_asan_is_images, <- world_classifier_b_asan_is_images.
  apply OSSVerify.Core.ClassifierShapes.classifies_patch_diff_sound_of_exact. rewrite OSSVerify.Core.ClassifierShapes.classifies_patch_diff_is_lps.
  exact ((OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_agrees_alloc_forced_only.AgreeW.R27U.cb_iff SpuriousCfgM.cfg OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_agrees_alloc_forced_only.AgreeW.R27U.x1_srco_tgt (OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_agrees_alloc_forced_only.BaseAsanU1.base_asan_plain_u1) OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_agrees_alloc_forced_only.AgreeW.R27U.x2_src_tgto)).
Qed.
