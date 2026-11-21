(* SPDX-License-Identifier: MIT *)
(** [Statements.ubsan_cb_sound], from a theorem of this proof library.  The library states that theorem over
    its own names for the memory images; the alias texts in its World folder make each of them the
    repository's image of the same build, which [world_*_is_images] below checks by computation.
    The library's theorem says that the classifier decides exactly the inputs on which each
    build agrees with its original; [ClassifierShapes.classifies_patch_diff_sound_of_exact]
    gives the sound form of the entry. *)
From Stdlib Require Import QArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import MemImageType.
Require LinuxProcessSemantics.LinuxProcessSem.Run LinuxProcessSemantics.EquivalenceDefinition.Equivalence.
Require OSSVerify.Core.Shapes OSSVerify.Core.ClassifierShapes.
From OSSVerify.zlib.zlib_uncompress3_fuzzer Require Statements Images.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.World Require Clb_zlib_uncompress3_fuzzer_ubsan SrcO_zlib_zlib_uncompress3_fuzzer_repro Src_zlib_zlib_uncompress3_fuzzer_repro TgtO_zlib_uncompress3_fuzzer_ubsan Tgt_zlib_uncompress3_fuzzer_ubsan.
Require OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.AgreeW.R26U OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.I8S.S_TopI OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.I8U.T_TopI OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.Thm_uncompress3_ubsan_mr.

Module SpuriousCfgM <: LinuxProcessSemantics.EquivalenceDefinition.Equivalence.SPURIOUS_CFG.
  Definition cfg := LinuxProcessSemantics.LinuxProcessSem.Run.mkSpuriousCfg false true true true true true.
End SpuriousCfgM.

Lemma world_plain_original_is_images :
  mkImage SrcO_zlib_zlib_uncompress3_fuzzer_repro.M.loaded_segments SrcO_zlib_zlib_uncompress3_fuzzer_repro.M.init_pc SrcO_zlib_zlib_uncompress3_fuzzer_repro.M.phdrs = Images.plain_original.
Proof. reflexivity. Qed.

Lemma world_plain_is_images :
  mkImage Src_zlib_zlib_uncompress3_fuzzer_repro.M.loaded_segments Src_zlib_zlib_uncompress3_fuzzer_repro.M.init_pc Src_zlib_zlib_uncompress3_fuzzer_repro.M.phdrs = Images.plain.
Proof. reflexivity. Qed.

Lemma world_ubsan_original_is_images :
  mkImage TgtO_zlib_uncompress3_fuzzer_ubsan.M.loaded_segments TgtO_zlib_uncompress3_fuzzer_ubsan.M.init_pc TgtO_zlib_uncompress3_fuzzer_ubsan.M.phdrs = Images.ubsan_original.
Proof. reflexivity. Qed.

Lemma world_ubsan_is_images :
  mkImage Tgt_zlib_uncompress3_fuzzer_ubsan.M.loaded_segments Tgt_zlib_uncompress3_fuzzer_ubsan.M.init_pc Tgt_zlib_uncompress3_fuzzer_ubsan.M.phdrs = Images.ubsan.
Proof. reflexivity. Qed.

Lemma world_classifier_b_ubsan_is_images :
  mkImage Clb_zlib_uncompress3_fuzzer_ubsan.M.loaded_segments Clb_zlib_uncompress3_fuzzer_ubsan.M.init_pc Clb_zlib_uncompress3_fuzzer_ubsan.M.phdrs = Images.classifier_b_ubsan.
Proof. reflexivity. Qed.

Theorem ubsan_cb_sound_holds : Statements.ubsan_cb_sound.
Proof.
  unfold Statements.ubsan_cb_sound. rewrite <- world_plain_original_is_images, <- world_plain_is_images, <- world_ubsan_original_is_images, <- world_ubsan_is_images, <- world_classifier_b_ubsan_is_images.
  apply OSSVerify.Core.ClassifierShapes.classifies_patch_diff_sound_of_exact. rewrite OSSVerify.Core.ClassifierShapes.classifies_patch_diff_is_lps.
  exact ((OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.AgreeW.R26U.cb_iff SpuriousCfgM.cfg OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.AgreeW.R26U.x1_srco_tgt (OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.Thm_uncompress3_ubsan_mr.thm_of_lib (@OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.I8S.S_TopI.zlib_contract_S8) (@OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.I8U.T_TopI.zlib_contract_U8)) OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.AgreeW.R26U.x2_src_tgto)).
Qed.
