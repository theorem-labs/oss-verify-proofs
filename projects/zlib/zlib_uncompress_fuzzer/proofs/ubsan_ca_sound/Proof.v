(* SPDX-License-Identifier: MIT *)
(** [Statements.ubsan_ca_sound], from a theorem of this proof library.  The library states that theorem over
    its own names for the memory images; the alias texts in its World folder make each of them the
    repository's image of the same build, which [world_*_is_images] below checks by computation.
    The library's theorem says that the classifier decides exactly the inputs on which the
    originals agree; [ClassifierShapes.classifies_good_inputs_sound_of_classifies] gives the
    sound form of the entry. *)
From Stdlib Require Import QArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import MemImageType.
Require LinuxProcessSemantics.LinuxProcessSem.Run LinuxProcessSemantics.EquivalenceDefinition.Equivalence.
Require OSSVerify.Core.Shapes OSSVerify.Core.ClassifierShapes.
From OSSVerify.zlib.zlib_uncompress_fuzzer Require Statements Images.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.World Require Cla_zlib_uncompress_fuzzer_ubsan SrcO_zlib_zlib_uncompress_fuzzer_repro TgtO_zlib_uncompress_fuzzer_ubsan.
Require OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.AgreeW.R29U OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.I9S.S_TopI OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.I9U.T_TopI OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.Thm_uncompress_ubsan_mr.

Module SpuriousCfgM <: LinuxProcessSemantics.EquivalenceDefinition.Equivalence.SPURIOUS_CFG.
  Definition cfg := LinuxProcessSemantics.LinuxProcessSem.Run.mkSpuriousCfg false true true true true true.
End SpuriousCfgM.

Lemma world_plain_original_is_images :
  mkImage SrcO_zlib_zlib_uncompress_fuzzer_repro.M.loaded_segments SrcO_zlib_zlib_uncompress_fuzzer_repro.M.init_pc SrcO_zlib_zlib_uncompress_fuzzer_repro.M.phdrs = Images.plain_original.
Proof. reflexivity. Qed.

Lemma world_ubsan_original_is_images :
  mkImage TgtO_zlib_uncompress_fuzzer_ubsan.M.loaded_segments TgtO_zlib_uncompress_fuzzer_ubsan.M.init_pc TgtO_zlib_uncompress_fuzzer_ubsan.M.phdrs = Images.ubsan_original.
Proof. reflexivity. Qed.

Lemma world_classifier_a_ubsan_is_images :
  mkImage Cla_zlib_uncompress_fuzzer_ubsan.M.loaded_segments Cla_zlib_uncompress_fuzzer_ubsan.M.init_pc Cla_zlib_uncompress_fuzzer_ubsan.M.phdrs = Images.classifier_a_ubsan.
Proof. reflexivity. Qed.

Theorem ubsan_ca_sound_holds : Statements.ubsan_ca_sound.
Proof.
  unfold Statements.ubsan_ca_sound. rewrite <- world_plain_original_is_images, <- world_ubsan_original_is_images, <- world_classifier_a_ubsan_is_images.
  apply OSSVerify.Core.ClassifierShapes.classifies_good_inputs_sound_of_classifies. rewrite OSSVerify.Core.Shapes.classifies_is_lps.
  exact ((OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.AgreeW.R29U.ca_iff SpuriousCfgM.cfg (OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.Thm_uncompress_ubsan_mr.thm_of_lib (@OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.I9S.S_TopI.zlib_contract_S9) (@OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.I9U.T_TopI.zlib_contract_U9)))).
Qed.
