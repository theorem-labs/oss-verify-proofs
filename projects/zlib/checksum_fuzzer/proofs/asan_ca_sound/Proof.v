(* SPDX-License-Identifier: MIT *)
(** [Statements.asan_ca_sound], from a theorem of this proof library.  The library states that theorem over
    its own names for the memory images; the alias texts in its World folder make each of them the
    repository's image of the same build, which [world_*_is_images] below checks by computation.
    The library's theorem says that the classifier decides exactly the inputs on which the
    originals agree; [ClassifierShapes.classifies_good_inputs_sound_of_classifies] gives the
    sound form of the entry. *)
From Stdlib Require Import QArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import MemImageType.
Require LinuxProcessSemantics.LinuxProcessSem.Run LinuxProcessSemantics.EquivalenceDefinition.Equivalence.
Require OSSVerify.Core.Shapes OSSVerify.Core.ClassifierShapes.
From OSSVerify.zlib.checksum_fuzzer Require Statements Images.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.asan_ca_sound.World Require Cla_checksum_fuzzer_asan SrcO_zlib_checksum_fuzzer_repro TgtO_checksum_fuzzer_asan.
Require OSSVerify.Proofs.zlib.checksum_fuzzer.lib.asan_ca_sound.AsanW.AMain_final OSSVerify.Proofs.zlib.checksum_fuzzer.lib.asan_ca_sound.ClsW.Rows.R_checksum_fuzzer_asan.

Module SpuriousCfgM <: LinuxProcessSemantics.EquivalenceDefinition.Equivalence.SPURIOUS_CFG.
  Definition cfg := LinuxProcessSemantics.LinuxProcessSem.Run.mkSpuriousCfg false true true true true true.
End SpuriousCfgM.

Lemma world_plain_original_is_images :
  mkImage SrcO_zlib_checksum_fuzzer_repro.M.loaded_segments SrcO_zlib_checksum_fuzzer_repro.M.init_pc SrcO_zlib_checksum_fuzzer_repro.M.phdrs = Images.plain_original.
Proof. reflexivity. Qed.

Lemma world_asan_original_is_images :
  mkImage TgtO_checksum_fuzzer_asan.M.loaded_segments TgtO_checksum_fuzzer_asan.M.init_pc TgtO_checksum_fuzzer_asan.M.phdrs = Images.asan_original.
Proof. reflexivity. Qed.

Lemma world_classifier_a_asan_is_images :
  mkImage Cla_checksum_fuzzer_asan.M.loaded_segments Cla_checksum_fuzzer_asan.M.init_pc Cla_checksum_fuzzer_asan.M.phdrs = Images.classifier_a_asan.
Proof. reflexivity. Qed.

Theorem asan_ca_sound_holds : Statements.asan_ca_sound.
Proof.
  unfold Statements.asan_ca_sound. rewrite <- world_plain_original_is_images, <- world_asan_original_is_images, <- world_classifier_a_asan_is_images.
  apply OSSVerify.Core.ClassifierShapes.classifies_good_inputs_sound_of_classifies. rewrite OSSVerify.Core.Shapes.classifies_is_lps.
  exact ((OSSVerify.Proofs.zlib.checksum_fuzzer.lib.asan_ca_sound.ClsW.Rows.R_checksum_fuzzer_asan.ca_iff SpuriousCfgM.cfg (OSSVerify.Proofs.zlib.checksum_fuzzer.lib.asan_ca_sound.AsanW.AMain_final.base_asan_plain_closed))).
Qed.
