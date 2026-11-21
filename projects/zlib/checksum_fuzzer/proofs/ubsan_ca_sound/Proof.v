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
From OSSVerify.zlib.checksum_fuzzer Require Statements Images.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_ca_sound.World Require Cla_checksum_fuzzer_ubsan SrcO_zlib_checksum_fuzzer_repro TgtO_checksum_fuzzer_ubsan.
Require OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_ca_sound.ClsW.Rows.R_checksum_fuzzer_ubsan OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_ca_sound.S0Fuzz OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_ca_sound.Thm_checksum_ubsan_mr OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_ca_sound.U0Fuzz.

Module SpuriousCfgM <: LinuxProcessSemantics.EquivalenceDefinition.Equivalence.SPURIOUS_CFG.
  Definition cfg := LinuxProcessSemantics.LinuxProcessSem.Run.mkSpuriousCfg false true true true true true.
End SpuriousCfgM.

Lemma world_plain_original_is_images :
  mkImage SrcO_zlib_checksum_fuzzer_repro.M.loaded_segments SrcO_zlib_checksum_fuzzer_repro.M.init_pc SrcO_zlib_checksum_fuzzer_repro.M.phdrs = Images.plain_original.
Proof. reflexivity. Qed.

Lemma world_ubsan_original_is_images :
  mkImage TgtO_checksum_fuzzer_ubsan.M.loaded_segments TgtO_checksum_fuzzer_ubsan.M.init_pc TgtO_checksum_fuzzer_ubsan.M.phdrs = Images.ubsan_original.
Proof. reflexivity. Qed.

Lemma world_classifier_a_ubsan_is_images :
  mkImage Cla_checksum_fuzzer_ubsan.M.loaded_segments Cla_checksum_fuzzer_ubsan.M.init_pc Cla_checksum_fuzzer_ubsan.M.phdrs = Images.classifier_a_ubsan.
Proof. reflexivity. Qed.

Theorem ubsan_ca_sound_holds : Statements.ubsan_ca_sound.
Proof.
  unfold Statements.ubsan_ca_sound. rewrite <- world_plain_original_is_images, <- world_ubsan_original_is_images, <- world_classifier_a_ubsan_is_images.
  apply OSSVerify.Core.ClassifierShapes.classifies_good_inputs_sound_of_classifies. rewrite OSSVerify.Core.Shapes.classifies_is_lps.
  exact ((OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_ca_sound.ClsW.Rows.R_checksum_fuzzer_ubsan.ca_iff SpuriousCfgM.cfg (OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_ca_sound.Thm_checksum_ubsan_mr.thm_of_fuzz (@OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_ca_sound.S0Fuzz.s0_fuzz) (@OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_ca_sound.U0Fuzz.u0_fuzz)))).
Qed.
