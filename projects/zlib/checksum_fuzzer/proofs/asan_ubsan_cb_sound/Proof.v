(* SPDX-License-Identifier: MIT *)
(** [Statements.asan_ubsan_cb_sound], from a theorem of this proof library.  The library states that theorem over
    its own names for the memory images; the alias texts in its World folder make each of them the
    repository's image of the same build, which [world_*_is_images] below checks by computation.
    The library's theorem says that the classifier decides exactly the inputs on which each
    build agrees with its original; [ClassifierShapes.classifies_patch_diff_sound_of_exact]
    gives the sound form of the entry. *)
From Stdlib Require Import QArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import MemImageType.
Require LinuxProcessSemantics.LinuxProcessSem.Run LinuxProcessSemantics.EquivalenceDefinition.Equivalence.
Require OSSVerify.Core.Shapes OSSVerify.Core.ClassifierShapes.
From OSSVerify.zlib.checksum_fuzzer Require Statements Images.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.asan_ubsan_ca_sound.World Require Clb_checksum_fuzzer_both SrcO_zlib_checksum_fuzzer_repro Src_zlib_checksum_fuzzer_repro TgtO_checksum_fuzzer_both Tgt_checksum_fuzzer_both.
Require OSSVerify.Proofs.zlib.checksum_fuzzer.lib.asan_ubsan_ca_sound.BothW.AMain_final OSSVerify.Proofs.zlib.checksum_fuzzer.lib.asan_ubsan_ca_sound.ClsW.Rows.R_checksum_fuzzer_both.

Module SpuriousCfgM <: LinuxProcessSemantics.EquivalenceDefinition.Equivalence.SPURIOUS_CFG.
  Definition cfg := LinuxProcessSemantics.LinuxProcessSem.Run.mkSpuriousCfg false true true true true true.
End SpuriousCfgM.

Lemma world_plain_original_is_images :
  mkImage SrcO_zlib_checksum_fuzzer_repro.M.loaded_segments SrcO_zlib_checksum_fuzzer_repro.M.init_pc SrcO_zlib_checksum_fuzzer_repro.M.phdrs = Images.plain_original.
Proof. reflexivity. Qed.

Lemma world_plain_is_images :
  mkImage Src_zlib_checksum_fuzzer_repro.M.loaded_segments Src_zlib_checksum_fuzzer_repro.M.init_pc Src_zlib_checksum_fuzzer_repro.M.phdrs = Images.plain.
Proof. reflexivity. Qed.

Lemma world_asan_ubsan_original_is_images :
  mkImage TgtO_checksum_fuzzer_both.M.loaded_segments TgtO_checksum_fuzzer_both.M.init_pc TgtO_checksum_fuzzer_both.M.phdrs = Images.asan_ubsan_original.
Proof. reflexivity. Qed.

Lemma world_asan_ubsan_is_images :
  mkImage Tgt_checksum_fuzzer_both.M.loaded_segments Tgt_checksum_fuzzer_both.M.init_pc Tgt_checksum_fuzzer_both.M.phdrs = Images.asan_ubsan.
Proof. reflexivity. Qed.

Lemma world_classifier_b_asan_ubsan_is_images :
  mkImage Clb_checksum_fuzzer_both.M.loaded_segments Clb_checksum_fuzzer_both.M.init_pc Clb_checksum_fuzzer_both.M.phdrs = Images.classifier_b_asan_ubsan.
Proof. reflexivity. Qed.

Theorem asan_ubsan_cb_sound_holds : Statements.asan_ubsan_cb_sound.
Proof.
  unfold Statements.asan_ubsan_cb_sound. rewrite <- world_plain_original_is_images, <- world_plain_is_images, <- world_asan_ubsan_original_is_images, <- world_asan_ubsan_is_images, <- world_classifier_b_asan_ubsan_is_images.
  apply OSSVerify.Core.ClassifierShapes.classifies_patch_diff_sound_of_exact. rewrite OSSVerify.Core.ClassifierShapes.classifies_patch_diff_is_lps.
  exact ((OSSVerify.Proofs.zlib.checksum_fuzzer.lib.asan_ubsan_ca_sound.ClsW.Rows.R_checksum_fuzzer_both.cb_iff SpuriousCfgM.cfg (OSSVerify.Proofs.zlib.checksum_fuzzer.lib.asan_ubsan_ca_sound.BothW.AMain_final.base_both_plain_closed))).
Qed.
