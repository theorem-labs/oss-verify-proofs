(* SPDX-License-Identifier: MIT *)
(** [Statements.asan_ubsan_ca_total], from a theorem of this proof library.  The library states that theorem over
    its own names for the memory images; the alias texts in its World folder make each of them the
    repository's image of the same build, which [world_*_is_images] below checks by computation.
    The library's theorem says that the classifier answers yes or no;
    [ClassifierShapes.classifier_total3_of_total] gives the three-answer form of the entry. *)
From Stdlib Require Import QArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import MemImageType.
Require LinuxProcessSemantics.LinuxProcessSem.Run LinuxProcessSemantics.EquivalenceDefinition.Equivalence.
Require OSSVerify.Core.Shapes OSSVerify.Core.ClassifierShapes.
From OSSVerify.zlib.zlib_uncompress3_fuzzer Require Statements Images.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.World Require Cla_zlib_uncompress3_fuzzer_both.
Require OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.ClsW.Rows.R_zlib_uncompress3_fuzzer_both.

Lemma world_classifier_a_asan_ubsan_is_images :
  mkImage Cla_zlib_uncompress3_fuzzer_both.M.loaded_segments Cla_zlib_uncompress3_fuzzer_both.M.init_pc Cla_zlib_uncompress3_fuzzer_both.M.phdrs = Images.classifier_a_asan_ubsan.
Proof. reflexivity. Qed.

Theorem asan_ubsan_ca_total_holds : Statements.asan_ubsan_ca_total.
Proof.
  unfold Statements.asan_ubsan_ca_total. rewrite <- world_classifier_a_asan_ubsan_is_images.
  apply OSSVerify.Core.ClassifierShapes.classifier_total3_of_total. rewrite OSSVerify.Core.ClassifierShapes.classifier_total_is_lps.
  exact (OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.ClsW.Rows.R_zlib_uncompress3_fuzzer_both.ca_total).
Qed.
