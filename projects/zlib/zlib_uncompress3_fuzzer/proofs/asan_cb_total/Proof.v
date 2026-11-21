(* SPDX-License-Identifier: MIT *)
(** [Statements.asan_cb_total], from a theorem of this proof library.  The library states that theorem over
    its own names for the memory images; the alias texts in its World folder make each of them the
    repository's image of the same build, which [world_*_is_images] below checks by computation.
    The library's theorem says that the classifier answers yes or no;
    [ClassifierShapes.classifier_total3_of_total] gives the three-answer form of the entry. *)
From Stdlib Require Import QArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import MemImageType.
Require LinuxProcessSemantics.LinuxProcessSem.Run LinuxProcessSemantics.EquivalenceDefinition.Equivalence.
Require OSSVerify.Core.Shapes OSSVerify.Core.ClassifierShapes.
From OSSVerify.zlib.zlib_uncompress3_fuzzer Require Statements Images.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_agrees_alloc_forced_only.World Require Clb_zlib_uncompress3_fuzzer_asan.
Require OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_agrees_alloc_forced_only.ClsW.Rows.R_zlib_uncompress3_fuzzer_asan.

Lemma world_classifier_b_asan_is_images :
  mkImage Clb_zlib_uncompress3_fuzzer_asan.M.loaded_segments Clb_zlib_uncompress3_fuzzer_asan.M.init_pc Clb_zlib_uncompress3_fuzzer_asan.M.phdrs = Images.classifier_b_asan.
Proof. reflexivity. Qed.

Theorem asan_cb_total_holds : Statements.asan_cb_total.
Proof.
  unfold Statements.asan_cb_total. rewrite <- world_classifier_b_asan_is_images.
  apply OSSVerify.Core.ClassifierShapes.classifier_total3_of_total. rewrite OSSVerify.Core.ClassifierShapes.classifier_total_is_lps.
  exact (OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_agrees_alloc_forced_only.ClsW.Rows.R_zlib_uncompress3_fuzzer_asan.cb_total).
Qed.
