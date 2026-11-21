(* SPDX-License-Identifier: MIT *)
(** [Statements.asan_ubsan_bound_diff], from a theorem of this proof library.  The library states that theorem over
    its own names for the memory images; the alias texts in its World folder make each of them the
    repository's image of the same build, which [world_*_is_images] below checks by computation.
    The library's theorem is the entry itself, at the bound written below. *)
From Stdlib Require Import QArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import MemImageType.
Require LinuxProcessSemantics.LinuxProcessSem.Run LinuxProcessSemantics.EquivalenceDefinition.Equivalence.
Require OSSVerify.Core.Shapes OSSVerify.Core.ClassifierShapes.
From OSSVerify.zlib.zlib_uncompress_fuzzer Require Statements Images.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.World Require Clb_zlib_uncompress_fuzzer_both W_aefw2_zlib_zlib_uncompress_fuzzer.
Require OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.ClsW.Rows.R_zlib_uncompress_fuzzer_both.

Definition b_zlib_uncompress_fuzzer_both_bound_diff : Q := 0%Q.

Lemma world_classifier_b_asan_ubsan_is_images :
  mkImage Clb_zlib_uncompress_fuzzer_both.M.loaded_segments Clb_zlib_uncompress_fuzzer_both.M.init_pc Clb_zlib_uncompress_fuzzer_both.M.phdrs = Images.classifier_b_asan_ubsan.
Proof. reflexivity. Qed.

Theorem asan_ubsan_bound_diff_holds : Statements.asan_ubsan_bound_diff (0 # 1).
Proof.
  unfold Statements.asan_ubsan_bound_diff. rewrite <- world_classifier_b_asan_ubsan_is_images.
  rewrite OSSVerify.Core.Shapes.classifier_rejects_at_most_is_lps.
  exact ((OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.ClsW.Rows.R_zlib_uncompress_fuzzer_both.bound_diff b_zlib_uncompress_fuzzer_both_bound_diff eq_refl)).
Qed.
