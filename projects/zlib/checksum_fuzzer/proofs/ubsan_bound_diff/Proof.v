(* SPDX-License-Identifier: MIT *)
(** [Statements.ubsan_bound_diff], from a theorem of this proof library.  The library states that theorem over
    its own names for the memory images; the alias texts in its World folder make each of them the
    repository's image of the same build, which [world_*_is_images] below checks by computation.
    The library's theorem is the entry itself, at the bound written below. *)
From Stdlib Require Import QArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import MemImageType.
Require LinuxProcessSemantics.LinuxProcessSem.Run LinuxProcessSemantics.EquivalenceDefinition.Equivalence.
Require OSSVerify.Core.Shapes OSSVerify.Core.ClassifierShapes.
From OSSVerify.zlib.checksum_fuzzer Require Statements Images.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_agrees_alloc_forced_only.World Require Clb_checksum_fuzzer_ubsan W_aefw2_zlib_checksum_fuzzer.
Require OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_agrees_alloc_forced_only.ClsW.Rows.R_checksum_fuzzer_ubsan.

Definition b_checksum_fuzzer_ubsan_bound_diff : Q := 0%Q.

Lemma world_classifier_b_ubsan_is_images :
  mkImage Clb_checksum_fuzzer_ubsan.M.loaded_segments Clb_checksum_fuzzer_ubsan.M.init_pc Clb_checksum_fuzzer_ubsan.M.phdrs = Images.classifier_b_ubsan.
Proof. reflexivity. Qed.

Theorem ubsan_bound_diff_holds : Statements.ubsan_bound_diff (0 # 1).
Proof.
  unfold Statements.ubsan_bound_diff. rewrite <- world_classifier_b_ubsan_is_images.
  rewrite OSSVerify.Core.Shapes.classifier_rejects_at_most_is_lps.
  exact ((OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_agrees_alloc_forced_only.ClsW.Rows.R_checksum_fuzzer_ubsan.bound_diff b_checksum_fuzzer_ubsan_bound_diff eq_refl)).
Qed.
