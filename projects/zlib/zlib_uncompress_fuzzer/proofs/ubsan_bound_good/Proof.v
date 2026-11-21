(* SPDX-License-Identifier: MIT *)
(** [Statements.ubsan_bound_good], from a theorem of this proof library.  The library states that theorem over
    its own names for the memory images; the alias texts in its World folder make each of them the
    repository's image of the same build, which [world_*_is_images] below checks by computation.
    The library's theorem is the entry itself, at the bound written below. *)
From Stdlib Require Import QArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import MemImageType.
Require LinuxProcessSemantics.LinuxProcessSem.Run LinuxProcessSemantics.EquivalenceDefinition.Equivalence.
Require OSSVerify.Core.Shapes OSSVerify.Core.ClassifierShapes.
From OSSVerify.zlib.zlib_uncompress_fuzzer Require Statements Images.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.World Require Cla_zlib_uncompress_fuzzer_ubsan W_aefw2_zlib_zlib_uncompress_fuzzer.
Require OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.ClsW.Rows.R_zlib_uncompress_fuzzer_ubsan.

Definition b_zlib_uncompress_fuzzer_ubsan_bound_good : Q := 0%Q.

Lemma world_classifier_a_ubsan_is_images :
  mkImage Cla_zlib_uncompress_fuzzer_ubsan.M.loaded_segments Cla_zlib_uncompress_fuzzer_ubsan.M.init_pc Cla_zlib_uncompress_fuzzer_ubsan.M.phdrs = Images.classifier_a_ubsan.
Proof. reflexivity. Qed.

Theorem ubsan_bound_good_holds : Statements.ubsan_bound_good (0 # 1).
Proof.
  unfold Statements.ubsan_bound_good. rewrite <- world_classifier_a_ubsan_is_images.
  rewrite OSSVerify.Core.Shapes.classifier_rejects_at_most_is_lps.
  exact ((OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_agrees_alloc_forced_only.ClsW.Rows.R_zlib_uncompress_fuzzer_ubsan.bound_good b_zlib_uncompress_fuzzer_ubsan_bound_good eq_refl)).
Qed.
