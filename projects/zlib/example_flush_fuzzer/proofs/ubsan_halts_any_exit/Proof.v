(* SPDX-License-Identifier: MIT *)
(** [Statements.ubsan_halts_any_exit], from a theorem of this proof library.  The library states that theorem over
    its own names for the memory images; the alias texts in its World folder make each of them the
    repository's image of the same build, which [world_*_is_images] below checks by computation. *)
From LinuxProcessSemantics.LinuxProcessSem Require Import MemImageType.
From OSSVerify.zlib.example_flush_fuzzer Require Statements Images.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.World Require Tgt_example_flush_fuzzer_ubsan.
Require OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.FO.Thm_halts_ubsan_fo.

Lemma world_ubsan_is_images :
  mkImage Tgt_example_flush_fuzzer_ubsan.M.loaded_segments Tgt_example_flush_fuzzer_ubsan.M.init_pc Tgt_example_flush_fuzzer_ubsan.M.phdrs = Images.ubsan.
Proof. reflexivity. Qed.

Theorem ubsan_halts_any_exit_holds : Statements.ubsan_halts_any_exit.
Proof.
  unfold Statements.ubsan_halts_any_exit. rewrite <- world_ubsan_is_images.
  exact ((OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.FO.Thm_halts_ubsan_fo.halts_ubsan_forced_only)).
Qed.
