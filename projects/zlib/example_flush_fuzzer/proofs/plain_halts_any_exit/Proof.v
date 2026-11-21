(* SPDX-License-Identifier: MIT *)
(** [Statements.plain_halts_any_exit], from a theorem of this proof library.  The library states that theorem over
    its own names for the memory images; the alias texts in its World folder make each of them the
    repository's image of the same build, which [world_*_is_images] below checks by computation. *)
From LinuxProcessSemantics.LinuxProcessSem Require Import MemImageType.
From OSSVerify.zlib.example_flush_fuzzer Require Statements Images.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_plain.World Require Src_zlib_example_flush_fuzzer_repro.
Require OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_plain.FO.Thm_halts_fo.

Lemma world_plain_is_images :
  mkImage Src_zlib_example_flush_fuzzer_repro.M.loaded_segments Src_zlib_example_flush_fuzzer_repro.M.init_pc Src_zlib_example_flush_fuzzer_repro.M.phdrs = Images.plain.
Proof. reflexivity. Qed.

Theorem plain_halts_any_exit_holds : Statements.plain_halts_any_exit.
Proof.
  unfold Statements.plain_halts_any_exit. rewrite <- world_plain_is_images.
  exact ((OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_plain.FO.Thm_halts_fo.halts_plain_forced_only)).
Qed.
