(* SPDX-License-Identifier: MIT *)
(** [Statements.asan_agrees_alloc_forced_only], from a theorem of this proof library.  The library states that theorem over
    its own names for the memory images; the alias texts in its World folder make each of them the
    repository's image of the same build, which [world_*_is_images] below checks by computation. *)
From LinuxProcessSemantics.LinuxProcessSem Require Import MemImageType.
From OSSVerify.zlib.checksum_fuzzer Require Statements Images.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.asan_agrees_alloc_forced_only.World Require Src_zlib_checksum_fuzzer_repro Tgt_checksum_fuzzer_asan.
Require OSSVerify.Proofs.zlib.checksum_fuzzer.lib.asan_agrees_alloc_forced_only.AsanW.AMain_final.

Lemma world_plain_is_images :
  mkImage Src_zlib_checksum_fuzzer_repro.M.loaded_segments Src_zlib_checksum_fuzzer_repro.M.init_pc Src_zlib_checksum_fuzzer_repro.M.phdrs = Images.plain.
Proof. reflexivity. Qed.

Lemma world_asan_is_images :
  mkImage Tgt_checksum_fuzzer_asan.M.loaded_segments Tgt_checksum_fuzzer_asan.M.init_pc Tgt_checksum_fuzzer_asan.M.phdrs = Images.asan.
Proof. reflexivity. Qed.

Theorem asan_agrees_alloc_forced_only_holds : Statements.asan_agrees_alloc_forced_only.
Proof.
  unfold Statements.asan_agrees_alloc_forced_only. rewrite <- world_plain_is_images, <- world_asan_is_images.
  exact ((OSSVerify.Proofs.zlib.checksum_fuzzer.lib.asan_agrees_alloc_forced_only.AsanW.AMain_final.base_asan_closed)).
Qed.
