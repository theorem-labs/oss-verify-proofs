(* SPDX-License-Identifier: MIT *)
(** [Statements.asan_halts_any_exit], from a theorem of this proof library.  The library states that theorem over
    its own names for the memory images; the alias texts in its World folder make each of them the
    repository's image of the same build, which [world_*_is_images] below checks by computation. *)
From LinuxProcessSemantics.LinuxProcessSem Require Import MemImageType.
From OSSVerify.zlib.zlib_uncompress_fuzzer Require Statements Images.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_halts_any_exit.World Require Tgt_zlib_uncompress_fuzzer_asan.
Require OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_halts_any_exit.BaseAsanU1.

Lemma world_asan_is_images :
  mkImage Tgt_zlib_uncompress_fuzzer_asan.M.loaded_segments Tgt_zlib_uncompress_fuzzer_asan.M.init_pc Tgt_zlib_uncompress_fuzzer_asan.M.phdrs = Images.asan.
Proof. reflexivity. Qed.

Theorem asan_halts_any_exit_holds : Statements.asan_halts_any_exit.
Proof.
  unfold Statements.asan_halts_any_exit. rewrite <- world_asan_is_images.
  exact ((OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_halts_any_exit.BaseAsanU1.halts_asan_u1)).
Qed.
