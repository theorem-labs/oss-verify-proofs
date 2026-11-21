(* SPDX-License-Identifier: MIT *)
(** [Statements.asan_ubsan_halts_any_exit], from a theorem of this proof library.  The library states that theorem over
    its own names for the memory images; the alias texts in its World folder make each of them the
    repository's image of the same build, which [world_*_is_images] below checks by computation. *)
From LinuxProcessSemantics.LinuxProcessSem Require Import MemImageType.
From OSSVerify.zlib.zlib_uncompress3_fuzzer Require Statements Images.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.zlib_uncompress3_fuzzer_asan_ubsan.World Require Tgt_zlib_uncompress3_fuzzer_both.
Require OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.zlib_uncompress3_fuzzer_asan_ubsan.BaseBothU3.

Lemma world_asan_ubsan_is_images :
  mkImage Tgt_zlib_uncompress3_fuzzer_both.M.loaded_segments Tgt_zlib_uncompress3_fuzzer_both.M.init_pc Tgt_zlib_uncompress3_fuzzer_both.M.phdrs = Images.asan_ubsan.
Proof. reflexivity. Qed.

Theorem asan_ubsan_halts_any_exit_holds : Statements.asan_ubsan_halts_any_exit.
Proof.
  unfold Statements.asan_ubsan_halts_any_exit. rewrite <- world_asan_ubsan_is_images.
  exact ((OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.zlib_uncompress3_fuzzer_asan_ubsan.BaseBothU3.halts_both_u3)).
Qed.
