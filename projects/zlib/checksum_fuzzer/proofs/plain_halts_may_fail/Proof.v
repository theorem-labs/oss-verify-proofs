(* SPDX-License-Identifier: MIT *)
(** [Statements.plain_halts_may_fail], on the plain build this tree pins, from [halts_plain] of this harness's proof
    library (lib/plain_halts_any_exit/Thm_checksum_halts.v: every execution exits, whatever the environment refuses,
    any exit status).  The library states that theorem over its own name for the memory image; the alias text in its
    World folder makes it the repository's image of the plain build, which [world_plain_is_images] below checks by
    computation. *)
From LinuxProcessSemantics.LinuxProcessSem Require Import MemImageType.
From OSSVerify.zlib.checksum_fuzzer Require Statements Images.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.plain_halts_any_exit.World Require Src_zlib_checksum_fuzzer_repro.
Require OSSVerify.Proofs.zlib.checksum_fuzzer.lib.plain_halts_any_exit.Thm_checksum_halts.

Lemma world_plain_is_images :
  mkImage Src_zlib_checksum_fuzzer_repro.M.loaded_segments Src_zlib_checksum_fuzzer_repro.M.init_pc Src_zlib_checksum_fuzzer_repro.M.phdrs = Images.plain.
Proof. reflexivity. Qed.

Theorem plain_halts_may_fail_holds : Statements.plain_halts_may_fail.
Proof.
  unfold Statements.plain_halts_may_fail. rewrite <- world_plain_is_images.
  exact OSSVerify.Proofs.zlib.checksum_fuzzer.lib.plain_halts_any_exit.Thm_checksum_halts.halts_plain.
Qed.
