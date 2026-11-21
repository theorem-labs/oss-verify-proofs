(* SPDX-License-Identifier: MIT *)
(** [Statements.plain_halts], from a theorem of this proof library: the halting walk of [plain_halts_any_exit]
    with its exit set narrowed to [Exits.ok_or_refused] (every end of the specification that walk realizes exits
    with status 0 or 2).  The library states that theorem over its own names for the memory images; the alias
    texts in its World folder make each of them the repository's image of the same build, which
    [world_plain_is_images] below checks by computation. *)
From LinuxProcessSemantics.LinuxProcessSem Require Import MemImageType.
From OSSVerify.zlib.checksum_fuzzer Require Statements Images.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.plain_halts_any_exit.World Require Src_zlib_checksum_fuzzer_repro.
Require OSSVerify.Proofs.zlib.checksum_fuzzer.lib.plain_halts.Thm_halts_fo_okr.

Lemma world_plain_is_images :
  mkImage Src_zlib_checksum_fuzzer_repro.M.loaded_segments Src_zlib_checksum_fuzzer_repro.M.init_pc Src_zlib_checksum_fuzzer_repro.M.phdrs = Images.plain.
Proof. reflexivity. Qed.

Theorem plain_halts_holds : Statements.plain_halts.
Proof.
  unfold Statements.plain_halts. rewrite <- world_plain_is_images.
  exact ((OSSVerify.Proofs.zlib.checksum_fuzzer.lib.plain_halts.Thm_halts_fo_okr.halts_plain_okr_forced_only)).
Qed.
