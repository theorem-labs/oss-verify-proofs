(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (AT_EXECFN): changed envp_words, envp_block, length_envp_words, length_envp_block; added top, efn; removed sp. *)
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require Import YK11 YK0h YK0i YK14 YK1a YK1b YK15 YK0n YP0n.
From OSSVerify.Proofs.cgif.cgif_file_fuzzer.lib Require Import YP0m YP09 YP02 YP0l YP0k YP06 YP03 YP08 YP04 YL02 YN3u.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Open Scope bv_scope.
Open Scope Z_scope.
Definition envp_words (top : word) (argv envp : list (list byte)) (efn : list byte) : list word :=
fst (string_addrs (cat_env_base top argv envp efn) envp) ++ [Z_to_bv 64 0].
Definition envp_block (top : word) (argv envp : list (list byte)) (efn : list byte) : list byte :=
flat_map word_le8 (envp_words top argv envp efn).
Section e.
Variable top : word.
Variable argv envp : list (list byte).
Variable efn : list byte.
Lemma length_envp_words : length (envp_words top argv envp efn) = (length envp + 1)%nat.
Proof. unfold envp_words. rewrite length_app, length_string_addrs_fst. reflexivity. Qed.
Lemma length_envp_block : length (envp_block top argv envp efn) = (8 * length envp + 8)%nat.
Proof. unfold envp_block. rewrite length_flat_map_le8, length_envp_words. lia. Qed.
End e.