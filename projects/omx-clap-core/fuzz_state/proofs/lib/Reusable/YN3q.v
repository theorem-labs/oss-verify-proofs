(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1a YK1b YK15 YK0n YP0n.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YP0m YP09 YP02 YP0l YP0k YP06 YP03 YP08 YP04 YL02 YN3u.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Open Scope bv_scope.
Open Scope Z_scope.
Definition envp_words (sp : word) (argv envp : list (list byte)) : list word :=
fst (string_addrs (cat_env_base sp argv envp) envp) ++ [Z_to_bv 64 0].
Definition envp_block (sp : word) (argv envp : list (list byte)) : list byte :=
flat_map word_le8 (envp_words sp argv envp).
Section e.
Variable sp : word.
Variable argv envp : list (list byte).
Lemma length_envp_words : length (envp_words sp argv envp) = (length envp + 1)%nat.
Proof. unfold envp_words. rewrite length_app, length_string_addrs_fst. reflexivity. Qed.
Lemma length_envp_block : length (envp_block sp argv envp) = (8 * length envp + 8)%nat.
Proof. unfold envp_block. rewrite length_flat_map_le8, length_envp_words. lia. Qed.
End e.