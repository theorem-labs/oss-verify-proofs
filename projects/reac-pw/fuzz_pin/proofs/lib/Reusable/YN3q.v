(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/YN3q.v, with its module paths changed. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/libreac/fuzz_knock/lib/Reusable/YN3q.v (fuzz_knock's released ASan tree); module paths changed to reac-pw/fuzz_pin. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (the launch's ProcInput, mmap base and entry draw; the launch's string area with the exec file name); internal commit ids in comments replaced by public commits or removed. *)
From OSSVerify.Proofs.reac_pw.fuzz_pin.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_pin.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1a YK1b YK15 YK0n YP0n.
From OSSVerify.Proofs.reac_pw.fuzz_pin.lib.Reusable Require Import YP0m YP09 YP02 YP0l YP0k YP06 YP03 YP08 YP04 YL02 YN3u.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Open Scope bv_scope.
Open Scope Z_scope.
(* 75d69e00: [cat_env_base] takes FOUR arguments (theories/Common/CatExec.v:416-418,
   `(top : word) (av ev : list (list byte)) (execfn : list byte)`), where f1006fe8 took three
   (theories/Common/CatExec.v:304).  Its first argument is the stack VMA's END, not [sp]: at this
   revision the strings sit at the TOP of the block, above the AT_RANDOM bytes and the
   arch_align_stack pad (CatExec.v:403-415).  The already-ported twin in this tree is
   Reusable/YN3e.v:91, which passes (ed_top rnd) (in_argv inp) (in_envp inp) (in_execfn inp). *)
Definition envp_words (top : word) (argv envp : list (list byte)) (execfn : list byte) : list word :=
fst (string_addrs (cat_env_base top argv envp execfn) envp) ++ [Z_to_bv 64 0].
Definition envp_block (top : word) (argv envp : list (list byte)) (execfn : list byte) : list byte :=
flat_map word_le8 (envp_words top argv envp execfn).
Section e.
Variable top : word.
Variable argv envp : list (list byte).
Variable execfn : list byte.
Lemma length_envp_words : length (envp_words top argv envp execfn) = (length envp + 1)%nat.
Proof. unfold envp_words. rewrite length_app, length_string_addrs_fst. reflexivity. Qed.
Lemma length_envp_block : length (envp_block top argv envp execfn) = (8 * length envp + 8)%nat.
Proof. unfold envp_block. rewrite length_flat_map_le8, length_envp_words. lia. Qed.
End e.