(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: from proofs/cgif/cgif_file_fuzzer/lib/AGjc.v (commit 30a1993588f, c5 + memnorm; file sha256 ef40d313555f) onto plugin-hostd/fuzz_reply's asan image (unstripped fuzz_reply.asan, sha256 d751b179ea49; pin 42c58610e125); module paths changed; taken by path: no numeral of it names an image address, none changed. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/plugin-hostd/fuzz_reply/lib/A/AGjc.v at commit 789778cb16f, with its module paths changed (lib.A to lib.B; the image twins A<r> to Y<r>), taken by path: no numeral of it names an image address that differs in fuzz_reply.asan-ubsan. *)
(* cgif_file's view facts for the hit-k walk (requests 0..48 bytes): from ARm of the allocator state at the memory mem0,
   the machine facts of the cached chunk at the top of the per-thread cache of class cl.
   The k path reuses AGiy unchanged: the cached-chunk facts do not depend on the size range (AGiy needs only
   0 <= n and from_primary n = true). Each lemma below is AGiy's lemma with AGiy's name, section variables and
   hypotheses in AGiy's order, and its statement is AGiy's text over the k hub's names (AGj6.Pv, PVv, Kv, SHBv, SKv,
   SSLOTv). These are definitionally equal to AGis's (the same bodies), so each proof is the AGiy lemma itself, and
   the k files see AGj6's constants in the statements. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s YO0d.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YP0j.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YN3v YI04.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK04 YA0i YA0n YA0o YA0p YA0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YG00 YG0a YG01 YG04 YG06 YG07 YG03 YG0f YG0v YG0n YG0d YG0s YG0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import YB1v YB1q YF0l YF0m YF0x YFl0.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YO0a.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import YB1w YE3d YFhy AGhy.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require AGj6 AGiy.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YM05.
Import ListNotations.
Local Set Warnings "-abstract-large-number".
Local Set Warnings "-notation-for-abbreviation".
Open Scope Z_scope.
Set Printing Depth 50. Set Printing Width 180.
Lemma In_combine_seq_last : forall (l0 : list Z) (x : Z) s, In ((s + length l0)%nat, x) (combine (seq s (length l0 + 1)) (l0 ++ [x])).
Proof. exact AGiy.In_combine_seq_last. Qed.
(* Every lemma below is abstracted over all the variables of its sections, in their declaration order (the
   argument lists are fixed by the section headers, as in AGiy). *)
Set Default Proof Using "All".
Section f. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Section h.
Variables (B : asyms) (W : world tfibsegs) (ly : alayout) (mem0 : word -> option byte).
Variables (n cl cnt v : Z) (S : astate) (l : list Z) (off : Z).
Let T : Z := ly_T ly.
Let SB : Z := ly_space ly.
Local Abbreviation Pv := (@AGj6.Pv ly cl).
Local Abbreviation PVv := (@AGj6.PVv ly cl cnt).
Local Abbreviation Kv := (@AGj6.Kv ly cl v).
Local Abbreviation SHBv := (@AGj6.SHBv).
Local Abbreviation SKv := (@AGj6.SKv ly cl v).
Local Abbreviation SSLOTv := (@AGj6.SSLOTv ly cl).
Hypothesis TS : TfibSyms B.
Hypothesis LY : layout_ok ly.
Hypothesis IMG : img_cover ly.
Hypothesis Hn0 : 0 <= n.
Hypothesis FP : from_primary n = true.
Hypothesis Hinited : st_cache_inited S = true.
Hypothesis Hcache : pc_chunks (cache S cl) = l ++ [off].
Hypothesis Hcl_class : cl = chunk_class n.
Hypothesis Hcnt_def : cnt = Z.of_nat (length (l ++ [off])).
Hypothesis Hoff_def : off = 16 * v.
Let rd0 : reader := aview tfibsegs (w_H W) mem0.
Let m0 := mrestrict (w_H W) mem0.
End h.
End f.
