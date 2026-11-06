(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/YCfl.v (donor image sha256 1c29845fe605), with its module paths changed and its addresses moved to libreac/fuzz_scene's ASan build. *)
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Reusable Require Import YK11 YK0s YP09.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Reusable Require Import YK04 YA0i YA0n.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d. From OSSVerify.Proofs.libreac.fuzz_scene.lib.Reusable Require Import YCe5.

From OSSVerify.Proofs.libreac.fuzz_scene.lib.AU Require Import YB1v YCeg.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Reusable Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Open Scope Z_scope.
Definition A_LLVMF : Z := 0x828a4.
Definition RA_LLVMF : Z := 0x827a0.
Definition A_EMPTY : Z := 0x5d6160.
Definition EV_LIB : Z := 2000.
Definition LIVE_LIB : Z := 2 ^ 33.
Definition LLVMF_STK : Z := 32768.
Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Definition tfib_lib_contract (B : asyms) : Prop :=
forall ly S (W : world tfibsegs) (regs : bvmap 5 word) mem md p n,
afn_pre tfibsegs B LLVMF_STK ly S W regs mem md [] ->
raZ regs = RA_LLVMF ->
getr regs 10 = w64 p -> getr regs 11 = w64 n ->
((n = 0 /\ p = A_EMPTY) \/ (0 < n < 2 ^ 26 /\ In (p, n) (ablocks B ly S))) ->
frames S = [] -> st_nev S + EV_LIB <= EV_MAX -> blocks_bytes S + LIVE_LIB <= LIVE_MAX ->
arodata_ok B (aview tfibsegs (w_H W) mem) ->
SRr tfibsegs W (cfg_at tfibsegs A_LLVMF regs mem md)
(fun W' c' => exists ly' S' regs' mem' md' k,
c' = cfg_at tfibsegs RA_LLVMF regs' mem' md' /\
ajournal tfibsegs B LLVMF_STK (spZ regs) [] ly S W mem md [] ly' S' W' mem' md' k /\ k <= EV_LIB /\
aregs_preserved regs regs' /\ getr regs' 10 = w64 0 /\
exists leak, Permutation (ablocks B ly' S') (leak ++ ablocks B ly S) /\
(leak = [] \/ exists a m, leak = [(a, m)] /\ 0 <= m < 3 * 2 ^ 16)).
End b.
