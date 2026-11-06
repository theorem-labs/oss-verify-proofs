(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YK11 YK0p YK0s YK15 YQ0b YI00 YI02.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YI1i YP14 YI08 YI0c.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YG10.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YK05 YA0i YA0l.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import
YG00 YG0a YG01 YG0h YG0u YG0d YC04.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YB0z YF8z YC1d YC1a YC1b.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YN05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Open Scope Z_scope.
From OSSVerify.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YG0n YG0t YC4u.
Section a. Context {fx : YK11.FPState} {rc : YN05.RunCeil}.
Section b.
Variable B : asyms.
Definition tfree_tree_specV : Prop :=
forall (d : nat) ly S W (regs : bvmap 5 word) mem md ch (t : tree) (rest : list (Z * Z)),
(tree_height t <= d)%nat ->
afn_pre trasegs B (FDT_STK (Z.of_nat d)) ly S W regs mem md ch ->
In (raZ regs :: spine ch) CTX_free_decision_tree ->
getr regs 10 = w64 (troot t) ->
tree_at trasegs (mrestrict (w_H W) mem) t ->
Permutation (ablocks B ly S) (tree_blocks t ++ rest) ->
bud_ok S (Z.of_nat (length (tree_nodes t))) 1 (2 ^ 17) (HULL_UNIT + 2 ^ 24) ->
SRr trasegs W (cfg_at trasegs A_free_decision_tree regs mem md)
(apost_base B (FDT_STK (Z.of_nat d)) (ablocks_fp (tree_blocks t)) regs ly S W mem md (Z.of_nat (length (tree_nodes t)))
(fun ly' S' W' regs' mem' md' => Permutation (ablocks B ly' S') rest /\ bud_le S S' (Z.of_nat (length (tree_nodes t))) 0 0 0)).
End b.
End a.
