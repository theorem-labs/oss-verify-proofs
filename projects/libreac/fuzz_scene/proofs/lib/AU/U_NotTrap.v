(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: U_not_atom and kill_not_trap copied from proofs/cgif/cgif_file_fuzzer/lib/YCh0.v:345
   and :449-456 (ASan copy lib/A/ACh0.v:450) for fuzz_scene, with its module paths changed; the donor's tactic was written
   for cgif's env slot 32, this copy reads the slot out of the goal instead, so the file holds no image constant. *)
(* What it is for: the UBSan guards of the shape [not rX; bltu rX, rK -> unimp] that scene's asan-ubsan image places
   before an object walk (check_step 0x835d8 / 0x835e0, reac_ctrl_checksum_verify 0x83a18,
   reac_ctrl_build_scene_step 0x83d14). The symbolic engine gives [~p] no range, so the branch stays open; here
   [branch_taken BC_LTU (~ SOff n 0) (SLit k) = true] is turned into [2 ^ 64 - 1 - g <? k = true] and refuted from the
   per-site object bound [0 <= g /\ g + k < 2 ^ 64], which the walk carries. *)
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Reusable Require Import YP0m YP0e YP03 YN3v YI04 YI08.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.

(* cgif lib/YCh0.v:345-350, verbatim. *)
Lemma U_not_atom : forall E n v, ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 ->
U E (SAlu ALU_XOR (SOff n 0) (SLit (-1))) = 2 ^ 64 - 1 - v.
Proof.
intros E n v Hn Hv. rewrite U_SAlu. cbn [zalu_raw]. rewrite (U_atom E n v Hn Hv). rewrite U_SLit.
change (zcanon (-1)) with (2 ^ 64 - 1). rewrite lxor_allones by lia. apply zcanon_id. unfold M64. lia.
Qed.

(* cgif lib/YCh0.v:449-456, with the env slot taken from the goal instead of the donor's literal 32.
   [kill_not_trap Hbase Hrange] closes any goal from a hypothesis
     H : branch_taken BC_LTU (sv_denot Ex (SAlu ALU_XOR (SOff n 0) (SLit k))) (sv_denot Ex (SLit k')) = true
   with k = -1, where
     Hbase  : ew E n = Z_to_bv 64 g      (E may be Ex itself or any prefix of it under ewset / havoc at slots <> n),
     Hrange : lia-provable 0 <= g and g + k' < 2 ^ 64 (e.g. [0 <= g /\ g + 9 < 2 ^ 64]).
   The slot n and the symbolic environment Ex are read out of H, so no address, listing or symbol of any image
   appears here. *)
Ltac kill_not_trap Hbase Hrange :=
lazymatch goal with H : branch_taken BC_LTU (sv_denot ?Ex (SAlu ALU_XOR (SOff ?n 0) (SLit (-1)))) (sv_denot _ (SLit ?k)) = true |- _ =>
exfalso; rewrite branch_ltu_U in H;
lazymatch type of Hbase with _ = Z_to_bv 64 ?g =>
rewrite (U_not_atom Ex n g) in H;
[ rewrite U_lit in H by (clear; lia); apply Z.ltb_lt in H; clear - H Hrange; lia
| cbn [ew ewset havoc Nat.eqb Nat.ltb Nat.leb nth Nat.sub]; rewrite ?ew_ewset_other by lia; rewrite ?ew_havoc_old by lia; exact Hbase
| clear - Hrange; lia ] end end.

(* Self-test: the guard of check_step 0x835d8 in the shape the engine produces it (ALIGN.md section 3: [~blk <u 9],
   the block base held in an env slot, read under the writes the walk has done to other slots), closed by the tactic. *)
Example kill_not_trap_check_step_835d8 :
forall (E : env) (w : bv 64) (g : Z),
ew E 32 = Z_to_bv 64 g -> 0 <= g /\ g + 9 < 2 ^ 64 ->
branch_taken BC_LTU (sv_denot (ewset E 14 w) (SAlu ALU_XOR (SOff 32 0) (SLit (-1))))
(sv_denot (ewset E 14 w) (SLit 9)) = true -> False.
Proof.
intros E w g Hbase Hrange H. kill_not_trap Hbase Hrange.
Qed.
Print Assumptions kill_not_trap_check_step_835d8.
