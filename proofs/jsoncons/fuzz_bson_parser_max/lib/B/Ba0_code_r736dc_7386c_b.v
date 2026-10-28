(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require BvWfKernel.
(* [comment removed for export] *)
From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OssFuzzTheorems.jsoncons.fuzz_bson_parser_max.images Require Import AsanUbsan.
Open Scope bv_scope.

Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

(* [comment removed for export] *)
Definition W_8d570 : bv 32 := 0x00060693.
Lemma F_8d570 : fetch_word AsanUbsan.M.loaded_segments (0x8d988 : word) = Some W_8d570.
Proof. vm_refl. Qed.
Lemma D_8d570 : decode_any W_8d570 = Some (OpImm ALU_ADD 13 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8d574 : bv 32 := 0x00000613.
Lemma F_8d574 : fetch_word AsanUbsan.M.loaded_segments (0x8d98c : word) = Some W_8d574.
Proof. vm_refl. Qed.
Lemma D_8d574 : decode_any W_8d574 = Some (OpImm ALU_ADD 12 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8d578 : bv 32 := 0x0040006f.
Lemma F_8d578 : fetch_word AsanUbsan.M.loaded_segments (0x8d990 : word) = Some W_8d578.
Proof. vm_refl. Qed.
Lemma D_8d578 : decode_any W_8d578 = Some (Jal 0 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8d57c : bv 32 := 0xfa010113.
Lemma F_8d57c : fetch_word AsanUbsan.M.loaded_segments (0x8d994 : word) = Some W_8d57c.
Proof. vm_refl. Qed.
Lemma D_8d57c : decode_any W_8d57c = Some (OpImm ALU_ADD 2 2 4000, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8d580 : bv 32 := 0x04113c23.
Lemma F_8d580 : fetch_word AsanUbsan.M.loaded_segments (0x8d998 : word) = Some W_8d580.
Proof. vm_refl. Qed.
Lemma D_8d580 : decode_any W_8d580 = Some (Store SZ8 2 1 88, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8d584 : bv 32 := 0x04813823.
Lemma F_8d584 : fetch_word AsanUbsan.M.loaded_segments (0x8d99c : word) = Some W_8d584.
Proof. vm_refl. Qed.
Lemma D_8d584 : decode_any W_8d584 = Some (Store SZ8 2 8 80, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8d588 : bv 32 := 0x04913423.
Lemma F_8d588 : fetch_word AsanUbsan.M.loaded_segments (0x8d9a0 : word) = Some W_8d588.
Proof. vm_refl. Qed.
Lemma D_8d588 : decode_any W_8d588 = Some (Store SZ8 2 9 72, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8d58c : bv 32 := 0x05213023.
Lemma F_8d58c : fetch_word AsanUbsan.M.loaded_segments (0x8d9a4 : word) = Some W_8d58c.
Proof. vm_refl. Qed.
Lemma D_8d58c : decode_any W_8d58c = Some (Store SZ8 2 18 64, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8d590 : bv 32 := 0x03313c23.
Lemma F_8d590 : fetch_word AsanUbsan.M.loaded_segments (0x8d9a8 : word) = Some W_8d590.
Proof. vm_refl. Qed.
Lemma D_8d590 : decode_any W_8d590 = Some (Store SZ8 2 19 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8d594 : bv 32 := 0x03413823.
Lemma F_8d594 : fetch_word AsanUbsan.M.loaded_segments (0x8d9ac : word) = Some W_8d594.
Proof. vm_refl. Qed.
Lemma D_8d594 : decode_any W_8d594 = Some (Store SZ8 2 20 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8d598 : bv 32 := 0x00068993.
Lemma F_8d598 : fetch_word AsanUbsan.M.loaded_segments (0x8d9b0 : word) = Some W_8d598.
Proof. vm_refl. Qed.
Lemma D_8d598 : decode_any W_8d598 = Some (OpImm ALU_ADD 19 13 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8d59c : bv 32 := 0x00060493.
Lemma F_8d59c : fetch_word AsanUbsan.M.loaded_segments (0x8d9b4 : word) = Some W_8d59c.
Proof. vm_refl. Qed.
Lemma D_8d59c : decode_any W_8d59c = Some (OpImm ALU_ADD 9 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8d5a0 : bv 32 := 0x00058413.
Lemma F_8d5a0 : fetch_word AsanUbsan.M.loaded_segments (0x8d9b8 : word) = Some W_8d5a0.
Proof. vm_refl. Qed.
Lemma D_8d5a0 : decode_any W_8d5a0 = Some (OpImm ALU_ADD 8 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8d5a4 : bv 32 := 0x000aa597.
Lemma F_8d5a4 : fetch_word AsanUbsan.M.loaded_segments (0x8d9bc : word) = Some W_8d5a4.
Proof. vm_refl. Qed.
Lemma D_8d5a4 : decode_any W_8d5a4 = Some (Auipc 11 170, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8d5a8 : bv 32 := 0xae45ba03.
Lemma F_8d5a8 : fetch_word AsanUbsan.M.loaded_segments (0x8d9c0 : word) = Some W_8d5a8.
Proof. vm_refl. Qed.
Lemma D_8d5a8 : decode_any W_8d5a8 = Some (Load SZ8 true 20 11 2788, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8d5ac : bv 32 := 0x000a3583.
Lemma F_8d5ac : fetch_word AsanUbsan.M.loaded_segments (0x8d9c4 : word) = Some W_8d5ac.
Proof. vm_refl. Qed.
Lemma D_8d5ac : decode_any W_8d5ac = Some (Load SZ8 true 11 20 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8d5b0 : bv 32 := 0x00050913.
Lemma F_8d5b0 : fetch_word AsanUbsan.M.loaded_segments (0x8d9c8 : word) = Some W_8d5b0.
Proof. vm_refl. Qed.
Lemma D_8d5b0 : decode_any W_8d5b0 = Some (OpImm ALU_ADD 18 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8d5b4 : bv 32 := 0x00059863.
Lemma F_8d5b4 : fetch_word AsanUbsan.M.loaded_segments (0x8d9cc : word) = Some W_8d5b4.
Proof. vm_refl. Qed.
Lemma D_8d5b4 : decode_any W_8d5b4 = Some (Branch BC_NE 11 0 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8d5c4 : bv 32 := 0xfff58513.
Lemma F_8d5c4 : fetch_word AsanUbsan.M.loaded_segments (0x8d9dc : word) = Some W_8d5c4.
Proof. vm_refl. Qed.
Lemma D_8d5c4 : decode_any W_8d5c4 = Some (OpImm ALU_ADD 10 11 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8d5c8 : bv 32 := 0x00a5f533.
Lemma F_8d5c8 : fetch_word AsanUbsan.M.loaded_segments (0x8d9e0 : word) = Some W_8d5c8.
Proof. vm_refl. Qed.
Lemma D_8d5c8 : decode_any W_8d5c8 = Some (Op ALU_AND 10 11 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8d5cc : bv 32 := 0x0a051863.
Lemma F_8d5cc : fetch_word AsanUbsan.M.loaded_segments (0x8d9e4 : word) = Some W_8d5cc.
Proof. vm_refl. Qed.
Lemma D_8d5cc : decode_any W_8d5cc = Some (Branch BC_NE 10 0 176, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8d5d0 : bv 32 := 0x00b40433.
Lemma F_8d5d0 : fetch_word AsanUbsan.M.loaded_segments (0x8d9e8 : word) = Some W_8d5d0.
Proof. vm_refl. Qed.
Lemma D_8d5d0 : decode_any W_8d5d0 = Some (Op ALU_ADD 8 8 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8d5d4 : bv 32 := 0xfff40413.
Lemma F_8d5d4 : fetch_word AsanUbsan.M.loaded_segments (0x8d9ec : word) = Some W_8d5d4.
Proof. vm_refl. Qed.
Lemma D_8d5d4 : decode_any W_8d5d4 = Some (OpImm ALU_ADD 8 8 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8d5d8 : bv 32 := 0x40b00533.
Lemma F_8d5d8 : fetch_word AsanUbsan.M.loaded_segments (0x8d9f0 : word) = Some W_8d5d8.
Proof. vm_refl. Qed.
Lemma D_8d5d8 : decode_any W_8d5d8 = Some (Op ALU_SUB 10 0 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8d5dc : bv 32 := 0x00a47433.
Lemma F_8d5dc : fetch_word AsanUbsan.M.loaded_segments (0x8d9f4 : word) = Some W_8d5dc.
Proof. vm_refl. Qed.
Lemma D_8d5dc : decode_any W_8d5dc = Some (Op ALU_AND 8 8 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8d5e0 : bv 32 := 0x00059863.
Lemma F_8d5e0 : fetch_word AsanUbsan.M.loaded_segments (0x8d9f8 : word) = Some W_8d5e0.
Proof. vm_refl. Qed.
Lemma D_8d5e0 : decode_any W_8d5e0 = Some (Branch BC_NE 11 0 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8d5f0 : bv 32 := 0x00a97933.
Lemma F_8d5f0 : fetch_word AsanUbsan.M.loaded_segments (0x8da08 : word) = Some W_8d5f0.
Proof. vm_refl. Qed.
Lemma D_8d5f0 : decode_any W_8d5f0 = Some (Op ALU_AND 18 18 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8d5f4 : bv 32 := 0x03200513.
Lemma F_8d5f4 : fetch_word AsanUbsan.M.loaded_segments (0x8da0c : word) = Some W_8d5f4.
Proof. vm_refl. Qed.
Lemma D_8d5f4 : decode_any W_8d5f4 = Some (OpImm ALU_ADD 10 0 50, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8d5f8 : bv 32 := 0x00a12023.
Lemma F_8d5f8 : fetch_word AsanUbsan.M.loaded_segments (0x8da10 : word) = Some W_8d5f8.
Proof. vm_refl. Qed.
Lemma D_8d5f8 : decode_any W_8d5f8 = Some (Store SZ4 2 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8d5fc : bv 32 := 0x00010613.
Lemma F_8d5fc : fetch_word AsanUbsan.M.loaded_segments (0x8da14 : word) = Some W_8d5fc.
Proof. vm_refl. Qed.
Lemma D_8d5fc : decode_any W_8d5fc = Some (OpImm ALU_ADD 12 2 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8d600 : bv 32 := 0x00098513.
Lemma F_8d600 : fetch_word AsanUbsan.M.loaded_segments (0x8da18 : word) = Some W_8d600.
Proof. vm_refl. Qed.
Lemma D_8d600 : decode_any W_8d600 = Some (OpImm ALU_ADD 10 19 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8d604 : bv 32 := 0x00040593.
Lemma F_8d604 : fetch_word AsanUbsan.M.loaded_segments (0x8da1c : word) = Some W_8d604.
Proof. vm_refl. Qed.
Lemma D_8d604 : decode_any W_8d604 = Some (OpImm ALU_ADD 11 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8d608 : bv 32 := 0x608000ef.
Lemma F_8d608 : fetch_word AsanUbsan.M.loaded_segments (0x8da20 : word) = Some W_8d608.
Proof. vm_refl. Qed.
Lemma D_8d608 : decode_any W_8d608 = Some (Jal 1 1544, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8d60c : bv 32 := 0x00012683.
Lemma F_8d60c : fetch_word AsanUbsan.M.loaded_segments (0x8da24 : word) = Some W_8d60c.
Proof. vm_refl. Qed.
Lemma D_8d60c : decode_any W_8d60c = Some (Load SZ4 true 13 2 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8d610 : bv 32 := 0x00050713.
Lemma F_8d610 : fetch_word AsanUbsan.M.loaded_segments (0x8da28 : word) = Some W_8d610.
Proof. vm_refl. Qed.
Lemma D_8d610 : decode_any W_8d610 = Some (OpImm ALU_ADD 14 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8d614 : bv 32 := 0x00300613.
Lemma F_8d614 : fetch_word AsanUbsan.M.loaded_segments (0x8da2c : word) = Some W_8d614.
Proof. vm_refl. Qed.
Lemma D_8d614 : decode_any W_8d614 = Some (OpImm ALU_ADD 12 0 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8d618 : bv 32 := 0x00090513.
Lemma F_8d618 : fetch_word AsanUbsan.M.loaded_segments (0x8da30 : word) = Some W_8d618.
Proof. vm_refl. Qed.
Lemma D_8d618 : decode_any W_8d618 = Some (OpImm ALU_ADD 10 18 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8d61c : bv 32 := 0x00040593.
Lemma F_8d61c : fetch_word AsanUbsan.M.loaded_segments (0x8da34 : word) = Some W_8d61c.
Proof. vm_refl. Qed.
Lemma D_8d61c : decode_any W_8d61c = Some (OpImm ALU_ADD 11 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8d620 : bv 32 := 0x00000793.
Lemma F_8d620 : fetch_word AsanUbsan.M.loaded_segments (0x8da38 : word) = Some W_8d620.
Proof. vm_refl. Qed.
Lemma D_8d620 : decode_any W_8d620 = Some (OpImm ALU_ADD 15 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8d624 : bv 32 := 0xa40fe0ef.
Lemma F_8d624 : fetch_word AsanUbsan.M.loaded_segments (0x8da3c : word) = Some W_8d624.
Proof. vm_refl. Qed.
Lemma D_8d624 : decode_any W_8d624 = Some (Jal 1 2089536, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8d628 : bv 32 := 0x00050993.
Lemma F_8d628 : fetch_word AsanUbsan.M.loaded_segments (0x8da40 : word) = Some W_8d628.
Proof. vm_refl. Qed.
Lemma D_8d628 : decode_any W_8d628 = Some (OpImm ALU_ADD 19 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8d62c : bv 32 := 0x00000593.
Lemma F_8d62c : fetch_word AsanUbsan.M.loaded_segments (0x8da44 : word) = Some W_8d62c.
Proof. vm_refl. Qed.
Lemma D_8d62c : decode_any W_8d62c = Some (OpImm ALU_ADD 11 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8d630 : bv 32 := 0xa14fe0ef.
Lemma F_8d630 : fetch_word AsanUbsan.M.loaded_segments (0x8da48 : word) = Some W_8d630.
Proof. vm_refl. Qed.
Lemma D_8d630 : decode_any W_8d630 = Some (Jal 1 2089492, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8d634 : bv 32 := 0xaaaab537.
Lemma F_8d634 : fetch_word AsanUbsan.M.loaded_segments (0x8da4c : word) = Some W_8d634.
Proof. vm_refl. Qed.
Lemma D_8d634 : decode_any W_8d634 = Some (Lui 10 699051, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8d638 : bv 32 := 0xaaa50513.
Lemma F_8d638 : fetch_word AsanUbsan.M.loaded_segments (0x8da50 : word) = Some W_8d638.
Proof. vm_refl. Qed.
Lemma D_8d638 : decode_any W_8d638 = Some (OpImm ALU_ADD 10 10 2730, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8d63c : bv 32 := 0x02a12623.
Lemma F_8d63c : fetch_word AsanUbsan.M.loaded_segments (0x8da54 : word) = Some W_8d63c.
Proof. vm_refl. Qed.
Lemma D_8d63c : decode_any W_8d63c = Some (Store SZ4 2 10 44, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8d640 : bv 32 := 0x02c10593.
Lemma F_8d640 : fetch_word AsanUbsan.M.loaded_segments (0x8da58 : word) = Some W_8d640.
Proof. vm_refl. Qed.
Lemma D_8d640 : decode_any W_8d640 = Some (OpImm ALU_ADD 11 2 44, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8d644 : bv 32 := 0x00098513.
Lemma F_8d644 : fetch_word AsanUbsan.M.loaded_segments (0x8da5c : word) = Some W_8d644.
Proof. vm_refl. Qed.
Lemma D_8d644 : decode_any W_8d644 = Some (OpImm ALU_ADD 10 19 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8d648 : bv 32 := 0x9fcfe0ef.
Lemma F_8d648 : fetch_word AsanUbsan.M.loaded_segments (0x8da60 : word) = Some W_8d648.
Proof. vm_refl. Qed.
Lemma D_8d648 : decode_any W_8d648 = Some (Jal 1 2089468, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8d64c : bv 32 := 0x04051063.
Lemma F_8d64c : fetch_word AsanUbsan.M.loaded_segments (0x8da64 : word) = Some W_8d64c.
Proof. vm_refl. Qed.
Lemma D_8d64c : decode_any W_8d64c = Some (Branch BC_NE 10 0 64, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8d650 : bv 32 := 0x00040513.
Lemma F_8d650 : fetch_word AsanUbsan.M.loaded_segments (0x8da68 : word) = Some W_8d650.
Proof. vm_refl. Qed.
Lemma D_8d650 : decode_any W_8d650 = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8d654 : bv 32 := 0x8d8fa0ef.
Lemma F_8d654 : fetch_word AsanUbsan.M.loaded_segments (0x8da6c : word) = Some W_8d654.
Proof. vm_refl. Qed.
Lemma D_8d654 : decode_any W_8d654 = Some (Jal 1 2072792, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8d658 : bv 32 := 0x00098513.
Lemma F_8d658 : fetch_word AsanUbsan.M.loaded_segments (0x8da70 : word) = Some W_8d658.
Proof. vm_refl. Qed.
Lemma D_8d658 : decode_any W_8d658 = Some (OpImm ALU_ADD 10 19 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8d65c : bv 32 := 0x05813083.
Lemma F_8d65c : fetch_word AsanUbsan.M.loaded_segments (0x8da74 : word) = Some W_8d65c.
Proof. vm_refl. Qed.
Lemma D_8d65c : decode_any W_8d65c = Some (Load SZ8 true 1 2 88, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8d660 : bv 32 := 0x05013403.
Lemma F_8d660 : fetch_word AsanUbsan.M.loaded_segments (0x8da78 : word) = Some W_8d660.
Proof. vm_refl. Qed.
Lemma D_8d660 : decode_any W_8d660 = Some (Load SZ8 true 8 2 80, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8d664 : bv 32 := 0x04813483.
Lemma F_8d664 : fetch_word AsanUbsan.M.loaded_segments (0x8da7c : word) = Some W_8d664.
Proof. vm_refl. Qed.
Lemma D_8d664 : decode_any W_8d664 = Some (Load SZ8 true 9 2 72, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8d668 : bv 32 := 0x04013903.
Lemma F_8d668 : fetch_word AsanUbsan.M.loaded_segments (0x8da80 : word) = Some W_8d668.
Proof. vm_refl. Qed.
Lemma D_8d668 : decode_any W_8d668 = Some (Load SZ8 true 18 2 64, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8d66c : bv 32 := 0x03813983.
Lemma F_8d66c : fetch_word AsanUbsan.M.loaded_segments (0x8da84 : word) = Some W_8d66c.
Proof. vm_refl. Qed.
Lemma D_8d66c : decode_any W_8d66c = Some (Load SZ8 true 19 2 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8d670 : bv 32 := 0x03013a03.
Lemma F_8d670 : fetch_word AsanUbsan.M.loaded_segments (0x8da88 : word) = Some W_8d670.
Proof. vm_refl. Qed.
Lemma D_8d670 : decode_any W_8d670 = Some (Load SZ8 true 20 2 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8d674 : bv 32 := 0x06010113.
Lemma F_8d674 : fetch_word AsanUbsan.M.loaded_segments (0x8da8c : word) = Some W_8d674.
Proof. vm_refl. Qed.
Lemma D_8d674 : decode_any W_8d674 = Some (OpImm ALU_ADD 2 2 96, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8d678 : bv 32 := 0x00008067.
Lemma F_8d678 : fetch_word AsanUbsan.M.loaded_segments (0x8da90 : word) = Some W_8d678.
Proof. vm_refl. Qed.
Lemma D_8d678 : decode_any W_8d678 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8d6f4 : bv 32 := 0x00060693.
Lemma F_8d6f4 : fetch_word AsanUbsan.M.loaded_segments (0x8db0c : word) = Some W_8d6f4.
Proof. vm_refl. Qed.
Lemma D_8d6f4 : decode_any W_8d6f4 = Some (OpImm ALU_ADD 13 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8d6f8 : bv 32 := 0x00100613.
Lemma F_8d6f8 : fetch_word AsanUbsan.M.loaded_segments (0x8db10 : word) = Some W_8d6f8.
Proof. vm_refl. Qed.
Lemma D_8d6f8 : decode_any W_8d6f8 = Some (OpImm ALU_ADD 12 0 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8d6fc : bv 32 := 0xe81ff06f.
Lemma F_8d6fc : fetch_word AsanUbsan.M.loaded_segments (0x8db14 : word) = Some W_8d6fc.
Proof. vm_refl. Qed.
Lemma D_8d6fc : decode_any W_8d6fc = Some (Jal 0 2096768, 4%Z).
Proof. vm_refl. Qed.
