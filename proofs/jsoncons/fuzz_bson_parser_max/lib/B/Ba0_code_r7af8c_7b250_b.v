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
Definition W_7b664 : bv 32 := 0x81010113.
Lemma F_7b664 : fetch_word AsanUbsan.M.loaded_segments (0x7ba7c : word) = Some W_7b664.
Proof. vm_refl. Qed.
Lemma D_7b664 : decode_any W_7b664 = Some (OpImm ALU_ADD 2 2 2064, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7b668 : bv 32 := 0x7e113423.
Lemma F_7b668 : fetch_word AsanUbsan.M.loaded_segments (0x7ba80 : word) = Some W_7b668.
Proof. vm_refl. Qed.
Lemma D_7b668 : decode_any W_7b668 = Some (Store SZ8 2 1 2024, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7b66c : bv 32 := 0x7e813023.
Lemma F_7b66c : fetch_word AsanUbsan.M.loaded_segments (0x7ba84 : word) = Some W_7b66c.
Proof. vm_refl. Qed.
Lemma D_7b66c : decode_any W_7b66c = Some (Store SZ8 2 8 2016, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7b670 : bv 32 := 0x7c913c23.
Lemma F_7b670 : fetch_word AsanUbsan.M.loaded_segments (0x7ba88 : word) = Some W_7b670.
Proof. vm_refl. Qed.
Lemma D_7b670 : decode_any W_7b670 = Some (Store SZ8 2 9 2008, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7b674 : bv 32 := 0x7d213823.
Lemma F_7b674 : fetch_word AsanUbsan.M.loaded_segments (0x7ba8c : word) = Some W_7b674.
Proof. vm_refl. Qed.
Lemma D_7b674 : decode_any W_7b674 = Some (Store SZ8 2 18 2000, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7b678 : bv 32 := 0x7d313423.
Lemma F_7b678 : fetch_word AsanUbsan.M.loaded_segments (0x7ba90 : word) = Some W_7b678.
Proof. vm_refl. Qed.
Lemma D_7b678 : decode_any W_7b678 = Some (Store SZ8 2 19 1992, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7b67c : bv 32 := 0x7d413023.
Lemma F_7b67c : fetch_word AsanUbsan.M.loaded_segments (0x7ba94 : word) = Some W_7b67c.
Proof. vm_refl. Qed.
Lemma D_7b67c : decode_any W_7b67c = Some (Store SZ8 2 20 1984, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7b680 : bv 32 := 0x7b513c23.
Lemma F_7b680 : fetch_word AsanUbsan.M.loaded_segments (0x7ba98 : word) = Some W_7b680.
Proof. vm_refl. Qed.
Lemma D_7b680 : decode_any W_7b680 = Some (Store SZ8 2 21 1976, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7b684 : bv 32 := 0x7f010413.
Lemma F_7b684 : fetch_word AsanUbsan.M.loaded_segments (0x7ba9c : word) = Some W_7b684.
Proof. vm_refl. Qed.
Lemma D_7b684 : decode_any W_7b684 = Some (OpImm ALU_ADD 8 2 2032, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7b688 : bv 32 := 0xfa010113.
Lemma F_7b688 : fetch_word AsanUbsan.M.loaded_segments (0x7baa0 : word) = Some W_7b688.
Proof. vm_refl. Qed.
Lemma D_7b688 : decode_any W_7b688 = Some (OpImm ALU_ADD 2 2 4000, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7b68c : bv 32 := 0x00058a13.
Lemma F_7b68c : fetch_word AsanUbsan.M.loaded_segments (0x7baa4 : word) = Some W_7b68c.
Proof. vm_refl. Qed.
Lemma D_7b68c : decode_any W_7b68c = Some (OpImm ALU_ADD 20 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7b690 : bv 32 := 0x000bc597.
Lemma F_7b690 : fetch_word AsanUbsan.M.loaded_segments (0x7baa8 : word) = Some W_7b690.
Proof. vm_refl. Qed.
Lemma D_7b690 : decode_any W_7b690 = Some (Auipc 11 188, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7b694 : bv 32 := 0xa105b583.
Lemma F_7b694 : fetch_word AsanUbsan.M.loaded_segments (0x7baac : word) = Some W_7b694.
Proof. vm_refl. Qed.
Lemma D_7b694 : decode_any W_7b694 = Some (Load SZ8 true 11 11 2576, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7b698 : bv 32 := 0x0605c583.
Lemma F_7b698 : fetch_word AsanUbsan.M.loaded_segments (0x7bab0 : word) = Some W_7b698.
Proof. vm_refl. Qed.
Lemma D_7b698 : decode_any W_7b698 = Some (Load SZ1 false 11 11 96, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7b69c : bv 32 := 0x22058863.
Lemma F_7b69c : fetch_word AsanUbsan.M.loaded_segments (0x7bab4 : word) = Some W_7b69c.
Proof. vm_refl. Qed.
Lemma D_7b69c : decode_any W_7b69c = Some (Branch BC_EQ 11 0 560, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7b6a0 : bv 32 := 0x00068913.
Lemma F_7b6a0 : fetch_word AsanUbsan.M.loaded_segments (0x7bab8 : word) = Some W_7b6a0.
Proof. vm_refl. Qed.
Lemma D_7b6a0 : decode_any W_7b6a0 = Some (OpImm ALU_ADD 18 13 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7b6a4 : bv 32 := 0x00060993.
Lemma F_7b6a4 : fetch_word AsanUbsan.M.loaded_segments (0x7babc : word) = Some W_7b6a4.
Proof. vm_refl. Qed.
Lemma D_7b6a4 : decode_any W_7b6a4 = Some (OpImm ALU_ADD 19 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7b6a8 : bv 32 := 0x00050493.
Lemma F_7b6a8 : fetch_word AsanUbsan.M.loaded_segments (0x7bac0 : word) = Some W_7b6a8.
Proof. vm_refl. Qed.
Lemma D_7b6a8 : decode_any W_7b6a8 = Some (OpImm ALU_ADD 9 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7b6ac : bv 32 := 0x000bc517.
Lemma F_7b6ac : fetch_word AsanUbsan.M.loaded_segments (0x7bac4 : word) = Some W_7b6ac.
Proof. vm_refl. Qed.
Lemma D_7b6ac : decode_any W_7b6ac = Some (Auipc 10 188, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7b6b0 : bv 32 := 0xa4c53503.
Lemma F_7b6b0 : fetch_word AsanUbsan.M.loaded_segments (0x7bac8 : word) = Some W_7b6b0.
Proof. vm_refl. Qed.
Lemma D_7b6b0 : decode_any W_7b6b0 = Some (Load SZ8 true 10 10 2636, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7b6b4 : bv 32 := 0x00052503.
Lemma F_7b6b4 : fetch_word AsanUbsan.M.loaded_segments (0x7bacc : word) = Some W_7b6b4.
Proof. vm_refl. Qed.
Lemma D_7b6b4 : decode_any W_7b6b4 = Some (Load SZ4 true 10 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7b6b8 : bv 32 := 0x00300593.
Lemma F_7b6b8 : fetch_word AsanUbsan.M.loaded_segments (0x7bad0 : word) = Some W_7b6b8.
Proof. vm_refl. Qed.
Lemma D_7b6b8 : decode_any W_7b6b8 = Some (OpImm ALU_ADD 11 0 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7b6bc : bv 32 := 0x08b57063.
Lemma F_7b6bc : fetch_word AsanUbsan.M.loaded_segments (0x7bad4 : word) = Some W_7b6bc.
Proof. vm_refl. Qed.
Lemma D_7b6bc : decode_any W_7b6bc = Some (Branch BC_GEU 10 11 128, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7b6c0 : bv 32 := 0x0899fe63.
Lemma F_7b6c0 : fetch_word AsanUbsan.M.loaded_segments (0x7bad8 : word) = Some W_7b6c0.
Proof. vm_refl. Qed.
Lemma D_7b6c0 : decode_any W_7b6c0 = Some (Branch BC_GEU 19 9 156, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7b6c4 : bv 32 := 0x80040513.
Lemma F_7b6c4 : fetch_word AsanUbsan.M.loaded_segments (0x7badc : word) = Some W_7b6c4.
Proof. vm_refl. Qed.
Lemma D_7b6c4 : decode_any W_7b6c4 = Some (OpImm ALU_ADD 10 8 2048, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7b6c8 : bv 32 := 0xfb050513.
Lemma F_7b6c8 : fetch_word AsanUbsan.M.loaded_segments (0x7bae0 : word) = Some W_7b6c8.
Proof. vm_refl. Qed.
Lemma D_7b6c8 : decode_any W_7b6c8 = Some (OpImm ALU_ADD 10 10 4016, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7b6cc : bv 32 := 0x80040593.
Lemma F_7b6cc : fetch_word AsanUbsan.M.loaded_segments (0x7bae4 : word) = Some W_7b6cc.
Proof. vm_refl. Qed.
Lemma D_7b6cc : decode_any W_7b6cc = Some (OpImm ALU_ADD 11 8 2048, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7b6d0 : bv 32 := 0xfc058593.
Lemma F_7b6d0 : fetch_word AsanUbsan.M.loaded_segments (0x7bae8 : word) = Some W_7b6d0.
Proof. vm_refl. Qed.
Lemma D_7b6d0 : decode_any W_7b6d0 = Some (OpImm ALU_ADD 11 11 4032, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7b6d4 : bv 32 := 0x80040613.
Lemma F_7b6d4 : fetch_word AsanUbsan.M.loaded_segments (0x7baec : word) = Some W_7b6d4.
Proof. vm_refl. Qed.
Lemma D_7b6d4 : decode_any W_7b6d4 = Some (OpImm ALU_ADD 12 8 2048, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7b6d8 : bv 32 := 0xfb060613.
Lemma F_7b6d8 : fetch_word AsanUbsan.M.loaded_segments (0x7baf0 : word) = Some W_7b6d8.
Proof. vm_refl. Qed.
Lemma D_7b6d8 : decode_any W_7b6d8 = Some (OpImm ALU_ADD 12 12 4016, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7b6dc : bv 32 := 0x7ff60a93.
Lemma F_7b6dc : fetch_word AsanUbsan.M.loaded_segments (0x7baf4 : word) = Some W_7b6dc.
Proof. vm_refl. Qed.
Lemma D_7b6dc : decode_any W_7b6dc = Some (OpImm ALU_ADD 21 12 2047, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7b6e0 : bv 32 := 0x000ab4a3.
Lemma F_7b6e0 : fetch_word AsanUbsan.M.loaded_segments (0x7baf8 : word) = Some W_7b6e0.
Proof. vm_refl. Qed.
Lemma D_7b6e0 : decode_any W_7b6e0 = Some (Store SZ8 21 0 9, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7b6e4 : bv 32 := 0x00b53023.
Lemma F_7b6e4 : fetch_word AsanUbsan.M.loaded_segments (0x7bafc : word) = Some W_7b6e4.
Proof. vm_refl. Qed.
Lemma D_7b6e4 : decode_any W_7b6e4 = Some (Store SZ8 10 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7b6e8 : bv 32 := 0x00053423.
Lemma F_7b6e8 : fetch_word AsanUbsan.M.loaded_segments (0x7bb00 : word) = Some W_7b6e8.
Proof. vm_refl. Qed.
Lemma D_7b6e8 : decode_any W_7b6e8 = Some (Store SZ8 10 0 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7b6ec : bv 32 := 0x6451e0ef.
Lemma F_7b6ec : fetch_word AsanUbsan.M.loaded_segments (0x7bb04 : word) = Some W_7b6ec.
Proof. vm_refl. Qed.
Lemma D_7b6ec : decode_any W_7b6ec = Some (Jal 1 126532, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7b6f0 : bv 32 := 0x00050593.
Lemma F_7b6f0 : fetch_word AsanUbsan.M.loaded_segments (0x7bb08 : word) = Some W_7b6f0.
Proof. vm_refl. Qed.
Lemma D_7b6f0 : decode_any W_7b6f0 = Some (OpImm ALU_ADD 11 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7b6f4 : bv 32 := 0x000bc517.
Lemma F_7b6f4 : fetch_word AsanUbsan.M.loaded_segments (0x7bb0c : word) = Some W_7b6f4.
Proof. vm_refl. Qed.
Lemma D_7b6f4 : decode_any W_7b6f4 = Some (Auipc 10 188, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7b6f8 : bv 32 := 0x9a453503.
Lemma F_7b6f8 : fetch_word AsanUbsan.M.loaded_segments (0x7bb10 : word) = Some W_7b6f8.
Proof. vm_refl. Qed.
Lemma D_7b6f8 : decode_any W_7b6f8 = Some (Load SZ8 true 10 10 2468, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7b6fc : bv 32 := 0x02154703.
Lemma F_7b6fc : fetch_word AsanUbsan.M.loaded_segments (0x7bb14 : word) = Some W_7b6fc.
Proof. vm_refl. Qed.
Lemma D_7b6fc : decode_any W_7b6fc = Some (Load SZ1 false 14 10 33, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7b700 : bv 32 := 0x008ab4a3.
Lemma F_7b700 : fetch_word AsanUbsan.M.loaded_segments (0x7bb18 : word) = Some W_7b700.
Proof. vm_refl. Qed.
Lemma D_7b700 : decode_any W_7b700 = Some (Store SZ8 21 8 9, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7b704 : bv 32 := 0x80040513.
Lemma F_7b704 : fetch_word AsanUbsan.M.loaded_segments (0x7bb1c : word) = Some W_7b704.
Proof. vm_refl. Qed.
Lemma D_7b704 : decode_any W_7b704 = Some (OpImm ALU_ADD 10 8 2048, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7b708 : bv 32 := 0xfb050513.
Lemma F_7b708 : fetch_word AsanUbsan.M.loaded_segments (0x7bb20 : word) = Some W_7b708.
Proof. vm_refl. Qed.
Lemma D_7b708 : decode_any W_7b708 = Some (OpImm ALU_ADD 10 10 4016, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7b70c : bv 32 := 0x0ff00793.
Lemma F_7b70c : fetch_word AsanUbsan.M.loaded_segments (0x7bb24 : word) = Some W_7b70c.
Proof. vm_refl. Qed.
Lemma D_7b70c : decode_any W_7b70c = Some (OpImm ALU_ADD 15 0 255, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7b710 : bv 32 := 0x00040613.
Lemma F_7b710 : fetch_word AsanUbsan.M.loaded_segments (0x7bb28 : word) = Some W_7b710.
Proof. vm_refl. Qed.
Lemma D_7b710 : decode_any W_7b710 = Some (OpImm ALU_ADD 12 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7b714 : bv 32 := 0x00000693.
Lemma F_7b714 : fetch_word AsanUbsan.M.loaded_segments (0x7bb2c : word) = Some W_7b714.
Proof. vm_refl. Qed.
Lemma D_7b714 : decode_any W_7b714 = Some (OpImm ALU_ADD 13 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7b718 : bv 32 := 0x34c060ef.
Lemma F_7b718 : fetch_word AsanUbsan.M.loaded_segments (0x7bb30 : word) = Some W_7b718.
Proof. vm_refl. Qed.
Lemma D_7b718 : decode_any W_7b718 = Some (Jal 1 25420, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7b71c : bv 32 := 0x80040713.
Lemma F_7b71c : fetch_word AsanUbsan.M.loaded_segments (0x7bb34 : word) = Some W_7b71c.
Proof. vm_refl. Qed.
Lemma D_7b71c : decode_any W_7b71c = Some (OpImm ALU_ADD 14 8 2048, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7b720 : bv 32 := 0xfb070713.
Lemma F_7b720 : fetch_word AsanUbsan.M.loaded_segments (0x7bb38 : word) = Some W_7b720.
Proof. vm_refl. Qed.
Lemma D_7b720 : decode_any W_7b720 = Some (OpImm ALU_ADD 14 14 4016, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7b724 : bv 32 := 0x00048513.
Lemma F_7b724 : fetch_word AsanUbsan.M.loaded_segments (0x7bb3c : word) = Some W_7b724.
Proof. vm_refl. Qed.
Lemma D_7b724 : decode_any W_7b724 = Some (OpImm ALU_ADD 10 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7b728 : bv 32 := 0x000a0593.
Lemma F_7b728 : fetch_word AsanUbsan.M.loaded_segments (0x7bb40 : word) = Some W_7b728.
Proof. vm_refl. Qed.
Lemma D_7b728 : decode_any W_7b728 = Some (OpImm ALU_ADD 11 20 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7b72c : bv 32 := 0x00098613.
Lemma F_7b72c : fetch_word AsanUbsan.M.loaded_segments (0x7bb44 : word) = Some W_7b72c.
Proof. vm_refl. Qed.
Lemma D_7b72c : decode_any W_7b72c = Some (OpImm ALU_ADD 12 19 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7b730 : bv 32 := 0x00090693.
Lemma F_7b730 : fetch_word AsanUbsan.M.loaded_segments (0x7bb48 : word) = Some W_7b730.
Proof. vm_refl. Qed.
Lemma D_7b730 : decode_any W_7b730 = Some (OpImm ALU_ADD 13 18 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7b734 : bv 32 := 0x0e0030ef.
Lemma F_7b734 : fetch_word AsanUbsan.M.loaded_segments (0x7bb4c : word) = Some W_7b734.
Proof. vm_refl. Qed.
Lemma D_7b734 : decode_any W_7b734 = Some (Jal 1 12512, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7b738 : bv 32 := 0x0300006f.
Lemma F_7b738 : fetch_word AsanUbsan.M.loaded_segments (0x7bb50 : word) = Some W_7b738.
Proof. vm_refl. Qed.
Lemma D_7b738 : decode_any W_7b738 = Some (Jal 0 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7b73c : bv 32 := 0xfff9d517.
Lemma F_7b73c : fetch_word AsanUbsan.M.loaded_segments (0x7bb54 : word) = Some W_7b73c.
Proof. vm_refl. Qed.
Lemma D_7b73c : decode_any W_7b73c = Some (Auipc 10 1048477, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7b740 : bv 32 := 0x66550513.
Lemma F_7b740 : fetch_word AsanUbsan.M.loaded_segments (0x7bb58 : word) = Some W_7b740.
Proof. vm_refl. Qed.
Lemma D_7b740 : decode_any W_7b740 = Some (OpImm ALU_ADD 10 10 1637, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7b744 : bv 32 := 0x00048593.
Lemma F_7b744 : fetch_word AsanUbsan.M.loaded_segments (0x7bb5c : word) = Some W_7b744.
Proof. vm_refl. Qed.
Lemma D_7b744 : decode_any W_7b744 = Some (OpImm ALU_ADD 11 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7b748 : bv 32 := 0x000a0613.
Lemma F_7b748 : fetch_word AsanUbsan.M.loaded_segments (0x7bb60 : word) = Some W_7b748.
Proof. vm_refl. Qed.
Lemma D_7b748 : decode_any W_7b748 = Some (OpImm ALU_ADD 12 20 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7b74c : bv 32 := 0x00098693.
Lemma F_7b74c : fetch_word AsanUbsan.M.loaded_segments (0x7bb64 : word) = Some W_7b74c.
Proof. vm_refl. Qed.
Lemma D_7b74c : decode_any W_7b74c = Some (OpImm ALU_ADD 13 19 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7b750 : bv 32 := 0x00090713.
Lemma F_7b750 : fetch_word AsanUbsan.M.loaded_segments (0x7bb68 : word) = Some W_7b750.
Proof. vm_refl. Qed.
Lemma D_7b750 : decode_any W_7b750 = Some (OpImm ALU_ADD 14 18 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7b754 : bv 32 := 0x491120ef.
Lemma F_7b754 : fetch_word AsanUbsan.M.loaded_segments (0x7bb6c : word) = Some W_7b754.
Proof. vm_refl. Qed.
Lemma D_7b754 : decode_any W_7b754 = Some (Jal 1 76944, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7b758 : bv 32 := 0xf699e6e3.
Lemma F_7b758 : fetch_word AsanUbsan.M.loaded_segments (0x7bb70 : word) = Some W_7b758.
Proof. vm_refl. Qed.
Lemma D_7b758 : decode_any W_7b758 = Some (Branch BC_LTU 19 9 8044, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7b75c : bv 32 := 0xf72a64e3.
Lemma F_7b75c : fetch_word AsanUbsan.M.loaded_segments (0x7bb74 : word) = Some W_7b75c.
Proof. vm_refl. Qed.
Lemma D_7b75c : decode_any W_7b75c = Some (Branch BC_LTU 20 18 8040, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7b760 : bv 32 := 0xf73a62e3.
Lemma F_7b760 : fetch_word AsanUbsan.M.loaded_segments (0x7bb78 : word) = Some W_7b760.
Proof. vm_refl. Qed.
Lemma D_7b760 : decode_any W_7b760 = Some (Branch BC_LTU 20 19 8036, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7b764 : bv 32 := 0xf69960e3.
Lemma F_7b764 : fetch_word AsanUbsan.M.loaded_segments (0x7bb7c : word) = Some W_7b764.
Proof. vm_refl. Qed.
Lemma D_7b764 : decode_any W_7b764 = Some (Branch BC_LTU 18 9 8032, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7b768 : bv 32 := 0x409a06b3.
Lemma F_7b768 : fetch_word AsanUbsan.M.loaded_segments (0x7bb80 : word) = Some W_7b768.
Proof. vm_refl. Qed.
Lemma D_7b768 : decode_any W_7b768 = Some (Op ALU_SUB 13 20 9, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7b76c : bv 32 := 0x00100713.
Lemma F_7b76c : fetch_word AsanUbsan.M.loaded_segments (0x7bb84 : word) = Some W_7b76c.
Proof. vm_refl. Qed.
Lemma D_7b76c : decode_any W_7b76c = Some (OpImm ALU_ADD 14 0 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7b770 : bv 32 := 0x02871713.
Lemma F_7b770 : fetch_word AsanUbsan.M.loaded_segments (0x7bb88 : word) = Some W_7b770.
Proof. vm_refl. Qed.
Lemma D_7b770 : decode_any W_7b770 = Some (ShiftImm ALU_SLL 14 14 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7b774 : bv 32 := 0x00170513.
Lemma F_7b774 : fetch_word AsanUbsan.M.loaded_segments (0x7bb8c : word) = Some W_7b774.
Proof. vm_refl. Qed.
Lemma D_7b774 : decode_any W_7b774 = Some (OpImm ALU_ADD 10 14 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7b778 : bv 32 := 0x04a6fa63.
Lemma F_7b778 : fetch_word AsanUbsan.M.loaded_segments (0x7bb90 : word) = Some W_7b778.
Proof. vm_refl. Qed.
Lemma D_7b778 : decode_any W_7b778 = Some (Branch BC_GEU 13 10 84, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7b77c : bv 32 := 0x15298863.
Lemma F_7b77c : fetch_word AsanUbsan.M.loaded_segments (0x7bb94 : word) = Some W_7b77c.
Proof. vm_refl. Qed.
Lemma D_7b77c : decode_any W_7b77c = Some (Branch BC_EQ 19 18 336, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7b780 : bv 32 := 0x007a7513.
Lemma F_7b780 : fetch_word AsanUbsan.M.loaded_segments (0x7bb98 : word) = Some W_7b780.
Proof. vm_refl. Qed.
Lemma D_7b780 : decode_any W_7b780 = Some (OpImm ALU_AND 10 20 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7b784 : bv 32 := 0x06051063.
Lemma F_7b784 : fetch_word AsanUbsan.M.loaded_segments (0x7bb9c : word) = Some W_7b784.
Proof. vm_refl. Qed.
Lemma D_7b784 : decode_any W_7b784 = Some (Branch BC_NE 10 0 96, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7b788 : bv 32 := 0x00098a13.
Lemma F_7b788 : fetch_word AsanUbsan.M.loaded_segments (0x7bba0 : word) = Some W_7b788.
Proof. vm_refl. Qed.
Lemma D_7b788 : decode_any W_7b788 = Some (OpImm ALU_ADD 20 19 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7b78c : bv 32 := 0x00090a93.
Lemma F_7b78c : fetch_word AsanUbsan.M.loaded_segments (0x7bba4 : word) = Some W_7b78c.
Proof. vm_refl. Qed.
Lemma D_7b78c : decode_any W_7b78c = Some (OpImm ALU_ADD 21 18 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7b790 : bv 32 := 0x00048513.
Lemma F_7b790 : fetch_word AsanUbsan.M.loaded_segments (0x7bba8 : word) = Some W_7b790.
Proof. vm_refl. Qed.
Lemma D_7b790 : decode_any W_7b790 = Some (OpImm ALU_ADD 10 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7b794 : bv 32 := 0x0074f993.
Lemma F_7b794 : fetch_word AsanUbsan.M.loaded_segments (0x7bbac : word) = Some W_7b794.
Proof. vm_refl. Qed.
Lemma D_7b794 : decode_any W_7b794 = Some (OpImm ALU_AND 19 9 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7b798 : bv 32 := 0x08099e63.
Lemma F_7b798 : fetch_word AsanUbsan.M.loaded_segments (0x7bbb0 : word) = Some W_7b798.
Proof. vm_refl. Qed.
Lemma D_7b798 : decode_any W_7b798 = Some (Branch BC_NE 19 0 156, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7b79c : bv 32 := 0x000a0593.
Lemma F_7b79c : fetch_word AsanUbsan.M.loaded_segments (0x7bbb4 : word) = Some W_7b79c.
Proof. vm_refl. Qed.
Lemma D_7b79c : decode_any W_7b79c = Some (OpImm ALU_ADD 11 20 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7b7a0 : bv 32 := 0x000a0513.
Lemma F_7b7a0 : fetch_word AsanUbsan.M.loaded_segments (0x7bbb8 : word) = Some W_7b7a0.
Proof. vm_refl. Qed.
Lemma D_7b7a0 : decode_any W_7b7a0 = Some (OpImm ALU_ADD 10 20 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7b7a4 : bv 32 := 0x0d5a6863.
Lemma F_7b7a4 : fetch_word AsanUbsan.M.loaded_segments (0x7bbbc : word) = Some W_7b7a4.
Proof. vm_refl. Qed.
Lemma D_7b7a4 : decode_any W_7b7a4 = Some (Branch BC_LTU 20 21 208, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7b7a8 : bv 32 := 0xff8af513.
Lemma F_7b7a8 : fetch_word AsanUbsan.M.loaded_segments (0x7bbc0 : word) = Some W_7b7a8.
Proof. vm_refl. Qed.
Lemma D_7b7a8 : decode_any W_7b7a8 = Some (OpImm ALU_AND 10 21 4088, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7b7ac : bv 32 := 0x0cbaf863.
Lemma F_7b7ac : fetch_word AsanUbsan.M.loaded_segments (0x7bbc4 : word) = Some W_7b7ac.
Proof. vm_refl. Qed.
Lemma D_7b7ac : decode_any W_7b7ac = Some (Branch BC_GEU 21 11 208, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7b7b0 : bv 32 := 0xff8af493.
Lemma F_7b7b0 : fetch_word AsanUbsan.M.loaded_segments (0x7bbc8 : word) = Some W_7b7b0.
Proof. vm_refl. Qed.
Lemma D_7b7b0 : decode_any W_7b7b0 = Some (OpImm ALU_AND 9 21 4088, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7b7b4 : bv 32 := 0x007a8613.
Lemma F_7b7b4 : fetch_word AsanUbsan.M.loaded_segments (0x7bbcc : word) = Some W_7b7b4.
Proof. vm_refl. Qed.
Lemma D_7b7b4 : decode_any W_7b7b4 = Some (OpImm ALU_ADD 12 21 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7b7b8 : bv 32 := 0xff867913.
Lemma F_7b7b8 : fetch_word AsanUbsan.M.loaded_segments (0x7bbd0 : word) = Some W_7b7b8.
Proof. vm_refl. Qed.
Lemma D_7b7b8 : decode_any W_7b7b8 = Some (OpImm ALU_AND 18 12 4088, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7b7bc : bv 32 := 0x0c957a63.
Lemma F_7b7bc : fetch_word AsanUbsan.M.loaded_segments (0x7bbd4 : word) = Some W_7b7bc.
Proof. vm_refl. Qed.
Lemma D_7b7bc : decode_any W_7b7bc = Some (Branch BC_GEU 10 9 212, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7b7c0 : bv 32 := 0x40a485b3.
Lemma F_7b7c0 : fetch_word AsanUbsan.M.loaded_segments (0x7bbd8 : word) = Some W_7b7c0.
Proof. vm_refl. Qed.
Lemma D_7b7c0 : decode_any W_7b7c0 = Some (Op ALU_SUB 11 9 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7b7c4 : bv 32 := 0x00000613.
Lemma F_7b7c4 : fetch_word AsanUbsan.M.loaded_segments (0x7bbdc : word) = Some W_7b7c4.
Proof. vm_refl. Qed.
Lemma D_7b7c4 : decode_any W_7b7c4 = Some (OpImm ALU_ADD 12 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7b7c8 : bv 32 := 0x0e00006f.
Lemma F_7b7c8 : fetch_word AsanUbsan.M.loaded_segments (0x7bbe0 : word) = Some W_7b7c8.
Proof. vm_refl. Qed.
Lemma D_7b7c8 : decode_any W_7b7c8 = Some (Jal 0 224, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7b7cc : bv 32 := 0xfffa5517.
Lemma F_7b7cc : fetch_word AsanUbsan.M.loaded_segments (0x7bbe4 : word) = Some W_7b7cc.
Proof. vm_refl. Qed.
Lemma D_7b7cc : decode_any W_7b7cc = Some (Auipc 10 1048485, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7b7d0 : bv 32 := 0xfffa6597.
Lemma F_7b7d0 : fetch_word AsanUbsan.M.loaded_segments (0x7bbe8 : word) = Some W_7b7d0.
Proof. vm_refl. Qed.
Lemma D_7b7d0 : decode_any W_7b7d0 = Some (Auipc 11 1048486, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7b7d4 : bv 32 := 0x6da50513.
Lemma F_7b7d4 : fetch_word AsanUbsan.M.loaded_segments (0x7bbec : word) = Some W_7b7d4.
Proof. vm_refl. Qed.
Lemma D_7b7d4 : decode_any W_7b7d4 = Some (OpImm ALU_ADD 10 10 1754, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7b7d8 : bv 32 := 0x7e558613.
Lemma F_7b7d8 : fetch_word AsanUbsan.M.loaded_segments (0x7bbf0 : word) = Some W_7b7d8.
Proof. vm_refl. Qed.
Lemma D_7b7d8 : decode_any W_7b7d8 = Some (OpImm ALU_ADD 12 11 2021, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7b7dc : bv 32 := 0x1b600593.
Lemma F_7b7dc : fetch_word AsanUbsan.M.loaded_segments (0x7bbf4 : word) = Some W_7b7dc.
Proof. vm_refl. Qed.
Lemma D_7b7dc : decode_any W_7b7dc = Some (OpImm ALU_ADD 11 0 438, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7b7e0 : bv 32 := 0x58c170ef.
Lemma F_7b7e0 : fetch_word AsanUbsan.M.loaded_segments (0x7bbf8 : word) = Some W_7b7e0.
Proof. vm_refl. Qed.
Lemma D_7b7e0 : decode_any W_7b7e0 = Some (Jal 1 95628, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7b7e4 : bv 32 := 0xff8a7a93.
Lemma F_7b7e4 : fetch_word AsanUbsan.M.loaded_segments (0x7bbfc : word) = Some W_7b7e4.
Proof. vm_refl. Qed.
Lemma D_7b7e4 : decode_any W_7b7e4 = Some (OpImm ALU_AND 21 20 4088, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7b7e8 : bv 32 := 0x00098593.
Lemma F_7b7e8 : fetch_word AsanUbsan.M.loaded_segments (0x7bc00 : word) = Some W_7b7e8.
Proof. vm_refl. Qed.
Lemma D_7b7e8 : decode_any W_7b7e8 = Some (OpImm ALU_ADD 11 19 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7b7ec : bv 32 := 0x01396463.
Lemma F_7b7ec : fetch_word AsanUbsan.M.loaded_segments (0x7bc04 : word) = Some W_7b7ec.
Proof. vm_refl. Qed.
Lemma D_7b7ec : decode_any W_7b7ec = Some (Branch BC_LTU 18 19 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7b7f0 : bv 32 := 0x00090593.
Lemma F_7b7f0 : fetch_word AsanUbsan.M.loaded_segments (0x7bc08 : word) = Some W_7b7f0.
Proof. vm_refl. Qed.
Lemma D_7b7f0 : decode_any W_7b7f0 = Some (OpImm ALU_ADD 11 18 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7b7f4 : bv 32 := 0xf8bafae3.
Lemma F_7b7f4 : fetch_word AsanUbsan.M.loaded_segments (0x7bc0c : word) = Some W_7b7f4.
Proof. vm_refl. Qed.
Lemma D_7b7f4 : decode_any W_7b7f4 = Some (Branch BC_GEU 21 11 8084, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7b7f8 : bv 32 := 0x000bc597.
Lemma F_7b7f8 : fetch_word AsanUbsan.M.loaded_segments (0x7bc10 : word) = Some W_7b7f8.
Proof. vm_refl. Qed.
Lemma D_7b7f8 : decode_any W_7b7f8 = Some (Auipc 11 188, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7b7fc : bv 32 := 0x8b05b583.
Lemma F_7b7fc : fetch_word AsanUbsan.M.loaded_segments (0x7bc14 : word) = Some W_7b7fc.
Proof. vm_refl. Qed.
Lemma D_7b7fc : decode_any W_7b7fc = Some (Load SZ8 true 11 11 2224, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7b800 : bv 32 := 0x0005b583.
Lemma F_7b800 : fetch_word AsanUbsan.M.loaded_segments (0x7bc18 : word) = Some W_7b800.
Proof. vm_refl. Qed.
Lemma D_7b800 : decode_any W_7b800 = Some (Load SZ8 true 11 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7b804 : bv 32 := 0x003a5613.
Lemma F_7b804 : fetch_word AsanUbsan.M.loaded_segments (0x7bc1c : word) = Some W_7b804.
Proof. vm_refl. Qed.
Lemma D_7b804 : decode_any W_7b804 = Some (ShiftImm ALU_SRL 12 20 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7b808 : bv 32 := 0x00c585b3.
Lemma F_7b808 : fetch_word AsanUbsan.M.loaded_segments (0x7bc20 : word) = Some W_7b808.
Proof. vm_refl. Qed.
Lemma D_7b808 : decode_any W_7b808 = Some (Op ALU_ADD 11 11 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7b80c : bv 32 := 0x00058583.
Lemma F_7b80c : fetch_word AsanUbsan.M.loaded_segments (0x7bc24 : word) = Some W_7b80c.
Proof. vm_refl. Qed.
Lemma D_7b80c : decode_any W_7b80c = Some (Load SZ1 true 11 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7b810 : bv 32 := 0x00058463.
Lemma F_7b810 : fetch_word AsanUbsan.M.loaded_segments (0x7bc28 : word) = Some W_7b810.
Proof. vm_refl. Qed.
Lemma D_7b810 : decode_any W_7b810 = Some (Branch BC_EQ 11 0 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7b814 : bv 32 := 0xf6b55ae3.
Lemma F_7b814 : fetch_word AsanUbsan.M.loaded_segments (0x7bc2c : word) = Some W_7b814.
Proof. vm_refl. Qed.
Lemma D_7b814 : decode_any W_7b814 = Some (Branch BC_GE 10 11 8052, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7b818 : bv 32 := 0x000a8513.
Lemma F_7b818 : fetch_word AsanUbsan.M.loaded_segments (0x7bc30 : word) = Some W_7b818.
Proof. vm_refl. Qed.
Lemma D_7b818 : decode_any W_7b818 = Some (OpImm ALU_ADD 10 21 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7b81c : bv 32 := 0x0e9aea63.
Lemma F_7b81c : fetch_word AsanUbsan.M.loaded_segments (0x7bc34 : word) = Some W_7b81c.
Proof. vm_refl. Qed.
Lemma D_7b81c : decode_any W_7b81c = Some (Branch BC_LTU 21 9 244, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7b820 : bv 32 := 0x00048513.
Lemma F_7b820 : fetch_word AsanUbsan.M.loaded_segments (0x7bc38 : word) = Some W_7b820.
Proof. vm_refl. Qed.
Lemma D_7b820 : decode_any W_7b820 = Some (OpImm ALU_ADD 10 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7b824 : bv 32 := 0x000a8a13.
Lemma F_7b824 : fetch_word AsanUbsan.M.loaded_segments (0x7bc3c : word) = Some W_7b824.
Proof. vm_refl. Qed.
Lemma D_7b824 : decode_any W_7b824 = Some (OpImm ALU_ADD 20 21 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7b828 : bv 32 := 0x0f3af863.
Lemma F_7b828 : fetch_word AsanUbsan.M.loaded_segments (0x7bc40 : word) = Some W_7b828.
Proof. vm_refl. Qed.
Lemma D_7b828 : decode_any W_7b828 = Some (Branch BC_GEU 21 19 240, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7b82c : bv 32 := 0xf72ae4e3.
Lemma F_7b82c : fetch_word AsanUbsan.M.loaded_segments (0x7bc44 : word) = Some W_7b82c.
Proof. vm_refl. Qed.
Lemma D_7b82c : decode_any W_7b82c = Some (Branch BC_LTU 21 18 8040, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7b830 : bv 32 := 0x0f00006f.
Lemma F_7b830 : fetch_word AsanUbsan.M.loaded_segments (0x7bc48 : word) = Some W_7b830.
Proof. vm_refl. Qed.
Lemma D_7b830 : decode_any W_7b830 = Some (Jal 0 240, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7b834 : bv 32 := 0xf74504e3.
Lemma F_7b834 : fetch_word AsanUbsan.M.loaded_segments (0x7bc4c : word) = Some W_7b834.
Proof. vm_refl. Qed.
Lemma D_7b834 : decode_any W_7b834 = Some (Branch BC_EQ 10 20 8040, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7b838 : bv 32 := 0xf75512e3.
Lemma F_7b838 : fetch_word AsanUbsan.M.loaded_segments (0x7bc50 : word) = Some W_7b838.
Proof. vm_refl. Qed.
Lemma D_7b838 : decode_any W_7b838 = Some (Branch BC_NE 10 21 8036, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7b83c : bv 32 := 0x00748593.
Lemma F_7b83c : fetch_word AsanUbsan.M.loaded_segments (0x7bc54 : word) = Some W_7b83c.
Proof. vm_refl. Qed.
Lemma D_7b83c : decode_any W_7b83c = Some (OpImm ALU_ADD 11 9 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7b840 : bv 32 := 0xff85f913.
Lemma F_7b840 : fetch_word AsanUbsan.M.loaded_segments (0x7bc58 : word) = Some W_7b840.
Proof. vm_refl. Qed.
Lemma D_7b840 : decode_any W_7b840 = Some (OpImm ALU_AND 18 11 4088, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7b844 : bv 32 := 0xf5257ce3.
Lemma F_7b844 : fetch_word AsanUbsan.M.loaded_segments (0x7bc5c : word) = Some W_7b844.
Proof. vm_refl. Qed.
Lemma D_7b844 : decode_any W_7b844 = Some (Branch BC_GEU 10 18 8024, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7b848 : bv 32 := 0xff84f513.
Lemma F_7b848 : fetch_word AsanUbsan.M.loaded_segments (0x7bc60 : word) = Some W_7b848.
Proof. vm_refl. Qed.
Lemma D_7b848 : decode_any W_7b848 = Some (OpImm ALU_AND 10 9 4088, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7b84c : bv 32 := 0xbd0ff0ef.
Lemma F_7b84c : fetch_word AsanUbsan.M.loaded_segments (0x7bc64 : word) = Some W_7b84c.
Proof. vm_refl. Qed.
Lemma D_7b84c : decode_any W_7b84c = Some (Jal 1 2094032, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7b850 : bv 32 := 0x01350023.
Lemma F_7b850 : fetch_word AsanUbsan.M.loaded_segments (0x7bc68 : word) = Some W_7b850.
Proof. vm_refl. Qed.
Lemma D_7b850 : decode_any W_7b850 = Some (Store SZ1 10 19 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7b854 : bv 32 := 0x00090593.
Lemma F_7b854 : fetch_word AsanUbsan.M.loaded_segments (0x7bc6c : word) = Some W_7b854.
Proof. vm_refl. Qed.
Lemma D_7b854 : decode_any W_7b854 = Some (OpImm ALU_ADD 11 18 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7b858 : bv 32 := 0x012a6463.
Lemma F_7b858 : fetch_word AsanUbsan.M.loaded_segments (0x7bc70 : word) = Some W_7b858.
Proof. vm_refl. Qed.
Lemma D_7b858 : decode_any W_7b858 = Some (Branch BC_LTU 20 18 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7b85c : bv 32 := 0x000a0593.
Lemma F_7b85c : fetch_word AsanUbsan.M.loaded_segments (0x7bc74 : word) = Some W_7b85c.
Proof. vm_refl. Qed.
Lemma D_7b85c : decode_any W_7b85c = Some (OpImm ALU_ADD 11 20 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7b860 : bv 32 := 0x012ae463.
Lemma F_7b860 : fetch_word AsanUbsan.M.loaded_segments (0x7bc78 : word) = Some W_7b860.
Proof. vm_refl. Qed.
Lemma D_7b860 : decode_any W_7b860 = Some (Branch BC_LTU 21 18 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7b864 : bv 32 := 0x000a8913.
Lemma F_7b864 : fetch_word AsanUbsan.M.loaded_segments (0x7bc7c : word) = Some W_7b864.
Proof. vm_refl. Qed.
Lemma D_7b864 : decode_any W_7b864 = Some (OpImm ALU_ADD 18 21 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7b868 : bv 32 := 0x00090a93.
Lemma F_7b868 : fetch_word AsanUbsan.M.loaded_segments (0x7bc80 : word) = Some W_7b868.
Proof. vm_refl. Qed.
Lemma D_7b868 : decode_any W_7b868 = Some (OpImm ALU_ADD 21 18 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7b86c : bv 32 := 0x00058513.
Lemma F_7b86c : fetch_word AsanUbsan.M.loaded_segments (0x7bc84 : word) = Some W_7b86c.
Proof. vm_refl. Qed.
Lemma D_7b86c : decode_any W_7b86c = Some (OpImm ALU_ADD 10 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7b870 : bv 32 := 0xf325fce3.
Lemma F_7b870 : fetch_word AsanUbsan.M.loaded_segments (0x7bc88 : word) = Some W_7b870.
Proof. vm_refl. Qed.
Lemma D_7b870 : decode_any W_7b870 = Some (Branch BC_GEU 11 18 7992, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7b874 : bv 32 := 0xff857513.
Lemma F_7b874 : fetch_word AsanUbsan.M.loaded_segments (0x7bc8c : word) = Some W_7b874.
Proof. vm_refl. Qed.
Lemma D_7b874 : decode_any W_7b874 = Some (OpImm ALU_AND 10 10 4088, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7b878 : bv 32 := 0xf2baece3.
Lemma F_7b878 : fetch_word AsanUbsan.M.loaded_segments (0x7bc90 : word) = Some W_7b878.
Proof. vm_refl. Qed.
Lemma D_7b878 : decode_any W_7b878 = Some (Branch BC_LTU 21 11 7992, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7b87c : bv 32 := 0x000a8593.
Lemma F_7b87c : fetch_word AsanUbsan.M.loaded_segments (0x7bc94 : word) = Some W_7b87c.
Proof. vm_refl. Qed.
Lemma D_7b87c : decode_any W_7b87c = Some (OpImm ALU_ADD 11 21 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7b880 : bv 32 := 0xff8af493.
Lemma F_7b880 : fetch_word AsanUbsan.M.loaded_segments (0x7bc98 : word) = Some W_7b880.
Proof. vm_refl. Qed.
Lemma D_7b880 : decode_any W_7b880 = Some (OpImm ALU_AND 9 21 4088, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7b884 : bv 32 := 0x007a8613.
Lemma F_7b884 : fetch_word AsanUbsan.M.loaded_segments (0x7bc9c : word) = Some W_7b884.
Proof. vm_refl. Qed.
Lemma D_7b884 : decode_any W_7b884 = Some (OpImm ALU_ADD 12 21 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7b888 : bv 32 := 0xff867913.
Lemma F_7b888 : fetch_word AsanUbsan.M.loaded_segments (0x7bca0 : word) = Some W_7b888.
Proof. vm_refl. Qed.
Lemma D_7b888 : decode_any W_7b888 = Some (OpImm ALU_AND 18 12 4088, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7b88c : bv 32 := 0xf2956ae3.
Lemma F_7b88c : fetch_word AsanUbsan.M.loaded_segments (0x7bca4 : word) = Some W_7b88c.
Proof. vm_refl. Qed.
Lemma D_7b88c : decode_any W_7b88c = Some (Branch BC_LTU 10 9 7988, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7b890 : bv 32 := 0x00758513.
Lemma F_7b890 : fetch_word AsanUbsan.M.loaded_segments (0x7bca8 : word) = Some W_7b890.
Proof. vm_refl. Qed.
Lemma D_7b890 : decode_any W_7b890 = Some (OpImm ALU_ADD 10 11 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7b894 : bv 32 := 0xff857513.
Lemma F_7b894 : fetch_word AsanUbsan.M.loaded_segments (0x7bcac : word) = Some W_7b894.
Proof. vm_refl. Qed.
Lemma D_7b894 : decode_any W_7b894 = Some (OpImm ALU_AND 10 10 4088, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7b898 : bv 32 := 0x00a97a63.
Lemma F_7b898 : fetch_word AsanUbsan.M.loaded_segments (0x7bcb0 : word) = Some W_7b898.
Proof. vm_refl. Qed.
Lemma D_7b898 : decode_any W_7b898 = Some (Branch BC_GEU 18 10 20, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7b89c : bv 32 := 0x412505b3.
Lemma F_7b89c : fetch_word AsanUbsan.M.loaded_segments (0x7bcb4 : word) = Some W_7b89c.
Proof. vm_refl. Qed.
Lemma D_7b89c : decode_any W_7b89c = Some (Op ALU_SUB 11 10 18, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7b8a0 : bv 32 := 0x0fc00613.
Lemma F_7b8a0 : fetch_word AsanUbsan.M.loaded_segments (0x7bcb8 : word) = Some W_7b8a0.
Proof. vm_refl. Qed.
Lemma D_7b8a0 : decode_any W_7b8a0 = Some (OpImm ALU_ADD 12 0 252, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7b8a4 : bv 32 := 0x00090513.
Lemma F_7b8a4 : fetch_word AsanUbsan.M.loaded_segments (0x7bcbc : word) = Some W_7b8a4.
Proof. vm_refl. Qed.
Lemma D_7b8a4 : decode_any W_7b8a4 = Some (OpImm ALU_ADD 10 18 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7b8a8 : bv 32 := 0xe79fe0ef.
Lemma F_7b8a8 : fetch_word AsanUbsan.M.loaded_segments (0x7bcc0 : word) = Some W_7b8a8.
Proof. vm_refl. Qed.
Lemma D_7b8a8 : decode_any W_7b8a8 = Some (Jal 1 2092664, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7b8ac : bv 32 := 0x02990063.
Lemma F_7b8ac : fetch_word AsanUbsan.M.loaded_segments (0x7bcc4 : word) = Some W_7b8ac.
Proof. vm_refl. Qed.
Lemma D_7b8ac : decode_any W_7b8ac = Some (Branch BC_EQ 18 9 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7b8b0 : bv 32 := 0x409906b3.
Lemma F_7b8b0 : fetch_word AsanUbsan.M.loaded_segments (0x7bcc8 : word) = Some W_7b8b0.
Proof. vm_refl. Qed.
Lemma D_7b8b0 : decode_any W_7b8b0 = Some (Op ALU_SUB 13 18 9, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7b8b4 : bv 32 := 0x00800513.
Lemma F_7b8b4 : fetch_word AsanUbsan.M.loaded_segments (0x7bccc : word) = Some W_7b8b4.
Proof. vm_refl. Qed.
Lemma D_7b8b4 : decode_any W_7b8b4 = Some (OpImm ALU_ADD 10 0 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7b8b8 : bv 32 := 0x02a69e63.
Lemma F_7b8b8 : fetch_word AsanUbsan.M.loaded_segments (0x7bcd0 : word) = Some W_7b8b8.
Proof. vm_refl. Qed.
Lemma D_7b8b8 : decode_any W_7b8b8 = Some (Branch BC_NE 13 10 60, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7b8bc : bv 32 := 0x007af913.
Lemma F_7b8bc : fetch_word AsanUbsan.M.loaded_segments (0x7bcd4 : word) = Some W_7b8bc.
Proof. vm_refl. Qed.
Lemma D_7b8bc : decode_any W_7b8bc = Some (OpImm ALU_AND 18 21 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7b8c0 : bv 32 := 0x00048513.
Lemma F_7b8c0 : fetch_word AsanUbsan.M.loaded_segments (0x7bcd8 : word) = Some W_7b8c0.
Proof. vm_refl. Qed.
Lemma D_7b8c0 : decode_any W_7b8c0 = Some (OpImm ALU_ADD 10 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7b8c4 : bv 32 := 0xb58ff0ef.
Lemma F_7b8c4 : fetch_word AsanUbsan.M.loaded_segments (0x7bcdc : word) = Some W_7b8c4.
Proof. vm_refl. Qed.
Lemma D_7b8c4 : decode_any W_7b8c4 = Some (Jal 1 2093912, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7b8c8 : bv 32 := 0x01250023.
Lemma F_7b8c8 : fetch_word AsanUbsan.M.loaded_segments (0x7bce0 : word) = Some W_7b8c8.
Proof. vm_refl. Qed.
Lemma D_7b8c8 : decode_any W_7b8c8 = Some (Store SZ1 10 18 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7b8cc : bv 32 := 0x06010113.
Lemma F_7b8cc : fetch_word AsanUbsan.M.loaded_segments (0x7bce4 : word) = Some W_7b8cc.
Proof. vm_refl. Qed.
Lemma D_7b8cc : decode_any W_7b8cc = Some (OpImm ALU_ADD 2 2 96, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7b8d0 : bv 32 := 0x7e813083.
Lemma F_7b8d0 : fetch_word AsanUbsan.M.loaded_segments (0x7bce8 : word) = Some W_7b8d0.
Proof. vm_refl. Qed.
Lemma D_7b8d0 : decode_any W_7b8d0 = Some (Load SZ8 true 1 2 2024, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7b8d4 : bv 32 := 0x7e013403.
Lemma F_7b8d4 : fetch_word AsanUbsan.M.loaded_segments (0x7bcec : word) = Some W_7b8d4.
Proof. vm_refl. Qed.
Lemma D_7b8d4 : decode_any W_7b8d4 = Some (Load SZ8 true 8 2 2016, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7b8d8 : bv 32 := 0x7d813483.
Lemma F_7b8d8 : fetch_word AsanUbsan.M.loaded_segments (0x7bcf0 : word) = Some W_7b8d8.
Proof. vm_refl. Qed.
Lemma D_7b8d8 : decode_any W_7b8d8 = Some (Load SZ8 true 9 2 2008, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7b8dc : bv 32 := 0x7d013903.
Lemma F_7b8dc : fetch_word AsanUbsan.M.loaded_segments (0x7bcf4 : word) = Some W_7b8dc.
Proof. vm_refl. Qed.
Lemma D_7b8dc : decode_any W_7b8dc = Some (Load SZ8 true 18 2 2000, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7b8e0 : bv 32 := 0x7c813983.
Lemma F_7b8e0 : fetch_word AsanUbsan.M.loaded_segments (0x7bcf8 : word) = Some W_7b8e0.
Proof. vm_refl. Qed.
Lemma D_7b8e0 : decode_any W_7b8e0 = Some (Load SZ8 true 19 2 1992, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7b8e4 : bv 32 := 0x7c013a03.
Lemma F_7b8e4 : fetch_word AsanUbsan.M.loaded_segments (0x7bcfc : word) = Some W_7b8e4.
Proof. vm_refl. Qed.
Lemma D_7b8e4 : decode_any W_7b8e4 = Some (Load SZ8 true 20 2 1984, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7b8e8 : bv 32 := 0x7b813a83.
Lemma F_7b8e8 : fetch_word AsanUbsan.M.loaded_segments (0x7bd00 : word) = Some W_7b8e8.
Proof. vm_refl. Qed.
Lemma D_7b8e8 : decode_any W_7b8e8 = Some (Load SZ8 true 21 2 1976, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7b8ec : bv 32 := 0x7f010113.
Lemma F_7b8ec : fetch_word AsanUbsan.M.loaded_segments (0x7bd04 : word) = Some W_7b8ec.
Proof. vm_refl. Qed.
Lemma D_7b8ec : decode_any W_7b8ec = Some (OpImm ALU_ADD 2 2 2032, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7b8f0 : bv 32 := 0x00008067.
Lemma F_7b8f0 : fetch_word AsanUbsan.M.loaded_segments (0x7bd08 : word) = Some W_7b8f0.
Proof. vm_refl. Qed.
Lemma D_7b8f0 : decode_any W_7b8f0 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7b8f4 : bv 32 := 0xfffa5517.
Lemma F_7b8f4 : fetch_word AsanUbsan.M.loaded_segments (0x7bd0c : word) = Some W_7b8f4.
Proof. vm_refl. Qed.
Lemma D_7b8f4 : decode_any W_7b8f4 = Some (Auipc 10 1048485, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7b8f8 : bv 32 := 0xfff9d617.
Lemma F_7b8f8 : fetch_word AsanUbsan.M.loaded_segments (0x7bd10 : word) = Some W_7b8f8.
Proof. vm_refl. Qed.
Lemma D_7b8f8 : decode_any W_7b8f8 = Some (Auipc 12 1048477, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7b8fc : bv 32 := 0x1dc00593.
Lemma F_7b8fc : fetch_word AsanUbsan.M.loaded_segments (0x7bd14 : word) = Some W_7b8fc.
Proof. vm_refl. Qed.
Lemma D_7b8fc : decode_any W_7b8fc = Some (OpImm ALU_ADD 11 0 476, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7b900 : bv 32 := 0x5b250513.
Lemma F_7b900 : fetch_word AsanUbsan.M.loaded_segments (0x7bd18 : word) = Some W_7b900.
Proof. vm_refl. Qed.
Lemma D_7b900 : decode_any W_7b900 = Some (OpImm ALU_ADD 10 10 1458, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7b904 : bv 32 := 0xa8f60613.
Lemma F_7b904 : fetch_word AsanUbsan.M.loaded_segments (0x7bd1c : word) = Some W_7b904.
Proof. vm_refl. Qed.
Lemma D_7b904 : decode_any W_7b904 = Some (OpImm ALU_ADD 12 12 2703, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7b908 : bv 32 := 0x00800713.
Lemma F_7b908 : fetch_word AsanUbsan.M.loaded_segments (0x7bd20 : word) = Some W_7b908.
Proof. vm_refl. Qed.
Lemma D_7b908 : decode_any W_7b908 = Some (OpImm ALU_ADD 14 0 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7b90c : bv 32 := 0x460170ef.
Lemma F_7b90c : fetch_word AsanUbsan.M.loaded_segments (0x7bd24 : word) = Some W_7b90c.
Proof. vm_refl. Qed.
Lemma D_7b90c : decode_any W_7b90c = Some (Jal 1 95328, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7b910 : bv 32 := 0x000a8a13.
Lemma F_7b910 : fetch_word AsanUbsan.M.loaded_segments (0x7bd28 : word) = Some W_7b910.
Proof. vm_refl. Qed.
Lemma D_7b910 : decode_any W_7b910 = Some (OpImm ALU_ADD 20 21 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7b914 : bv 32 := 0xf13aece3.
Lemma F_7b914 : fetch_word AsanUbsan.M.loaded_segments (0x7bd2c : word) = Some W_7b914.
Proof. vm_refl. Qed.
Lemma D_7b914 : decode_any W_7b914 = Some (Branch BC_LTU 21 19 7960, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7b918 : bv 32 := 0x00098a13.
Lemma F_7b918 : fetch_word AsanUbsan.M.loaded_segments (0x7bd30 : word) = Some W_7b918.
Proof. vm_refl. Qed.
Lemma D_7b918 : decode_any W_7b918 = Some (OpImm ALU_ADD 20 19 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7b91c : bv 32 := 0xe72aece3.
Lemma F_7b91c : fetch_word AsanUbsan.M.loaded_segments (0x7bd34 : word) = Some W_7b91c.
Proof. vm_refl. Qed.
Lemma D_7b91c : decode_any W_7b91c = Some (Branch BC_LTU 21 18 7800, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7b920 : bv 32 := 0x00090a93.
Lemma F_7b920 : fetch_word AsanUbsan.M.loaded_segments (0x7bd38 : word) = Some W_7b920.
Proof. vm_refl. Qed.
Lemma D_7b920 : decode_any W_7b920 = Some (OpImm ALU_ADD 21 18 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7b924 : bv 32 := 0xe71ff06f.
Lemma F_7b924 : fetch_word AsanUbsan.M.loaded_segments (0x7bd3c : word) = Some W_7b924.
Proof. vm_refl. Qed.
Lemma D_7b924 : decode_any W_7b924 = Some (Jal 0 2096752, 4%Z).
Proof. vm_refl. Qed.
