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
Definition W_81a54 : bv 32 := 0x000bf517.
Lemma F_81a54 : fetch_word AsanUbsan.M.loaded_segments (0x81e6c : word) = Some W_81a54.
Proof. vm_refl. Qed.
Lemma D_81a54 : decode_any W_81a54 = Some (Auipc 10 191, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_81a58 : bv 32 := 0xad052503.
Lemma F_81a58 : fetch_word AsanUbsan.M.loaded_segments (0x81e70 : word) = Some W_81a58.
Proof. vm_refl. Qed.
Lemma D_81a58 : decode_any W_81a58 = Some (Load SZ4 true 10 10 2768, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_81a5c : bv 32 := 0x0230000f.
Lemma F_81a5c : fetch_word AsanUbsan.M.loaded_segments (0x81e74 : word) = Some W_81a5c.
Proof. vm_refl. Qed.
Lemma D_81a5c : decode_any W_81a5c = Some (Fence 0 2 3 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_81a60 : bv 32 := 0x00008067.
Lemma F_81a60 : fetch_word AsanUbsan.M.loaded_segments (0x81e78 : word) = Some W_81a60.
Proof. vm_refl. Qed.
Lemma D_81a60 : decode_any W_81a60 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_81a64 : bv 32 := 0xfb010113.
Lemma F_81a64 : fetch_word AsanUbsan.M.loaded_segments (0x81e7c : word) = Some W_81a64.
Proof. vm_refl. Qed.
Lemma D_81a64 : decode_any W_81a64 = Some (OpImm ALU_ADD 2 2 4016, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_81a68 : bv 32 := 0x04113423.
Lemma F_81a68 : fetch_word AsanUbsan.M.loaded_segments (0x81e80 : word) = Some W_81a68.
Proof. vm_refl. Qed.
Lemma D_81a68 : decode_any W_81a68 = Some (Store SZ8 2 1 72, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_81a6c : bv 32 := 0x04813023.
Lemma F_81a6c : fetch_word AsanUbsan.M.loaded_segments (0x81e84 : word) = Some W_81a6c.
Proof. vm_refl. Qed.
Lemma D_81a6c : decode_any W_81a6c = Some (Store SZ8 2 8 64, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_81a70 : bv 32 := 0x02913c23.
Lemma F_81a70 : fetch_word AsanUbsan.M.loaded_segments (0x81e88 : word) = Some W_81a70.
Proof. vm_refl. Qed.
Lemma D_81a70 : decode_any W_81a70 = Some (Store SZ8 2 9 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_81a74 : bv 32 := 0x03213823.
Lemma F_81a74 : fetch_word AsanUbsan.M.loaded_segments (0x81e8c : word) = Some W_81a74.
Proof. vm_refl. Qed.
Lemma D_81a74 : decode_any W_81a74 = Some (Store SZ8 2 18 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_81a78 : bv 32 := 0x03313423.
Lemma F_81a78 : fetch_word AsanUbsan.M.loaded_segments (0x81e90 : word) = Some W_81a78.
Proof. vm_refl. Qed.
Lemma D_81a78 : decode_any W_81a78 = Some (Store SZ8 2 19 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_81a7c : bv 32 := 0x03413023.
Lemma F_81a7c : fetch_word AsanUbsan.M.loaded_segments (0x81e94 : word) = Some W_81a7c.
Proof. vm_refl. Qed.
Lemma D_81a7c : decode_any W_81a7c = Some (Store SZ8 2 20 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_81a80 : bv 32 := 0x01513c23.
Lemma F_81a80 : fetch_word AsanUbsan.M.loaded_segments (0x81e98 : word) = Some W_81a80.
Proof. vm_refl. Qed.
Lemma D_81a80 : decode_any W_81a80 = Some (Store SZ8 2 21 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_81a84 : bv 32 := 0x01613823.
Lemma F_81a84 : fetch_word AsanUbsan.M.loaded_segments (0x81e9c : word) = Some W_81a84.
Proof. vm_refl. Qed.
Lemma D_81a84 : decode_any W_81a84 = Some (Store SZ8 2 22 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_81a88 : bv 32 := 0x01713423.
Lemma F_81a88 : fetch_word AsanUbsan.M.loaded_segments (0x81ea0 : word) = Some W_81a88.
Proof. vm_refl. Qed.
Lemma D_81a88 : decode_any W_81a88 = Some (Store SZ8 2 23 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_81a8c : bv 32 := 0x01813023.
Lemma F_81a8c : fetch_word AsanUbsan.M.loaded_segments (0x81ea4 : word) = Some W_81a8c.
Proof. vm_refl. Qed.
Lemma D_81a8c : decode_any W_81a8c = Some (Store SZ8 2 24 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_81a90 : bv 32 := 0x00078493.
Lemma F_81a90 : fetch_word AsanUbsan.M.loaded_segments (0x81ea8 : word) = Some W_81a90.
Proof. vm_refl. Qed.
Lemma D_81a90 : decode_any W_81a90 = Some (OpImm ALU_ADD 9 15 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_81a94 : bv 32 := 0x00070a93.
Lemma F_81a94 : fetch_word AsanUbsan.M.loaded_segments (0x81eac : word) = Some W_81a94.
Proof. vm_refl. Qed.
Lemma D_81a94 : decode_any W_81a94 = Some (OpImm ALU_ADD 21 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_81a98 : bv 32 := 0x00068a13.
Lemma F_81a98 : fetch_word AsanUbsan.M.loaded_segments (0x81eb0 : word) = Some W_81a98.
Proof. vm_refl. Qed.
Lemma D_81a98 : decode_any W_81a98 = Some (OpImm ALU_ADD 20 13 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_81a9c : bv 32 := 0x00060413.
Lemma F_81a9c : fetch_word AsanUbsan.M.loaded_segments (0x81eb4 : word) = Some W_81a9c.
Proof. vm_refl. Qed.
Lemma D_81a9c : decode_any W_81a9c = Some (OpImm ALU_ADD 8 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_81aa0 : bv 32 := 0x00058913.
Lemma F_81aa0 : fetch_word AsanUbsan.M.loaded_segments (0x81eb8 : word) = Some W_81aa0.
Proof. vm_refl. Qed.
Lemma D_81aa0 : decode_any W_81aa0 = Some (OpImm ALU_ADD 18 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_81aa4 : bv 32 := 0x00050993.
Lemma F_81aa4 : fetch_word AsanUbsan.M.loaded_segments (0x81ebc : word) = Some W_81aa4.
Proof. vm_refl. Qed.
Lemma D_81aa4 : decode_any W_81aa4 = Some (OpImm ALU_ADD 19 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_81aa8 : bv 32 := 0x00052423.
Lemma F_81aa8 : fetch_word AsanUbsan.M.loaded_segments (0x81ec0 : word) = Some W_81aa8.
Proof. vm_refl. Qed.
Lemma D_81aa8 : decode_any W_81aa8 = Some (Store SZ4 10 0 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_81aac : bv 32 := 0xb10fe0ef.
Lemma F_81aac : fetch_word AsanUbsan.M.loaded_segments (0x81ec4 : word) = Some W_81aac.
Proof. vm_refl. Qed.
Lemma D_81aac : decode_any W_81aac = Some (Jal 1 2089744, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_81ab0 : bv 32 := 0x0c050a63.
Lemma F_81ab0 : fetch_word AsanUbsan.M.loaded_segments (0x81ec8 : word) = Some W_81ab0.
Proof. vm_refl. Qed.
Lemma D_81ab0 : decode_any W_81ab0 = Some (Branch BC_EQ 10 0 212, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_81ab4 : bv 32 := 0x219010ef.
Lemma F_81ab4 : fetch_word AsanUbsan.M.loaded_segments (0x81ecc : word) = Some W_81ab4.
Proof. vm_refl. Qed.
Lemma D_81ab4 : decode_any W_81ab4 = Some (Jal 1 6680, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_81ab8 : bv 32 := 0x04050a63.
Lemma F_81ab8 : fetch_word AsanUbsan.M.loaded_segments (0x81ed0 : word) = Some W_81ab8.
Proof. vm_refl. Qed.
Lemma D_81ab8 : decode_any W_81ab8 = Some (Branch BC_EQ 10 0 84, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_81abc : bv 32 := 0x7ff50c13.
Lemma F_81abc : fetch_word AsanUbsan.M.loaded_segments (0x81ed4 : word) = Some W_81abc.
Proof. vm_refl. Qed.
Lemma D_81abc : decode_any W_81abc = Some (OpImm ALU_ADD 24 10 2047, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_81ac0 : bv 32 := 0x461c4583.
Lemma F_81ac0 : fetch_word AsanUbsan.M.loaded_segments (0x81ed8 : word) = Some W_81ac0.
Proof. vm_refl. Qed.
Lemma D_81ac0 : decode_any W_81ac0 = Some (Load SZ1 false 11 24 1121, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_81ac4 : bv 32 := 0x00100613.
Lemma F_81ac4 : fetch_word AsanUbsan.M.loaded_segments (0x81edc : word) = Some W_81ac4.
Proof. vm_refl. Qed.
Lemma D_81ac4 : decode_any W_81ac4 = Some (OpImm ALU_ADD 12 0 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_81ac8 : bv 32 := 0x46cc00a3.
Lemma F_81ac8 : fetch_word AsanUbsan.M.loaded_segments (0x81ee0 : word) = Some W_81ac8.
Proof. vm_refl. Qed.
Lemma D_81ac8 : decode_any W_81ac8 = Some (Store SZ1 24 12 1121, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_81acc : bv 32 := 0x0a059a63.
Lemma F_81acc : fetch_word AsanUbsan.M.loaded_segments (0x81ee4 : word) = Some W_81acc.
Proof. vm_refl. Qed.
Lemma D_81acc : decode_any W_81acc = Some (Branch BC_NE 11 0 180, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_81ad0 : bv 32 := 0x00050b93.
Lemma F_81ad0 : fetch_word AsanUbsan.M.loaded_segments (0x81ee8 : word) = Some W_81ad0.
Proof. vm_refl. Qed.
Lemma D_81ad0 : decode_any W_81ad0 = Some (OpImm ALU_ADD 23 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_81ad4 : bv 32 := 0x3bd010ef.
Lemma F_81ad4 : fetch_word AsanUbsan.M.loaded_segments (0x81eec : word) = Some W_81ad4.
Proof. vm_refl. Qed.
Lemma D_81ad4 : decode_any W_81ad4 = Some (Jal 1 7100, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_81ad8 : bv 32 := 0x00050b13.
Lemma F_81ad8 : fetch_word AsanUbsan.M.loaded_segments (0x81ef0 : word) = Some W_81ad8.
Proof. vm_refl. Qed.
Lemma D_81ad8 : decode_any W_81ad8 = Some (OpImm ALU_ADD 22 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_81adc : bv 32 := 0x000b8513.
Lemma F_81adc : fetch_word AsanUbsan.M.loaded_segments (0x81ef4 : word) = Some W_81adc.
Proof. vm_refl. Qed.
Lemma D_81adc : decode_any W_81adc = Some (OpImm ALU_ADD 10 23 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_81ae0 : bv 32 := 0x409010ef.
Lemma F_81ae0 : fetch_word AsanUbsan.M.loaded_segments (0x81ef8 : word) = Some W_81ae0.
Proof. vm_refl. Qed.
Lemma D_81ae0 : decode_any W_81ae0 = Some (Jal 1 7176, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_81ae4 : bv 32 := 0x00050813.
Lemma F_81ae4 : fetch_word AsanUbsan.M.loaded_segments (0x81efc : word) = Some W_81ae4.
Proof. vm_refl. Qed.
Lemma D_81ae4 : decode_any W_81ae4 = Some (OpImm ALU_ADD 16 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_81ae8 : bv 32 := 0x060a8c63.
Lemma F_81ae8 : fetch_word AsanUbsan.M.loaded_segments (0x81f00 : word) = Some W_81ae8.
Proof. vm_refl. Qed.
Lemma D_81ae8 : decode_any W_81ae8 = Some (Branch BC_EQ 21 0 120, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_81aec : bv 32 := 0x00100893.
Lemma F_81aec : fetch_word AsanUbsan.M.loaded_segments (0x81f04 : word) = Some W_81aec.
Proof. vm_refl. Qed.
Lemma D_81aec : decode_any W_81aec = Some (OpImm ALU_ADD 17 0 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_81af0 : bv 32 := 0x00098513.
Lemma F_81af0 : fetch_word AsanUbsan.M.loaded_segments (0x81f08 : word) = Some W_81af0.
Proof. vm_refl. Qed.
Lemma D_81af0 : decode_any W_81af0 = Some (OpImm ALU_ADD 10 19 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_81af4 : bv 32 := 0x00048593.
Lemma F_81af4 : fetch_word AsanUbsan.M.loaded_segments (0x81f0c : word) = Some W_81af4.
Proof. vm_refl. Qed.
Lemma D_81af4 : decode_any W_81af4 = Some (OpImm ALU_ADD 11 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_81af8 : bv 32 := 0x00090613.
Lemma F_81af8 : fetch_word AsanUbsan.M.loaded_segments (0x81f10 : word) = Some W_81af8.
Proof. vm_refl. Qed.
Lemma D_81af8 : decode_any W_81af8 = Some (OpImm ALU_ADD 12 18 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_81afc : bv 32 := 0x00040693.
Lemma F_81afc : fetch_word AsanUbsan.M.loaded_segments (0x81f14 : word) = Some W_81afc.
Proof. vm_refl. Qed.
Lemma D_81afc : decode_any W_81afc = Some (OpImm ALU_ADD 13 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_81b00 : bv 32 := 0x00000713.
Lemma F_81b00 : fetch_word AsanUbsan.M.loaded_segments (0x81f18 : word) = Some W_81b00.
Proof. vm_refl. Qed.
Lemma D_81b00 : decode_any W_81b00 = Some (OpImm ALU_ADD 14 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_81b04 : bv 32 := 0x000b0793.
Lemma F_81b04 : fetch_word AsanUbsan.M.loaded_segments (0x81f1c : word) = Some W_81b04.
Proof. vm_refl. Qed.
Lemma D_81b04 : decode_any W_81b04 = Some (OpImm ALU_ADD 15 22 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_81b08 : bv 32 := 0x0740006f.
Lemma F_81b08 : fetch_word AsanUbsan.M.loaded_segments (0x81f20 : word) = Some W_81b08.
Proof. vm_refl. Qed.
Lemma D_81b08 : decode_any W_81b08 = Some (Jal 0 116, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_81b7c : bv 32 := 0x018190ef.
Lemma F_81b7c : fetch_word AsanUbsan.M.loaded_segments (0x81f94 : word) = Some W_81b7c.
Proof. vm_refl. Qed.
Lemma D_81b7c : decode_any W_81b7c = Some (Jal 1 102424, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_81b80 : bv 32 := 0x460c00a3.
Lemma F_81b80 : fetch_word AsanUbsan.M.loaded_segments (0x81f98 : word) = Some W_81b80.
Proof. vm_refl. Qed.
Lemma D_81b80 : decode_any W_81b80 = Some (Store SZ1 24 0 1121, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_81b84 : bv 32 := 0x04813083.
Lemma F_81b84 : fetch_word AsanUbsan.M.loaded_segments (0x81f9c : word) = Some W_81b84.
Proof. vm_refl. Qed.
Lemma D_81b84 : decode_any W_81b84 = Some (Load SZ8 true 1 2 72, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_81b88 : bv 32 := 0x04013403.
Lemma F_81b88 : fetch_word AsanUbsan.M.loaded_segments (0x81fa0 : word) = Some W_81b88.
Proof. vm_refl. Qed.
Lemma D_81b88 : decode_any W_81b88 = Some (Load SZ8 true 8 2 64, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_81b8c : bv 32 := 0x03813483.
Lemma F_81b8c : fetch_word AsanUbsan.M.loaded_segments (0x81fa4 : word) = Some W_81b8c.
Proof. vm_refl. Qed.
Lemma D_81b8c : decode_any W_81b8c = Some (Load SZ8 true 9 2 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_81b90 : bv 32 := 0x03013903.
Lemma F_81b90 : fetch_word AsanUbsan.M.loaded_segments (0x81fa8 : word) = Some W_81b90.
Proof. vm_refl. Qed.
Lemma D_81b90 : decode_any W_81b90 = Some (Load SZ8 true 18 2 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_81b94 : bv 32 := 0x02813983.
Lemma F_81b94 : fetch_word AsanUbsan.M.loaded_segments (0x81fac : word) = Some W_81b94.
Proof. vm_refl. Qed.
Lemma D_81b94 : decode_any W_81b94 = Some (Load SZ8 true 19 2 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_81b98 : bv 32 := 0x02013a03.
Lemma F_81b98 : fetch_word AsanUbsan.M.loaded_segments (0x81fb0 : word) = Some W_81b98.
Proof. vm_refl. Qed.
Lemma D_81b98 : decode_any W_81b98 = Some (Load SZ8 true 20 2 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_81b9c : bv 32 := 0x01813a83.
Lemma F_81b9c : fetch_word AsanUbsan.M.loaded_segments (0x81fb4 : word) = Some W_81b9c.
Proof. vm_refl. Qed.
Lemma D_81b9c : decode_any W_81b9c = Some (Load SZ8 true 21 2 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_81ba0 : bv 32 := 0x01013b03.
Lemma F_81ba0 : fetch_word AsanUbsan.M.loaded_segments (0x81fb8 : word) = Some W_81ba0.
Proof. vm_refl. Qed.
Lemma D_81ba0 : decode_any W_81ba0 = Some (Load SZ8 true 22 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_81ba4 : bv 32 := 0x00813b83.
Lemma F_81ba4 : fetch_word AsanUbsan.M.loaded_segments (0x81fbc : word) = Some W_81ba4.
Proof. vm_refl. Qed.
Lemma D_81ba4 : decode_any W_81ba4 = Some (Load SZ8 true 23 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_81ba8 : bv 32 := 0x00013c03.
Lemma F_81ba8 : fetch_word AsanUbsan.M.loaded_segments (0x81fc0 : word) = Some W_81ba8.
Proof. vm_refl. Qed.
Lemma D_81ba8 : decode_any W_81ba8 = Some (Load SZ8 true 24 2 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_81bac : bv 32 := 0x05010113.
Lemma F_81bac : fetch_word AsanUbsan.M.loaded_segments (0x81fc4 : word) = Some W_81bac.
Proof. vm_refl. Qed.
Lemma D_81bac : decode_any W_81bac = Some (OpImm ALU_ADD 2 2 80, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_81bb0 : bv 32 := 0x00008067.
Lemma F_81bb0 : fetch_word AsanUbsan.M.loaded_segments (0x81fc8 : word) = Some W_81bb0.
Proof. vm_refl. Qed.
Lemma D_81bb0 : decode_any W_81bb0 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.
