(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
(* [comment removed for export] *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require BvWfKernel.

From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.jsoncons.fuzz_ubjson_encoder.images Require Import AsanUbsan.
Open Scope bv_scope.

Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

Definition W_7a970 : bv 32 := 0x0100006f.
Lemma F_7a970 : fetch_word AsanUbsan.M.loaded_segments (0x7a9c0 : word) = Some W_7a970.
Proof. vm_refl. Qed.
Lemma D_7a970 : decode_any W_7a970 = Some (Jal 0 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_7a974 : bv 32 := 0x1dc0006f.
Lemma F_7a974 : fetch_word AsanUbsan.M.loaded_segments (0x7a9c4 : word) = Some W_7a974.
Proof. vm_refl. Qed.
Lemma D_7a974 : decode_any W_7a974 = Some (Jal 0 476, 4%Z).
Proof. vm_refl. Qed.

Definition W_7a97c : bv 32 := 0x7400006f.
Lemma F_7a97c : fetch_word AsanUbsan.M.loaded_segments (0x7a9cc : word) = Some W_7a97c.
Proof. vm_refl. Qed.
Lemma D_7a97c : decode_any W_7a97c = Some (Jal 0 1856, 4%Z).
Proof. vm_refl. Qed.

Definition W_7a980 : bv 32 := 0x81010113.
Lemma F_7a980 : fetch_word AsanUbsan.M.loaded_segments (0x7a9d0 : word) = Some W_7a980.
Proof. vm_refl. Qed.
Lemma D_7a980 : decode_any W_7a980 = Some (OpImm ALU_ADD 2 2 2064, 4%Z).
Proof. vm_refl. Qed.

Definition W_7a984 : bv 32 := 0x7e113423.
Lemma F_7a984 : fetch_word AsanUbsan.M.loaded_segments (0x7a9d4 : word) = Some W_7a984.
Proof. vm_refl. Qed.
Lemma D_7a984 : decode_any W_7a984 = Some (Store SZ8 2 1 2024, 4%Z).
Proof. vm_refl. Qed.

Definition W_7a988 : bv 32 := 0x7e813023.
Lemma F_7a988 : fetch_word AsanUbsan.M.loaded_segments (0x7a9d8 : word) = Some W_7a988.
Proof. vm_refl. Qed.
Lemma D_7a988 : decode_any W_7a988 = Some (Store SZ8 2 8 2016, 4%Z).
Proof. vm_refl. Qed.

Definition W_7a98c : bv 32 := 0x7c913c23.
Lemma F_7a98c : fetch_word AsanUbsan.M.loaded_segments (0x7a9dc : word) = Some W_7a98c.
Proof. vm_refl. Qed.
Lemma D_7a98c : decode_any W_7a98c = Some (Store SZ8 2 9 2008, 4%Z).
Proof. vm_refl. Qed.

Definition W_7a990 : bv 32 := 0x7d213823.
Lemma F_7a990 : fetch_word AsanUbsan.M.loaded_segments (0x7a9e0 : word) = Some W_7a990.
Proof. vm_refl. Qed.
Lemma D_7a990 : decode_any W_7a990 = Some (Store SZ8 2 18 2000, 4%Z).
Proof. vm_refl. Qed.

Definition W_7a994 : bv 32 := 0x7d313423.
Lemma F_7a994 : fetch_word AsanUbsan.M.loaded_segments (0x7a9e4 : word) = Some W_7a994.
Proof. vm_refl. Qed.
Lemma D_7a994 : decode_any W_7a994 = Some (Store SZ8 2 19 1992, 4%Z).
Proof. vm_refl. Qed.

Definition W_7a998 : bv 32 := 0x7d413023.
Lemma F_7a998 : fetch_word AsanUbsan.M.loaded_segments (0x7a9e8 : word) = Some W_7a998.
Proof. vm_refl. Qed.
Lemma D_7a998 : decode_any W_7a998 = Some (Store SZ8 2 20 1984, 4%Z).
Proof. vm_refl. Qed.

Definition W_7a99c : bv 32 := 0x7b513c23.
Lemma F_7a99c : fetch_word AsanUbsan.M.loaded_segments (0x7a9ec : word) = Some W_7a99c.
Proof. vm_refl. Qed.
Lemma D_7a99c : decode_any W_7a99c = Some (Store SZ8 2 21 1976, 4%Z).
Proof. vm_refl. Qed.

Definition W_7a9a0 : bv 32 := 0x7f010413.
Lemma F_7a9a0 : fetch_word AsanUbsan.M.loaded_segments (0x7a9f0 : word) = Some W_7a9a0.
Proof. vm_refl. Qed.
Lemma D_7a9a0 : decode_any W_7a9a0 = Some (OpImm ALU_ADD 8 2 2032, 4%Z).
Proof. vm_refl. Qed.

Definition W_7a9a4 : bv 32 := 0xfa010113.
Lemma F_7a9a4 : fetch_word AsanUbsan.M.loaded_segments (0x7a9f4 : word) = Some W_7a9a4.
Proof. vm_refl. Qed.
Lemma D_7a9a4 : decode_any W_7a9a4 = Some (OpImm ALU_ADD 2 2 4000, 4%Z).
Proof. vm_refl. Qed.

Definition W_7a9a8 : bv 32 := 0x00008913.
Lemma F_7a9a8 : fetch_word AsanUbsan.M.loaded_segments (0x7a9f8 : word) = Some W_7a9a8.
Proof. vm_refl. Qed.
Lemma D_7a9a8 : decode_any W_7a9a8 = Some (OpImm ALU_ADD 18 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7a9ac : bv 32 := 0x00050493.
Lemma F_7a9ac : fetch_word AsanUbsan.M.loaded_segments (0x7a9fc : word) = Some W_7a9ac.
Proof. vm_refl. Qed.
Lemma D_7a9ac : decode_any W_7a9ac = Some (OpImm ALU_ADD 9 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7a9b0 : bv 32 := 0x10c0c0ef.
Lemma F_7a9b0 : fetch_word AsanUbsan.M.loaded_segments (0x7aa00 : word) = Some W_7a9b0.
Proof. vm_refl. Qed.
Lemma D_7a9b0 : decode_any W_7a9b0 = Some (Jal 1 49420, 4%Z).
Proof. vm_refl. Qed.

Definition W_7a9b4 : bv 32 := 0x02f4d593.
Lemma F_7a9b4 : fetch_word AsanUbsan.M.loaded_segments (0x7aa04 : word) = Some W_7a9b4.
Proof. vm_refl. Qed.
Lemma D_7a9b4 : decode_any W_7a9b4 = Some (ShiftImm ALU_SRL 11 9 47, 4%Z).
Proof. vm_refl. Qed.

Definition W_7a9b8 : bv 32 := 0x0a059063.
Lemma F_7a9b8 : fetch_word AsanUbsan.M.loaded_segments (0x7aa08 : word) = Some W_7a9b8.
Proof. vm_refl. Qed.
Lemma D_7a9b8 : decode_any W_7a9b8 = Some (Branch BC_NE 11 0 160, 4%Z).
Proof. vm_refl. Qed.

Definition W_7a9bc : bv 32 := 0x0204d593.
Lemma F_7a9bc : fetch_word AsanUbsan.M.loaded_segments (0x7aa0c : word) = Some W_7a9bc.
Proof. vm_refl. Qed.
Lemma D_7a9bc : decode_any W_7a9bc = Some (ShiftImm ALU_SRL 11 9 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_7a9c0 : bv 32 := 0x00359613.
Lemma F_7a9c0 : fetch_word AsanUbsan.M.loaded_segments (0x7aa10 : word) = Some W_7a9c0.
Proof. vm_refl. Qed.
Lemma D_7a9c0 : decode_any W_7a9c0 = Some (ShiftImm ALU_SLL 12 11 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_7a9c4 : bv 32 := 0x00c50633.
Lemma F_7a9c4 : fetch_word AsanUbsan.M.loaded_segments (0x7aa14 : word) = Some W_7a9c4.
Proof. vm_refl. Qed.
Lemma D_7a9c4 : decode_any W_7a9c4 = Some (Op ALU_ADD 12 10 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_7a9c8 : bv 32 := 0x00863683.
Lemma F_7a9c8 : fetch_word AsanUbsan.M.loaded_segments (0x7aa18 : word) = Some W_7a9c8.
Proof. vm_refl. Qed.
Lemma D_7a9c8 : decode_any W_7a9c8 = Some (Load SZ8 true 13 12 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_7a9cc : bv 32 := 0x0230000f.
Lemma F_7a9cc : fetch_word AsanUbsan.M.loaded_segments (0x7aa1c : word) = Some W_7a9cc.
Proof. vm_refl. Qed.
Lemma D_7a9cc : decode_any W_7a9cc = Some (Fence 0 2 3 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7a9d0 : bv 32 := 0x08068463.
Lemma F_7a9d0 : fetch_word AsanUbsan.M.loaded_segments (0x7aa20 : word) = Some W_7a9d0.
Proof. vm_refl. Qed.
Lemma D_7a9d0 : decode_any W_7a9d0 = Some (Branch BC_EQ 13 0 136, 4%Z).
Proof. vm_refl. Qed.

Definition W_7aa58 : bv 32 := 0x80040a13.
Lemma F_7aa58 : fetch_word AsanUbsan.M.loaded_segments (0x7aaa8 : word) = Some W_7aa58.
Proof. vm_refl. Qed.
Lemma D_7aa58 : decode_any W_7aa58 = Some (OpImm ALU_ADD 20 8 2048, 4%Z).
Proof. vm_refl. Qed.

Definition W_7aa5c : bv 32 := 0xfb0a0a13.
Lemma F_7aa5c : fetch_word AsanUbsan.M.loaded_segments (0x7aaac : word) = Some W_7aa5c.
Proof. vm_refl. Qed.
Lemma D_7aa5c : decode_any W_7aa5c = Some (OpImm ALU_ADD 20 20 4016, 4%Z).
Proof. vm_refl. Qed.

Definition W_7aa60 : bv 32 := 0x80040513.
Lemma F_7aa60 : fetch_word AsanUbsan.M.loaded_segments (0x7aab0 : word) = Some W_7aa60.
Proof. vm_refl. Qed.
Lemma D_7aa60 : decode_any W_7aa60 = Some (OpImm ALU_ADD 10 8 2048, 4%Z).
Proof. vm_refl. Qed.

Definition W_7aa64 : bv 32 := 0xfc050513.
Lemma F_7aa64 : fetch_word AsanUbsan.M.loaded_segments (0x7aab4 : word) = Some W_7aa64.
Proof. vm_refl. Qed.
Lemma D_7aa64 : decode_any W_7aa64 = Some (OpImm ALU_ADD 10 10 4032, 4%Z).
Proof. vm_refl. Qed.

Definition W_7aa68 : bv 32 := 0x7ffa0a93.
Lemma F_7aa68 : fetch_word AsanUbsan.M.loaded_segments (0x7aab8 : word) = Some W_7aa68.
Proof. vm_refl. Qed.
Lemma D_7aa68 : decode_any W_7aa68 = Some (OpImm ALU_ADD 21 20 2047, 4%Z).
Proof. vm_refl. Qed.

Definition W_7aa6c : bv 32 := 0x000ab4a3.
Lemma F_7aa6c : fetch_word AsanUbsan.M.loaded_segments (0x7aabc : word) = Some W_7aa6c.
Proof. vm_refl. Qed.
Lemma D_7aa6c : decode_any W_7aa6c = Some (Store SZ8 21 0 9, 4%Z).
Proof. vm_refl. Qed.

Definition W_7aa70 : bv 32 := 0x00aa3023.
Lemma F_7aa70 : fetch_word AsanUbsan.M.loaded_segments (0x7aac0 : word) = Some W_7aa70.
Proof. vm_refl. Qed.
Lemma D_7aa70 : decode_any W_7aa70 = Some (Store SZ8 20 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7aa74 : bv 32 := 0x000a3423.
Lemma F_7aa74 : fetch_word AsanUbsan.M.loaded_segments (0x7aac4 : word) = Some W_7aa74.
Proof. vm_refl. Qed.
Lemma D_7aa74 : decode_any W_7aa74 = Some (Store SZ8 20 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_7aa78 : bv 32 := 0x550080ef.
Lemma F_7aa78 : fetch_word AsanUbsan.M.loaded_segments (0x7aac8 : word) = Some W_7aa78.
Proof. vm_refl. Qed.
Lemma D_7aa78 : decode_any W_7aa78 = Some (Jal 1 34128, 4%Z).
Proof. vm_refl. Qed.

Definition W_7aa7c : bv 32 := 0x00200593.
Lemma F_7aa7c : fetch_word AsanUbsan.M.loaded_segments (0x7aacc : word) = Some W_7aa7c.
Proof. vm_refl. Qed.
Lemma D_7aa7c : decode_any W_7aa7c = Some (OpImm ALU_ADD 11 0 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_7aa80 : bv 32 := 0x02a5ea63.
Lemma F_7aa80 : fetch_word AsanUbsan.M.loaded_segments (0x7aad0 : word) = Some W_7aa80.
Proof. vm_refl. Qed.
Lemma D_7aa80 : decode_any W_7aa80 = Some (Branch BC_LTU 11 10 52, 4%Z).
Proof. vm_refl. Qed.

Definition W_7aab4 : bv 32 := 0x7f1200ef.
Lemma F_7aab4 : fetch_word AsanUbsan.M.loaded_segments (0x7ab04 : word) = Some W_7aab4.
Proof. vm_refl. Qed.
Lemma D_7aab4 : decode_any W_7aab4 = Some (Jal 1 135152, 4%Z).
Proof. vm_refl. Qed.

Definition W_7aab8 : bv 32 := 0x000c3597.
Lemma F_7aab8 : fetch_word AsanUbsan.M.loaded_segments (0x7ab08 : word) = Some W_7aab8.
Proof. vm_refl. Qed.
Lemma D_7aab8 : decode_any W_7aab8 = Some (Auipc 11 195, 4%Z).
Proof. vm_refl. Qed.

Definition W_7aabc : bv 32 := 0xdb05b583.
Lemma F_7aabc : fetch_word AsanUbsan.M.loaded_segments (0x7ab0c : word) = Some W_7aabc.
Proof. vm_refl. Qed.
Lemma D_7aabc : decode_any W_7aabc = Some (Load SZ8 true 11 11 3504, 4%Z).
Proof. vm_refl. Qed.

Definition W_7aac0 : bv 32 := 0x0225c983.
Lemma F_7aac0 : fetch_word AsanUbsan.M.loaded_segments (0x7ab10 : word) = Some W_7aac0.
Proof. vm_refl. Qed.
Lemma D_7aac0 : decode_any W_7aac0 = Some (Load SZ1 false 19 11 34, 4%Z).
Proof. vm_refl. Qed.

Definition W_7aac4 : bv 32 := 0x00050913.
Lemma F_7aac4 : fetch_word AsanUbsan.M.loaded_segments (0x7ab14 : word) = Some W_7aac4.
Proof. vm_refl. Qed.
Lemma D_7aac4 : decode_any W_7aac4 = Some (OpImm ALU_ADD 18 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7aac8 : bv 32 := 0x500080ef.
Lemma F_7aac8 : fetch_word AsanUbsan.M.loaded_segments (0x7ab18 : word) = Some W_7aac8.
Proof. vm_refl. Qed.
Lemma D_7aac8 : decode_any W_7aac8 = Some (Jal 1 34048, 4%Z).
Proof. vm_refl. Qed.

Definition W_7aacc : bv 32 := 0x00050793.
Lemma F_7aacc : fetch_word AsanUbsan.M.loaded_segments (0x7ab1c : word) = Some W_7aacc.
Proof. vm_refl. Qed.
Lemma D_7aacc : decode_any W_7aacc = Some (OpImm ALU_ADD 15 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7aad0 : bv 32 := 0x00153513.
Lemma F_7aad0 : fetch_word AsanUbsan.M.loaded_segments (0x7ab20 : word) = Some W_7aad0.
Proof. vm_refl. Qed.
Lemma D_7aad0 : decode_any W_7aad0 = Some (OpImm ALU_SLTU 10 10 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_7aad4 : bv 32 := 0xfff50513.
Lemma F_7aad4 : fetch_word AsanUbsan.M.loaded_segments (0x7ab24 : word) = Some W_7aad4.
Proof. vm_refl. Qed.
Lemma D_7aad4 : decode_any W_7aad4 = Some (OpImm ALU_ADD 10 10 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_7aad8 : bv 32 := 0x008575b3.
Lemma F_7aad8 : fetch_word AsanUbsan.M.loaded_segments (0x7ab28 : word) = Some W_7aad8.
Proof. vm_refl. Qed.
Lemma D_7aad8 : decode_any W_7aad8 = Some (Op ALU_AND 11 10 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_7aadc : bv 32 := 0x00100513.
Lemma F_7aadc : fetch_word AsanUbsan.M.loaded_segments (0x7ab2c : word) = Some W_7aadc.
Proof. vm_refl. Qed.
Lemma D_7aadc : decode_any W_7aadc = Some (OpImm ALU_ADD 10 0 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_7aae0 : bv 32 := 0x00bab4a3.
Lemma F_7aae0 : fetch_word AsanUbsan.M.loaded_segments (0x7ab30 : word) = Some W_7aae0.
Proof. vm_refl. Qed.
Lemma D_7aae0 : decode_any W_7aae0 = Some (Store SZ8 21 11 9, 4%Z).
Proof. vm_refl. Qed.

Definition W_7aae4 : bv 32 := 0x00f56a63.
Lemma F_7aae4 : fetch_word AsanUbsan.M.loaded_segments (0x7ab34 : word) = Some W_7aae4.
Proof. vm_refl. Qed.
Lemma D_7aae4 : decode_any W_7aae4 = Some (Branch BC_LTU 10 15 20, 4%Z).
Proof. vm_refl. Qed.

Definition W_7aaf8 : bv 32 := 0x80040513.
Lemma F_7aaf8 : fetch_word AsanUbsan.M.loaded_segments (0x7ab48 : word) = Some W_7aaf8.
Proof. vm_refl. Qed.
Lemma D_7aaf8 : decode_any W_7aaf8 = Some (OpImm ALU_ADD 10 8 2048, 4%Z).
Proof. vm_refl. Qed.

Definition W_7aafc : bv 32 := 0xfb050513.
Lemma F_7aafc : fetch_word AsanUbsan.M.loaded_segments (0x7ab4c : word) = Some W_7aafc.
Proof. vm_refl. Qed.
Lemma D_7aafc : decode_any W_7aafc = Some (OpImm ALU_ADD 10 10 4016, 4%Z).
Proof. vm_refl. Qed.

Definition W_7ab00 : bv 32 := 0x00090593.
Lemma F_7ab00 : fetch_word AsanUbsan.M.loaded_segments (0x7ab50 : word) = Some W_7ab00.
Proof. vm_refl. Qed.
Lemma D_7ab00 : decode_any W_7ab00 = Some (OpImm ALU_ADD 11 18 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7ab04 : bv 32 := 0x00040613.
Lemma F_7ab04 : fetch_word AsanUbsan.M.loaded_segments (0x7ab54 : word) = Some W_7ab04.
Proof. vm_refl. Qed.
Lemma D_7ab04 : decode_any W_7ab04 = Some (OpImm ALU_ADD 12 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7ab08 : bv 32 := 0x00000693.
Lemma F_7ab08 : fetch_word AsanUbsan.M.loaded_segments (0x7ab58 : word) = Some W_7ab08.
Proof. vm_refl. Qed.
Lemma D_7ab08 : decode_any W_7ab08 = Some (OpImm ALU_ADD 13 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7ab0c : bv 32 := 0x00098713.
Lemma F_7ab0c : fetch_word AsanUbsan.M.loaded_segments (0x7ab5c : word) = Some W_7ab0c.
Proof. vm_refl. Qed.
Lemma D_7ab0c : decode_any W_7ab0c = Some (OpImm ALU_ADD 14 19 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7ab10 : bv 32 := 0x4c8080ef.
Lemma F_7ab10 : fetch_word AsanUbsan.M.loaded_segments (0x7ab60 : word) = Some W_7ab10.
Proof. vm_refl. Qed.
Lemma D_7ab10 : decode_any W_7ab10 = Some (Jal 1 33992, 4%Z).
Proof. vm_refl. Qed.

Definition W_7ab14 : bv 32 := 0x80040593.
Lemma F_7ab14 : fetch_word AsanUbsan.M.loaded_segments (0x7ab64 : word) = Some W_7ab14.
Proof. vm_refl. Qed.
Lemma D_7ab14 : decode_any W_7ab14 = Some (OpImm ALU_ADD 11 8 2048, 4%Z).
Proof. vm_refl. Qed.

Definition W_7ab18 : bv 32 := 0xfb058593.
Lemma F_7ab18 : fetch_word AsanUbsan.M.loaded_segments (0x7ab68 : word) = Some W_7ab18.
Proof. vm_refl. Qed.
Lemma D_7ab18 : decode_any W_7ab18 = Some (OpImm ALU_ADD 11 11 4016, 4%Z).
Proof. vm_refl. Qed.

Definition W_7ab1c : bv 32 := 0x00100613.
Lemma F_7ab1c : fetch_word AsanUbsan.M.loaded_segments (0x7ab6c : word) = Some W_7ab1c.
Proof. vm_refl. Qed.
Lemma D_7ab1c : decode_any W_7ab1c = Some (OpImm ALU_ADD 12 0 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_7ab20 : bv 32 := 0x00048513.
Lemma F_7ab20 : fetch_word AsanUbsan.M.loaded_segments (0x7ab70 : word) = Some W_7ab20.
Proof. vm_refl. Qed.
Lemma D_7ab20 : decode_any W_7ab20 = Some (OpImm ALU_ADD 10 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7ab24 : bv 32 := 0xf44d80ef.
Lemma F_7ab24 : fetch_word AsanUbsan.M.loaded_segments (0x7ab74 : word) = Some W_7ab24.
Proof. vm_refl. Qed.
Lemma D_7ab24 : decode_any W_7ab24 = Some (Jal 1 1935172, 4%Z).
Proof. vm_refl. Qed.

Definition W_7ab28 : bv 32 := 0x06010113.
Lemma F_7ab28 : fetch_word AsanUbsan.M.loaded_segments (0x7ab78 : word) = Some W_7ab28.
Proof. vm_refl. Qed.
Lemma D_7ab28 : decode_any W_7ab28 = Some (OpImm ALU_ADD 2 2 96, 4%Z).
Proof. vm_refl. Qed.

Definition W_7ab2c : bv 32 := 0x7e813083.
Lemma F_7ab2c : fetch_word AsanUbsan.M.loaded_segments (0x7ab7c : word) = Some W_7ab2c.
Proof. vm_refl. Qed.
Lemma D_7ab2c : decode_any W_7ab2c = Some (Load SZ8 true 1 2 2024, 4%Z).
Proof. vm_refl. Qed.

Definition W_7ab30 : bv 32 := 0x7e013403.
Lemma F_7ab30 : fetch_word AsanUbsan.M.loaded_segments (0x7ab80 : word) = Some W_7ab30.
Proof. vm_refl. Qed.
Lemma D_7ab30 : decode_any W_7ab30 = Some (Load SZ8 true 8 2 2016, 4%Z).
Proof. vm_refl. Qed.

Definition W_7ab34 : bv 32 := 0x7d813483.
Lemma F_7ab34 : fetch_word AsanUbsan.M.loaded_segments (0x7ab84 : word) = Some W_7ab34.
Proof. vm_refl. Qed.
Lemma D_7ab34 : decode_any W_7ab34 = Some (Load SZ8 true 9 2 2008, 4%Z).
Proof. vm_refl. Qed.

Definition W_7ab38 : bv 32 := 0x7d013903.
Lemma F_7ab38 : fetch_word AsanUbsan.M.loaded_segments (0x7ab88 : word) = Some W_7ab38.
Proof. vm_refl. Qed.
Lemma D_7ab38 : decode_any W_7ab38 = Some (Load SZ8 true 18 2 2000, 4%Z).
Proof. vm_refl. Qed.

Definition W_7ab3c : bv 32 := 0x7c813983.
Lemma F_7ab3c : fetch_word AsanUbsan.M.loaded_segments (0x7ab8c : word) = Some W_7ab3c.
Proof. vm_refl. Qed.
Lemma D_7ab3c : decode_any W_7ab3c = Some (Load SZ8 true 19 2 1992, 4%Z).
Proof. vm_refl. Qed.

Definition W_7ab40 : bv 32 := 0x7c013a03.
Lemma F_7ab40 : fetch_word AsanUbsan.M.loaded_segments (0x7ab90 : word) = Some W_7ab40.
Proof. vm_refl. Qed.
Lemma D_7ab40 : decode_any W_7ab40 = Some (Load SZ8 true 20 2 1984, 4%Z).
Proof. vm_refl. Qed.

Definition W_7ab44 : bv 32 := 0x7b813a83.
Lemma F_7ab44 : fetch_word AsanUbsan.M.loaded_segments (0x7ab94 : word) = Some W_7ab44.
Proof. vm_refl. Qed.
Lemma D_7ab44 : decode_any W_7ab44 = Some (Load SZ8 true 21 2 1976, 4%Z).
Proof. vm_refl. Qed.

Definition W_7ab48 : bv 32 := 0x7f010113.
Lemma F_7ab48 : fetch_word AsanUbsan.M.loaded_segments (0x7ab98 : word) = Some W_7ab48.
Proof. vm_refl. Qed.
Lemma D_7ab48 : decode_any W_7ab48 = Some (OpImm ALU_ADD 2 2 2032, 4%Z).
Proof. vm_refl. Qed.

Definition W_7ab4c : bv 32 := 0x00008067.
Lemma F_7ab4c : fetch_word AsanUbsan.M.loaded_segments (0x7ab9c : word) = Some W_7ab4c.
Proof. vm_refl. Qed.
Lemma D_7ab4c : decode_any W_7ab4c = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7ab50 : bv 32 := 0x81010113.
Lemma F_7ab50 : fetch_word AsanUbsan.M.loaded_segments (0x7aba0 : word) = Some W_7ab50.
Proof. vm_refl. Qed.
Lemma D_7ab50 : decode_any W_7ab50 = Some (OpImm ALU_ADD 2 2 2064, 4%Z).
Proof. vm_refl. Qed.

Definition W_7ab54 : bv 32 := 0x7e113423.
Lemma F_7ab54 : fetch_word AsanUbsan.M.loaded_segments (0x7aba4 : word) = Some W_7ab54.
Proof. vm_refl. Qed.
Lemma D_7ab54 : decode_any W_7ab54 = Some (Store SZ8 2 1 2024, 4%Z).
Proof. vm_refl. Qed.

Definition W_7ab58 : bv 32 := 0x7e813023.
Lemma F_7ab58 : fetch_word AsanUbsan.M.loaded_segments (0x7aba8 : word) = Some W_7ab58.
Proof. vm_refl. Qed.
Lemma D_7ab58 : decode_any W_7ab58 = Some (Store SZ8 2 8 2016, 4%Z).
Proof. vm_refl. Qed.

Definition W_7ab5c : bv 32 := 0x7c913c23.
Lemma F_7ab5c : fetch_word AsanUbsan.M.loaded_segments (0x7abac : word) = Some W_7ab5c.
Proof. vm_refl. Qed.
Lemma D_7ab5c : decode_any W_7ab5c = Some (Store SZ8 2 9 2008, 4%Z).
Proof. vm_refl. Qed.

Definition W_7ab60 : bv 32 := 0x7d213823.
Lemma F_7ab60 : fetch_word AsanUbsan.M.loaded_segments (0x7abb0 : word) = Some W_7ab60.
Proof. vm_refl. Qed.
Lemma D_7ab60 : decode_any W_7ab60 = Some (Store SZ8 2 18 2000, 4%Z).
Proof. vm_refl. Qed.

Definition W_7ab64 : bv 32 := 0x7d313423.
Lemma F_7ab64 : fetch_word AsanUbsan.M.loaded_segments (0x7abb4 : word) = Some W_7ab64.
Proof. vm_refl. Qed.
Lemma D_7ab64 : decode_any W_7ab64 = Some (Store SZ8 2 19 1992, 4%Z).
Proof. vm_refl. Qed.

Definition W_7ab68 : bv 32 := 0x7d413023.
Lemma F_7ab68 : fetch_word AsanUbsan.M.loaded_segments (0x7abb8 : word) = Some W_7ab68.
Proof. vm_refl. Qed.
Lemma D_7ab68 : decode_any W_7ab68 = Some (Store SZ8 2 20 1984, 4%Z).
Proof. vm_refl. Qed.

Definition W_7ab6c : bv 32 := 0x7b513c23.
Lemma F_7ab6c : fetch_word AsanUbsan.M.loaded_segments (0x7abbc : word) = Some W_7ab6c.
Proof. vm_refl. Qed.
Lemma D_7ab6c : decode_any W_7ab6c = Some (Store SZ8 2 21 1976, 4%Z).
Proof. vm_refl. Qed.

Definition W_7ab70 : bv 32 := 0x7f010413.
Lemma F_7ab70 : fetch_word AsanUbsan.M.loaded_segments (0x7abc0 : word) = Some W_7ab70.
Proof. vm_refl. Qed.
Lemma D_7ab70 : decode_any W_7ab70 = Some (OpImm ALU_ADD 8 2 2032, 4%Z).
Proof. vm_refl. Qed.

Definition W_7ab74 : bv 32 := 0xfa010113.
Lemma F_7ab74 : fetch_word AsanUbsan.M.loaded_segments (0x7abc4 : word) = Some W_7ab74.
Proof. vm_refl. Qed.
Lemma D_7ab74 : decode_any W_7ab74 = Some (OpImm ALU_ADD 2 2 4000, 4%Z).
Proof. vm_refl. Qed.

Definition W_7ab78 : bv 32 := 0x00008913.
Lemma F_7ab78 : fetch_word AsanUbsan.M.loaded_segments (0x7abc8 : word) = Some W_7ab78.
Proof. vm_refl. Qed.
Lemma D_7ab78 : decode_any W_7ab78 = Some (OpImm ALU_ADD 18 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7ab7c : bv 32 := 0x00050493.
Lemma F_7ab7c : fetch_word AsanUbsan.M.loaded_segments (0x7abcc : word) = Some W_7ab7c.
Proof. vm_refl. Qed.
Lemma D_7ab7c : decode_any W_7ab7c = Some (OpImm ALU_ADD 9 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7ab80 : bv 32 := 0x6c0070ef.
Lemma F_7ab80 : fetch_word AsanUbsan.M.loaded_segments (0x7abd0 : word) = Some W_7ab80.
Proof. vm_refl. Qed.
Lemma D_7ab80 : decode_any W_7ab80 = Some (Jal 1 30400, 4%Z).
Proof. vm_refl. Qed.

Definition W_7ab84 : bv 32 := 0x06050063.
Lemma F_7ab84 : fetch_word AsanUbsan.M.loaded_segments (0x7abd4 : word) = Some W_7ab84.
Proof. vm_refl. Qed.
Lemma D_7ab84 : decode_any W_7ab84 = Some (Branch BC_EQ 10 0 96, 4%Z).
Proof. vm_refl. Qed.

Definition W_7ab88 : bv 32 := 0x80040a13.
Lemma F_7ab88 : fetch_word AsanUbsan.M.loaded_segments (0x7abd8 : word) = Some W_7ab88.
Proof. vm_refl. Qed.
Lemma D_7ab88 : decode_any W_7ab88 = Some (OpImm ALU_ADD 20 8 2048, 4%Z).
Proof. vm_refl. Qed.

Definition W_7ab8c : bv 32 := 0xfb0a0a13.
Lemma F_7ab8c : fetch_word AsanUbsan.M.loaded_segments (0x7abdc : word) = Some W_7ab8c.
Proof. vm_refl. Qed.
Lemma D_7ab8c : decode_any W_7ab8c = Some (OpImm ALU_ADD 20 20 4016, 4%Z).
Proof. vm_refl. Qed.

Definition W_7ab90 : bv 32 := 0x80040513.
Lemma F_7ab90 : fetch_word AsanUbsan.M.loaded_segments (0x7abe0 : word) = Some W_7ab90.
Proof. vm_refl. Qed.
Lemma D_7ab90 : decode_any W_7ab90 = Some (OpImm ALU_ADD 10 8 2048, 4%Z).
Proof. vm_refl. Qed.

Definition W_7ab94 : bv 32 := 0xfc050513.
Lemma F_7ab94 : fetch_word AsanUbsan.M.loaded_segments (0x7abe4 : word) = Some W_7ab94.
Proof. vm_refl. Qed.
Lemma D_7ab94 : decode_any W_7ab94 = Some (OpImm ALU_ADD 10 10 4032, 4%Z).
Proof. vm_refl. Qed.

Definition W_7ab98 : bv 32 := 0x7ffa0a93.
Lemma F_7ab98 : fetch_word AsanUbsan.M.loaded_segments (0x7abe8 : word) = Some W_7ab98.
Proof. vm_refl. Qed.
Lemma D_7ab98 : decode_any W_7ab98 = Some (OpImm ALU_ADD 21 20 2047, 4%Z).
Proof. vm_refl. Qed.

Definition W_7ab9c : bv 32 := 0x000ab4a3.
Lemma F_7ab9c : fetch_word AsanUbsan.M.loaded_segments (0x7abec : word) = Some W_7ab9c.
Proof. vm_refl. Qed.
Lemma D_7ab9c : decode_any W_7ab9c = Some (Store SZ8 21 0 9, 4%Z).
Proof. vm_refl. Qed.

Definition W_7aba0 : bv 32 := 0x00aa3023.
Lemma F_7aba0 : fetch_word AsanUbsan.M.loaded_segments (0x7abf0 : word) = Some W_7aba0.
Proof. vm_refl. Qed.
Lemma D_7aba0 : decode_any W_7aba0 = Some (Store SZ8 20 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7aba4 : bv 32 := 0x000a3423.
Lemma F_7aba4 : fetch_word AsanUbsan.M.loaded_segments (0x7abf4 : word) = Some W_7aba4.
Proof. vm_refl. Qed.
Lemma D_7aba4 : decode_any W_7aba4 = Some (Store SZ8 20 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_7aba8 : bv 32 := 0x420080ef.
Lemma F_7aba8 : fetch_word AsanUbsan.M.loaded_segments (0x7abf8 : word) = Some W_7aba8.
Proof. vm_refl. Qed.
Lemma D_7aba8 : decode_any W_7aba8 = Some (Jal 1 33824, 4%Z).
Proof. vm_refl. Qed.

Definition W_7abac : bv 32 := 0x00200593.
Lemma F_7abac : fetch_word AsanUbsan.M.loaded_segments (0x7abfc : word) = Some W_7abac.
Proof. vm_refl. Qed.
Lemma D_7abac : decode_any W_7abac = Some (OpImm ALU_ADD 11 0 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_7abb0 : bv 32 := 0x06a5e263.
Lemma F_7abb0 : fetch_word AsanUbsan.M.loaded_segments (0x7ac00 : word) = Some W_7abb0.
Proof. vm_refl. Qed.
Lemma D_7abb0 : decode_any W_7abb0 = Some (Branch BC_LTU 11 10 100, 4%Z).
Proof. vm_refl. Qed.

Definition W_7ac14 : bv 32 := 0x691200ef.
Lemma F_7ac14 : fetch_word AsanUbsan.M.loaded_segments (0x7ac64 : word) = Some W_7ac14.
Proof. vm_refl. Qed.
Lemma D_7ac14 : decode_any W_7ac14 = Some (Jal 1 134800, 4%Z).
Proof. vm_refl. Qed.

Definition W_7ac18 : bv 32 := 0x000c3597.
Lemma F_7ac18 : fetch_word AsanUbsan.M.loaded_segments (0x7ac68 : word) = Some W_7ac18.
Proof. vm_refl. Qed.
Lemma D_7ac18 : decode_any W_7ac18 = Some (Auipc 11 195, 4%Z).
Proof. vm_refl. Qed.

Definition W_7ac1c : bv 32 := 0xc505b583.
Lemma F_7ac1c : fetch_word AsanUbsan.M.loaded_segments (0x7ac6c : word) = Some W_7ac1c.
Proof. vm_refl. Qed.
Lemma D_7ac1c : decode_any W_7ac1c = Some (Load SZ8 true 11 11 3152, 4%Z).
Proof. vm_refl. Qed.

Definition W_7ac20 : bv 32 := 0x0225c983.
Lemma F_7ac20 : fetch_word AsanUbsan.M.loaded_segments (0x7ac70 : word) = Some W_7ac20.
Proof. vm_refl. Qed.
Lemma D_7ac20 : decode_any W_7ac20 = Some (Load SZ1 false 19 11 34, 4%Z).
Proof. vm_refl. Qed.

Definition W_7ac24 : bv 32 := 0x00050913.
Lemma F_7ac24 : fetch_word AsanUbsan.M.loaded_segments (0x7ac74 : word) = Some W_7ac24.
Proof. vm_refl. Qed.
Lemma D_7ac24 : decode_any W_7ac24 = Some (OpImm ALU_ADD 18 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7ac28 : bv 32 := 0x3a0080ef.
Lemma F_7ac28 : fetch_word AsanUbsan.M.loaded_segments (0x7ac78 : word) = Some W_7ac28.
Proof. vm_refl. Qed.
Lemma D_7ac28 : decode_any W_7ac28 = Some (Jal 1 33696, 4%Z).
Proof. vm_refl. Qed.

Definition W_7ac2c : bv 32 := 0x00050793.
Lemma F_7ac2c : fetch_word AsanUbsan.M.loaded_segments (0x7ac7c : word) = Some W_7ac2c.
Proof. vm_refl. Qed.
Lemma D_7ac2c : decode_any W_7ac2c = Some (OpImm ALU_ADD 15 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7ac30 : bv 32 := 0x00153513.
Lemma F_7ac30 : fetch_word AsanUbsan.M.loaded_segments (0x7ac80 : word) = Some W_7ac30.
Proof. vm_refl. Qed.
Lemma D_7ac30 : decode_any W_7ac30 = Some (OpImm ALU_SLTU 10 10 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_7ac34 : bv 32 := 0xfff50513.
Lemma F_7ac34 : fetch_word AsanUbsan.M.loaded_segments (0x7ac84 : word) = Some W_7ac34.
Proof. vm_refl. Qed.
Lemma D_7ac34 : decode_any W_7ac34 = Some (OpImm ALU_ADD 10 10 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_7ac38 : bv 32 := 0x008575b3.
Lemma F_7ac38 : fetch_word AsanUbsan.M.loaded_segments (0x7ac88 : word) = Some W_7ac38.
Proof. vm_refl. Qed.
Lemma D_7ac38 : decode_any W_7ac38 = Some (Op ALU_AND 11 10 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_7ac3c : bv 32 := 0x00100513.
Lemma F_7ac3c : fetch_word AsanUbsan.M.loaded_segments (0x7ac8c : word) = Some W_7ac3c.
Proof. vm_refl. Qed.
Lemma D_7ac3c : decode_any W_7ac3c = Some (OpImm ALU_ADD 10 0 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_7ac40 : bv 32 := 0x00bab4a3.
Lemma F_7ac40 : fetch_word AsanUbsan.M.loaded_segments (0x7ac90 : word) = Some W_7ac40.
Proof. vm_refl. Qed.
Lemma D_7ac40 : decode_any W_7ac40 = Some (Store SZ8 21 11 9, 4%Z).
Proof. vm_refl. Qed.

Definition W_7ac44 : bv 32 := 0x00f56a63.
Lemma F_7ac44 : fetch_word AsanUbsan.M.loaded_segments (0x7ac94 : word) = Some W_7ac44.
Proof. vm_refl. Qed.
Lemma D_7ac44 : decode_any W_7ac44 = Some (Branch BC_LTU 10 15 20, 4%Z).
Proof. vm_refl. Qed.

Definition W_7ac58 : bv 32 := 0x80040513.
Lemma F_7ac58 : fetch_word AsanUbsan.M.loaded_segments (0x7aca8 : word) = Some W_7ac58.
Proof. vm_refl. Qed.
Lemma D_7ac58 : decode_any W_7ac58 = Some (OpImm ALU_ADD 10 8 2048, 4%Z).
Proof. vm_refl. Qed.

Definition W_7ac5c : bv 32 := 0xfb050513.
Lemma F_7ac5c : fetch_word AsanUbsan.M.loaded_segments (0x7acac : word) = Some W_7ac5c.
Proof. vm_refl. Qed.
Lemma D_7ac5c : decode_any W_7ac5c = Some (OpImm ALU_ADD 10 10 4016, 4%Z).
Proof. vm_refl. Qed.

Definition W_7ac60 : bv 32 := 0x00090593.
Lemma F_7ac60 : fetch_word AsanUbsan.M.loaded_segments (0x7acb0 : word) = Some W_7ac60.
Proof. vm_refl. Qed.
Lemma D_7ac60 : decode_any W_7ac60 = Some (OpImm ALU_ADD 11 18 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7ac64 : bv 32 := 0x00040613.
Lemma F_7ac64 : fetch_word AsanUbsan.M.loaded_segments (0x7acb4 : word) = Some W_7ac64.
Proof. vm_refl. Qed.
Lemma D_7ac64 : decode_any W_7ac64 = Some (OpImm ALU_ADD 12 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7ac68 : bv 32 := 0x00000693.
Lemma F_7ac68 : fetch_word AsanUbsan.M.loaded_segments (0x7acb8 : word) = Some W_7ac68.
Proof. vm_refl. Qed.
Lemma D_7ac68 : decode_any W_7ac68 = Some (OpImm ALU_ADD 13 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7ac6c : bv 32 := 0x00098713.
Lemma F_7ac6c : fetch_word AsanUbsan.M.loaded_segments (0x7acbc : word) = Some W_7ac6c.
Proof. vm_refl. Qed.
Lemma D_7ac6c : decode_any W_7ac6c = Some (OpImm ALU_ADD 14 19 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7ac70 : bv 32 := 0x368080ef.
Lemma F_7ac70 : fetch_word AsanUbsan.M.loaded_segments (0x7acc0 : word) = Some W_7ac70.
Proof. vm_refl. Qed.
Lemma D_7ac70 : decode_any W_7ac70 = Some (Jal 1 33640, 4%Z).
Proof. vm_refl. Qed.

Definition W_7ac74 : bv 32 := 0x80040593.
Lemma F_7ac74 : fetch_word AsanUbsan.M.loaded_segments (0x7acc4 : word) = Some W_7ac74.
Proof. vm_refl. Qed.
Lemma D_7ac74 : decode_any W_7ac74 = Some (OpImm ALU_ADD 11 8 2048, 4%Z).
Proof. vm_refl. Qed.

Definition W_7ac78 : bv 32 := 0xfb058593.
Lemma F_7ac78 : fetch_word AsanUbsan.M.loaded_segments (0x7acc8 : word) = Some W_7ac78.
Proof. vm_refl. Qed.
Lemma D_7ac78 : decode_any W_7ac78 = Some (OpImm ALU_ADD 11 11 4016, 4%Z).
Proof. vm_refl. Qed.

Definition W_7ac7c : bv 32 := 0x00048513.
Lemma F_7ac7c : fetch_word AsanUbsan.M.loaded_segments (0x7accc : word) = Some W_7ac7c.
Proof. vm_refl. Qed.
Lemma D_7ac7c : decode_any W_7ac7c = Some (OpImm ALU_ADD 10 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7ac80 : bv 32 := 0x8c9d80ef.
Lemma F_7ac80 : fetch_word AsanUbsan.M.loaded_segments (0x7acd0 : word) = Some W_7ac80.
Proof. vm_refl. Qed.
Lemma D_7ac80 : decode_any W_7ac80 = Some (Jal 1 1935560, 4%Z).
Proof. vm_refl. Qed.

Definition W_7ac84 : bv 32 := 0x06010113.
Lemma F_7ac84 : fetch_word AsanUbsan.M.loaded_segments (0x7acd4 : word) = Some W_7ac84.
Proof. vm_refl. Qed.
Lemma D_7ac84 : decode_any W_7ac84 = Some (OpImm ALU_ADD 2 2 96, 4%Z).
Proof. vm_refl. Qed.

Definition W_7ac88 : bv 32 := 0x7e813083.
Lemma F_7ac88 : fetch_word AsanUbsan.M.loaded_segments (0x7acd8 : word) = Some W_7ac88.
Proof. vm_refl. Qed.
Lemma D_7ac88 : decode_any W_7ac88 = Some (Load SZ8 true 1 2 2024, 4%Z).
Proof. vm_refl. Qed.

Definition W_7ac8c : bv 32 := 0x7e013403.
Lemma F_7ac8c : fetch_word AsanUbsan.M.loaded_segments (0x7acdc : word) = Some W_7ac8c.
Proof. vm_refl. Qed.
Lemma D_7ac8c : decode_any W_7ac8c = Some (Load SZ8 true 8 2 2016, 4%Z).
Proof. vm_refl. Qed.

Definition W_7ac90 : bv 32 := 0x7d813483.
Lemma F_7ac90 : fetch_word AsanUbsan.M.loaded_segments (0x7ace0 : word) = Some W_7ac90.
Proof. vm_refl. Qed.
Lemma D_7ac90 : decode_any W_7ac90 = Some (Load SZ8 true 9 2 2008, 4%Z).
Proof. vm_refl. Qed.

Definition W_7ac94 : bv 32 := 0x7d013903.
Lemma F_7ac94 : fetch_word AsanUbsan.M.loaded_segments (0x7ace4 : word) = Some W_7ac94.
Proof. vm_refl. Qed.
Lemma D_7ac94 : decode_any W_7ac94 = Some (Load SZ8 true 18 2 2000, 4%Z).
Proof. vm_refl. Qed.

Definition W_7ac98 : bv 32 := 0x7c813983.
Lemma F_7ac98 : fetch_word AsanUbsan.M.loaded_segments (0x7ace8 : word) = Some W_7ac98.
Proof. vm_refl. Qed.
Lemma D_7ac98 : decode_any W_7ac98 = Some (Load SZ8 true 19 2 1992, 4%Z).
Proof. vm_refl. Qed.

Definition W_7ac9c : bv 32 := 0x7c013a03.
Lemma F_7ac9c : fetch_word AsanUbsan.M.loaded_segments (0x7acec : word) = Some W_7ac9c.
Proof. vm_refl. Qed.
Lemma D_7ac9c : decode_any W_7ac9c = Some (Load SZ8 true 20 2 1984, 4%Z).
Proof. vm_refl. Qed.

Definition W_7aca0 : bv 32 := 0x7b813a83.
Lemma F_7aca0 : fetch_word AsanUbsan.M.loaded_segments (0x7acf0 : word) = Some W_7aca0.
Proof. vm_refl. Qed.
Lemma D_7aca0 : decode_any W_7aca0 = Some (Load SZ8 true 21 2 1976, 4%Z).
Proof. vm_refl. Qed.

Definition W_7aca4 : bv 32 := 0x7f010113.
Lemma F_7aca4 : fetch_word AsanUbsan.M.loaded_segments (0x7acf4 : word) = Some W_7aca4.
Proof. vm_refl. Qed.
Lemma D_7aca4 : decode_any W_7aca4 = Some (OpImm ALU_ADD 2 2 2032, 4%Z).
Proof. vm_refl. Qed.

Definition W_7aca8 : bv 32 := 0x00008067.
Lemma F_7aca8 : fetch_word AsanUbsan.M.loaded_segments (0x7acf8 : word) = Some W_7aca8.
Proof. vm_refl. Qed.
Lemma D_7aca8 : decode_any W_7aca8 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7b0bc : bv 32 := 0x81010113.
Lemma F_7b0bc : fetch_word AsanUbsan.M.loaded_segments (0x7b10c : word) = Some W_7b0bc.
Proof. vm_refl. Qed.
Lemma D_7b0bc : decode_any W_7b0bc = Some (OpImm ALU_ADD 2 2 2064, 4%Z).
Proof. vm_refl. Qed.

Definition W_7b0c0 : bv 32 := 0x7e113423.
Lemma F_7b0c0 : fetch_word AsanUbsan.M.loaded_segments (0x7b110 : word) = Some W_7b0c0.
Proof. vm_refl. Qed.
Lemma D_7b0c0 : decode_any W_7b0c0 = Some (Store SZ8 2 1 2024, 4%Z).
Proof. vm_refl. Qed.

Definition W_7b0c4 : bv 32 := 0x7e813023.
Lemma F_7b0c4 : fetch_word AsanUbsan.M.loaded_segments (0x7b114 : word) = Some W_7b0c4.
Proof. vm_refl. Qed.
Lemma D_7b0c4 : decode_any W_7b0c4 = Some (Store SZ8 2 8 2016, 4%Z).
Proof. vm_refl. Qed.

Definition W_7b0c8 : bv 32 := 0x7c913c23.
Lemma F_7b0c8 : fetch_word AsanUbsan.M.loaded_segments (0x7b118 : word) = Some W_7b0c8.
Proof. vm_refl. Qed.
Lemma D_7b0c8 : decode_any W_7b0c8 = Some (Store SZ8 2 9 2008, 4%Z).
Proof. vm_refl. Qed.

Definition W_7b0cc : bv 32 := 0x7d213823.
Lemma F_7b0cc : fetch_word AsanUbsan.M.loaded_segments (0x7b11c : word) = Some W_7b0cc.
Proof. vm_refl. Qed.
Lemma D_7b0cc : decode_any W_7b0cc = Some (Store SZ8 2 18 2000, 4%Z).
Proof. vm_refl. Qed.

Definition W_7b0d0 : bv 32 := 0x7d313423.
Lemma F_7b0d0 : fetch_word AsanUbsan.M.loaded_segments (0x7b120 : word) = Some W_7b0d0.
Proof. vm_refl. Qed.
Lemma D_7b0d0 : decode_any W_7b0d0 = Some (Store SZ8 2 19 1992, 4%Z).
Proof. vm_refl. Qed.

Definition W_7b0d4 : bv 32 := 0x7d413023.
Lemma F_7b0d4 : fetch_word AsanUbsan.M.loaded_segments (0x7b124 : word) = Some W_7b0d4.
Proof. vm_refl. Qed.
Lemma D_7b0d4 : decode_any W_7b0d4 = Some (Store SZ8 2 20 1984, 4%Z).
Proof. vm_refl. Qed.

Definition W_7b0d8 : bv 32 := 0x7b513c23.
Lemma F_7b0d8 : fetch_word AsanUbsan.M.loaded_segments (0x7b128 : word) = Some W_7b0d8.
Proof. vm_refl. Qed.
Lemma D_7b0d8 : decode_any W_7b0d8 = Some (Store SZ8 2 21 1976, 4%Z).
Proof. vm_refl. Qed.

Definition W_7b0dc : bv 32 := 0x7b613823.
Lemma F_7b0dc : fetch_word AsanUbsan.M.loaded_segments (0x7b12c : word) = Some W_7b0dc.
Proof. vm_refl. Qed.
Lemma D_7b0dc : decode_any W_7b0dc = Some (Store SZ8 2 22 1968, 4%Z).
Proof. vm_refl. Qed.

Definition W_7b0e0 : bv 32 := 0x7f010413.
Lemma F_7b0e0 : fetch_word AsanUbsan.M.loaded_segments (0x7b130 : word) = Some W_7b0e0.
Proof. vm_refl. Qed.
Lemma D_7b0e0 : decode_any W_7b0e0 = Some (OpImm ALU_ADD 8 2 2032, 4%Z).
Proof. vm_refl. Qed.

Definition W_7b0e4 : bv 32 := 0xf9010113.
Lemma F_7b0e4 : fetch_word AsanUbsan.M.loaded_segments (0x7b134 : word) = Some W_7b0e4.
Proof. vm_refl. Qed.
Lemma D_7b0e4 : decode_any W_7b0e4 = Some (OpImm ALU_ADD 2 2 3984, 4%Z).
Proof. vm_refl. Qed.

Definition W_7b0e8 : bv 32 := 0x00008993.
Lemma F_7b0e8 : fetch_word AsanUbsan.M.loaded_segments (0x7b138 : word) = Some W_7b0e8.
Proof. vm_refl. Qed.
Lemma D_7b0e8 : decode_any W_7b0e8 = Some (OpImm ALU_ADD 19 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7b0ec : bv 32 := 0x00058493.
Lemma F_7b0ec : fetch_word AsanUbsan.M.loaded_segments (0x7b13c : word) = Some W_7b0ec.
Proof. vm_refl. Qed.
Lemma D_7b0ec : decode_any W_7b0ec = Some (OpImm ALU_ADD 9 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7b0f0 : bv 32 := 0x00050913.
Lemma F_7b0f0 : fetch_word AsanUbsan.M.loaded_segments (0x7b140 : word) = Some W_7b0f0.
Proof. vm_refl. Qed.
Lemma D_7b0f0 : decode_any W_7b0f0 = Some (OpImm ALU_ADD 18 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7b0f4 : bv 32 := 0x80040a93.
Lemma F_7b0f4 : fetch_word AsanUbsan.M.loaded_segments (0x7b144 : word) = Some W_7b0f4.
Proof. vm_refl. Qed.
Lemma D_7b0f4 : decode_any W_7b0f4 = Some (OpImm ALU_ADD 21 8 2048, 4%Z).
Proof. vm_refl. Qed.

Definition W_7b0f8 : bv 32 := 0xfa8a8a93.
Lemma F_7b0f8 : fetch_word AsanUbsan.M.loaded_segments (0x7b148 : word) = Some W_7b0f8.
Proof. vm_refl. Qed.
Lemma D_7b0f8 : decode_any W_7b0f8 = Some (OpImm ALU_ADD 21 21 4008, 4%Z).
Proof. vm_refl. Qed.

Definition W_7b0fc : bv 32 := 0x80040513.
Lemma F_7b0fc : fetch_word AsanUbsan.M.loaded_segments (0x7b14c : word) = Some W_7b0fc.
Proof. vm_refl. Qed.
Lemma D_7b0fc : decode_any W_7b0fc = Some (OpImm ALU_ADD 10 8 2048, 4%Z).
Proof. vm_refl. Qed.

Definition W_7b100 : bv 32 := 0xfb850513.
Lemma F_7b100 : fetch_word AsanUbsan.M.loaded_segments (0x7b150 : word) = Some W_7b100.
Proof. vm_refl. Qed.
Lemma D_7b100 : decode_any W_7b100 = Some (OpImm ALU_ADD 10 10 4024, 4%Z).
Proof. vm_refl. Qed.

Definition W_7b104 : bv 32 := 0x7ffa8b13.
Lemma F_7b104 : fetch_word AsanUbsan.M.loaded_segments (0x7b154 : word) = Some W_7b104.
Proof. vm_refl. Qed.
Lemma D_7b104 : decode_any W_7b104 = Some (OpImm ALU_ADD 22 21 2047, 4%Z).
Proof. vm_refl. Qed.

Definition W_7b108 : bv 32 := 0x000b34a3.
Lemma F_7b108 : fetch_word AsanUbsan.M.loaded_segments (0x7b158 : word) = Some W_7b108.
Proof. vm_refl. Qed.
Lemma D_7b108 : decode_any W_7b108 = Some (Store SZ8 22 0 9, 4%Z).
Proof. vm_refl. Qed.

Definition W_7b10c : bv 32 := 0x00aab023.
Lemma F_7b10c : fetch_word AsanUbsan.M.loaded_segments (0x7b15c : word) = Some W_7b10c.
Proof. vm_refl. Qed.
Lemma D_7b10c : decode_any W_7b10c = Some (Store SZ8 21 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7b110 : bv 32 := 0x000ab423.
Lemma F_7b110 : fetch_word AsanUbsan.M.loaded_segments (0x7b160 : word) = Some W_7b110.
Proof. vm_refl. Qed.
Lemma D_7b110 : decode_any W_7b110 = Some (Store SZ8 21 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_7b114 : bv 32 := 0x6b5070ef.
Lemma F_7b114 : fetch_word AsanUbsan.M.loaded_segments (0x7b164 : word) = Some W_7b114.
Proof. vm_refl. Qed.
Lemma D_7b114 : decode_any W_7b114 = Some (Jal 1 32436, 4%Z).
Proof. vm_refl. Qed.

Definition W_7b118 : bv 32 := 0x00200593.
Lemma F_7b118 : fetch_word AsanUbsan.M.loaded_segments (0x7b168 : word) = Some W_7b118.
Proof. vm_refl. Qed.
Lemma D_7b118 : decode_any W_7b118 = Some (OpImm ALU_ADD 11 0 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_7b11c : bv 32 := 0x02a5ea63.
Lemma F_7b11c : fetch_word AsanUbsan.M.loaded_segments (0x7b16c : word) = Some W_7b11c.
Proof. vm_refl. Qed.
Lemma D_7b11c : decode_any W_7b11c = Some (Branch BC_LTU 11 10 52, 4%Z).
Proof. vm_refl. Qed.

Definition W_7b150 : bv 32 := 0x155200ef.
Lemma F_7b150 : fetch_word AsanUbsan.M.loaded_segments (0x7b1a0 : word) = Some W_7b150.
Proof. vm_refl. Qed.
Lemma D_7b150 : decode_any W_7b150 = Some (Jal 1 133460, 4%Z).
Proof. vm_refl. Qed.

Definition W_7b154 : bv 32 := 0x000c2597.
Lemma F_7b154 : fetch_word AsanUbsan.M.loaded_segments (0x7b1a4 : word) = Some W_7b154.
Proof. vm_refl. Qed.
Lemma D_7b154 : decode_any W_7b154 = Some (Auipc 11 194, 4%Z).
Proof. vm_refl. Qed.

Definition W_7b158 : bv 32 := 0x7145b583.
Lemma F_7b158 : fetch_word AsanUbsan.M.loaded_segments (0x7b1a8 : word) = Some W_7b158.
Proof. vm_refl. Qed.
Lemma D_7b158 : decode_any W_7b158 = Some (Load SZ8 true 11 11 1812, 4%Z).
Proof. vm_refl. Qed.

Definition W_7b15c : bv 32 := 0x0225ca03.
Lemma F_7b15c : fetch_word AsanUbsan.M.loaded_segments (0x7b1ac : word) = Some W_7b15c.
Proof. vm_refl. Qed.
Lemma D_7b15c : decode_any W_7b15c = Some (Load SZ1 false 20 11 34, 4%Z).
Proof. vm_refl. Qed.

Definition W_7b160 : bv 32 := 0x00050993.
Lemma F_7b160 : fetch_word AsanUbsan.M.loaded_segments (0x7b1b0 : word) = Some W_7b160.
Proof. vm_refl. Qed.
Lemma D_7b160 : decode_any W_7b160 = Some (OpImm ALU_ADD 19 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7b164 : bv 32 := 0x665070ef.
Lemma F_7b164 : fetch_word AsanUbsan.M.loaded_segments (0x7b1b4 : word) = Some W_7b164.
Proof. vm_refl. Qed.
Lemma D_7b164 : decode_any W_7b164 = Some (Jal 1 32356, 4%Z).
Proof. vm_refl. Qed.

Definition W_7b168 : bv 32 := 0x00050793.
Lemma F_7b168 : fetch_word AsanUbsan.M.loaded_segments (0x7b1b8 : word) = Some W_7b168.
Proof. vm_refl. Qed.
Lemma D_7b168 : decode_any W_7b168 = Some (OpImm ALU_ADD 15 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7b16c : bv 32 := 0x00153513.
Lemma F_7b16c : fetch_word AsanUbsan.M.loaded_segments (0x7b1bc : word) = Some W_7b16c.
Proof. vm_refl. Qed.
Lemma D_7b16c : decode_any W_7b16c = Some (OpImm ALU_SLTU 10 10 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_7b170 : bv 32 := 0xfff50513.
Lemma F_7b170 : fetch_word AsanUbsan.M.loaded_segments (0x7b1c0 : word) = Some W_7b170.
Proof. vm_refl. Qed.
Lemma D_7b170 : decode_any W_7b170 = Some (OpImm ALU_ADD 10 10 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_7b174 : bv 32 := 0x008575b3.
Lemma F_7b174 : fetch_word AsanUbsan.M.loaded_segments (0x7b1c4 : word) = Some W_7b174.
Proof. vm_refl. Qed.
Lemma D_7b174 : decode_any W_7b174 = Some (Op ALU_AND 11 10 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_7b178 : bv 32 := 0x00100513.
Lemma F_7b178 : fetch_word AsanUbsan.M.loaded_segments (0x7b1c8 : word) = Some W_7b178.
Proof. vm_refl. Qed.
Lemma D_7b178 : decode_any W_7b178 = Some (OpImm ALU_ADD 10 0 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_7b17c : bv 32 := 0x00bb34a3.
Lemma F_7b17c : fetch_word AsanUbsan.M.loaded_segments (0x7b1cc : word) = Some W_7b17c.
Proof. vm_refl. Qed.
Lemma D_7b17c : decode_any W_7b17c = Some (Store SZ8 22 11 9, 4%Z).
Proof. vm_refl. Qed.

Definition W_7b180 : bv 32 := 0x00f56a63.
Lemma F_7b180 : fetch_word AsanUbsan.M.loaded_segments (0x7b1d0 : word) = Some W_7b180.
Proof. vm_refl. Qed.
Lemma D_7b180 : decode_any W_7b180 = Some (Branch BC_LTU 10 15 20, 4%Z).
Proof. vm_refl. Qed.

Definition W_7b194 : bv 32 := 0x80040513.
Lemma F_7b194 : fetch_word AsanUbsan.M.loaded_segments (0x7b1e4 : word) = Some W_7b194.
Proof. vm_refl. Qed.
Lemma D_7b194 : decode_any W_7b194 = Some (OpImm ALU_ADD 10 8 2048, 4%Z).
Proof. vm_refl. Qed.

Definition W_7b198 : bv 32 := 0xfa850513.
Lemma F_7b198 : fetch_word AsanUbsan.M.loaded_segments (0x7b1e8 : word) = Some W_7b198.
Proof. vm_refl. Qed.
Lemma D_7b198 : decode_any W_7b198 = Some (OpImm ALU_ADD 10 10 4008, 4%Z).
Proof. vm_refl. Qed.

Definition W_7b19c : bv 32 := 0x00098593.
Lemma F_7b19c : fetch_word AsanUbsan.M.loaded_segments (0x7b1ec : word) = Some W_7b19c.
Proof. vm_refl. Qed.
Lemma D_7b19c : decode_any W_7b19c = Some (OpImm ALU_ADD 11 19 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7b1a0 : bv 32 := 0x00040613.
Lemma F_7b1a0 : fetch_word AsanUbsan.M.loaded_segments (0x7b1f0 : word) = Some W_7b1a0.
Proof. vm_refl. Qed.
Lemma D_7b1a0 : decode_any W_7b1a0 = Some (OpImm ALU_ADD 12 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7b1a4 : bv 32 := 0x00000693.
Lemma F_7b1a4 : fetch_word AsanUbsan.M.loaded_segments (0x7b1f4 : word) = Some W_7b1a4.
Proof. vm_refl. Qed.
Lemma D_7b1a4 : decode_any W_7b1a4 = Some (OpImm ALU_ADD 13 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7b1a8 : bv 32 := 0x000a0713.
Lemma F_7b1a8 : fetch_word AsanUbsan.M.loaded_segments (0x7b1f8 : word) = Some W_7b1a8.
Proof. vm_refl. Qed.
Lemma D_7b1a8 : decode_any W_7b1a8 = Some (OpImm ALU_ADD 14 20 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7b1ac : bv 32 := 0x62d070ef.
Lemma F_7b1ac : fetch_word AsanUbsan.M.loaded_segments (0x7b1fc : word) = Some W_7b1ac.
Proof. vm_refl. Qed.
Lemma D_7b1ac : decode_any W_7b1ac = Some (Jal 1 32300, 4%Z).
Proof. vm_refl. Qed.

Definition W_7b1b0 : bv 32 := 0x80040613.
Lemma F_7b1b0 : fetch_word AsanUbsan.M.loaded_segments (0x7b200 : word) = Some W_7b1b0.
Proof. vm_refl. Qed.
Lemma D_7b1b0 : decode_any W_7b1b0 = Some (OpImm ALU_ADD 12 8 2048, 4%Z).
Proof. vm_refl. Qed.

Definition W_7b1b4 : bv 32 := 0xfa860613.
Lemma F_7b1b4 : fetch_word AsanUbsan.M.loaded_segments (0x7b204 : word) = Some W_7b1b4.
Proof. vm_refl. Qed.
Lemma D_7b1b4 : decode_any W_7b1b4 = Some (OpImm ALU_ADD 12 12 4008, 4%Z).
Proof. vm_refl. Qed.

Definition W_7b1b8 : bv 32 := 0x00090513.
Lemma F_7b1b8 : fetch_word AsanUbsan.M.loaded_segments (0x7b208 : word) = Some W_7b1b8.
Proof. vm_refl. Qed.
Lemma D_7b1b8 : decode_any W_7b1b8 = Some (OpImm ALU_ADD 10 18 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7b1bc : bv 32 := 0x00048593.
Lemma F_7b1bc : fetch_word AsanUbsan.M.loaded_segments (0x7b20c : word) = Some W_7b1bc.
Proof. vm_refl. Qed.
Lemma D_7b1bc : decode_any W_7b1bc = Some (OpImm ALU_ADD 11 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7b1c0 : bv 32 := 0xf79d80ef.
Lemma F_7b1c0 : fetch_word AsanUbsan.M.loaded_segments (0x7b210 : word) = Some W_7b1c0.
Proof. vm_refl. Qed.
Lemma D_7b1c0 : decode_any W_7b1c0 = Some (Jal 1 1937272, 4%Z).
Proof. vm_refl. Qed.

Definition W_7b1c4 : bv 32 := 0x07010113.
Lemma F_7b1c4 : fetch_word AsanUbsan.M.loaded_segments (0x7b214 : word) = Some W_7b1c4.
Proof. vm_refl. Qed.
Lemma D_7b1c4 : decode_any W_7b1c4 = Some (OpImm ALU_ADD 2 2 112, 4%Z).
Proof. vm_refl. Qed.

Definition W_7b1c8 : bv 32 := 0x7e813083.
Lemma F_7b1c8 : fetch_word AsanUbsan.M.loaded_segments (0x7b218 : word) = Some W_7b1c8.
Proof. vm_refl. Qed.
Lemma D_7b1c8 : decode_any W_7b1c8 = Some (Load SZ8 true 1 2 2024, 4%Z).
Proof. vm_refl. Qed.

Definition W_7b1cc : bv 32 := 0x7e013403.
Lemma F_7b1cc : fetch_word AsanUbsan.M.loaded_segments (0x7b21c : word) = Some W_7b1cc.
Proof. vm_refl. Qed.
Lemma D_7b1cc : decode_any W_7b1cc = Some (Load SZ8 true 8 2 2016, 4%Z).
Proof. vm_refl. Qed.

Definition W_7b1d0 : bv 32 := 0x7d813483.
Lemma F_7b1d0 : fetch_word AsanUbsan.M.loaded_segments (0x7b220 : word) = Some W_7b1d0.
Proof. vm_refl. Qed.
Lemma D_7b1d0 : decode_any W_7b1d0 = Some (Load SZ8 true 9 2 2008, 4%Z).
Proof. vm_refl. Qed.

Definition W_7b1d4 : bv 32 := 0x7d013903.
Lemma F_7b1d4 : fetch_word AsanUbsan.M.loaded_segments (0x7b224 : word) = Some W_7b1d4.
Proof. vm_refl. Qed.
Lemma D_7b1d4 : decode_any W_7b1d4 = Some (Load SZ8 true 18 2 2000, 4%Z).
Proof. vm_refl. Qed.

Definition W_7b1d8 : bv 32 := 0x7c813983.
Lemma F_7b1d8 : fetch_word AsanUbsan.M.loaded_segments (0x7b228 : word) = Some W_7b1d8.
Proof. vm_refl. Qed.
Lemma D_7b1d8 : decode_any W_7b1d8 = Some (Load SZ8 true 19 2 1992, 4%Z).
Proof. vm_refl. Qed.

Definition W_7b1dc : bv 32 := 0x7c013a03.
Lemma F_7b1dc : fetch_word AsanUbsan.M.loaded_segments (0x7b22c : word) = Some W_7b1dc.
Proof. vm_refl. Qed.
Lemma D_7b1dc : decode_any W_7b1dc = Some (Load SZ8 true 20 2 1984, 4%Z).
Proof. vm_refl. Qed.

Definition W_7b1e0 : bv 32 := 0x7b813a83.
Lemma F_7b1e0 : fetch_word AsanUbsan.M.loaded_segments (0x7b230 : word) = Some W_7b1e0.
Proof. vm_refl. Qed.
Lemma D_7b1e0 : decode_any W_7b1e0 = Some (Load SZ8 true 21 2 1976, 4%Z).
Proof. vm_refl. Qed.

Definition W_7b1e4 : bv 32 := 0x7b013b03.
Lemma F_7b1e4 : fetch_word AsanUbsan.M.loaded_segments (0x7b234 : word) = Some W_7b1e4.
Proof. vm_refl. Qed.
Lemma D_7b1e4 : decode_any W_7b1e4 = Some (Load SZ8 true 22 2 1968, 4%Z).
Proof. vm_refl. Qed.

Definition W_7b1e8 : bv 32 := 0x7f010113.
Lemma F_7b1e8 : fetch_word AsanUbsan.M.loaded_segments (0x7b238 : word) = Some W_7b1e8.
Proof. vm_refl. Qed.
Lemma D_7b1e8 : decode_any W_7b1e8 = Some (OpImm ALU_ADD 2 2 2032, 4%Z).
Proof. vm_refl. Qed.

Definition W_7b1ec : bv 32 := 0x00008067.
Lemma F_7b1ec : fetch_word AsanUbsan.M.loaded_segments (0x7b23c : word) = Some W_7b1ec.
Proof. vm_refl. Qed.
Lemma D_7b1ec : decode_any W_7b1ec = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.
