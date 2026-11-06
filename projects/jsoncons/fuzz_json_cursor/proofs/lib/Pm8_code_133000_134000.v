(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.jsoncons.fuzz_json_cursor.images Require Import Asan.
Open Scope bv_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Hint Extern 0 (BvWf _ _) =>
  (lazymatch goal with |- BvWf ?n ?v => is_closed_term n; is_closed_term v end; exact I) : typeclass_instances.
Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

Definition W_13337c : bv 32 := 0x0004b503.
Lemma F_13337c : fetch_word Asan.M.loaded_segments (0x1333cc : word) = Some W_13337c.
Proof. vm_refl. Qed.
Lemma D_13337c : decode_any W_13337c = Some (Load SZ8 true 10 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_133380 : bv 32 := 0x00848493.
Lemma F_133380 : fetch_word Asan.M.loaded_segments (0x1333d0 : word) = Some W_133380.
Proof. vm_refl. Qed.
Lemma D_133380 : decode_any W_133380 = Some (OpImm ALU_ADD 9 9 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_133384 : bv 32 := 0xfe051ce3.
Lemma F_133384 : fetch_word Asan.M.loaded_segments (0x1333d4 : word) = Some W_133384.
Proof. vm_refl. Qed.
Lemma D_133384 : decode_any W_133384 = Some (Branch BC_NE 10 0 8184, 4%Z).
Proof. vm_refl. Qed.

Definition W_133438 : bv 32 := 0x00b53023.
Lemma F_133438 : fetch_word Asan.M.loaded_segments (0x133488 : word) = Some W_133438.
Proof. vm_refl. Qed.
Lemma D_133438 : decode_any W_133438 = Some (Store SZ8 10 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_13343c : bv 32 := 0x00158593.
Lemma F_13343c : fetch_word Asan.M.loaded_segments (0x13348c : word) = Some W_13343c.
Proof. vm_refl. Qed.
Lemma D_13343c : decode_any W_13343c = Some (OpImm ALU_ADD 11 11 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_133440 : bv 32 := 0xfff5c683.
Lemma F_133440 : fetch_word Asan.M.loaded_segments (0x133490 : word) = Some W_133440.
Proof. vm_refl. Qed.
Lemma D_133440 : decode_any W_133440 = Some (Load SZ1 false 13 11 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_133444 : bv 32 := 0xfec68ae3.
Lemma F_133444 : fetch_word Asan.M.loaded_segments (0x133494 : word) = Some W_133444.
Proof. vm_refl. Qed.
Lemma D_133444 : decode_any W_133444 = Some (Branch BC_EQ 13 12 8180, 4%Z).
Proof. vm_refl. Qed.

Definition W_133448 : bv 32 := 0xfe069ae3.
Lemma F_133448 : fetch_word Asan.M.loaded_segments (0x133498 : word) = Some W_133448.
Proof. vm_refl. Qed.
Lemma D_133448 : decode_any W_133448 = Some (Branch BC_NE 13 0 8180, 4%Z).
Proof. vm_refl. Qed.

Definition W_133a60 : bv 32 := 0x00020513.
Lemma F_133a60 : fetch_word Asan.M.loaded_segments (0x133aa4 : word) = Some W_133a60.
Proof. vm_refl. Qed.
Lemma D_133a60 : decode_any W_133a60 = Some (OpImm ALU_ADD 10 4 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_133a64 : bv 32 := 0xf5c50513.
Lemma F_133a64 : fetch_word Asan.M.loaded_segments (0x133aa8 : word) = Some W_133a64.
Proof. vm_refl. Qed.
Lemma D_133a64 : decode_any W_133a64 = Some (OpImm ALU_ADD 10 10 3932, 4%Z).
Proof. vm_refl. Qed.

Definition W_133a68 : bv 32 := 0x00008067.
Lemma F_133a68 : fetch_word Asan.M.loaded_segments (0x133aac : word) = Some W_133a68.
Proof. vm_refl. Qed.
Lemma D_133a68 : decode_any W_133a68 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_133c54 : bv 32 := 0xfd010113.
Lemma F_133c54 : fetch_word Asan.M.loaded_segments (0x133c98 : word) = Some W_133c54.
Proof. vm_refl. Qed.
Lemma D_133c54 : decode_any W_133c54 = Some (OpImm ALU_ADD 2 2 4048, 4%Z).
Proof. vm_refl. Qed.

Definition W_133c58 : bv 32 := 0x02113423.
Lemma F_133c58 : fetch_word Asan.M.loaded_segments (0x133c9c : word) = Some W_133c58.
Proof. vm_refl. Qed.
Lemma D_133c58 : decode_any W_133c58 = Some (Store SZ8 2 1 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_133c5c : bv 32 := 0x02813023.
Lemma F_133c5c : fetch_word Asan.M.loaded_segments (0x133ca0 : word) = Some W_133c5c.
Proof. vm_refl. Qed.
Lemma D_133c5c : decode_any W_133c5c = Some (Store SZ8 2 8 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_133c60 : bv 32 := 0x00913c23.
Lemma F_133c60 : fetch_word Asan.M.loaded_segments (0x133ca4 : word) = Some W_133c60.
Proof. vm_refl. Qed.
Lemma D_133c60 : decode_any W_133c60 = Some (Store SZ8 2 9 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_133c64 : bv 32 := 0x01213823.
Lemma F_133c64 : fetch_word Asan.M.loaded_segments (0x133ca8 : word) = Some W_133c64.
Proof. vm_refl. Qed.
Lemma D_133c64 : decode_any W_133c64 = Some (Store SZ8 2 18 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_133c68 : bv 32 := 0x01313423.
Lemma F_133c68 : fetch_word Asan.M.loaded_segments (0x133cac : word) = Some W_133c68.
Proof. vm_refl. Qed.
Lemma D_133c68 : decode_any W_133c68 = Some (Store SZ8 2 19 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_133c6c : bv 32 := 0x01413023.
Lemma F_133c6c : fetch_word Asan.M.loaded_segments (0x133cb0 : word) = Some W_133c6c.
Proof. vm_refl. Qed.
Lemma D_133c6c : decode_any W_133c6c = Some (Store SZ8 2 20 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_133c70 : bv 32 := 0x00058493.
Lemma F_133c70 : fetch_word Asan.M.loaded_segments (0x133cb4 : word) = Some W_133c70.
Proof. vm_refl. Qed.
Lemma D_133c70 : decode_any W_133c70 = Some (OpImm ALU_ADD 9 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_133c74 : bv 32 := 0x00050913.
Lemma F_133c74 : fetch_word Asan.M.loaded_segments (0x133cb8 : word) = Some W_133c74.
Proof. vm_refl. Qed.
Lemma D_133c74 : decode_any W_133c74 = Some (OpImm ALU_ADD 18 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_133c78 : bv 32 := 0x0057d517.
Lemma F_133c78 : fetch_word Asan.M.loaded_segments (0x133cbc : word) = Some W_133c78.
Proof. vm_refl. Qed.
Lemma D_133c78 : decode_any W_133c78 = Some (Auipc 10 1405, 4%Z).
Proof. vm_refl. Qed.

Definition W_133c7c : bv 32 := 0xde450a13.
Lemma F_133c7c : fetch_word Asan.M.loaded_segments (0x133cc0 : word) = Some W_133c7c.
Proof. vm_refl. Qed.
Lemma D_133c7c : decode_any W_133c7c = Some (OpImm ALU_ADD 20 10 3556, 4%Z).
Proof. vm_refl. Qed.

Definition W_133c80 : bv 32 := 0x004a0413.
Lemma F_133c80 : fetch_word Asan.M.loaded_segments (0x133cc4 : word) = Some W_133c80.
Proof. vm_refl. Qed.
Lemma D_133c80 : decode_any W_133c80 = Some (OpImm ALU_ADD 8 20 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_133c84 : bv 32 := 0x00040513.
Lemma F_133c84 : fetch_word Asan.M.loaded_segments (0x133cc8 : word) = Some W_133c84.
Proof. vm_refl. Qed.
Lemma D_133c84 : decode_any W_133c84 = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_133c88 : bv 32 := 0x6f9110ef.
Lemma F_133c88 : fetch_word Asan.M.loaded_segments (0x133ccc : word) = Some W_133c88.
Proof. vm_refl. Qed.
Lemma D_133c88 : decode_any W_133c88 = Some (Jal 1 73464, 4%Z).
Proof. vm_refl. Qed.

Definition W_133c8c : bv 32 := 0x000a4503.
Lemma F_133c8c : fetch_word Asan.M.loaded_segments (0x133cd0 : word) = Some W_133c8c.
Proof. vm_refl. Qed.
Lemma D_133c8c : decode_any W_133c8c = Some (Load SZ1 false 10 20 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_133c90 : bv 32 := 0xfff00993.
Lemma F_133c90 : fetch_word Asan.M.loaded_segments (0x133cd4 : word) = Some W_133c90.
Proof. vm_refl. Qed.
Lemma D_133c90 : decode_any W_133c90 = Some (OpImm ALU_ADD 19 0 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_133c94 : bv 32 := 0x04051e63.
Lemma F_133c94 : fetch_word Asan.M.loaded_segments (0x133cd8 : word) = Some W_133c94.
Proof. vm_refl. Qed.
Lemma D_133c94 : decode_any W_133c94 = Some (Branch BC_NE 10 0 92, 4%Z).
Proof. vm_refl. Qed.

Definition W_133c98 : bv 32 := 0x010a3503.
Lemma F_133c98 : fetch_word Asan.M.loaded_segments (0x133cdc : word) = Some W_133c98.
Proof. vm_refl. Qed.
Lemma D_133c98 : decode_any W_133c98 = Some (Load SZ8 true 10 20 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_133c9c : bv 32 := 0x00051663.
Lemma F_133c9c : fetch_word Asan.M.loaded_segments (0x133ce0 : word) = Some W_133c9c.
Proof. vm_refl. Qed.
Lemma D_133c9c : decode_any W_133c9c = Some (Branch BC_NE 10 0 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_133ca8 : bv 32 := 0x008a2583.
Lemma F_133ca8 : fetch_word Asan.M.loaded_segments (0x133cec : word) = Some W_133ca8.
Proof. vm_refl. Qed.
Lemma D_133ca8 : decode_any W_133ca8 = Some (Load SZ4 true 11 20 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_133cac : bv 32 := 0x02000613.
Lemma F_133cac : fetch_word Asan.M.loaded_segments (0x133cf0 : word) = Some W_133cac.
Proof. vm_refl. Qed.
Lemma D_133cac : decode_any W_133cac = Some (OpImm ALU_ADD 12 0 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_133cb0 : bv 32 := 0x02c59263.
Lemma F_133cb0 : fetch_word Asan.M.loaded_segments (0x133cf4 : word) = Some W_133cb0.
Proof. vm_refl. Qed.
Lemma D_133cb0 : decode_any W_133cb0 = Some (Branch BC_NE 11 12 36, 4%Z).
Proof. vm_refl. Qed.

Definition W_133cd4 : bv 32 := 0x00000993.
Lemma F_133cd4 : fetch_word Asan.M.loaded_segments (0x133d18 : word) = Some W_133cd4.
Proof. vm_refl. Qed.
Lemma D_133cd4 : decode_any W_133cd4 = Some (OpImm ALU_ADD 19 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_133cd8 : bv 32 := 0x00359613.
Lemma F_133cd8 : fetch_word Asan.M.loaded_segments (0x133d1c : word) = Some W_133cd8.
Proof. vm_refl. Qed.
Lemma D_133cd8 : decode_any W_133cd8 = Some (ShiftImm ALU_SLL 12 11 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_133cdc : bv 32 := 0x00c50533.
Lemma F_133cdc : fetch_word Asan.M.loaded_segments (0x133d20 : word) = Some W_133cdc.
Proof. vm_refl. Qed.
Lemma D_133cdc : decode_any W_133cdc = Some (Op ALU_ADD 10 10 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_133ce0 : bv 32 := 0x00158593.
Lemma F_133ce0 : fetch_word Asan.M.loaded_segments (0x133d24 : word) = Some W_133ce0.
Proof. vm_refl. Qed.
Lemma D_133ce0 : decode_any W_133ce0 = Some (OpImm ALU_ADD 11 11 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_133ce4 : bv 32 := 0x01253423.
Lemma F_133ce4 : fetch_word Asan.M.loaded_segments (0x133d28 : word) = Some W_133ce4.
Proof. vm_refl. Qed.
Lemma D_133ce4 : decode_any W_133ce4 = Some (Store SZ8 10 18 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_133ce8 : bv 32 := 0x10953423.
Lemma F_133ce8 : fetch_word Asan.M.loaded_segments (0x133d2c : word) = Some W_133ce8.
Proof. vm_refl. Qed.
Lemma D_133ce8 : decode_any W_133ce8 = Some (Store SZ8 10 9 264, 4%Z).
Proof. vm_refl. Qed.

Definition W_133cec : bv 32 := 0x00ba2423.
Lemma F_133cec : fetch_word Asan.M.loaded_segments (0x133d30 : word) = Some W_133cec.
Proof. vm_refl. Qed.
Lemma D_133cec : decode_any W_133cec = Some (Store SZ4 20 11 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_133cf0 : bv 32 := 0x00040513.
Lemma F_133cf0 : fetch_word Asan.M.loaded_segments (0x133d34 : word) = Some W_133cf0.
Proof. vm_refl. Qed.
Lemma D_133cf0 : decode_any W_133cf0 = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_133cf4 : bv 32 := 0x114120ef.
Lemma F_133cf4 : fetch_word Asan.M.loaded_segments (0x133d38 : word) = Some W_133cf4.
Proof. vm_refl. Qed.
Lemma D_133cf4 : decode_any W_133cf4 = Some (Jal 1 74004, 4%Z).
Proof. vm_refl. Qed.

Definition W_133cf8 : bv 32 := 0x00098513.
Lemma F_133cf8 : fetch_word Asan.M.loaded_segments (0x133d3c : word) = Some W_133cf8.
Proof. vm_refl. Qed.
Lemma D_133cf8 : decode_any W_133cf8 = Some (OpImm ALU_ADD 10 19 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_133cfc : bv 32 := 0x02813083.
Lemma F_133cfc : fetch_word Asan.M.loaded_segments (0x133d40 : word) = Some W_133cfc.
Proof. vm_refl. Qed.
Lemma D_133cfc : decode_any W_133cfc = Some (Load SZ8 true 1 2 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_133d00 : bv 32 := 0x02013403.
Lemma F_133d00 : fetch_word Asan.M.loaded_segments (0x133d44 : word) = Some W_133d00.
Proof. vm_refl. Qed.
Lemma D_133d00 : decode_any W_133d00 = Some (Load SZ8 true 8 2 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_133d04 : bv 32 := 0x01813483.
Lemma F_133d04 : fetch_word Asan.M.loaded_segments (0x133d48 : word) = Some W_133d04.
Proof. vm_refl. Qed.
Lemma D_133d04 : decode_any W_133d04 = Some (Load SZ8 true 9 2 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_133d08 : bv 32 := 0x01013903.
Lemma F_133d08 : fetch_word Asan.M.loaded_segments (0x133d4c : word) = Some W_133d08.
Proof. vm_refl. Qed.
Lemma D_133d08 : decode_any W_133d08 = Some (Load SZ8 true 18 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_133d0c : bv 32 := 0x00813983.
Lemma F_133d0c : fetch_word Asan.M.loaded_segments (0x133d50 : word) = Some W_133d0c.
Proof. vm_refl. Qed.
Lemma D_133d0c : decode_any W_133d0c = Some (Load SZ8 true 19 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_133d10 : bv 32 := 0x00013a03.
Lemma F_133d10 : fetch_word Asan.M.loaded_segments (0x133d54 : word) = Some W_133d10.
Proof. vm_refl. Qed.
Lemma D_133d10 : decode_any W_133d10 = Some (Load SZ8 true 20 2 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_133d14 : bv 32 := 0x03010113.
Lemma F_133d14 : fetch_word Asan.M.loaded_segments (0x133d58 : word) = Some W_133d14.
Proof. vm_refl. Qed.
Lemma D_133d14 : decode_any W_133d14 = Some (OpImm ALU_ADD 2 2 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_133d18 : bv 32 := 0x00008067.
Lemma F_133d18 : fetch_word Asan.M.loaded_segments (0x133d5c : word) = Some W_133d18.
Proof. vm_refl. Qed.
Lemma D_133d18 : decode_any W_133d18 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

