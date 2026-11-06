(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
(* [comment removed for export] *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require BvWfKernel.

From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.jsoncons.fuzz_ubjson_encoder.images Require Import Asan.
Open Scope bv_scope.

Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

Definition W_5ea10 : bv 32 := 0xfe010113.
Lemma F_5ea10 : fetch_word Asan.M.loaded_segments (0x5ea60 : word) = Some W_5ea10.
Proof. vm_refl. Qed.
Lemma D_5ea10 : decode_any W_5ea10 = Some (OpImm ALU_ADD 2 2 4064, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ea14 : bv 32 := 0x00113c23.
Lemma F_5ea14 : fetch_word Asan.M.loaded_segments (0x5ea64 : word) = Some W_5ea14.
Proof. vm_refl. Qed.
Lemma D_5ea14 : decode_any W_5ea14 = Some (Store SZ8 2 1 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ea18 : bv 32 := 0x00813823.
Lemma F_5ea18 : fetch_word Asan.M.loaded_segments (0x5ea68 : word) = Some W_5ea18.
Proof. vm_refl. Qed.
Lemma D_5ea18 : decode_any W_5ea18 = Some (Store SZ8 2 8 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ea1c : bv 32 := 0x00913423.
Lemma F_5ea1c : fetch_word Asan.M.loaded_segments (0x5ea6c : word) = Some W_5ea1c.
Proof. vm_refl. Qed.
Lemma D_5ea1c : decode_any W_5ea1c = Some (Store SZ8 2 9 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ea20 : bv 32 := 0x01213023.
Lemma F_5ea20 : fetch_word Asan.M.loaded_segments (0x5ea70 : word) = Some W_5ea20.
Proof. vm_refl. Qed.
Lemma D_5ea20 : decode_any W_5ea20 = Some (Store SZ8 2 18 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ea24 : bv 32 := 0x02010413.
Lemma F_5ea24 : fetch_word Asan.M.loaded_segments (0x5ea74 : word) = Some W_5ea24.
Proof. vm_refl. Qed.
Lemma D_5ea24 : decode_any W_5ea24 = Some (OpImm ALU_ADD 8 2 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ea28 : bv 32 := 0x000db517.
Lemma F_5ea28 : fetch_word Asan.M.loaded_segments (0x5ea78 : word) = Some W_5ea28.
Proof. vm_refl. Qed.
Lemma D_5ea28 : decode_any W_5ea28 = Some (Auipc 10 219, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ea2c : bv 32 := 0x53850513.
Lemma F_5ea2c : fetch_word Asan.M.loaded_segments (0x5ea7c : word) = Some W_5ea2c.
Proof. vm_refl. Qed.
Lemma D_5ea2c : decode_any W_5ea2c = Some (OpImm ALU_ADD 10 10 1336, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ea30 : bv 32 := 0x2f4050ef.
Lemma F_5ea30 : fetch_word Asan.M.loaded_segments (0x5ea80 : word) = Some W_5ea30.
Proof. vm_refl. Qed.
Lemma D_5ea30 : decode_any W_5ea30 = Some (Jal 1 21236, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ea34 : bv 32 := 0x00053483.
Lemma F_5ea34 : fetch_word Asan.M.loaded_segments (0x5ea84 : word) = Some W_5ea34.
Proof. vm_refl. Qed.
Lemma D_5ea34 : decode_any W_5ea34 = Some (Load SZ8 true 9 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ea38 : bv 32 := 0x08048863.
Lemma F_5ea38 : fetch_word Asan.M.loaded_segments (0x5ea88 : word) = Some W_5ea38.
Proof. vm_refl. Qed.
Lemma D_5ea38 : decode_any W_5ea38 = Some (Branch BC_EQ 9 0 144, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ea3c : bv 32 := 0x0604c503.
Lemma F_5ea3c : fetch_word Asan.M.loaded_segments (0x5ea8c : word) = Some W_5ea3c.
Proof. vm_refl. Qed.
Lemma D_5ea3c : decode_any W_5ea3c = Some (Load SZ1 false 10 9 96, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ea40 : bv 32 := 0x0584b903.
Lemma F_5ea40 : fetch_word Asan.M.loaded_segments (0x5ea90 : word) = Some W_5ea40.
Proof. vm_refl. Qed.
Lemma D_5ea40 : decode_any W_5ea40 = Some (Load SZ8 true 18 9 88, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ea44 : bv 32 := 0x00050863.
Lemma F_5ea44 : fetch_word Asan.M.loaded_segments (0x5ea94 : word) = Some W_5ea44.
Proof. vm_refl. Qed.
Lemma D_5ea44 : decode_any W_5ea44 = Some (Branch BC_EQ 10 0 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ea48 : bv 32 := 0x00048513.
Lemma F_5ea48 : fetch_word Asan.M.loaded_segments (0x5ea98 : word) = Some W_5ea48.
Proof. vm_refl. Qed.
Lemma D_5ea48 : decode_any W_5ea48 = Some (OpImm ALU_ADD 10 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ea4c : bv 32 := 0x00040593.
Lemma F_5ea4c : fetch_word Asan.M.loaded_segments (0x5ea9c : word) = Some W_5ea4c.
Proof. vm_refl. Qed.
Lemma D_5ea4c : decode_any W_5ea4c = Some (OpImm ALU_ADD 11 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ea50 : bv 32 := 0xd28ff0ef.
Lemma F_5ea50 : fetch_word Asan.M.loaded_segments (0x5eaa0 : word) = Some W_5ea50.
Proof. vm_refl. Qed.
Lemma D_5ea50 : decode_any W_5ea50 = Some (Jal 1 2094376, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ea54 : bv 32 := 0xff590593.
Lemma F_5ea54 : fetch_word Asan.M.loaded_segments (0x5eaa4 : word) = Some W_5ea54.
Proof. vm_refl. Qed.
Lemma D_5ea54 : decode_any W_5ea54 = Some (OpImm ALU_ADD 11 18 4085, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ea58 : bv 32 := 0x00100513.
Lemma F_5ea58 : fetch_word Asan.M.loaded_segments (0x5eaa8 : word) = Some W_5ea58.
Proof. vm_refl. Qed.
Lemma D_5ea58 : decode_any W_5ea58 = Some (OpImm ALU_ADD 10 0 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ea5c : bv 32 := 0x00b51533.
Lemma F_5ea5c : fetch_word Asan.M.loaded_segments (0x5eaac : word) = Some W_5ea5c.
Proof. vm_refl. Qed.
Lemma D_5ea5c : decode_any W_5ea5c = Some (Op ALU_SLL 10 10 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ea60 : bv 32 := 0x0005061b.
Lemma F_5ea60 : fetch_word Asan.M.loaded_segments (0x5eab0 : word) = Some W_5ea60.
Proof. vm_refl. Qed.
Lemma D_5ea60 : decode_any W_5ea60 = Some (OpImm32 12 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ea64 : bv 32 := 0x08c05263.
Lemma F_5ea64 : fetch_word Asan.M.loaded_segments (0x5eab4 : word) = Some W_5ea64.
Proof. vm_refl. Qed.
Lemma D_5ea64 : decode_any W_5ea64 = Some (Branch BC_GE 0 12 132, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ea68 : bv 32 := 0x000016b7.
Lemma F_5ea68 : fetch_word Asan.M.loaded_segments (0x5eab8 : word) = Some W_5ea68.
Proof. vm_refl. Qed.
Lemma D_5ea68 : decode_any W_5ea68 = Some (Lui 13 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ea6c : bv 32 := 0xff190613.
Lemma F_5ea6c : fetch_word Asan.M.loaded_segments (0x5eabc : word) = Some W_5ea6c.
Proof. vm_refl. Qed.
Lemma D_5ea6c : decode_any W_5ea6c = Some (OpImm ALU_ADD 12 18 4081, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ea70 : bv 32 := 0x3e000713.
Lemma F_5ea70 : fetch_word Asan.M.loaded_segments (0x5eac0 : word) = Some W_5ea70.
Proof. vm_refl. Qed.
Lemma D_5ea70 : decode_any W_5ea70 = Some (OpImm ALU_ADD 14 0 992, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ea74 : bv 32 := 0xfff00793.
Lemma F_5ea74 : fetch_word Asan.M.loaded_segments (0x5eac4 : word) = Some W_5ea74.
Proof. vm_refl. Qed.
Lemma D_5ea74 : decode_any W_5ea74 = Some (OpImm ALU_ADD 15 0 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ea78 : bv 32 := 0x00c71733.
Lemma F_5ea78 : fetch_word Asan.M.loaded_segments (0x5eac8 : word) = Some W_5ea78.
Proof. vm_refl. Qed.
Lemma D_5ea78 : decode_any W_5ea78 = Some (Op ALU_SLL 14 14 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ea7c : bv 32 := 0x0284b603.
Lemma F_5ea7c : fetch_word Asan.M.loaded_segments (0x5eacc : word) = Some W_5ea7c.
Proof. vm_refl. Qed.
Lemma D_5ea7c : decode_any W_5ea7c = Some (Load SZ8 true 12 9 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ea80 : bv 32 := 0x00b797b3.
Lemma F_5ea80 : fetch_word Asan.M.loaded_segments (0x5ead0 : word) = Some W_5ea80.
Proof. vm_refl. Qed.
Lemma D_5ea80 : decode_any W_5ea80 = Some (Op ALU_SLL 15 15 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ea84 : bv 32 := 0xfff50813.
Lemma F_5ea84 : fetch_word Asan.M.loaded_segments (0x5ead4 : word) = Some W_5ea84.
Proof. vm_refl. Qed.
Lemma D_5ea84 : decode_any W_5ea84 = Some (OpImm ALU_ADD 16 10 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ea88 : bv 32 := 0x00d485b3.
Lemma F_5ea88 : fetch_word Asan.M.loaded_segments (0x5ead8 : word) = Some W_5ea88.
Proof. vm_refl. Qed.
Lemma D_5ea88 : decode_any W_5ea88 = Some (Op ALU_ADD 11 9 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ea8c : bv 32 := 0x00e586b3.
Lemma F_5ea8c : fetch_word Asan.M.loaded_segments (0x5eadc : word) = Some W_5ea8c.
Proof. vm_refl. Qed.
Lemma D_5ea8c : decode_any W_5ea8c = Some (Op ALU_ADD 13 11 14, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ea90 : bv 32 := 0xfff7c713.
Lemma F_5ea90 : fetch_word Asan.M.loaded_segments (0x5eae0 : word) = Some W_5ea90.
Proof. vm_refl. Qed.
Lemma D_5ea90 : decode_any W_5ea90 = Some (OpImm ALU_XOR 14 15 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ea94 : bv 32 := 0x02081813.
Lemma F_5ea94 : fetch_word Asan.M.loaded_segments (0x5eae4 : word) = Some W_5ea94.
Proof. vm_refl. Qed.
Lemma D_5ea94 : decode_any W_5ea94 = Some (ShiftImm ALU_SLL 16 16 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ea98 : bv 32 := 0x02085793.
Lemma F_5ea98 : fetch_word Asan.M.loaded_segments (0x5eae8 : word) = Some W_5ea98.
Proof. vm_refl. Qed.
Lemma D_5ea98 : decode_any W_5ea98 = Some (ShiftImm ALU_SRL 15 16 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ea9c : bv 32 := 0x00f607b3.
Lemma F_5ea9c : fetch_word Asan.M.loaded_segments (0x5eaec : word) = Some W_5ea9c.
Proof. vm_refl. Qed.
Lemma D_5ea9c : decode_any W_5ea9c = Some (Op ALU_ADD 15 12 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_5eaa0 : bv 32 := 0x00178813.
Lemma F_5eaa0 : fetch_word Asan.M.loaded_segments (0x5eaf0 : word) = Some W_5eaa0.
Proof. vm_refl. Qed.
Lemma D_5eaa0 : decode_any W_5eaa0 = Some (OpImm ALU_ADD 16 15 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_5eaa4 : bv 32 := 0x00e678b3.
Lemma F_5eaa4 : fetch_word Asan.M.loaded_segments (0x5eaf4 : word) = Some W_5eaa4.
Proof. vm_refl. Qed.
Lemma D_5eaa4 : decode_any W_5eaa4 = Some (Op ALU_AND 17 12 14, 4%Z).
Proof. vm_refl. Qed.

Definition W_5eaa8 : bv 32 := 0x011687b3.
Lemma F_5eaa8 : fetch_word Asan.M.loaded_segments (0x5eaf8 : word) = Some W_5eaa8.
Proof. vm_refl. Qed.
Lemma D_5eaa8 : decode_any W_5eaa8 = Some (Op ALU_ADD 15 13 17, 4%Z).
Proof. vm_refl. Qed.

Definition W_5eaac : bv 32 := 0x0007c283.
Lemma F_5eaac : fetch_word Asan.M.loaded_segments (0x5eafc : word) = Some W_5eaac.
Proof. vm_refl. Qed.
Lemma D_5eaac : decode_any W_5eaac = Some (Load SZ1 false 5 15 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5eab0 : bv 32 := 0x06028663.
Lemma F_5eab0 : fetch_word Asan.M.loaded_segments (0x5eb00 : word) = Some W_5eab0.
Proof. vm_refl. Qed.
Lemma D_5eab0 : decode_any W_5eab0 = Some (Branch BC_EQ 5 0 108, 4%Z).
Proof. vm_refl. Qed.

Definition W_5eab4 : bv 32 := 0xfff5051b.
Lemma F_5eab4 : fetch_word Asan.M.loaded_segments (0x5eb04 : word) = Some W_5eab4.
Proof. vm_refl. Qed.
Lemma D_5eab4 : decode_any W_5eab4 = Some (OpImm32 10 10 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_5eab8 : bv 32 := 0x00160613.
Lemma F_5eab8 : fetch_word Asan.M.loaded_segments (0x5eb08 : word) = Some W_5eab8.
Proof. vm_refl. Qed.
Lemma D_5eab8 : decode_any W_5eab8 = Some (OpImm ALU_ADD 12 12 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_5eabc : bv 32 := 0xfe0514e3.
Lemma F_5eabc : fetch_word Asan.M.loaded_segments (0x5eb0c : word) = Some W_5eabc.
Proof. vm_refl. Qed.
Lemma D_5eabc : decode_any W_5eabc = Some (Branch BC_NE 10 0 8168, 4%Z).
Proof. vm_refl. Qed.

Definition W_5eac0 : bv 32 := 0x0304b423.
Lemma F_5eac0 : fetch_word Asan.M.loaded_segments (0x5eb10 : word) = Some W_5eac0.
Proof. vm_refl. Qed.
Lemma D_5eac0 : decode_any W_5eac0 = Some (Store SZ8 9 16 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_5eac4 : bv 32 := 0x0400006f.
Lemma F_5eac4 : fetch_word Asan.M.loaded_segments (0x5eb14 : word) = Some W_5eac4.
Proof. vm_refl. Qed.
Lemma D_5eac4 : decode_any W_5eac4 = Some (Jal 0 64, 4%Z).
Proof. vm_refl. Qed.

Definition W_5eac8 : bv 32 := 0x000da517.
Lemma F_5eac8 : fetch_word Asan.M.loaded_segments (0x5eb18 : word) = Some W_5eac8.
Proof. vm_refl. Qed.
Lemma D_5eac8 : decode_any W_5eac8 = Some (Auipc 10 218, 4%Z).
Proof. vm_refl. Qed.

Definition W_5eacc : bv 32 := 0x6f853503.
Lemma F_5eacc : fetch_word Asan.M.loaded_segments (0x5eb1c : word) = Some W_5eacc.
Proof. vm_refl. Qed.
Lemma D_5eacc : decode_any W_5eacc = Some (Load SZ8 true 10 10 1784, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ead0 : bv 32 := 0x00052503.
Lemma F_5ead0 : fetch_word Asan.M.loaded_segments (0x5eb20 : word) = Some W_5ead0.
Proof. vm_refl. Qed.
Lemma D_5ead0 : decode_any W_5ead0 = Some (Load SZ4 true 10 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ead4 : bv 32 := 0x02050863.
Lemma F_5ead4 : fetch_word Asan.M.loaded_segments (0x5eb24 : word) = Some W_5ead4.
Proof. vm_refl. Qed.
Lemma D_5ead4 : decode_any W_5ead4 = Some (Branch BC_EQ 10 0 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ead8 : bv 32 := 0x740250ef.
Lemma F_5ead8 : fetch_word Asan.M.loaded_segments (0x5eb28 : word) = Some W_5ead8.
Proof. vm_refl. Qed.
Lemma D_5ead8 : decode_any W_5ead8 = Some (Jal 1 153408, 4%Z).
Proof. vm_refl. Qed.

Definition W_5eadc : bv 32 := 0x02050463.
Lemma F_5eadc : fetch_word Asan.M.loaded_segments (0x5eb2c : word) = Some W_5eadc.
Proof. vm_refl. Qed.
Lemma D_5eadc : decode_any W_5eadc = Some (Branch BC_EQ 10 0 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_5eae0 : bv 32 := 0x02850583.
Lemma F_5eae0 : fetch_word Asan.M.loaded_segments (0x5eb30 : word) = Some W_5eae0.
Proof. vm_refl. Qed.
Lemma D_5eae0 : decode_any W_5eae0 = Some (Load SZ1 true 11 10 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_5eae4 : bv 32 := 0x10058e63.
Lemma F_5eae4 : fetch_word Asan.M.loaded_segments (0x5eb34 : word) = Some W_5eae4.
Proof. vm_refl. Qed.
Lemma D_5eae4 : decode_any W_5eae4 = Some (Branch BC_EQ 11 0 284, 4%Z).
Proof. vm_refl. Qed.

Definition W_5eae8 : bv 32 := 0x00000513.
Lemma F_5eae8 : fetch_word Asan.M.loaded_segments (0x5eb38 : word) = Some W_5eae8.
Proof. vm_refl. Qed.
Lemma D_5eae8 : decode_any W_5eae8 = Some (OpImm ALU_ADD 10 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5eaec : bv 32 := 0x01813083.
Lemma F_5eaec : fetch_word Asan.M.loaded_segments (0x5eb3c : word) = Some W_5eaec.
Proof. vm_refl. Qed.
Lemma D_5eaec : decode_any W_5eaec = Some (Load SZ8 true 1 2 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_5eaf0 : bv 32 := 0x01013403.
Lemma F_5eaf0 : fetch_word Asan.M.loaded_segments (0x5eb40 : word) = Some W_5eaf0.
Proof. vm_refl. Qed.
Lemma D_5eaf0 : decode_any W_5eaf0 = Some (Load SZ8 true 8 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_5eaf4 : bv 32 := 0x00813483.
Lemma F_5eaf4 : fetch_word Asan.M.loaded_segments (0x5eb44 : word) = Some W_5eaf4.
Proof. vm_refl. Qed.
Lemma D_5eaf4 : decode_any W_5eaf4 = Some (Load SZ8 true 9 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_5eaf8 : bv 32 := 0x00013903.
Lemma F_5eaf8 : fetch_word Asan.M.loaded_segments (0x5eb48 : word) = Some W_5eaf8.
Proof. vm_refl. Qed.
Lemma D_5eaf8 : decode_any W_5eaf8 = Some (Load SZ8 true 18 2 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5eafc : bv 32 := 0x02010113.
Lemma F_5eafc : fetch_word Asan.M.loaded_segments (0x5eb4c : word) = Some W_5eafc.
Proof. vm_refl. Qed.
Lemma D_5eafc : decode_any W_5eafc = Some (OpImm ALU_ADD 2 2 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_5eb00 : bv 32 := 0x00008067.
Lemma F_5eb00 : fetch_word Asan.M.loaded_segments (0x5eb50 : word) = Some W_5eb00.
Proof. vm_refl. Qed.
Lemma D_5eb00 : decode_any W_5eb00 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5eb04 : bv 32 := 0x01813083.
Lemma F_5eb04 : fetch_word Asan.M.loaded_segments (0x5eb54 : word) = Some W_5eb04.
Proof. vm_refl. Qed.
Lemma D_5eb04 : decode_any W_5eb04 = Some (Load SZ8 true 1 2 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_5eb08 : bv 32 := 0x01013403.
Lemma F_5eb08 : fetch_word Asan.M.loaded_segments (0x5eb58 : word) = Some W_5eb08.
Proof. vm_refl. Qed.
Lemma D_5eb08 : decode_any W_5eb08 = Some (Load SZ8 true 8 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_5eb0c : bv 32 := 0x00813483.
Lemma F_5eb0c : fetch_word Asan.M.loaded_segments (0x5eb5c : word) = Some W_5eb0c.
Proof. vm_refl. Qed.
Lemma D_5eb0c : decode_any W_5eb0c = Some (Load SZ8 true 9 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_5eb10 : bv 32 := 0x00013903.
Lemma F_5eb10 : fetch_word Asan.M.loaded_segments (0x5eb60 : word) = Some W_5eb10.
Proof. vm_refl. Qed.
Lemma D_5eb10 : decode_any W_5eb10 = Some (Load SZ8 true 18 2 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5eb14 : bv 32 := 0x02010113.
Lemma F_5eb14 : fetch_word Asan.M.loaded_segments (0x5eb64 : word) = Some W_5eb14.
Proof. vm_refl. Qed.
Lemma D_5eb14 : decode_any W_5eb14 = Some (OpImm ALU_ADD 2 2 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_5eb18 : bv 32 := 0x00008067.
Lemma F_5eb18 : fetch_word Asan.M.loaded_segments (0x5eb68 : word) = Some W_5eb18.
Proof. vm_refl. Qed.
Lemma D_5eb18 : decode_any W_5eb18 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5eb1c : bv 32 := 0x00160613.
Lemma F_5eb1c : fetch_word Asan.M.loaded_segments (0x5eb6c : word) = Some W_5eb1c.
Proof. vm_refl. Qed.
Lemma D_5eb1c : decode_any W_5eb1c = Some (OpImm ALU_ADD 12 12 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_5eb20 : bv 32 := 0x00100513.
Lemma F_5eb20 : fetch_word Asan.M.loaded_segments (0x5eb70 : word) = Some W_5eb20.
Proof. vm_refl. Qed.
Lemma D_5eb20 : decode_any W_5eb20 = Some (OpImm ALU_ADD 10 0 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_5eb24 : bv 32 := 0xffb90693.
Lemma F_5eb24 : fetch_word Asan.M.loaded_segments (0x5eb74 : word) = Some W_5eb24.
Proof. vm_refl. Qed.
Lemma D_5eb24 : decode_any W_5eb24 = Some (OpImm ALU_ADD 13 18 4091, 4%Z).
Proof. vm_refl. Qed.

Definition W_5eb28 : bv 32 := 0x02c4b423.
Lemma F_5eb28 : fetch_word Asan.M.loaded_segments (0x5eb78 : word) = Some W_5eb28.
Proof. vm_refl. Qed.
Lemma D_5eb28 : decode_any W_5eb28 = Some (Store SZ8 9 12 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_5eb2c : bv 32 := 0x00a78023.
Lemma F_5eb2c : fetch_word Asan.M.loaded_segments (0x5eb7c : word) = Some W_5eb2c.
Proof. vm_refl. Qed.
Lemma D_5eb2c : decode_any W_5eb2c = Some (Store SZ1 15 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5eb30 : bv 32 := 0x00d51533.
Lemma F_5eb30 : fetch_word Asan.M.loaded_segments (0x5eb80 : word) = Some W_5eb30.
Proof. vm_refl. Qed.
Lemma D_5eb30 : decode_any W_5eb30 = Some (Op ALU_SLL 10 10 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_5eb34 : bv 32 := 0x00500613.
Lemma F_5eb34 : fetch_word Asan.M.loaded_segments (0x5eb84 : word) = Some W_5eb34.
Proof. vm_refl. Qed.
Lemma D_5eb34 : decode_any W_5eb34 = Some (OpImm ALU_ADD 12 0 5, 4%Z).
Proof. vm_refl. Qed.

Definition W_5eb38 : bv 32 := 0x00b89893.
Lemma F_5eb38 : fetch_word Asan.M.loaded_segments (0x5eb88 : word) = Some W_5eb38.
Proof. vm_refl. Qed.
Lemma D_5eb38 : decode_any W_5eb38 = Some (ShiftImm ALU_SLL 17 17 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_5eb3c : bv 32 := 0x01261633.
Lemma F_5eb3c : fetch_word Asan.M.loaded_segments (0x5eb8c : word) = Some W_5eb3c.
Proof. vm_refl. Qed.
Lemma D_5eb3c : decode_any W_5eb3c = Some (Op ALU_SLL 12 12 18, 4%Z).
Proof. vm_refl. Qed.

Definition W_5eb40 : bv 32 := 0x00a58533.
Lemma F_5eb40 : fetch_word Asan.M.loaded_segments (0x5eb90 : word) = Some W_5eb40.
Proof. vm_refl. Qed.
Lemma D_5eb40 : decode_any W_5eb40 = Some (Op ALU_ADD 10 11 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_5eb44 : bv 32 := 0x01160633.
Lemma F_5eb44 : fetch_word Asan.M.loaded_segments (0x5eb94 : word) = Some W_5eb44.
Proof. vm_refl. Qed.
Lemma D_5eb44 : decode_any W_5eb44 = Some (Op ALU_ADD 12 12 17, 4%Z).
Proof. vm_refl. Qed.

Definition W_5eb48 : bv 32 := 0x00c504b3.
Lemma F_5eb48 : fetch_word Asan.M.loaded_segments (0x5eb98 : word) = Some W_5eb48.
Proof. vm_refl. Qed.
Lemma D_5eb48 : decode_any W_5eb48 = Some (Op ALU_ADD 9 10 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_5eb4c : bv 32 := 0x0084bc23.
Lemma F_5eb4c : fetch_word Asan.M.loaded_segments (0x5eb9c : word) = Some W_5eb4c.
Proof. vm_refl. Qed.
Lemma D_5eb4c : decode_any W_5eb4c = Some (Store SZ8 9 8 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_5eb50 : bv 32 := 0x7ef4bc23.
Lemma F_5eb50 : fetch_word Asan.M.loaded_segments (0x5eba0 : word) = Some W_5eb50.
Proof. vm_refl. Qed.
Lemma D_5eb50 : decode_any W_5eb50 = Some (Store SZ8 9 15 2040, 4%Z).
Proof. vm_refl. Qed.

Definition W_5eb54 : bv 32 := 0x00048513.
Lemma F_5eb54 : fetch_word Asan.M.loaded_segments (0x5eba4 : word) = Some W_5eb54.
Proof. vm_refl. Qed.
Lemma D_5eb54 : decode_any W_5eb54 = Some (OpImm ALU_ADD 10 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5eb58 : bv 32 := 0x178000ef.
Lemma F_5eb58 : fetch_word Asan.M.loaded_segments (0x5eba8 : word) = Some W_5eb58.
Proof. vm_refl. Qed.
Lemma D_5eb58 : decode_any W_5eb58 = Some (Jal 1 376, 4%Z).
Proof. vm_refl. Qed.

Definition W_5eb5c : bv 32 := 0x00050593.
Lemma F_5eb5c : fetch_word Asan.M.loaded_segments (0x5ebac : word) = Some W_5eb5c.
Proof. vm_refl. Qed.
Lemma D_5eb5c : decode_any W_5eb5c = Some (OpImm ALU_ADD 11 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5eb60 : bv 32 := 0x00048513.
Lemma F_5eb60 : fetch_word Asan.M.loaded_segments (0x5ebb0 : word) = Some W_5eb60.
Proof. vm_refl. Qed.
Lemma D_5eb60 : decode_any W_5eb60 = Some (OpImm ALU_ADD 10 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5eb64 : bv 32 := 0x00000613.
Lemma F_5eb64 : fetch_word Asan.M.loaded_segments (0x5ebb4 : word) = Some W_5eb64.
Proof. vm_refl. Qed.
Lemma D_5eb64 : decode_any W_5eb64 = Some (OpImm ALU_ADD 12 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5eb68 : bv 32 := 0x0005b023.
Lemma F_5eb68 : fetch_word Asan.M.loaded_segments (0x5ebb8 : word) = Some W_5eb68.
Proof. vm_refl. Qed.
Lemma D_5eb68 : decode_any W_5eb68 = Some (Store SZ8 11 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5eb6c : bv 32 := 0x0005b423.
Lemma F_5eb6c : fetch_word Asan.M.loaded_segments (0x5ebbc : word) = Some W_5eb6c.
Proof. vm_refl. Qed.
Lemma D_5eb6c : decode_any W_5eb6c = Some (Store SZ8 11 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_5eb70 : bv 32 := 0x0005b823.
Lemma F_5eb70 : fetch_word Asan.M.loaded_segments (0x5ebc0 : word) = Some W_5eb70.
Proof. vm_refl. Qed.
Lemma D_5eb70 : decode_any W_5eb70 = Some (Store SZ8 11 0 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_5eb74 : bv 32 := 0x0005bc23.
Lemma F_5eb74 : fetch_word Asan.M.loaded_segments (0x5ebc4 : word) = Some W_5eb74.
Proof. vm_refl. Qed.
Lemma D_5eb74 : decode_any W_5eb74 = Some (Store SZ8 11 0 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_5eb78 : bv 32 := 0x0205b023.
Lemma F_5eb78 : fetch_word Asan.M.loaded_segments (0x5ebc8 : word) = Some W_5eb78.
Proof. vm_refl. Qed.
Lemma D_5eb78 : decode_any W_5eb78 = Some (Store SZ8 11 0 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_5eb7c : bv 32 := 0x0205b423.
Lemma F_5eb7c : fetch_word Asan.M.loaded_segments (0x5ebcc : word) = Some W_5eb7c.
Proof. vm_refl. Qed.
Lemma D_5eb7c : decode_any W_5eb7c = Some (Store SZ8 11 0 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_5eb80 : bv 32 := 0x0205b823.
Lemma F_5eb80 : fetch_word Asan.M.loaded_segments (0x5ebd0 : word) = Some W_5eb80.
Proof. vm_refl. Qed.
Lemma D_5eb80 : decode_any W_5eb80 = Some (Store SZ8 11 0 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_5eb84 : bv 32 := 0x0205bc23.
Lemma F_5eb84 : fetch_word Asan.M.loaded_segments (0x5ebd4 : word) = Some W_5eb84.
Proof. vm_refl. Qed.
Lemma D_5eb84 : decode_any W_5eb84 = Some (Store SZ8 11 0 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_5eb88 : bv 32 := 0x0405b023.
Lemma F_5eb88 : fetch_word Asan.M.loaded_segments (0x5ebd8 : word) = Some W_5eb88.
Proof. vm_refl. Qed.
Lemma D_5eb88 : decode_any W_5eb88 = Some (Store SZ8 11 0 64, 4%Z).
Proof. vm_refl. Qed.

Definition W_5eb8c : bv 32 := 0x0405b423.
Lemma F_5eb8c : fetch_word Asan.M.loaded_segments (0x5ebdc : word) = Some W_5eb8c.
Proof. vm_refl. Qed.
Lemma D_5eb8c : decode_any W_5eb8c = Some (Store SZ8 11 0 72, 4%Z).
Proof. vm_refl. Qed.

Definition W_5eb90 : bv 32 := 0x0405b823.
Lemma F_5eb90 : fetch_word Asan.M.loaded_segments (0x5ebe0 : word) = Some W_5eb90.
Proof. vm_refl. Qed.
Lemma D_5eb90 : decode_any W_5eb90 = Some (Store SZ8 11 0 80, 4%Z).
Proof. vm_refl. Qed.

Definition W_5eb94 : bv 32 := 0x0405bc23.
Lemma F_5eb94 : fetch_word Asan.M.loaded_segments (0x5ebe4 : word) = Some W_5eb94.
Proof. vm_refl. Qed.
Lemma D_5eb94 : decode_any W_5eb94 = Some (Store SZ8 11 0 88, 4%Z).
Proof. vm_refl. Qed.

Definition W_5eb98 : bv 32 := 0x0605b023.
Lemma F_5eb98 : fetch_word Asan.M.loaded_segments (0x5ebe8 : word) = Some W_5eb98.
Proof. vm_refl. Qed.
Lemma D_5eb98 : decode_any W_5eb98 = Some (Store SZ8 11 0 96, 4%Z).
Proof. vm_refl. Qed.

Definition W_5eb9c : bv 32 := 0x0605b423.
Lemma F_5eb9c : fetch_word Asan.M.loaded_segments (0x5ebec : word) = Some W_5eb9c.
Proof. vm_refl. Qed.
Lemma D_5eb9c : decode_any W_5eb9c = Some (Store SZ8 11 0 104, 4%Z).
Proof. vm_refl. Qed.

Definition W_5eba0 : bv 32 := 0x0605b823.
Lemma F_5eba0 : fetch_word Asan.M.loaded_segments (0x5ebf0 : word) = Some W_5eba0.
Proof. vm_refl. Qed.
Lemma D_5eba0 : decode_any W_5eba0 = Some (Store SZ8 11 0 112, 4%Z).
Proof. vm_refl. Qed.

Definition W_5eba4 : bv 32 := 0x0605bc23.
Lemma F_5eba4 : fetch_word Asan.M.loaded_segments (0x5ebf4 : word) = Some W_5eba4.
Proof. vm_refl. Qed.
Lemma D_5eba4 : decode_any W_5eba4 = Some (Store SZ8 11 0 120, 4%Z).
Proof. vm_refl. Qed.

Definition W_5eba8 : bv 32 := 0x0805b023.
Lemma F_5eba8 : fetch_word Asan.M.loaded_segments (0x5ebf8 : word) = Some W_5eba8.
Proof. vm_refl. Qed.
Lemma D_5eba8 : decode_any W_5eba8 = Some (Store SZ8 11 0 128, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ebac : bv 32 := 0x0805b423.
Lemma F_5ebac : fetch_word Asan.M.loaded_segments (0x5ebfc : word) = Some W_5ebac.
Proof. vm_refl. Qed.
Lemma D_5ebac : decode_any W_5ebac = Some (Store SZ8 11 0 136, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ebb0 : bv 32 := 0x0805b823.
Lemma F_5ebb0 : fetch_word Asan.M.loaded_segments (0x5ec00 : word) = Some W_5ebb0.
Proof. vm_refl. Qed.
Lemma D_5ebb0 : decode_any W_5ebb0 = Some (Store SZ8 11 0 144, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ebb4 : bv 32 := 0x0805bc23.
Lemma F_5ebb4 : fetch_word Asan.M.loaded_segments (0x5ec04 : word) = Some W_5ebb4.
Proof. vm_refl. Qed.
Lemma D_5ebb4 : decode_any W_5ebb4 = Some (Store SZ8 11 0 152, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ebb8 : bv 32 := 0x0a05b023.
Lemma F_5ebb8 : fetch_word Asan.M.loaded_segments (0x5ec08 : word) = Some W_5ebb8.
Proof. vm_refl. Qed.
Lemma D_5ebb8 : decode_any W_5ebb8 = Some (Store SZ8 11 0 160, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ebbc : bv 32 := 0x0a05b423.
Lemma F_5ebbc : fetch_word Asan.M.loaded_segments (0x5ec0c : word) = Some W_5ebbc.
Proof. vm_refl. Qed.
Lemma D_5ebbc : decode_any W_5ebbc = Some (Store SZ8 11 0 168, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ebc0 : bv 32 := 0x0a05b823.
Lemma F_5ebc0 : fetch_word Asan.M.loaded_segments (0x5ec10 : word) = Some W_5ebc0.
Proof. vm_refl. Qed.
Lemma D_5ebc0 : decode_any W_5ebc0 = Some (Store SZ8 11 0 176, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ebc4 : bv 32 := 0x0a05bc23.
Lemma F_5ebc4 : fetch_word Asan.M.loaded_segments (0x5ec14 : word) = Some W_5ebc4.
Proof. vm_refl. Qed.
Lemma D_5ebc4 : decode_any W_5ebc4 = Some (Store SZ8 11 0 184, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ebc8 : bv 32 := 0x0c05b023.
Lemma F_5ebc8 : fetch_word Asan.M.loaded_segments (0x5ec18 : word) = Some W_5ebc8.
Proof. vm_refl. Qed.
Lemma D_5ebc8 : decode_any W_5ebc8 = Some (Store SZ8 11 0 192, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ebcc : bv 32 := 0x0c05b423.
Lemma F_5ebcc : fetch_word Asan.M.loaded_segments (0x5ec1c : word) = Some W_5ebcc.
Proof. vm_refl. Qed.
Lemma D_5ebcc : decode_any W_5ebcc = Some (Store SZ8 11 0 200, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ebd0 : bv 32 := 0x0c05b823.
Lemma F_5ebd0 : fetch_word Asan.M.loaded_segments (0x5ec20 : word) = Some W_5ebd0.
Proof. vm_refl. Qed.
Lemma D_5ebd0 : decode_any W_5ebd0 = Some (Store SZ8 11 0 208, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ebd4 : bv 32 := 0x0c05bc23.
Lemma F_5ebd4 : fetch_word Asan.M.loaded_segments (0x5ec24 : word) = Some W_5ebd4.
Proof. vm_refl. Qed.
Lemma D_5ebd4 : decode_any W_5ebd4 = Some (Store SZ8 11 0 216, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ebd8 : bv 32 := 0x0e05b023.
Lemma F_5ebd8 : fetch_word Asan.M.loaded_segments (0x5ec28 : word) = Some W_5ebd8.
Proof. vm_refl. Qed.
Lemma D_5ebd8 : decode_any W_5ebd8 = Some (Store SZ8 11 0 224, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ebdc : bv 32 := 0x0e05b423.
Lemma F_5ebdc : fetch_word Asan.M.loaded_segments (0x5ec2c : word) = Some W_5ebdc.
Proof. vm_refl. Qed.
Lemma D_5ebdc : decode_any W_5ebdc = Some (Store SZ8 11 0 232, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ebe0 : bv 32 := 0x0e05b823.
Lemma F_5ebe0 : fetch_word Asan.M.loaded_segments (0x5ec30 : word) = Some W_5ebe0.
Proof. vm_refl. Qed.
Lemma D_5ebe0 : decode_any W_5ebe0 = Some (Store SZ8 11 0 240, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ebe4 : bv 32 := 0x0e05bc23.
Lemma F_5ebe4 : fetch_word Asan.M.loaded_segments (0x5ec34 : word) = Some W_5ebe4.
Proof. vm_refl. Qed.
Lemma D_5ebe4 : decode_any W_5ebe4 = Some (Store SZ8 11 0 248, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ebe8 : bv 32 := 0x01813083.
Lemma F_5ebe8 : fetch_word Asan.M.loaded_segments (0x5ec38 : word) = Some W_5ebe8.
Proof. vm_refl. Qed.
Lemma D_5ebe8 : decode_any W_5ebe8 = Some (Load SZ8 true 1 2 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ebec : bv 32 := 0x01013403.
Lemma F_5ebec : fetch_word Asan.M.loaded_segments (0x5ec3c : word) = Some W_5ebec.
Proof. vm_refl. Qed.
Lemma D_5ebec : decode_any W_5ebec = Some (Load SZ8 true 8 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ebf0 : bv 32 := 0x00813483.
Lemma F_5ebf0 : fetch_word Asan.M.loaded_segments (0x5ec40 : word) = Some W_5ebf0.
Proof. vm_refl. Qed.
Lemma D_5ebf0 : decode_any W_5ebf0 = Some (Load SZ8 true 9 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ebf4 : bv 32 := 0x00013903.
Lemma F_5ebf4 : fetch_word Asan.M.loaded_segments (0x5ec44 : word) = Some W_5ebf4.
Proof. vm_refl. Qed.
Lemma D_5ebf4 : decode_any W_5ebf4 = Some (Load SZ8 true 18 2 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ebf8 : bv 32 := 0x02010113.
Lemma F_5ebf8 : fetch_word Asan.M.loaded_segments (0x5ec48 : word) = Some W_5ebf8.
Proof. vm_refl. Qed.
Lemma D_5ebf8 : decode_any W_5ebf8 = Some (OpImm ALU_ADD 2 2 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ebfc : bv 32 := 0x00008067.
Lemma F_5ebfc : fetch_word Asan.M.loaded_segments (0x5ec4c : word) = Some W_5ebfc.
Proof. vm_refl. Qed.
Lemma D_5ebfc : decode_any W_5ebfc = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ec00 : bv 32 := 0x04853483.
Lemma F_5ec00 : fetch_word Asan.M.loaded_segments (0x5ec50 : word) = Some W_5ec00.
Proof. vm_refl. Qed.
Lemma D_5ec00 : decode_any W_5ec00 = Some (Load SZ8 true 9 10 72, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ec04 : bv 32 := 0x00100593.
Lemma F_5ec04 : fetch_word Asan.M.loaded_segments (0x5ec54 : word) = Some W_5ec04.
Proof. vm_refl. Qed.
Lemma D_5ec04 : decode_any W_5ec04 = Some (OpImm ALU_ADD 11 0 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ec08 : bv 32 := 0x0095e663.
Lemma F_5ec08 : fetch_word Asan.M.loaded_segments (0x5ec58 : word) = Some W_5ec08.
Proof. vm_refl. Qed.
Lemma D_5ec08 : decode_any W_5ec08 = Some (Branch BC_LTU 11 9 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ec0c : bv 32 := 0x081250ef.
Lemma F_5ec0c : fetch_word Asan.M.loaded_segments (0x5ec5c : word) = Some W_5ec0c.
Proof. vm_refl. Qed.
Lemma D_5ec0c : decode_any W_5ec0c = Some (Jal 1 153728, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ec10 : bv 32 := 0x00050493.
Lemma F_5ec10 : fetch_word Asan.M.loaded_segments (0x5ec60 : word) = Some W_5ec10.
Proof. vm_refl. Qed.
Lemma D_5ec10 : decode_any W_5ec10 = Some (OpImm ALU_ADD 9 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ec14 : bv 32 := 0xe20494e3.
Lemma F_5ec14 : fetch_word Asan.M.loaded_segments (0x5ec64 : word) = Some W_5ec14.
Proof. vm_refl. Qed.
Lemma D_5ec14 : decode_any W_5ec14 = Some (Branch BC_NE 9 0 7720, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ec18 : bv 32 := 0xed1ff06f.
Lemma F_5ec18 : fetch_word Asan.M.loaded_segments (0x5ec68 : word) = Some W_5ec18.
Proof. vm_refl. Qed.
Lemma D_5ec18 : decode_any W_5ec18 = Some (Jal 0 2096848, 4%Z).
Proof. vm_refl. Qed.
