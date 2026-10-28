(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)


From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OssFuzzTheorems.json_c.json_object_fuzzer.images Require Import Ubsan.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.

Local Ltac vm_refl :=
lazymatch goal with
| |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
end.

Definition W_4e9bc : bv 32 := 0x17813083.
Lemma F_4e9bc : fetch_word Ubsan.M.loaded_segments (0x507a4 : word) = Some W_4e9bc.
Proof. vm_refl. Qed.
Lemma D_4e9bc : decode_any W_4e9bc = Some (Load SZ8 true 1 2 376, 4%Z).
Proof. vm_refl. Qed.

Definition W_4e9c0 : bv 32 := 0x17013403.
Lemma F_4e9c0 : fetch_word Ubsan.M.loaded_segments (0x507a8 : word) = Some W_4e9c0.
Proof. vm_refl. Qed.
Lemma D_4e9c0 : decode_any W_4e9c0 = Some (Load SZ8 true 8 2 368, 4%Z).
Proof. vm_refl. Qed.

Definition W_4e9c4 : bv 32 := 0x16813483.
Lemma F_4e9c4 : fetch_word Ubsan.M.loaded_segments (0x507ac : word) = Some W_4e9c4.
Proof. vm_refl. Qed.
Lemma D_4e9c4 : decode_any W_4e9c4 = Some (Load SZ8 true 9 2 360, 4%Z).
Proof. vm_refl. Qed.

Definition W_4e9c8 : bv 32 := 0x16013903.
Lemma F_4e9c8 : fetch_word Ubsan.M.loaded_segments (0x507b0 : word) = Some W_4e9c8.
Proof. vm_refl. Qed.
Lemma D_4e9c8 : decode_any W_4e9c8 = Some (Load SZ8 true 18 2 352, 4%Z).
Proof. vm_refl. Qed.

Definition W_4e9cc : bv 32 := 0x18010113.
Lemma F_4e9cc : fetch_word Ubsan.M.loaded_segments (0x507b4 : word) = Some W_4e9cc.
Proof. vm_refl. Qed.
Lemma D_4e9cc : decode_any W_4e9cc = Some (OpImm ALU_ADD 2 2 384, 4%Z).
Proof. vm_refl. Qed.

Definition W_4e9d0 : bv 32 := 0x00008067.
Lemma F_4e9d0 : fetch_word Ubsan.M.loaded_segments (0x507b8 : word) = Some W_4e9d0.
Proof. vm_refl. Qed.
Lemma D_4e9d0 : decode_any W_4e9d0 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_4e9d4 : bv 32 := 0xfe010113.
Lemma F_4e9d4 : fetch_word Ubsan.M.loaded_segments (0x507bc : word) = Some W_4e9d4.
Proof. vm_refl. Qed.
Lemma D_4e9d4 : decode_any W_4e9d4 = Some (OpImm ALU_ADD 2 2 4064, 4%Z).
Proof. vm_refl. Qed.

Definition W_4e9d8 : bv 32 := 0x00113c23.
Lemma F_4e9d8 : fetch_word Ubsan.M.loaded_segments (0x507c0 : word) = Some W_4e9d8.
Proof. vm_refl. Qed.
Lemma D_4e9d8 : decode_any W_4e9d8 = Some (Store SZ8 2 1 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_4e9dc : bv 32 := 0x00813823.
Lemma F_4e9dc : fetch_word Ubsan.M.loaded_segments (0x507c4 : word) = Some W_4e9dc.
Proof. vm_refl. Qed.
Lemma D_4e9dc : decode_any W_4e9dc = Some (Store SZ8 2 8 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_4e9e0 : bv 32 := 0x00913423.
Lemma F_4e9e0 : fetch_word Ubsan.M.loaded_segments (0x507c8 : word) = Some W_4e9e0.
Proof. vm_refl. Qed.
Lemma D_4e9e0 : decode_any W_4e9e0 = Some (Store SZ8 2 9 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_4e9e4 : bv 32 := 0xdc1ff0ef.
Lemma F_4e9e4 : fetch_word Ubsan.M.loaded_segments (0x507cc : word) = Some W_4e9e4.
Proof. vm_refl. Qed.
Lemma D_4e9e4 : decode_any W_4e9e4 = Some (Jal 1 2096576, 4%Z).
Proof. vm_refl. Qed.

Definition W_4e9e8 : bv 32 := 0x00015517.
Lemma F_4e9e8 : fetch_word Ubsan.M.loaded_segments (0x507d0 : word) = Some W_4e9e8.
Proof. vm_refl. Qed.
Lemma D_4e9e8 : decode_any W_4e9e8 = Some (Auipc 10 21, 4%Z).
Proof. vm_refl. Qed.

Definition W_4e9ec : bv 32 := 0x00015597.
Lemma F_4e9ec : fetch_word Ubsan.M.loaded_segments (0x507d4 : word) = Some W_4e9ec.
Proof. vm_refl. Qed.
Lemma D_4e9ec : decode_any W_4e9ec = Some (Auipc 11 21, 4%Z).
Proof. vm_refl. Qed.

Definition W_4e9f0 : bv 32 := 0x1f053403.
Lemma F_4e9f0 : fetch_word Ubsan.M.loaded_segments (0x507d8 : word) = Some W_4e9f0.
Proof. vm_refl. Qed.
Lemma D_4e9f0 : decode_any W_4e9f0 = Some (Load SZ8 true 8 10 496, 4%Z).
Proof. vm_refl. Qed.

Definition W_4e9f4 : bv 32 := 0x1f45b483.
Lemma F_4e9f4 : fetch_word Ubsan.M.loaded_segments (0x507dc : word) = Some W_4e9f4.
Proof. vm_refl. Qed.
Lemma D_4e9f4 : decode_any W_4e9f4 = Some (Load SZ8 true 9 11 500, 4%Z).
Proof. vm_refl. Qed.

Definition W_4e9f8 : bv 32 := 0x0084fa63.
Lemma F_4e9f8 : fetch_word Ubsan.M.loaded_segments (0x507e0 : word) = Some W_4e9f8.
Proof. vm_refl. Qed.
Lemma D_4e9f8 : decode_any W_4e9f8 = Some (Branch BC_GEU 9 8 20, 4%Z).
Proof. vm_refl. Qed.

Definition W_4e9fc : bv 32 := 0x0004b503.
Lemma F_4e9fc : fetch_word Ubsan.M.loaded_segments (0x507e4 : word) = Some W_4e9fc.
Proof. vm_refl. Qed.
Lemma D_4e9fc : decode_any W_4e9fc = Some (Load SZ8 true 10 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_4ea00 : bv 32 := 0x000500e7.
Lemma F_4ea00 : fetch_word Ubsan.M.loaded_segments (0x507e8 : word) = Some W_4ea00.
Proof. vm_refl. Qed.
Lemma D_4ea00 : decode_any W_4ea00 = Some (Jalr 1 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_4ea04 : bv 32 := 0x00848493.
Lemma F_4ea04 : fetch_word Ubsan.M.loaded_segments (0x507ec : word) = Some W_4ea04.
Proof. vm_refl. Qed.
Lemma D_4ea04 : decode_any W_4ea04 = Some (OpImm ALU_ADD 9 9 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_4ea08 : bv 32 := 0xfe84eae3.
Lemma F_4ea08 : fetch_word Ubsan.M.loaded_segments (0x507f0 : word) = Some W_4ea08.
Proof. vm_refl. Qed.
Lemma D_4ea08 : decode_any W_4ea08 = Some (Branch BC_LTU 9 8 8180, 4%Z).
Proof. vm_refl. Qed.

Definition W_4ea0c : bv 32 := 0x01813083.
Lemma F_4ea0c : fetch_word Ubsan.M.loaded_segments (0x507f4 : word) = Some W_4ea0c.
Proof. vm_refl. Qed.
Lemma D_4ea0c : decode_any W_4ea0c = Some (Load SZ8 true 1 2 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_4ea10 : bv 32 := 0x01013403.
Lemma F_4ea10 : fetch_word Ubsan.M.loaded_segments (0x507f8 : word) = Some W_4ea10.
Proof. vm_refl. Qed.
Lemma D_4ea10 : decode_any W_4ea10 = Some (Load SZ8 true 8 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_4ea14 : bv 32 := 0x00813483.
Lemma F_4ea14 : fetch_word Ubsan.M.loaded_segments (0x507fc : word) = Some W_4ea14.
Proof. vm_refl. Qed.
Lemma D_4ea14 : decode_any W_4ea14 = Some (Load SZ8 true 9 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_4ea18 : bv 32 := 0x02010113.
Lemma F_4ea18 : fetch_word Ubsan.M.loaded_segments (0x50800 : word) = Some W_4ea18.
Proof. vm_refl. Qed.
Lemma D_4ea18 : decode_any W_4ea18 = Some (OpImm ALU_ADD 2 2 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_4ea1c : bv 32 := 0x00008067.
Lemma F_4ea1c : fetch_word Ubsan.M.loaded_segments (0x50804 : word) = Some W_4ea1c.
Proof. vm_refl. Qed.
Lemma D_4ea1c : decode_any W_4ea1c = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_4ea20 : bv 32 := 0xfe010113.
Lemma F_4ea20 : fetch_word Ubsan.M.loaded_segments (0x50808 : word) = Some W_4ea20.
Proof. vm_refl. Qed.
Lemma D_4ea20 : decode_any W_4ea20 = Some (OpImm ALU_ADD 2 2 4064, 4%Z).
Proof. vm_refl. Qed.

Definition W_4ea24 : bv 32 := 0x00113c23.
Lemma F_4ea24 : fetch_word Ubsan.M.loaded_segments (0x5080c : word) = Some W_4ea24.
Proof. vm_refl. Qed.
Lemma D_4ea24 : decode_any W_4ea24 = Some (Store SZ8 2 1 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_4ea28 : bv 32 := 0x00813823.
Lemma F_4ea28 : fetch_word Ubsan.M.loaded_segments (0x50810 : word) = Some W_4ea28.
Proof. vm_refl. Qed.
Lemma D_4ea28 : decode_any W_4ea28 = Some (Store SZ8 2 8 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_4ea2c : bv 32 := 0x00913423.
Lemma F_4ea2c : fetch_word Ubsan.M.loaded_segments (0x50814 : word) = Some W_4ea2c.
Proof. vm_refl. Qed.
Lemma D_4ea2c : decode_any W_4ea2c = Some (Store SZ8 2 9 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_4ea30 : bv 32 := 0x01213023.
Lemma F_4ea30 : fetch_word Ubsan.M.loaded_segments (0x50818 : word) = Some W_4ea30.
Proof. vm_refl. Qed.
Lemma D_4ea30 : decode_any W_4ea30 = Some (Store SZ8 2 18 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_4ea34 : bv 32 := 0x00060413.
Lemma F_4ea34 : fetch_word Ubsan.M.loaded_segments (0x5081c : word) = Some W_4ea34.
Proof. vm_refl. Qed.
Lemma D_4ea34 : decode_any W_4ea34 = Some (OpImm ALU_ADD 8 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_4ea38 : bv 32 := 0x00058493.
Lemma F_4ea38 : fetch_word Ubsan.M.loaded_segments (0x50820 : word) = Some W_4ea38.
Proof. vm_refl. Qed.
Lemma D_4ea38 : decode_any W_4ea38 = Some (OpImm ALU_ADD 9 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_4ea3c : bv 32 := 0x00050913.
Lemma F_4ea3c : fetch_word Ubsan.M.loaded_segments (0x50824 : word) = Some W_4ea3c.
Proof. vm_refl. Qed.
Lemma D_4ea3c : decode_any W_4ea3c = Some (OpImm ALU_ADD 18 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_4ea40 : bv 32 := 0x00063583.
Lemma F_4ea40 : fetch_word Ubsan.M.loaded_segments (0x50828 : word) = Some W_4ea40.
Proof. vm_refl. Qed.
Lemma D_4ea40 : decode_any W_4ea40 = Some (Load SZ8 true 11 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_4ea44 : bv 32 := 0x00349513.
Lemma F_4ea44 : fetch_word Ubsan.M.loaded_segments (0x5082c : word) = Some W_4ea44.
Proof. vm_refl. Qed.
Lemma D_4ea44 : decode_any W_4ea44 = Some (ShiftImm ALU_SLL 10 9 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_4ea48 : bv 32 := 0x00a60533.
Lemma F_4ea48 : fetch_word Ubsan.M.loaded_segments (0x50830 : word) = Some W_4ea48.
Proof. vm_refl. Qed.
Lemma D_4ea48 : decode_any W_4ea48 = Some (Op ALU_ADD 10 12 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_4ea4c : bv 32 := 0x00850513.
Lemma F_4ea4c : fetch_word Ubsan.M.loaded_segments (0x50834 : word) = Some W_4ea4c.
Proof. vm_refl. Qed.
Lemma D_4ea4c : decode_any W_4ea4c = Some (OpImm ALU_ADD 10 10 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_4ea50 : bv 32 := 0xd59ff0ef.
Lemma F_4ea50 : fetch_word Ubsan.M.loaded_segments (0x50838 : word) = Some W_4ea50.
Proof. vm_refl. Qed.
Lemma D_4ea50 : decode_any W_4ea50 = Some (Jal 1 2096472, 4%Z).
Proof. vm_refl. Qed.

Definition W_4ea54 : bv 32 := 0x00000517.
Lemma F_4ea54 : fetch_word Ubsan.M.loaded_segments (0x5083c : word) = Some W_4ea54.
Proof. vm_refl. Qed.
Lemma D_4ea54 : decode_any W_4ea54 = Some (Auipc 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_4ea58 : bv 32 := 0x02c50313.
Lemma F_4ea58 : fetch_word Ubsan.M.loaded_segments (0x50840 : word) = Some W_4ea58.
Proof. vm_refl. Qed.
Lemma D_4ea58 : decode_any W_4ea58 = Some (OpImm ALU_ADD 6 10 44, 4%Z).
Proof. vm_refl. Qed.

Definition W_4ea5c : bv 32 := 0x00090513.
Lemma F_4ea5c : fetch_word Ubsan.M.loaded_segments (0x50844 : word) = Some W_4ea5c.
Proof. vm_refl. Qed.
Lemma D_4ea5c : decode_any W_4ea5c = Some (OpImm ALU_ADD 10 18 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_4ea60 : bv 32 := 0x00048593.
Lemma F_4ea60 : fetch_word Ubsan.M.loaded_segments (0x50848 : word) = Some W_4ea60.
Proof. vm_refl. Qed.
Lemma D_4ea60 : decode_any W_4ea60 = Some (OpImm ALU_ADD 11 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_4ea64 : bv 32 := 0x00040613.
Lemma F_4ea64 : fetch_word Ubsan.M.loaded_segments (0x5084c : word) = Some W_4ea64.
Proof. vm_refl. Qed.
Lemma D_4ea64 : decode_any W_4ea64 = Some (OpImm ALU_ADD 12 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_4ea68 : bv 32 := 0x01813083.
Lemma F_4ea68 : fetch_word Ubsan.M.loaded_segments (0x50850 : word) = Some W_4ea68.
Proof. vm_refl. Qed.
Lemma D_4ea68 : decode_any W_4ea68 = Some (Load SZ8 true 1 2 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_4ea6c : bv 32 := 0x01013403.
Lemma F_4ea6c : fetch_word Ubsan.M.loaded_segments (0x50854 : word) = Some W_4ea6c.
Proof. vm_refl. Qed.
Lemma D_4ea6c : decode_any W_4ea6c = Some (Load SZ8 true 8 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_4ea70 : bv 32 := 0x00813483.
Lemma F_4ea70 : fetch_word Ubsan.M.loaded_segments (0x50858 : word) = Some W_4ea70.
Proof. vm_refl. Qed.
Lemma D_4ea70 : decode_any W_4ea70 = Some (Load SZ8 true 9 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_4ea74 : bv 32 := 0x00013903.
Lemma F_4ea74 : fetch_word Ubsan.M.loaded_segments (0x5085c : word) = Some W_4ea74.
Proof. vm_refl. Qed.
Lemma D_4ea74 : decode_any W_4ea74 = Some (Load SZ8 true 18 2 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_4ea78 : bv 32 := 0x02010113.
Lemma F_4ea78 : fetch_word Ubsan.M.loaded_segments (0x50860 : word) = Some W_4ea78.
Proof. vm_refl. Qed.
Lemma D_4ea78 : decode_any W_4ea78 = Some (OpImm ALU_ADD 2 2 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_4ea7c : bv 32 := 0x00030067.
Lemma F_4ea7c : fetch_word Ubsan.M.loaded_segments (0x50864 : word) = Some W_4ea7c.
Proof. vm_refl. Qed.
Lemma D_4ea7c : decode_any W_4ea7c = Some (Jalr 0 6 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_4ea80 : bv 32 := 0xfd010113.
Lemma F_4ea80 : fetch_word Ubsan.M.loaded_segments (0x50868 : word) = Some W_4ea80.
Proof. vm_refl. Qed.
Lemma D_4ea80 : decode_any W_4ea80 = Some (OpImm ALU_ADD 2 2 4048, 4%Z).
Proof. vm_refl. Qed.

Definition W_4ea84 : bv 32 := 0x02113423.
Lemma F_4ea84 : fetch_word Ubsan.M.loaded_segments (0x5086c : word) = Some W_4ea84.
Proof. vm_refl. Qed.
Lemma D_4ea84 : decode_any W_4ea84 = Some (Store SZ8 2 1 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_4ea88 : bv 32 := 0x02813023.
Lemma F_4ea88 : fetch_word Ubsan.M.loaded_segments (0x50870 : word) = Some W_4ea88.
Proof. vm_refl. Qed.
Lemma D_4ea88 : decode_any W_4ea88 = Some (Store SZ8 2 8 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_4ea8c : bv 32 := 0x00913c23.
Lemma F_4ea8c : fetch_word Ubsan.M.loaded_segments (0x50874 : word) = Some W_4ea8c.
Proof. vm_refl. Qed.
Lemma D_4ea8c : decode_any W_4ea8c = Some (Store SZ8 2 9 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_4ea90 : bv 32 := 0x01213823.
Lemma F_4ea90 : fetch_word Ubsan.M.loaded_segments (0x50878 : word) = Some W_4ea90.
Proof. vm_refl. Qed.
Lemma D_4ea90 : decode_any W_4ea90 = Some (Store SZ8 2 18 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_4ea94 : bv 32 := 0x01313423.
Lemma F_4ea94 : fetch_word Ubsan.M.loaded_segments (0x5087c : word) = Some W_4ea94.
Proof. vm_refl. Qed.
Lemma D_4ea94 : decode_any W_4ea94 = Some (Store SZ8 2 19 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_4ea98 : bv 32 := 0x00060413.
Lemma F_4ea98 : fetch_word Ubsan.M.loaded_segments (0x50880 : word) = Some W_4ea98.
Proof. vm_refl. Qed.
Lemma D_4ea98 : decode_any W_4ea98 = Some (OpImm ALU_ADD 8 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_4ea9c : bv 32 := 0x00058493.
Lemma F_4ea9c : fetch_word Ubsan.M.loaded_segments (0x50884 : word) = Some W_4ea9c.
Proof. vm_refl. Qed.
Lemma D_4ea9c : decode_any W_4ea9c = Some (OpImm ALU_ADD 9 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_4eaa0 : bv 32 := 0x00050913.
Lemma F_4eaa0 : fetch_word Ubsan.M.loaded_segments (0x50888 : word) = Some W_4eaa0.
Proof. vm_refl. Qed.
Lemma D_4eaa0 : decode_any W_4eaa0 = Some (OpImm ALU_ADD 18 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_4eaa4 : bv 32 := 0x00359513.
Lemma F_4eaa4 : fetch_word Ubsan.M.loaded_segments (0x5088c : word) = Some W_4eaa4.
Proof. vm_refl. Qed.
Lemma D_4eaa4 : decode_any W_4eaa4 = Some (ShiftImm ALU_SLL 10 11 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_4eaa8 : bv 32 := 0x00a60533.
Lemma F_4eaa8 : fetch_word Ubsan.M.loaded_segments (0x50890 : word) = Some W_4eaa8.
Proof. vm_refl. Qed.
Lemma D_4eaa8 : decode_any W_4eaa8 = Some (Op ALU_ADD 10 12 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_4eaac : bv 32 := 0x00850993.
Lemma F_4eaac : fetch_word Ubsan.M.loaded_segments (0x50894 : word) = Some W_4eaac.
Proof. vm_refl. Qed.
Lemma D_4eaac : decode_any W_4eaac = Some (OpImm ALU_ADD 19 10 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_4eab0 : bv 32 := 0xf25ff0ef.
Lemma F_4eab0 : fetch_word Ubsan.M.loaded_segments (0x50898 : word) = Some W_4eab0.
Proof. vm_refl. Qed.
Lemma D_4eab0 : decode_any W_4eab0 = Some (Jal 1 2096932, 4%Z).
Proof. vm_refl. Qed.

Definition W_4eab4 : bv 32 := 0x00048513.
Lemma F_4eab4 : fetch_word Ubsan.M.loaded_segments (0x5089c : word) = Some W_4eab4.
Proof. vm_refl. Qed.
Lemma D_4eab4 : decode_any W_4eab4 = Some (OpImm ALU_ADD 10 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_4eab8 : bv 32 := 0x00040593.
Lemma F_4eab8 : fetch_word Ubsan.M.loaded_segments (0x508a0 : word) = Some W_4eab8.
Proof. vm_refl. Qed.
Lemma D_4eab8 : decode_any W_4eab8 = Some (OpImm ALU_ADD 11 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_4eabc : bv 32 := 0x00098613.
Lemma F_4eabc : fetch_word Ubsan.M.loaded_segments (0x508a4 : word) = Some W_4eabc.
Proof. vm_refl. Qed.
Lemma D_4eabc : decode_any W_4eabc = Some (OpImm ALU_ADD 12 19 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_4eac0 : bv 32 := 0x000900e7.
Lemma F_4eac0 : fetch_word Ubsan.M.loaded_segments (0x508a8 : word) = Some W_4eac0.
Proof. vm_refl. Qed.
Lemma D_4eac0 : decode_any W_4eac0 = Some (Jalr 1 18 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_4eac4 : bv 32 := 0x5c0000ef.
Lemma F_4eac4 : fetch_word Ubsan.M.loaded_segments (0x508ac : word) = Some W_4eac4.
Proof. vm_refl. Qed.
Lemma D_4eac4 : decode_any W_4eac4 = Some (Jal 1 1472, 4%Z).
Proof. vm_refl. Qed.

Definition W_4eb28 : bv 32 := 0xfc010113.
Lemma F_4eb28 : fetch_word Ubsan.M.loaded_segments (0x508b0 : word) = Some W_4eb28.
Proof. vm_refl. Qed.
Lemma D_4eb28 : decode_any W_4eb28 = Some (OpImm ALU_ADD 2 2 4032, 4%Z).
Proof. vm_refl. Qed.

Definition W_4eb2c : bv 32 := 0x02113c23.
Lemma F_4eb2c : fetch_word Ubsan.M.loaded_segments (0x508b4 : word) = Some W_4eb2c.
Proof. vm_refl. Qed.
Lemma D_4eb2c : decode_any W_4eb2c = Some (Store SZ8 2 1 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_4eb30 : bv 32 := 0x02813823.
Lemma F_4eb30 : fetch_word Ubsan.M.loaded_segments (0x508b8 : word) = Some W_4eb30.
Proof. vm_refl. Qed.
Lemma D_4eb30 : decode_any W_4eb30 = Some (Store SZ8 2 8 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_4eb34 : bv 32 := 0x02913423.
Lemma F_4eb34 : fetch_word Ubsan.M.loaded_segments (0x508bc : word) = Some W_4eb34.
Proof. vm_refl. Qed.
Lemma D_4eb34 : decode_any W_4eb34 = Some (Store SZ8 2 9 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_4eb38 : bv 32 := 0x03213023.
Lemma F_4eb38 : fetch_word Ubsan.M.loaded_segments (0x508c0 : word) = Some W_4eb38.
Proof. vm_refl. Qed.
Lemma D_4eb38 : decode_any W_4eb38 = Some (Store SZ8 2 18 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_4eb3c : bv 32 := 0x01313c23.
Lemma F_4eb3c : fetch_word Ubsan.M.loaded_segments (0x508c4 : word) = Some W_4eb3c.
Proof. vm_refl. Qed.
Lemma D_4eb3c : decode_any W_4eb3c = Some (Store SZ8 2 19 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_4eb40 : bv 32 := 0x01413823.
Lemma F_4eb40 : fetch_word Ubsan.M.loaded_segments (0x508c8 : word) = Some W_4eb40.
Proof. vm_refl. Qed.
Lemma D_4eb40 : decode_any W_4eb40 = Some (Store SZ8 2 20 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_4eb44 : bv 32 := 0x01513423.
Lemma F_4eb44 : fetch_word Ubsan.M.loaded_segments (0x508cc : word) = Some W_4eb44.
Proof. vm_refl. Qed.
Lemma D_4eb44 : decode_any W_4eb44 = Some (Store SZ8 2 21 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_4eb48 : bv 32 := 0x02853683.
Lemma F_4eb48 : fetch_word Ubsan.M.loaded_segments (0x508d0 : word) = Some W_4eb48.
Proof. vm_refl. Qed.
Lemma D_4eb48 : decode_any W_4eb48 = Some (Load SZ8 true 13 10 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_4eb4c : bv 32 := 0x00047597.
Lemma F_4eb4c : fetch_word Ubsan.M.loaded_segments (0x508d4 : word) = Some W_4eb4c.
Proof. vm_refl. Qed.
Lemma D_4eb4c : decode_any W_4eb4c = Some (Auipc 11 71, 4%Z).
Proof. vm_refl. Qed.

Definition W_4eb50 : bv 32 := 0x33458593.
Lemma F_4eb50 : fetch_word Ubsan.M.loaded_segments (0x508d8 : word) = Some W_4eb50.
Proof. vm_refl. Qed.
Lemma D_4eb50 : decode_any W_4eb50 = Some (OpImm ALU_ADD 11 11 820, 4%Z).
Proof. vm_refl. Qed.

Definition W_4eb54 : bv 32 := 0x00047617.
Lemma F_4eb54 : fetch_word Ubsan.M.loaded_segments (0x508dc : word) = Some W_4eb54.
Proof. vm_refl. Qed.
Lemma D_4eb54 : decode_any W_4eb54 = Some (Auipc 12 71, 4%Z).
Proof. vm_refl. Qed.

Definition W_4eb58 : bv 32 := 0x5b460493.
Lemma F_4eb58 : fetch_word Ubsan.M.loaded_segments (0x508e0 : word) = Some W_4eb58.
Proof. vm_refl. Qed.
Lemma D_4eb58 : decode_any W_4eb58 = Some (OpImm ALU_ADD 9 12 1460, 4%Z).
Proof. vm_refl. Qed.

Definition W_4eb5c : bv 32 := 0x0c068e63.
Lemma F_4eb5c : fetch_word Ubsan.M.loaded_segments (0x508e4 : word) = Some W_4eb5c.
Proof. vm_refl. Qed.
Lemma D_4eb5c : decode_any W_4eb5c = Some (Branch BC_EQ 13 0 220, 4%Z).
Proof. vm_refl. Qed.

Definition W_4eb60 : bv 32 := 0x00000613.
Lemma F_4eb60 : fetch_word Ubsan.M.loaded_segments (0x508e8 : word) = Some W_4eb60.
Proof. vm_refl. Qed.
Lemma D_4eb60 : decode_any W_4eb60 = Some (OpImm ALU_ADD 12 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_4eb64 : bv 32 := 0x00000893.
Lemma F_4eb64 : fetch_word Ubsan.M.loaded_segments (0x508ec : word) = Some W_4eb64.
Proof. vm_refl. Qed.
Lemma D_4eb64 : decode_any W_4eb64 = Some (OpImm ALU_ADD 17 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_4eb68 : bv 32 := 0x00016717.
Lemma F_4eb68 : fetch_word Ubsan.M.loaded_segments (0x508f0 : word) = Some W_4eb68.
Proof. vm_refl. Qed.
Lemma D_4eb68 : decode_any W_4eb68 = Some (Auipc 14 22, 4%Z).
Proof. vm_refl. Qed.

Definition W_4eb6c : bv 32 := 0x01853783.
Lemma F_4eb6c : fetch_word Ubsan.M.loaded_segments (0x508f4 : word) = Some W_4eb6c.
Proof. vm_refl. Qed.
Lemma D_4eb6c : decode_any W_4eb6c = Some (Load SZ8 true 15 10 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_4eb70 : bv 32 := 0x02053503.
Lemma F_4eb70 : fetch_word Ubsan.M.loaded_segments (0x508f8 : word) = Some W_4eb70.
Proof. vm_refl. Qed.
Lemma D_4eb70 : decode_any W_4eb70 = Some (Load SZ8 true 10 10 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_4eb74 : bv 32 := 0x00600813.
Lemma F_4eb74 : fetch_word Ubsan.M.loaded_segments (0x508fc : word) = Some W_4eb74.
Proof. vm_refl. Qed.
Lemma D_4eb74 : decode_any W_4eb74 = Some (OpImm ALU_ADD 16 0 6, 4%Z).
Proof. vm_refl. Qed.

Definition W_4eb78 : bv 32 := 0x00015297.
Lemma F_4eb78 : fetch_word Ubsan.M.loaded_segments (0x50900 : word) = Some W_4eb78.
Proof. vm_refl. Qed.
Lemma D_4eb78 : decode_any W_4eb78 = Some (Auipc 5 21, 4%Z).
Proof. vm_refl. Qed.

Definition W_4eb7c : bv 32 := 0x62876f03.
Lemma F_4eb7c : fetch_word Ubsan.M.loaded_segments (0x50904 : word) = Some W_4eb7c.
Proof. vm_refl. Qed.
Lemma D_4eb7c : decode_any W_4eb7c = Some (Load SZ4 false 30 14 1576, 4%Z).
Proof. vm_refl. Qed.

Definition W_4eb80 : bv 32 := 0xf702b283.
Lemma F_4eb80 : fetch_word Ubsan.M.loaded_segments (0x50908 : word) = Some W_4eb80.
Proof. vm_refl. Qed.
Lemma D_4eb80 : decode_any W_4eb80 = Some (Load SZ8 true 5 5 3952, 4%Z).
Proof. vm_refl. Qed.

Definition W_4eb84 : bv 32 := 0x00200313.
Lemma F_4eb84 : fetch_word Ubsan.M.loaded_segments (0x5090c : word) = Some W_4eb84.
Proof. vm_refl. Qed.
Lemma D_4eb84 : decode_any W_4eb84 = Some (OpImm ALU_ADD 6 0 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_4eb88 : bv 32 := 0x00700393.
Lemma F_4eb88 : fetch_word Ubsan.M.loaded_segments (0x50910 : word) = Some W_4eb88.
Proof. vm_refl. Qed.
Lemma D_4eb88 : decode_any W_4eb88 = Some (OpImm ALU_ADD 7 0 7, 4%Z).
Proof. vm_refl. Qed.

Definition W_4eb8c : bv 32 := 0x6474ee37.
Lemma F_4eb8c : fetch_word Ubsan.M.loaded_segments (0x50914 : word) = Some W_4eb8c.
Proof. vm_refl. Qed.
Lemma D_4eb8c : decode_any W_4eb8c = Some (Lui 28 411470, 4%Z).
Proof. vm_refl. Qed.

Definition W_4eb90 : bv 32 := 0x551e0e1b.
Lemma F_4eb90 : fetch_word Ubsan.M.loaded_segments (0x50918 : word) = Some W_4eb90.
Proof. vm_refl. Qed.
Lemma D_4eb90 : decode_any W_4eb90 = Some (OpImm32 28 28 1361, 4%Z).
Proof. vm_refl. Qed.

Definition W_4eb94 : bv 32 := 0x00078e93.
Lemma F_4eb94 : fetch_word Ubsan.M.loaded_segments (0x5091c : word) = Some W_4eb94.
Proof. vm_refl. Qed.
Lemma D_4eb94 : decode_any W_4eb94 = Some (OpImm ALU_ADD 29 15 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_4eb98 : bv 32 := 0x0180006f.
Lemma F_4eb98 : fetch_word Ubsan.M.loaded_segments (0x50920 : word) = Some W_4eb98.
Proof. vm_refl. Qed.
Lemma D_4eb98 : decode_any W_4eb98 = Some (Jal 0 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_4eb9c : bv 32 := 0x010eb603.
Lemma F_4eb9c : fetch_word Ubsan.M.loaded_segments (0x50924 : word) = Some W_4eb9c.
Proof. vm_refl. Qed.
Lemma D_4eb9c : decode_any W_4eb9c = Some (Load SZ8 true 12 29 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_4eba0 : bv 32 := 0x40c78633.
Lemma F_4eba0 : fetch_word Ubsan.M.loaded_segments (0x50928 : word) = Some W_4eba0.
Proof. vm_refl. Qed.
Lemma D_4eba0 : decode_any W_4eba0 = Some (Op ALU_SUB 12 15 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_4eba4 : bv 32 := 0xfff68693.
Lemma F_4eba4 : fetch_word Ubsan.M.loaded_segments (0x5092c : word) = Some W_4eba4.
Proof. vm_refl. Qed.
Lemma D_4eba4 : decode_any W_4eba4 = Some (OpImm ALU_ADD 13 13 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_4eba8 : bv 32 := 0x00ae8eb3.
Lemma F_4eba8 : fetch_word Ubsan.M.loaded_segments (0x50930 : word) = Some W_4eba8.
Proof. vm_refl. Qed.
Lemma D_4eba8 : decode_any W_4eba8 = Some (Op ALU_ADD 29 29 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_4ebac : bv 32 := 0x04068a63.
Lemma F_4ebac : fetch_word Ubsan.M.loaded_segments (0x50934 : word) = Some W_4ebac.
Proof. vm_refl. Qed.
Lemma D_4ebac : decode_any W_4ebac = Some (Branch BC_EQ 13 0 84, 4%Z).
Proof. vm_refl. Qed.

Definition W_4ebb0 : bv 32 := 0x000ea403.
Lemma F_4ebb0 : fetch_word Ubsan.M.loaded_segments (0x50938 : word) = Some W_4ebb0.
Proof. vm_refl. Qed.
Lemma D_4ebb0 : decode_any W_4ebb0 = Some (Load SZ4 true 8 29 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_4ebb4 : bv 32 := 0xff0404e3.
Lemma F_4ebb4 : fetch_word Ubsan.M.loaded_segments (0x5093c : word) = Some W_4ebb4.
Proof. vm_refl. Qed.
Lemma D_4ebb4 : decode_any W_4ebb4 = Some (Branch BC_EQ 8 16 8168, 4%Z).
Proof. vm_refl. Qed.

Definition W_4ebb8 : bv 32 := 0x00028a63.
Lemma F_4ebb8 : fetch_word Ubsan.M.loaded_segments (0x50940 : word) = Some W_4ebb8.
Proof. vm_refl. Qed.
Lemma D_4ebb8 : decode_any W_4ebb8 = Some (Branch BC_EQ 5 0 20, 4%Z).
Proof. vm_refl. Qed.

Definition W_4ebcc : bv 32 := 0x000e8f93.
Lemma F_4ebcc : fetch_word Ubsan.M.loaded_segments (0x50954 : word) = Some W_4ebcc.
Proof. vm_refl. Qed.
Lemma D_4ebcc : decode_any W_4ebcc = Some (OpImm ALU_ADD 31 29 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_4ebd0 : bv 32 := 0x00740463.
Lemma F_4ebd0 : fetch_word Ubsan.M.loaded_segments (0x50958 : word) = Some W_4ebd0.
Proof. vm_refl. Qed.
Lemma D_4ebd0 : decode_any W_4ebd0 = Some (Branch BC_EQ 8 7 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_4ebd4 : bv 32 := 0x00088f93.
Lemma F_4ebd4 : fetch_word Ubsan.M.loaded_segments (0x5095c : word) = Some W_4ebd4.
Proof. vm_refl. Qed.
Lemma D_4ebd4 : decode_any W_4ebd4 = Some (OpImm ALU_ADD 31 17 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_4ebd8 : bv 32 := 0x03c41063.
Lemma F_4ebd8 : fetch_word Ubsan.M.loaded_segments (0x50960 : word) = Some W_4ebd8.
Proof. vm_refl. Qed.
Lemma D_4ebd8 : decode_any W_4ebd8 = Some (Branch BC_NE 8 28 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_4ebdc : bv 32 := 0x028eb883.
Lemma F_4ebdc : fetch_word Ubsan.M.loaded_segments (0x50964 : word) = Some W_4ebdc.
Proof. vm_refl. Qed.
Lemma D_4ebdc : decode_any W_4ebdc = Some (Load SZ8 true 17 29 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_4ebe0 : bv 32 := 0x011f7c63.
Lemma F_4ebe0 : fetch_word Ubsan.M.loaded_segments (0x50968 : word) = Some W_4ebe0.
Proof. vm_refl. Qed.
Lemma D_4ebe0 : decode_any W_4ebe0 = Some (Branch BC_GEU 30 17 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_4ebf8 : bv 32 := 0x000f8893.
Lemma F_4ebf8 : fetch_word Ubsan.M.loaded_segments (0x50980 : word) = Some W_4ebf8.
Proof. vm_refl. Qed.
Lemma D_4ebf8 : decode_any W_4ebf8 = Some (OpImm ALU_ADD 17 31 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_4ebfc : bv 32 := 0xfa9ff06f.
Lemma F_4ebfc : fetch_word Ubsan.M.loaded_segments (0x50984 : word) = Some W_4ebfc.
Proof. vm_refl. Qed.
Lemma D_4ebfc : decode_any W_4ebfc = Some (Jal 0 2097064, 4%Z).
Proof. vm_refl. Qed.

Definition W_4ec00 : bv 32 := 0x02088c63.
Lemma F_4ec00 : fetch_word Ubsan.M.loaded_segments (0x50988 : word) = Some W_4ec00.
Proof. vm_refl. Qed.
Lemma D_4ec00 : decode_any W_4ec00 = Some (Branch BC_EQ 17 0 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_4ec04 : bv 32 := 0x00858713.
Lemma F_4ec04 : fetch_word Ubsan.M.loaded_segments (0x5098c : word) = Some W_4ec04.
Proof. vm_refl. Qed.
Lemma D_4ec04 : decode_any W_4ec04 = Some (OpImm ALU_ADD 14 11 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_4ec08 : bv 32 := 0x0108b783.
Lemma F_4ec08 : fetch_word Ubsan.M.loaded_segments (0x50990 : word) = Some W_4ec08.
Proof. vm_refl. Qed.
Lemma D_4ec08 : decode_any W_4ec08 = Some (Load SZ8 true 15 17 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_4ec0c : bv 32 := 0x0208b803.
Lemma F_4ec0c : fetch_word Ubsan.M.loaded_segments (0x50994 : word) = Some W_4ec0c.
Proof. vm_refl. Qed.
Lemma D_4ec0c : decode_any W_4ec0c = Some (Load SZ8 true 16 17 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_4ec10 : bv 32 := 0x0288b683.
Lemma F_4ec10 : fetch_word Ubsan.M.loaded_segments (0x50998 : word) = Some W_4ec10.
Proof. vm_refl. Qed.
Lemma D_4ec10 : decode_any W_4ec10 = Some (Load SZ8 true 13 17 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_4ec14 : bv 32 := 0x0308b503.
Lemma F_4ec14 : fetch_word Ubsan.M.loaded_segments (0x5099c : word) = Some W_4ec14.
Proof. vm_refl. Qed.
Lemma D_4ec14 : decode_any W_4ec14 = Some (Load SZ8 true 10 17 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_4ec18 : bv 32 := 0x00c78633.
Lemma F_4ec18 : fetch_word Ubsan.M.loaded_segments (0x509a0 : word) = Some W_4ec18.
Proof. vm_refl. Qed.
Lemma D_4ec18 : decode_any W_4ec18 = Some (Op ALU_ADD 12 15 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_4ec1c : bv 32 := 0x00100793.
Lemma F_4ec1c : fetch_word Ubsan.M.loaded_segments (0x509a4 : word) = Some W_4ec1c.
Proof. vm_refl. Qed.
Lemma D_4ec1c : decode_any W_4ec1c = Some (OpImm ALU_ADD 15 0 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_4ec20 : bv 32 := 0x00c5b823.
Lemma F_4ec20 : fetch_word Ubsan.M.loaded_segments (0x509a8 : word) = Some W_4ec20.
Proof. vm_refl. Qed.
Lemma D_4ec20 : decode_any W_4ec20 = Some (Store SZ8 11 12 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_4ec24 : bv 32 := 0x0105bc23.
Lemma F_4ec24 : fetch_word Ubsan.M.loaded_segments (0x509ac : word) = Some W_4ec24.
Proof. vm_refl. Qed.
Lemma D_4ec24 : decode_any W_4ec24 = Some (Store SZ8 11 16 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_4ec28 : bv 32 := 0x02a5b423.
Lemma F_4ec28 : fetch_word Ubsan.M.loaded_segments (0x509b0 : word) = Some W_4ec28.
Proof. vm_refl. Qed.
Lemma D_4ec28 : decode_any W_4ec28 = Some (Store SZ8 11 10 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_4ec2c : bv 32 := 0x00e4b823.
Lemma F_4ec2c : fetch_word Ubsan.M.loaded_segments (0x509b4 : word) = Some W_4ec2c.
Proof. vm_refl. Qed.
Lemma D_4ec2c : decode_any W_4ec2c = Some (Store SZ8 9 14 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_4ec30 : bv 32 := 0x02f4b423.
Lemma F_4ec30 : fetch_word Ubsan.M.loaded_segments (0x509b8 : word) = Some W_4ec30.
Proof. vm_refl. Qed.
Lemma D_4ec30 : decode_any W_4ec30 = Some (Store SZ8 9 15 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_4ec34 : bv 32 := 0x0100006f.
Lemma F_4ec34 : fetch_word Ubsan.M.loaded_segments (0x509bc : word) = Some W_4ec34.
Proof. vm_refl. Qed.
Lemma D_4ec34 : decode_any W_4ec34 = Some (Jal 0 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_4ec44 : bv 32 := 0x00c68733.
Lemma F_4ec44 : fetch_word Ubsan.M.loaded_segments (0x509cc : word) = Some W_4ec44.
Proof. vm_refl. Qed.
Lemma D_4ec44 : decode_any W_4ec44 = Some (Op ALU_ADD 14 13 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_4ec48 : bv 32 := 0xfff50793.
Lemma F_4ec48 : fetch_word Ubsan.M.loaded_segments (0x509d0 : word) = Some W_4ec48.
Proof. vm_refl. Qed.
Lemma D_4ec48 : decode_any W_4ec48 = Some (OpImm ALU_ADD 15 10 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_4ec4c : bv 32 := 0x40e00733.
Lemma F_4ec4c : fetch_word Ubsan.M.loaded_segments (0x509d4 : word) = Some W_4ec4c.
Proof. vm_refl. Qed.
Lemma D_4ec4c : decode_any W_4ec4c = Some (Op ALU_SUB 14 0 14, 4%Z).
Proof. vm_refl. Qed.

Definition W_4ec50 : bv 32 := 0x00c7f633.
Lemma F_4ec50 : fetch_word Ubsan.M.loaded_segments (0x509d8 : word) = Some W_4ec50.
Proof. vm_refl. Qed.
Lemma D_4ec50 : decode_any W_4ec50 = Some (Op ALU_AND 12 15 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_4ec54 : bv 32 := 0x00e7f733.
Lemma F_4ec54 : fetch_word Ubsan.M.loaded_segments (0x509dc : word) = Some W_4ec54.
Proof. vm_refl. Qed.
Lemma D_4ec54 : decode_any W_4ec54 = Some (Op ALU_AND 14 15 14, 4%Z).
Proof. vm_refl. Qed.

Definition W_4ec58 : bv 32 := 0x00700793.
Lemma F_4ec58 : fetch_word Ubsan.M.loaded_segments (0x509e0 : word) = Some W_4ec58.
Proof. vm_refl. Qed.
Lemma D_4ec58 : decode_any W_4ec58 = Some (OpImm ALU_ADD 15 0 7, 4%Z).
Proof. vm_refl. Qed.

Definition W_4ec5c : bv 32 := 0x00d706b3.
Lemma F_4ec5c : fetch_word Ubsan.M.loaded_segments (0x509e4 : word) = Some W_4ec5c.
Proof. vm_refl. Qed.
Lemma D_4ec5c : decode_any W_4ec5c = Some (Op ALU_ADD 13 14 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_4ec60 : bv 32 := 0x02d5b023.
Lemma F_4ec60 : fetch_word Ubsan.M.loaded_segments (0x509e8 : word) = Some W_4ec60.
Proof. vm_refl. Qed.
Lemma D_4ec60 : decode_any W_4ec60 = Some (Store SZ8 11 13 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_4ec64 : bv 32 := 0x02c5b823.
Lemma F_4ec64 : fetch_word Ubsan.M.loaded_segments (0x509ec : word) = Some W_4ec64.
Proof. vm_refl. Qed.
Lemma D_4ec64 : decode_any W_4ec64 = Some (Store SZ8 11 12 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_4ec68 : bv 32 := 0x00a7e663.
Lemma F_4ec68 : fetch_word Ubsan.M.loaded_segments (0x509f0 : word) = Some W_4ec68.
Proof. vm_refl. Qed.
Lemma D_4ec68 : decode_any W_4ec68 = Some (Branch BC_LTU 15 10 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_4ec74 : bv 32 := 0x00d60633.
Lemma F_4ec74 : fetch_word Ubsan.M.loaded_segments (0x509fc : word) = Some W_4ec74.
Proof. vm_refl. Qed.
Lemma D_4ec74 : decode_any W_4ec74 = Some (Op ALU_ADD 12 12 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_4ec78 : bv 32 := 0x000205b7.
Lemma F_4ec78 : fetch_word Ubsan.M.loaded_segments (0x50a00 : word) = Some W_4ec78.
Proof. vm_refl. Qed.
Lemma D_4ec78 : decode_any W_4ec78 = Some (Lui 11 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_4ec7c : bv 32 := 0x00a60633.
Lemma F_4ec7c : fetch_word Ubsan.M.loaded_segments (0x50a04 : word) = Some W_4ec7c.
Proof. vm_refl. Qed.
Lemma D_4ec7c : decode_any W_4ec7c = Some (Op ALU_ADD 12 12 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_4ec80 : bv 32 := 0x0d15869b.
Lemma F_4ec80 : fetch_word Ubsan.M.loaded_segments (0x50a08 : word) = Some W_4ec80.
Proof. vm_refl. Qed.
Lemma D_4ec80 : decode_any W_4ec80 = Some (OpImm32 13 11 209, 4%Z).
Proof. vm_refl. Qed.

Definition W_4ec84 : bv 32 := 0x0df60593.
Lemma F_4ec84 : fetch_word Ubsan.M.loaded_segments (0x50a0c : word) = Some W_4ec84.
Proof. vm_refl. Qed.
Lemma D_4ec84 : decode_any W_4ec84 = Some (OpImm ALU_ADD 11 12 223, 4%Z).
Proof. vm_refl. Qed.

Definition W_4ec88 : bv 32 := 0xff85f593.
Lemma F_4ec88 : fetch_word Ubsan.M.loaded_segments (0x50a10 : word) = Some W_4ec88.
Proof. vm_refl. Qed.
Lemma D_4ec88 : decode_any W_4ec88 = Some (OpImm ALU_AND 11 11 4088, 4%Z).
Proof. vm_refl. Qed.

Definition W_4ec8c : bv 32 := 0x00b4bc23.
Lemma F_4ec8c : fetch_word Ubsan.M.loaded_segments (0x50a14 : word) = Some W_4ec8c.
Proof. vm_refl. Qed.
Lemma D_4ec8c : decode_any W_4ec8c = Some (Store SZ8 9 11 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_4ec90 : bv 32 := 0x02a4b023.
Lemma F_4ec90 : fetch_word Ubsan.M.loaded_segments (0x50a18 : word) = Some W_4ec90.
Proof. vm_refl. Qed.
Lemma D_4ec90 : decode_any W_4ec90 = Some (Store SZ8 9 10 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_4ec94 : bv 32 := 0x02d5ea63.
Lemma F_4ec94 : fetch_word Ubsan.M.loaded_segments (0x50a1c : word) = Some W_4ec94.
Proof. vm_refl. Qed.
Lemma D_4ec94 : decode_any W_4ec94 = Some (Branch BC_LTU 11 13 52, 4%Z).
Proof. vm_refl. Qed.

Definition W_4ecc8 : bv 32 := 0x00027697.
Lemma F_4ecc8 : fetch_word Ubsan.M.loaded_segments (0x50a50 : word) = Some W_4ecc8.
Proof. vm_refl. Qed.
Lemma D_4ecc8 : decode_any W_4ecc8 = Some (Auipc 13 39, 4%Z).
Proof. vm_refl. Qed.

Definition W_4eccc : bv 32 := 0x0104b983.
Lemma F_4eccc : fetch_word Ubsan.M.loaded_segments (0x50a54 : word) = Some W_4eccc.
Proof. vm_refl. Qed.
Lemma D_4eccc : decode_any W_4eccc = Some (Load SZ8 true 19 9 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_4ecd0 : bv 32 := 0x0284b603.
Lemma F_4ecd0 : fetch_word Ubsan.M.loaded_segments (0x50a58 : word) = Some W_4ecd0.
Proof. vm_refl. Qed.
Lemma D_4ecd0 : decode_any W_4ecd0 = Some (Load SZ8 true 12 9 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_4ecd4 : bv 32 := 0xfff50713.
Lemma F_4ecd4 : fetch_word Ubsan.M.loaded_segments (0x50a5c : word) = Some W_4ecd4.
Proof. vm_refl. Qed.
Lemma D_4ecd4 : decode_any W_4ecd4 = Some (OpImm ALU_ADD 14 10 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_4ecd8 : bv 32 := 0xf3800793.
Lemma F_4ecd8 : fetch_word Ubsan.M.loaded_segments (0x50a60 : word) = Some W_4ecd8.
Proof. vm_refl. Qed.
Lemma D_4ecd8 : decode_any W_4ecd8 = Some (OpImm ALU_ADD 15 0 3896, 4%Z).
Proof. vm_refl. Qed.

Definition W_4ecdc : bv 32 := 0x0e868513.
Lemma F_4ecdc : fetch_word Ubsan.M.loaded_segments (0x50a64 : word) = Some W_4ecdc.
Proof. vm_refl. Qed.
Lemma D_4ecdc : decode_any W_4ecdc = Some (OpImm ALU_ADD 10 13 232, 4%Z).
Proof. vm_refl. Qed.

Definition W_4ece0 : bv 32 := 0x40a787b3.
Lemma F_4ece0 : fetch_word Ubsan.M.loaded_segments (0x50a68 : word) = Some W_4ece0.
Proof. vm_refl. Qed.
Lemma D_4ece0 : decode_any W_4ece0 = Some (Op ALU_SUB 15 15 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_4ece4 : bv 32 := 0x00f77733.
Lemma F_4ece4 : fetch_word Ubsan.M.loaded_segments (0x50a6c : word) = Some W_4ece4.
Proof. vm_refl. Qed.
Lemma D_4ece4 : decode_any W_4ece4 = Some (Op ALU_AND 14 14 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_4ece8 : bv 32 := 0xfff64693.
Lemma F_4ece8 : fetch_word Ubsan.M.loaded_segments (0x50a70 : word) = Some W_4ece8.
Proof. vm_refl. Qed.
Lemma D_4ece8 : decode_any W_4ece8 = Some (OpImm ALU_XOR 13 12 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_4ecec : bv 32 := 0x00e50933.
Lemma F_4ecec : fetch_word Ubsan.M.loaded_segments (0x50a74 : word) = Some W_4ecec.
Proof. vm_refl. Qed.
Lemma D_4ecec : decode_any W_4ecec = Some (Op ALU_ADD 18 10 14, 4%Z).
Proof. vm_refl. Qed.

Definition W_4ecf0 : bv 32 := 0x00369693.
Lemma F_4ecf0 : fetch_word Ubsan.M.loaded_segments (0x50a78 : word) = Some W_4ecf0.
Proof. vm_refl. Qed.
Lemma D_4ecf0 : decode_any W_4ecf0 = Some (ShiftImm ALU_SLL 13 13 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_4ecf4 : bv 32 := 0x00d506b3.
Lemma F_4ecf4 : fetch_word Ubsan.M.loaded_segments (0x50a7c : word) = Some W_4ecf4.
Proof. vm_refl. Qed.
Lemma D_4ecf4 : decode_any W_4ecf4 = Some (Op ALU_ADD 13 10 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_4ecf8 : bv 32 := 0x00b68a33.
Lemma F_4ecf8 : fetch_word Ubsan.M.loaded_segments (0x50a80 : word) = Some W_4ecf8.
Proof. vm_refl. Qed.
Lemma D_4ecf8 : decode_any W_4ecf8 = Some (Op ALU_ADD 20 13 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_4ecfc : bv 32 := 0x0c890413.
Lemma F_4ecfc : fetch_word Ubsan.M.loaded_segments (0x50a84 : word) = Some W_4ecfc.
Proof. vm_refl. Qed.
Lemma D_4ecfc : decode_any W_4ecfc = Some (OpImm ALU_ADD 8 18 200, 4%Z).
Proof. vm_refl. Qed.

Definition W_4ed00 : bv 32 := 0x04098463.
Lemma F_4ed00 : fetch_word Ubsan.M.loaded_segments (0x50a88 : word) = Some W_4ed00.
Proof. vm_refl. Qed.
Lemma D_4ed00 : decode_any W_4ed00 = Some (Branch BC_EQ 19 0 72, 4%Z).
Proof. vm_refl. Qed.

Definition W_4ed04 : bv 32 := 0x00361613.
Lemma F_4ed04 : fetch_word Ubsan.M.loaded_segments (0x50a8c : word) = Some W_4ed04.
Proof. vm_refl. Qed.
Lemma D_4ed04 : decode_any W_4ed04 = Some (ShiftImm ALU_SLL 12 12 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_4ed08 : bv 32 := 0x40c50533.
Lemma F_4ed08 : fetch_word Ubsan.M.loaded_segments (0x50a90 : word) = Some W_4ed08.
Proof. vm_refl. Qed.
Lemma D_4ed08 : decode_any W_4ed08 = Some (Op ALU_SUB 10 10 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_4ed0c : bv 32 := 0x00b50ab3.
Lemma F_4ed0c : fetch_word Ubsan.M.loaded_segments (0x50a94 : word) = Some W_4ed0c.
Proof. vm_refl. Qed.
Lemma D_4ed0c : decode_any W_4ed0c = Some (Op ALU_ADD 21 10 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_4ed10 : bv 32 := 0x0289b503.
Lemma F_4ed10 : fetch_word Ubsan.M.loaded_segments (0x50a98 : word) = Some W_4ed10.
Proof. vm_refl. Qed.
Lemma D_4ed10 : decode_any W_4ed10 = Some (Load SZ8 true 10 19 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_4ed14 : bv 32 := 0x00a40533.
Lemma F_4ed14 : fetch_word Ubsan.M.loaded_segments (0x50a9c : word) = Some W_4ed14.
Proof. vm_refl. Qed.
Lemma D_4ed14 : decode_any W_4ed14 = Some (Op ALU_ADD 10 8 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_4ed18 : bv 32 := 0x7ff50513.
Lemma F_4ed18 : fetch_word Ubsan.M.loaded_segments (0x50aa0 : word) = Some W_4ed18.
Proof. vm_refl. Qed.
Lemma D_4ed18 : decode_any W_4ed18 = Some (OpImm ALU_ADD 10 10 2047, 4%Z).
Proof. vm_refl. Qed.

Definition W_4ed1c : bv 32 := 0x00150513.
Lemma F_4ed1c : fetch_word Ubsan.M.loaded_segments (0x50aa4 : word) = Some W_4ed1c.
Proof. vm_refl. Qed.
Lemma D_4ed1c : decode_any W_4ed1c = Some (OpImm ALU_ADD 10 10 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_4ed20 : bv 32 := 0x00aab023.
Lemma F_4ed20 : fetch_word Ubsan.M.loaded_segments (0x50aa8 : word) = Some W_4ed20.
Proof. vm_refl. Qed.
Lemma D_4ed20 : decode_any W_4ed20 = Some (Store SZ8 21 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_4ed24 : bv 32 := 0x0289b503.
Lemma F_4ed24 : fetch_word Ubsan.M.loaded_segments (0x50aac : word) = Some W_4ed24.
Proof. vm_refl. Qed.
Lemma D_4ed24 : decode_any W_4ed24 = Some (Load SZ8 true 10 19 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_4ed28 : bv 32 := 0x0089b583.
Lemma F_4ed28 : fetch_word Ubsan.M.loaded_segments (0x50ab0 : word) = Some W_4ed28.
Proof. vm_refl. Qed.
Lemma D_4ed28 : decode_any W_4ed28 = Some (Load SZ8 true 11 19 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_4ed2c : bv 32 := 0x0109b603.
Lemma F_4ed2c : fetch_word Ubsan.M.loaded_segments (0x50ab4 : word) = Some W_4ed2c.
Proof. vm_refl. Qed.
Lemma D_4ed2c : decode_any W_4ed2c = Some (Load SZ8 true 12 19 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_4ed30 : bv 32 := 0x00a40533.
Lemma F_4ed30 : fetch_word Ubsan.M.loaded_segments (0x50ab8 : word) = Some W_4ed30.
Proof. vm_refl. Qed.
Lemma D_4ed30 : decode_any W_4ed30 = Some (Op ALU_ADD 10 8 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_4ed34 : bv 32 := 0x17d0e0ef.
Lemma F_4ed34 : fetch_word Ubsan.M.loaded_segments (0x50abc : word) = Some W_4ed34.
Proof. vm_refl. Qed.
Lemma D_4ed34 : decode_any W_4ed34 = Some (Jal 1 59772, 4%Z).
Proof. vm_refl. Qed.

Definition W_4ed38 : bv 32 := 0x0009b983.
Lemma F_4ed38 : fetch_word Ubsan.M.loaded_segments (0x50ac0 : word) = Some W_4ed38.
Proof. vm_refl. Qed.
Lemma D_4ed38 : decode_any W_4ed38 = Some (Load SZ8 true 19 19 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_4ed3c : bv 32 := 0x008a8a93.
Lemma F_4ed3c : fetch_word Ubsan.M.loaded_segments (0x50ac4 : word) = Some W_4ed3c.
Proof. vm_refl. Qed.
Lemma D_4ed3c : decode_any W_4ed3c = Some (OpImm ALU_ADD 21 21 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_4ed40 : bv 32 := 0xfc0998e3.
Lemma F_4ed40 : fetch_word Ubsan.M.loaded_segments (0x50ac8 : word) = Some W_4ed40.
Proof. vm_refl. Qed.
Lemma D_4ed40 : decode_any W_4ed40 = Some (Branch BC_NE 19 0 8144, 4%Z).
Proof. vm_refl. Qed.

Definition W_4ed44 : bv 32 := 0x0284b603.
Lemma F_4ed44 : fetch_word Ubsan.M.loaded_segments (0x50acc : word) = Some W_4ed44.
Proof. vm_refl. Qed.
Lemma D_4ed44 : decode_any W_4ed44 = Some (Load SZ8 true 12 9 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_4ed48 : bv 32 := 0x00ca3023.
Lemma F_4ed48 : fetch_word Ubsan.M.loaded_segments (0x50ad0 : word) = Some W_4ed48.
Proof. vm_refl. Qed.
Lemma D_4ed48 : decode_any W_4ed48 = Some (Store SZ8 20 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_4ed4c : bv 32 := 0x0d493023.
Lemma F_4ed4c : fetch_word Ubsan.M.loaded_segments (0x50ad4 : word) = Some W_4ed4c.
Proof. vm_refl. Qed.
Lemma D_4ed4c : decode_any W_4ed4c = Some (Store SZ8 18 20 192, 4%Z).
Proof. vm_refl. Qed.

Definition W_4ed50 : bv 32 := 0x01293023.
Lemma F_4ed50 : fetch_word Ubsan.M.loaded_segments (0x50ad8 : word) = Some W_4ed50.
Proof. vm_refl. Qed.
Lemma D_4ed50 : decode_any W_4ed50 = Some (Store SZ8 18 18 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_4ed54 : bv 32 := 0x00040513.
Lemma F_4ed54 : fetch_word Ubsan.M.loaded_segments (0x50adc : word) = Some W_4ed54.
Proof. vm_refl. Qed.
Lemma D_4ed54 : decode_any W_4ed54 = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_4ed58 : bv 32 := 0x390100ef.
Lemma F_4ed58 : fetch_word Ubsan.M.loaded_segments (0x50ae0 : word) = Some W_4ed58.
Proof. vm_refl. Qed.
Lemma D_4ed58 : decode_any W_4ed58 = Some (Jal 1 66448, 4%Z).
Proof. vm_refl. Qed.

Definition W_4ed5c : bv 32 := 0x04054a63.
Lemma F_4ed5c : fetch_word Ubsan.M.loaded_segments (0x50ae4 : word) = Some W_4ed5c.
Proof. vm_refl. Qed.
Lemma D_4ed5c : decode_any W_4ed5c = Some (Branch BC_LT 10 0 84, 4%Z).
Proof. vm_refl. Qed.

Definition W_4ed60 : bv 32 := 0x00051663.
Lemma F_4ed60 : fetch_word Ubsan.M.loaded_segments (0x50ae8 : word) = Some W_4ed60.
Proof. vm_refl. Qed.
Lemma D_4ed60 : decode_any W_4ed60 = Some (Branch BC_NE 10 0 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_4ed64 : bv 32 := 0x00100513.
Lemma F_4ed64 : fetch_word Ubsan.M.loaded_segments (0x50aec : word) = Some W_4ed64.
Proof. vm_refl. Qed.
Lemma D_4ed64 : decode_any W_4ed64 = Some (OpImm ALU_ADD 10 0 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_4ed68 : bv 32 := 0x00a48023.
Lemma F_4ed68 : fetch_word Ubsan.M.loaded_segments (0x50af0 : word) = Some W_4ed68.
Proof. vm_refl. Qed.
Lemma D_4ed68 : decode_any W_4ed68 = Some (Store SZ1 9 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_4ed6c : bv 32 := 0x00200513.
Lemma F_4ed6c : fetch_word Ubsan.M.loaded_segments (0x50af4 : word) = Some W_4ed6c.
Proof. vm_refl. Qed.
Lemma D_4ed6c : decode_any W_4ed6c = Some (OpImm ALU_ADD 10 0 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_4ed70 : bv 32 := 0x00047597.
Lemma F_4ed70 : fetch_word Ubsan.M.loaded_segments (0x50af8 : word) = Some W_4ed70.
Proof. vm_refl. Qed.
Lemma D_4ed70 : decode_any W_4ed70 = Some (Auipc 11 71, 4%Z).
Proof. vm_refl. Qed.

Definition W_4ed74 : bv 32 := 0x02a92423.
Lemma F_4ed74 : fetch_word Ubsan.M.loaded_segments (0x50afc : word) = Some W_4ed74.
Proof. vm_refl. Qed.
Lemma D_4ed74 : decode_any W_4ed74 = Some (Store SZ4 18 10 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_4ed78 : bv 32 := 0x06000893.
Lemma F_4ed78 : fetch_word Ubsan.M.loaded_segments (0x50b00 : word) = Some W_4ed78.
Proof. vm_refl. Qed.
Lemma D_4ed78 : decode_any W_4ed78 = Some (OpImm ALU_ADD 17 0 96, 4%Z).
Proof. vm_refl. Qed.

Definition W_4ed7c : bv 32 := 0x11058513.
Lemma F_4ed7c : fetch_word Ubsan.M.loaded_segments (0x50b04 : word) = Some W_4ed7c.
Proof. vm_refl. Qed.
Lemma D_4ed7c : decode_any W_4ed7c = Some (OpImm ALU_ADD 10 11 272, 4%Z).
Proof. vm_refl. Qed.

Definition W_4ed80 : bv 32 := 0x03848593.
Lemma F_4ed80 : fetch_word Ubsan.M.loaded_segments (0x50b08 : word) = Some W_4ed80.
Proof. vm_refl. Qed.
Lemma D_4ed80 : decode_any W_4ed80 = Some (OpImm ALU_ADD 11 9 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_4ed84 : bv 32 := 0x00000073.
Lemma F_4ed84 : fetch_word Ubsan.M.loaded_segments (0x50b0c : word) = Some W_4ed84.
Proof. vm_refl. Qed.

Lemma E_4ed84 : is_ecall W_4ed84 = true.
Proof. reflexivity. Qed.

Definition W_4ed88 : bv 32 := 0x07890613.
Lemma F_4ed88 : fetch_word Ubsan.M.loaded_segments (0x50b10 : word) = Some W_4ed88.
Proof. vm_refl. Qed.
Lemma D_4ed88 : decode_any W_4ed88 = Some (OpImm ALU_ADD 12 18 120, 4%Z).
Proof. vm_refl. Qed.

Definition W_4ed8c : bv 32 := 0x02a92023.
Lemma F_4ed8c : fetch_word Ubsan.M.loaded_segments (0x50b14 : word) = Some W_4ed8c.
Proof. vm_refl. Qed.
Lemma D_4ed8c : decode_any W_4ed8c = Some (Store SZ4 18 10 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_4ed90 : bv 32 := 0x08b93c23.
Lemma F_4ed90 : fetch_word Ubsan.M.loaded_segments (0x50b18 : word) = Some W_4ed90.
Proof. vm_refl. Qed.
Lemma D_4ed90 : decode_any W_4ed90 = Some (Store SZ8 18 11 152, 4%Z).
Proof. vm_refl. Qed.

Definition W_4ed94 : bv 32 := 0x06c93c23.
Lemma F_4ed94 : fetch_word Ubsan.M.loaded_segments (0x50b1c : word) = Some W_4ed94.
Proof. vm_refl. Qed.
Lemma D_4ed94 : decode_any W_4ed94 = Some (Store SZ8 18 12 120, 4%Z).
Proof. vm_refl. Qed.

Definition W_4ed98 : bv 32 := 0x00047517.
Lemma F_4ed98 : fetch_word Ubsan.M.loaded_segments (0x50b20 : word) = Some W_4ed98.
Proof. vm_refl. Qed.
Lemma D_4ed98 : decode_any W_4ed98 = Some (Auipc 10 71, 4%Z).
Proof. vm_refl. Qed.

Definition W_4ed9c : bv 32 := 0x35853503.
Lemma F_4ed9c : fetch_word Ubsan.M.loaded_segments (0x50b24 : word) = Some W_4ed9c.
Proof. vm_refl. Qed.
Lemma D_4ed9c : decode_any W_4ed9c = Some (Load SZ8 true 10 10 856, 4%Z).
Proof. vm_refl. Qed.

Definition W_4eda0 : bv 32 := 0x01293423.
Lemma F_4eda0 : fetch_word Ubsan.M.loaded_segments (0x50b28 : word) = Some W_4eda0.
Proof. vm_refl. Qed.
Lemma D_4eda0 : decode_any W_4eda0 = Some (Store SZ8 18 18 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_4eda4 : bv 32 := 0x01293823.
Lemma F_4eda4 : fetch_word Ubsan.M.loaded_segments (0x50b2c : word) = Some W_4eda4.
Proof. vm_refl. Qed.
Lemma D_4eda4 : decode_any W_4eda4 = Some (Store SZ8 18 18 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_4eda8 : bv 32 := 0x00a93c23.
Lemma F_4eda8 : fetch_word Ubsan.M.loaded_segments (0x50b30 : word) = Some W_4eda8.
Proof. vm_refl. Qed.
Lemma D_4eda8 : decode_any W_4eda8 = Some (Store SZ8 18 10 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_4edac : bv 32 := 0x0080006f.
Lemma F_4edac : fetch_word Ubsan.M.loaded_segments (0x50b34 : word) = Some W_4edac.
Proof. vm_refl. Qed.
Lemma D_4edac : decode_any W_4edac = Some (Jal 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_4edb4 : bv 32 := 0x03813083.
Lemma F_4edb4 : fetch_word Ubsan.M.loaded_segments (0x50b3c : word) = Some W_4edb4.
Proof. vm_refl. Qed.
Lemma D_4edb4 : decode_any W_4edb4 = Some (Load SZ8 true 1 2 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_4edb8 : bv 32 := 0x03013403.
Lemma F_4edb8 : fetch_word Ubsan.M.loaded_segments (0x50b40 : word) = Some W_4edb8.
Proof. vm_refl. Qed.
Lemma D_4edb8 : decode_any W_4edb8 = Some (Load SZ8 true 8 2 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_4edbc : bv 32 := 0x02813483.
Lemma F_4edbc : fetch_word Ubsan.M.loaded_segments (0x50b44 : word) = Some W_4edbc.
Proof. vm_refl. Qed.
Lemma D_4edbc : decode_any W_4edbc = Some (Load SZ8 true 9 2 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_4edc0 : bv 32 := 0x02013903.
Lemma F_4edc0 : fetch_word Ubsan.M.loaded_segments (0x50b48 : word) = Some W_4edc0.
Proof. vm_refl. Qed.
Lemma D_4edc0 : decode_any W_4edc0 = Some (Load SZ8 true 18 2 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_4edc4 : bv 32 := 0x01813983.
Lemma F_4edc4 : fetch_word Ubsan.M.loaded_segments (0x50b4c : word) = Some W_4edc4.
Proof. vm_refl. Qed.
Lemma D_4edc4 : decode_any W_4edc4 = Some (Load SZ8 true 19 2 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_4edc8 : bv 32 := 0x01013a03.
Lemma F_4edc8 : fetch_word Ubsan.M.loaded_segments (0x50b50 : word) = Some W_4edc8.
Proof. vm_refl. Qed.
Lemma D_4edc8 : decode_any W_4edc8 = Some (Load SZ8 true 20 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_4edcc : bv 32 := 0x00813a83.
Lemma F_4edcc : fetch_word Ubsan.M.loaded_segments (0x50b54 : word) = Some W_4edcc.
Proof. vm_refl. Qed.
Lemma D_4edcc : decode_any W_4edcc = Some (Load SZ8 true 21 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_4edd0 : bv 32 := 0x04010113.
Lemma F_4edd0 : fetch_word Ubsan.M.loaded_segments (0x50b58 : word) = Some W_4edd0.
Proof. vm_refl. Qed.
Lemma D_4edd0 : decode_any W_4edd0 = Some (OpImm ALU_ADD 2 2 64, 4%Z).
Proof. vm_refl. Qed.

Definition W_4edd4 : bv 32 := 0x00008067.
Lemma F_4edd4 : fetch_word Ubsan.M.loaded_segments (0x50b5c : word) = Some W_4edd4.
Proof. vm_refl. Qed.
Lemma D_4edd4 : decode_any W_4edd4 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_4ee60 : bv 32 := 0x00050593.
Lemma F_4ee60 : fetch_word Ubsan.M.loaded_segments (0x50c3c : word) = Some W_4ee60.
Proof. vm_refl. Qed.
Lemma D_4ee60 : decode_any W_4ee60 = Some (OpImm ALU_ADD 11 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_4ee64 : bv 32 := 0x05e00893.
Lemma F_4ee64 : fetch_word Ubsan.M.loaded_segments (0x50c40 : word) = Some W_4ee64.
Proof. vm_refl. Qed.
Lemma D_4ee64 : decode_any W_4ee64 = Some (OpImm ALU_ADD 17 0 94, 4%Z).
Proof. vm_refl. Qed.

Definition W_4ee68 : bv 32 := 0x00000073.
Lemma F_4ee68 : fetch_word Ubsan.M.loaded_segments (0x50c44 : word) = Some W_4ee68.
Proof. vm_refl. Qed.

Lemma E_4ee68 : is_ecall W_4ee68 = true.
Proof. reflexivity. Qed.

Definition W_4eeac : bv 32 := 0xfd010113.
Lemma F_4eeac : fetch_word Ubsan.M.loaded_segments (0x50c88 : word) = Some W_4eeac.
Proof. vm_refl. Qed.
Lemma D_4eeac : decode_any W_4eeac = Some (OpImm ALU_ADD 2 2 4048, 4%Z).
Proof. vm_refl. Qed.

Definition W_4eeb0 : bv 32 := 0x02113423.
Lemma F_4eeb0 : fetch_word Ubsan.M.loaded_segments (0x50c8c : word) = Some W_4eeb0.
Proof. vm_refl. Qed.
Lemma D_4eeb0 : decode_any W_4eeb0 = Some (Store SZ8 2 1 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_4eeb4 : bv 32 := 0x02813023.
Lemma F_4eeb4 : fetch_word Ubsan.M.loaded_segments (0x50c90 : word) = Some W_4eeb4.
Proof. vm_refl. Qed.
Lemma D_4eeb4 : decode_any W_4eeb4 = Some (Store SZ8 2 8 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_4eeb8 : bv 32 := 0x00913c23.
Lemma F_4eeb8 : fetch_word Ubsan.M.loaded_segments (0x50c94 : word) = Some W_4eeb8.
Proof. vm_refl. Qed.
Lemma D_4eeb8 : decode_any W_4eeb8 = Some (Store SZ8 2 9 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_4eebc : bv 32 := 0x01213823.
Lemma F_4eebc : fetch_word Ubsan.M.loaded_segments (0x50c98 : word) = Some W_4eebc.
Proof. vm_refl. Qed.
Lemma D_4eebc : decode_any W_4eebc = Some (Store SZ8 2 18 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_4eec0 : bv 32 := 0x01313423.
Lemma F_4eec0 : fetch_word Ubsan.M.loaded_segments (0x50c9c : word) = Some W_4eec0.
Proof. vm_refl. Qed.
Lemma D_4eec0 : decode_any W_4eec0 = Some (Store SZ8 2 19 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_4eec4 : bv 32 := 0x00047517.
Lemma F_4eec4 : fetch_word Ubsan.M.loaded_segments (0x50ca0 : word) = Some W_4eec4.
Proof. vm_refl. Qed.
Lemma D_4eec4 : decode_any W_4eec4 = Some (Auipc 10 71, 4%Z).
Proof. vm_refl. Qed.

Definition W_4eec8 : bv 32 := 0xfa850913.
Lemma F_4eec8 : fetch_word Ubsan.M.loaded_segments (0x50ca4 : word) = Some W_4eec8.
Proof. vm_refl. Qed.
Lemma D_4eec8 : decode_any W_4eec8 = Some (OpImm ALU_ADD 18 10 4008, 4%Z).
Proof. vm_refl. Qed.

Definition W_4eecc : bv 32 := 0x00490413.
Lemma F_4eecc : fetch_word Ubsan.M.loaded_segments (0x50ca8 : word) = Some W_4eecc.
Proof. vm_refl. Qed.
Lemma D_4eecc : decode_any W_4eecc = Some (OpImm ALU_ADD 8 18 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_4eed0 : bv 32 := 0x00040513.
Lemma F_4eed0 : fetch_word Ubsan.M.loaded_segments (0x50cac : word) = Some W_4eed0.
Proof. vm_refl. Qed.
Lemma D_4eed0 : decode_any W_4eed0 = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_4eed4 : bv 32 := 0x0a10f0ef.
Lemma F_4eed4 : fetch_word Ubsan.M.loaded_segments (0x50cb0 : word) = Some W_4eed4.
Proof. vm_refl. Qed.
Lemma D_4eed4 : decode_any W_4eed4 = Some (Jal 1 63648, 4%Z).
Proof. vm_refl. Qed.

Definition W_4eed8 : bv 32 := 0x01093503.
Lemma F_4eed8 : fetch_word Ubsan.M.loaded_segments (0x50cb4 : word) = Some W_4eed8.
Proof. vm_refl. Qed.
Lemma D_4eed8 : decode_any W_4eed8 = Some (Load SZ8 true 10 18 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_4eedc : bv 32 := 0x06050863.
Lemma F_4eedc : fetch_word Ubsan.M.loaded_segments (0x50cb8 : word) = Some W_4eedc.
Proof. vm_refl. Qed.
Lemma D_4eedc : decode_any W_4eedc = Some (Branch BC_EQ 10 0 112, 4%Z).
Proof. vm_refl. Qed.

Definition W_4eee0 : bv 32 := 0x00892583.
Lemma F_4eee0 : fetch_word Ubsan.M.loaded_segments (0x50cbc : word) = Some W_4eee0.
Proof. vm_refl. Qed.
Lemma D_4eee0 : decode_any W_4eee0 = Some (Load SZ4 true 11 18 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_4eee4 : bv 32 := 0x0180006f.
Lemma F_4eee4 : fetch_word Ubsan.M.loaded_segments (0x50cc0 : word) = Some W_4eee4.
Proof. vm_refl. Qed.
Lemma D_4eee4 : decode_any W_4eee4 = Some (Jal 0 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_4eee8 : bv 32 := 0x00053503.
Lemma F_4eee8 : fetch_word Ubsan.M.loaded_segments (0x50cc4 : word) = Some W_4eee8.
Proof. vm_refl. Qed.
Lemma D_4eee8 : decode_any W_4eee8 = Some (Load SZ8 true 10 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_4eeec : bv 32 := 0x02000593.
Lemma F_4eeec : fetch_word Ubsan.M.loaded_segments (0x50cc8 : word) = Some W_4eeec.
Proof. vm_refl. Qed.
Lemma D_4eeec : decode_any W_4eeec = Some (OpImm ALU_ADD 11 0 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_4eef0 : bv 32 := 0x00b92423.
Lemma F_4eef0 : fetch_word Ubsan.M.loaded_segments (0x50ccc : word) = Some W_4eef0.
Proof. vm_refl. Qed.
Lemma D_4eef0 : decode_any W_4eef0 = Some (Store SZ4 18 11 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_4eef4 : bv 32 := 0x00a93823.
Lemma F_4eef4 : fetch_word Ubsan.M.loaded_segments (0x50cd0 : word) = Some W_4eef4.
Proof. vm_refl. Qed.
Lemma D_4eef4 : decode_any W_4eef4 = Some (Store SZ8 18 10 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_4eef8 : bv 32 := 0x04050a63.
Lemma F_4eef8 : fetch_word Ubsan.M.loaded_segments (0x50cd4 : word) = Some W_4eef8.
Proof. vm_refl. Qed.
Lemma D_4eef8 : decode_any W_4eef8 = Some (Branch BC_EQ 10 0 84, 4%Z).
Proof. vm_refl. Qed.

Definition W_4eefc : bv 32 := 0xfff5861b.
Lemma F_4eefc : fetch_word Ubsan.M.loaded_segments (0x50cd8 : word) = Some W_4eefc.
Proof. vm_refl. Qed.
Lemma D_4eefc : decode_any W_4eefc = Some (OpImm32 12 11 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_4ef00 : bv 32 := 0x00c92423.
Lemma F_4ef00 : fetch_word Ubsan.M.loaded_segments (0x50cdc : word) = Some W_4ef00.
Proof. vm_refl. Qed.
Lemma D_4ef00 : decode_any W_4ef00 = Some (Store SZ4 18 12 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_4ef04 : bv 32 := 0xfeb052e3.
Lemma F_4ef04 : fetch_word Ubsan.M.loaded_segments (0x50ce0 : word) = Some W_4ef04.
Proof. vm_refl. Qed.
Lemma D_4ef04 : decode_any W_4ef04 = Some (Branch BC_GE 0 11 8164, 4%Z).
Proof. vm_refl. Qed.

Definition W_4ef08 : bv 32 := 0x01093503.
Lemma F_4ef08 : fetch_word Ubsan.M.loaded_segments (0x50ce4 : word) = Some W_4ef08.
Proof. vm_refl. Qed.
Lemma D_4ef08 : decode_any W_4ef08 = Some (Load SZ8 true 10 18 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_4ef0c : bv 32 := 0x00361613.
Lemma F_4ef0c : fetch_word Ubsan.M.loaded_segments (0x50ce8 : word) = Some W_4ef0c.
Proof. vm_refl. Qed.
Lemma D_4ef0c : decode_any W_4ef0c = Some (ShiftImm ALU_SLL 12 12 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_4ef10 : bv 32 := 0x00c50533.
Lemma F_4ef10 : fetch_word Ubsan.M.loaded_segments (0x50cec : word) = Some W_4ef10.
Proof. vm_refl. Qed.
Lemma D_4ef10 : decode_any W_4ef10 = Some (Op ALU_ADD 10 10 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_4ef14 : bv 32 := 0x00853983.
Lemma F_4ef14 : fetch_word Ubsan.M.loaded_segments (0x50cf0 : word) = Some W_4ef14.
Proof. vm_refl. Qed.
Lemma D_4ef14 : decode_any W_4ef14 = Some (Load SZ8 true 19 10 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_4ef18 : bv 32 := 0x10853483.
Lemma F_4ef18 : fetch_word Ubsan.M.loaded_segments (0x50cf4 : word) = Some W_4ef18.
Proof. vm_refl. Qed.
Lemma D_4ef18 : decode_any W_4ef18 = Some (Load SZ8 true 9 10 264, 4%Z).
Proof. vm_refl. Qed.

Definition W_4ef1c : bv 32 := 0x00040513.
Lemma F_4ef1c : fetch_word Ubsan.M.loaded_segments (0x50cf8 : word) = Some W_4ef1c.
Proof. vm_refl. Qed.
Lemma D_4ef1c : decode_any W_4ef1c = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_4ef20 : bv 32 := 0x2dd0f0ef.
Lemma F_4ef20 : fetch_word Ubsan.M.loaded_segments (0x50cfc : word) = Some W_4ef20.
Proof. vm_refl. Qed.
Lemma D_4ef20 : decode_any W_4ef20 = Some (Jal 1 64220, 4%Z).
Proof. vm_refl. Qed.

Definition W_4ef24 : bv 32 := 0x00048513.
Lemma F_4ef24 : fetch_word Ubsan.M.loaded_segments (0x50d00 : word) = Some W_4ef24.
Proof. vm_refl. Qed.
Lemma D_4ef24 : decode_any W_4ef24 = Some (OpImm ALU_ADD 10 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_4ef28 : bv 32 := 0x000980e7.
Lemma F_4ef28 : fetch_word Ubsan.M.loaded_segments (0x50d04 : word) = Some W_4ef28.
Proof. vm_refl. Qed.
Lemma D_4ef28 : decode_any W_4ef28 = Some (Jalr 1 19 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_4ef2c : bv 32 := 0x00040513.
Lemma F_4ef2c : fetch_word Ubsan.M.loaded_segments (0x50d08 : word) = Some W_4ef2c.
Proof. vm_refl. Qed.
Lemma D_4ef2c : decode_any W_4ef2c = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_4ef30 : bv 32 := 0x0450f0ef.
Lemma F_4ef30 : fetch_word Ubsan.M.loaded_segments (0x50d0c : word) = Some W_4ef30.
Proof. vm_refl. Qed.
Lemma D_4ef30 : decode_any W_4ef30 = Some (Jal 1 63556, 4%Z).
Proof. vm_refl. Qed.

Definition W_4ef34 : bv 32 := 0x00892503.
Lemma F_4ef34 : fetch_word Ubsan.M.loaded_segments (0x50d10 : word) = Some W_4ef34.
Proof. vm_refl. Qed.
Lemma D_4ef34 : decode_any W_4ef34 = Some (Load SZ4 true 10 18 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_4ef38 : bv 32 := 0xfff5061b.
Lemma F_4ef38 : fetch_word Ubsan.M.loaded_segments (0x50d14 : word) = Some W_4ef38.
Proof. vm_refl. Qed.
Lemma D_4ef38 : decode_any W_4ef38 = Some (OpImm32 12 10 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_4ef3c : bv 32 := 0x00c92423.
Lemma F_4ef3c : fetch_word Ubsan.M.loaded_segments (0x50d18 : word) = Some W_4ef3c.
Proof. vm_refl. Qed.
Lemma D_4ef3c : decode_any W_4ef3c = Some (Store SZ4 18 12 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_4ef40 : bv 32 := 0xfca044e3.
Lemma F_4ef40 : fetch_word Ubsan.M.loaded_segments (0x50d1c : word) = Some W_4ef40.
Proof. vm_refl. Qed.
Lemma D_4ef40 : decode_any W_4ef40 = Some (Branch BC_LT 0 10 8136, 4%Z).
Proof. vm_refl. Qed.

Definition W_4ef44 : bv 32 := 0x01093503.
Lemma F_4ef44 : fetch_word Ubsan.M.loaded_segments (0x50d20 : word) = Some W_4ef44.
Proof. vm_refl. Qed.
Lemma D_4ef44 : decode_any W_4ef44 = Some (Load SZ8 true 10 18 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_4ef48 : bv 32 := 0xfa1ff06f.
Lemma F_4ef48 : fetch_word Ubsan.M.loaded_segments (0x50d24 : word) = Some W_4ef48.
Proof. vm_refl. Qed.
Lemma D_4ef48 : decode_any W_4ef48 = Some (Jal 0 2097056, 4%Z).
Proof. vm_refl. Qed.

Definition W_4ef4c : bv 32 := 0x00100513.
Lemma F_4ef4c : fetch_word Ubsan.M.loaded_segments (0x50d28 : word) = Some W_4ef4c.
Proof. vm_refl. Qed.
Lemma D_4ef4c : decode_any W_4ef4c = Some (OpImm ALU_ADD 10 0 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_4ef50 : bv 32 := 0x00a90023.
Lemma F_4ef50 : fetch_word Ubsan.M.loaded_segments (0x50d2c : word) = Some W_4ef50.
Proof. vm_refl. Qed.
Lemma D_4ef50 : decode_any W_4ef50 = Some (Store SZ1 18 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_4ef54 : bv 32 := 0x00040513.
Lemma F_4ef54 : fetch_word Ubsan.M.loaded_segments (0x50d30 : word) = Some W_4ef54.
Proof. vm_refl. Qed.
Lemma D_4ef54 : decode_any W_4ef54 = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_4ef58 : bv 32 := 0x02813083.
Lemma F_4ef58 : fetch_word Ubsan.M.loaded_segments (0x50d34 : word) = Some W_4ef58.
Proof. vm_refl. Qed.
Lemma D_4ef58 : decode_any W_4ef58 = Some (Load SZ8 true 1 2 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_4ef5c : bv 32 := 0x02013403.
Lemma F_4ef5c : fetch_word Ubsan.M.loaded_segments (0x50d38 : word) = Some W_4ef5c.
Proof. vm_refl. Qed.
Lemma D_4ef5c : decode_any W_4ef5c = Some (Load SZ8 true 8 2 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_4ef60 : bv 32 := 0x01813483.
Lemma F_4ef60 : fetch_word Ubsan.M.loaded_segments (0x50d3c : word) = Some W_4ef60.
Proof. vm_refl. Qed.
Lemma D_4ef60 : decode_any W_4ef60 = Some (Load SZ8 true 9 2 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_4ef64 : bv 32 := 0x01013903.
Lemma F_4ef64 : fetch_word Ubsan.M.loaded_segments (0x50d40 : word) = Some W_4ef64.
Proof. vm_refl. Qed.
Lemma D_4ef64 : decode_any W_4ef64 = Some (Load SZ8 true 18 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_4ef68 : bv 32 := 0x00813983.
Lemma F_4ef68 : fetch_word Ubsan.M.loaded_segments (0x50d44 : word) = Some W_4ef68.
Proof. vm_refl. Qed.
Lemma D_4ef68 : decode_any W_4ef68 = Some (Load SZ8 true 19 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_4ef6c : bv 32 := 0x03010113.
Lemma F_4ef6c : fetch_word Ubsan.M.loaded_segments (0x50d48 : word) = Some W_4ef6c.
Proof. vm_refl. Qed.
Lemma D_4ef6c : decode_any W_4ef6c = Some (OpImm ALU_ADD 2 2 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_4ef70 : bv 32 := 0x28d0f06f.
Lemma F_4ef70 : fetch_word Ubsan.M.loaded_segments (0x50d4c : word) = Some W_4ef70.
Proof. vm_refl. Qed.
Lemma D_4ef70 : decode_any W_4ef70 = Some (Jal 0 64140, 4%Z).
Proof. vm_refl. Qed.

Definition W_4ef74 : bv 32 := 0x00008067.
Lemma F_4ef74 : fetch_word Ubsan.M.loaded_segments (0x50d50 : word) = Some W_4ef74.
Proof. vm_refl. Qed.
Lemma D_4ef74 : decode_any W_4ef74 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_4f03c : bv 32 := 0x00050067.
Lemma F_4f03c : fetch_word Ubsan.M.loaded_segments (0x50e18 : word) = Some W_4f03c.
Proof. vm_refl. Qed.
Lemma D_4f03c : decode_any W_4f03c = Some (Jalr 0 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_4f040 : bv 32 := 0x00008067.
Lemma F_4f040 : fetch_word Ubsan.M.loaded_segments (0x50e1c : word) = Some W_4f040.
Proof. vm_refl. Qed.
Lemma D_4f040 : decode_any W_4f040 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_4f044 : bv 32 := 0xfe010113.
Lemma F_4f044 : fetch_word Ubsan.M.loaded_segments (0x50e20 : word) = Some W_4f044.
Proof. vm_refl. Qed.
Lemma D_4f044 : decode_any W_4f044 = Some (OpImm ALU_ADD 2 2 4064, 4%Z).
Proof. vm_refl. Qed.

Definition W_4f048 : bv 32 := 0x00113c23.
Lemma F_4f048 : fetch_word Ubsan.M.loaded_segments (0x50e24 : word) = Some W_4f048.
Proof. vm_refl. Qed.
Lemma D_4f048 : decode_any W_4f048 = Some (Store SZ8 2 1 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_4f04c : bv 32 := 0x00813823.
Lemma F_4f04c : fetch_word Ubsan.M.loaded_segments (0x50e28 : word) = Some W_4f04c.
Proof. vm_refl. Qed.
Lemma D_4f04c : decode_any W_4f04c = Some (Store SZ8 2 8 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_4f050 : bv 32 := 0x00913423.
Lemma F_4f050 : fetch_word Ubsan.M.loaded_segments (0x50e2c : word) = Some W_4f050.
Proof. vm_refl. Qed.
Lemma D_4f050 : decode_any W_4f050 = Some (Store SZ8 2 9 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_4f054 : bv 32 := 0x00015517.
Lemma F_4f054 : fetch_word Ubsan.M.loaded_segments (0x50e30 : word) = Some W_4f054.
Proof. vm_refl. Qed.
Lemma D_4f054 : decode_any W_4f054 = Some (Auipc 10 21, 4%Z).
Proof. vm_refl. Qed.

Definition W_4f058 : bv 32 := 0x00015597.
Lemma F_4f058 : fetch_word Ubsan.M.loaded_segments (0x50e34 : word) = Some W_4f058.
Proof. vm_refl. Qed.
Lemma D_4f058 : decode_any W_4f058 = Some (Auipc 11 21, 4%Z).
Proof. vm_refl. Qed.

Definition W_4f05c : bv 32 := 0xba853503.
Lemma F_4f05c : fetch_word Ubsan.M.loaded_segments (0x50e38 : word) = Some W_4f05c.
Proof. vm_refl. Qed.
Lemma D_4f05c : decode_any W_4f05c = Some (Load SZ8 true 10 10 2984, 4%Z).
Proof. vm_refl. Qed.

Definition W_4f060 : bv 32 := 0xbac5b403.
Lemma F_4f060 : fetch_word Ubsan.M.loaded_segments (0x50e3c : word) = Some W_4f060.
Proof. vm_refl. Qed.
Lemma D_4f060 : decode_any W_4f060 = Some (Load SZ8 true 8 11 2988, 4%Z).
Proof. vm_refl. Qed.

Definition W_4f064 : bv 32 := 0x00a47c63.
Lemma F_4f064 : fetch_word Ubsan.M.loaded_segments (0x50e40 : word) = Some W_4f064.
Proof. vm_refl. Qed.
Lemma D_4f064 : decode_any W_4f064 = Some (Branch BC_GEU 8 10 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_4f068 : bv 32 := 0xff853583.
Lemma F_4f068 : fetch_word Ubsan.M.loaded_segments (0x50e44 : word) = Some W_4f068.
Proof. vm_refl. Qed.
Lemma D_4f068 : decode_any W_4f068 = Some (Load SZ8 true 11 10 4088, 4%Z).
Proof. vm_refl. Qed.

Definition W_4f06c : bv 32 := 0xff850493.
Lemma F_4f06c : fetch_word Ubsan.M.loaded_segments (0x50e48 : word) = Some W_4f06c.
Proof. vm_refl. Qed.
Lemma D_4f06c : decode_any W_4f06c = Some (OpImm ALU_ADD 9 10 4088, 4%Z).
Proof. vm_refl. Qed.

Definition W_4f070 : bv 32 := 0x000580e7.
Lemma F_4f070 : fetch_word Ubsan.M.loaded_segments (0x50e4c : word) = Some W_4f070.
Proof. vm_refl. Qed.
Lemma D_4f070 : decode_any W_4f070 = Some (Jalr 1 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_4f074 : bv 32 := 0x00048513.
Lemma F_4f074 : fetch_word Ubsan.M.loaded_segments (0x50e50 : word) = Some W_4f074.
Proof. vm_refl. Qed.
Lemma D_4f074 : decode_any W_4f074 = Some (OpImm ALU_ADD 10 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_4f078 : bv 32 := 0xfe9468e3.
Lemma F_4f078 : fetch_word Ubsan.M.loaded_segments (0x50e54 : word) = Some W_4f078.
Proof. vm_refl. Qed.
Lemma D_4f078 : decode_any W_4f078 = Some (Branch BC_LTU 8 9 8176, 4%Z).
Proof. vm_refl. Qed.

Definition W_4f07c : bv 32 := 0x01813083.
Lemma F_4f07c : fetch_word Ubsan.M.loaded_segments (0x50e58 : word) = Some W_4f07c.
Proof. vm_refl. Qed.
Lemma D_4f07c : decode_any W_4f07c = Some (Load SZ8 true 1 2 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_4f080 : bv 32 := 0x01013403.
Lemma F_4f080 : fetch_word Ubsan.M.loaded_segments (0x50e5c : word) = Some W_4f080.
Proof. vm_refl. Qed.
Lemma D_4f080 : decode_any W_4f080 = Some (Load SZ8 true 8 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_4f084 : bv 32 := 0x00813483.
Lemma F_4f084 : fetch_word Ubsan.M.loaded_segments (0x50e60 : word) = Some W_4f084.
Proof. vm_refl. Qed.
Lemma D_4f084 : decode_any W_4f084 = Some (Load SZ8 true 9 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_4f088 : bv 32 := 0x02010113.
Lemma F_4f088 : fetch_word Ubsan.M.loaded_segments (0x50e64 : word) = Some W_4f088.
Proof. vm_refl. Qed.
Lemma D_4f088 : decode_any W_4f088 = Some (OpImm ALU_ADD 2 2 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_4f08c : bv 32 := 0xfb5ff06f.
Lemma F_4f08c : fetch_word Ubsan.M.loaded_segments (0x50e68 : word) = Some W_4f08c.
Proof. vm_refl. Qed.
Lemma D_4f08c : decode_any W_4f08c = Some (Jal 0 2097076, 4%Z).
Proof. vm_refl. Qed.

Definition W_4f090 : bv 32 := 0xff010113.
Lemma F_4f090 : fetch_word Ubsan.M.loaded_segments (0x50e6c : word) = Some W_4f090.
Proof. vm_refl. Qed.
Lemma D_4f090 : decode_any W_4f090 = Some (OpImm ALU_ADD 2 2 4080, 4%Z).
Proof. vm_refl. Qed.

Definition W_4f094 : bv 32 := 0x00113423.
Lemma F_4f094 : fetch_word Ubsan.M.loaded_segments (0x50e70 : word) = Some W_4f094.
Proof. vm_refl. Qed.
Lemma D_4f094 : decode_any W_4f094 = Some (Store SZ8 2 1 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_4f098 : bv 32 := 0x00813023.
Lemma F_4f098 : fetch_word Ubsan.M.loaded_segments (0x50e74 : word) = Some W_4f098.
Proof. vm_refl. Qed.
Lemma D_4f098 : decode_any W_4f098 = Some (Store SZ8 2 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_4f09c : bv 32 := 0x00000593.
Lemma F_4f09c : fetch_word Ubsan.M.loaded_segments (0x50e78 : word) = Some W_4f09c.
Proof. vm_refl. Qed.
Lemma D_4f09c : decode_any W_4f09c = Some (OpImm ALU_ADD 11 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_4f0a0 : bv 32 := 0x00020613.
Lemma F_4f0a0 : fetch_word Ubsan.M.loaded_segments (0x50e7c : word) = Some W_4f0a0.
Proof. vm_refl. Qed.
Lemma D_4f0a0 : decode_any W_4f0a0 = Some (OpImm ALU_ADD 12 4 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_4f0a4 : bv 32 := 0xf5862603.
Lemma F_4f0a4 : fetch_word Ubsan.M.loaded_segments (0x50e80 : word) = Some W_4f0a4.
Proof. vm_refl. Qed.
Lemma D_4f0a4 : decode_any W_4f0a4 = Some (Load SZ4 true 12 12 3928, 4%Z).
Proof. vm_refl. Qed.

Definition W_4f0a8 : bv 32 := 0x00047697.
Lemma F_4f0a8 : fetch_word Ubsan.M.loaded_segments (0x50e84 : word) = Some W_4f0a8.
Proof. vm_refl. Qed.
Lemma D_4f0a8 : decode_any W_4f0a8 = Some (Auipc 13 71, 4%Z).
Proof. vm_refl. Qed.

Definition W_4f0ac : bv 32 := 0xfe468693.
Lemma F_4f0ac : fetch_word Ubsan.M.loaded_segments (0x50e88 : word) = Some W_4f0ac.
Proof. vm_refl. Qed.
Lemma D_4f0ac : decode_any W_4f0ac = Some (OpImm ALU_ADD 13 13 4068, 4%Z).
Proof. vm_refl. Qed.

Definition W_4f0b0 : bv 32 := 0x1606a72f.
Lemma F_4f0b0 : fetch_word Ubsan.M.loaded_segments (0x50e8c : word) = Some W_4f0b0.
Proof. vm_refl. Qed.
Lemma D_4f0b0 : decode_any W_4f0b0 = Some (Lr AW true true 14 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_4f0b4 : bv 32 := 0x00b71663.
Lemma F_4f0b4 : fetch_word Ubsan.M.loaded_segments (0x50e90 : word) = Some W_4f0b4.
Proof. vm_refl. Qed.
Lemma D_4f0b4 : decode_any W_4f0b4 = Some (Branch BC_NE 14 11 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_4f0b8 : bv 32 := 0x1ec6a7af.
Lemma F_4f0b8 : fetch_word Ubsan.M.loaded_segments (0x50e94 : word) = Some W_4f0b8.
Proof. vm_refl. Qed.
Lemma D_4f0b8 : decode_any W_4f0b8 = Some (Sc AW true true 15 13 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_4f0bc : bv 32 := 0xfe079ae3.
Lemma F_4f0bc : fetch_word Ubsan.M.loaded_segments (0x50e98 : word) = Some W_4f0bc.
Proof. vm_refl. Qed.
Lemma D_4f0bc : decode_any W_4f0bc = Some (Branch BC_NE 15 0 8180, 4%Z).
Proof. vm_refl. Qed.

Definition W_4f0c0 : bv 32 := 0x0007059b.
Lemma F_4f0c0 : fetch_word Ubsan.M.loaded_segments (0x50e9c : word) = Some W_4f0c0.
Proof. vm_refl. Qed.
Lemma D_4f0c0 : decode_any W_4f0c0 = Some (OpImm32 11 14 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_4f0c4 : bv 32 := 0x02c58263.
Lemma F_4f0c4 : fetch_word Ubsan.M.loaded_segments (0x50ea0 : word) = Some W_4f0c4.
Proof. vm_refl. Qed.
Lemma D_4f0c4 : decode_any W_4f0c4 = Some (Branch BC_EQ 11 12 36, 4%Z).
Proof. vm_refl. Qed.

Definition W_4f0c8 : bv 32 := 0x02058263.
Lemma F_4f0c8 : fetch_word Ubsan.M.loaded_segments (0x50ea4 : word) = Some W_4f0c8.
Proof. vm_refl. Qed.
Lemma D_4f0c8 : decode_any W_4f0c8 = Some (Branch BC_EQ 11 0 36, 4%Z).
Proof. vm_refl. Qed.

Definition W_4f0ec : bv 32 := 0x00050413.
Lemma F_4f0ec : fetch_word Ubsan.M.loaded_segments (0x50ec8 : word) = Some W_4f0ec.
Proof. vm_refl. Qed.
Lemma D_4f0ec : decode_any W_4f0ec = Some (OpImm ALU_ADD 8 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_4f0f0 : bv 32 := 0xdbdff0ef.
Lemma F_4f0f0 : fetch_word Ubsan.M.loaded_segments (0x50ecc : word) = Some W_4f0f0.
Proof. vm_refl. Qed.
Lemma D_4f0f0 : decode_any W_4f0f0 = Some (Jal 1 2096572, 4%Z).
Proof. vm_refl. Qed.

Definition W_4f0f4 : bv 32 := 0xf51ff0ef.
Lemma F_4f0f4 : fetch_word Ubsan.M.loaded_segments (0x50ed0 : word) = Some W_4f0f4.
Proof. vm_refl. Qed.
Lemma D_4f0f4 : decode_any W_4f0f4 = Some (Jal 1 2096976, 4%Z).
Proof. vm_refl. Qed.

Definition W_4f0f8 : bv 32 := 0x6a9030ef.
Lemma F_4f0f8 : fetch_word Ubsan.M.loaded_segments (0x50ed4 : word) = Some W_4f0f8.
Proof. vm_refl. Qed.
Lemma D_4f0f8 : decode_any W_4f0f8 = Some (Jal 1 16040, 4%Z).
Proof. vm_refl. Qed.

Definition W_4f0fc : bv 32 := 0x00040513.
Lemma F_4f0fc : fetch_word Ubsan.M.loaded_segments (0x50ed8 : word) = Some W_4f0fc.
Proof. vm_refl. Qed.
Lemma D_4f0fc : decode_any W_4f0fc = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_4f100 : bv 32 := 0xd61ff0ef.
Lemma F_4f100 : fetch_word Ubsan.M.loaded_segments (0x50edc : word) = Some W_4f100.
Proof. vm_refl. Qed.
Lemma D_4f100 : decode_any W_4f100 = Some (Jal 1 2096480, 4%Z).
Proof. vm_refl. Qed.

Definition W_4f1e8 : bv 32 := 0xff010113.
Lemma F_4f1e8 : fetch_word Ubsan.M.loaded_segments (0x50fc4 : word) = Some W_4f1e8.
Proof. vm_refl. Qed.
Lemma D_4f1e8 : decode_any W_4f1e8 = Some (OpImm ALU_ADD 2 2 4080, 4%Z).
Proof. vm_refl. Qed.

Definition W_4f1ec : bv 32 := 0x00113423.
Lemma F_4f1ec : fetch_word Ubsan.M.loaded_segments (0x50fc8 : word) = Some W_4f1ec.
Proof. vm_refl. Qed.
Lemma D_4f1ec : decode_any W_4f1ec = Some (Store SZ8 2 1 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_4f1f0 : bv 32 := 0x00050e63.
Lemma F_4f1f0 : fetch_word Ubsan.M.loaded_segments (0x50fcc : word) = Some W_4f1f0.
Proof. vm_refl. Qed.
Lemma D_4f1f0 : decode_any W_4f1f0 = Some (Branch BC_EQ 10 0 28, 4%Z).
Proof. vm_refl. Qed.

Definition W_4f1f4 : bv 32 := 0x00050593.
Lemma F_4f1f4 : fetch_word Ubsan.M.loaded_segments (0x50fd0 : word) = Some W_4f1f4.
Proof. vm_refl. Qed.
Lemma D_4f1f4 : decode_any W_4f1f4 = Some (OpImm ALU_ADD 11 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_4f1f8 : bv 32 := 0x00015517.
Lemma F_4f1f8 : fetch_word Ubsan.M.loaded_segments (0x50fd4 : word) = Some W_4f1f8.
Proof. vm_refl. Qed.
Lemma D_4f1f8 : decode_any W_4f1f8 = Some (Auipc 10 21, 4%Z).
Proof. vm_refl. Qed.

Definition W_4f1fc : bv 32 := 0x9fc53503.
Lemma F_4f1fc : fetch_word Ubsan.M.loaded_segments (0x50fd8 : word) = Some W_4f1fc.
Proof. vm_refl. Qed.
Lemma D_4f1fc : decode_any W_4f1fc = Some (Load SZ8 true 10 10 2556, 4%Z).
Proof. vm_refl. Qed.

Definition W_4f200 : bv 32 := 0x00800613.
Lemma F_4f200 : fetch_word Ubsan.M.loaded_segments (0x50fdc : word) = Some W_4f200.
Proof. vm_refl. Qed.
Lemma D_4f200 : decode_any W_4f200 = Some (OpImm ALU_ADD 12 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_4f204 : bv 32 := 0x4580e0ef.
Lemma F_4f204 : fetch_word Ubsan.M.loaded_segments (0x50fe0 : word) = Some W_4f204.
Proof. vm_refl. Qed.
Lemma D_4f204 : decode_any W_4f204 = Some (Jal 1 58456, 4%Z).
Proof. vm_refl. Qed.

Definition W_4f208 : bv 32 := 0x01c0006f.
Lemma F_4f208 : fetch_word Ubsan.M.loaded_segments (0x50fe4 : word) = Some W_4f208.
Proof. vm_refl. Qed.
Lemma D_4f208 : decode_any W_4f208 = Some (Jal 0 28, 4%Z).
Proof. vm_refl. Qed.

Definition W_4f224 : bv 32 := 0x00015517.
Lemma F_4f224 : fetch_word Ubsan.M.loaded_segments (0x51000 : word) = Some W_4f224.
Proof. vm_refl. Qed.
Lemma D_4f224 : decode_any W_4f224 = Some (Auipc 10 21, 4%Z).
Proof. vm_refl. Qed.

Definition W_4f228 : bv 32 := 0x9d053503.
Lemma F_4f228 : fetch_word Ubsan.M.loaded_segments (0x51004 : word) = Some W_4f228.
Proof. vm_refl. Qed.
Lemma D_4f228 : decode_any W_4f228 = Some (Load SZ8 true 10 10 2512, 4%Z).
Proof. vm_refl. Qed.

Definition W_4f22c : bv 32 := 0x000500a3.
Lemma F_4f22c : fetch_word Ubsan.M.loaded_segments (0x51008 : word) = Some W_4f22c.
Proof. vm_refl. Qed.
Lemma D_4f22c : decode_any W_4f22c = Some (Store SZ1 10 0 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_4f230 : bv 32 := 0x00053503.
Lemma F_4f230 : fetch_word Ubsan.M.loaded_segments (0x5100c : word) = Some W_4f230.
Proof. vm_refl. Qed.
Lemma D_4f230 : decode_any W_4f230 = Some (Load SZ8 true 10 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_4f234 : bv 32 := 0x00020593.
Lemma F_4f234 : fetch_word Ubsan.M.loaded_segments (0x51010 : word) = Some W_4f234.
Proof. vm_refl. Qed.
Lemma D_4f234 : decode_any W_4f234 = Some (OpImm ALU_ADD 11 4 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_4f238 : bv 32 := 0xfea5b823.
Lemma F_4f238 : fetch_word Ubsan.M.loaded_segments (0x51014 : word) = Some W_4f238.
Proof. vm_refl. Qed.
Lemma D_4f238 : decode_any W_4f238 = Some (Store SZ8 11 10 4080, 4%Z).
Proof. vm_refl. Qed.

Definition W_4f23c : bv 32 := 0x00813083.
Lemma F_4f23c : fetch_word Ubsan.M.loaded_segments (0x51018 : word) = Some W_4f23c.
Proof. vm_refl. Qed.
Lemma D_4f23c : decode_any W_4f23c = Some (Load SZ8 true 1 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_4f240 : bv 32 := 0x01010113.
Lemma F_4f240 : fetch_word Ubsan.M.loaded_segments (0x5101c : word) = Some W_4f240.
Proof. vm_refl. Qed.
Lemma D_4f240 : decode_any W_4f240 = Some (OpImm ALU_ADD 2 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_4f244 : bv 32 := 0x00008067.
Lemma F_4f244 : fetch_word Ubsan.M.loaded_segments (0x51020 : word) = Some W_4f244.
Proof. vm_refl. Qed.
Lemma D_4f244 : decode_any W_4f244 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_4f250 : bv 32 := 0xfffff5b7.
Lemma F_4f250 : fetch_word Ubsan.M.loaded_segments (0x5102c : word) = Some W_4f250.
Proof. vm_refl. Qed.
Lemma D_4f250 : decode_any W_4f250 = Some (Lui 11 1048575, 4%Z).
Proof. vm_refl. Qed.

Definition W_4f254 : bv 32 := 0x0015859b.
Lemma F_4f254 : fetch_word Ubsan.M.loaded_segments (0x51030 : word) = Some W_4f254.
Proof. vm_refl. Qed.
Lemma D_4f254 : decode_any W_4f254 = Some (OpImm32 11 11 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_4f258 : bv 32 := 0x02b56663.
Lemma F_4f258 : fetch_word Ubsan.M.loaded_segments (0x51034 : word) = Some W_4f258.
Proof. vm_refl. Qed.
Lemma D_4f258 : decode_any W_4f258 = Some (Branch BC_LTU 10 11 44, 4%Z).
Proof. vm_refl. Qed.

Definition W_4f284 : bv 32 := 0x00008067.
Lemma F_4f284 : fetch_word Ubsan.M.loaded_segments (0x51060 : word) = Some W_4f284.
Proof. vm_refl. Qed.
Lemma D_4f284 : decode_any W_4f284 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.
