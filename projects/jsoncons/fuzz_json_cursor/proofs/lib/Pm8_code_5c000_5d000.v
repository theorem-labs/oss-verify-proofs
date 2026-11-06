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

Definition W_5c058 : bv 32 := 0xf8010113.
Lemma F_5c058 : fetch_word Asan.M.loaded_segments (0x5c0a8 : word) = Some W_5c058.
Proof. vm_refl. Qed.
Lemma D_5c058 : decode_any W_5c058 = Some (OpImm ALU_ADD 2 2 3968, 4%Z).
Proof. vm_refl. Qed.

Definition W_5c05c : bv 32 := 0x06113c23.
Lemma F_5c05c : fetch_word Asan.M.loaded_segments (0x5c0ac : word) = Some W_5c05c.
Proof. vm_refl. Qed.
Lemma D_5c05c : decode_any W_5c05c = Some (Store SZ8 2 1 120, 4%Z).
Proof. vm_refl. Qed.

Definition W_5c060 : bv 32 := 0x06813823.
Lemma F_5c060 : fetch_word Asan.M.loaded_segments (0x5c0b0 : word) = Some W_5c060.
Proof. vm_refl. Qed.
Lemma D_5c060 : decode_any W_5c060 = Some (Store SZ8 2 8 112, 4%Z).
Proof. vm_refl. Qed.

Definition W_5c064 : bv 32 := 0x06913423.
Lemma F_5c064 : fetch_word Asan.M.loaded_segments (0x5c0b4 : word) = Some W_5c064.
Proof. vm_refl. Qed.
Lemma D_5c064 : decode_any W_5c064 = Some (Store SZ8 2 9 104, 4%Z).
Proof. vm_refl. Qed.

Definition W_5c068 : bv 32 := 0x07213023.
Lemma F_5c068 : fetch_word Asan.M.loaded_segments (0x5c0b8 : word) = Some W_5c068.
Proof. vm_refl. Qed.
Lemma D_5c068 : decode_any W_5c068 = Some (Store SZ8 2 18 96, 4%Z).
Proof. vm_refl. Qed.

Definition W_5c06c : bv 32 := 0x05313c23.
Lemma F_5c06c : fetch_word Asan.M.loaded_segments (0x5c0bc : word) = Some W_5c06c.
Proof. vm_refl. Qed.
Lemma D_5c06c : decode_any W_5c06c = Some (Store SZ8 2 19 88, 4%Z).
Proof. vm_refl. Qed.

Definition W_5c070 : bv 32 := 0x05413823.
Lemma F_5c070 : fetch_word Asan.M.loaded_segments (0x5c0c0 : word) = Some W_5c070.
Proof. vm_refl. Qed.
Lemma D_5c070 : decode_any W_5c070 = Some (Store SZ8 2 20 80, 4%Z).
Proof. vm_refl. Qed.

Definition W_5c074 : bv 32 := 0x05513423.
Lemma F_5c074 : fetch_word Asan.M.loaded_segments (0x5c0c4 : word) = Some W_5c074.
Proof. vm_refl. Qed.
Lemma D_5c074 : decode_any W_5c074 = Some (Store SZ8 2 21 72, 4%Z).
Proof. vm_refl. Qed.

Definition W_5c078 : bv 32 := 0x05613023.
Lemma F_5c078 : fetch_word Asan.M.loaded_segments (0x5c0c8 : word) = Some W_5c078.
Proof. vm_refl. Qed.
Lemma D_5c078 : decode_any W_5c078 = Some (Store SZ8 2 22 64, 4%Z).
Proof. vm_refl. Qed.

Definition W_5c07c : bv 32 := 0x03713c23.
Lemma F_5c07c : fetch_word Asan.M.loaded_segments (0x5c0cc : word) = Some W_5c07c.
Proof. vm_refl. Qed.
Lemma D_5c07c : decode_any W_5c07c = Some (Store SZ8 2 23 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_5c080 : bv 32 := 0x03813823.
Lemma F_5c080 : fetch_word Asan.M.loaded_segments (0x5c0d0 : word) = Some W_5c080.
Proof. vm_refl. Qed.
Lemma D_5c080 : decode_any W_5c080 = Some (Store SZ8 2 24 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_5c084 : bv 32 := 0x03913423.
Lemma F_5c084 : fetch_word Asan.M.loaded_segments (0x5c0d4 : word) = Some W_5c084.
Proof. vm_refl. Qed.
Lemma D_5c084 : decode_any W_5c084 = Some (Store SZ8 2 25 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_5c088 : bv 32 := 0x03a13023.
Lemma F_5c088 : fetch_word Asan.M.loaded_segments (0x5c0d8 : word) = Some W_5c088.
Proof. vm_refl. Qed.
Lemma D_5c088 : decode_any W_5c088 = Some (Store SZ8 2 26 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_5c08c : bv 32 := 0x01b13c23.
Lemma F_5c08c : fetch_word Asan.M.loaded_segments (0x5c0dc : word) = Some W_5c08c.
Proof. vm_refl. Qed.
Lemma D_5c08c : decode_any W_5c08c = Some (Store SZ8 2 27 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_5c090 : bv 32 := 0x00078a93.
Lemma F_5c090 : fetch_word Asan.M.loaded_segments (0x5c0e0 : word) = Some W_5c090.
Proof. vm_refl. Qed.
Lemma D_5c090 : decode_any W_5c090 = Some (OpImm ALU_ADD 21 15 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5c094 : bv 32 := 0x00070b13.
Lemma F_5c094 : fetch_word Asan.M.loaded_segments (0x5c0e4 : word) = Some W_5c094.
Proof. vm_refl. Qed.
Lemma D_5c094 : decode_any W_5c094 = Some (OpImm ALU_ADD 22 14 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5c098 : bv 32 := 0x00068913.
Lemma F_5c098 : fetch_word Asan.M.loaded_segments (0x5c0e8 : word) = Some W_5c098.
Proof. vm_refl. Qed.
Lemma D_5c098 : decode_any W_5c098 = Some (OpImm ALU_ADD 18 13 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5c09c : bv 32 := 0x00058993.
Lemma F_5c09c : fetch_word Asan.M.loaded_segments (0x5c0ec : word) = Some W_5c09c.
Proof. vm_refl. Qed.
Lemma D_5c09c : decode_any W_5c09c = Some (OpImm ALU_ADD 19 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5c0a0 : bv 32 := 0x00050a13.
Lemma F_5c0a0 : fetch_word Asan.M.loaded_segments (0x5c0f0 : word) = Some W_5c0a0.
Proof. vm_refl. Qed.
Lemma D_5c0a0 : decode_any W_5c0a0 = Some (OpImm ALU_ADD 20 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5c0a4 : bv 32 := 0x00000513.
Lemma F_5c0a4 : fetch_word Asan.M.loaded_segments (0x5c0f4 : word) = Some W_5c0a4.
Proof. vm_refl. Qed.
Lemma D_5c0a4 : decode_any W_5c0a4 = Some (OpImm ALU_ADD 10 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5c0a8 : bv 32 := 0x00100d93.
Lemma F_5c0a8 : fetch_word Asan.M.loaded_segments (0x5c0f8 : word) = Some W_5c0a8.
Proof. vm_refl. Qed.
Lemma D_5c0a8 : decode_any W_5c0a8 = Some (OpImm ALU_ADD 27 0 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_5c0ac : bv 32 := 0x020a3603.
Lemma F_5c0ac : fetch_word Asan.M.loaded_segments (0x5c0fc : word) = Some W_5c0ac.
Proof. vm_refl. Qed.
Lemma D_5c0ac : decode_any W_5c0ac = Some (Load SZ8 true 12 20 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_5c0b0 : bv 32 := 0x030a3403.
Lemma F_5c0b0 : fetch_word Asan.M.loaded_segments (0x5c100 : word) = Some W_5c0b0.
Proof. vm_refl. Qed.
Lemma D_5c0b0 : decode_any W_5c0b0 = Some (Load SZ8 true 8 20 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_5c0b4 : bv 32 := 0x00769693.
Lemma F_5c0b4 : fetch_word Asan.M.loaded_segments (0x5c104 : word) = Some W_5c0b4.
Proof. vm_refl. Qed.
Lemma D_5c0b4 : decode_any W_5c0b4 = Some (ShiftImm ALU_SLL 13 13 7, 4%Z).
Proof. vm_refl. Qed.

Definition W_5c0b8 : bv 32 := 0x02091713.
Lemma F_5c0b8 : fetch_word Asan.M.loaded_segments (0x5c108 : word) = Some W_5c0b8.
Proof. vm_refl. Qed.
Lemma D_5c0b8 : decode_any W_5c0b8 = Some (ShiftImm ALU_SLL 14 18 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_5c0bc : bv 32 := 0x00700793.
Lemma F_5c0bc : fetch_word Asan.M.loaded_segments (0x5c10c : word) = Some W_5c0bc.
Proof. vm_refl. Qed.
Lemma D_5c0bc : decode_any W_5c0bc = Some (OpImm ALU_ADD 15 0 7, 4%Z).
Proof. vm_refl. Qed.

Definition W_5c0c0 : bv 32 := 0xfff00593.
Lemma F_5c0c0 : fetch_word Asan.M.loaded_segments (0x5c110 : word) = Some W_5c0c0.
Proof. vm_refl. Qed.
Lemma D_5c0c0 : decode_any W_5c0c0 = Some (OpImm ALU_ADD 11 0 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_5c0c4 : bv 32 := 0x03dd9c13.
Lemma F_5c0c4 : fetch_word Asan.M.loaded_segments (0x5c114 : word) = Some W_5c0c4.
Proof. vm_refl. Qed.
Lemma D_5c0c4 : decode_any W_5c0c4 = Some (ShiftImm ALU_SLL 24 27 61, 4%Z).
Proof. vm_refl. Qed.

Definition W_5c0c8 : bv 32 := 0x01d79793.
Lemma F_5c0c8 : fetch_word Asan.M.loaded_segments (0x5c118 : word) = Some W_5c0c8.
Proof. vm_refl. Qed.
Lemma D_5c0c8 : decode_any W_5c0c8 = Some (ShiftImm ALU_SLL 15 15 29, 4%Z).
Proof. vm_refl. Qed.

Definition W_5c0cc : bv 32 := 0x028d9b93.
Lemma F_5c0cc : fetch_word Asan.M.loaded_segments (0x5c11c : word) = Some W_5c0cc.
Proof. vm_refl. Qed.
Lemma D_5c0cc : decode_any W_5c0cc = Some (ShiftImm ALU_SLL 23 27 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_5c0d0 : bv 32 := 0x001b8813.
Lemma F_5c0d0 : fetch_word Asan.M.loaded_segments (0x5c120 : word) = Some W_5c0d0.
Proof. vm_refl. Qed.
Lemma D_5c0d0 : decode_any W_5c0d0 = Some (OpImm ALU_ADD 16 23 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_5c0d4 : bv 32 := 0x01481813.
Lemma F_5c0d4 : fetch_word Asan.M.loaded_segments (0x5c124 : word) = Some W_5c0d4.
Proof. vm_refl. Qed.
Lemma D_5c0d4 : decode_any W_5c0d4 = Some (ShiftImm ALU_SLL 16 16 20, 4%Z).
Proof. vm_refl. Qed.

Definition W_5c0d8 : bv 32 := 0x00d40433.
Lemma F_5c0d8 : fetch_word Asan.M.loaded_segments (0x5c128 : word) = Some W_5c0d8.
Proof. vm_refl. Qed.
Lemma D_5c0d8 : decode_any W_5c0d8 = Some (Op ALU_ADD 8 8 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_5c0dc : bv 32 := 0x00e60633.
Lemma F_5c0dc : fetch_word Asan.M.loaded_segments (0x5c12c : word) = Some W_5c0dc.
Proof. vm_refl. Qed.
Lemma D_5c0dc : decode_any W_5c0dc = Some (Op ALU_ADD 12 12 14, 4%Z).
Proof. vm_refl. Qed.

Definition W_5c0e0 : bv 32 := 0xfff80d13.
Lemma F_5c0e0 : fetch_word Asan.M.loaded_segments (0x5c130 : word) = Some W_5c0e0.
Proof. vm_refl. Qed.
Lemma D_5c0e0 : decode_any W_5c0e0 = Some (OpImm ALU_ADD 26 16 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_5c0e4 : bv 32 := 0x00f60cb3.
Lemma F_5c0e4 : fetch_word Asan.M.loaded_segments (0x5c134 : word) = Some W_5c0e4.
Proof. vm_refl. Qed.
Lemma D_5c0e4 : decode_any W_5c0e4 = Some (Op ALU_ADD 25 12 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_5c0e8 : bv 32 := 0x00043683.
Lemma F_5c0e8 : fetch_word Asan.M.loaded_segments (0x5c138 : word) = Some W_5c0e8.
Proof. vm_refl. Qed.
Lemma D_5c0e8 : decode_any W_5c0e8 = Some (Load SZ8 true 13 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5c0ec : bv 32 := 0x00840713.
Lemma F_5c0ec : fetch_word Asan.M.loaded_segments (0x5c13c : word) = Some W_5c0ec.
Proof. vm_refl. Qed.
Lemma D_5c0ec : decode_any W_5c0ec = Some (OpImm ALU_ADD 14 8 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_5c0f0 : bv 32 := 0x00e13823.
Lemma F_5c0f0 : fetch_word Asan.M.loaded_segments (0x5c140 : word) = Some W_5c0f0.
Proof. vm_refl. Qed.
Lemma D_5c0f0 : decode_any W_5c0f0 = Some (Store SZ8 2 14 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_5c0f4 : bv 32 := 0x03cd9d93.
Lemma F_5c0f4 : fetch_word Asan.M.loaded_segments (0x5c144 : word) = Some W_5c0f4.
Proof. vm_refl. Qed.
Lemma D_5c0f4 : decode_any W_5c0f4 = Some (ShiftImm ALU_SLL 27 27 60, 4%Z).
Proof. vm_refl. Qed.

Definition W_5c0f8 : bv 32 := 0x5dc00893.
Lemma F_5c0f8 : fetch_word Asan.M.loaded_segments (0x5c148 : word) = Some W_5c0f8.
Proof. vm_refl. Qed.
Lemma D_5c0f8 : decode_any W_5c0f8 = Some (OpImm ALU_ADD 17 0 1500, 4%Z).
Proof. vm_refl. Qed.

Definition W_5c0fc : bv 32 := 0x03d59493.
Lemma F_5c0fc : fetch_word Asan.M.loaded_segments (0x5c14c : word) = Some W_5c0fc.
Proof. vm_refl. Qed.
Lemma D_5c0fc : decode_any W_5c0fc = Some (ShiftImm ALU_SLL 9 11 61, 4%Z).
Proof. vm_refl. Qed.

Definition W_5c100 : bv 32 := 0xfff48493.
Lemma F_5c100 : fetch_word Asan.M.loaded_segments (0x5c150 : word) = Some W_5c100.
Proof. vm_refl. Qed.
Lemma D_5c100 : decode_any W_5c100 = Some (OpImm ALU_ADD 9 9 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_5c104 : bv 32 := 0x01a6f733.
Lemma F_5c104 : fetch_word Asan.M.loaded_segments (0x5c154 : word) = Some W_5c104.
Proof. vm_refl. Qed.
Lemma D_5c104 : decode_any W_5c104 = Some (Op ALU_AND 14 13 26, 4%Z).
Proof. vm_refl. Qed.

Definition W_5c108 : bv 32 := 0x02071663.
Lemma F_5c108 : fetch_word Asan.M.loaded_segments (0x5c158 : word) = Some W_5c108.
Proof. vm_refl. Qed.
Lemma D_5c108 : decode_any W_5c108 = Some (Branch BC_NE 14 0 44, 4%Z).
Proof. vm_refl. Qed.

Definition W_5c10c : bv 32 := 0x01b6e733.
Lemma F_5c10c : fetch_word Asan.M.loaded_segments (0x5c15c : word) = Some W_5c10c.
Proof. vm_refl. Qed.
Lemma D_5c10c : decode_any W_5c10c = Some (Op ALU_OR 14 13 27, 4%Z).
Proof. vm_refl. Qed.

Definition W_5c110 : bv 32 := 0x00e5f7b3.
Lemma F_5c110 : fetch_word Asan.M.loaded_segments (0x5c160 : word) = Some W_5c110.
Proof. vm_refl. Qed.
Lemma D_5c110 : decode_any W_5c110 = Some (Op ALU_AND 15 11 14, 4%Z).
Proof. vm_refl. Qed.

Definition W_5c114 : bv 32 := 0x1604372f.
Lemma F_5c114 : fetch_word Asan.M.loaded_segments (0x5c164 : word) = Some W_5c114.
Proof. vm_refl. Qed.
Lemma D_5c114 : decode_any W_5c114 = Some (Lr AD true true 14 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_5c118 : bv 32 := 0x00d71663.
Lemma F_5c118 : fetch_word Asan.M.loaded_segments (0x5c168 : word) = Some W_5c118.
Proof. vm_refl. Qed.
Lemma D_5c118 : decode_any W_5c118 = Some (Branch BC_NE 14 13 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_5c11c : bv 32 := 0x1af4382f.
Lemma F_5c11c : fetch_word Asan.M.loaded_segments (0x5c16c : word) = Some W_5c11c.
Proof. vm_refl. Qed.
Lemma D_5c11c : decode_any W_5c11c = Some (Sc AD false true 16 8 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_5c120 : bv 32 := 0xfe081ae3.
Lemma F_5c120 : fetch_word Asan.M.loaded_segments (0x5c170 : word) = Some W_5c120.
Proof. vm_refl. Qed.
Lemma D_5c120 : decode_any W_5c120 = Some (Branch BC_NE 16 0 8180, 4%Z).
Proof. vm_refl. Qed.

Definition W_5c124 : bv 32 := 0x08d70063.
Lemma F_5c124 : fetch_word Asan.M.loaded_segments (0x5c174 : word) = Some W_5c124.
Proof. vm_refl. Qed.
Lemma D_5c124 : decode_any W_5c124 = Some (Branch BC_EQ 14 13 128, 4%Z).
Proof. vm_refl. Qed.

Definition W_5c1a4 : bv 32 := 0x01043483.
Lemma F_5c1a4 : fetch_word Asan.M.loaded_segments (0x5c1f4 : word) = Some W_5c1a4.
Proof. vm_refl. Qed.
Lemma D_5c1a4 : decode_any W_5c1a4 = Some (Load SZ8 true 9 8 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_5c1a8 : bv 32 := 0x01548bb3.
Lemma F_5c1a8 : fetch_word Asan.M.loaded_segments (0x5c1f8 : word) = Some W_5c1a8.
Proof. vm_refl. Qed.
Lemma D_5c1a8 : decode_any W_5c1a8 = Some (Op ALU_ADD 23 9 21, 4%Z).
Proof. vm_refl. Qed.

Definition W_5c1ac : bv 32 := 0x000a0513.
Lemma F_5c1ac : fetch_word Asan.M.loaded_segments (0x5c1fc : word) = Some W_5c1ac.
Proof. vm_refl. Qed.
Lemma D_5c1ac : decode_any W_5c1ac = Some (OpImm ALU_ADD 10 20 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5c1b0 : bv 32 := 0x00040593.
Lemma F_5c1b0 : fetch_word Asan.M.loaded_segments (0x5c200 : word) = Some W_5c1b0.
Proof. vm_refl. Qed.
Lemma D_5c1b0 : decode_any W_5c1b0 = Some (OpImm ALU_ADD 11 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5c1b4 : bv 32 := 0x000b8693.
Lemma F_5c1b4 : fetch_word Asan.M.loaded_segments (0x5c204 : word) = Some W_5c1b4.
Proof. vm_refl. Qed.
Lemma D_5c1b4 : decode_any W_5c1b4 = Some (OpImm ALU_ADD 13 23 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5c1b8 : bv 32 := 0x1c8000ef.
Lemma F_5c1b8 : fetch_word Asan.M.loaded_segments (0x5c208 : word) = Some W_5c1b8.
Proof. vm_refl. Qed.
Lemma D_5c1b8 : decode_any W_5c1b8 = Some (Jal 1 456, 4%Z).
Proof. vm_refl. Qed.

Definition W_5c1bc : bv 32 := 0x18050463.
Lemma F_5c1bc : fetch_word Asan.M.loaded_segments (0x5c20c : word) = Some W_5c1bc.
Proof. vm_refl. Qed.
Lemma D_5c1bc : decode_any W_5c1bc = Some (Branch BC_EQ 10 0 392, 4%Z).
Proof. vm_refl. Qed.

Definition W_5c1c0 : bv 32 := 0x020a8463.
Lemma F_5c1c0 : fetch_word Asan.M.loaded_segments (0x5c210 : word) = Some W_5c1c0.
Proof. vm_refl. Qed.
Lemma D_5c1c0 : decode_any W_5c1c0 = Some (Branch BC_EQ 21 0 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_5c1c4 : bv 32 := 0x00249493.
Lemma F_5c1c4 : fetch_word Asan.M.loaded_segments (0x5c214 : word) = Some W_5c1c4.
Proof. vm_refl. Qed.
Lemma D_5c1c4 : decode_any W_5c1c4 = Some (ShiftImm ALU_SLL 9 9 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_5c1c8 : bv 32 := 0x009c8cb3.
Lemma F_5c1c8 : fetch_word Asan.M.loaded_segments (0x5c218 : word) = Some W_5c1c8.
Proof. vm_refl. Qed.
Lemma D_5c1c8 : decode_any W_5c1c8 = Some (Op ALU_ADD 25 25 9, 4%Z).
Proof. vm_refl. Qed.

Definition W_5c1cc : bv 32 := 0x002a9513.
Lemma F_5c1cc : fetch_word Asan.M.loaded_segments (0x5c21c : word) = Some W_5c1cc.
Proof. vm_refl. Qed.
Lemma D_5c1cc : decode_any W_5c1cc = Some (ShiftImm ALU_SLL 10 21 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_5c1d0 : bv 32 := 0x00ab0533.
Lemma F_5c1d0 : fetch_word Asan.M.loaded_segments (0x5c220 : word) = Some W_5c1d0.
Proof. vm_refl. Qed.
Lemma D_5c1d0 : decode_any W_5c1d0 = Some (Op ALU_ADD 10 22 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_5c1d4 : bv 32 := 0x000b2583.
Lemma F_5c1d4 : fetch_word Asan.M.loaded_segments (0x5c224 : word) = Some W_5c1d4.
Proof. vm_refl. Qed.
Lemma D_5c1d4 : decode_any W_5c1d4 = Some (Load SZ4 true 11 22 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5c1d8 : bv 32 := 0x004b0b13.
Lemma F_5c1d8 : fetch_word Asan.M.loaded_segments (0x5c228 : word) = Some W_5c1d8.
Proof. vm_refl. Qed.
Lemma D_5c1d8 : decode_any W_5c1d8 = Some (OpImm ALU_ADD 22 22 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_5c1dc : bv 32 := 0x00bca023.
Lemma F_5c1dc : fetch_word Asan.M.loaded_segments (0x5c22c : word) = Some W_5c1dc.
Proof. vm_refl. Qed.
Lemma D_5c1dc : decode_any W_5c1dc = Some (Store SZ4 25 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5c1e0 : bv 32 := 0x004c8c93.
Lemma F_5c1e0 : fetch_word Asan.M.loaded_segments (0x5c230 : word) = Some W_5c1e0.
Proof. vm_refl. Qed.
Lemma D_5c1e0 : decode_any W_5c1e0 = Some (OpImm ALU_ADD 25 25 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_5c1e4 : bv 32 := 0xfeab18e3.
Lemma F_5c1e4 : fetch_word Asan.M.loaded_segments (0x5c234 : word) = Some W_5c1e4.
Proof. vm_refl. Qed.
Lemma D_5c1e4 : decode_any W_5c1e4 = Some (Branch BC_NE 22 10 8176, 4%Z).
Proof. vm_refl. Qed.

Definition W_5c1e8 : bv 32 := 0x05043503.
Lemma F_5c1e8 : fetch_word Asan.M.loaded_segments (0x5c238 : word) = Some W_5c1e8.
Proof. vm_refl. Qed.
Lemma D_5c1e8 : decode_any W_5c1e8 = Some (Load SZ8 true 10 8 80, 4%Z).
Proof. vm_refl. Qed.

Definition W_5c1ec : bv 32 := 0x01743823.
Lemma F_5c1ec : fetch_word Asan.M.loaded_segments (0x5c23c : word) = Some W_5c1ec.
Proof. vm_refl. Qed.
Lemma D_5c1ec : decode_any W_5c1ec = Some (Store SZ8 8 23 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_5c1f0 : bv 32 := 0x01550533.
Lemma F_5c1f0 : fetch_word Asan.M.loaded_segments (0x5c240 : word) = Some W_5c1f0.
Proof. vm_refl. Qed.
Lemma D_5c1f0 : decode_any W_5c1f0 = Some (Op ALU_ADD 10 10 21, 4%Z).
Proof. vm_refl. Qed.

Definition W_5c1f4 : bv 32 := 0x04a43823.
Lemma F_5c1f4 : fetch_word Asan.M.loaded_segments (0x5c244 : word) = Some W_5c1f4.
Proof. vm_refl. Qed.
Lemma D_5c1f4 : decode_any W_5c1f4 = Some (Store SZ8 8 10 80, 4%Z).
Proof. vm_refl. Qed.

Definition W_5c1f8 : bv 32 := 0x000a0513.
Lemma F_5c1f8 : fetch_word Asan.M.loaded_segments (0x5c248 : word) = Some W_5c1f8.
Proof. vm_refl. Qed.
Lemma D_5c1f8 : decode_any W_5c1f8 = Some (OpImm ALU_ADD 10 20 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5c1fc : bv 32 := 0x00098593.
Lemma F_5c1fc : fetch_word Asan.M.loaded_segments (0x5c24c : word) = Some W_5c1fc.
Proof. vm_refl. Qed.
Lemma D_5c1fc : decode_any W_5c1fc = Some (OpImm ALU_ADD 11 19 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5c200 : bv 32 := 0x00090613.
Lemma F_5c200 : fetch_word Asan.M.loaded_segments (0x5c250 : word) = Some W_5c200.
Proof. vm_refl. Qed.
Lemma D_5c200 : decode_any W_5c200 = Some (OpImm ALU_ADD 12 18 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5c204 : bv 32 := 0x00000693.
Lemma F_5c204 : fetch_word Asan.M.loaded_segments (0x5c254 : word) = Some W_5c204.
Proof. vm_refl. Qed.
Lemma D_5c204 : decode_any W_5c204 = Some (OpImm ALU_ADD 13 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5c208 : bv 32 := 0x2f8000ef.
Lemma F_5c208 : fetch_word Asan.M.loaded_segments (0x5c258 : word) = Some W_5c208.
Proof. vm_refl. Qed.
Lemma D_5c208 : decode_any W_5c208 = Some (Jal 1 760, 4%Z).
Proof. vm_refl. Qed.

Definition W_5c20c : bv 32 := 0x00043503.
Lemma F_5c20c : fetch_word Asan.M.loaded_segments (0x5c25c : word) = Some W_5c20c.
Proof. vm_refl. Qed.
Lemma D_5c20c : decode_any W_5c20c = Some (Load SZ8 true 10 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5c210 : bv 32 := 0xfff00813.
Lemma F_5c210 : fetch_word Asan.M.loaded_segments (0x5c260 : word) = Some W_5c210.
Proof. vm_refl. Qed.
Lemma D_5c210 : decode_any W_5c210 = Some (OpImm ALU_ADD 16 0 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_5c214 : bv 32 := 0x00300613.
Lemma F_5c214 : fetch_word Asan.M.loaded_segments (0x5c264 : word) = Some W_5c214.
Proof. vm_refl. Qed.
Lemma D_5c214 : decode_any W_5c214 = Some (OpImm ALU_ADD 12 0 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_5c218 : bv 32 := 0x001005b7.
Lemma F_5c218 : fetch_word Asan.M.loaded_segments (0x5c268 : word) = Some W_5c218.
Proof. vm_refl. Qed.
Lemma D_5c218 : decode_any W_5c218 = Some (Lui 11 256, 4%Z).
Proof. vm_refl. Qed.

Definition W_5c21c : bv 32 := 0xfffb4697.
Lemma F_5c21c : fetch_word Asan.M.loaded_segments (0x5c26c : word) = Some W_5c21c.
Proof. vm_refl. Qed.
Lemma D_5c21c : decode_any W_5c21c = Some (Auipc 13 1048500, 4%Z).
Proof. vm_refl. Qed.

Definition W_5c220 : bv 32 := 0x03c81713.
Lemma F_5c220 : fetch_word Asan.M.loaded_segments (0x5c270 : word) = Some W_5c220.
Proof. vm_refl. Qed.
Lemma D_5c220 : decode_any W_5c220 = Some (ShiftImm ALU_SLL 14 16 60, 4%Z).
Proof. vm_refl. Qed.

Definition W_5c224 : bv 32 := 0x03d61613.
Lemma F_5c224 : fetch_word Asan.M.loaded_segments (0x5c274 : word) = Some W_5c224.
Proof. vm_refl. Qed.
Lemma D_5c224 : decode_any W_5c224 = Some (ShiftImm ALU_SLL 12 12 61, 4%Z).
Proof. vm_refl. Qed.

Definition W_5c228 : bv 32 := 0xfff58593.
Lemma F_5c228 : fetch_word Asan.M.loaded_segments (0x5c278 : word) = Some W_5c228.
Proof. vm_refl. Qed.
Lemma D_5c228 : decode_any W_5c228 = Some (OpImm ALU_ADD 11 11 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_5c22c : bv 32 := 0x1d46b683.
Lemma F_5c22c : fetch_word Asan.M.loaded_segments (0x5c27c : word) = Some W_5c22c.
Proof. vm_refl. Qed.
Lemma D_5c22c : decode_any W_5c22c = Some (Load SZ8 true 13 13 468, 4%Z).
Proof. vm_refl. Qed.

Definition W_5c230 : bv 32 := 0xfff70713.
Lemma F_5c230 : fetch_word Asan.M.loaded_segments (0x5c280 : word) = Some W_5c230.
Proof. vm_refl. Qed.
Lemma D_5c230 : decode_any W_5c230 = Some (OpImm ALU_ADD 14 14 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_5c234 : bv 32 := 0x02859793.
Lemma F_5c234 : fetch_word Asan.M.loaded_segments (0x5c284 : word) = Some W_5c234.
Proof. vm_refl. Qed.
Lemma D_5c234 : decode_any W_5c234 = Some (ShiftImm ALU_SLL 15 11 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_5c238 : bv 32 := 0x02881813.
Lemma F_5c238 : fetch_word Asan.M.loaded_segments (0x5c288 : word) = Some W_5c238.
Proof. vm_refl. Qed.
Lemma D_5c238 : decode_any W_5c238 = Some (ShiftImm ALU_SLL 16 16 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_5c23c : bv 32 := 0x00100893.
Lemma F_5c23c : fetch_word Asan.M.loaded_segments (0x5c28c : word) = Some W_5c23c.
Proof. vm_refl. Qed.
Lemma D_5c23c : decode_any W_5c23c = Some (OpImm ALU_ADD 17 0 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_5c240 : bv 32 := 0x03e89893.
Lemma F_5c240 : fetch_word Asan.M.loaded_segments (0x5c290 : word) = Some W_5c240.
Proof. vm_refl. Qed.
Lemma D_5c240 : decode_any W_5c240 = Some (ShiftImm ALU_SLL 17 17 62, 4%Z).
Proof. vm_refl. Qed.

Definition W_5c244 : bv 32 := 0x01c0006f.
Lemma F_5c244 : fetch_word Asan.M.loaded_segments (0x5c294 : word) = Some W_5c244.
Proof. vm_refl. Qed.
Lemma D_5c244 : decode_any W_5c244 = Some (Jal 0 28, 4%Z).
Proof. vm_refl. Qed.

Definition W_5c248 : bv 32 := 0x1604332f.
Lemma F_5c248 : fetch_word Asan.M.loaded_segments (0x5c298 : word) = Some W_5c248.
Proof. vm_refl. Qed.
Lemma D_5c248 : decode_any W_5c248 = Some (Lr AD true true 6 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_5c24c : bv 32 := 0x00a31663.
Lemma F_5c24c : fetch_word Asan.M.loaded_segments (0x5c29c : word) = Some W_5c24c.
Proof. vm_refl. Qed.
Lemma D_5c24c : decode_any W_5c24c = Some (Branch BC_NE 6 10 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_5c250 : bv 32 := 0x1a5433af.
Lemma F_5c250 : fetch_word Asan.M.loaded_segments (0x5c2a0 : word) = Some W_5c250.
Proof. vm_refl. Qed.
Lemma D_5c250 : decode_any W_5c250 = Some (Sc AD false true 7 8 5, 4%Z).
Proof. vm_refl. Qed.

Definition W_5c254 : bv 32 := 0xfe039ae3.
Lemma F_5c254 : fetch_word Asan.M.loaded_segments (0x5c2a4 : word) = Some W_5c254.
Proof. vm_refl. Qed.
Lemma D_5c254 : decode_any W_5c254 = Some (Branch BC_NE 7 0 8180, 4%Z).
Proof. vm_refl. Qed.

Definition W_5c258 : bv 32 := 0x06a30463.
Lemma F_5c258 : fetch_word Asan.M.loaded_segments (0x5c2a8 : word) = Some W_5c258.
Proof. vm_refl. Qed.
Lemma D_5c258 : decode_any W_5c258 = Some (Branch BC_EQ 6 10 104, 4%Z).
Proof. vm_refl. Qed.

Definition W_5c260 : bv 32 := 0x00c575b3.
Lemma F_5c260 : fetch_word Asan.M.loaded_segments (0x5c2b0 : word) = Some W_5c260.
Proof. vm_refl. Qed.
Lemma D_5c260 : decode_any W_5c260 = Some (Op ALU_AND 11 10 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_5c264 : bv 32 := 0x00e572b3.
Lemma F_5c264 : fetch_word Asan.M.loaded_segments (0x5c2b4 : word) = Some W_5c264.
Proof. vm_refl. Qed.
Lemma D_5c264 : decode_any W_5c264 = Some (Op ALU_AND 5 10 14, 4%Z).
Proof. vm_refl. Qed.

Definition W_5c268 : bv 32 := 0x02059663.
Lemma F_5c268 : fetch_word Asan.M.loaded_segments (0x5c2b8 : word) = Some W_5c268.
Proof. vm_refl. Qed.
Lemma D_5c268 : decode_any W_5c268 = Some (Branch BC_NE 11 0 44, 4%Z).
Proof. vm_refl. Qed.

Definition W_5c26c : bv 32 := 0x00f575b3.
Lemma F_5c26c : fetch_word Asan.M.loaded_segments (0x5c2bc : word) = Some W_5c26c.
Proof. vm_refl. Qed.
Lemma D_5c26c : decode_any W_5c26c = Some (Op ALU_AND 11 10 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_5c270 : bv 32 := 0x02058263.
Lemma F_5c270 : fetch_word Asan.M.loaded_segments (0x5c2c0 : word) = Some W_5c270.
Proof. vm_refl. Qed.
Lemma D_5c270 : decode_any W_5c270 = Some (Branch BC_EQ 11 0 36, 4%Z).
Proof. vm_refl. Qed.

Definition W_5c294 : bv 32 := 0x018575b3.
Lemma F_5c294 : fetch_word Asan.M.loaded_segments (0x5c2e4 : word) = Some W_5c294.
Proof. vm_refl. Qed.
Lemma D_5c294 : decode_any W_5c294 = Some (Op ALU_AND 11 10 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_5c298 : bv 32 := 0x00b035b3.
Lemma F_5c298 : fetch_word Asan.M.loaded_segments (0x5c2e8 : word) = Some W_5c298.
Proof. vm_refl. Qed.
Lemma D_5c298 : decode_any W_5c298 = Some (Op ALU_SLTU 11 0 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_5c29c : bv 32 := 0x01455313.
Lemma F_5c29c : fetch_word Asan.M.loaded_segments (0x5c2ec : word) = Some W_5c29c.
Proof. vm_refl. Qed.
Lemma D_5c29c : decode_any W_5c29c = Some (ShiftImm ALU_SRL 6 10 20, 4%Z).
Proof. vm_refl. Qed.

Definition W_5c2a0 : bv 32 := 0xfff58593.
Lemma F_5c2a0 : fetch_word Asan.M.loaded_segments (0x5c2f0 : word) = Some W_5c2a0.
Proof. vm_refl. Qed.
Lemma D_5c2a0 : decode_any W_5c2a0 = Some (OpImm ALU_ADD 11 11 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_5c2a4 : bv 32 := 0x00b375b3.
Lemma F_5c2a4 : fetch_word Asan.M.loaded_segments (0x5c2f4 : word) = Some W_5c2a4.
Proof. vm_refl. Qed.
Lemma D_5c2a4 : decode_any W_5c2a4 = Some (Op ALU_AND 11 6 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_5c2a8 : bv 32 := 0x02c59593.
Lemma F_5c2a8 : fetch_word Asan.M.loaded_segments (0x5c2f8 : word) = Some W_5c2a8.
Proof. vm_refl. Qed.
Lemma D_5c2a8 : decode_any W_5c2a8 = Some (ShiftImm ALU_SLL 11 11 44, 4%Z).
Proof. vm_refl. Qed.

Definition W_5c2ac : bv 32 := 0x02c5d593.
Lemma F_5c2ac : fetch_word Asan.M.loaded_segments (0x5c2fc : word) = Some W_5c2ac.
Proof. vm_refl. Qed.
Lemma D_5c2ac : decode_any W_5c2ac = Some (ShiftImm ALU_SRL 11 11 44, 4%Z).
Proof. vm_refl. Qed.

Definition W_5c2b0 : bv 32 := 0xf8058ce3.
Lemma F_5c2b0 : fetch_word Asan.M.loaded_segments (0x5c300 : word) = Some W_5c2b0.
Proof. vm_refl. Qed.
Lemma D_5c2b0 : decode_any W_5c2b0 = Some (Branch BC_EQ 11 0 8088, 4%Z).
Proof. vm_refl. Qed.

Definition W_5c2c0 : bv 32 := 0x0a059c63.
Lemma F_5c2c0 : fetch_word Asan.M.loaded_segments (0x5c310 : word) = Some W_5c2c0.
Proof. vm_refl. Qed.
Lemma D_5c2c0 : decode_any W_5c2c0 = Some (Branch BC_NE 11 0 184, 4%Z).
Proof. vm_refl. Qed.

Definition W_5c2c4 : bv 32 := 0x07813083.
Lemma F_5c2c4 : fetch_word Asan.M.loaded_segments (0x5c314 : word) = Some W_5c2c4.
Proof. vm_refl. Qed.
Lemma D_5c2c4 : decode_any W_5c2c4 = Some (Load SZ8 true 1 2 120, 4%Z).
Proof. vm_refl. Qed.

Definition W_5c2c8 : bv 32 := 0x07013403.
Lemma F_5c2c8 : fetch_word Asan.M.loaded_segments (0x5c318 : word) = Some W_5c2c8.
Proof. vm_refl. Qed.
Lemma D_5c2c8 : decode_any W_5c2c8 = Some (Load SZ8 true 8 2 112, 4%Z).
Proof. vm_refl. Qed.

Definition W_5c2cc : bv 32 := 0x06813483.
Lemma F_5c2cc : fetch_word Asan.M.loaded_segments (0x5c31c : word) = Some W_5c2cc.
Proof. vm_refl. Qed.
Lemma D_5c2cc : decode_any W_5c2cc = Some (Load SZ8 true 9 2 104, 4%Z).
Proof. vm_refl. Qed.

Definition W_5c2d0 : bv 32 := 0x06013903.
Lemma F_5c2d0 : fetch_word Asan.M.loaded_segments (0x5c320 : word) = Some W_5c2d0.
Proof. vm_refl. Qed.
Lemma D_5c2d0 : decode_any W_5c2d0 = Some (Load SZ8 true 18 2 96, 4%Z).
Proof. vm_refl. Qed.

Definition W_5c2d4 : bv 32 := 0x05813983.
Lemma F_5c2d4 : fetch_word Asan.M.loaded_segments (0x5c324 : word) = Some W_5c2d4.
Proof. vm_refl. Qed.
Lemma D_5c2d4 : decode_any W_5c2d4 = Some (Load SZ8 true 19 2 88, 4%Z).
Proof. vm_refl. Qed.

Definition W_5c2d8 : bv 32 := 0x05013a03.
Lemma F_5c2d8 : fetch_word Asan.M.loaded_segments (0x5c328 : word) = Some W_5c2d8.
Proof. vm_refl. Qed.
Lemma D_5c2d8 : decode_any W_5c2d8 = Some (Load SZ8 true 20 2 80, 4%Z).
Proof. vm_refl. Qed.

Definition W_5c2dc : bv 32 := 0x04813a83.
Lemma F_5c2dc : fetch_word Asan.M.loaded_segments (0x5c32c : word) = Some W_5c2dc.
Proof. vm_refl. Qed.
Lemma D_5c2dc : decode_any W_5c2dc = Some (Load SZ8 true 21 2 72, 4%Z).
Proof. vm_refl. Qed.

Definition W_5c2e0 : bv 32 := 0x04013b03.
Lemma F_5c2e0 : fetch_word Asan.M.loaded_segments (0x5c330 : word) = Some W_5c2e0.
Proof. vm_refl. Qed.
Lemma D_5c2e0 : decode_any W_5c2e0 = Some (Load SZ8 true 22 2 64, 4%Z).
Proof. vm_refl. Qed.

Definition W_5c2e4 : bv 32 := 0x03813b83.
Lemma F_5c2e4 : fetch_word Asan.M.loaded_segments (0x5c334 : word) = Some W_5c2e4.
Proof. vm_refl. Qed.
Lemma D_5c2e4 : decode_any W_5c2e4 = Some (Load SZ8 true 23 2 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_5c2e8 : bv 32 := 0x03013c03.
Lemma F_5c2e8 : fetch_word Asan.M.loaded_segments (0x5c338 : word) = Some W_5c2e8.
Proof. vm_refl. Qed.
Lemma D_5c2e8 : decode_any W_5c2e8 = Some (Load SZ8 true 24 2 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_5c2ec : bv 32 := 0x02813c83.
Lemma F_5c2ec : fetch_word Asan.M.loaded_segments (0x5c33c : word) = Some W_5c2ec.
Proof. vm_refl. Qed.
Lemma D_5c2ec : decode_any W_5c2ec = Some (Load SZ8 true 25 2 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_5c2f0 : bv 32 := 0x02013d03.
Lemma F_5c2f0 : fetch_word Asan.M.loaded_segments (0x5c340 : word) = Some W_5c2f0.
Proof. vm_refl. Qed.
Lemma D_5c2f0 : decode_any W_5c2f0 = Some (Load SZ8 true 26 2 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_5c2f4 : bv 32 := 0x01813d83.
Lemma F_5c2f4 : fetch_word Asan.M.loaded_segments (0x5c344 : word) = Some W_5c2f4.
Proof. vm_refl. Qed.
Lemma D_5c2f4 : decode_any W_5c2f4 = Some (Load SZ8 true 27 2 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_5c2f8 : bv 32 := 0x08010113.
Lemma F_5c2f8 : fetch_word Asan.M.loaded_segments (0x5c348 : word) = Some W_5c2f8.
Proof. vm_refl. Qed.
Lemma D_5c2f8 : decode_any W_5c2f8 = Some (OpImm ALU_ADD 2 2 128, 4%Z).
Proof. vm_refl. Qed.

Definition W_5c2fc : bv 32 := 0x00008067.
Lemma F_5c2fc : fetch_word Asan.M.loaded_segments (0x5c34c : word) = Some W_5c2fc.
Proof. vm_refl. Qed.
Lemma D_5c2fc : decode_any W_5c2fc = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5c380 : bv 32 := 0xfd010113.
Lemma F_5c380 : fetch_word Asan.M.loaded_segments (0x5c3d0 : word) = Some W_5c380.
Proof. vm_refl. Qed.
Lemma D_5c380 : decode_any W_5c380 = Some (OpImm ALU_ADD 2 2 4048, 4%Z).
Proof. vm_refl. Qed.

Definition W_5c384 : bv 32 := 0x02113423.
Lemma F_5c384 : fetch_word Asan.M.loaded_segments (0x5c3d4 : word) = Some W_5c384.
Proof. vm_refl. Qed.
Lemma D_5c384 : decode_any W_5c384 = Some (Store SZ8 2 1 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_5c388 : bv 32 := 0x02813023.
Lemma F_5c388 : fetch_word Asan.M.loaded_segments (0x5c3d8 : word) = Some W_5c388.
Proof. vm_refl. Qed.
Lemma D_5c388 : decode_any W_5c388 = Some (Store SZ8 2 8 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_5c38c : bv 32 := 0x00913c23.
Lemma F_5c38c : fetch_word Asan.M.loaded_segments (0x5c3dc : word) = Some W_5c38c.
Proof. vm_refl. Qed.
Lemma D_5c38c : decode_any W_5c38c = Some (Store SZ8 2 9 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_5c390 : bv 32 := 0x01213823.
Lemma F_5c390 : fetch_word Asan.M.loaded_segments (0x5c3e0 : word) = Some W_5c390.
Proof. vm_refl. Qed.
Lemma D_5c390 : decode_any W_5c390 = Some (Store SZ8 2 18 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_5c394 : bv 32 := 0x01313423.
Lemma F_5c394 : fetch_word Asan.M.loaded_segments (0x5c3e4 : word) = Some W_5c394.
Proof. vm_refl. Qed.
Lemma D_5c394 : decode_any W_5c394 = Some (Store SZ8 2 19 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_5c398 : bv 32 := 0x0185b703.
Lemma F_5c398 : fetch_word Asan.M.loaded_segments (0x5c3e8 : word) = Some W_5c398.
Proof. vm_refl. Qed.
Lemma D_5c398 : decode_any W_5c398 = Some (Load SZ8 true 14 11 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_5c39c : bv 32 := 0x00269793.
Lemma F_5c39c : fetch_word Asan.M.loaded_segments (0x5c3ec : word) = Some W_5c39c.
Proof. vm_refl. Qed.
Lemma D_5c39c : decode_any W_5c39c = Some (ShiftImm ALU_SLL 15 13 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_5c3a0 : bv 32 := 0x00100693.
Lemma F_5c3a0 : fetch_word Asan.M.loaded_segments (0x5c3f0 : word) = Some W_5c3a0.
Proof. vm_refl. Qed.
Lemma D_5c3a0 : decode_any W_5c3a0 = Some (OpImm ALU_ADD 13 0 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_5c3a4 : bv 32 := 0x0cf77063.
Lemma F_5c3a4 : fetch_word Asan.M.loaded_segments (0x5c3f4 : word) = Some W_5c3a4.
Proof. vm_refl. Qed.
Lemma D_5c3a4 : decode_any W_5c3a4 = Some (Branch BC_GEU 14 15 192, 4%Z).
Proof. vm_refl. Qed.

Definition W_5c3a8 : bv 32 := 0x000406b7.
Lemma F_5c3a8 : fetch_word Asan.M.loaded_segments (0x5c3f8 : word) = Some W_5c3a8.
Proof. vm_refl. Qed.
Lemma D_5c3a8 : decode_any W_5c3a8 = Some (Lui 13 64, 4%Z).
Proof. vm_refl. Qed.

Definition W_5c3ac : bv 32 := 0xfff6869b.
Lemma F_5c3ac : fetch_word Asan.M.loaded_segments (0x5c3fc : word) = Some W_5c3ac.
Proof. vm_refl. Qed.
Lemma D_5c3ac : decode_any W_5c3ac = Some (OpImm32 13 13 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_5c3b0 : bv 32 := 0x00d786b3.
Lemma F_5c3b0 : fetch_word Asan.M.loaded_segments (0x5c400 : word) = Some W_5c3b0.
Proof. vm_refl. Qed.
Lemma D_5c3b0 : decode_any W_5c3b0 = Some (Op ALU_ADD 13 15 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_5c3b4 : bv 32 := 0xfffc0437.
Lemma F_5c3b4 : fetch_word Asan.M.loaded_segments (0x5c404 : word) = Some W_5c3b4.
Proof. vm_refl. Qed.
Lemma D_5c3b4 : decode_any W_5c3b4 = Some (Lui 8 1048512, 4%Z).
Proof. vm_refl. Qed.

Definition W_5c3b8 : bv 32 := 0x0086f433.
Lemma F_5c3b8 : fetch_word Asan.M.loaded_segments (0x5c408 : word) = Some W_5c3b8.
Proof. vm_refl. Qed.
Lemma D_5c3b8 : decode_any W_5c3b8 = Some (Op ALU_AND 8 13 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_5c3bc : bv 32 := 0x200006b7.
Lemma F_5c3bc : fetch_word Asan.M.loaded_segments (0x5c40c : word) = Some W_5c3bc.
Proof. vm_refl. Qed.
Lemma D_5c3bc : decode_any W_5c3bc = Some (Lui 13 131072, 4%Z).
Proof. vm_refl. Qed.

Definition W_5c3c0 : bv 32 := 0x0016869b.
Lemma F_5c3c0 : fetch_word Asan.M.loaded_segments (0x5c410 : word) = Some W_5c3c0.
Proof. vm_refl. Qed.
Lemma D_5c3c0 : decode_any W_5c3c0 = Some (OpImm32 13 13 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_5c3c4 : bv 32 := 0x0cd47063.
Lemma F_5c3c4 : fetch_word Asan.M.loaded_segments (0x5c414 : word) = Some W_5c3c4.
Proof. vm_refl. Qed.
Lemma D_5c3c4 : decode_any W_5c3c4 = Some (Branch BC_GEU 8 13 192, 4%Z).
Proof. vm_refl. Qed.

Definition W_5c3c8 : bv 32 := 0x03854683.
Lemma F_5c3c8 : fetch_word Asan.M.loaded_segments (0x5c418 : word) = Some W_5c3c8.
Proof. vm_refl. Qed.
Lemma D_5c3c8 : decode_any W_5c3c8 = Some (Load SZ1 false 13 10 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_5c3cc : bv 32 := 0x00700793.
Lemma F_5c3cc : fetch_word Asan.M.loaded_segments (0x5c41c : word) = Some W_5c3cc.
Proof. vm_refl. Qed.
Lemma D_5c3cc : decode_any W_5c3cc = Some (OpImm ALU_ADD 15 0 7, 4%Z).
Proof. vm_refl. Qed.

Definition W_5c3d0 : bv 32 := 0x01d79793.
Lemma F_5c3d0 : fetch_word Asan.M.loaded_segments (0x5c420 : word) = Some W_5c3d0.
Proof. vm_refl. Qed.
Lemma D_5c3d0 : decode_any W_5c3d0 = Some (ShiftImm ALU_SLL 15 15 29, 4%Z).
Proof. vm_refl. Qed.

Definition W_5c3d4 : bv 32 := 0x00f60633.
Lemma F_5c3d4 : fetch_word Asan.M.loaded_segments (0x5c424 : word) = Some W_5c3d4.
Proof. vm_refl. Qed.
Lemma D_5c3d4 : decode_any W_5c3d4 = Some (Op ALU_ADD 12 12 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_5c3d8 : bv 32 := 0x00c704b3.
Lemma F_5c3d8 : fetch_word Asan.M.loaded_segments (0x5c428 : word) = Some W_5c3d8.
Proof. vm_refl. Qed.
Lemma D_5c3d8 : decode_any W_5c3d8 = Some (Op ALU_ADD 9 14 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_5c3dc : bv 32 := 0x02068463.
Lemma F_5c3dc : fetch_word Asan.M.loaded_segments (0x5c42c : word) = Some W_5c3dc.
Proof. vm_refl. Qed.
Lemma D_5c3dc : decode_any W_5c3dc = Some (Branch BC_EQ 13 0 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_5c404 : bv 32 := 0x00058993.
Lemma F_5c404 : fetch_word Asan.M.loaded_segments (0x5c454 : word) = Some W_5c404.
Proof. vm_refl. Qed.
Lemma D_5c404 : decode_any W_5c404 = Some (OpImm ALU_ADD 19 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5c408 : bv 32 := 0x40e40933.
Lemma F_5c408 : fetch_word Asan.M.loaded_segments (0x5c458 : word) = Some W_5c408.
Proof. vm_refl. Qed.
Lemma D_5c408 : decode_any W_5c408 = Some (Op ALU_SUB 18 8 14, 4%Z).
Proof. vm_refl. Qed.

Definition W_5c40c : bv 32 := 0xfffbe597.
Lemma F_5c40c : fetch_word Asan.M.loaded_segments (0x5c45c : word) = Some W_5c40c.
Proof. vm_refl. Qed.
Lemma D_5c40c : decode_any W_5c40c = Some (Auipc 11 1048510, 4%Z).
Proof. vm_refl. Qed.

Definition W_5c410 : bv 32 := 0x9fd58693.
Lemma F_5c410 : fetch_word Asan.M.loaded_segments (0x5c460 : word) = Some W_5c410.
Proof. vm_refl. Qed.
Lemma D_5c410 : decode_any W_5c410 = Some (OpImm ALU_ADD 13 11 2557, 4%Z).
Proof. vm_refl. Qed.

Definition W_5c414 : bv 32 := 0x00048593.
Lemma F_5c414 : fetch_word Asan.M.loaded_segments (0x5c464 : word) = Some W_5c414.
Proof. vm_refl. Qed.
Lemma D_5c414 : decode_any W_5c414 = Some (OpImm ALU_ADD 11 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5c418 : bv 32 := 0x00090613.
Lemma F_5c418 : fetch_word Asan.M.loaded_segments (0x5c468 : word) = Some W_5c418.
Proof. vm_refl. Qed.
Lemma D_5c418 : decode_any W_5c418 = Some (OpImm ALU_ADD 12 18 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5c41c : bv 32 := 0x141400ef.
Lemma F_5c41c : fetch_word Asan.M.loaded_segments (0x5c46c : word) = Some W_5c41c.
Proof. vm_refl. Qed.
Lemma D_5c41c : decode_any W_5c41c = Some (Jal 1 264512, 4%Z).
Proof. vm_refl. Qed.

Definition W_5c420 : bv 32 := 0x08050263.
Lemma F_5c420 : fetch_word Asan.M.loaded_segments (0x5c470 : word) = Some W_5c420.
Proof. vm_refl. Qed.
Lemma D_5c420 : decode_any W_5c420 = Some (Branch BC_EQ 10 0 132, 4%Z).
Proof. vm_refl. Qed.

Definition W_5c424 : bv 32 := 0x00050713.
Lemma F_5c424 : fetch_word Asan.M.loaded_segments (0x5c474 : word) = Some W_5c424.
Proof. vm_refl. Qed.
Lemma D_5c424 : decode_any W_5c424 = Some (OpImm ALU_ADD 14 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5c428 : bv 32 := 0x08a49263.
Lemma F_5c428 : fetch_word Asan.M.loaded_segments (0x5c478 : word) = Some W_5c428.
Proof. vm_refl. Qed.
Lemma D_5c428 : decode_any W_5c428 = Some (Branch BC_NE 9 10 132, 4%Z).
Proof. vm_refl. Qed.

Definition W_5c42c : bv 32 := 0x0fa00613.
Lemma F_5c42c : fetch_word Asan.M.loaded_segments (0x5c47c : word) = Some W_5c42c.
Proof. vm_refl. Qed.
Lemma D_5c42c : decode_any W_5c42c = Some (OpImm ALU_ADD 12 0 250, 4%Z).
Proof. vm_refl. Qed.

Definition W_5c430 : bv 32 := 0x00048513.
Lemma F_5c430 : fetch_word Asan.M.loaded_segments (0x5c480 : word) = Some W_5c430.
Proof. vm_refl. Qed.
Lemma D_5c430 : decode_any W_5c430 = Some (OpImm ALU_ADD 10 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5c434 : bv 32 := 0x00090593.
Lemma F_5c434 : fetch_word Asan.M.loaded_segments (0x5c484 : word) = Some W_5c434.
Proof. vm_refl. Qed.
Lemma D_5c434 : decode_any W_5c434 = Some (OpImm ALU_ADD 11 18 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5c438 : bv 32 := 0x091250ef.
Lemma F_5c438 : fetch_word Asan.M.loaded_segments (0x5c488 : word) = Some W_5c438.
Proof. vm_refl. Qed.
Lemma D_5c438 : decode_any W_5c438 = Some (Jal 1 153744, 4%Z).
Proof. vm_refl. Qed.

Definition W_5c43c : bv 32 := 0x0052d0ef.
Lemma F_5c43c : fetch_word Asan.M.loaded_segments (0x5c48c : word) = Some W_5c43c.
Proof. vm_refl. Qed.
Lemma D_5c43c : decode_any W_5c43c = Some (Jal 1 186372, 4%Z).
Proof. vm_refl. Qed.

Definition W_5c440 : bv 32 := 0x05053583.
Lemma F_5c440 : fetch_word Asan.M.loaded_segments (0x5c490 : word) = Some W_5c440.
Proof. vm_refl. Qed.
Lemma D_5c440 : decode_any W_5c440 = Some (Load SZ8 true 11 10 80, 4%Z).
Proof. vm_refl. Qed.

Definition W_5c444 : bv 32 := 0x04853603.
Lemma F_5c444 : fetch_word Asan.M.loaded_segments (0x5c494 : word) = Some W_5c444.
Proof. vm_refl. Qed.
Lemma D_5c444 : decode_any W_5c444 = Some (Load SZ8 true 12 10 72, 4%Z).
Proof. vm_refl. Qed.

Definition W_5c448 : bv 32 := 0x012585b3.
Lemma F_5c448 : fetch_word Asan.M.loaded_segments (0x5c498 : word) = Some W_5c448.
Proof. vm_refl. Qed.
Lemma D_5c448 : decode_any W_5c448 = Some (Op ALU_ADD 11 11 18, 4%Z).
Proof. vm_refl. Qed.

Definition W_5c44c : bv 32 := 0x00160613.
Lemma F_5c44c : fetch_word Asan.M.loaded_segments (0x5c49c : word) = Some W_5c44c.
Proof. vm_refl. Qed.
Lemma D_5c44c : decode_any W_5c44c = Some (OpImm ALU_ADD 12 12 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_5c450 : bv 32 := 0x04c53423.
Lemma F_5c450 : fetch_word Asan.M.loaded_segments (0x5c4a0 : word) = Some W_5c450.
Proof. vm_refl. Qed.
Lemma D_5c450 : decode_any W_5c450 = Some (Store SZ8 10 12 72, 4%Z).
Proof. vm_refl. Qed.

Definition W_5c454 : bv 32 := 0x04b53823.
Lemma F_5c454 : fetch_word Asan.M.loaded_segments (0x5c4a4 : word) = Some W_5c454.
Proof. vm_refl. Qed.
Lemma D_5c454 : decode_any W_5c454 = Some (Store SZ8 10 11 80, 4%Z).
Proof. vm_refl. Qed.

Definition W_5c458 : bv 32 := 0x00098593.
Lemma F_5c458 : fetch_word Asan.M.loaded_segments (0x5c4a8 : word) = Some W_5c458.
Proof. vm_refl. Qed.
Lemma D_5c458 : decode_any W_5c458 = Some (OpImm ALU_ADD 11 19 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5c45c : bv 32 := 0x0085bc23.
Lemma F_5c45c : fetch_word Asan.M.loaded_segments (0x5c4ac : word) = Some W_5c45c.
Proof. vm_refl. Qed.
Lemma D_5c45c : decode_any W_5c45c = Some (Store SZ8 11 8 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_5c460 : bv 32 := 0x00100693.
Lemma F_5c460 : fetch_word Asan.M.loaded_segments (0x5c4b0 : word) = Some W_5c460.
Proof. vm_refl. Qed.
Lemma D_5c460 : decode_any W_5c460 = Some (OpImm ALU_ADD 13 0 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_5c464 : bv 32 := 0x00068513.
Lemma F_5c464 : fetch_word Asan.M.loaded_segments (0x5c4b4 : word) = Some W_5c464.
Proof. vm_refl. Qed.
Lemma D_5c464 : decode_any W_5c464 = Some (OpImm ALU_ADD 10 13 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5c468 : bv 32 := 0x02813083.
Lemma F_5c468 : fetch_word Asan.M.loaded_segments (0x5c4b8 : word) = Some W_5c468.
Proof. vm_refl. Qed.
Lemma D_5c468 : decode_any W_5c468 = Some (Load SZ8 true 1 2 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_5c46c : bv 32 := 0x02013403.
Lemma F_5c46c : fetch_word Asan.M.loaded_segments (0x5c4bc : word) = Some W_5c46c.
Proof. vm_refl. Qed.
Lemma D_5c46c : decode_any W_5c46c = Some (Load SZ8 true 8 2 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_5c470 : bv 32 := 0x01813483.
Lemma F_5c470 : fetch_word Asan.M.loaded_segments (0x5c4c0 : word) = Some W_5c470.
Proof. vm_refl. Qed.
Lemma D_5c470 : decode_any W_5c470 = Some (Load SZ8 true 9 2 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_5c474 : bv 32 := 0x01013903.
Lemma F_5c474 : fetch_word Asan.M.loaded_segments (0x5c4c4 : word) = Some W_5c474.
Proof. vm_refl. Qed.
Lemma D_5c474 : decode_any W_5c474 = Some (Load SZ8 true 18 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_5c478 : bv 32 := 0x00813983.
Lemma F_5c478 : fetch_word Asan.M.loaded_segments (0x5c4c8 : word) = Some W_5c478.
Proof. vm_refl. Qed.
Lemma D_5c478 : decode_any W_5c478 = Some (Load SZ8 true 19 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_5c47c : bv 32 := 0x03010113.
Lemma F_5c47c : fetch_word Asan.M.loaded_segments (0x5c4cc : word) = Some W_5c47c.
Proof. vm_refl. Qed.
Lemma D_5c47c : decode_any W_5c47c = Some (OpImm ALU_ADD 2 2 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_5c480 : bv 32 := 0x00008067.
Lemma F_5c480 : fetch_word Asan.M.loaded_segments (0x5c4d0 : word) = Some W_5c480.
Proof. vm_refl. Qed.
Lemma D_5c480 : decode_any W_5c480 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5c500 : bv 32 := 0xfb010113.
Lemma F_5c500 : fetch_word Asan.M.loaded_segments (0x5c550 : word) = Some W_5c500.
Proof. vm_refl. Qed.
Lemma D_5c500 : decode_any W_5c500 = Some (OpImm ALU_ADD 2 2 4016, 4%Z).
Proof. vm_refl. Qed.

Definition W_5c504 : bv 32 := 0x04113423.
Lemma F_5c504 : fetch_word Asan.M.loaded_segments (0x5c554 : word) = Some W_5c504.
Proof. vm_refl. Qed.
Lemma D_5c504 : decode_any W_5c504 = Some (Store SZ8 2 1 72, 4%Z).
Proof. vm_refl. Qed.

Definition W_5c508 : bv 32 := 0x04813023.
Lemma F_5c508 : fetch_word Asan.M.loaded_segments (0x5c558 : word) = Some W_5c508.
Proof. vm_refl. Qed.
Lemma D_5c508 : decode_any W_5c508 = Some (Store SZ8 2 8 64, 4%Z).
Proof. vm_refl. Qed.

Definition W_5c50c : bv 32 := 0x02913c23.
Lemma F_5c50c : fetch_word Asan.M.loaded_segments (0x5c55c : word) = Some W_5c50c.
Proof. vm_refl. Qed.
Lemma D_5c50c : decode_any W_5c50c = Some (Store SZ8 2 9 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_5c510 : bv 32 := 0x03213823.
Lemma F_5c510 : fetch_word Asan.M.loaded_segments (0x5c560 : word) = Some W_5c510.
Proof. vm_refl. Qed.
Lemma D_5c510 : decode_any W_5c510 = Some (Store SZ8 2 18 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_5c514 : bv 32 := 0x03313423.
Lemma F_5c514 : fetch_word Asan.M.loaded_segments (0x5c564 : word) = Some W_5c514.
Proof. vm_refl. Qed.
Lemma D_5c514 : decode_any W_5c514 = Some (Store SZ8 2 19 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_5c518 : bv 32 := 0x03413023.
Lemma F_5c518 : fetch_word Asan.M.loaded_segments (0x5c568 : word) = Some W_5c518.
Proof. vm_refl. Qed.
Lemma D_5c518 : decode_any W_5c518 = Some (Store SZ8 2 20 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_5c51c : bv 32 := 0x01513c23.
Lemma F_5c51c : fetch_word Asan.M.loaded_segments (0x5c56c : word) = Some W_5c51c.
Proof. vm_refl. Qed.
Lemma D_5c51c : decode_any W_5c51c = Some (Store SZ8 2 21 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_5c520 : bv 32 := 0x01613823.
Lemma F_5c520 : fetch_word Asan.M.loaded_segments (0x5c570 : word) = Some W_5c520.
Proof. vm_refl. Qed.
Lemma D_5c520 : decode_any W_5c520 = Some (Store SZ8 2 22 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_5c524 : bv 32 := 0x01713423.
Lemma F_5c524 : fetch_word Asan.M.loaded_segments (0x5c574 : word) = Some W_5c524.
Proof. vm_refl. Qed.
Lemma D_5c524 : decode_any W_5c524 = Some (Store SZ8 2 23 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_5c528 : bv 32 := 0x00068a93.
Lemma F_5c528 : fetch_word Asan.M.loaded_segments (0x5c578 : word) = Some W_5c528.
Proof. vm_refl. Qed.
Lemma D_5c528 : decode_any W_5c528 = Some (OpImm ALU_ADD 21 13 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5c52c : bv 32 := 0x00060493.
Lemma F_5c52c : fetch_word Asan.M.loaded_segments (0x5c57c : word) = Some W_5c52c.
Proof. vm_refl. Qed.
Lemma D_5c52c : decode_any W_5c52c = Some (OpImm ALU_ADD 9 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5c530 : bv 32 := 0x00058413.
Lemma F_5c530 : fetch_word Asan.M.loaded_segments (0x5c580 : word) = Some W_5c530.
Proof. vm_refl. Qed.
Lemma D_5c530 : decode_any W_5c530 = Some (OpImm ALU_ADD 8 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5c534 : bv 32 := 0x00050993.
Lemma F_5c534 : fetch_word Asan.M.loaded_segments (0x5c584 : word) = Some W_5c534.
Proof. vm_refl. Qed.
Lemma D_5c534 : decode_any W_5c534 = Some (OpImm ALU_ADD 19 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5c538 : bv 32 := 0x03053b03.
Lemma F_5c538 : fetch_word Asan.M.loaded_segments (0x5c588 : word) = Some W_5c538.
Proof. vm_refl. Qed.
Lemma D_5c538 : decode_any W_5c538 = Some (Load SZ8 true 22 10 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_5c53c : bv 32 := 0x01f00513.
Lemma F_5c53c : fetch_word Asan.M.loaded_segments (0x5c58c : word) = Some W_5c53c.
Proof. vm_refl. Qed.
Lemma D_5c53c : decode_any W_5c53c = Some (OpImm ALU_ADD 10 0 31, 4%Z).
Proof. vm_refl. Qed.

Definition W_5c540 : bv 32 := 0x00761593.
Lemma F_5c540 : fetch_word Asan.M.loaded_segments (0x5c590 : word) = Some W_5c540.
Proof. vm_refl. Qed.
Lemma D_5c540 : decode_any W_5c540 = Some (ShiftImm ALU_SLL 11 12 7, 4%Z).
Proof. vm_refl. Qed.

Definition W_5c544 : bv 32 := 0x18a60863.
Lemma F_5c544 : fetch_word Asan.M.loaded_segments (0x5c594 : word) = Some W_5c544.
Proof. vm_refl. Qed.
Lemma D_5c544 : decode_any W_5c544 = Some (Branch BC_EQ 12 10 400, 4%Z).
Proof. vm_refl. Qed.

Definition W_5c548 : bv 32 := 0x01000513.
Lemma F_5c548 : fetch_word Asan.M.loaded_segments (0x5c598 : word) = Some W_5c548.
Proof. vm_refl. Qed.
Lemma D_5c548 : decode_any W_5c548 = Some (OpImm ALU_ADD 10 0 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_5c54c : bv 32 := 0x00956663.
Lemma F_5c54c : fetch_word Asan.M.loaded_segments (0x5c59c : word) = Some W_5c54c.
Proof. vm_refl. Qed.
Lemma D_5c54c : decode_any W_5c54c = Some (Branch BC_LTU 10 9 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_5c550 : bv 32 := 0x00549913.
Lemma F_5c550 : fetch_word Asan.M.loaded_segments (0x5c5a0 : word) = Some W_5c550.
Proof. vm_refl. Qed.
Lemma D_5c550 : decode_any W_5c550 = Some (ShiftImm ALU_SLL 18 9 5, 4%Z).
Proof. vm_refl. Qed.

Definition W_5c554 : bv 32 := 0x0280006f.
Lemma F_5c554 : fetch_word Asan.M.loaded_segments (0x5c5a4 : word) = Some W_5c554.
Proof. vm_refl. Qed.
Lemma D_5c554 : decode_any W_5c554 = Some (Jal 0 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_5c558 : bv 32 := 0xff048513.
Lemma F_5c558 : fetch_word Asan.M.loaded_segments (0x5c5a8 : word) = Some W_5c558.
Proof. vm_refl. Qed.
Lemma D_5c558 : decode_any W_5c558 = Some (OpImm ALU_ADD 10 9 4080, 4%Z).
Proof. vm_refl. Qed.

Definition W_5c55c : bv 32 := 0x20000613.
Lemma F_5c55c : fetch_word Asan.M.loaded_segments (0x5c5ac : word) = Some W_5c55c.
Proof. vm_refl. Qed.
Lemma D_5c55c : decode_any W_5c55c = Some (OpImm ALU_ADD 12 0 512, 4%Z).
Proof. vm_refl. Qed.

Definition W_5c560 : bv 32 := 0x03f49693.
Lemma F_5c560 : fetch_word Asan.M.loaded_segments (0x5c5b0 : word) = Some W_5c560.
Proof. vm_refl. Qed.
Lemma D_5c560 : decode_any W_5c560 = Some (ShiftImm ALU_SLL 13 9 63, 4%Z).
Proof. vm_refl. Qed.

Definition W_5c564 : bv 32 := 0x00155513.
Lemma F_5c564 : fetch_word Asan.M.loaded_segments (0x5c5b4 : word) = Some W_5c564.
Proof. vm_refl. Qed.
Lemma D_5c564 : decode_any W_5c564 = Some (ShiftImm ALU_SRL 10 10 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_5c568 : bv 32 := 0x00a61933.
Lemma F_5c568 : fetch_word Asan.M.loaded_segments (0x5c5b8 : word) = Some W_5c568.
Proof. vm_refl. Qed.
Lemma D_5c568 : decode_any W_5c568 = Some (Op ALU_SLL 18 12 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_5c56c : bv 32 := 0x00195513.
Lemma F_5c56c : fetch_word Asan.M.loaded_segments (0x5c5bc : word) = Some W_5c56c.
Proof. vm_refl. Qed.
Lemma D_5c56c : decode_any W_5c56c = Some (ShiftImm ALU_SRL 10 18 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_5c570 : bv 32 := 0x43f6d693.
Lemma F_5c570 : fetch_word Asan.M.loaded_segments (0x5c5c0 : word) = Some W_5c570.
Proof. vm_refl. Qed.
Lemma D_5c570 : decode_any W_5c570 = Some (ShiftImm ALU_SRA 13 13 63, 4%Z).
Proof. vm_refl. Qed.

Definition W_5c574 : bv 32 := 0x00a6f533.
Lemma F_5c574 : fetch_word Asan.M.loaded_segments (0x5c5c4 : word) = Some W_5c574.
Proof. vm_refl. Qed.
Lemma D_5c574 : decode_any W_5c574 = Some (Op ALU_AND 10 13 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_5c578 : bv 32 := 0x01250933.
Lemma F_5c578 : fetch_word Asan.M.loaded_segments (0x5c5c8 : word) = Some W_5c578.
Proof. vm_refl. Qed.
Lemma D_5c578 : decode_any W_5c578 = Some (Op ALU_ADD 18 10 18, 4%Z).
Proof. vm_refl. Qed.

Definition W_5c57c : bv 32 := 0x000f7517.
Lemma F_5c57c : fetch_word Asan.M.loaded_segments (0x5c5cc : word) = Some W_5c57c.
Proof. vm_refl. Qed.
Lemma D_5c57c : decode_any W_5c57c = Some (Auipc 10 247, 4%Z).
Proof. vm_refl. Qed.

Definition W_5c580 : bv 32 := 0xb4c53a03.
Lemma F_5c580 : fetch_word Asan.M.loaded_segments (0x5c5d0 : word) = Some W_5c580.
Proof. vm_refl. Qed.
Lemma D_5c580 : decode_any W_5c580 = Some (Load SZ8 true 20 10 2892, 4%Z).
Proof. vm_refl. Qed.

Definition W_5c584 : bv 32 := 0x000a3503.
Lemma F_5c584 : fetch_word Asan.M.loaded_segments (0x5c5d4 : word) = Some W_5c584.
Proof. vm_refl. Qed.
Lemma D_5c584 : decode_any W_5c584 = Some (Load SZ8 true 10 20 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5c588 : bv 32 := 0x00bb0b33.
Lemma F_5c588 : fetch_word Asan.M.loaded_segments (0x5c5d8 : word) = Some W_5c588.
Proof. vm_refl. Qed.
Lemma D_5c588 : decode_any W_5c588 = Some (Op ALU_ADD 22 22 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_5c58c : bv 32 := 0x00050a63.
Lemma F_5c58c : fetch_word Asan.M.loaded_segments (0x5c5dc : word) = Some W_5c58c.
Proof. vm_refl. Qed.
Lemma D_5c58c : decode_any W_5c58c = Some (Branch BC_EQ 10 0 20, 4%Z).
Proof. vm_refl. Qed.

Definition W_5c590 : bv 32 := 0x010b3a03.
Lemma F_5c590 : fetch_word Asan.M.loaded_segments (0x5c5e0 : word) = Some W_5c590.
Proof. vm_refl. Qed.
Lemma D_5c590 : decode_any W_5c590 = Some (Load SZ8 true 20 22 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_5c594 : bv 32 := 0x032a05b3.
Lemma F_5c594 : fetch_word Asan.M.loaded_segments (0x5c5e4 : word) = Some W_5c594.
Proof. vm_refl. Qed.
Lemma D_5c594 : decode_any W_5c594 = Some (Mul M_MUL 11 20 18, 4%Z).
Proof. vm_refl. Qed.

Definition W_5c598 : bv 32 := 0x00a5fe63.
Lemma F_5c598 : fetch_word Asan.M.loaded_segments (0x5c5e8 : word) = Some W_5c598.
Proof. vm_refl. Qed.
Lemma D_5c598 : decode_any W_5c598 = Some (Branch BC_GEU 11 10 28, 4%Z).
Proof. vm_refl. Qed.

Definition W_5c59c : bv 32 := 0x10c0006f.
Lemma F_5c59c : fetch_word Asan.M.loaded_segments (0x5c5ec : word) = Some W_5c59c.
Proof. vm_refl. Qed.
Lemma D_5c59c : decode_any W_5c59c = Some (Jal 0 268, 4%Z).
Proof. vm_refl. Qed.

Definition W_5c5b4 : bv 32 := 0x050b3583.
Lemma F_5c5b4 : fetch_word Asan.M.loaded_segments (0x5c604 : word) = Some W_5c5b4.
Proof. vm_refl. Qed.
Lemma D_5c5b4 : decode_any W_5c5b4 = Some (Load SZ8 true 11 22 80, 4%Z).
Proof. vm_refl. Qed.

Definition W_5c5b8 : bv 32 := 0x058b3603.
Lemma F_5c5b8 : fetch_word Asan.M.loaded_segments (0x5c608 : word) = Some W_5c5b8.
Proof. vm_refl. Qed.
Lemma D_5c5b8 : decode_any W_5c5b8 = Some (Load SZ8 true 12 22 88, 4%Z).
Proof. vm_refl. Qed.

Definition W_5c5bc : bv 32 := 0x40c585b3.
Lemma F_5c5bc : fetch_word Asan.M.loaded_segments (0x5c60c : word) = Some W_5c5bc.
Proof. vm_refl. Qed.
Lemma D_5c5bc : decode_any W_5c5bc = Some (Op ALU_SUB 11 11 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_5c5c0 : bv 32 := 0x032585b3.
Lemma F_5c5c0 : fetch_word Asan.M.loaded_segments (0x5c610 : word) = Some W_5c5c0.
Proof. vm_refl. Qed.
Lemma D_5c5c0 : decode_any W_5c5c0 = Some (Mul M_MUL 11 11 18, 4%Z).
Proof. vm_refl. Qed.

Definition W_5c5c4 : bv 32 := 0x0ea5e263.
Lemma F_5c5c4 : fetch_word Asan.M.loaded_segments (0x5c614 : word) = Some W_5c5c4.
Proof. vm_refl. Qed.
Lemma D_5c5c4 : decode_any W_5c5c4 = Some (Branch BC_LTU 11 10 228, 4%Z).
Proof. vm_refl. Qed.

Definition W_5c5c8 : bv 32 := 0x020a9a63.
Lemma F_5c5c8 : fetch_word Asan.M.loaded_segments (0x5c618 : word) = Some W_5c5c8.
Proof. vm_refl. Qed.
Lemma D_5c5c8 : decode_any W_5c5c8 = Some (Branch BC_NE 21 0 52, 4%Z).
Proof. vm_refl. Qed.

Definition W_5c5cc : bv 32 := 0x0289a583.
Lemma F_5c5cc : fetch_word Asan.M.loaded_segments (0x5c61c : word) = Some W_5c5cc.
Proof. vm_refl. Qed.
Lemma D_5c5cc : decode_any W_5c5cc = Some (Load SZ4 true 11 19 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_5c5d0 : bv 32 := 0x0c05cc63.
Lemma F_5c5d0 : fetch_word Asan.M.loaded_segments (0x5c620 : word) = Some W_5c5d0.
Proof. vm_refl. Qed.
Lemma D_5c5d0 : decode_any W_5c5d0 = Some (Branch BC_LT 11 0 216, 4%Z).
Proof. vm_refl. Qed.

Definition W_5c6a8 : bv 32 := 0x04813083.
Lemma F_5c6a8 : fetch_word Asan.M.loaded_segments (0x5c6f8 : word) = Some W_5c6a8.
Proof. vm_refl. Qed.
Lemma D_5c6a8 : decode_any W_5c6a8 = Some (Load SZ8 true 1 2 72, 4%Z).
Proof. vm_refl. Qed.

Definition W_5c6ac : bv 32 := 0x04013403.
Lemma F_5c6ac : fetch_word Asan.M.loaded_segments (0x5c6fc : word) = Some W_5c6ac.
Proof. vm_refl. Qed.
Lemma D_5c6ac : decode_any W_5c6ac = Some (Load SZ8 true 8 2 64, 4%Z).
Proof. vm_refl. Qed.

Definition W_5c6b0 : bv 32 := 0x03813483.
Lemma F_5c6b0 : fetch_word Asan.M.loaded_segments (0x5c700 : word) = Some W_5c6b0.
Proof. vm_refl. Qed.
Lemma D_5c6b0 : decode_any W_5c6b0 = Some (Load SZ8 true 9 2 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_5c6b4 : bv 32 := 0x03013903.
Lemma F_5c6b4 : fetch_word Asan.M.loaded_segments (0x5c704 : word) = Some W_5c6b4.
Proof. vm_refl. Qed.
Lemma D_5c6b4 : decode_any W_5c6b4 = Some (Load SZ8 true 18 2 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_5c6b8 : bv 32 := 0x02813983.
Lemma F_5c6b8 : fetch_word Asan.M.loaded_segments (0x5c708 : word) = Some W_5c6b8.
Proof. vm_refl. Qed.
Lemma D_5c6b8 : decode_any W_5c6b8 = Some (Load SZ8 true 19 2 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_5c6bc : bv 32 := 0x02013a03.
Lemma F_5c6bc : fetch_word Asan.M.loaded_segments (0x5c70c : word) = Some W_5c6bc.
Proof. vm_refl. Qed.
Lemma D_5c6bc : decode_any W_5c6bc = Some (Load SZ8 true 20 2 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_5c6c0 : bv 32 := 0x01813a83.
Lemma F_5c6c0 : fetch_word Asan.M.loaded_segments (0x5c710 : word) = Some W_5c6c0.
Proof. vm_refl. Qed.
Lemma D_5c6c0 : decode_any W_5c6c0 = Some (Load SZ8 true 21 2 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_5c6c4 : bv 32 := 0x01013b03.
Lemma F_5c6c4 : fetch_word Asan.M.loaded_segments (0x5c714 : word) = Some W_5c6c4.
Proof. vm_refl. Qed.
Lemma D_5c6c4 : decode_any W_5c6c4 = Some (Load SZ8 true 22 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_5c6c8 : bv 32 := 0x00813b83.
Lemma F_5c6c8 : fetch_word Asan.M.loaded_segments (0x5c718 : word) = Some W_5c6c8.
Proof. vm_refl. Qed.
Lemma D_5c6c8 : decode_any W_5c6c8 = Some (Load SZ8 true 23 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_5c6cc : bv 32 := 0x05010113.
Lemma F_5c6cc : fetch_word Asan.M.loaded_segments (0x5c71c : word) = Some W_5c6cc.
Proof. vm_refl. Qed.
Lemma D_5c6cc : decode_any W_5c6cc = Some (OpImm ALU_ADD 2 2 80, 4%Z).
Proof. vm_refl. Qed.

Definition W_5c6d0 : bv 32 := 0x00008067.
Lemma F_5c6d0 : fetch_word Asan.M.loaded_segments (0x5c720 : word) = Some W_5c6d0.
Proof. vm_refl. Qed.
Lemma D_5c6d0 : decode_any W_5c6d0 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

