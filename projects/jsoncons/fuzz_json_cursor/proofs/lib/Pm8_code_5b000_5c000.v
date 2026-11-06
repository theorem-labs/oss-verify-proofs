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

Definition W_5b0d8 : bv 32 := 0xfd010113.
Lemma F_5b0d8 : fetch_word Asan.M.loaded_segments (0x5b128 : word) = Some W_5b0d8.
Proof. vm_refl. Qed.
Lemma D_5b0d8 : decode_any W_5b0d8 = Some (OpImm ALU_ADD 2 2 4048, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b0dc : bv 32 := 0x02113423.
Lemma F_5b0dc : fetch_word Asan.M.loaded_segments (0x5b12c : word) = Some W_5b0dc.
Proof. vm_refl. Qed.
Lemma D_5b0dc : decode_any W_5b0dc = Some (Store SZ8 2 1 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b0e0 : bv 32 := 0x02813023.
Lemma F_5b0e0 : fetch_word Asan.M.loaded_segments (0x5b130 : word) = Some W_5b0e0.
Proof. vm_refl. Qed.
Lemma D_5b0e0 : decode_any W_5b0e0 = Some (Store SZ8 2 8 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b0e4 : bv 32 := 0x00913c23.
Lemma F_5b0e4 : fetch_word Asan.M.loaded_segments (0x5b134 : word) = Some W_5b0e4.
Proof. vm_refl. Qed.
Lemma D_5b0e4 : decode_any W_5b0e4 = Some (Store SZ8 2 9 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b0e8 : bv 32 := 0x01213823.
Lemma F_5b0e8 : fetch_word Asan.M.loaded_segments (0x5b138 : word) = Some W_5b0e8.
Proof. vm_refl. Qed.
Lemma D_5b0e8 : decode_any W_5b0e8 = Some (Store SZ8 2 18 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b0ec : bv 32 := 0x01313423.
Lemma F_5b0ec : fetch_word Asan.M.loaded_segments (0x5b13c : word) = Some W_5b0ec.
Proof. vm_refl. Qed.
Lemma D_5b0ec : decode_any W_5b0ec = Some (Store SZ8 2 19 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b0f0 : bv 32 := 0x09850713.
Lemma F_5b0f0 : fetch_word Asan.M.loaded_segments (0x5b140 : word) = Some W_5b0f0.
Proof. vm_refl. Qed.
Lemma D_5b0f0 : decode_any W_5b0f0 = Some (OpImm ALU_ADD 14 10 152, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b0f4 : bv 32 := 0x0ff00793.
Lemma F_5b0f4 : fetch_word Asan.M.loaded_segments (0x5b144 : word) = Some W_5b0f4.
Proof. vm_refl. Qed.
Lemma D_5b0f4 : decode_any W_5b0f4 = Some (OpImm ALU_ADD 15 0 255, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b0f8 : bv 32 := 0xffc77813.
Lemma F_5b0f8 : fetch_word Asan.M.loaded_segments (0x5b148 : word) = Some W_5b0f8.
Proof. vm_refl. Qed.
Lemma D_5b0f8 : decode_any W_5b0f8 = Some (OpImm ALU_AND 16 14 4092, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b0fc : bv 32 := 0x00100893.
Lemma F_5b0fc : fetch_word Asan.M.loaded_segments (0x5b14c : word) = Some W_5b0fc.
Proof. vm_refl. Qed.
Lemma D_5b0fc : decode_any W_5b0fc = Some (OpImm ALU_ADD 17 0 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b100 : bv 32 := 0x140822af.
Lemma F_5b100 : fetch_word Asan.M.loaded_segments (0x5b150 : word) = Some W_5b100.
Proof. vm_refl. Qed.
Lemma D_5b100 : decode_any W_5b100 = Some (Lr AW true false 5 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b104 : bv 32 := 0x00088313.
Lemma F_5b104 : fetch_word Asan.M.loaded_segments (0x5b154 : word) = Some W_5b104.
Proof. vm_refl. Qed.
Lemma D_5b104 : decode_any W_5b104 = Some (OpImm ALU_ADD 6 17 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b108 : bv 32 := 0x0062c333.
Lemma F_5b108 : fetch_word Asan.M.loaded_segments (0x5b158 : word) = Some W_5b108.
Proof. vm_refl. Qed.
Lemma D_5b108 : decode_any W_5b108 = Some (Op ALU_XOR 6 5 6, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b10c : bv 32 := 0x00f37333.
Lemma F_5b10c : fetch_word Asan.M.loaded_segments (0x5b15c : word) = Some W_5b10c.
Proof. vm_refl. Qed.
Lemma D_5b10c : decode_any W_5b10c = Some (Op ALU_AND 6 6 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b110 : bv 32 := 0x0062c333.
Lemma F_5b110 : fetch_word Asan.M.loaded_segments (0x5b160 : word) = Some W_5b110.
Proof. vm_refl. Qed.
Lemma D_5b110 : decode_any W_5b110 = Some (Op ALU_XOR 6 5 6, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b114 : bv 32 := 0x1868232f.
Lemma F_5b114 : fetch_word Asan.M.loaded_segments (0x5b164 : word) = Some W_5b114.
Proof. vm_refl. Qed.
Lemma D_5b114 : decode_any W_5b114 = Some (Sc AW false false 6 16 6, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b118 : bv 32 := 0xfe0314e3.
Lemma F_5b118 : fetch_word Asan.M.loaded_segments (0x5b168 : word) = Some W_5b118.
Proof. vm_refl. Qed.
Lemma D_5b118 : decode_any W_5b118 = Some (Branch BC_NE 6 0 8168, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b11c : bv 32 := 0x0ff2f793.
Lemma F_5b11c : fetch_word Asan.M.loaded_segments (0x5b16c : word) = Some W_5b11c.
Proof. vm_refl. Qed.
Lemma D_5b11c : decode_any W_5b11c = Some (OpImm ALU_AND 15 5 255, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b120 : bv 32 := 0x10079663.
Lemma F_5b120 : fetch_word Asan.M.loaded_segments (0x5b170 : word) = Some W_5b120.
Proof. vm_refl. Qed.
Lemma D_5b120 : decode_any W_5b120 = Some (Branch BC_NE 15 0 268, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b124 : bv 32 := 0x0a050713.
Lemma F_5b124 : fetch_word Asan.M.loaded_segments (0x5b174 : word) = Some W_5b124.
Proof. vm_refl. Qed.
Lemma D_5b124 : decode_any W_5b124 = Some (OpImm ALU_ADD 14 10 160, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b128 : bv 32 := 0x12b70a63.
Lemma F_5b128 : fetch_word Asan.M.loaded_segments (0x5b178 : word) = Some W_5b128.
Proof. vm_refl. Qed.
Lemma D_5b128 : decode_any W_5b128 = Some (Branch BC_EQ 14 11 308, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b12c : bv 32 := 0x0005b783.
Lemma F_5b12c : fetch_word Asan.M.loaded_segments (0x5b17c : word) = Some W_5b12c.
Proof. vm_refl. Qed.
Lemma D_5b12c : decode_any W_5b12c = Some (Load SZ8 true 15 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b130 : bv 32 := 0x04078863.
Lemma F_5b130 : fetch_word Asan.M.loaded_segments (0x5b180 : word) = Some W_5b130.
Proof. vm_refl. Qed.
Lemma D_5b130 : decode_any W_5b130 = Some (Branch BC_EQ 15 0 80, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b134 : bv 32 := 0x00073803.
Lemma F_5b134 : fetch_word Asan.M.loaded_segments (0x5b184 : word) = Some W_5b134.
Proof. vm_refl. Qed.
Lemma D_5b134 : decode_any W_5b134 = Some (Load SZ8 true 16 14 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b138 : bv 32 := 0x02080263.
Lemma F_5b138 : fetch_word Asan.M.loaded_segments (0x5b188 : word) = Some W_5b138.
Proof. vm_refl. Qed.
Lemma D_5b138 : decode_any W_5b138 = Some (Branch BC_EQ 16 0 36, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b13c : bv 32 := 0x0b053703.
Lemma F_5b13c : fetch_word Asan.M.loaded_segments (0x5b18c : word) = Some W_5b13c.
Proof. vm_refl. Qed.
Lemma D_5b13c : decode_any W_5b13c = Some (Load SZ8 true 14 10 176, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b140 : bv 32 := 0x0085b883.
Lemma F_5b140 : fetch_word Asan.M.loaded_segments (0x5b190 : word) = Some W_5b140.
Proof. vm_refl. Qed.
Lemma D_5b140 : decode_any W_5b140 = Some (Load SZ8 true 17 11 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b144 : bv 32 := 0x0105b283.
Lemma F_5b144 : fetch_word Asan.M.loaded_segments (0x5b194 : word) = Some W_5b144.
Proof. vm_refl. Qed.
Lemma D_5b144 : decode_any W_5b144 = Some (Load SZ8 true 5 11 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b148 : bv 32 := 0x00f807b3.
Lemma F_5b148 : fetch_word Asan.M.loaded_segments (0x5b198 : word) = Some W_5b148.
Proof. vm_refl. Qed.
Lemma D_5b148 : decode_any W_5b148 = Some (Op ALU_ADD 15 16 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b14c : bv 32 := 0x01173023.
Lemma F_5b14c : fetch_word Asan.M.loaded_segments (0x5b19c : word) = Some W_5b14c.
Proof. vm_refl. Qed.
Lemma D_5b14c : decode_any W_5b14c = Some (Store SZ8 14 17 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b150 : bv 32 := 0x0af53023.
Lemma F_5b150 : fetch_word Asan.M.loaded_segments (0x5b1a0 : word) = Some W_5b150.
Proof. vm_refl. Qed.
Lemma D_5b150 : decode_any W_5b150 = Some (Store SZ8 10 15 160, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b154 : bv 32 := 0x0a553823.
Lemma F_5b154 : fetch_word Asan.M.loaded_segments (0x5b1a4 : word) = Some W_5b154.
Proof. vm_refl. Qed.
Lemma D_5b154 : decode_any W_5b154 = Some (Store SZ8 10 5 176, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b158 : bv 32 := 0x01c0006f.
Lemma F_5b158 : fetch_word Asan.M.loaded_segments (0x5b1a8 : word) = Some W_5b158.
Proof. vm_refl. Qed.
Lemma D_5b158 : decode_any W_5b158 = Some (Jal 0 28, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b15c : bv 32 := 0x0105b783.
Lemma F_5b15c : fetch_word Asan.M.loaded_segments (0x5b1ac : word) = Some W_5b15c.
Proof. vm_refl. Qed.
Lemma D_5b15c : decode_any W_5b15c = Some (Load SZ8 true 15 11 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b160 : bv 32 := 0x00f73823.
Lemma F_5b160 : fetch_word Asan.M.loaded_segments (0x5b1b0 : word) = Some W_5b160.
Proof. vm_refl. Qed.
Lemma D_5b160 : decode_any W_5b160 = Some (Store SZ8 14 15 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b164 : bv 32 := 0x0085b783.
Lemma F_5b164 : fetch_word Asan.M.loaded_segments (0x5b1b4 : word) = Some W_5b164.
Proof. vm_refl. Qed.
Lemma D_5b164 : decode_any W_5b164 = Some (Load SZ8 true 15 11 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b168 : bv 32 := 0x00f73423.
Lemma F_5b168 : fetch_word Asan.M.loaded_segments (0x5b1b8 : word) = Some W_5b168.
Proof. vm_refl. Qed.
Lemma D_5b168 : decode_any W_5b168 = Some (Store SZ8 14 15 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b16c : bv 32 := 0x0005b783.
Lemma F_5b16c : fetch_word Asan.M.loaded_segments (0x5b1bc : word) = Some W_5b16c.
Proof. vm_refl. Qed.
Lemma D_5b16c : decode_any W_5b16c = Some (Load SZ8 true 15 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b170 : bv 32 := 0x00f73023.
Lemma F_5b170 : fetch_word Asan.M.loaded_segments (0x5b1c0 : word) = Some W_5b170.
Proof. vm_refl. Qed.
Lemma D_5b170 : decode_any W_5b170 = Some (Store SZ8 14 15 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b174 : bv 32 := 0x0005b023.
Lemma F_5b174 : fetch_word Asan.M.loaded_segments (0x5b1c4 : word) = Some W_5b174.
Proof. vm_refl. Qed.
Lemma D_5b174 : decode_any W_5b174 = Some (Store SZ8 11 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b178 : bv 32 := 0x0005b423.
Lemma F_5b178 : fetch_word Asan.M.loaded_segments (0x5b1c8 : word) = Some W_5b178.
Proof. vm_refl. Qed.
Lemma D_5b178 : decode_any W_5b178 = Some (Store SZ8 11 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b17c : bv 32 := 0x0005b823.
Lemma F_5b17c : fetch_word Asan.M.loaded_segments (0x5b1cc : word) = Some W_5b17c.
Proof. vm_refl. Qed.
Lemma D_5b17c : decode_any W_5b17c = Some (Store SZ8 11 0 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b180 : bv 32 := 0x0185b703.
Lemma F_5b180 : fetch_word Asan.M.loaded_segments (0x5b1d0 : word) = Some W_5b180.
Proof. vm_refl. Qed.
Lemma D_5b180 : decode_any W_5b180 = Some (Load SZ8 true 14 11 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b184 : bv 32 := 0x0b853783.
Lemma F_5b184 : fetch_word Asan.M.loaded_segments (0x5b1d4 : word) = Some W_5b184.
Proof. vm_refl. Qed.
Lemma D_5b184 : decode_any W_5b184 = Some (Load SZ8 true 15 10 184, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b188 : bv 32 := 0x00e78733.
Lemma F_5b188 : fetch_word Asan.M.loaded_segments (0x5b1d8 : word) = Some W_5b188.
Proof. vm_refl. Qed.
Lemma D_5b188 : decode_any W_5b188 = Some (Op ALU_ADD 14 15 14, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b18c : bv 32 := 0x0ae53c23.
Lemma F_5b18c : fetch_word Asan.M.loaded_segments (0x5b1dc : word) = Some W_5b18c.
Proof. vm_refl. Qed.
Lemma D_5b18c : decode_any W_5b18c = Some (Store SZ8 10 14 184, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b190 : bv 32 := 0x0005bc23.
Lemma F_5b190 : fetch_word Asan.M.loaded_segments (0x5b1e0 : word) = Some W_5b190.
Proof. vm_refl. Qed.
Lemma D_5b190 : decode_any W_5b190 = Some (Store SZ8 11 0 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b194 : bv 32 := 0x0310000f.
Lemma F_5b194 : fetch_word Asan.M.loaded_segments (0x5b1e4 : word) = Some W_5b194.
Proof. vm_refl. Qed.
Lemma D_5b194 : decode_any W_5b194 = Some (Fence 0 3 1 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b198 : bv 32 := 0x08050c23.
Lemma F_5b198 : fetch_word Asan.M.loaded_segments (0x5b1e8 : word) = Some W_5b198.
Proof. vm_refl. Qed.
Lemma D_5b198 : decode_any W_5b198 = Some (Store SZ1 10 0 152, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b19c : bv 32 := 0x0b853583.
Lemma F_5b19c : fetch_word Asan.M.loaded_segments (0x5b1ec : word) = Some W_5b19c.
Proof. vm_refl. Qed.
Lemma D_5b19c : decode_any W_5b19c = Some (Load SZ8 true 11 10 184, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b1a0 : bv 32 := 0x04053703.
Lemma F_5b1a0 : fetch_word Asan.M.loaded_segments (0x5b1f0 : word) = Some W_5b1a0.
Proof. vm_refl. Qed.
Lemma D_5b1a0 : decode_any W_5b1a0 = Some (Load SZ8 true 14 10 64, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b1a4 : bv 32 := 0x04b77663.
Lemma F_5b1a4 : fetch_word Asan.M.loaded_segments (0x5b1f4 : word) = Some W_5b1a4.
Proof. vm_refl. Qed.
Lemma D_5b1a4 : decode_any W_5b1a4 = Some (Branch BC_GEU 14 11 76, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b1a8 : bv 32 := 0x09950593.
Lemma F_5b1a8 : fetch_word Asan.M.loaded_segments (0x5b1f8 : word) = Some W_5b1a8.
Proof. vm_refl. Qed.
Lemma D_5b1a8 : decode_any W_5b1a8 = Some (OpImm ALU_ADD 11 10 153, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b1ac : bv 32 := 0x0ff00713.
Lemma F_5b1ac : fetch_word Asan.M.loaded_segments (0x5b1fc : word) = Some W_5b1ac.
Proof. vm_refl. Qed.
Lemma D_5b1ac : decode_any W_5b1ac = Some (OpImm ALU_ADD 14 0 255, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b1b0 : bv 32 := 0x00100793.
Lemma F_5b1b0 : fetch_word Asan.M.loaded_segments (0x5b200 : word) = Some W_5b1b0.
Proof. vm_refl. Qed.
Lemma D_5b1b0 : decode_any W_5b1b0 = Some (OpImm ALU_ADD 15 0 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b1b4 : bv 32 := 0xffc5f813.
Lemma F_5b1b4 : fetch_word Asan.M.loaded_segments (0x5b204 : word) = Some W_5b1b4.
Proof. vm_refl. Qed.
Lemma D_5b1b4 : decode_any W_5b1b4 = Some (OpImm ALU_AND 16 11 4092, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b1b8 : bv 32 := 0x0035f593.
Lemma F_5b1b8 : fetch_word Asan.M.loaded_segments (0x5b208 : word) = Some W_5b1b8.
Proof. vm_refl. Qed.
Lemma D_5b1b8 : decode_any W_5b1b8 = Some (OpImm ALU_AND 11 11 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b1bc : bv 32 := 0x00359593.
Lemma F_5b1bc : fetch_word Asan.M.loaded_segments (0x5b20c : word) = Some W_5b1bc.
Proof. vm_refl. Qed.
Lemma D_5b1bc : decode_any W_5b1bc = Some (ShiftImm ALU_SLL 11 11 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b1c0 : bv 32 := 0x00b7173b.
Lemma F_5b1c0 : fetch_word Asan.M.loaded_segments (0x5b210 : word) = Some W_5b1c0.
Proof. vm_refl. Qed.
Lemma D_5b1c0 : decode_any W_5b1c0 = Some (Op32 ALU_SLL 14 14 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b1c4 : bv 32 := 0x00b797bb.
Lemma F_5b1c4 : fetch_word Asan.M.loaded_segments (0x5b214 : word) = Some W_5b1c4.
Proof. vm_refl. Qed.
Lemma D_5b1c4 : decode_any W_5b1c4 = Some (Op32 ALU_SLL 15 15 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b1c8 : bv 32 := 0x140828af.
Lemma F_5b1c8 : fetch_word Asan.M.loaded_segments (0x5b218 : word) = Some W_5b1c8.
Proof. vm_refl. Qed.
Lemma D_5b1c8 : decode_any W_5b1c8 = Some (Lr AW true false 17 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b1cc : bv 32 := 0x00078293.
Lemma F_5b1cc : fetch_word Asan.M.loaded_segments (0x5b21c : word) = Some W_5b1cc.
Proof. vm_refl. Qed.
Lemma D_5b1cc : decode_any W_5b1cc = Some (OpImm ALU_ADD 5 15 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b1d0 : bv 32 := 0x0058c2b3.
Lemma F_5b1d0 : fetch_word Asan.M.loaded_segments (0x5b220 : word) = Some W_5b1d0.
Proof. vm_refl. Qed.
Lemma D_5b1d0 : decode_any W_5b1d0 = Some (Op ALU_XOR 5 17 5, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b1d4 : bv 32 := 0x00e2f2b3.
Lemma F_5b1d4 : fetch_word Asan.M.loaded_segments (0x5b224 : word) = Some W_5b1d4.
Proof. vm_refl. Qed.
Lemma D_5b1d4 : decode_any W_5b1d4 = Some (Op ALU_AND 5 5 14, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b1d8 : bv 32 := 0x0058c2b3.
Lemma F_5b1d8 : fetch_word Asan.M.loaded_segments (0x5b228 : word) = Some W_5b1d8.
Proof. vm_refl. Qed.
Lemma D_5b1d8 : decode_any W_5b1d8 = Some (Op ALU_XOR 5 17 5, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b1dc : bv 32 := 0x185822af.
Lemma F_5b1dc : fetch_word Asan.M.loaded_segments (0x5b22c : word) = Some W_5b1dc.
Proof. vm_refl. Qed.
Lemma D_5b1dc : decode_any W_5b1dc = Some (Sc AW false false 5 16 5, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b1e0 : bv 32 := 0xfe0294e3.
Lemma F_5b1e0 : fetch_word Asan.M.loaded_segments (0x5b230 : word) = Some W_5b1e0.
Proof. vm_refl. Qed.
Lemma D_5b1e0 : decode_any W_5b1e0 = Some (Branch BC_NE 5 0 8168, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b1e4 : bv 32 := 0x00b8d5bb.
Lemma F_5b1e4 : fetch_word Asan.M.loaded_segments (0x5b234 : word) = Some W_5b1e4.
Proof. vm_refl. Qed.
Lemma D_5b1e4 : decode_any W_5b1e4 = Some (Op32 ALU_SRL 11 17 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b1e8 : bv 32 := 0x0ff5f593.
Lemma F_5b1e8 : fetch_word Asan.M.loaded_segments (0x5b238 : word) = Some W_5b1e8.
Proof. vm_refl. Qed.
Lemma D_5b1e8 : decode_any W_5b1e8 = Some (OpImm ALU_AND 11 11 255, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b1ec : bv 32 := 0x02058063.
Lemma F_5b1ec : fetch_word Asan.M.loaded_segments (0x5b23c : word) = Some W_5b1ec.
Proof. vm_refl. Qed.
Lemma D_5b1ec : decode_any W_5b1ec = Some (Branch BC_EQ 11 0 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b1f0 : bv 32 := 0x02813083.
Lemma F_5b1f0 : fetch_word Asan.M.loaded_segments (0x5b240 : word) = Some W_5b1f0.
Proof. vm_refl. Qed.
Lemma D_5b1f0 : decode_any W_5b1f0 = Some (Load SZ8 true 1 2 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b1f4 : bv 32 := 0x02013403.
Lemma F_5b1f4 : fetch_word Asan.M.loaded_segments (0x5b244 : word) = Some W_5b1f4.
Proof. vm_refl. Qed.
Lemma D_5b1f4 : decode_any W_5b1f4 = Some (Load SZ8 true 8 2 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b1f8 : bv 32 := 0x01813483.
Lemma F_5b1f8 : fetch_word Asan.M.loaded_segments (0x5b248 : word) = Some W_5b1f8.
Proof. vm_refl. Qed.
Lemma D_5b1f8 : decode_any W_5b1f8 = Some (Load SZ8 true 9 2 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b1fc : bv 32 := 0x01013903.
Lemma F_5b1fc : fetch_word Asan.M.loaded_segments (0x5b24c : word) = Some W_5b1fc.
Proof. vm_refl. Qed.
Lemma D_5b1fc : decode_any W_5b1fc = Some (Load SZ8 true 18 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b200 : bv 32 := 0x00813983.
Lemma F_5b200 : fetch_word Asan.M.loaded_segments (0x5b250 : word) = Some W_5b200.
Proof. vm_refl. Qed.
Lemma D_5b200 : decode_any W_5b200 = Some (Load SZ8 true 19 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b204 : bv 32 := 0x03010113.
Lemma F_5b204 : fetch_word Asan.M.loaded_segments (0x5b254 : word) = Some W_5b204.
Proof. vm_refl. Qed.
Lemma D_5b204 : decode_any W_5b204 = Some (OpImm ALU_ADD 2 2 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b208 : bv 32 := 0x00008067.
Lemma F_5b208 : fetch_word Asan.M.loaded_segments (0x5b258 : word) = Some W_5b208.
Proof. vm_refl. Qed.
Lemma D_5b208 : decode_any W_5b208 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b20c : bv 32 := 0x04853583.
Lemma F_5b20c : fetch_word Asan.M.loaded_segments (0x5b25c : word) = Some W_5b20c.
Proof. vm_refl. Qed.
Lemma D_5b20c : decode_any W_5b20c = Some (Load SZ8 true 11 10 72, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b210 : bv 32 := 0x02813083.
Lemma F_5b210 : fetch_word Asan.M.loaded_segments (0x5b260 : word) = Some W_5b210.
Proof. vm_refl. Qed.
Lemma D_5b210 : decode_any W_5b210 = Some (Load SZ8 true 1 2 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b214 : bv 32 := 0x02013403.
Lemma F_5b214 : fetch_word Asan.M.loaded_segments (0x5b264 : word) = Some W_5b214.
Proof. vm_refl. Qed.
Lemma D_5b214 : decode_any W_5b214 = Some (Load SZ8 true 8 2 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b218 : bv 32 := 0x01813483.
Lemma F_5b218 : fetch_word Asan.M.loaded_segments (0x5b268 : word) = Some W_5b218.
Proof. vm_refl. Qed.
Lemma D_5b218 : decode_any W_5b218 = Some (Load SZ8 true 9 2 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b21c : bv 32 := 0x01013903.
Lemma F_5b21c : fetch_word Asan.M.loaded_segments (0x5b26c : word) = Some W_5b21c.
Proof. vm_refl. Qed.
Lemma D_5b21c : decode_any W_5b21c = Some (Load SZ8 true 18 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b220 : bv 32 := 0x00813983.
Lemma F_5b220 : fetch_word Asan.M.loaded_segments (0x5b270 : word) = Some W_5b220.
Proof. vm_refl. Qed.
Lemma D_5b220 : decode_any W_5b220 = Some (Load SZ8 true 19 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b224 : bv 32 := 0x03010113.
Lemma F_5b224 : fetch_word Asan.M.loaded_segments (0x5b274 : word) = Some W_5b224.
Proof. vm_refl. Qed.
Lemma D_5b224 : decode_any W_5b224 = Some (OpImm ALU_ADD 2 2 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b228 : bv 32 := 0x0540006f.
Lemma F_5b228 : fetch_word Asan.M.loaded_segments (0x5b278 : word) = Some W_5b228.
Proof. vm_refl. Qed.
Lemma D_5b228 : decode_any W_5b228 = Some (Jal 0 84, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b27c : bv 32 := 0xfb010113.
Lemma F_5b27c : fetch_word Asan.M.loaded_segments (0x5b2cc : word) = Some W_5b27c.
Proof. vm_refl. Qed.
Lemma D_5b27c : decode_any W_5b27c = Some (OpImm ALU_ADD 2 2 4016, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b280 : bv 32 := 0x04113423.
Lemma F_5b280 : fetch_word Asan.M.loaded_segments (0x5b2d0 : word) = Some W_5b280.
Proof. vm_refl. Qed.
Lemma D_5b280 : decode_any W_5b280 = Some (Store SZ8 2 1 72, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b284 : bv 32 := 0x04813023.
Lemma F_5b284 : fetch_word Asan.M.loaded_segments (0x5b2d4 : word) = Some W_5b284.
Proof. vm_refl. Qed.
Lemma D_5b284 : decode_any W_5b284 = Some (Store SZ8 2 8 64, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b288 : bv 32 := 0x02913c23.
Lemma F_5b288 : fetch_word Asan.M.loaded_segments (0x5b2d8 : word) = Some W_5b288.
Proof. vm_refl. Qed.
Lemma D_5b288 : decode_any W_5b288 = Some (Store SZ8 2 9 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b28c : bv 32 := 0x03213823.
Lemma F_5b28c : fetch_word Asan.M.loaded_segments (0x5b2dc : word) = Some W_5b28c.
Proof. vm_refl. Qed.
Lemma D_5b28c : decode_any W_5b28c = Some (Store SZ8 2 18 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b290 : bv 32 := 0x03313423.
Lemma F_5b290 : fetch_word Asan.M.loaded_segments (0x5b2e0 : word) = Some W_5b290.
Proof. vm_refl. Qed.
Lemma D_5b290 : decode_any W_5b290 = Some (Store SZ8 2 19 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b294 : bv 32 := 0x03413023.
Lemma F_5b294 : fetch_word Asan.M.loaded_segments (0x5b2e4 : word) = Some W_5b294.
Proof. vm_refl. Qed.
Lemma D_5b294 : decode_any W_5b294 = Some (Store SZ8 2 20 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b298 : bv 32 := 0x00013023.
Lemma F_5b298 : fetch_word Asan.M.loaded_segments (0x5b2e8 : word) = Some W_5b298.
Proof. vm_refl. Qed.
Lemma D_5b298 : decode_any W_5b298 = Some (Store SZ8 2 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b29c : bv 32 := 0x00013423.
Lemma F_5b29c : fetch_word Asan.M.loaded_segments (0x5b2ec : word) = Some W_5b29c.
Proof. vm_refl. Qed.
Lemma D_5b29c : decode_any W_5b29c = Some (Store SZ8 2 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b2a0 : bv 32 := 0x00013823.
Lemma F_5b2a0 : fetch_word Asan.M.loaded_segments (0x5b2f0 : word) = Some W_5b2a0.
Proof. vm_refl. Qed.
Lemma D_5b2a0 : decode_any W_5b2a0 = Some (Store SZ8 2 0 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b2a4 : bv 32 := 0x00013c23.
Lemma F_5b2a4 : fetch_word Asan.M.loaded_segments (0x5b2f4 : word) = Some W_5b2a4.
Proof. vm_refl. Qed.
Lemma D_5b2a4 : decode_any W_5b2a4 = Some (Store SZ8 2 0 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b2a8 : bv 32 := 0x09850713.
Lemma F_5b2a8 : fetch_word Asan.M.loaded_segments (0x5b2f8 : word) = Some W_5b2a8.
Proof. vm_refl. Qed.
Lemma D_5b2a8 : decode_any W_5b2a8 = Some (OpImm ALU_ADD 14 10 152, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b2ac : bv 32 := 0x0ff00793.
Lemma F_5b2ac : fetch_word Asan.M.loaded_segments (0x5b2fc : word) = Some W_5b2ac.
Proof. vm_refl. Qed.
Lemma D_5b2ac : decode_any W_5b2ac = Some (OpImm ALU_ADD 15 0 255, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b2b0 : bv 32 := 0xffc77813.
Lemma F_5b2b0 : fetch_word Asan.M.loaded_segments (0x5b300 : word) = Some W_5b2b0.
Proof. vm_refl. Qed.
Lemma D_5b2b0 : decode_any W_5b2b0 = Some (OpImm ALU_AND 16 14 4092, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b2b4 : bv 32 := 0x00100893.
Lemma F_5b2b4 : fetch_word Asan.M.loaded_segments (0x5b304 : word) = Some W_5b2b4.
Proof. vm_refl. Qed.
Lemma D_5b2b4 : decode_any W_5b2b4 = Some (OpImm ALU_ADD 17 0 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b2b8 : bv 32 := 0x140822af.
Lemma F_5b2b8 : fetch_word Asan.M.loaded_segments (0x5b308 : word) = Some W_5b2b8.
Proof. vm_refl. Qed.
Lemma D_5b2b8 : decode_any W_5b2b8 = Some (Lr AW true false 5 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b2bc : bv 32 := 0x00088313.
Lemma F_5b2bc : fetch_word Asan.M.loaded_segments (0x5b30c : word) = Some W_5b2bc.
Proof. vm_refl. Qed.
Lemma D_5b2bc : decode_any W_5b2bc = Some (OpImm ALU_ADD 6 17 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b2c0 : bv 32 := 0x0062c333.
Lemma F_5b2c0 : fetch_word Asan.M.loaded_segments (0x5b310 : word) = Some W_5b2c0.
Proof. vm_refl. Qed.
Lemma D_5b2c0 : decode_any W_5b2c0 = Some (Op ALU_XOR 6 5 6, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b2c4 : bv 32 := 0x00f37333.
Lemma F_5b2c4 : fetch_word Asan.M.loaded_segments (0x5b314 : word) = Some W_5b2c4.
Proof. vm_refl. Qed.
Lemma D_5b2c4 : decode_any W_5b2c4 = Some (Op ALU_AND 6 6 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b2c8 : bv 32 := 0x0062c333.
Lemma F_5b2c8 : fetch_word Asan.M.loaded_segments (0x5b318 : word) = Some W_5b2c8.
Proof. vm_refl. Qed.
Lemma D_5b2c8 : decode_any W_5b2c8 = Some (Op ALU_XOR 6 5 6, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b2cc : bv 32 := 0x1868232f.
Lemma F_5b2cc : fetch_word Asan.M.loaded_segments (0x5b31c : word) = Some W_5b2cc.
Proof. vm_refl. Qed.
Lemma D_5b2cc : decode_any W_5b2cc = Some (Sc AW false false 6 16 6, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b2d0 : bv 32 := 0xfe0314e3.
Lemma F_5b2d0 : fetch_word Asan.M.loaded_segments (0x5b320 : word) = Some W_5b2d0.
Proof. vm_refl. Qed.
Lemma D_5b2d0 : decode_any W_5b2d0 = Some (Branch BC_NE 6 0 8168, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b2d4 : bv 32 := 0x0ff2f793.
Lemma F_5b2d4 : fetch_word Asan.M.loaded_segments (0x5b324 : word) = Some W_5b2d4.
Proof. vm_refl. Qed.
Lemma D_5b2d4 : decode_any W_5b2d4 = Some (OpImm ALU_AND 15 5 255, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b2d8 : bv 32 := 0x12079a63.
Lemma F_5b2d8 : fetch_word Asan.M.loaded_segments (0x5b328 : word) = Some W_5b2d8.
Proof. vm_refl. Qed.
Lemma D_5b2d8 : decode_any W_5b2d8 = Some (Branch BC_NE 15 0 308, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b2dc : bv 32 := 0x0b853783.
Lemma F_5b2dc : fetch_word Asan.M.loaded_segments (0x5b32c : word) = Some W_5b2dc.
Proof. vm_refl. Qed.
Lemma D_5b2dc : decode_any W_5b2dc = Some (Load SZ8 true 15 10 184, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b2e0 : bv 32 := 0x0a053803.
Lemma F_5b2e0 : fetch_word Asan.M.loaded_segments (0x5b330 : word) = Some W_5b2e0.
Proof. vm_refl. Qed.
Lemma D_5b2e0 : decode_any W_5b2e0 = Some (Load SZ8 true 16 10 160, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b2e4 : bv 32 := 0x00d81713.
Lemma F_5b2e4 : fetch_word Asan.M.loaded_segments (0x5b334 : word) = Some W_5b2e4.
Proof. vm_refl. Qed.
Lemma D_5b2e4 : decode_any W_5b2e4 = Some (ShiftImm ALU_SLL 14 16 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b2e8 : bv 32 := 0x14e7ee63.
Lemma F_5b2e8 : fetch_word Asan.M.loaded_segments (0x5b338 : word) = Some W_5b2e8.
Proof. vm_refl. Qed.
Lemma D_5b2e8 : decode_any W_5b2e8 = Some (Branch BC_LTU 15 14 348, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b2ec : bv 32 := 0x04f77663.
Lemma F_5b2ec : fetch_word Asan.M.loaded_segments (0x5b33c : word) = Some W_5b2ec.
Proof. vm_refl. Qed.
Lemma D_5b2ec : decode_any W_5b2ec = Some (Branch BC_GEU 14 15 76, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b2f0 : bv 32 := 0x00190737.
Lemma F_5b2f0 : fetch_word Asan.M.loaded_segments (0x5b340 : word) = Some W_5b2f0.
Proof. vm_refl. Qed.
Lemma D_5b2f0 : decode_any W_5b2f0 = Some (Lui 14 400, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b2f4 : bv 32 := 0x06400893.
Lemma F_5b2f4 : fetch_word Asan.M.loaded_segments (0x5b344 : word) = Some W_5b2f4.
Proof. vm_refl. Qed.
Lemma D_5b2f4 : decode_any W_5b2f4 = Some (OpImm ALU_ADD 17 0 100, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b2f8 : bv 32 := 0x02e80733.
Lemma F_5b2f8 : fetch_word Asan.M.loaded_segments (0x5b348 : word) = Some W_5b2f8.
Proof. vm_refl. Qed.
Lemma D_5b2f8 : decode_any W_5b2f8 = Some (Mul M_MUL 14 16 14, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b2fc : bv 32 := 0x031787b3.
Lemma F_5b2fc : fetch_word Asan.M.loaded_segments (0x5b34c : word) = Some W_5b2fc.
Proof. vm_refl. Qed.
Lemma D_5b2fc : decode_any W_5b2fc = Some (Mul M_MUL 15 15 17, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b300 : bv 32 := 0x02e7fc63.
Lemma F_5b300 : fetch_word Asan.M.loaded_segments (0x5b350 : word) = Some W_5b300.
Proof. vm_refl. Qed.
Lemma D_5b300 : decode_any W_5b300 = Some (Branch BC_GEU 15 14 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b338 : bv 32 := 0x00013703.
Lemma F_5b338 : fetch_word Asan.M.loaded_segments (0x5b388 : word) = Some W_5b338.
Proof. vm_refl. Qed.
Lemma D_5b338 : decode_any W_5b338 = Some (Load SZ8 true 14 2 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b33c : bv 32 := 0x01013783.
Lemma F_5b33c : fetch_word Asan.M.loaded_segments (0x5b38c : word) = Some W_5b33c.
Proof. vm_refl. Qed.
Lemma D_5b33c : decode_any W_5b33c = Some (Load SZ8 true 15 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b340 : bv 32 := 0x0b853883.
Lemma F_5b340 : fetch_word Asan.M.loaded_segments (0x5b390 : word) = Some W_5b340.
Proof. vm_refl. Qed.
Lemma D_5b340 : decode_any W_5b340 = Some (Load SZ8 true 17 10 184, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b344 : bv 32 := 0x0915f863.
Lemma F_5b344 : fetch_word Asan.M.loaded_segments (0x5b394 : word) = Some W_5b344.
Proof. vm_refl. Qed.
Lemma D_5b344 : decode_any W_5b344 = Some (Branch BC_GEU 11 17 144, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b348 : bv 32 := 0x0a853283.
Lemma F_5b348 : fetch_word Asan.M.loaded_segments (0x5b398 : word) = Some W_5b348.
Proof. vm_refl. Qed.
Lemma D_5b348 : decode_any W_5b348 = Some (Load SZ8 true 5 10 168, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b34c : bv 32 := 0x02c0006f.
Lemma F_5b34c : fetch_word Asan.M.loaded_segments (0x5b39c : word) = Some W_5b34c.
Proof. vm_refl. Qed.
Lemma D_5b34c : decode_any W_5b34c = Some (Jal 0 44, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b350 : bv 32 := 0x0067b023.
Lemma F_5b350 : fetch_word Asan.M.loaded_segments (0x5b3a0 : word) = Some W_5b350.
Proof. vm_refl. Qed.
Lemma D_5b350 : decode_any W_5b350 = Some (Store SZ8 15 6 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b354 : bv 32 := 0x00833783.
Lemma F_5b354 : fetch_word Asan.M.loaded_segments (0x5b3a4 : word) = Some W_5b354.
Proof. vm_refl. Qed.
Lemma D_5b354 : decode_any W_5b354 = Some (Load SZ8 true 15 6 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b358 : bv 32 := 0x01813283.
Lemma F_5b358 : fetch_word Asan.M.loaded_segments (0x5b3a8 : word) = Some W_5b358.
Proof. vm_refl. Qed.
Lemma D_5b358 : decode_any W_5b358 = Some (Load SZ8 true 5 2 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b35c : bv 32 := 0x00f287b3.
Lemma F_5b35c : fetch_word Asan.M.loaded_segments (0x5b3ac : word) = Some W_5b35c.
Proof. vm_refl. Qed.
Lemma D_5b35c : decode_any W_5b35c = Some (Op ALU_ADD 15 5 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b360 : bv 32 := 0x00f13c23.
Lemma F_5b360 : fetch_word Asan.M.loaded_segments (0x5b3b0 : word) = Some W_5b360.
Proof. vm_refl. Qed.
Lemma D_5b360 : decode_any W_5b360 = Some (Store SZ8 2 15 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b364 : bv 32 := 0x0b853383.
Lemma F_5b364 : fetch_word Asan.M.loaded_segments (0x5b3b4 : word) = Some W_5b364.
Proof. vm_refl. Qed.
Lemma D_5b364 : decode_any W_5b364 = Some (Load SZ8 true 7 10 184, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b368 : bv 32 := 0x00170713.
Lemma F_5b368 : fetch_word Asan.M.loaded_segments (0x5b3b8 : word) = Some W_5b368.
Proof. vm_refl. Qed.
Lemma D_5b368 : decode_any W_5b368 = Some (OpImm ALU_ADD 14 14 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b36c : bv 32 := 0x00088293.
Lemma F_5b36c : fetch_word Asan.M.loaded_segments (0x5b3bc : word) = Some W_5b36c.
Proof. vm_refl. Qed.
Lemma D_5b36c : decode_any W_5b36c = Some (OpImm ALU_ADD 5 17 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b370 : bv 32 := 0x00030793.
Lemma F_5b370 : fetch_word Asan.M.loaded_segments (0x5b3c0 : word) = Some W_5b370.
Proof. vm_refl. Qed.
Lemma D_5b370 : decode_any W_5b370 = Some (OpImm ALU_ADD 15 6 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b374 : bv 32 := 0x0475fc63.
Lemma F_5b374 : fetch_word Asan.M.loaded_segments (0x5b3c4 : word) = Some W_5b374.
Proof. vm_refl. Qed.
Lemma D_5b374 : decode_any W_5b374 = Some (Branch BC_GEU 11 7 88, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b378 : bv 32 := 0x02080e63.
Lemma F_5b378 : fetch_word Asan.M.loaded_segments (0x5b3c8 : word) = Some W_5b378.
Proof. vm_refl. Qed.
Lemma D_5b378 : decode_any W_5b378 = Some (Branch BC_EQ 16 0 60, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b37c : bv 32 := 0x0002b883.
Lemma F_5b37c : fetch_word Asan.M.loaded_segments (0x5b3cc : word) = Some W_5b37c.
Proof. vm_refl. Qed.
Lemma D_5b37c : decode_any W_5b37c = Some (Load SZ8 true 17 5 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b380 : bv 32 := 0x0b153423.
Lemma F_5b380 : fetch_word Asan.M.loaded_segments (0x5b3d0 : word) = Some W_5b380.
Proof. vm_refl. Qed.
Lemma D_5b380 : decode_any W_5b380 = Some (Store SZ8 10 17 168, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b384 : bv 32 := 0x00089463.
Lemma F_5b384 : fetch_word Asan.M.loaded_segments (0x5b3d4 : word) = Some W_5b384.
Proof. vm_refl. Qed.
Lemma D_5b384 : decode_any W_5b384 = Some (Branch BC_NE 17 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b388 : bv 32 := 0x0a053823.
Lemma F_5b388 : fetch_word Asan.M.loaded_segments (0x5b3d8 : word) = Some W_5b388.
Proof. vm_refl. Qed.
Lemma D_5b388 : decode_any W_5b388 = Some (Store SZ8 10 0 176, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b38c : bv 32 := 0xfff80813.
Lemma F_5b38c : fetch_word Asan.M.loaded_segments (0x5b3dc : word) = Some W_5b38c.
Proof. vm_refl. Qed.
Lemma D_5b38c : decode_any W_5b38c = Some (OpImm ALU_ADD 16 16 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b390 : bv 32 := 0x0b053023.
Lemma F_5b390 : fetch_word Asan.M.loaded_segments (0x5b3e0 : word) = Some W_5b390.
Proof. vm_refl. Qed.
Lemma D_5b390 : decode_any W_5b390 = Some (Store SZ8 10 16 160, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b394 : bv 32 := 0x0082b303.
Lemma F_5b394 : fetch_word Asan.M.loaded_segments (0x5b3e4 : word) = Some W_5b394.
Proof. vm_refl. Qed.
Lemma D_5b394 : decode_any W_5b394 = Some (Load SZ8 true 6 5 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b398 : bv 32 := 0x0b853383.
Lemma F_5b398 : fetch_word Asan.M.loaded_segments (0x5b3e8 : word) = Some W_5b398.
Proof. vm_refl. Qed.
Lemma D_5b398 : decode_any W_5b398 = Some (Load SZ8 true 7 10 184, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b39c : bv 32 := 0x40638333.
Lemma F_5b39c : fetch_word Asan.M.loaded_segments (0x5b3ec : word) = Some W_5b39c.
Proof. vm_refl. Qed.
Lemma D_5b39c : decode_any W_5b39c = Some (Op ALU_SUB 6 7 6, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b3a0 : bv 32 := 0x0a653c23.
Lemma F_5b3a0 : fetch_word Asan.M.loaded_segments (0x5b3f0 : word) = Some W_5b3a0.
Proof. vm_refl. Qed.
Lemma D_5b3a0 : decode_any W_5b3a0 = Some (Store SZ8 10 6 184, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b3a4 : bv 32 := 0x00028313.
Lemma F_5b3a4 : fetch_word Asan.M.loaded_segments (0x5b3f4 : word) = Some W_5b3a4.
Proof. vm_refl. Qed.
Lemma D_5b3a4 : decode_any W_5b3a4 = Some (OpImm ALU_ADD 6 5 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b3a8 : bv 32 := 0x0002b023.
Lemma F_5b3a8 : fetch_word Asan.M.loaded_segments (0x5b3f8 : word) = Some W_5b3a8.
Proof. vm_refl. Qed.
Lemma D_5b3a8 : decode_any W_5b3a8 = Some (Store SZ8 5 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b3ac : bv 32 := 0xfa0712e3.
Lemma F_5b3ac : fetch_word Asan.M.loaded_segments (0x5b3fc : word) = Some W_5b3ac.
Proof. vm_refl. Qed.
Lemma D_5b3ac : decode_any W_5b3ac = Some (Branch BC_NE 14 0 8100, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b3b0 : bv 32 := 0x0140006f.
Lemma F_5b3b0 : fetch_word Asan.M.loaded_segments (0x5b400 : word) = Some W_5b3b0.
Proof. vm_refl. Qed.
Lemma D_5b3b0 : decode_any W_5b3b0 = Some (Jal 0 20, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b3c4 : bv 32 := 0x00613423.
Lemma F_5b3c4 : fetch_word Asan.M.loaded_segments (0x5b414 : word) = Some W_5b3c4.
Proof. vm_refl. Qed.
Lemma D_5b3c4 : decode_any W_5b3c4 = Some (Store SZ8 2 6 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b3c8 : bv 32 := 0xf8dff06f.
Lemma F_5b3c8 : fetch_word Asan.M.loaded_segments (0x5b418 : word) = Some W_5b3c8.
Proof. vm_refl. Qed.
Lemma D_5b3c8 : decode_any W_5b3c8 = Some (Jal 0 2097036, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b3cc : bv 32 := 0x00e13023.
Lemma F_5b3cc : fetch_word Asan.M.loaded_segments (0x5b41c : word) = Some W_5b3cc.
Proof. vm_refl. Qed.
Lemma D_5b3cc : decode_any W_5b3cc = Some (Store SZ8 2 14 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b3d0 : bv 32 := 0x00613823.
Lemma F_5b3d0 : fetch_word Asan.M.loaded_segments (0x5b420 : word) = Some W_5b3d0.
Proof. vm_refl. Qed.
Lemma D_5b3d0 : decode_any W_5b3d0 = Some (Store SZ8 2 6 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b3d4 : bv 32 := 0x0310000f.
Lemma F_5b3d4 : fetch_word Asan.M.loaded_segments (0x5b424 : word) = Some W_5b3d4.
Proof. vm_refl. Qed.
Lemma D_5b3d4 : decode_any W_5b3d4 = Some (Fence 0 3 1 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b3d8 : bv 32 := 0x08050c23.
Lemma F_5b3d8 : fetch_word Asan.M.loaded_segments (0x5b428 : word) = Some W_5b3d8.
Proof. vm_refl. Qed.
Lemma D_5b3d8 : decode_any W_5b3d8 = Some (Store SZ1 10 0 152, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b3dc : bv 32 := 0x0310000f.
Lemma F_5b3dc : fetch_word Asan.M.loaded_segments (0x5b42c : word) = Some W_5b3dc.
Proof. vm_refl. Qed.
Lemma D_5b3dc : decode_any W_5b3dc = Some (Fence 0 3 1 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b3e0 : bv 32 := 0x08050ca3.
Lemma F_5b3e0 : fetch_word Asan.M.loaded_segments (0x5b430 : word) = Some W_5b3e0.
Proof. vm_refl. Qed.
Lemma D_5b3e0 : decode_any W_5b3e0 = Some (Store SZ1 10 0 153, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b3e4 : bv 32 := 0x00010593.
Lemma F_5b3e4 : fetch_word Asan.M.loaded_segments (0x5b434 : word) = Some W_5b3e4.
Proof. vm_refl. Qed.
Lemma D_5b3e4 : decode_any W_5b3e4 = Some (OpImm ALU_ADD 11 2 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b3e8 : bv 32 := 0x1fc000ef.
Lemma F_5b3e8 : fetch_word Asan.M.loaded_segments (0x5b438 : word) = Some W_5b3e8.
Proof. vm_refl. Qed.
Lemma D_5b3e8 : decode_any W_5b3e8 = Some (Jal 1 508, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b3ec : bv 32 := 0x04813083.
Lemma F_5b3ec : fetch_word Asan.M.loaded_segments (0x5b43c : word) = Some W_5b3ec.
Proof. vm_refl. Qed.
Lemma D_5b3ec : decode_any W_5b3ec = Some (Load SZ8 true 1 2 72, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b3f0 : bv 32 := 0x04013403.
Lemma F_5b3f0 : fetch_word Asan.M.loaded_segments (0x5b440 : word) = Some W_5b3f0.
Proof. vm_refl. Qed.
Lemma D_5b3f0 : decode_any W_5b3f0 = Some (Load SZ8 true 8 2 64, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b3f4 : bv 32 := 0x03813483.
Lemma F_5b3f4 : fetch_word Asan.M.loaded_segments (0x5b444 : word) = Some W_5b3f4.
Proof. vm_refl. Qed.
Lemma D_5b3f4 : decode_any W_5b3f4 = Some (Load SZ8 true 9 2 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b3f8 : bv 32 := 0x03013903.
Lemma F_5b3f8 : fetch_word Asan.M.loaded_segments (0x5b448 : word) = Some W_5b3f8.
Proof. vm_refl. Qed.
Lemma D_5b3f8 : decode_any W_5b3f8 = Some (Load SZ8 true 18 2 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b3fc : bv 32 := 0x02813983.
Lemma F_5b3fc : fetch_word Asan.M.loaded_segments (0x5b44c : word) = Some W_5b3fc.
Proof. vm_refl. Qed.
Lemma D_5b3fc : decode_any W_5b3fc = Some (Load SZ8 true 19 2 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b400 : bv 32 := 0x02013a03.
Lemma F_5b400 : fetch_word Asan.M.loaded_segments (0x5b450 : word) = Some W_5b400.
Proof. vm_refl. Qed.
Lemma D_5b400 : decode_any W_5b400 = Some (Load SZ8 true 20 2 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b404 : bv 32 := 0x05010113.
Lemma F_5b404 : fetch_word Asan.M.loaded_segments (0x5b454 : word) = Some W_5b404.
Proof. vm_refl. Qed.
Lemma D_5b404 : decode_any W_5b404 = Some (OpImm ALU_ADD 2 2 80, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b408 : bv 32 := 0x00008067.
Lemma F_5b408 : fetch_word Asan.M.loaded_segments (0x5b458 : word) = Some W_5b408.
Proof. vm_refl. Qed.
Lemma D_5b408 : decode_any W_5b408 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b5e4 : bv 32 := 0xf9010113.
Lemma F_5b5e4 : fetch_word Asan.M.loaded_segments (0x5b634 : word) = Some W_5b5e4.
Proof. vm_refl. Qed.
Lemma D_5b5e4 : decode_any W_5b5e4 = Some (OpImm ALU_ADD 2 2 3984, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b5e8 : bv 32 := 0x06113423.
Lemma F_5b5e8 : fetch_word Asan.M.loaded_segments (0x5b638 : word) = Some W_5b5e8.
Proof. vm_refl. Qed.
Lemma D_5b5e8 : decode_any W_5b5e8 = Some (Store SZ8 2 1 104, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b5ec : bv 32 := 0x06813023.
Lemma F_5b5ec : fetch_word Asan.M.loaded_segments (0x5b63c : word) = Some W_5b5ec.
Proof. vm_refl. Qed.
Lemma D_5b5ec : decode_any W_5b5ec = Some (Store SZ8 2 8 96, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b5f0 : bv 32 := 0x04913c23.
Lemma F_5b5f0 : fetch_word Asan.M.loaded_segments (0x5b640 : word) = Some W_5b5f0.
Proof. vm_refl. Qed.
Lemma D_5b5f0 : decode_any W_5b5f0 = Some (Store SZ8 2 9 88, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b5f4 : bv 32 := 0x05213823.
Lemma F_5b5f4 : fetch_word Asan.M.loaded_segments (0x5b644 : word) = Some W_5b5f4.
Proof. vm_refl. Qed.
Lemma D_5b5f4 : decode_any W_5b5f4 = Some (Store SZ8 2 18 80, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b5f8 : bv 32 := 0x05313423.
Lemma F_5b5f8 : fetch_word Asan.M.loaded_segments (0x5b648 : word) = Some W_5b5f8.
Proof. vm_refl. Qed.
Lemma D_5b5f8 : decode_any W_5b5f8 = Some (Store SZ8 2 19 72, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b5fc : bv 32 := 0x05413023.
Lemma F_5b5fc : fetch_word Asan.M.loaded_segments (0x5b64c : word) = Some W_5b5fc.
Proof. vm_refl. Qed.
Lemma D_5b5fc : decode_any W_5b5fc = Some (Store SZ8 2 20 64, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b600 : bv 32 := 0x03513c23.
Lemma F_5b600 : fetch_word Asan.M.loaded_segments (0x5b650 : word) = Some W_5b600.
Proof. vm_refl. Qed.
Lemma D_5b600 : decode_any W_5b600 = Some (Store SZ8 2 21 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b604 : bv 32 := 0x03613823.
Lemma F_5b604 : fetch_word Asan.M.loaded_segments (0x5b654 : word) = Some W_5b604.
Proof. vm_refl. Qed.
Lemma D_5b604 : decode_any W_5b604 = Some (Store SZ8 2 22 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b608 : bv 32 := 0x03713423.
Lemma F_5b608 : fetch_word Asan.M.loaded_segments (0x5b658 : word) = Some W_5b608.
Proof. vm_refl. Qed.
Lemma D_5b608 : decode_any W_5b608 = Some (Store SZ8 2 23 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b60c : bv 32 := 0x03813023.
Lemma F_5b60c : fetch_word Asan.M.loaded_segments (0x5b65c : word) = Some W_5b60c.
Proof. vm_refl. Qed.
Lemma D_5b60c : decode_any W_5b60c = Some (Store SZ8 2 24 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b610 : bv 32 := 0x01913c23.
Lemma F_5b610 : fetch_word Asan.M.loaded_segments (0x5b660 : word) = Some W_5b610.
Proof. vm_refl. Qed.
Lemma D_5b610 : decode_any W_5b610 = Some (Store SZ8 2 25 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b614 : bv 32 := 0x0005b503.
Lemma F_5b614 : fetch_word Asan.M.loaded_segments (0x5b664 : word) = Some W_5b614.
Proof. vm_refl. Qed.
Lemma D_5b614 : decode_any W_5b614 = Some (Load SZ8 true 10 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b618 : bv 32 := 0x00c13423.
Lemma F_5b618 : fetch_word Asan.M.loaded_segments (0x5b668 : word) = Some W_5b618.
Proof. vm_refl. Qed.
Lemma D_5b618 : decode_any W_5b618 = Some (Store SZ8 2 12 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b61c : bv 32 := 0x00d13823.
Lemma F_5b61c : fetch_word Asan.M.loaded_segments (0x5b66c : word) = Some W_5b61c.
Proof. vm_refl. Qed.
Lemma D_5b61c : decode_any W_5b61c = Some (Store SZ8 2 13 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b620 : bv 32 := 0x0c050463.
Lemma F_5b620 : fetch_word Asan.M.loaded_segments (0x5b670 : word) = Some W_5b620.
Proof. vm_refl. Qed.
Lemma D_5b620 : decode_any W_5b620 = Some (Branch BC_EQ 10 0 200, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b624 : bv 32 := 0x00058413.
Lemma F_5b624 : fetch_word Asan.M.loaded_segments (0x5b674 : word) = Some W_5b624.
Proof. vm_refl. Qed.
Lemma D_5b624 : decode_any W_5b624 = Some (OpImm ALU_ADD 8 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b628 : bv 32 := 0x000fe597.
Lemma F_5b628 : fetch_word Asan.M.loaded_segments (0x5b678 : word) = Some W_5b628.
Proof. vm_refl. Qed.
Lemma D_5b628 : decode_any W_5b628 = Some (Auipc 11 254, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b62c : bv 32 := 0x00100a93.
Lemma F_5b62c : fetch_word Asan.M.loaded_segments (0x5b67c : word) = Some W_5b62c.
Proof. vm_refl. Qed.
Lemma D_5b62c : decode_any W_5b62c = Some (OpImm ALU_ADD 21 0 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b630 : bv 32 := 0xce058493.
Lemma F_5b630 : fetch_word Asan.M.loaded_segments (0x5b680 : word) = Some W_5b630.
Proof. vm_refl. Qed.
Lemma D_5b630 : decode_any W_5b630 = Some (OpImm ALU_ADD 9 11 3296, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b634 : bv 32 := 0x025a9a93.
Lemma F_5b634 : fetch_word Asan.M.loaded_segments (0x5b684 : word) = Some W_5b634.
Proof. vm_refl. Qed.
Lemma D_5b634 : decode_any W_5b634 = Some (ShiftImm ALU_SLL 21 21 37, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b638 : bv 32 := 0x04048913.
Lemma F_5b638 : fetch_word Asan.M.loaded_segments (0x5b688 : word) = Some W_5b638.
Proof. vm_refl. Qed.
Lemma D_5b638 : decode_any W_5b638 = Some (OpImm ALU_ADD 18 9 64, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b63c : bv 32 := 0x2b048993.
Lemma F_5b63c : fetch_word Asan.M.loaded_segments (0x5b68c : word) = Some W_5b63c.
Proof. vm_refl. Qed.
Lemma D_5b63c : decode_any W_5b63c = Some (OpImm ALU_ADD 19 9 688, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b640 : bv 32 := 0x01c0006f.
Lemma F_5b640 : fetch_word Asan.M.loaded_segments (0x5b690 : word) = Some W_5b640.
Proof. vm_refl. Qed.
Lemma D_5b640 : decode_any W_5b640 = Some (Jal 0 28, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b65c : bv 32 := 0x00843a03.
Lemma F_5b65c : fetch_word Asan.M.loaded_segments (0x5b6ac : word) = Some W_5b65c.
Proof. vm_refl. Qed.
Lemma D_5b65c : decode_any W_5b65c = Some (Load SZ8 true 20 8 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b660 : bv 32 := 0x000a3583.
Lemma F_5b660 : fetch_word Asan.M.loaded_segments (0x5b6b0 : word) = Some W_5b660.
Proof. vm_refl. Qed.
Lemma D_5b660 : decode_any W_5b660 = Some (Load SZ8 true 11 20 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b664 : bv 32 := 0x00b43423.
Lemma F_5b664 : fetch_word Asan.M.loaded_segments (0x5b6b4 : word) = Some W_5b664.
Proof. vm_refl. Qed.
Lemma D_5b664 : decode_any W_5b664 = Some (Store SZ8 8 11 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b668 : bv 32 := 0x00059463.
Lemma F_5b668 : fetch_word Asan.M.loaded_segments (0x5b6b8 : word) = Some W_5b668.
Proof. vm_refl. Qed.
Lemma D_5b668 : decode_any W_5b668 = Some (Branch BC_NE 11 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b66c : bv 32 := 0x00043823.
Lemma F_5b66c : fetch_word Asan.M.loaded_segments (0x5b6bc : word) = Some W_5b66c.
Proof. vm_refl. Qed.
Lemma D_5b66c : decode_any W_5b66c = Some (Store SZ8 8 0 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b670 : bv 32 := 0xfff50513.
Lemma F_5b670 : fetch_word Asan.M.loaded_segments (0x5b6c0 : word) = Some W_5b670.
Proof. vm_refl. Qed.
Lemma D_5b670 : decode_any W_5b670 = Some (OpImm ALU_ADD 10 10 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b674 : bv 32 := 0x00a43023.
Lemma F_5b674 : fetch_word Asan.M.loaded_segments (0x5b6c4 : word) = Some W_5b674.
Proof. vm_refl. Qed.
Lemma D_5b674 : decode_any W_5b674 = Some (Store SZ8 8 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b678 : bv 32 := 0x008a3503.
Lemma F_5b678 : fetch_word Asan.M.loaded_segments (0x5b6c8 : word) = Some W_5b678.
Proof. vm_refl. Qed.
Lemma D_5b678 : decode_any W_5b678 = Some (Load SZ8 true 10 20 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b67c : bv 32 := 0x01843583.
Lemma F_5b67c : fetch_word Asan.M.loaded_segments (0x5b6cc : word) = Some W_5b67c.
Proof. vm_refl. Qed.
Lemma D_5b67c : decode_any W_5b67c = Some (Load SZ8 true 11 8 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b680 : bv 32 := 0x40a585b3.
Lemma F_5b680 : fetch_word Asan.M.loaded_segments (0x5b6d0 : word) = Some W_5b680.
Proof. vm_refl. Qed.
Lemma D_5b680 : decode_any W_5b680 = Some (Op ALU_SUB 11 11 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b684 : bv 32 := 0x00b43c23.
Lemma F_5b684 : fetch_word Asan.M.loaded_segments (0x5b6d4 : word) = Some W_5b684.
Proof. vm_refl. Qed.
Lemma D_5b684 : decode_any W_5b684 = Some (Store SZ8 8 11 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b688 : bv 32 := 0x010a3b03.
Lemma F_5b688 : fetch_word Asan.M.loaded_segments (0x5b6d8 : word) = Some W_5b688.
Proof. vm_refl. Qed.
Lemma D_5b688 : decode_any W_5b688 = Some (Load SZ8 true 22 20 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b68c : bv 32 := 0x020b0463.
Lemma F_5b68c : fetch_word Asan.M.loaded_segments (0x5b6dc : word) = Some W_5b68c.
Proof. vm_refl. Qed.
Lemma D_5b68c : decode_any W_5b68c = Some (Branch BC_EQ 22 0 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b690 : bv 32 := 0x098a0b93.
Lemma F_5b690 : fetch_word Asan.M.loaded_segments (0x5b6e0 : word) = Some W_5b690.
Proof. vm_refl. Qed.
Lemma D_5b690 : decode_any W_5b690 = Some (OpImm ALU_ADD 23 20 152, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b694 : bv 32 := 0x010b0c13.
Lemma F_5b694 : fetch_word Asan.M.loaded_segments (0x5b6e4 : word) = Some W_5b694.
Proof. vm_refl. Qed.
Lemma D_5b694 : decode_any W_5b694 = Some (OpImm ALU_ADD 24 22 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b698 : bv 32 := 0x01000c93.
Lemma F_5b698 : fetch_word Asan.M.loaded_segments (0x5b6e8 : word) = Some W_5b698.
Proof. vm_refl. Qed.
Lemma D_5b698 : decode_any W_5b698 = Some (OpImm ALU_ADD 25 0 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b69c : bv 32 := 0xf80bb583.
Lemma F_5b69c : fetch_word Asan.M.loaded_segments (0x5b6ec : word) = Some W_5b69c.
Proof. vm_refl. Qed.
Lemma D_5b69c : decode_any W_5b69c = Some (Load SZ8 true 11 23 3968, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b6a0 : bv 32 := 0x00810513.
Lemma F_5b6a0 : fetch_word Asan.M.loaded_segments (0x5b6f0 : word) = Some W_5b6a0.
Proof. vm_refl. Qed.
Lemma D_5b6a0 : decode_any W_5b6a0 = Some (OpImm ALU_ADD 10 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b6a4 : bv 32 := 0x078000ef.
Lemma F_5b6a4 : fetch_word Asan.M.loaded_segments (0x5b6f4 : word) = Some W_5b6a4.
Proof. vm_refl. Qed.
Lemma D_5b6a4 : decode_any W_5b6a4 = Some (Jal 1 120, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b6a8 : bv 32 := 0x001c8c93.
Lemma F_5b6a8 : fetch_word Asan.M.loaded_segments (0x5b6f8 : word) = Some W_5b6a8.
Proof. vm_refl. Qed.
Lemma D_5b6a8 : decode_any W_5b6a8 = Some (OpImm ALU_ADD 25 25 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b6ac : bv 32 := 0x008b8b93.
Lemma F_5b6ac : fetch_word Asan.M.loaded_segments (0x5b6fc : word) = Some W_5b6ac.
Proof. vm_refl. Qed.
Lemma D_5b6ac : decode_any W_5b6ac = Some (OpImm ALU_ADD 23 23 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b6b0 : bv 32 := 0xff8c96e3.
Lemma F_5b6b0 : fetch_word Asan.M.loaded_segments (0x5b700 : word) = Some W_5b6b0.
Proof. vm_refl. Qed.
Lemma D_5b6b0 : decode_any W_5b6b0 = Some (Branch BC_NE 25 24 8172, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b6b4 : bv 32 := 0x0204b583.
Lemma F_5b6b4 : fetch_word Asan.M.loaded_segments (0x5b704 : word) = Some W_5b6b4.
Proof. vm_refl. Qed.
Lemma D_5b6b4 : decode_any W_5b6b4 = Some (Load SZ8 true 11 9 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b6b8 : bv 32 := 0xf8ba66e3.
Lemma F_5b6b8 : fetch_word Asan.M.loaded_segments (0x5b708 : word) = Some W_5b6b8.
Proof. vm_refl. Qed.
Lemma D_5b6b8 : decode_any W_5b6b8 = Some (Branch BC_LTU 20 11 8076, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b6bc : bv 32 := 0x01558533.
Lemma F_5b6bc : fetch_word Asan.M.loaded_segments (0x5b70c : word) = Some W_5b6bc.
Proof. vm_refl. Qed.
Lemma D_5b6bc : decode_any W_5b6bc = Some (Op ALU_ADD 10 11 21, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b6c0 : bv 32 := 0xf8aa72e3.
Lemma F_5b6c0 : fetch_word Asan.M.loaded_segments (0x5b710 : word) = Some W_5b6c0.
Proof. vm_refl. Qed.
Lemma D_5b6c0 : decode_any W_5b6c0 = Some (Branch BC_GEU 20 10 8068, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b6c4 : bv 32 := 0x00813503.
Lemma F_5b6c4 : fetch_word Asan.M.loaded_segments (0x5b714 : word) = Some W_5b6c4.
Proof. vm_refl. Qed.
Lemma D_5b6c4 : decode_any W_5b6c4 = Some (Load SZ8 true 10 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b6c8 : bv 32 := 0x40ba05b3.
Lemma F_5b6c8 : fetch_word Asan.M.loaded_segments (0x5b718 : word) = Some W_5b6c8.
Proof. vm_refl. Qed.
Lemma D_5b6c8 : decode_any W_5b6c8 = Some (Op ALU_SUB 11 20 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b6cc : bv 32 := 0x01b59593.
Lemma F_5b6cc : fetch_word Asan.M.loaded_segments (0x5b71c : word) = Some W_5b6cc.
Proof. vm_refl. Qed.
Lemma D_5b6cc : decode_any W_5b6cc = Some (ShiftImm ALU_SLL 11 11 27, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b6d0 : bv 32 := 0x03b5d613.
Lemma F_5b6d0 : fetch_word Asan.M.loaded_segments (0x5b720 : word) = Some W_5b6d0.
Proof. vm_refl. Qed.
Lemma D_5b6d0 : decode_any W_5b6d0 = Some (ShiftImm ALU_SRL 12 11 59, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b6d4 : bv 32 := 0x00048593.
Lemma F_5b6d4 : fetch_word Asan.M.loaded_segments (0x5b724 : word) = Some W_5b6d4.
Proof. vm_refl. Qed.
Lemma D_5b6d4 : decode_any W_5b6d4 = Some (OpImm ALU_ADD 11 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b6d8 : bv 32 := 0x000a0693.
Lemma F_5b6d8 : fetch_word Asan.M.loaded_segments (0x5b728 : word) = Some W_5b6d8.
Proof. vm_refl. Qed.
Lemma D_5b6d8 : decode_any W_5b6d8 = Some (OpImm ALU_ADD 13 20 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b6dc : bv 32 := 0x444000ef.
Lemma F_5b6dc : fetch_word Asan.M.loaded_segments (0x5b72c : word) = Some W_5b6dc.
Proof. vm_refl. Qed.
Lemma D_5b6dc : decode_any W_5b6dc = Some (Jal 1 1092, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b6e0 : bv 32 := 0x00043503.
Lemma F_5b6e0 : fetch_word Asan.M.loaded_segments (0x5b730 : word) = Some W_5b6e0.
Proof. vm_refl. Qed.
Lemma D_5b6e0 : decode_any W_5b6e0 = Some (Load SZ8 true 10 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b6e4 : bv 32 := 0xf6051ce3.
Lemma F_5b6e4 : fetch_word Asan.M.loaded_segments (0x5b734 : word) = Some W_5b6e4.
Proof. vm_refl. Qed.
Lemma D_5b6e4 : decode_any W_5b6e4 = Some (Branch BC_NE 10 0 8056, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b6e8 : bv 32 := 0x06813083.
Lemma F_5b6e8 : fetch_word Asan.M.loaded_segments (0x5b738 : word) = Some W_5b6e8.
Proof. vm_refl. Qed.
Lemma D_5b6e8 : decode_any W_5b6e8 = Some (Load SZ8 true 1 2 104, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b6ec : bv 32 := 0x06013403.
Lemma F_5b6ec : fetch_word Asan.M.loaded_segments (0x5b73c : word) = Some W_5b6ec.
Proof. vm_refl. Qed.
Lemma D_5b6ec : decode_any W_5b6ec = Some (Load SZ8 true 8 2 96, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b6f0 : bv 32 := 0x05813483.
Lemma F_5b6f0 : fetch_word Asan.M.loaded_segments (0x5b740 : word) = Some W_5b6f0.
Proof. vm_refl. Qed.
Lemma D_5b6f0 : decode_any W_5b6f0 = Some (Load SZ8 true 9 2 88, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b6f4 : bv 32 := 0x05013903.
Lemma F_5b6f4 : fetch_word Asan.M.loaded_segments (0x5b744 : word) = Some W_5b6f4.
Proof. vm_refl. Qed.
Lemma D_5b6f4 : decode_any W_5b6f4 = Some (Load SZ8 true 18 2 80, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b6f8 : bv 32 := 0x04813983.
Lemma F_5b6f8 : fetch_word Asan.M.loaded_segments (0x5b748 : word) = Some W_5b6f8.
Proof. vm_refl. Qed.
Lemma D_5b6f8 : decode_any W_5b6f8 = Some (Load SZ8 true 19 2 72, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b6fc : bv 32 := 0x04013a03.
Lemma F_5b6fc : fetch_word Asan.M.loaded_segments (0x5b74c : word) = Some W_5b6fc.
Proof. vm_refl. Qed.
Lemma D_5b6fc : decode_any W_5b6fc = Some (Load SZ8 true 20 2 64, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b700 : bv 32 := 0x03813a83.
Lemma F_5b700 : fetch_word Asan.M.loaded_segments (0x5b750 : word) = Some W_5b700.
Proof. vm_refl. Qed.
Lemma D_5b700 : decode_any W_5b700 = Some (Load SZ8 true 21 2 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b704 : bv 32 := 0x03013b03.
Lemma F_5b704 : fetch_word Asan.M.loaded_segments (0x5b754 : word) = Some W_5b704.
Proof. vm_refl. Qed.
Lemma D_5b704 : decode_any W_5b704 = Some (Load SZ8 true 22 2 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b708 : bv 32 := 0x02813b83.
Lemma F_5b708 : fetch_word Asan.M.loaded_segments (0x5b758 : word) = Some W_5b708.
Proof. vm_refl. Qed.
Lemma D_5b708 : decode_any W_5b708 = Some (Load SZ8 true 23 2 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b70c : bv 32 := 0x02013c03.
Lemma F_5b70c : fetch_word Asan.M.loaded_segments (0x5b75c : word) = Some W_5b70c.
Proof. vm_refl. Qed.
Lemma D_5b70c : decode_any W_5b70c = Some (Load SZ8 true 24 2 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b710 : bv 32 := 0x01813c83.
Lemma F_5b710 : fetch_word Asan.M.loaded_segments (0x5b760 : word) = Some W_5b710.
Proof. vm_refl. Qed.
Lemma D_5b710 : decode_any W_5b710 = Some (Load SZ8 true 25 2 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b714 : bv 32 := 0x07010113.
Lemma F_5b714 : fetch_word Asan.M.loaded_segments (0x5b764 : word) = Some W_5b714.
Proof. vm_refl. Qed.
Lemma D_5b714 : decode_any W_5b714 = Some (OpImm ALU_ADD 2 2 112, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b718 : bv 32 := 0x00008067.
Lemma F_5b718 : fetch_word Asan.M.loaded_segments (0x5b768 : word) = Some W_5b718.
Proof. vm_refl. Qed.
Lemma D_5b718 : decode_any W_5b718 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b71c : bv 32 := 0xfd010113.
Lemma F_5b71c : fetch_word Asan.M.loaded_segments (0x5b76c : word) = Some W_5b71c.
Proof. vm_refl. Qed.
Lemma D_5b71c : decode_any W_5b71c = Some (OpImm ALU_ADD 2 2 4048, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b720 : bv 32 := 0x02113423.
Lemma F_5b720 : fetch_word Asan.M.loaded_segments (0x5b770 : word) = Some W_5b720.
Proof. vm_refl. Qed.
Lemma D_5b720 : decode_any W_5b720 = Some (Store SZ8 2 1 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b724 : bv 32 := 0x02813023.
Lemma F_5b724 : fetch_word Asan.M.loaded_segments (0x5b774 : word) = Some W_5b724.
Proof. vm_refl. Qed.
Lemma D_5b724 : decode_any W_5b724 = Some (Store SZ8 2 8 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b728 : bv 32 := 0x00913c23.
Lemma F_5b728 : fetch_word Asan.M.loaded_segments (0x5b778 : word) = Some W_5b728.
Proof. vm_refl. Qed.
Lemma D_5b728 : decode_any W_5b728 = Some (Store SZ8 2 9 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b72c : bv 32 := 0x01213823.
Lemma F_5b72c : fetch_word Asan.M.loaded_segments (0x5b77c : word) = Some W_5b72c.
Proof. vm_refl. Qed.
Lemma D_5b72c : decode_any W_5b72c = Some (Store SZ8 2 18 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b730 : bv 32 := 0x01313423.
Lemma F_5b730 : fetch_word Asan.M.loaded_segments (0x5b780 : word) = Some W_5b730.
Proof. vm_refl. Qed.
Lemma D_5b730 : decode_any W_5b730 = Some (Store SZ8 2 19 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b734 : bv 32 := 0x01413023.
Lemma F_5b734 : fetch_word Asan.M.loaded_segments (0x5b784 : word) = Some W_5b734.
Proof. vm_refl. Qed.
Lemma D_5b734 : decode_any W_5b734 = Some (Store SZ8 2 20 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b738 : bv 32 := 0x00058493.
Lemma F_5b738 : fetch_word Asan.M.loaded_segments (0x5b788 : word) = Some W_5b738.
Proof. vm_refl. Qed.
Lemma D_5b738 : decode_any W_5b738 = Some (OpImm ALU_ADD 9 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b73c : bv 32 := 0x00050413.
Lemma F_5b73c : fetch_word Asan.M.loaded_segments (0x5b78c : word) = Some W_5b73c.
Proof. vm_refl. Qed.
Lemma D_5b73c : decode_any W_5b73c = Some (OpImm ALU_ADD 8 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b740 : bv 32 := 0x000fe517.
Lemma F_5b740 : fetch_word Asan.M.loaded_segments (0x5b790 : word) = Some W_5b740.
Proof. vm_refl. Qed.
Lemma D_5b740 : decode_any W_5b740 = Some (Auipc 10 254, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b744 : bv 32 := 0xbc850993.
Lemma F_5b744 : fetch_word Asan.M.loaded_segments (0x5b794 : word) = Some W_5b744.
Proof. vm_refl. Qed.
Lemma D_5b744 : decode_any W_5b744 = Some (OpImm ALU_ADD 19 10 3016, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b748 : bv 32 := 0x0209b503.
Lemma F_5b748 : fetch_word Asan.M.loaded_segments (0x5b798 : word) = Some W_5b748.
Proof. vm_refl. Qed.
Lemma D_5b748 : decode_any W_5b748 = Some (Load SZ8 true 10 19 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b74c : bv 32 := 0x00100a13.
Lemma F_5b74c : fetch_word Asan.M.loaded_segments (0x5b79c : word) = Some W_5b74c.
Proof. vm_refl. Qed.
Lemma D_5b74c : decode_any W_5b74c = Some (OpImm ALU_ADD 20 0 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b750 : bv 32 := 0x025a1a13.
Lemma F_5b750 : fetch_word Asan.M.loaded_segments (0x5b7a0 : word) = Some W_5b750.
Proof. vm_refl. Qed.
Lemma D_5b750 : decode_any W_5b750 = Some (ShiftImm ALU_SLL 20 20 37, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b754 : bv 32 := 0x02a5ea63.
Lemma F_5b754 : fetch_word Asan.M.loaded_segments (0x5b7a4 : word) = Some W_5b754.
Proof. vm_refl. Qed.
Lemma D_5b754 : decode_any W_5b754 = Some (Branch BC_LTU 11 10 52, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b758 : bv 32 := 0x014505b3.
Lemma F_5b758 : fetch_word Asan.M.loaded_segments (0x5b7a8 : word) = Some W_5b758.
Proof. vm_refl. Qed.
Lemma D_5b758 : decode_any W_5b758 = Some (Op ALU_ADD 11 10 20, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b75c : bv 32 := 0x02b4f663.
Lemma F_5b75c : fetch_word Asan.M.loaded_segments (0x5b7ac : word) = Some W_5b75c.
Proof. vm_refl. Qed.
Lemma D_5b75c : decode_any W_5b75c = Some (Branch BC_GEU 9 11 44, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b760 : bv 32 := 0x40a48733.
Lemma F_5b760 : fetch_word Asan.M.loaded_segments (0x5b7b0 : word) = Some W_5b760.
Proof. vm_refl. Qed.
Lemma D_5b760 : decode_any W_5b760 = Some (Op ALU_SUB 14 9 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b764 : bv 32 := 0x02075693.
Lemma F_5b764 : fetch_word Asan.M.loaded_segments (0x5b7b4 : word) = Some W_5b764.
Proof. vm_refl. Qed.
Lemma D_5b764 : decode_any W_5b764 = Some (ShiftImm ALU_SRL 13 14 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b768 : bv 32 := 0x01f6f613.
Lemma F_5b768 : fetch_word Asan.M.loaded_segments (0x5b7b8 : word) = Some W_5b768.
Proof. vm_refl. Qed.
Lemma D_5b768 : decode_any W_5b768 = Some (OpImm ALU_AND 12 13 31, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b76c : bv 32 := 0x01f00793.
Lemma F_5b76c : fetch_word Asan.M.loaded_segments (0x5b7bc : word) = Some W_5b76c.
Proof. vm_refl. Qed.
Lemma D_5b76c : decode_any W_5b76c = Some (OpImm ALU_ADD 15 0 31, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b770 : bv 32 := 0x1ef60663.
Lemma F_5b770 : fetch_word Asan.M.loaded_segments (0x5b7c0 : word) = Some W_5b770.
Proof. vm_refl. Qed.
Lemma D_5b770 : decode_any W_5b770 = Some (Branch BC_EQ 12 15 492, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b774 : bv 32 := 0x01100793.
Lemma F_5b774 : fetch_word Asan.M.loaded_segments (0x5b7c4 : word) = Some W_5b774.
Proof. vm_refl. Qed.
Lemma D_5b774 : decode_any W_5b774 = Some (OpImm ALU_ADD 15 0 17, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b778 : bv 32 := 0x02f67863.
Lemma F_5b778 : fetch_word Asan.M.loaded_segments (0x5b7c8 : word) = Some W_5b778.
Proof. vm_refl. Qed.
Lemma D_5b778 : decode_any W_5b778 = Some (Branch BC_GEU 12 15 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b77c : bv 32 := 0x1c060a63.
Lemma F_5b77c : fetch_word Asan.M.loaded_segments (0x5b7cc : word) = Some W_5b77c.
Proof. vm_refl. Qed.
Lemma D_5b77c : decode_any W_5b77c = Some (Branch BC_EQ 12 0 468, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b780 : bv 32 := 0x00561793.
Lemma F_5b780 : fetch_word Asan.M.loaded_segments (0x5b7d0 : word) = Some W_5b780.
Proof. vm_refl. Qed.
Lemma D_5b780 : decode_any W_5b780 = Some (ShiftImm ALU_SLL 15 12 5, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b784 : bv 32 := 0x0480006f.
Lemma F_5b784 : fetch_word Asan.M.loaded_segments (0x5b7d4 : word) = Some W_5b784.
Proof. vm_refl. Qed.
Lemma D_5b784 : decode_any W_5b784 = Some (Jal 0 72, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b788 : bv 32 := 0x04098513.
Lemma F_5b788 : fetch_word Asan.M.loaded_segments (0x5b7d8 : word) = Some W_5b788.
Proof. vm_refl. Qed.
Lemma D_5b788 : decode_any W_5b788 = Some (OpImm ALU_ADD 10 19 64, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b78c : bv 32 := 0x00048593.
Lemma F_5b78c : fetch_word Asan.M.loaded_segments (0x5b7dc : word) = Some W_5b78c.
Proof. vm_refl. Qed.
Lemma D_5b78c : decode_any W_5b78c = Some (OpImm ALU_ADD 11 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b790 : bv 32 := 0x210000ef.
Lemma F_5b790 : fetch_word Asan.M.loaded_segments (0x5b7e0 : word) = Some W_5b790.
Proof. vm_refl. Qed.
Lemma D_5b790 : decode_any W_5b790 = Some (Jal 1 528, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b794 : bv 32 := 0x00050913.
Lemma F_5b794 : fetch_word Asan.M.loaded_segments (0x5b7e4 : word) = Some W_5b794.
Proof. vm_refl. Qed.
Lemma D_5b794 : decode_any W_5b794 = Some (OpImm ALU_ADD 18 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b798 : bv 32 := 0x0209b503.
Lemma F_5b798 : fetch_word Asan.M.loaded_segments (0x5b7e8 : word) = Some W_5b798.
Proof. vm_refl. Qed.
Lemma D_5b798 : decode_any W_5b798 = Some (Load SZ8 true 10 19 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b79c : bv 32 := 0x014505b3.
Lemma F_5b79c : fetch_word Asan.M.loaded_segments (0x5b7ec : word) = Some W_5b79c.
Proof. vm_refl. Qed.
Lemma D_5b79c : decode_any W_5b79c = Some (Op ALU_ADD 11 10 20, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b7a0 : bv 32 := 0x06a97663.
Lemma F_5b7a0 : fetch_word Asan.M.loaded_segments (0x5b7f0 : word) = Some W_5b7a0.
Proof. vm_refl. Qed.
Lemma D_5b7a0 : decode_any W_5b7a0 = Some (Branch BC_GEU 18 10 108, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b7a4 : bv 32 := 0x0e40006f.
Lemma F_5b7a4 : fetch_word Asan.M.loaded_segments (0x5b7f4 : word) = Some W_5b7a4.
Proof. vm_refl. Qed.
Lemma D_5b7a4 : decode_any W_5b7a4 = Some (Jal 0 228, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b7a8 : bv 32 := 0xff060793.
Lemma F_5b7a8 : fetch_word Asan.M.loaded_segments (0x5b7f8 : word) = Some W_5b7a8.
Proof. vm_refl. Qed.
Lemma D_5b7a8 : decode_any W_5b7a8 = Some (OpImm ALU_ADD 15 12 4080, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b7ac : bv 32 := 0x20000813.
Lemma F_5b7ac : fetch_word Asan.M.loaded_segments (0x5b7fc : word) = Some W_5b7ac.
Proof. vm_refl. Qed.
Lemma D_5b7ac : decode_any W_5b7ac = Some (OpImm ALU_ADD 16 0 512, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b7b0 : bv 32 := 0x03f69893.
Lemma F_5b7b0 : fetch_word Asan.M.loaded_segments (0x5b800 : word) = Some W_5b7b0.
Proof. vm_refl. Qed.
Lemma D_5b7b0 : decode_any W_5b7b0 = Some (ShiftImm ALU_SLL 17 13 63, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b7b4 : bv 32 := 0x0017d793.
Lemma F_5b7b4 : fetch_word Asan.M.loaded_segments (0x5b804 : word) = Some W_5b7b4.
Proof. vm_refl. Qed.
Lemma D_5b7b4 : decode_any W_5b7b4 = Some (ShiftImm ALU_SRL 15 15 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b7b8 : bv 32 := 0x00f817b3.
Lemma F_5b7b8 : fetch_word Asan.M.loaded_segments (0x5b808 : word) = Some W_5b7b8.
Proof. vm_refl. Qed.
Lemma D_5b7b8 : decode_any W_5b7b8 = Some (Op ALU_SLL 15 16 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b7bc : bv 32 := 0x0017d813.
Lemma F_5b7bc : fetch_word Asan.M.loaded_segments (0x5b80c : word) = Some W_5b7bc.
Proof. vm_refl. Qed.
Lemma D_5b7bc : decode_any W_5b7bc = Some (ShiftImm ALU_SRL 16 15 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b7c0 : bv 32 := 0x43f8d893.
Lemma F_5b7c0 : fetch_word Asan.M.loaded_segments (0x5b810 : word) = Some W_5b7c0.
Proof. vm_refl. Qed.
Lemma D_5b7c0 : decode_any W_5b7c0 = Some (ShiftImm ALU_SRA 17 17 63, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b7c4 : bv 32 := 0x0108f833.
Lemma F_5b7c4 : fetch_word Asan.M.loaded_segments (0x5b814 : word) = Some W_5b7c4.
Proof. vm_refl. Qed.
Lemma D_5b7c4 : decode_any W_5b7c4 = Some (Op ALU_AND 16 17 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b7c8 : bv 32 := 0x00f807b3.
Lemma F_5b7c8 : fetch_word Asan.M.loaded_segments (0x5b818 : word) = Some W_5b7c8.
Proof. vm_refl. Qed.
Lemma D_5b7c8 : decode_any W_5b7c8 = Some (Op ALU_ADD 15 16 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b7cc : bv 32 := 0x02f7573b.
Lemma F_5b7cc : fetch_word Asan.M.loaded_segments (0x5b81c : word) = Some W_5b7cc.
Proof. vm_refl. Qed.
Lemma D_5b7cc : decode_any W_5b7cc = Some (Mul32 M_DIVU 14 14 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b7d0 : bv 32 := 0x02069693.
Lemma F_5b7d0 : fetch_word Asan.M.loaded_segments (0x5b820 : word) = Some W_5b7d0.
Proof. vm_refl. Qed.
Lemma D_5b7d0 : decode_any W_5b7d0 = Some (ShiftImm ALU_SLL 13 13 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b7d4 : bv 32 := 0x0309b803.
Lemma F_5b7d4 : fetch_word Asan.M.loaded_segments (0x5b824 : word) = Some W_5b7d4.
Proof. vm_refl. Qed.
Lemma D_5b7d4 : decode_any W_5b7d4 = Some (Load SZ8 true 16 19 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b7d8 : bv 32 := 0x00761613.
Lemma F_5b7d8 : fetch_word Asan.M.loaded_segments (0x5b828 : word) = Some W_5b7d8.
Proof. vm_refl. Qed.
Lemma D_5b7d8 : decode_any W_5b7d8 = Some (ShiftImm ALU_SLL 12 12 7, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b7dc : bv 32 := 0x02071713.
Lemma F_5b7dc : fetch_word Asan.M.loaded_segments (0x5b82c : word) = Some W_5b7dc.
Proof. vm_refl. Qed.
Lemma D_5b7dc : decode_any W_5b7dc = Some (ShiftImm ALU_SLL 14 14 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b7e0 : bv 32 := 0x00a686b3.
Lemma F_5b7e0 : fetch_word Asan.M.loaded_segments (0x5b830 : word) = Some W_5b7e0.
Proof. vm_refl. Qed.
Lemma D_5b7e0 : decode_any W_5b7e0 = Some (Op ALU_ADD 13 13 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b7e4 : bv 32 := 0x00c80633.
Lemma F_5b7e4 : fetch_word Asan.M.loaded_segments (0x5b834 : word) = Some W_5b7e4.
Proof. vm_refl. Qed.
Lemma D_5b7e4 : decode_any W_5b7e4 = Some (Op ALU_ADD 12 16 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b7e8 : bv 32 := 0x03063603.
Lemma F_5b7e8 : fetch_word Asan.M.loaded_segments (0x5b838 : word) = Some W_5b7e8.
Proof. vm_refl. Qed.
Lemma D_5b7e8 : decode_any W_5b7e8 = Some (Load SZ8 true 12 12 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b7ec : bv 32 := 0x02075713.
Lemma F_5b7ec : fetch_word Asan.M.loaded_segments (0x5b83c : word) = Some W_5b7ec.
Proof. vm_refl. Qed.
Lemma D_5b7ec : decode_any W_5b7ec = Some (ShiftImm ALU_SRL 14 14 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b7f0 : bv 32 := 0x02e78733.
Lemma F_5b7f0 : fetch_word Asan.M.loaded_segments (0x5b840 : word) = Some W_5b7f0.
Proof. vm_refl. Qed.
Lemma D_5b7f0 : decode_any W_5b7f0 = Some (Mul M_MUL 14 15 14, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b7f4 : bv 32 := 0x00f707b3.
Lemma F_5b7f4 : fetch_word Asan.M.loaded_segments (0x5b844 : word) = Some W_5b7f4.
Proof. vm_refl. Qed.
Lemma D_5b7f4 : decode_any W_5b7f4 = Some (Op ALU_ADD 15 14 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b7f8 : bv 32 := 0x00f63633.
Lemma F_5b7f8 : fetch_word Asan.M.loaded_segments (0x5b848 : word) = Some W_5b7f8.
Proof. vm_refl. Qed.
Lemma D_5b7f8 : decode_any W_5b7f8 = Some (Op ALU_SLTU 12 12 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b7fc : bv 32 := 0x00e686b3.
Lemma F_5b7fc : fetch_word Asan.M.loaded_segments (0x5b84c : word) = Some W_5b7fc.
Proof. vm_refl. Qed.
Lemma D_5b7fc : decode_any W_5b7fc = Some (Op ALU_ADD 13 13 14, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b800 : bv 32 := 0xfff60613.
Lemma F_5b800 : fetch_word Asan.M.loaded_segments (0x5b850 : word) = Some W_5b800.
Proof. vm_refl. Qed.
Lemma D_5b800 : decode_any W_5b800 = Some (OpImm ALU_ADD 12 12 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b804 : bv 32 := 0x00d67933.
Lemma F_5b804 : fetch_word Asan.M.loaded_segments (0x5b854 : word) = Some W_5b804.
Proof. vm_refl. Qed.
Lemma D_5b804 : decode_any W_5b804 = Some (Op ALU_AND 18 12 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b808 : bv 32 := 0x08a96063.
Lemma F_5b808 : fetch_word Asan.M.loaded_segments (0x5b858 : word) = Some W_5b808.
Proof. vm_refl. Qed.
Lemma D_5b808 : decode_any W_5b808 = Some (Branch BC_LTU 18 10 128, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b80c : bv 32 := 0x06b97e63.
Lemma F_5b80c : fetch_word Asan.M.loaded_segments (0x5b85c : word) = Some W_5b80c.
Proof. vm_refl. Qed.
Lemma D_5b80c : decode_any W_5b80c = Some (Branch BC_GEU 18 11 124, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b810 : bv 32 := 0x00990e63.
Lemma F_5b810 : fetch_word Asan.M.loaded_segments (0x5b860 : word) = Some W_5b810.
Proof. vm_refl. Qed.
Lemma D_5b810 : decode_any W_5b810 = Some (Branch BC_EQ 18 9 28, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b814 : bv 32 := 0xfffb5517.
Lemma F_5b814 : fetch_word Asan.M.loaded_segments (0x5b864 : word) = Some W_5b814.
Proof. vm_refl. Qed.
Lemma D_5b814 : decode_any W_5b814 = Some (Auipc 10 1048501, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b818 : bv 32 := 0xb1453703.
Lemma F_5b818 : fetch_word Asan.M.loaded_segments (0x5b868 : word) = Some W_5b818.
Proof. vm_refl. Qed.
Lemma D_5b818 : decode_any W_5b818 = Some (Load SZ8 true 14 10 2836, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b81c : bv 32 := 0x160936af.
Lemma F_5b81c : fetch_word Asan.M.loaded_segments (0x5b86c : word) = Some W_5b81c.
Proof. vm_refl. Qed.
Lemma D_5b81c : decode_any W_5b81c = Some (Lr AD true true 13 18, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b820 : bv 32 := 0x16e69463.
Lemma F_5b820 : fetch_word Asan.M.loaded_segments (0x5b870 : word) = Some W_5b820.
Proof. vm_refl. Qed.
Lemma D_5b820 : decode_any W_5b820 = Some (Branch BC_NE 13 14 360, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b824 : bv 32 := 0x1a09352f.
Lemma F_5b824 : fetch_word Asan.M.loaded_segments (0x5b874 : word) = Some W_5b824.
Proof. vm_refl. Qed.
Lemma D_5b824 : decode_any W_5b824 = Some (Sc AD false true 10 18 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b828 : bv 32 := 0xfe051ae3.
Lemma F_5b828 : fetch_word Asan.M.loaded_segments (0x5b878 : word) = Some W_5b828.
Proof. vm_refl. Qed.
Lemma D_5b828 : decode_any W_5b828 = Some (Branch BC_NE 10 0 8180, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b82c : bv 32 := 0xffc4f613.
Lemma F_5b82c : fetch_word Asan.M.loaded_segments (0x5b87c : word) = Some W_5b82c.
Proof. vm_refl. Qed.
Lemma D_5b82c : decode_any W_5b82c = Some (OpImm ALU_AND 12 9 4092, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b830 : bv 32 := 0x00349513.
Lemma F_5b830 : fetch_word Asan.M.loaded_segments (0x5b880 : word) = Some W_5b830.
Proof. vm_refl. Qed.
Lemma D_5b830 : decode_any W_5b830 = Some (ShiftImm ALU_SLL 10 9 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b834 : bv 32 := 0x0ff00593.
Lemma F_5b834 : fetch_word Asan.M.loaded_segments (0x5b884 : word) = Some W_5b834.
Proof. vm_refl. Qed.
Lemma D_5b834 : decode_any W_5b834 = Some (OpImm ALU_ADD 11 0 255, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b838 : bv 32 := 0x00300693.
Lemma F_5b838 : fetch_word Asan.M.loaded_segments (0x5b888 : word) = Some W_5b838.
Proof. vm_refl. Qed.
Lemma D_5b838 : decode_any W_5b838 = Some (OpImm ALU_ADD 13 0 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b83c : bv 32 := 0x00a5973b.
Lemma F_5b83c : fetch_word Asan.M.loaded_segments (0x5b88c : word) = Some W_5b83c.
Proof. vm_refl. Qed.
Lemma D_5b83c : decode_any W_5b83c = Some (Op32 ALU_SLL 14 11 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b840 : bv 32 := 0x00a696bb.
Lemma F_5b840 : fetch_word Asan.M.loaded_segments (0x5b890 : word) = Some W_5b840.
Proof. vm_refl. Qed.
Lemma D_5b840 : decode_any W_5b840 = Some (Op32 ALU_SLL 13 13 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b844 : bv 32 := 0x160625af.
Lemma F_5b844 : fetch_word Asan.M.loaded_segments (0x5b894 : word) = Some W_5b844.
Proof. vm_refl. Qed.
Lemma D_5b844 : decode_any W_5b844 = Some (Lr AW true true 11 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b848 : bv 32 := 0x00e5f7b3.
Lemma F_5b848 : fetch_word Asan.M.loaded_segments (0x5b898 : word) = Some W_5b848.
Proof. vm_refl. Qed.
Lemma D_5b848 : decode_any W_5b848 = Some (Op ALU_AND 15 11 14, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b84c : bv 32 := 0x10d79c63.
Lemma F_5b84c : fetch_word Asan.M.loaded_segments (0x5b89c : word) = Some W_5b84c.
Proof. vm_refl. Qed.
Lemma D_5b84c : decode_any W_5b84c = Some (Branch BC_NE 15 13 280, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b850 : bv 32 := 0x0005c7b3.
Lemma F_5b850 : fetch_word Asan.M.loaded_segments (0x5b8a0 : word) = Some W_5b850.
Proof. vm_refl. Qed.
Lemma D_5b850 : decode_any W_5b850 = Some (Op ALU_XOR 15 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b854 : bv 32 := 0x00e7f7b3.
Lemma F_5b854 : fetch_word Asan.M.loaded_segments (0x5b8a4 : word) = Some W_5b854.
Proof. vm_refl. Qed.
Lemma D_5b854 : decode_any W_5b854 = Some (Op ALU_AND 15 15 14, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b858 : bv 32 := 0x00f5c7b3.
Lemma F_5b858 : fetch_word Asan.M.loaded_segments (0x5b8a8 : word) = Some W_5b858.
Proof. vm_refl. Qed.
Lemma D_5b858 : decode_any W_5b858 = Some (Op ALU_XOR 15 11 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b85c : bv 32 := 0x1af627af.
Lemma F_5b85c : fetch_word Asan.M.loaded_segments (0x5b8ac : word) = Some W_5b85c.
Proof. vm_refl. Qed.
Lemma D_5b85c : decode_any W_5b85c = Some (Sc AW false true 15 12 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b860 : bv 32 := 0xfe0792e3.
Lemma F_5b860 : fetch_word Asan.M.loaded_segments (0x5b8b0 : word) = Some W_5b860.
Proof. vm_refl. Qed.
Lemma D_5b860 : decode_any W_5b860 = Some (Branch BC_NE 15 0 8164, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b864 : bv 32 := 0x0024d583.
Lemma F_5b864 : fetch_word Asan.M.loaded_segments (0x5b8b4 : word) = Some W_5b864.
Proof. vm_refl. Qed.
Lemma D_5b864 : decode_any W_5b864 = Some (Load SZ2 false 11 9 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b868 : bv 32 := 0x0044e603.
Lemma F_5b868 : fetch_word Asan.M.loaded_segments (0x5b8b8 : word) = Some W_5b868.
Proof. vm_refl. Qed.
Lemma D_5b868 : decode_any W_5b868 = Some (Load SZ4 false 12 9 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b86c : bv 32 := 0x01048513.
Lemma F_5b86c : fetch_word Asan.M.loaded_segments (0x5b8bc : word) = Some W_5b86c.
Proof. vm_refl. Qed.
Lemma D_5b86c : decode_any W_5b86c = Some (OpImm ALU_ADD 10 9 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b870 : bv 32 := 0x02059593.
Lemma F_5b870 : fetch_word Asan.M.loaded_segments (0x5b8c0 : word) = Some W_5b870.
Proof. vm_refl. Qed.
Lemma D_5b870 : decode_any W_5b870 = Some (ShiftImm ALU_SLL 11 11 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b874 : bv 32 := 0x00c5e5b3.
Lemma F_5b874 : fetch_word Asan.M.loaded_segments (0x5b8c4 : word) = Some W_5b874.
Proof. vm_refl. Qed.
Lemma D_5b874 : decode_any W_5b874 = Some (Op ALU_OR 11 11 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b878 : bv 32 := 0x00758593.
Lemma F_5b878 : fetch_word Asan.M.loaded_segments (0x5b8c8 : word) = Some W_5b878.
Proof. vm_refl. Qed.
Lemma D_5b878 : decode_any W_5b878 = Some (OpImm ALU_ADD 11 11 7, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b87c : bv 32 := 0xff85f593.
Lemma F_5b87c : fetch_word Asan.M.loaded_segments (0x5b8cc : word) = Some W_5b87c.
Proof. vm_refl. Qed.
Lemma D_5b87c : decode_any W_5b87c = Some (OpImm ALU_AND 11 11 4088, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b880 : bv 32 := 0x0fa00613.
Lemma F_5b880 : fetch_word Asan.M.loaded_segments (0x5b8d0 : word) = Some W_5b880.
Proof. vm_refl. Qed.
Lemma D_5b880 : decode_any W_5b880 = Some (OpImm ALU_ADD 12 0 250, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b884 : bv 32 := 0x444260ef.
Lemma F_5b884 : fetch_word Asan.M.loaded_segments (0x5b8d4 : word) = Some W_5b884.
Proof. vm_refl. Qed.
Lemma D_5b884 : decode_any W_5b884 = Some (Jal 1 156740, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b888 : bv 32 := 0x3b82e0ef.
Lemma F_5b888 : fetch_word Asan.M.loaded_segments (0x5b8d8 : word) = Some W_5b888.
Proof. vm_refl. Qed.
Lemma D_5b888 : decode_any W_5b888 = Some (Jal 1 189368, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b88c : bv 32 := 0x0024d583.
Lemma F_5b88c : fetch_word Asan.M.loaded_segments (0x5b8dc : word) = Some W_5b88c.
Proof. vm_refl. Qed.
Lemma D_5b88c : decode_any W_5b88c = Some (Load SZ2 false 11 9 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b890 : bv 32 := 0x0044e603.
Lemma F_5b890 : fetch_word Asan.M.loaded_segments (0x5b8e0 : word) = Some W_5b890.
Proof. vm_refl. Qed.
Lemma D_5b890 : decode_any W_5b890 = Some (Load SZ4 false 12 9 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b894 : bv 32 := 0x03053683.
Lemma F_5b894 : fetch_word Asan.M.loaded_segments (0x5b8e4 : word) = Some W_5b894.
Proof. vm_refl. Qed.
Lemma D_5b894 : decode_any W_5b894 = Some (Load SZ8 true 13 10 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b898 : bv 32 := 0x02853703.
Lemma F_5b898 : fetch_word Asan.M.loaded_segments (0x5b8e8 : word) = Some W_5b898.
Proof. vm_refl. Qed.
Lemma D_5b898 : decode_any W_5b898 = Some (Load SZ8 true 14 10 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b89c : bv 32 := 0x02059593.
Lemma F_5b89c : fetch_word Asan.M.loaded_segments (0x5b8ec : word) = Some W_5b89c.
Proof. vm_refl. Qed.
Lemma D_5b89c : decode_any W_5b89c = Some (ShiftImm ALU_SLL 11 11 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b8a0 : bv 32 := 0x00c5e5b3.
Lemma F_5b8a0 : fetch_word Asan.M.loaded_segments (0x5b8f0 : word) = Some W_5b8a0.
Proof. vm_refl. Qed.
Lemma D_5b8a0 : decode_any W_5b8a0 = Some (Op ALU_OR 11 11 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b8a4 : bv 32 := 0x00d585b3.
Lemma F_5b8a4 : fetch_word Asan.M.loaded_segments (0x5b8f4 : word) = Some W_5b8a4.
Proof. vm_refl. Qed.
Lemma D_5b8a4 : decode_any W_5b8a4 = Some (Op ALU_ADD 11 11 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b8a8 : bv 32 := 0x00170713.
Lemma F_5b8a8 : fetch_word Asan.M.loaded_segments (0x5b8f8 : word) = Some W_5b8a8.
Proof. vm_refl. Qed.
Lemma D_5b8a8 : decode_any W_5b8a8 = Some (OpImm ALU_ADD 14 14 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b8ac : bv 32 := 0x02e53423.
Lemma F_5b8ac : fetch_word Asan.M.loaded_segments (0x5b8fc : word) = Some W_5b8ac.
Proof. vm_refl. Qed.
Lemma D_5b8ac : decode_any W_5b8ac = Some (Store SZ8 10 14 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b8b0 : bv 32 := 0x02b53823.
Lemma F_5b8b0 : fetch_word Asan.M.loaded_segments (0x5b900 : word) = Some W_5b8b0.
Proof. vm_refl. Qed.
Lemma D_5b8b0 : decode_any W_5b8b0 = Some (Store SZ8 10 11 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b8b4 : bv 32 := 0x04090863.
Lemma F_5b8b4 : fetch_word Asan.M.loaded_segments (0x5b904 : word) = Some W_5b8b4.
Proof. vm_refl. Qed.
Lemma D_5b8b4 : decode_any W_5b8b4 = Some (Branch BC_EQ 18 0 80, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b8b8 : bv 32 := 0x0209b583.
Lemma F_5b8b8 : fetch_word Asan.M.loaded_segments (0x5b908 : word) = Some W_5b8b8.
Proof. vm_refl. Qed.
Lemma D_5b8b8 : decode_any W_5b8b8 = Some (Load SZ8 true 11 19 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b8bc : bv 32 := 0x06b96463.
Lemma F_5b8bc : fetch_word Asan.M.loaded_segments (0x5b90c : word) = Some W_5b8bc.
Proof. vm_refl. Qed.
Lemma D_5b8bc : decode_any W_5b8bc = Some (Branch BC_LTU 18 11 104, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b8c0 : bv 32 := 0x01458a33.
Lemma F_5b8c0 : fetch_word Asan.M.loaded_segments (0x5b910 : word) = Some W_5b8c0.
Proof. vm_refl. Qed.
Lemma D_5b8c0 : decode_any W_5b8c0 = Some (Op ALU_ADD 20 11 20, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b8c4 : bv 32 := 0x07497063.
Lemma F_5b8c4 : fetch_word Asan.M.loaded_segments (0x5b914 : word) = Some W_5b8c4.
Proof. vm_refl. Qed.
Lemma D_5b8c4 : decode_any W_5b8c4 = Some (Branch BC_GEU 18 20 96, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b8c8 : bv 32 := 0x00043503.
Lemma F_5b8c8 : fetch_word Asan.M.loaded_segments (0x5b918 : word) = Some W_5b8c8.
Proof. vm_refl. Qed.
Lemma D_5b8c8 : decode_any W_5b8c8 = Some (Load SZ8 true 10 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b8cc : bv 32 := 0x40b905b3.
Lemma F_5b8cc : fetch_word Asan.M.loaded_segments (0x5b91c : word) = Some W_5b8cc.
Proof. vm_refl. Qed.
Lemma D_5b8cc : decode_any W_5b8cc = Some (Op ALU_SUB 11 18 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b8d0 : bv 32 := 0x01b59593.
Lemma F_5b8d0 : fetch_word Asan.M.loaded_segments (0x5b920 : word) = Some W_5b8d0.
Proof. vm_refl. Qed.
Lemma D_5b8d0 : decode_any W_5b8d0 = Some (ShiftImm ALU_SLL 11 11 27, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b8d4 : bv 32 := 0x03b5d613.
Lemma F_5b8d4 : fetch_word Asan.M.loaded_segments (0x5b924 : word) = Some W_5b8d4.
Proof. vm_refl. Qed.
Lemma D_5b8d4 : decode_any W_5b8d4 = Some (ShiftImm ALU_SRL 12 11 59, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b8d8 : bv 32 := 0x000fe597.
Lemma F_5b8d8 : fetch_word Asan.M.loaded_segments (0x5b928 : word) = Some W_5b8d8.
Proof. vm_refl. Qed.
Lemma D_5b8d8 : decode_any W_5b8d8 = Some (Auipc 11 254, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b8dc : bv 32 := 0xa3058593.
Lemma F_5b8dc : fetch_word Asan.M.loaded_segments (0x5b92c : word) = Some W_5b8dc.
Proof. vm_refl. Qed.
Lemma D_5b8dc : decode_any W_5b8dc = Some (OpImm ALU_ADD 11 11 2608, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b8e0 : bv 32 := 0x00090693.
Lemma F_5b8e0 : fetch_word Asan.M.loaded_segments (0x5b930 : word) = Some W_5b8e0.
Proof. vm_refl. Qed.
Lemma D_5b8e0 : decode_any W_5b8e0 = Some (OpImm ALU_ADD 13 18 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b8e4 : bv 32 := 0x02813083.
Lemma F_5b8e4 : fetch_word Asan.M.loaded_segments (0x5b934 : word) = Some W_5b8e4.
Proof. vm_refl. Qed.
Lemma D_5b8e4 : decode_any W_5b8e4 = Some (Load SZ8 true 1 2 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b8e8 : bv 32 := 0x02013403.
Lemma F_5b8e8 : fetch_word Asan.M.loaded_segments (0x5b938 : word) = Some W_5b8e8.
Proof. vm_refl. Qed.
Lemma D_5b8e8 : decode_any W_5b8e8 = Some (Load SZ8 true 8 2 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b8ec : bv 32 := 0x01813483.
Lemma F_5b8ec : fetch_word Asan.M.loaded_segments (0x5b93c : word) = Some W_5b8ec.
Proof. vm_refl. Qed.
Lemma D_5b8ec : decode_any W_5b8ec = Some (Load SZ8 true 9 2 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b8f0 : bv 32 := 0x01013903.
Lemma F_5b8f0 : fetch_word Asan.M.loaded_segments (0x5b940 : word) = Some W_5b8f0.
Proof. vm_refl. Qed.
Lemma D_5b8f0 : decode_any W_5b8f0 = Some (Load SZ8 true 18 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b8f4 : bv 32 := 0x00813983.
Lemma F_5b8f4 : fetch_word Asan.M.loaded_segments (0x5b944 : word) = Some W_5b8f4.
Proof. vm_refl. Qed.
Lemma D_5b8f4 : decode_any W_5b8f4 = Some (Load SZ8 true 19 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b8f8 : bv 32 := 0x00013a03.
Lemma F_5b8f8 : fetch_word Asan.M.loaded_segments (0x5b948 : word) = Some W_5b8f8.
Proof. vm_refl. Qed.
Lemma D_5b8f8 : decode_any W_5b8f8 = Some (Load SZ8 true 20 2 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b8fc : bv 32 := 0x03010113.
Lemma F_5b8fc : fetch_word Asan.M.loaded_segments (0x5b94c : word) = Some W_5b8fc.
Proof. vm_refl. Qed.
Lemma D_5b8fc : decode_any W_5b8fc = Some (OpImm ALU_ADD 2 2 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b900 : bv 32 := 0x2200006f.
Lemma F_5b900 : fetch_word Asan.M.loaded_segments (0x5b950 : word) = Some W_5b900.
Proof. vm_refl. Qed.
Lemma D_5b900 : decode_any W_5b900 = Some (Jal 0 544, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b924 : bv 32 := 0x04098513.
Lemma F_5b924 : fetch_word Asan.M.loaded_segments (0x5b974 : word) = Some W_5b924.
Proof. vm_refl. Qed.
Lemma D_5b924 : decode_any W_5b924 = Some (OpImm ALU_ADD 10 19 64, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b928 : bv 32 := 0x2b098593.
Lemma F_5b928 : fetch_word Asan.M.loaded_segments (0x5b978 : word) = Some W_5b928.
Proof. vm_refl. Qed.
Lemma D_5b928 : decode_any W_5b928 = Some (OpImm ALU_ADD 11 19 688, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b92c : bv 32 := 0x00090613.
Lemma F_5b92c : fetch_word Asan.M.loaded_segments (0x5b97c : word) = Some W_5b92c.
Proof. vm_refl. Qed.
Lemma D_5b92c : decode_any W_5b92c = Some (OpImm ALU_ADD 12 18 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b930 : bv 32 := 0x02813083.
Lemma F_5b930 : fetch_word Asan.M.loaded_segments (0x5b980 : word) = Some W_5b930.
Proof. vm_refl. Qed.
Lemma D_5b930 : decode_any W_5b930 = Some (Load SZ8 true 1 2 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b934 : bv 32 := 0x02013403.
Lemma F_5b934 : fetch_word Asan.M.loaded_segments (0x5b984 : word) = Some W_5b934.
Proof. vm_refl. Qed.
Lemma D_5b934 : decode_any W_5b934 = Some (Load SZ8 true 8 2 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b938 : bv 32 := 0x01813483.
Lemma F_5b938 : fetch_word Asan.M.loaded_segments (0x5b988 : word) = Some W_5b938.
Proof. vm_refl. Qed.
Lemma D_5b938 : decode_any W_5b938 = Some (Load SZ8 true 9 2 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b93c : bv 32 := 0x01013903.
Lemma F_5b93c : fetch_word Asan.M.loaded_segments (0x5b98c : word) = Some W_5b93c.
Proof. vm_refl. Qed.
Lemma D_5b93c : decode_any W_5b93c = Some (Load SZ8 true 18 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b940 : bv 32 := 0x00813983.
Lemma F_5b940 : fetch_word Asan.M.loaded_segments (0x5b990 : word) = Some W_5b940.
Proof. vm_refl. Qed.
Lemma D_5b940 : decode_any W_5b940 = Some (Load SZ8 true 19 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b944 : bv 32 := 0x00013a03.
Lemma F_5b944 : fetch_word Asan.M.loaded_segments (0x5b994 : word) = Some W_5b944.
Proof. vm_refl. Qed.
Lemma D_5b944 : decode_any W_5b944 = Some (Load SZ8 true 20 2 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b948 : bv 32 := 0x03010113.
Lemma F_5b948 : fetch_word Asan.M.loaded_segments (0x5b998 : word) = Some W_5b948.
Proof. vm_refl. Qed.
Lemma D_5b948 : decode_any W_5b948 = Some (OpImm ALU_ADD 2 2 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b94c : bv 32 := 0x39c0006f.
Lemma F_5b94c : fetch_word Asan.M.loaded_segments (0x5b99c : word) = Some W_5b94c.
Proof. vm_refl. Qed.
Lemma D_5b94c : decode_any W_5b94c = Some (Jal 0 924, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b9a0 : bv 32 := 0xfe010113.
Lemma F_5b9a0 : fetch_word Asan.M.loaded_segments (0x5b9f0 : word) = Some W_5b9a0.
Proof. vm_refl. Qed.
Lemma D_5b9a0 : decode_any W_5b9a0 = Some (OpImm ALU_ADD 2 2 4064, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b9a4 : bv 32 := 0x00113c23.
Lemma F_5b9a4 : fetch_word Asan.M.loaded_segments (0x5b9f4 : word) = Some W_5b9a4.
Proof. vm_refl. Qed.
Lemma D_5b9a4 : decode_any W_5b9a4 = Some (Store SZ8 2 1 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b9a8 : bv 32 := 0x00813823.
Lemma F_5b9a8 : fetch_word Asan.M.loaded_segments (0x5b9f8 : word) = Some W_5b9a8.
Proof. vm_refl. Qed.
Lemma D_5b9a8 : decode_any W_5b9a8 = Some (Store SZ8 2 8 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b9ac : bv 32 := 0x00913423.
Lemma F_5b9ac : fetch_word Asan.M.loaded_segments (0x5b9fc : word) = Some W_5b9ac.
Proof. vm_refl. Qed.
Lemma D_5b9ac : decode_any W_5b9ac = Some (Store SZ8 2 9 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b9b0 : bv 32 := 0x01213023.
Lemma F_5b9b0 : fetch_word Asan.M.loaded_segments (0x5ba00 : word) = Some W_5b9b0.
Proof. vm_refl. Qed.
Lemma D_5b9b0 : decode_any W_5b9b0 = Some (Store SZ8 2 18 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b9b4 : bv 32 := 0x26850413.
Lemma F_5b9b4 : fetch_word Asan.M.loaded_segments (0x5ba04 : word) = Some W_5b9b4.
Proof. vm_refl. Qed.
Lemma D_5b9b4 : decode_any W_5b9b4 = Some (OpImm ALU_ADD 8 10 616, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b9b8 : bv 32 := 0x0ff00613.
Lemma F_5b9b8 : fetch_word Asan.M.loaded_segments (0x5ba08 : word) = Some W_5b9b8.
Proof. vm_refl. Qed.
Lemma D_5b9b8 : decode_any W_5b9b8 = Some (OpImm ALU_ADD 12 0 255, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b9bc : bv 32 := 0xffc47693.
Lemma F_5b9bc : fetch_word Asan.M.loaded_segments (0x5ba0c : word) = Some W_5b9bc.
Proof. vm_refl. Qed.
Lemma D_5b9bc : decode_any W_5b9bc = Some (OpImm ALU_AND 13 8 4092, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b9c0 : bv 32 := 0x00100713.
Lemma F_5b9c0 : fetch_word Asan.M.loaded_segments (0x5ba10 : word) = Some W_5b9c0.
Proof. vm_refl. Qed.
Lemma D_5b9c0 : decode_any W_5b9c0 = Some (OpImm ALU_ADD 14 0 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b9c4 : bv 32 := 0x1406a7af.
Lemma F_5b9c4 : fetch_word Asan.M.loaded_segments (0x5ba14 : word) = Some W_5b9c4.
Proof. vm_refl. Qed.
Lemma D_5b9c4 : decode_any W_5b9c4 = Some (Lr AW true false 15 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b9c8 : bv 32 := 0x00070813.
Lemma F_5b9c8 : fetch_word Asan.M.loaded_segments (0x5ba18 : word) = Some W_5b9c8.
Proof. vm_refl. Qed.
Lemma D_5b9c8 : decode_any W_5b9c8 = Some (OpImm ALU_ADD 16 14 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b9cc : bv 32 := 0x0107c833.
Lemma F_5b9cc : fetch_word Asan.M.loaded_segments (0x5ba1c : word) = Some W_5b9cc.
Proof. vm_refl. Qed.
Lemma D_5b9cc : decode_any W_5b9cc = Some (Op ALU_XOR 16 15 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b9d0 : bv 32 := 0x00c87833.
Lemma F_5b9d0 : fetch_word Asan.M.loaded_segments (0x5ba20 : word) = Some W_5b9d0.
Proof. vm_refl. Qed.
Lemma D_5b9d0 : decode_any W_5b9d0 = Some (Op ALU_AND 16 16 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b9d4 : bv 32 := 0x0107c833.
Lemma F_5b9d4 : fetch_word Asan.M.loaded_segments (0x5ba24 : word) = Some W_5b9d4.
Proof. vm_refl. Qed.
Lemma D_5b9d4 : decode_any W_5b9d4 = Some (Op ALU_XOR 16 15 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b9d8 : bv 32 := 0x1906a82f.
Lemma F_5b9d8 : fetch_word Asan.M.loaded_segments (0x5ba28 : word) = Some W_5b9d8.
Proof. vm_refl. Qed.
Lemma D_5b9d8 : decode_any W_5b9d8 = Some (Sc AW false false 16 13 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b9dc : bv 32 := 0xfe0814e3.
Lemma F_5b9dc : fetch_word Asan.M.loaded_segments (0x5ba2c : word) = Some W_5b9dc.
Proof. vm_refl. Qed.
Lemma D_5b9dc : decode_any W_5b9dc = Some (Branch BC_NE 16 0 8168, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b9e0 : bv 32 := 0x0ff7f613.
Lemma F_5b9e0 : fetch_word Asan.M.loaded_segments (0x5ba30 : word) = Some W_5b9e0.
Proof. vm_refl. Qed.
Lemma D_5b9e0 : decode_any W_5b9e0 = Some (OpImm ALU_AND 12 15 255, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b9e4 : bv 32 := 0x08061663.
Lemma F_5b9e4 : fetch_word Asan.M.loaded_segments (0x5ba34 : word) = Some W_5b9e4.
Proof. vm_refl. Qed.
Lemma D_5b9e4 : decode_any W_5b9e4 = Some (Branch BC_NE 12 0 140, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b9e8 : bv 32 := 0x03853703.
Lemma F_5b9e8 : fetch_word Asan.M.loaded_segments (0x5ba38 : word) = Some W_5b9e8.
Proof. vm_refl. Qed.
Lemma D_5b9e8 : decode_any W_5b9e8 = Some (Load SZ8 true 14 10 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b9ec : bv 32 := 0x0a070263.
Lemma F_5b9ec : fetch_word Asan.M.loaded_segments (0x5ba3c : word) = Some W_5b9ec.
Proof. vm_refl. Qed.
Lemma D_5b9ec : decode_any W_5b9ec = Some (Branch BC_EQ 14 0 164, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b9f0 : bv 32 := 0x00000693.
Lemma F_5b9f0 : fetch_word Asan.M.loaded_segments (0x5ba40 : word) = Some W_5b9f0.
Proof. vm_refl. Qed.
Lemma D_5b9f0 : decode_any W_5b9f0 = Some (OpImm ALU_ADD 13 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b9f4 : bv 32 := 0x00853603.
Lemma F_5b9f4 : fetch_word Asan.M.loaded_segments (0x5ba44 : word) = Some W_5b9f4.
Proof. vm_refl. Qed.
Lemma D_5b9f4 : decode_any W_5b9f4 = Some (Load SZ8 true 12 10 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b9f8 : bv 32 := 0x00371713.
Lemma F_5b9f8 : fetch_word Asan.M.loaded_segments (0x5ba48 : word) = Some W_5b9f8.
Proof. vm_refl. Qed.
Lemma D_5b9f8 : decode_any W_5b9f8 = Some (ShiftImm ALU_SLL 14 14 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_5b9fc : bv 32 := 0x00e60733.
Lemma F_5b9fc : fetch_word Asan.M.loaded_segments (0x5ba4c : word) = Some W_5b9fc.
Proof. vm_refl. Qed.
Lemma D_5b9fc : decode_any W_5b9fc = Some (Op ALU_ADD 14 12 14, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ba00 : bv 32 := 0x00c0006f.
Lemma F_5ba00 : fetch_word Asan.M.loaded_segments (0x5ba50 : word) = Some W_5ba00.
Proof. vm_refl. Qed.
Lemma D_5ba00 : decode_any W_5ba00 = Some (Jal 0 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ba04 : bv 32 := 0x00860613.
Lemma F_5ba04 : fetch_word Asan.M.loaded_segments (0x5ba54 : word) = Some W_5ba04.
Proof. vm_refl. Qed.
Lemma D_5ba04 : decode_any W_5ba04 = Some (OpImm ALU_ADD 12 12 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ba08 : bv 32 := 0x02e60863.
Lemma F_5ba08 : fetch_word Asan.M.loaded_segments (0x5ba58 : word) = Some W_5ba08.
Proof. vm_refl. Qed.
Lemma D_5ba08 : decode_any W_5ba08 = Some (Branch BC_EQ 12 14 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ba0c : bv 32 := 0x00063783.
Lemma F_5ba0c : fetch_word Asan.M.loaded_segments (0x5ba5c : word) = Some W_5ba0c.
Proof. vm_refl. Qed.
Lemma D_5ba0c : decode_any W_5ba0c = Some (Load SZ8 true 15 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ba10 : bv 32 := 0x40f588b3.
Lemma F_5ba10 : fetch_word Asan.M.loaded_segments (0x5ba60 : word) = Some W_5ba10.
Proof. vm_refl. Qed.
Lemma D_5ba10 : decode_any W_5ba10 = Some (Op ALU_SUB 17 11 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ba14 : bv 32 := 0x40d582b3.
Lemma F_5ba14 : fetch_word Asan.M.loaded_segments (0x5ba64 : word) = Some W_5ba14.
Proof. vm_refl. Qed.
Lemma D_5ba14 : decode_any W_5ba14 = Some (Op ALU_SUB 5 11 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ba18 : bv 32 := 0x00078813.
Lemma F_5ba18 : fetch_word Asan.M.loaded_segments (0x5ba68 : word) = Some W_5ba18.
Proof. vm_refl. Qed.
Lemma D_5ba18 : decode_any W_5ba18 = Some (OpImm ALU_ADD 16 15 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ba1c : bv 32 := 0x0058e863.
Lemma F_5ba1c : fetch_word Asan.M.loaded_segments (0x5ba6c : word) = Some W_5ba1c.
Proof. vm_refl. Qed.
Lemma D_5ba1c : decode_any W_5ba1c = Some (Branch BC_LTU 17 5 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ba20 : bv 32 := 0x00068813.
Lemma F_5ba20 : fetch_word Asan.M.loaded_segments (0x5ba70 : word) = Some W_5ba20.
Proof. vm_refl. Qed.
Lemma D_5ba20 : decode_any W_5ba20 = Some (OpImm ALU_ADD 16 13 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ba24 : bv 32 := 0xfef5e0e3.
Lemma F_5ba24 : fetch_word Asan.M.loaded_segments (0x5ba74 : word) = Some W_5ba24.
Proof. vm_refl. Qed.
Lemma D_5ba24 : decode_any W_5ba24 = Some (Branch BC_LTU 11 15 8160, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ba28 : bv 32 := 0x0080006f.
Lemma F_5ba28 : fetch_word Asan.M.loaded_segments (0x5ba78 : word) = Some W_5ba28.
Proof. vm_refl. Qed.
Lemma D_5ba28 : decode_any W_5ba28 = Some (Jal 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ba2c : bv 32 := 0xfcf5ece3.
Lemma F_5ba2c : fetch_word Asan.M.loaded_segments (0x5ba7c : word) = Some W_5ba2c.
Proof. vm_refl. Qed.
Lemma D_5ba2c : decode_any W_5ba2c = Some (Branch BC_LTU 11 15 8152, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ba30 : bv 32 := 0x00080693.
Lemma F_5ba30 : fetch_word Asan.M.loaded_segments (0x5ba80 : word) = Some W_5ba30.
Proof. vm_refl. Qed.
Lemma D_5ba30 : decode_any W_5ba30 = Some (OpImm ALU_ADD 13 16 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ba34 : bv 32 := 0xfd1ff06f.
Lemma F_5ba34 : fetch_word Asan.M.loaded_segments (0x5ba84 : word) = Some W_5ba34.
Proof. vm_refl. Qed.
Lemma D_5ba34 : decode_any W_5ba34 = Some (Jal 0 2097104, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ba38 : bv 32 := 0x04068c63.
Lemma F_5ba38 : fetch_word Asan.M.loaded_segments (0x5ba88 : word) = Some W_5ba38.
Proof. vm_refl. Qed.
Lemma D_5ba38 : decode_any W_5ba38 = Some (Branch BC_EQ 13 0 88, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ba3c : bv 32 := 0x0006b703.
Lemma F_5ba3c : fetch_word Asan.M.loaded_segments (0x5ba8c : word) = Some W_5ba3c.
Proof. vm_refl. Qed.
Lemma D_5ba3c : decode_any W_5ba3c = Some (Load SZ8 true 14 13 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ba40 : bv 32 := 0x06e6ea63.
Lemma F_5ba40 : fetch_word Asan.M.loaded_segments (0x5ba90 : word) = Some W_5ba40.
Proof. vm_refl. Qed.
Lemma D_5ba40 : decode_any W_5ba40 = Some (Branch BC_LTU 13 14 116, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ba44 : bv 32 := 0x0086b603.
Lemma F_5ba44 : fetch_word Asan.M.loaded_segments (0x5ba94 : word) = Some W_5ba44.
Proof. vm_refl. Qed.
Lemma D_5ba44 : decode_any W_5ba44 = Some (Load SZ8 true 12 13 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ba48 : bv 32 := 0x00e60733.
Lemma F_5ba48 : fetch_word Asan.M.loaded_segments (0x5ba98 : word) = Some W_5ba48.
Proof. vm_refl. Qed.
Lemma D_5ba48 : decode_any W_5ba48 = Some (Op ALU_ADD 14 12 14, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ba4c : bv 32 := 0x08e6f063.
Lemma F_5ba4c : fetch_word Asan.M.loaded_segments (0x5ba9c : word) = Some W_5ba4c.
Proof. vm_refl. Qed.
Lemma D_5ba4c : decode_any W_5ba4c = Some (Branch BC_GEU 13 14 128, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ba50 : bv 32 := 0x08d5ea63.
Lemma F_5ba50 : fetch_word Asan.M.loaded_segments (0x5baa0 : word) = Some W_5ba50.
Proof. vm_refl. Qed.
Lemma D_5ba50 : decode_any W_5ba50 = Some (Branch BC_LTU 11 13 148, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ba54 : bv 32 := 0x02e5fe63.
Lemma F_5ba54 : fetch_word Asan.M.loaded_segments (0x5baa4 : word) = Some W_5ba54.
Proof. vm_refl. Qed.
Lemma D_5ba54 : decode_any W_5ba54 = Some (Branch BC_GEU 11 14 60, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ba58 : bv 32 := 0x00053503.
Lemma F_5ba58 : fetch_word Asan.M.loaded_segments (0x5baa8 : word) = Some W_5ba58.
Proof. vm_refl. Qed.
Lemma D_5ba58 : decode_any W_5ba58 = Some (Load SZ8 true 10 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ba5c : bv 32 := 0xfff50593.
Lemma F_5ba5c : fetch_word Asan.M.loaded_segments (0x5baac : word) = Some W_5ba5c.
Proof. vm_refl. Qed.
Lemma D_5ba5c : decode_any W_5ba5c = Some (OpImm ALU_ADD 11 10 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ba60 : bv 32 := 0x00d5f5b3.
Lemma F_5ba60 : fetch_word Asan.M.loaded_segments (0x5bab0 : word) = Some W_5ba60.
Proof. vm_refl. Qed.
Lemma D_5ba60 : decode_any W_5ba60 = Some (Op ALU_AND 11 11 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ba64 : bv 32 := 0x08059e63.
Lemma F_5ba64 : fetch_word Asan.M.loaded_segments (0x5bab4 : word) = Some W_5ba64.
Proof. vm_refl. Qed.
Lemma D_5ba64 : decode_any W_5ba64 = Some (Branch BC_NE 11 0 156, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ba68 : bv 32 := 0x00d50533.
Lemma F_5ba68 : fetch_word Asan.M.loaded_segments (0x5bab8 : word) = Some W_5ba68.
Proof. vm_refl. Qed.
Lemma D_5ba68 : decode_any W_5ba68 = Some (Op ALU_ADD 10 10 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ba6c : bv 32 := 0x0280006f.
Lemma F_5ba6c : fetch_word Asan.M.loaded_segments (0x5babc : word) = Some W_5ba6c.
Proof. vm_refl. Qed.
Lemma D_5ba6c : decode_any W_5ba6c = Some (Jal 0 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ba94 : bv 32 := 0x0310000f.
Lemma F_5ba94 : fetch_word Asan.M.loaded_segments (0x5bae4 : word) = Some W_5ba94.
Proof. vm_refl. Qed.
Lemma D_5ba94 : decode_any W_5ba94 = Some (Fence 0 3 1 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ba98 : bv 32 := 0x00040023.
Lemma F_5ba98 : fetch_word Asan.M.loaded_segments (0x5bae8 : word) = Some W_5ba98.
Proof. vm_refl. Qed.
Lemma D_5ba98 : decode_any W_5ba98 = Some (Store SZ1 8 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5ba9c : bv 32 := 0x01813083.
Lemma F_5ba9c : fetch_word Asan.M.loaded_segments (0x5baec : word) = Some W_5ba9c.
Proof. vm_refl. Qed.
Lemma D_5ba9c : decode_any W_5ba9c = Some (Load SZ8 true 1 2 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_5baa0 : bv 32 := 0x01013403.
Lemma F_5baa0 : fetch_word Asan.M.loaded_segments (0x5baf0 : word) = Some W_5baa0.
Proof. vm_refl. Qed.
Lemma D_5baa0 : decode_any W_5baa0 = Some (Load SZ8 true 8 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_5baa4 : bv 32 := 0x00813483.
Lemma F_5baa4 : fetch_word Asan.M.loaded_segments (0x5baf4 : word) = Some W_5baa4.
Proof. vm_refl. Qed.
Lemma D_5baa4 : decode_any W_5baa4 = Some (Load SZ8 true 9 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_5baa8 : bv 32 := 0x00013903.
Lemma F_5baa8 : fetch_word Asan.M.loaded_segments (0x5baf8 : word) = Some W_5baa8.
Proof. vm_refl. Qed.
Lemma D_5baa8 : decode_any W_5baa8 = Some (Load SZ8 true 18 2 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5baac : bv 32 := 0x02010113.
Lemma F_5baac : fetch_word Asan.M.loaded_segments (0x5bafc : word) = Some W_5baac.
Proof. vm_refl. Qed.
Lemma D_5baac : decode_any W_5baac = Some (OpImm ALU_ADD 2 2 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_5bab0 : bv 32 := 0x00008067.
Lemma F_5bab0 : fetch_word Asan.M.loaded_segments (0x5bb00 : word) = Some W_5bab0.
Proof. vm_refl. Qed.
Lemma D_5bab0 : decode_any W_5bab0 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5bb20 : bv 32 := 0xfd010113.
Lemma F_5bb20 : fetch_word Asan.M.loaded_segments (0x5bb70 : word) = Some W_5bb20.
Proof. vm_refl. Qed.
Lemma D_5bb20 : decode_any W_5bb20 = Some (OpImm ALU_ADD 2 2 4048, 4%Z).
Proof. vm_refl. Qed.

Definition W_5bb24 : bv 32 := 0x02113423.
Lemma F_5bb24 : fetch_word Asan.M.loaded_segments (0x5bb74 : word) = Some W_5bb24.
Proof. vm_refl. Qed.
Lemma D_5bb24 : decode_any W_5bb24 = Some (Store SZ8 2 1 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_5bb28 : bv 32 := 0x02813023.
Lemma F_5bb28 : fetch_word Asan.M.loaded_segments (0x5bb78 : word) = Some W_5bb28.
Proof. vm_refl. Qed.
Lemma D_5bb28 : decode_any W_5bb28 = Some (Store SZ8 2 8 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_5bb2c : bv 32 := 0x00913c23.
Lemma F_5bb2c : fetch_word Asan.M.loaded_segments (0x5bb7c : word) = Some W_5bb2c.
Proof. vm_refl. Qed.
Lemma D_5bb2c : decode_any W_5bb2c = Some (Store SZ8 2 9 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_5bb30 : bv 32 := 0x01213823.
Lemma F_5bb30 : fetch_word Asan.M.loaded_segments (0x5bb80 : word) = Some W_5bb30.
Proof. vm_refl. Qed.
Lemma D_5bb30 : decode_any W_5bb30 = Some (Store SZ8 2 18 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_5bb34 : bv 32 := 0x01313423.
Lemma F_5bb34 : fetch_word Asan.M.loaded_segments (0x5bb84 : word) = Some W_5bb34.
Proof. vm_refl. Qed.
Lemma D_5bb34 : decode_any W_5bb34 = Some (Store SZ8 2 19 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_5bb38 : bv 32 := 0x01413023.
Lemma F_5bb38 : fetch_word Asan.M.loaded_segments (0x5bb88 : word) = Some W_5bb38.
Proof. vm_refl. Qed.
Lemma D_5bb38 : decode_any W_5bb38 = Some (Store SZ8 2 20 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5bb3c : bv 32 := 0x08060463.
Lemma F_5bb3c : fetch_word Asan.M.loaded_segments (0x5bb8c : word) = Some W_5bb3c.
Proof. vm_refl. Qed.
Lemma D_5bb3c : decode_any W_5bb3c = Some (Branch BC_EQ 12 0 136, 4%Z).
Proof. vm_refl. Qed.

Definition W_5bb40 : bv 32 := 0x02000713.
Lemma F_5bb40 : fetch_word Asan.M.loaded_segments (0x5bb90 : word) = Some W_5bb40.
Proof. vm_refl. Qed.
Lemma D_5bb40 : decode_any W_5bb40 = Some (OpImm ALU_ADD 14 0 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_5bb44 : bv 32 := 0x0ae67063.
Lemma F_5bb44 : fetch_word Asan.M.loaded_segments (0x5bb94 : word) = Some W_5bb44.
Proof. vm_refl. Qed.
Lemma D_5bb44 : decode_any W_5bb44 = Some (Branch BC_GEU 12 14 160, 4%Z).
Proof. vm_refl. Qed.

Definition W_5bb48 : bv 32 := 0x05000713.
Lemma F_5bb48 : fetch_word Asan.M.loaded_segments (0x5bb98 : word) = Some W_5bb48.
Proof. vm_refl. Qed.
Lemma D_5bb48 : decode_any W_5bb48 = Some (OpImm ALU_ADD 14 0 80, 4%Z).
Proof. vm_refl. Qed.

Definition W_5bb4c : bv 32 := 0x02e60433.
Lemma F_5bb4c : fetch_word Asan.M.loaded_segments (0x5bb9c : word) = Some W_5bb4c.
Proof. vm_refl. Qed.
Lemma D_5bb4c : decode_any W_5bb4c = Some (Mul M_MUL 8 12 14, 4%Z).
Proof. vm_refl. Qed.

Definition W_5bb50 : bv 32 := 0x00850433.
Lemma F_5bb50 : fetch_word Asan.M.loaded_segments (0x5bba0 : word) = Some W_5bb50.
Proof. vm_refl. Qed.
Lemma D_5bb50 : decode_any W_5bb50 = Some (Op ALU_ADD 8 10 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_5bb54 : bv 32 := 0x00442783.
Lemma F_5bb54 : fetch_word Asan.M.loaded_segments (0x5bba4 : word) = Some W_5bb54.
Proof. vm_refl. Qed.
Lemma D_5bb54 : decode_any W_5bb54 = Some (Load SZ4 true 15 8 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_5bb58 : bv 32 := 0x0a078863.
Lemma F_5bb58 : fetch_word Asan.M.loaded_segments (0x5bba8 : word) = Some W_5bb58.
Proof. vm_refl. Qed.
Lemma D_5bb58 : decode_any W_5bb58 = Some (Branch BC_EQ 15 0 176, 4%Z).
Proof. vm_refl. Qed.

Definition W_5bb5c : bv 32 := 0x00042703.
Lemma F_5bb5c : fetch_word Asan.M.loaded_segments (0x5bbac : word) = Some W_5bb5c.
Proof. vm_refl. Qed.
Lemma D_5bb5c : decode_any W_5bb5c = Some (Load SZ4 true 14 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5bb60 : bv 32 := 0x14f70863.
Lemma F_5bb60 : fetch_word Asan.M.loaded_segments (0x5bbb0 : word) = Some W_5bb60.
Proof. vm_refl. Qed.
Lemma D_5bb60 : decode_any W_5bb60 = Some (Branch BC_EQ 14 15 336, 4%Z).
Proof. vm_refl. Qed.

Definition W_5bb64 : bv 32 := 0x0205b583.
Lemma F_5bb64 : fetch_word Asan.M.loaded_segments (0x5bbb4 : word) = Some W_5bb64.
Proof. vm_refl. Qed.
Lemma D_5bb64 : decode_any W_5bb64 = Some (Load SZ8 true 11 11 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_5bb68 : bv 32 := 0x02061613.
Lemma F_5bb68 : fetch_word Asan.M.loaded_segments (0x5bbb8 : word) = Some W_5bb68.
Proof. vm_refl. Qed.
Lemma D_5bb68 : decode_any W_5bb68 = Some (ShiftImm ALU_SLL 12 12 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_5bb6c : bv 32 := 0x40c686b3.
Lemma F_5bb6c : fetch_word Asan.M.loaded_segments (0x5bbbc : word) = Some W_5bb6c.
Proof. vm_refl. Qed.
Lemma D_5bb6c : decode_any W_5bb6c = Some (Op ALU_SUB 13 13 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_5bb70 : bv 32 := 0x02071613.
Lemma F_5bb70 : fetch_word Asan.M.loaded_segments (0x5bbc0 : word) = Some W_5bb70.
Proof. vm_refl. Qed.
Lemma D_5bb70 : decode_any W_5bb70 = Some (ShiftImm ALU_SLL 12 14 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_5bb74 : bv 32 := 0x00170713.
Lemma F_5bb74 : fetch_word Asan.M.loaded_segments (0x5bbc4 : word) = Some W_5bb74.
Proof. vm_refl. Qed.
Lemma D_5bb74 : decode_any W_5bb74 = Some (OpImm ALU_ADD 14 14 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_5bb78 : bv 32 := 0x40b686b3.
Lemma F_5bb78 : fetch_word Asan.M.loaded_segments (0x5bbc8 : word) = Some W_5bb78.
Proof. vm_refl. Qed.
Lemma D_5bb78 : decode_any W_5bb78 = Some (Op ALU_SUB 13 13 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_5bb7c : bv 32 := 0x00843583.
Lemma F_5bb7c : fetch_word Asan.M.loaded_segments (0x5bbcc : word) = Some W_5bb7c.
Proof. vm_refl. Qed.
Lemma D_5bb7c : decode_any W_5bb7c = Some (Load SZ8 true 11 8 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_5bb80 : bv 32 := 0x7ff50513.
Lemma F_5bb80 : fetch_word Asan.M.loaded_segments (0x5bbd0 : word) = Some W_5bb80.
Proof. vm_refl. Qed.
Lemma D_5bb80 : decode_any W_5bb80 = Some (OpImm ALU_ADD 10 10 2047, 4%Z).
Proof. vm_refl. Qed.

Definition W_5bb84 : bv 32 := 0x01e65613.
Lemma F_5bb84 : fetch_word Asan.M.loaded_segments (0x5bbd4 : word) = Some W_5bb84.
Proof. vm_refl. Qed.
Lemma D_5bb84 : decode_any W_5bb84 = Some (ShiftImm ALU_SRL 12 12 30, 4%Z).
Proof. vm_refl. Qed.

Definition W_5bb88 : bv 32 := 0x21150513.
Lemma F_5bb88 : fetch_word Asan.M.loaded_segments (0x5bbd8 : word) = Some W_5bb88.
Proof. vm_refl. Qed.
Lemma D_5bb88 : decode_any W_5bb88 = Some (OpImm ALU_ADD 10 10 529, 4%Z).
Proof. vm_refl. Qed.

Definition W_5bb8c : bv 32 := 0x00c40633.
Lemma F_5bb8c : fetch_word Asan.M.loaded_segments (0x5bbdc : word) = Some W_5bb8c.
Proof. vm_refl. Qed.
Lemma D_5bb8c : decode_any W_5bb8c = Some (Op ALU_ADD 12 8 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_5bb90 : bv 32 := 0x0046d693.
Lemma F_5bb90 : fetch_word Asan.M.loaded_segments (0x5bbe0 : word) = Some W_5bb90.
Proof. vm_refl. Qed.
Lemma D_5bb90 : decode_any W_5bb90 = Some (ShiftImm ALU_SRL 13 13 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_5bb94 : bv 32 := 0x00e42023.
Lemma F_5bb94 : fetch_word Asan.M.loaded_segments (0x5bbe4 : word) = Some W_5bb94.
Proof. vm_refl. Qed.
Lemma D_5bb94 : decode_any W_5bb94 = Some (Store SZ4 8 14 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5bb98 : bv 32 := 0x00d62823.
Lemma F_5bb98 : fetch_word Asan.M.loaded_segments (0x5bbe8 : word) = Some W_5bb98.
Proof. vm_refl. Qed.
Lemma D_5bb98 : decode_any W_5bb98 = Some (Store SZ4 12 13 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_5bb9c : bv 32 := 0x40b005b3.
Lemma F_5bb9c : fetch_word Asan.M.loaded_segments (0x5bbec : word) = Some W_5bb9c.
Proof. vm_refl. Qed.
Lemma D_5bb9c : decode_any W_5bb9c = Some (Op ALU_SUB 11 0 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_5bba0 : bv 32 := 0x00b5302f.
Lemma F_5bba0 : fetch_word Asan.M.loaded_segments (0x5bbf0 : word) = Some W_5bba0.
Proof. vm_refl. Qed.
Lemma D_5bba0 : decode_any W_5bba0 = Some (Amo AMO_ADD AD false false 0 10 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_5bba4 : bv 32 := 0x02813083.
Lemma F_5bba4 : fetch_word Asan.M.loaded_segments (0x5bbf4 : word) = Some W_5bba4.
Proof. vm_refl. Qed.
Lemma D_5bba4 : decode_any W_5bba4 = Some (Load SZ8 true 1 2 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_5bba8 : bv 32 := 0x02013403.
Lemma F_5bba8 : fetch_word Asan.M.loaded_segments (0x5bbf8 : word) = Some W_5bba8.
Proof. vm_refl. Qed.
Lemma D_5bba8 : decode_any W_5bba8 = Some (Load SZ8 true 8 2 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_5bbac : bv 32 := 0x01813483.
Lemma F_5bbac : fetch_word Asan.M.loaded_segments (0x5bbfc : word) = Some W_5bbac.
Proof. vm_refl. Qed.
Lemma D_5bbac : decode_any W_5bbac = Some (Load SZ8 true 9 2 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_5bbb0 : bv 32 := 0x01013903.
Lemma F_5bbb0 : fetch_word Asan.M.loaded_segments (0x5bc00 : word) = Some W_5bbb0.
Proof. vm_refl. Qed.
Lemma D_5bbb0 : decode_any W_5bbb0 = Some (Load SZ8 true 18 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_5bbb4 : bv 32 := 0x00813983.
Lemma F_5bbb4 : fetch_word Asan.M.loaded_segments (0x5bc04 : word) = Some W_5bbb4.
Proof. vm_refl. Qed.
Lemma D_5bbb4 : decode_any W_5bbb4 = Some (Load SZ8 true 19 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_5bbb8 : bv 32 := 0x00013a03.
Lemma F_5bbb8 : fetch_word Asan.M.loaded_segments (0x5bc08 : word) = Some W_5bbb8.
Proof. vm_refl. Qed.
Lemma D_5bbb8 : decode_any W_5bbb8 = Some (Load SZ8 true 20 2 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5bbbc : bv 32 := 0x03010113.
Lemma F_5bbbc : fetch_word Asan.M.loaded_segments (0x5bc0c : word) = Some W_5bbbc.
Proof. vm_refl. Qed.
Lemma D_5bbbc : decode_any W_5bbbc = Some (OpImm ALU_ADD 2 2 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_5bbc0 : bv 32 := 0x00008067.
Lemma F_5bbc0 : fetch_word Asan.M.loaded_segments (0x5bc10 : word) = Some W_5bbc0.
Proof. vm_refl. Qed.
Lemma D_5bbc0 : decode_any W_5bbc0 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5bcb0 : bv 32 := 0x00050493.
Lemma F_5bcb0 : fetch_word Asan.M.loaded_segments (0x5bd00 : word) = Some W_5bcb0.
Proof. vm_refl. Qed.
Lemma D_5bcb0 : decode_any W_5bcb0 = Some (OpImm ALU_ADD 9 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5bcb4 : bv 32 := 0x00058913.
Lemma F_5bcb4 : fetch_word Asan.M.loaded_segments (0x5bd04 : word) = Some W_5bcb4.
Proof. vm_refl. Qed.
Lemma D_5bcb4 : decode_any W_5bcb4 = Some (OpImm ALU_ADD 18 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5bcb8 : bv 32 := 0x00040593.
Lemma F_5bcb8 : fetch_word Asan.M.loaded_segments (0x5bd08 : word) = Some W_5bcb8.
Proof. vm_refl. Qed.
Lemma D_5bcb8 : decode_any W_5bcb8 = Some (OpImm ALU_ADD 11 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5bcbc : bv 32 := 0x00060993.
Lemma F_5bcbc : fetch_word Asan.M.loaded_segments (0x5bd0c : word) = Some W_5bcbc.
Proof. vm_refl. Qed.
Lemma D_5bcbc : decode_any W_5bcbc = Some (OpImm ALU_ADD 19 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5bcc0 : bv 32 := 0x00090613.
Lemma F_5bcc0 : fetch_word Asan.M.loaded_segments (0x5bd10 : word) = Some W_5bcc0.
Proof. vm_refl. Qed.
Lemma D_5bcc0 : decode_any W_5bcc0 = Some (OpImm ALU_ADD 12 18 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5bcc4 : bv 32 := 0x00068a13.
Lemma F_5bcc4 : fetch_word Asan.M.loaded_segments (0x5bd14 : word) = Some W_5bcc4.
Proof. vm_refl. Qed.
Lemma D_5bcc4 : decode_any W_5bcc4 = Some (OpImm ALU_ADD 20 13 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5bcc8 : bv 32 := 0x00098693.
Lemma F_5bcc8 : fetch_word Asan.M.loaded_segments (0x5bd18 : word) = Some W_5bcc8.
Proof. vm_refl. Qed.
Lemma D_5bcc8 : decode_any W_5bcc8 = Some (OpImm ALU_ADD 13 19 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5bccc : bv 32 := 0x1e8000ef.
Lemma F_5bccc : fetch_word Asan.M.loaded_segments (0x5bd1c : word) = Some W_5bccc.
Proof. vm_refl. Qed.
Lemma D_5bccc : decode_any W_5bccc = Some (Jal 1 488, 4%Z).
Proof. vm_refl. Qed.

Definition W_5bcd0 : bv 32 := 0x00090593.
Lemma F_5bcd0 : fetch_word Asan.M.loaded_segments (0x5bd20 : word) = Some W_5bcd0.
Proof. vm_refl. Qed.
Lemma D_5bcd0 : decode_any W_5bcd0 = Some (OpImm ALU_ADD 11 18 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5bcd4 : bv 32 := 0x000a0693.
Lemma F_5bcd4 : fetch_word Asan.M.loaded_segments (0x5bd24 : word) = Some W_5bcd4.
Proof. vm_refl. Qed.
Lemma D_5bcd4 : decode_any W_5bcd4 = Some (OpImm ALU_ADD 13 20 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5bcd8 : bv 32 := 0x00048513.
Lemma F_5bcd8 : fetch_word Asan.M.loaded_segments (0x5bd28 : word) = Some W_5bcd8.
Proof. vm_refl. Qed.
Lemma D_5bcd8 : decode_any W_5bcd8 = Some (OpImm ALU_ADD 10 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5bcdc : bv 32 := 0x00098613.
Lemma F_5bcdc : fetch_word Asan.M.loaded_segments (0x5bd2c : word) = Some W_5bcdc.
Proof. vm_refl. Qed.
Lemma D_5bcdc : decode_any W_5bcdc = Some (OpImm ALU_ADD 12 19 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5bce0 : bv 32 := 0x00042703.
Lemma F_5bce0 : fetch_word Asan.M.loaded_segments (0x5bd30 : word) = Some W_5bce0.
Proof. vm_refl. Qed.
Lemma D_5bce0 : decode_any W_5bce0 = Some (Load SZ4 true 14 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5bce4 : bv 32 := 0xe81ff06f.
Lemma F_5bce4 : fetch_word Asan.M.loaded_segments (0x5bd34 : word) = Some W_5bce4.
Proof. vm_refl. Qed.
Lemma D_5bce4 : decode_any W_5bce4 = Some (Jal 0 2096768, 4%Z).
Proof. vm_refl. Qed.

Definition W_5bce8 : bv 32 := 0xfe010113.
Lemma F_5bce8 : fetch_word Asan.M.loaded_segments (0x5bd38 : word) = Some W_5bce8.
Proof. vm_refl. Qed.
Lemma D_5bce8 : decode_any W_5bce8 = Some (OpImm ALU_ADD 2 2 4064, 4%Z).
Proof. vm_refl. Qed.

Definition W_5bcec : bv 32 := 0x00113c23.
Lemma F_5bcec : fetch_word Asan.M.loaded_segments (0x5bd3c : word) = Some W_5bcec.
Proof. vm_refl. Qed.
Lemma D_5bcec : decode_any W_5bcec = Some (Store SZ8 2 1 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_5bcf0 : bv 32 := 0x00813823.
Lemma F_5bcf0 : fetch_word Asan.M.loaded_segments (0x5bd40 : word) = Some W_5bcf0.
Proof. vm_refl. Qed.
Lemma D_5bcf0 : decode_any W_5bcf0 = Some (Store SZ8 2 8 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_5bcf4 : bv 32 := 0x00913423.
Lemma F_5bcf4 : fetch_word Asan.M.loaded_segments (0x5bd44 : word) = Some W_5bcf4.
Proof. vm_refl. Qed.
Lemma D_5bcf4 : decode_any W_5bcf4 = Some (Store SZ8 2 9 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_5bcf8 : bv 32 := 0x01213023.
Lemma F_5bcf8 : fetch_word Asan.M.loaded_segments (0x5bd48 : word) = Some W_5bcf8.
Proof. vm_refl. Qed.
Lemma D_5bcf8 : decode_any W_5bcf8 = Some (Store SZ8 2 18 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5bcfc : bv 32 := 0x00053703.
Lemma F_5bcfc : fetch_word Asan.M.loaded_segments (0x5bd4c : word) = Some W_5bcfc.
Proof. vm_refl. Qed.
Lemma D_5bcfc : decode_any W_5bcfc = Some (Load SZ8 true 14 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5bd00 : bv 32 := 0xfff70693.
Lemma F_5bd00 : fetch_word Asan.M.loaded_segments (0x5bd50 : word) = Some W_5bd00.
Proof. vm_refl. Qed.
Lemma D_5bd00 : decode_any W_5bd00 = Some (OpImm ALU_ADD 13 14 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_5bd04 : bv 32 := 0x00c6f6b3.
Lemma F_5bd04 : fetch_word Asan.M.loaded_segments (0x5bd54 : word) = Some W_5bd04.
Proof. vm_refl. Qed.
Lemma D_5bd04 : decode_any W_5bd04 = Some (Op ALU_AND 13 13 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_5bd08 : bv 32 := 0x12069263.
Lemma F_5bd08 : fetch_word Asan.M.loaded_segments (0x5bd58 : word) = Some W_5bd08.
Proof. vm_refl. Qed.
Lemma D_5bd08 : decode_any W_5bd08 = Some (Branch BC_NE 13 0 292, 4%Z).
Proof. vm_refl. Qed.

Definition W_5bd0c : bv 32 := 0x26850693.
Lemma F_5bd0c : fetch_word Asan.M.loaded_segments (0x5bd5c : word) = Some W_5bd0c.
Proof. vm_refl. Qed.
Lemma D_5bd0c : decode_any W_5bd0c = Some (OpImm ALU_ADD 13 10 616, 4%Z).
Proof. vm_refl. Qed.

Definition W_5bd10 : bv 32 := 0x0ff00793.
Lemma F_5bd10 : fetch_word Asan.M.loaded_segments (0x5bd60 : word) = Some W_5bd10.
Proof. vm_refl. Qed.
Lemma D_5bd10 : decode_any W_5bd10 = Some (OpImm ALU_ADD 15 0 255, 4%Z).
Proof. vm_refl. Qed.

Definition W_5bd14 : bv 32 := 0xffc6f813.
Lemma F_5bd14 : fetch_word Asan.M.loaded_segments (0x5bd64 : word) = Some W_5bd14.
Proof. vm_refl. Qed.
Lemma D_5bd14 : decode_any W_5bd14 = Some (OpImm ALU_AND 16 13 4092, 4%Z).
Proof. vm_refl. Qed.

Definition W_5bd18 : bv 32 := 0x00100893.
Lemma F_5bd18 : fetch_word Asan.M.loaded_segments (0x5bd68 : word) = Some W_5bd18.
Proof. vm_refl. Qed.
Lemma D_5bd18 : decode_any W_5bd18 = Some (OpImm ALU_ADD 17 0 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_5bd1c : bv 32 := 0x140822af.
Lemma F_5bd1c : fetch_word Asan.M.loaded_segments (0x5bd6c : word) = Some W_5bd1c.
Proof. vm_refl. Qed.
Lemma D_5bd1c : decode_any W_5bd1c = Some (Lr AW true false 5 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_5bd20 : bv 32 := 0x00088313.
Lemma F_5bd20 : fetch_word Asan.M.loaded_segments (0x5bd70 : word) = Some W_5bd20.
Proof. vm_refl. Qed.
Lemma D_5bd20 : decode_any W_5bd20 = Some (OpImm ALU_ADD 6 17 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5bd24 : bv 32 := 0x0062c333.
Lemma F_5bd24 : fetch_word Asan.M.loaded_segments (0x5bd74 : word) = Some W_5bd24.
Proof. vm_refl. Qed.
Lemma D_5bd24 : decode_any W_5bd24 = Some (Op ALU_XOR 6 5 6, 4%Z).
Proof. vm_refl. Qed.

Definition W_5bd28 : bv 32 := 0x00f37333.
Lemma F_5bd28 : fetch_word Asan.M.loaded_segments (0x5bd78 : word) = Some W_5bd28.
Proof. vm_refl. Qed.
Lemma D_5bd28 : decode_any W_5bd28 = Some (Op ALU_AND 6 6 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_5bd2c : bv 32 := 0x0062c333.
Lemma F_5bd2c : fetch_word Asan.M.loaded_segments (0x5bd7c : word) = Some W_5bd2c.
Proof. vm_refl. Qed.
Lemma D_5bd2c : decode_any W_5bd2c = Some (Op ALU_XOR 6 5 6, 4%Z).
Proof. vm_refl. Qed.

Definition W_5bd30 : bv 32 := 0x1868232f.
Lemma F_5bd30 : fetch_word Asan.M.loaded_segments (0x5bd80 : word) = Some W_5bd30.
Proof. vm_refl. Qed.
Lemma D_5bd30 : decode_any W_5bd30 = Some (Sc AW false false 6 16 6, 4%Z).
Proof. vm_refl. Qed.

Definition W_5bd34 : bv 32 := 0xfe0314e3.
Lemma F_5bd34 : fetch_word Asan.M.loaded_segments (0x5bd84 : word) = Some W_5bd34.
Proof. vm_refl. Qed.
Lemma D_5bd34 : decode_any W_5bd34 = Some (Branch BC_NE 6 0 8168, 4%Z).
Proof. vm_refl. Qed.

Definition W_5bd38 : bv 32 := 0x0ff2f793.
Lemma F_5bd38 : fetch_word Asan.M.loaded_segments (0x5bd88 : word) = Some W_5bd38.
Proof. vm_refl. Qed.
Lemma D_5bd38 : decode_any W_5bd38 = Some (OpImm ALU_AND 15 5 255, 4%Z).
Proof. vm_refl. Qed.

Definition W_5bd3c : bv 32 := 0x40e60433.
Lemma F_5bd3c : fetch_word Asan.M.loaded_segments (0x5bd8c : word) = Some W_5bd3c.
Proof. vm_refl. Qed.
Lemma D_5bd3c : decode_any W_5bd3c = Some (Op ALU_SUB 8 12 14, 4%Z).
Proof. vm_refl. Qed.

Definition W_5bd40 : bv 32 := 0x10079663.
Lemma F_5bd40 : fetch_word Asan.M.loaded_segments (0x5bd90 : word) = Some W_5bd40.
Proof. vm_refl. Qed.
Lemma D_5bd40 : decode_any W_5bd40 = Some (Branch BC_NE 15 0 268, 4%Z).
Proof. vm_refl. Qed.

Definition W_5bd44 : bv 32 := 0x01843683.
Lemma F_5bd44 : fetch_word Asan.M.loaded_segments (0x5bd94 : word) = Some W_5bd44.
Proof. vm_refl. Qed.
Lemma D_5bd44 : decode_any W_5bd44 = Some (Load SZ8 true 13 8 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_5bd48 : bv 32 := 0x00853783.
Lemma F_5bd48 : fetch_word Asan.M.loaded_segments (0x5bd98 : word) = Some W_5bd48.
Proof. vm_refl. Qed.
Lemma D_5bd48 : decode_any W_5bd48 = Some (Load SZ8 true 15 10 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_5bd4c : bv 32 := 0x00369613.
Lemma F_5bd4c : fetch_word Asan.M.loaded_segments (0x5bd9c : word) = Some W_5bd4c.
Proof. vm_refl. Qed.
Lemma D_5bd4c : decode_any W_5bd4c = Some (ShiftImm ALU_SLL 12 13 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_5bd50 : bv 32 := 0x00c78633.
Lemma F_5bd50 : fetch_word Asan.M.loaded_segments (0x5bda0 : word) = Some W_5bd50.
Proof. vm_refl. Qed.
Lemma D_5bd50 : decode_any W_5bd50 = Some (Op ALU_ADD 12 15 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_5bd54 : bv 32 := 0x00063703.
Lemma F_5bd54 : fetch_word Asan.M.loaded_segments (0x5bda4 : word) = Some W_5bd54.
Proof. vm_refl. Qed.
Lemma D_5bd54 : decode_any W_5bd54 = Some (Load SZ8 true 14 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5bd58 : bv 32 := 0x12871263.
Lemma F_5bd58 : fetch_word Asan.M.loaded_segments (0x5bda8 : word) = Some W_5bd58.
Proof. vm_refl. Qed.
Lemma D_5bd58 : decode_any W_5bd58 = Some (Branch BC_NE 14 8 292, 4%Z).
Proof. vm_refl. Qed.

Definition W_5bd5c : bv 32 := 0x03853703.
Lemma F_5bd5c : fetch_word Asan.M.loaded_segments (0x5bdac : word) = Some W_5bd5c.
Proof. vm_refl. Qed.
Lemma D_5bd5c : decode_any W_5bd5c = Some (Load SZ8 true 14 10 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_5bd60 : bv 32 := 0x12e6fe63.
Lemma F_5bd60 : fetch_word Asan.M.loaded_segments (0x5bdb0 : word) = Some W_5bd60.
Proof. vm_refl. Qed.
Lemma D_5bd60 : decode_any W_5bd60 = Some (Branch BC_GEU 13 14 316, 4%Z).
Proof. vm_refl. Qed.

Definition W_5bd64 : bv 32 := 0x00371813.
Lemma F_5bd64 : fetch_word Asan.M.loaded_segments (0x5bdb4 : word) = Some W_5bd64.
Proof. vm_refl. Qed.
Lemma D_5bd64 : decode_any W_5bd64 = Some (ShiftImm ALU_SLL 16 14 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_5bd68 : bv 32 := 0x00843883.
Lemma F_5bd68 : fetch_word Asan.M.loaded_segments (0x5bdb8 : word) = Some W_5bd68.
Proof. vm_refl. Qed.
Lemma D_5bd68 : decode_any W_5bd68 = Some (Load SZ8 true 17 8 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_5bd6c : bv 32 := 0x00f807b3.
Lemma F_5bd6c : fetch_word Asan.M.loaded_segments (0x5bdbc : word) = Some W_5bd6c.
Proof. vm_refl. Qed.
Lemma D_5bd6c : decode_any W_5bd6c = Some (Op ALU_ADD 15 16 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_5bd70 : bv 32 := 0x05053803.
Lemma F_5bd70 : fetch_word Asan.M.loaded_segments (0x5bdc0 : word) = Some W_5bd70.
Proof. vm_refl. Qed.
Lemma D_5bd70 : decode_any W_5bd70 = Some (Load SZ8 true 16 10 80, 4%Z).
Proof. vm_refl. Qed.

Definition W_5bd74 : bv 32 := 0x05853283.
Lemma F_5bd74 : fetch_word Asan.M.loaded_segments (0x5bdc4 : word) = Some W_5bd74.
Proof. vm_refl. Qed.
Lemma D_5bd74 : decode_any W_5bd74 = Some (Load SZ8 true 5 10 88, 4%Z).
Proof. vm_refl. Qed.

Definition W_5bd78 : bv 32 := 0xfff70713.
Lemma F_5bd78 : fetch_word Asan.M.loaded_segments (0x5bdc8 : word) = Some W_5bd78.
Proof. vm_refl. Qed.
Lemma D_5bd78 : decode_any W_5bd78 = Some (OpImm ALU_ADD 14 14 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_5bd7c : bv 32 := 0xff87b783.
Lemma F_5bd7c : fetch_word Asan.M.loaded_segments (0x5bdcc : word) = Some W_5bd7c.
Proof. vm_refl. Qed.
Lemma D_5bd7c : decode_any W_5bd7c = Some (Load SZ8 true 15 15 4088, 4%Z).
Proof. vm_refl. Qed.

Definition W_5bd80 : bv 32 := 0x00180813.
Lemma F_5bd80 : fetch_word Asan.M.loaded_segments (0x5bdd0 : word) = Some W_5bd80.
Proof. vm_refl. Qed.
Lemma D_5bd80 : decode_any W_5bd80 = Some (OpImm ALU_ADD 16 16 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_5bd84 : bv 32 := 0x411282b3.
Lemma F_5bd84 : fetch_word Asan.M.loaded_segments (0x5bdd4 : word) = Some W_5bd84.
Proof. vm_refl. Qed.
Lemma D_5bd84 : decode_any W_5bd84 = Some (Op ALU_SUB 5 5 17, 4%Z).
Proof. vm_refl. Qed.

Definition W_5bd88 : bv 32 := 0x02e53c23.
Lemma F_5bd88 : fetch_word Asan.M.loaded_segments (0x5bdd8 : word) = Some W_5bd88.
Proof. vm_refl. Qed.
Lemma D_5bd88 : decode_any W_5bd88 = Some (Store SZ8 10 14 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_5bd8c : bv 32 := 0x04050023.
Lemma F_5bd8c : fetch_word Asan.M.loaded_segments (0x5bddc : word) = Some W_5bd8c.
Proof. vm_refl. Qed.
Lemma D_5bd8c : decode_any W_5bd8c = Some (Store SZ1 10 0 64, 4%Z).
Proof. vm_refl. Qed.

Definition W_5bd90 : bv 32 := 0x05053823.
Lemma F_5bd90 : fetch_word Asan.M.loaded_segments (0x5bde0 : word) = Some W_5bd90.
Proof. vm_refl. Qed.
Lemma D_5bd90 : decode_any W_5bd90 = Some (Store SZ8 10 16 80, 4%Z).
Proof. vm_refl. Qed.

Definition W_5bd94 : bv 32 := 0x04553c23.
Lemma F_5bd94 : fetch_word Asan.M.loaded_segments (0x5bde4 : word) = Some W_5bd94.
Proof. vm_refl. Qed.
Lemma D_5bd94 : decode_any W_5bd94 = Some (Store SZ8 10 5 88, 4%Z).
Proof. vm_refl. Qed.

Definition W_5bd98 : bv 32 := 0x01058713.
Lemma F_5bd98 : fetch_word Asan.M.loaded_segments (0x5bde8 : word) = Some W_5bd98.
Proof. vm_refl. Qed.
Lemma D_5bd98 : decode_any W_5bd98 = Some (OpImm ALU_ADD 14 11 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_5bd9c : bv 32 := 0x41100833.
Lemma F_5bd9c : fetch_word Asan.M.loaded_segments (0x5bdec : word) = Some W_5bd9c.
Proof. vm_refl. Qed.
Lemma D_5bd9c : decode_any W_5bd9c = Some (Op ALU_SUB 16 0 17, 4%Z).
Proof. vm_refl. Qed.

Definition W_5bda0 : bv 32 := 0x00f63023.
Lemma F_5bda0 : fetch_word Asan.M.loaded_segments (0x5bdf0 : word) = Some W_5bda0.
Proof. vm_refl. Qed.
Lemma D_5bda0 : decode_any W_5bda0 = Some (Store SZ8 12 15 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5bda4 : bv 32 := 0x00d7bc23.
Lemma F_5bda4 : fetch_word Asan.M.loaded_segments (0x5bdf4 : word) = Some W_5bda4.
Proof. vm_refl. Qed.
Lemma D_5bda4 : decode_any W_5bda4 = Some (Store SZ8 15 13 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_5bda8 : bv 32 := 0x0107302f.
Lemma F_5bda8 : fetch_word Asan.M.loaded_segments (0x5bdf8 : word) = Some W_5bda8.
Proof. vm_refl. Qed.
Lemma D_5bda8 : decode_any W_5bda8 = Some (Amo AMO_ADD AD false false 0 14 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_5bdac : bv 32 := 0x00843603.
Lemma F_5bdac : fetch_word Asan.M.loaded_segments (0x5bdfc : word) = Some W_5bdac.
Proof. vm_refl. Qed.
Lemma D_5bdac : decode_any W_5bdac = Some (Load SZ8 true 12 8 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_5bdb0 : bv 32 := 0x01858593.
Lemma F_5bdb0 : fetch_word Asan.M.loaded_segments (0x5be00 : word) = Some W_5bdb0.
Proof. vm_refl. Qed.
Lemma D_5bdb0 : decode_any W_5bdb0 = Some (OpImm ALU_ADD 11 11 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_5bdb4 : bv 32 := 0x40c00633.
Lemma F_5bdb4 : fetch_word Asan.M.loaded_segments (0x5be04 : word) = Some W_5bdb4.
Proof. vm_refl. Qed.
Lemma D_5bdb4 : decode_any W_5bdb4 = Some (Op ALU_SUB 12 0 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_5bdb8 : bv 32 := 0x00c5b02f.
Lemma F_5bdb8 : fetch_word Asan.M.loaded_segments (0x5be08 : word) = Some W_5bdb8.
Proof. vm_refl. Qed.
Lemma D_5bdb8 : decode_any W_5bdb8 = Some (Amo AMO_ADD AD false false 0 11 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_5bdbc : bv 32 := 0x0310000f.
Lemma F_5bdbc : fetch_word Asan.M.loaded_segments (0x5be0c : word) = Some W_5bdbc.
Proof. vm_refl. Qed.
Lemma D_5bdbc : decode_any W_5bdbc = Some (Fence 0 3 1 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5bdc0 : bv 32 := 0x26050423.
Lemma F_5bdc0 : fetch_word Asan.M.loaded_segments (0x5be10 : word) = Some W_5bdc0.
Proof. vm_refl. Qed.
Lemma D_5bdc0 : decode_any W_5bdc0 = Some (Store SZ1 10 0 616, 4%Z).
Proof. vm_refl. Qed.

Definition W_5bdc4 : bv 32 := 0x00043483.
Lemma F_5bdc4 : fetch_word Asan.M.loaded_segments (0x5be14 : word) = Some W_5bdc4.
Proof. vm_refl. Qed.
Lemma D_5bdc4 : decode_any W_5bdc4 = Some (Load SZ8 true 9 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5bdc8 : bv 32 := 0x00843903.
Lemma F_5bdc8 : fetch_word Asan.M.loaded_segments (0x5be18 : word) = Some W_5bdc8.
Proof. vm_refl. Qed.
Lemma D_5bdc8 : decode_any W_5bdc8 = Some (Load SZ8 true 18 8 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_5bdcc : bv 32 := 0x00048513.
Lemma F_5bdcc : fetch_word Asan.M.loaded_segments (0x5be1c : word) = Some W_5bdcc.
Proof. vm_refl. Qed.
Lemma D_5bdcc : decode_any W_5bdcc = Some (OpImm ALU_ADD 10 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5bdd0 : bv 32 := 0x00090593.
Lemma F_5bdd0 : fetch_word Asan.M.loaded_segments (0x5be20 : word) = Some W_5bdd0.
Proof. vm_refl. Qed.
Lemma D_5bdd0 : decode_any W_5bdd0 = Some (OpImm ALU_ADD 11 18 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5bdd4 : bv 32 := 0x00000613.
Lemma F_5bdd4 : fetch_word Asan.M.loaded_segments (0x5be24 : word) = Some W_5bdd4.
Proof. vm_refl. Qed.
Lemma D_5bdd4 : decode_any W_5bdd4 = Some (OpImm ALU_ADD 12 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5bdd8 : bv 32 := 0x6f1250ef.
Lemma F_5bdd8 : fetch_word Asan.M.loaded_segments (0x5be28 : word) = Some W_5bdd8.
Proof. vm_refl. Qed.
Lemma D_5bdd8 : decode_any W_5bdd8 = Some (Jal 1 155376, 4%Z).
Proof. vm_refl. Qed.

Definition W_5bddc : bv 32 := 0x00048513.
Lemma F_5bddc : fetch_word Asan.M.loaded_segments (0x5be2c : word) = Some W_5bddc.
Proof. vm_refl. Qed.
Lemma D_5bddc : decode_any W_5bddc = Some (OpImm ALU_ADD 10 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5bde0 : bv 32 := 0x00090593.
Lemma F_5bde0 : fetch_word Asan.M.loaded_segments (0x5be30 : word) = Some W_5bde0.
Proof. vm_refl. Qed.
Lemma D_5bde0 : decode_any W_5bde0 = Some (OpImm ALU_ADD 11 18 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5bde4 : bv 32 := 0x0cd240ef.
Lemma F_5bde4 : fetch_word Asan.M.loaded_segments (0x5be34 : word) = Some W_5bde4.
Proof. vm_refl. Qed.
Lemma D_5bde4 : decode_any W_5bde4 = Some (Jal 1 149708, 4%Z).
Proof. vm_refl. Qed.

Definition W_5bde8 : bv 32 := 0x6592d0ef.
Lemma F_5bde8 : fetch_word Asan.M.loaded_segments (0x5be38 : word) = Some W_5bde8.
Proof. vm_refl. Qed.
Lemma D_5bde8 : decode_any W_5bde8 = Some (Jal 1 187992, 4%Z).
Proof. vm_refl. Qed.

Definition W_5bdec : bv 32 := 0x06053683.
Lemma F_5bdec : fetch_word Asan.M.loaded_segments (0x5be3c : word) = Some W_5bdec.
Proof. vm_refl. Qed.
Lemma D_5bdec : decode_any W_5bdec = Some (Load SZ8 true 13 10 96, 4%Z).
Proof. vm_refl. Qed.

Definition W_5bdf0 : bv 32 := 0x05853703.
Lemma F_5bdf0 : fetch_word Asan.M.loaded_segments (0x5be40 : word) = Some W_5bdf0.
Proof. vm_refl. Qed.
Lemma D_5bdf0 : decode_any W_5bdf0 = Some (Load SZ8 true 14 10 88, 4%Z).
Proof. vm_refl. Qed.

Definition W_5bdf4 : bv 32 := 0x00043603.
Lemma F_5bdf4 : fetch_word Asan.M.loaded_segments (0x5be44 : word) = Some W_5bdf4.
Proof. vm_refl. Qed.
Lemma D_5bdf4 : decode_any W_5bdf4 = Some (Load SZ8 true 12 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5bdf8 : bv 32 := 0x00843583.
Lemma F_5bdf8 : fetch_word Asan.M.loaded_segments (0x5be48 : word) = Some W_5bdf8.
Proof. vm_refl. Qed.
Lemma D_5bdf8 : decode_any W_5bdf8 = Some (Load SZ8 true 11 8 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_5bdfc : bv 32 := 0x012686b3.
Lemma F_5bdfc : fetch_word Asan.M.loaded_segments (0x5be4c : word) = Some W_5bdfc.
Proof. vm_refl. Qed.
Lemma D_5bdfc : decode_any W_5bdfc = Some (Op ALU_ADD 13 13 18, 4%Z).
Proof. vm_refl. Qed.

Definition W_5be00 : bv 32 := 0x00170713.
Lemma F_5be00 : fetch_word Asan.M.loaded_segments (0x5be50 : word) = Some W_5be00.
Proof. vm_refl. Qed.
Lemma D_5be00 : decode_any W_5be00 = Some (OpImm ALU_ADD 14 14 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_5be04 : bv 32 := 0x04e53c23.
Lemma F_5be04 : fetch_word Asan.M.loaded_segments (0x5be54 : word) = Some W_5be04.
Proof. vm_refl. Qed.
Lemma D_5be04 : decode_any W_5be04 = Some (Store SZ8 10 14 88, 4%Z).
Proof. vm_refl. Qed.

Definition W_5be08 : bv 32 := 0x06d53023.
Lemma F_5be08 : fetch_word Asan.M.loaded_segments (0x5be58 : word) = Some W_5be08.
Proof. vm_refl. Qed.
Lemma D_5be08 : decode_any W_5be08 = Some (Store SZ8 10 13 96, 4%Z).
Proof. vm_refl. Qed.

Definition W_5be0c : bv 32 := 0x00060513.
Lemma F_5be0c : fetch_word Asan.M.loaded_segments (0x5be5c : word) = Some W_5be0c.
Proof. vm_refl. Qed.
Lemma D_5be0c : decode_any W_5be0c = Some (OpImm ALU_ADD 10 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5be10 : bv 32 := 0x00000613.
Lemma F_5be10 : fetch_word Asan.M.loaded_segments (0x5be60 : word) = Some W_5be10.
Proof. vm_refl. Qed.
Lemma D_5be10 : decode_any W_5be10 = Some (OpImm ALU_ADD 12 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5be14 : bv 32 := 0x01813083.
Lemma F_5be14 : fetch_word Asan.M.loaded_segments (0x5be64 : word) = Some W_5be14.
Proof. vm_refl. Qed.
Lemma D_5be14 : decode_any W_5be14 = Some (Load SZ8 true 1 2 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_5be18 : bv 32 := 0x01013403.
Lemma F_5be18 : fetch_word Asan.M.loaded_segments (0x5be68 : word) = Some W_5be18.
Proof. vm_refl. Qed.
Lemma D_5be18 : decode_any W_5be18 = Some (Load SZ8 true 8 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_5be1c : bv 32 := 0x00813483.
Lemma F_5be1c : fetch_word Asan.M.loaded_segments (0x5be6c : word) = Some W_5be1c.
Proof. vm_refl. Qed.
Lemma D_5be1c : decode_any W_5be1c = Some (Load SZ8 true 9 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_5be20 : bv 32 := 0x00013903.
Lemma F_5be20 : fetch_word Asan.M.loaded_segments (0x5be70 : word) = Some W_5be20.
Proof. vm_refl. Qed.
Lemma D_5be20 : decode_any W_5be20 = Some (Load SZ8 true 18 2 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5be24 : bv 32 := 0x02010113.
Lemma F_5be24 : fetch_word Asan.M.loaded_segments (0x5be74 : word) = Some W_5be24.
Proof. vm_refl. Qed.
Lemma D_5be24 : decode_any W_5be24 = Some (OpImm ALU_ADD 2 2 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_5be28 : bv 32 := 0x0353806f.
Lemma F_5be28 : fetch_word Asan.M.loaded_segments (0x5be78 : word) = Some W_5be28.
Proof. vm_refl. Qed.
Lemma D_5be28 : decode_any W_5be28 = Some (Jal 0 231476, 4%Z).
Proof. vm_refl. Qed.

Definition W_5beb4 : bv 32 := 0xfc010113.
Lemma F_5beb4 : fetch_word Asan.M.loaded_segments (0x5bf04 : word) = Some W_5beb4.
Proof. vm_refl. Qed.
Lemma D_5beb4 : decode_any W_5beb4 = Some (OpImm ALU_ADD 2 2 4032, 4%Z).
Proof. vm_refl. Qed.

Definition W_5beb8 : bv 32 := 0x02113c23.
Lemma F_5beb8 : fetch_word Asan.M.loaded_segments (0x5bf08 : word) = Some W_5beb8.
Proof. vm_refl. Qed.
Lemma D_5beb8 : decode_any W_5beb8 = Some (Store SZ8 2 1 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_5bebc : bv 32 := 0x02013423.
Lemma F_5bebc : fetch_word Asan.M.loaded_segments (0x5bf0c : word) = Some W_5bebc.
Proof. vm_refl. Qed.
Lemma D_5bebc : decode_any W_5bebc = Some (Store SZ8 2 0 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_5bec0 : bv 32 := 0x02013823.
Lemma F_5bec0 : fetch_word Asan.M.loaded_segments (0x5bf10 : word) = Some W_5bec0.
Proof. vm_refl. Qed.
Lemma D_5bec0 : decode_any W_5bec0 = Some (Store SZ8 2 0 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_5bec4 : bv 32 := 0x0005a803.
Lemma F_5bec4 : fetch_word Asan.M.loaded_segments (0x5bf14 : word) = Some W_5bec4.
Proof. vm_refl. Qed.
Lemma D_5bec4 : decode_any W_5bec4 = Some (Load SZ4 true 16 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5bec8 : bv 32 := 0x0045e783.
Lemma F_5bec8 : fetch_word Asan.M.loaded_segments (0x5bf18 : word) = Some W_5bec8.
Proof. vm_refl. Qed.
Lemma D_5bec8 : decode_any W_5bec8 = Some (Load SZ4 false 15 11 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_5becc : bv 32 := 0x00c13423.
Lemma F_5becc : fetch_word Asan.M.loaded_segments (0x5bf1c : word) = Some W_5becc.
Proof. vm_refl. Qed.
Lemma D_5becc : decode_any W_5becc = Some (Store SZ8 2 12 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_5bed0 : bv 32 := 0x00013823.
Lemma F_5bed0 : fetch_word Asan.M.loaded_segments (0x5bf20 : word) = Some W_5bed0.
Proof. vm_refl. Qed.
Lemma D_5bed0 : decode_any W_5bed0 = Some (Store SZ8 2 0 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_5bed4 : bv 32 := 0x00013c23.
Lemma F_5bed4 : fetch_word Asan.M.loaded_segments (0x5bf24 : word) = Some W_5bed4.
Proof. vm_refl. Qed.
Lemma D_5bed4 : decode_any W_5bed4 = Some (Store SZ8 2 0 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_5bed8 : bv 32 := 0x02013023.
Lemma F_5bed8 : fetch_word Asan.M.loaded_segments (0x5bf28 : word) = Some W_5bed8.
Proof. vm_refl. Qed.
Lemma D_5bed8 : decode_any W_5bed8 = Some (Store SZ8 2 0 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_5bedc : bv 32 := 0x0017d793.
Lemma F_5bedc : fetch_word Asan.M.loaded_segments (0x5bf2c : word) = Some W_5bedc.
Proof. vm_refl. Qed.
Lemma D_5bedc : decode_any W_5bedc = Some (ShiftImm ALU_SRL 15 15 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_5bee0 : bv 32 := 0x02081713.
Lemma F_5bee0 : fetch_word Asan.M.loaded_segments (0x5bf30 : word) = Some W_5bee0.
Proof. vm_refl. Qed.
Lemma D_5bee0 : decode_any W_5bee0 = Some (ShiftImm ALU_SLL 14 16 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_5bee4 : bv 32 := 0x02075713.
Lemma F_5bee4 : fetch_word Asan.M.loaded_segments (0x5bf34 : word) = Some W_5bee4.
Proof. vm_refl. Qed.
Lemma D_5bee4 : decode_any W_5bee4 = Some (ShiftImm ALU_SRL 14 14 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_5bee8 : bv 32 := 0x04f86663.
Lemma F_5bee8 : fetch_word Asan.M.loaded_segments (0x5bf38 : word) = Some W_5bee8.
Proof. vm_refl. Qed.
Lemma D_5bee8 : decode_any W_5bee8 = Some (Branch BC_LTU 16 15 76, 4%Z).
Proof. vm_refl. Qed.

Definition W_5beec : bv 32 := 0x40f70733.
Lemma F_5beec : fetch_word Asan.M.loaded_segments (0x5bf3c : word) = Some W_5beec.
Proof. vm_refl. Qed.
Lemma D_5beec : decode_any W_5beec = Some (Op ALU_SUB 14 14 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_5bef0 : bv 32 := 0x7ff50513.
Lemma F_5bef0 : fetch_word Asan.M.loaded_segments (0x5bf40 : word) = Some W_5bef0.
Proof. vm_refl. Qed.
Lemma D_5bef0 : decode_any W_5bef0 = Some (OpImm ALU_ADD 10 10 2047, 4%Z).
Proof. vm_refl. Qed.

Definition W_5bef4 : bv 32 := 0x00e5a023.
Lemma F_5bef4 : fetch_word Asan.M.loaded_segments (0x5bf44 : word) = Some W_5bef4.
Proof. vm_refl. Qed.
Lemma D_5bef4 : decode_any W_5bef4 = Some (Store SZ4 11 14 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5bef8 : bv 32 := 0x20150813.
Lemma F_5bef8 : fetch_word Asan.M.loaded_segments (0x5bf48 : word) = Some W_5bef8.
Proof. vm_refl. Qed.
Lemma D_5bef8 : decode_any W_5bef8 = Some (OpImm ALU_ADD 16 10 513, 4%Z).
Proof. vm_refl. Qed.

Definition W_5befc : bv 32 := 0x00271713.
Lemma F_5befc : fetch_word Asan.M.loaded_segments (0x5bf4c : word) = Some W_5befc.
Proof. vm_refl. Qed.
Lemma D_5befc : decode_any W_5befc = Some (ShiftImm ALU_SLL 14 14 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_5bf00 : bv 32 := 0x00e585b3.
Lemma F_5bf00 : fetch_word Asan.M.loaded_segments (0x5bf50 : word) = Some W_5bf00.
Proof. vm_refl. Qed.
Lemma D_5bf00 : decode_any W_5bf00 = Some (Op ALU_ADD 11 11 14, 4%Z).
Proof. vm_refl. Qed.

Definition W_5bf04 : bv 32 := 0x01058713.
Lemma F_5bf04 : fetch_word Asan.M.loaded_segments (0x5bf54 : word) = Some W_5bf04.
Proof. vm_refl. Qed.
Lemma D_5bf04 : decode_any W_5bf04 = Some (OpImm ALU_ADD 14 11 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_5bf08 : bv 32 := 0x00810593.
Lemma F_5bf08 : fetch_word Asan.M.loaded_segments (0x5bf58 : word) = Some W_5bf08.
Proof. vm_refl. Qed.
Lemma D_5bf08 : decode_any W_5bf08 = Some (OpImm ALU_ADD 11 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_5bf0c : bv 32 := 0x00060513.
Lemma F_5bf0c : fetch_word Asan.M.loaded_segments (0x5bf5c : word) = Some W_5bf0c.
Proof. vm_refl. Qed.
Lemma D_5bf0c : decode_any W_5bf0c = Some (OpImm ALU_ADD 10 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5bf10 : bv 32 := 0x00080613.
Lemma F_5bf10 : fetch_word Asan.M.loaded_segments (0x5bf60 : word) = Some W_5bf10.
Proof. vm_refl. Qed.
Lemma D_5bf10 : decode_any W_5bf10 = Some (OpImm ALU_ADD 12 16 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5bf14 : bv 32 := 0x144000ef.
Lemma F_5bf14 : fetch_word Asan.M.loaded_segments (0x5bf64 : word) = Some W_5bf14.
Proof. vm_refl. Qed.
Lemma D_5bf14 : decode_any W_5bf14 = Some (Jal 1 324, 4%Z).
Proof. vm_refl. Qed.

Definition W_5bf18 : bv 32 := 0x02013503.
Lemma F_5bf18 : fetch_word Asan.M.loaded_segments (0x5bf68 : word) = Some W_5bf18.
Proof. vm_refl. Qed.
Lemma D_5bf18 : decode_any W_5bf18 = Some (Load SZ8 true 10 2 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_5bf1c : bv 32 := 0x02813583.
Lemma F_5bf1c : fetch_word Asan.M.loaded_segments (0x5bf6c : word) = Some W_5bf1c.
Proof. vm_refl. Qed.
Lemma D_5bf1c : decode_any W_5bf1c = Some (Load SZ8 true 11 2 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_5bf20 : bv 32 := 0x00000613.
Lemma F_5bf20 : fetch_word Asan.M.loaded_segments (0x5bf70 : word) = Some W_5bf20.
Proof. vm_refl. Qed.
Lemma D_5bf20 : decode_any W_5bf20 = Some (OpImm ALU_ADD 12 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5bf24 : bv 32 := 0x738380ef.
Lemma F_5bf24 : fetch_word Asan.M.loaded_segments (0x5bf74 : word) = Some W_5bf24.
Proof. vm_refl. Qed.
Lemma D_5bf24 : decode_any W_5bf24 = Some (Jal 1 231224, 4%Z).
Proof. vm_refl. Qed.

Definition W_5bf28 : bv 32 := 0x03813083.
Lemma F_5bf28 : fetch_word Asan.M.loaded_segments (0x5bf78 : word) = Some W_5bf28.
Proof. vm_refl. Qed.
Lemma D_5bf28 : decode_any W_5bf28 = Some (Load SZ8 true 1 2 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_5bf2c : bv 32 := 0x04010113.
Lemma F_5bf2c : fetch_word Asan.M.loaded_segments (0x5bf7c : word) = Some W_5bf2c.
Proof. vm_refl. Qed.
Lemma D_5bf2c : decode_any W_5bf2c = Some (OpImm ALU_ADD 2 2 64, 4%Z).
Proof. vm_refl. Qed.

Definition W_5bf30 : bv 32 := 0x00008067.
Lemma F_5bf30 : fetch_word Asan.M.loaded_segments (0x5bf80 : word) = Some W_5bf30.
Proof. vm_refl. Qed.
Lemma D_5bf30 : decode_any W_5bf30 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

