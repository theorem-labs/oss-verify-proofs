(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.jsoncons.fuzz_json_encoder.images Require Import Asan.
Open Scope bv_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Hint Extern 0 (BvWf _ _) =>
  (lazymatch goal with |- BvWf ?n ?v => is_closed_term n; is_closed_term v end; exact I) : typeclass_instances.
Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

(* [comment removed for export] *)
Definition W_5d07c : bv 32 := 0x00050493.
Lemma F_5d07c : fetch_word Asan.M.loaded_segments (0x5d0cc : word) = Some W_5d07c.
Proof. vm_refl. Qed.
Lemma D_5d07c : decode_any W_5d07c = Some (OpImm ALU_ADD 9 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d080 : bv 32 := 0x00058913.
Lemma F_5d080 : fetch_word Asan.M.loaded_segments (0x5d0d0 : word) = Some W_5d080.
Proof. vm_refl. Qed.
Lemma D_5d080 : decode_any W_5d080 = Some (OpImm ALU_ADD 18 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d084 : bv 32 := 0x00040593.
Lemma F_5d084 : fetch_word Asan.M.loaded_segments (0x5d0d4 : word) = Some W_5d084.
Proof. vm_refl. Qed.
Lemma D_5d084 : decode_any W_5d084 = Some (OpImm ALU_ADD 11 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d088 : bv 32 := 0x00060993.
Lemma F_5d088 : fetch_word Asan.M.loaded_segments (0x5d0d8 : word) = Some W_5d088.
Proof. vm_refl. Qed.
Lemma D_5d088 : decode_any W_5d088 = Some (OpImm ALU_ADD 19 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d08c : bv 32 := 0x00090613.
Lemma F_5d08c : fetch_word Asan.M.loaded_segments (0x5d0dc : word) = Some W_5d08c.
Proof. vm_refl. Qed.
Lemma D_5d08c : decode_any W_5d08c = Some (OpImm ALU_ADD 12 18 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d090 : bv 32 := 0x00068a13.
Lemma F_5d090 : fetch_word Asan.M.loaded_segments (0x5d0e0 : word) = Some W_5d090.
Proof. vm_refl. Qed.
Lemma D_5d090 : decode_any W_5d090 = Some (OpImm ALU_ADD 20 13 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d094 : bv 32 := 0x00098693.
Lemma F_5d094 : fetch_word Asan.M.loaded_segments (0x5d0e4 : word) = Some W_5d094.
Proof. vm_refl. Qed.
Lemma D_5d094 : decode_any W_5d094 = Some (OpImm ALU_ADD 13 19 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d098 : bv 32 := 0x1e8000ef.
Lemma F_5d098 : fetch_word Asan.M.loaded_segments (0x5d0e8 : word) = Some W_5d098.
Proof. vm_refl. Qed.
Lemma D_5d098 : decode_any W_5d098 = Some (Jal 1 488, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d09c : bv 32 := 0x00090593.
Lemma F_5d09c : fetch_word Asan.M.loaded_segments (0x5d0ec : word) = Some W_5d09c.
Proof. vm_refl. Qed.
Lemma D_5d09c : decode_any W_5d09c = Some (OpImm ALU_ADD 11 18 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d0a0 : bv 32 := 0x000a0693.
Lemma F_5d0a0 : fetch_word Asan.M.loaded_segments (0x5d0f0 : word) = Some W_5d0a0.
Proof. vm_refl. Qed.
Lemma D_5d0a0 : decode_any W_5d0a0 = Some (OpImm ALU_ADD 13 20 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d0a4 : bv 32 := 0x00048513.
Lemma F_5d0a4 : fetch_word Asan.M.loaded_segments (0x5d0f4 : word) = Some W_5d0a4.
Proof. vm_refl. Qed.
Lemma D_5d0a4 : decode_any W_5d0a4 = Some (OpImm ALU_ADD 10 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d0a8 : bv 32 := 0x00098613.
Lemma F_5d0a8 : fetch_word Asan.M.loaded_segments (0x5d0f8 : word) = Some W_5d0a8.
Proof. vm_refl. Qed.
Lemma D_5d0a8 : decode_any W_5d0a8 = Some (OpImm ALU_ADD 12 19 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d0ac : bv 32 := 0x00042703.
Lemma F_5d0ac : fetch_word Asan.M.loaded_segments (0x5d0fc : word) = Some W_5d0ac.
Proof. vm_refl. Qed.
Lemma D_5d0ac : decode_any W_5d0ac = Some (Load SZ4 true 14 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d0b0 : bv 32 := 0xe81ff06f.
Lemma F_5d0b0 : fetch_word Asan.M.loaded_segments (0x5d100 : word) = Some W_5d0b0.
Proof. vm_refl. Qed.
Lemma D_5d0b0 : decode_any W_5d0b0 = Some (Jal 0 2096768, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d0b4 : bv 32 := 0xfe010113.
Lemma F_5d0b4 : fetch_word Asan.M.loaded_segments (0x5d104 : word) = Some W_5d0b4.
Proof. vm_refl. Qed.
Lemma D_5d0b4 : decode_any W_5d0b4 = Some (OpImm ALU_ADD 2 2 4064, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d0b8 : bv 32 := 0x00113c23.
Lemma F_5d0b8 : fetch_word Asan.M.loaded_segments (0x5d108 : word) = Some W_5d0b8.
Proof. vm_refl. Qed.
Lemma D_5d0b8 : decode_any W_5d0b8 = Some (Store SZ8 2 1 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d0bc : bv 32 := 0x00813823.
Lemma F_5d0bc : fetch_word Asan.M.loaded_segments (0x5d10c : word) = Some W_5d0bc.
Proof. vm_refl. Qed.
Lemma D_5d0bc : decode_any W_5d0bc = Some (Store SZ8 2 8 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d0c0 : bv 32 := 0x00913423.
Lemma F_5d0c0 : fetch_word Asan.M.loaded_segments (0x5d110 : word) = Some W_5d0c0.
Proof. vm_refl. Qed.
Lemma D_5d0c0 : decode_any W_5d0c0 = Some (Store SZ8 2 9 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d0c4 : bv 32 := 0x01213023.
Lemma F_5d0c4 : fetch_word Asan.M.loaded_segments (0x5d114 : word) = Some W_5d0c4.
Proof. vm_refl. Qed.
Lemma D_5d0c4 : decode_any W_5d0c4 = Some (Store SZ8 2 18 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d0c8 : bv 32 := 0x00053703.
Lemma F_5d0c8 : fetch_word Asan.M.loaded_segments (0x5d118 : word) = Some W_5d0c8.
Proof. vm_refl. Qed.
Lemma D_5d0c8 : decode_any W_5d0c8 = Some (Load SZ8 true 14 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d0cc : bv 32 := 0xfff70693.
Lemma F_5d0cc : fetch_word Asan.M.loaded_segments (0x5d11c : word) = Some W_5d0cc.
Proof. vm_refl. Qed.
Lemma D_5d0cc : decode_any W_5d0cc = Some (OpImm ALU_ADD 13 14 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d0d0 : bv 32 := 0x00c6f6b3.
Lemma F_5d0d0 : fetch_word Asan.M.loaded_segments (0x5d120 : word) = Some W_5d0d0.
Proof. vm_refl. Qed.
Lemma D_5d0d0 : decode_any W_5d0d0 = Some (Op ALU_AND 13 13 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d0d4 : bv 32 := 0x12069263.
Lemma F_5d0d4 : fetch_word Asan.M.loaded_segments (0x5d124 : word) = Some W_5d0d4.
Proof. vm_refl. Qed.
Lemma D_5d0d4 : decode_any W_5d0d4 = Some (Branch BC_NE 13 0 292, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d0d8 : bv 32 := 0x26850693.
Lemma F_5d0d8 : fetch_word Asan.M.loaded_segments (0x5d128 : word) = Some W_5d0d8.
Proof. vm_refl. Qed.
Lemma D_5d0d8 : decode_any W_5d0d8 = Some (OpImm ALU_ADD 13 10 616, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d0dc : bv 32 := 0x0ff00793.
Lemma F_5d0dc : fetch_word Asan.M.loaded_segments (0x5d12c : word) = Some W_5d0dc.
Proof. vm_refl. Qed.
Lemma D_5d0dc : decode_any W_5d0dc = Some (OpImm ALU_ADD 15 0 255, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d0e0 : bv 32 := 0xffc6f813.
Lemma F_5d0e0 : fetch_word Asan.M.loaded_segments (0x5d130 : word) = Some W_5d0e0.
Proof. vm_refl. Qed.
Lemma D_5d0e0 : decode_any W_5d0e0 = Some (OpImm ALU_AND 16 13 4092, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d0e4 : bv 32 := 0x00100893.
Lemma F_5d0e4 : fetch_word Asan.M.loaded_segments (0x5d134 : word) = Some W_5d0e4.
Proof. vm_refl. Qed.
Lemma D_5d0e4 : decode_any W_5d0e4 = Some (OpImm ALU_ADD 17 0 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d0e8 : bv 32 := 0x140822af.
Lemma F_5d0e8 : fetch_word Asan.M.loaded_segments (0x5d138 : word) = Some W_5d0e8.
Proof. vm_refl. Qed.
Lemma D_5d0e8 : decode_any W_5d0e8 = Some (Lr AW true false 5 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d0ec : bv 32 := 0x00088313.
Lemma F_5d0ec : fetch_word Asan.M.loaded_segments (0x5d13c : word) = Some W_5d0ec.
Proof. vm_refl. Qed.
Lemma D_5d0ec : decode_any W_5d0ec = Some (OpImm ALU_ADD 6 17 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d0f0 : bv 32 := 0x0062c333.
Lemma F_5d0f0 : fetch_word Asan.M.loaded_segments (0x5d140 : word) = Some W_5d0f0.
Proof. vm_refl. Qed.
Lemma D_5d0f0 : decode_any W_5d0f0 = Some (Op ALU_XOR 6 5 6, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d0f4 : bv 32 := 0x00f37333.
Lemma F_5d0f4 : fetch_word Asan.M.loaded_segments (0x5d144 : word) = Some W_5d0f4.
Proof. vm_refl. Qed.
Lemma D_5d0f4 : decode_any W_5d0f4 = Some (Op ALU_AND 6 6 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d0f8 : bv 32 := 0x0062c333.
Lemma F_5d0f8 : fetch_word Asan.M.loaded_segments (0x5d148 : word) = Some W_5d0f8.
Proof. vm_refl. Qed.
Lemma D_5d0f8 : decode_any W_5d0f8 = Some (Op ALU_XOR 6 5 6, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d0fc : bv 32 := 0x1868232f.
Lemma F_5d0fc : fetch_word Asan.M.loaded_segments (0x5d14c : word) = Some W_5d0fc.
Proof. vm_refl. Qed.
Lemma D_5d0fc : decode_any W_5d0fc = Some (Sc AW false false 6 16 6, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d100 : bv 32 := 0xfe0314e3.
Lemma F_5d100 : fetch_word Asan.M.loaded_segments (0x5d150 : word) = Some W_5d100.
Proof. vm_refl. Qed.
Lemma D_5d100 : decode_any W_5d100 = Some (Branch BC_NE 6 0 8168, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d104 : bv 32 := 0x0ff2f793.
Lemma F_5d104 : fetch_word Asan.M.loaded_segments (0x5d154 : word) = Some W_5d104.
Proof. vm_refl. Qed.
Lemma D_5d104 : decode_any W_5d104 = Some (OpImm ALU_AND 15 5 255, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d108 : bv 32 := 0x40e60433.
Lemma F_5d108 : fetch_word Asan.M.loaded_segments (0x5d158 : word) = Some W_5d108.
Proof. vm_refl. Qed.
Lemma D_5d108 : decode_any W_5d108 = Some (Op ALU_SUB 8 12 14, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d10c : bv 32 := 0x10079663.
Lemma F_5d10c : fetch_word Asan.M.loaded_segments (0x5d15c : word) = Some W_5d10c.
Proof. vm_refl. Qed.
Lemma D_5d10c : decode_any W_5d10c = Some (Branch BC_NE 15 0 268, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d110 : bv 32 := 0x01843683.
Lemma F_5d110 : fetch_word Asan.M.loaded_segments (0x5d160 : word) = Some W_5d110.
Proof. vm_refl. Qed.
Lemma D_5d110 : decode_any W_5d110 = Some (Load SZ8 true 13 8 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d114 : bv 32 := 0x00853783.
Lemma F_5d114 : fetch_word Asan.M.loaded_segments (0x5d164 : word) = Some W_5d114.
Proof. vm_refl. Qed.
Lemma D_5d114 : decode_any W_5d114 = Some (Load SZ8 true 15 10 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d118 : bv 32 := 0x00369613.
Lemma F_5d118 : fetch_word Asan.M.loaded_segments (0x5d168 : word) = Some W_5d118.
Proof. vm_refl. Qed.
Lemma D_5d118 : decode_any W_5d118 = Some (ShiftImm ALU_SLL 12 13 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d11c : bv 32 := 0x00c78633.
Lemma F_5d11c : fetch_word Asan.M.loaded_segments (0x5d16c : word) = Some W_5d11c.
Proof. vm_refl. Qed.
Lemma D_5d11c : decode_any W_5d11c = Some (Op ALU_ADD 12 15 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d120 : bv 32 := 0x00063703.
Lemma F_5d120 : fetch_word Asan.M.loaded_segments (0x5d170 : word) = Some W_5d120.
Proof. vm_refl. Qed.
Lemma D_5d120 : decode_any W_5d120 = Some (Load SZ8 true 14 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d124 : bv 32 := 0x12871263.
Lemma F_5d124 : fetch_word Asan.M.loaded_segments (0x5d174 : word) = Some W_5d124.
Proof. vm_refl. Qed.
Lemma D_5d124 : decode_any W_5d124 = Some (Branch BC_NE 14 8 292, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d128 : bv 32 := 0x03853703.
Lemma F_5d128 : fetch_word Asan.M.loaded_segments (0x5d178 : word) = Some W_5d128.
Proof. vm_refl. Qed.
Lemma D_5d128 : decode_any W_5d128 = Some (Load SZ8 true 14 10 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d12c : bv 32 := 0x12e6fe63.
Lemma F_5d12c : fetch_word Asan.M.loaded_segments (0x5d17c : word) = Some W_5d12c.
Proof. vm_refl. Qed.
Lemma D_5d12c : decode_any W_5d12c = Some (Branch BC_GEU 13 14 316, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d130 : bv 32 := 0x00371813.
Lemma F_5d130 : fetch_word Asan.M.loaded_segments (0x5d180 : word) = Some W_5d130.
Proof. vm_refl. Qed.
Lemma D_5d130 : decode_any W_5d130 = Some (ShiftImm ALU_SLL 16 14 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d134 : bv 32 := 0x00843883.
Lemma F_5d134 : fetch_word Asan.M.loaded_segments (0x5d184 : word) = Some W_5d134.
Proof. vm_refl. Qed.
Lemma D_5d134 : decode_any W_5d134 = Some (Load SZ8 true 17 8 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d138 : bv 32 := 0x00f807b3.
Lemma F_5d138 : fetch_word Asan.M.loaded_segments (0x5d188 : word) = Some W_5d138.
Proof. vm_refl. Qed.
Lemma D_5d138 : decode_any W_5d138 = Some (Op ALU_ADD 15 16 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d13c : bv 32 := 0x05053803.
Lemma F_5d13c : fetch_word Asan.M.loaded_segments (0x5d18c : word) = Some W_5d13c.
Proof. vm_refl. Qed.
Lemma D_5d13c : decode_any W_5d13c = Some (Load SZ8 true 16 10 80, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d140 : bv 32 := 0x05853283.
Lemma F_5d140 : fetch_word Asan.M.loaded_segments (0x5d190 : word) = Some W_5d140.
Proof. vm_refl. Qed.
Lemma D_5d140 : decode_any W_5d140 = Some (Load SZ8 true 5 10 88, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d144 : bv 32 := 0xfff70713.
Lemma F_5d144 : fetch_word Asan.M.loaded_segments (0x5d194 : word) = Some W_5d144.
Proof. vm_refl. Qed.
Lemma D_5d144 : decode_any W_5d144 = Some (OpImm ALU_ADD 14 14 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d148 : bv 32 := 0xff87b783.
Lemma F_5d148 : fetch_word Asan.M.loaded_segments (0x5d198 : word) = Some W_5d148.
Proof. vm_refl. Qed.
Lemma D_5d148 : decode_any W_5d148 = Some (Load SZ8 true 15 15 4088, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d14c : bv 32 := 0x00180813.
Lemma F_5d14c : fetch_word Asan.M.loaded_segments (0x5d19c : word) = Some W_5d14c.
Proof. vm_refl. Qed.
Lemma D_5d14c : decode_any W_5d14c = Some (OpImm ALU_ADD 16 16 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d150 : bv 32 := 0x411282b3.
Lemma F_5d150 : fetch_word Asan.M.loaded_segments (0x5d1a0 : word) = Some W_5d150.
Proof. vm_refl. Qed.
Lemma D_5d150 : decode_any W_5d150 = Some (Op ALU_SUB 5 5 17, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d154 : bv 32 := 0x02e53c23.
Lemma F_5d154 : fetch_word Asan.M.loaded_segments (0x5d1a4 : word) = Some W_5d154.
Proof. vm_refl. Qed.
Lemma D_5d154 : decode_any W_5d154 = Some (Store SZ8 10 14 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d158 : bv 32 := 0x04050023.
Lemma F_5d158 : fetch_word Asan.M.loaded_segments (0x5d1a8 : word) = Some W_5d158.
Proof. vm_refl. Qed.
Lemma D_5d158 : decode_any W_5d158 = Some (Store SZ1 10 0 64, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d15c : bv 32 := 0x05053823.
Lemma F_5d15c : fetch_word Asan.M.loaded_segments (0x5d1ac : word) = Some W_5d15c.
Proof. vm_refl. Qed.
Lemma D_5d15c : decode_any W_5d15c = Some (Store SZ8 10 16 80, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d160 : bv 32 := 0x04553c23.
Lemma F_5d160 : fetch_word Asan.M.loaded_segments (0x5d1b0 : word) = Some W_5d160.
Proof. vm_refl. Qed.
Lemma D_5d160 : decode_any W_5d160 = Some (Store SZ8 10 5 88, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d164 : bv 32 := 0x01058713.
Lemma F_5d164 : fetch_word Asan.M.loaded_segments (0x5d1b4 : word) = Some W_5d164.
Proof. vm_refl. Qed.
Lemma D_5d164 : decode_any W_5d164 = Some (OpImm ALU_ADD 14 11 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d168 : bv 32 := 0x41100833.
Lemma F_5d168 : fetch_word Asan.M.loaded_segments (0x5d1b8 : word) = Some W_5d168.
Proof. vm_refl. Qed.
Lemma D_5d168 : decode_any W_5d168 = Some (Op ALU_SUB 16 0 17, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d16c : bv 32 := 0x00f63023.
Lemma F_5d16c : fetch_word Asan.M.loaded_segments (0x5d1bc : word) = Some W_5d16c.
Proof. vm_refl. Qed.
Lemma D_5d16c : decode_any W_5d16c = Some (Store SZ8 12 15 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d170 : bv 32 := 0x00d7bc23.
Lemma F_5d170 : fetch_word Asan.M.loaded_segments (0x5d1c0 : word) = Some W_5d170.
Proof. vm_refl. Qed.
Lemma D_5d170 : decode_any W_5d170 = Some (Store SZ8 15 13 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d174 : bv 32 := 0x0107302f.
Lemma F_5d174 : fetch_word Asan.M.loaded_segments (0x5d1c4 : word) = Some W_5d174.
Proof. vm_refl. Qed.
Lemma D_5d174 : decode_any W_5d174 = Some (Amo AMO_ADD AD false false 0 14 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d178 : bv 32 := 0x00843603.
Lemma F_5d178 : fetch_word Asan.M.loaded_segments (0x5d1c8 : word) = Some W_5d178.
Proof. vm_refl. Qed.
Lemma D_5d178 : decode_any W_5d178 = Some (Load SZ8 true 12 8 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d17c : bv 32 := 0x01858593.
Lemma F_5d17c : fetch_word Asan.M.loaded_segments (0x5d1cc : word) = Some W_5d17c.
Proof. vm_refl. Qed.
Lemma D_5d17c : decode_any W_5d17c = Some (OpImm ALU_ADD 11 11 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d180 : bv 32 := 0x40c00633.
Lemma F_5d180 : fetch_word Asan.M.loaded_segments (0x5d1d0 : word) = Some W_5d180.
Proof. vm_refl. Qed.
Lemma D_5d180 : decode_any W_5d180 = Some (Op ALU_SUB 12 0 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d184 : bv 32 := 0x00c5b02f.
Lemma F_5d184 : fetch_word Asan.M.loaded_segments (0x5d1d4 : word) = Some W_5d184.
Proof. vm_refl. Qed.
Lemma D_5d184 : decode_any W_5d184 = Some (Amo AMO_ADD AD false false 0 11 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d188 : bv 32 := 0x0310000f.
Lemma F_5d188 : fetch_word Asan.M.loaded_segments (0x5d1d8 : word) = Some W_5d188.
Proof. vm_refl. Qed.
Lemma D_5d188 : decode_any W_5d188 = Some (Fence 0 3 1 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d18c : bv 32 := 0x26050423.
Lemma F_5d18c : fetch_word Asan.M.loaded_segments (0x5d1dc : word) = Some W_5d18c.
Proof. vm_refl. Qed.
Lemma D_5d18c : decode_any W_5d18c = Some (Store SZ1 10 0 616, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d190 : bv 32 := 0x00043483.
Lemma F_5d190 : fetch_word Asan.M.loaded_segments (0x5d1e0 : word) = Some W_5d190.
Proof. vm_refl. Qed.
Lemma D_5d190 : decode_any W_5d190 = Some (Load SZ8 true 9 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d194 : bv 32 := 0x00843903.
Lemma F_5d194 : fetch_word Asan.M.loaded_segments (0x5d1e4 : word) = Some W_5d194.
Proof. vm_refl. Qed.
Lemma D_5d194 : decode_any W_5d194 = Some (Load SZ8 true 18 8 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d198 : bv 32 := 0x00048513.
Lemma F_5d198 : fetch_word Asan.M.loaded_segments (0x5d1e8 : word) = Some W_5d198.
Proof. vm_refl. Qed.
Lemma D_5d198 : decode_any W_5d198 = Some (OpImm ALU_ADD 10 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d19c : bv 32 := 0x00090593.
Lemma F_5d19c : fetch_word Asan.M.loaded_segments (0x5d1ec : word) = Some W_5d19c.
Proof. vm_refl. Qed.
Lemma D_5d19c : decode_any W_5d19c = Some (OpImm ALU_ADD 11 18 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d1a0 : bv 32 := 0x00000613.
Lemma F_5d1a0 : fetch_word Asan.M.loaded_segments (0x5d1f0 : word) = Some W_5d1a0.
Proof. vm_refl. Qed.
Lemma D_5d1a0 : decode_any W_5d1a0 = Some (OpImm ALU_ADD 12 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d1a4 : bv 32 := 0x6f1250ef.
Lemma F_5d1a4 : fetch_word Asan.M.loaded_segments (0x5d1f4 : word) = Some W_5d1a4.
Proof. vm_refl. Qed.
Lemma D_5d1a4 : decode_any W_5d1a4 = Some (Jal 1 155376, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d1a8 : bv 32 := 0x00048513.
Lemma F_5d1a8 : fetch_word Asan.M.loaded_segments (0x5d1f8 : word) = Some W_5d1a8.
Proof. vm_refl. Qed.
Lemma D_5d1a8 : decode_any W_5d1a8 = Some (OpImm ALU_ADD 10 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d1ac : bv 32 := 0x00090593.
Lemma F_5d1ac : fetch_word Asan.M.loaded_segments (0x5d1fc : word) = Some W_5d1ac.
Proof. vm_refl. Qed.
Lemma D_5d1ac : decode_any W_5d1ac = Some (OpImm ALU_ADD 11 18 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d1b0 : bv 32 := 0x0cd240ef.
Lemma F_5d1b0 : fetch_word Asan.M.loaded_segments (0x5d200 : word) = Some W_5d1b0.
Proof. vm_refl. Qed.
Lemma D_5d1b0 : decode_any W_5d1b0 = Some (Jal 1 149708, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d1b4 : bv 32 := 0x6592d0ef.
Lemma F_5d1b4 : fetch_word Asan.M.loaded_segments (0x5d204 : word) = Some W_5d1b4.
Proof. vm_refl. Qed.
Lemma D_5d1b4 : decode_any W_5d1b4 = Some (Jal 1 187992, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d1b8 : bv 32 := 0x06053683.
Lemma F_5d1b8 : fetch_word Asan.M.loaded_segments (0x5d208 : word) = Some W_5d1b8.
Proof. vm_refl. Qed.
Lemma D_5d1b8 : decode_any W_5d1b8 = Some (Load SZ8 true 13 10 96, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d1bc : bv 32 := 0x05853703.
Lemma F_5d1bc : fetch_word Asan.M.loaded_segments (0x5d20c : word) = Some W_5d1bc.
Proof. vm_refl. Qed.
Lemma D_5d1bc : decode_any W_5d1bc = Some (Load SZ8 true 14 10 88, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d1c0 : bv 32 := 0x00043603.
Lemma F_5d1c0 : fetch_word Asan.M.loaded_segments (0x5d210 : word) = Some W_5d1c0.
Proof. vm_refl. Qed.
Lemma D_5d1c0 : decode_any W_5d1c0 = Some (Load SZ8 true 12 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d1c4 : bv 32 := 0x00843583.
Lemma F_5d1c4 : fetch_word Asan.M.loaded_segments (0x5d214 : word) = Some W_5d1c4.
Proof. vm_refl. Qed.
Lemma D_5d1c4 : decode_any W_5d1c4 = Some (Load SZ8 true 11 8 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d1c8 : bv 32 := 0x012686b3.
Lemma F_5d1c8 : fetch_word Asan.M.loaded_segments (0x5d218 : word) = Some W_5d1c8.
Proof. vm_refl. Qed.
Lemma D_5d1c8 : decode_any W_5d1c8 = Some (Op ALU_ADD 13 13 18, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d1cc : bv 32 := 0x00170713.
Lemma F_5d1cc : fetch_word Asan.M.loaded_segments (0x5d21c : word) = Some W_5d1cc.
Proof. vm_refl. Qed.
Lemma D_5d1cc : decode_any W_5d1cc = Some (OpImm ALU_ADD 14 14 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d1d0 : bv 32 := 0x04e53c23.
Lemma F_5d1d0 : fetch_word Asan.M.loaded_segments (0x5d220 : word) = Some W_5d1d0.
Proof. vm_refl. Qed.
Lemma D_5d1d0 : decode_any W_5d1d0 = Some (Store SZ8 10 14 88, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d1d4 : bv 32 := 0x06d53023.
Lemma F_5d1d4 : fetch_word Asan.M.loaded_segments (0x5d224 : word) = Some W_5d1d4.
Proof. vm_refl. Qed.
Lemma D_5d1d4 : decode_any W_5d1d4 = Some (Store SZ8 10 13 96, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d1d8 : bv 32 := 0x00060513.
Lemma F_5d1d8 : fetch_word Asan.M.loaded_segments (0x5d228 : word) = Some W_5d1d8.
Proof. vm_refl. Qed.
Lemma D_5d1d8 : decode_any W_5d1d8 = Some (OpImm ALU_ADD 10 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d1dc : bv 32 := 0x00000613.
Lemma F_5d1dc : fetch_word Asan.M.loaded_segments (0x5d22c : word) = Some W_5d1dc.
Proof. vm_refl. Qed.
Lemma D_5d1dc : decode_any W_5d1dc = Some (OpImm ALU_ADD 12 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d1e0 : bv 32 := 0x01813083.
Lemma F_5d1e0 : fetch_word Asan.M.loaded_segments (0x5d230 : word) = Some W_5d1e0.
Proof. vm_refl. Qed.
Lemma D_5d1e0 : decode_any W_5d1e0 = Some (Load SZ8 true 1 2 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d1e4 : bv 32 := 0x01013403.
Lemma F_5d1e4 : fetch_word Asan.M.loaded_segments (0x5d234 : word) = Some W_5d1e4.
Proof. vm_refl. Qed.
Lemma D_5d1e4 : decode_any W_5d1e4 = Some (Load SZ8 true 8 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d1e8 : bv 32 := 0x00813483.
Lemma F_5d1e8 : fetch_word Asan.M.loaded_segments (0x5d238 : word) = Some W_5d1e8.
Proof. vm_refl. Qed.
Lemma D_5d1e8 : decode_any W_5d1e8 = Some (Load SZ8 true 9 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d1ec : bv 32 := 0x00013903.
Lemma F_5d1ec : fetch_word Asan.M.loaded_segments (0x5d23c : word) = Some W_5d1ec.
Proof. vm_refl. Qed.
Lemma D_5d1ec : decode_any W_5d1ec = Some (Load SZ8 true 18 2 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d1f0 : bv 32 := 0x02010113.
Lemma F_5d1f0 : fetch_word Asan.M.loaded_segments (0x5d240 : word) = Some W_5d1f0.
Proof. vm_refl. Qed.
Lemma D_5d1f0 : decode_any W_5d1f0 = Some (OpImm ALU_ADD 2 2 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d1f4 : bv 32 := 0x0353806f.
Lemma F_5d1f4 : fetch_word Asan.M.loaded_segments (0x5d244 : word) = Some W_5d1f4.
Proof. vm_refl. Qed.
Lemma D_5d1f4 : decode_any W_5d1f4 = Some (Jal 0 231476, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d280 : bv 32 := 0xfc010113.
Lemma F_5d280 : fetch_word Asan.M.loaded_segments (0x5d2d0 : word) = Some W_5d280.
Proof. vm_refl. Qed.
Lemma D_5d280 : decode_any W_5d280 = Some (OpImm ALU_ADD 2 2 4032, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d284 : bv 32 := 0x02113c23.
Lemma F_5d284 : fetch_word Asan.M.loaded_segments (0x5d2d4 : word) = Some W_5d284.
Proof. vm_refl. Qed.
Lemma D_5d284 : decode_any W_5d284 = Some (Store SZ8 2 1 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d288 : bv 32 := 0x02013423.
Lemma F_5d288 : fetch_word Asan.M.loaded_segments (0x5d2d8 : word) = Some W_5d288.
Proof. vm_refl. Qed.
Lemma D_5d288 : decode_any W_5d288 = Some (Store SZ8 2 0 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d28c : bv 32 := 0x02013823.
Lemma F_5d28c : fetch_word Asan.M.loaded_segments (0x5d2dc : word) = Some W_5d28c.
Proof. vm_refl. Qed.
Lemma D_5d28c : decode_any W_5d28c = Some (Store SZ8 2 0 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d290 : bv 32 := 0x0005a803.
Lemma F_5d290 : fetch_word Asan.M.loaded_segments (0x5d2e0 : word) = Some W_5d290.
Proof. vm_refl. Qed.
Lemma D_5d290 : decode_any W_5d290 = Some (Load SZ4 true 16 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d294 : bv 32 := 0x0045e783.
Lemma F_5d294 : fetch_word Asan.M.loaded_segments (0x5d2e4 : word) = Some W_5d294.
Proof. vm_refl. Qed.
Lemma D_5d294 : decode_any W_5d294 = Some (Load SZ4 false 15 11 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d298 : bv 32 := 0x00c13423.
Lemma F_5d298 : fetch_word Asan.M.loaded_segments (0x5d2e8 : word) = Some W_5d298.
Proof. vm_refl. Qed.
Lemma D_5d298 : decode_any W_5d298 = Some (Store SZ8 2 12 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d29c : bv 32 := 0x00013823.
Lemma F_5d29c : fetch_word Asan.M.loaded_segments (0x5d2ec : word) = Some W_5d29c.
Proof. vm_refl. Qed.
Lemma D_5d29c : decode_any W_5d29c = Some (Store SZ8 2 0 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d2a0 : bv 32 := 0x00013c23.
Lemma F_5d2a0 : fetch_word Asan.M.loaded_segments (0x5d2f0 : word) = Some W_5d2a0.
Proof. vm_refl. Qed.
Lemma D_5d2a0 : decode_any W_5d2a0 = Some (Store SZ8 2 0 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d2a4 : bv 32 := 0x02013023.
Lemma F_5d2a4 : fetch_word Asan.M.loaded_segments (0x5d2f4 : word) = Some W_5d2a4.
Proof. vm_refl. Qed.
Lemma D_5d2a4 : decode_any W_5d2a4 = Some (Store SZ8 2 0 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d2a8 : bv 32 := 0x0017d793.
Lemma F_5d2a8 : fetch_word Asan.M.loaded_segments (0x5d2f8 : word) = Some W_5d2a8.
Proof. vm_refl. Qed.
Lemma D_5d2a8 : decode_any W_5d2a8 = Some (ShiftImm ALU_SRL 15 15 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d2ac : bv 32 := 0x02081713.
Lemma F_5d2ac : fetch_word Asan.M.loaded_segments (0x5d2fc : word) = Some W_5d2ac.
Proof. vm_refl. Qed.
Lemma D_5d2ac : decode_any W_5d2ac = Some (ShiftImm ALU_SLL 14 16 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d2b0 : bv 32 := 0x02075713.
Lemma F_5d2b0 : fetch_word Asan.M.loaded_segments (0x5d300 : word) = Some W_5d2b0.
Proof. vm_refl. Qed.
Lemma D_5d2b0 : decode_any W_5d2b0 = Some (ShiftImm ALU_SRL 14 14 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d2b4 : bv 32 := 0x04f86663.
Lemma F_5d2b4 : fetch_word Asan.M.loaded_segments (0x5d304 : word) = Some W_5d2b4.
Proof. vm_refl. Qed.
Lemma D_5d2b4 : decode_any W_5d2b4 = Some (Branch BC_LTU 16 15 76, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d2b8 : bv 32 := 0x40f70733.
Lemma F_5d2b8 : fetch_word Asan.M.loaded_segments (0x5d308 : word) = Some W_5d2b8.
Proof. vm_refl. Qed.
Lemma D_5d2b8 : decode_any W_5d2b8 = Some (Op ALU_SUB 14 14 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d2bc : bv 32 := 0x7ff50513.
Lemma F_5d2bc : fetch_word Asan.M.loaded_segments (0x5d30c : word) = Some W_5d2bc.
Proof. vm_refl. Qed.
Lemma D_5d2bc : decode_any W_5d2bc = Some (OpImm ALU_ADD 10 10 2047, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d2c0 : bv 32 := 0x00e5a023.
Lemma F_5d2c0 : fetch_word Asan.M.loaded_segments (0x5d310 : word) = Some W_5d2c0.
Proof. vm_refl. Qed.
Lemma D_5d2c0 : decode_any W_5d2c0 = Some (Store SZ4 11 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d2c4 : bv 32 := 0x20150813.
Lemma F_5d2c4 : fetch_word Asan.M.loaded_segments (0x5d314 : word) = Some W_5d2c4.
Proof. vm_refl. Qed.
Lemma D_5d2c4 : decode_any W_5d2c4 = Some (OpImm ALU_ADD 16 10 513, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d2c8 : bv 32 := 0x00271713.
Lemma F_5d2c8 : fetch_word Asan.M.loaded_segments (0x5d318 : word) = Some W_5d2c8.
Proof. vm_refl. Qed.
Lemma D_5d2c8 : decode_any W_5d2c8 = Some (ShiftImm ALU_SLL 14 14 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d2cc : bv 32 := 0x00e585b3.
Lemma F_5d2cc : fetch_word Asan.M.loaded_segments (0x5d31c : word) = Some W_5d2cc.
Proof. vm_refl. Qed.
Lemma D_5d2cc : decode_any W_5d2cc = Some (Op ALU_ADD 11 11 14, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d2d0 : bv 32 := 0x01058713.
Lemma F_5d2d0 : fetch_word Asan.M.loaded_segments (0x5d320 : word) = Some W_5d2d0.
Proof. vm_refl. Qed.
Lemma D_5d2d0 : decode_any W_5d2d0 = Some (OpImm ALU_ADD 14 11 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d2d4 : bv 32 := 0x00810593.
Lemma F_5d2d4 : fetch_word Asan.M.loaded_segments (0x5d324 : word) = Some W_5d2d4.
Proof. vm_refl. Qed.
Lemma D_5d2d4 : decode_any W_5d2d4 = Some (OpImm ALU_ADD 11 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d2d8 : bv 32 := 0x00060513.
Lemma F_5d2d8 : fetch_word Asan.M.loaded_segments (0x5d328 : word) = Some W_5d2d8.
Proof. vm_refl. Qed.
Lemma D_5d2d8 : decode_any W_5d2d8 = Some (OpImm ALU_ADD 10 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d2dc : bv 32 := 0x00080613.
Lemma F_5d2dc : fetch_word Asan.M.loaded_segments (0x5d32c : word) = Some W_5d2dc.
Proof. vm_refl. Qed.
Lemma D_5d2dc : decode_any W_5d2dc = Some (OpImm ALU_ADD 12 16 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d2e0 : bv 32 := 0x144000ef.
Lemma F_5d2e0 : fetch_word Asan.M.loaded_segments (0x5d330 : word) = Some W_5d2e0.
Proof. vm_refl. Qed.
Lemma D_5d2e0 : decode_any W_5d2e0 = Some (Jal 1 324, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d2e4 : bv 32 := 0x02013503.
Lemma F_5d2e4 : fetch_word Asan.M.loaded_segments (0x5d334 : word) = Some W_5d2e4.
Proof. vm_refl. Qed.
Lemma D_5d2e4 : decode_any W_5d2e4 = Some (Load SZ8 true 10 2 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d2e8 : bv 32 := 0x02813583.
Lemma F_5d2e8 : fetch_word Asan.M.loaded_segments (0x5d338 : word) = Some W_5d2e8.
Proof. vm_refl. Qed.
Lemma D_5d2e8 : decode_any W_5d2e8 = Some (Load SZ8 true 11 2 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d2ec : bv 32 := 0x00000613.
Lemma F_5d2ec : fetch_word Asan.M.loaded_segments (0x5d33c : word) = Some W_5d2ec.
Proof. vm_refl. Qed.
Lemma D_5d2ec : decode_any W_5d2ec = Some (OpImm ALU_ADD 12 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d2f0 : bv 32 := 0x738380ef.
Lemma F_5d2f0 : fetch_word Asan.M.loaded_segments (0x5d340 : word) = Some W_5d2f0.
Proof. vm_refl. Qed.
Lemma D_5d2f0 : decode_any W_5d2f0 = Some (Jal 1 231224, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d2f4 : bv 32 := 0x03813083.
Lemma F_5d2f4 : fetch_word Asan.M.loaded_segments (0x5d344 : word) = Some W_5d2f4.
Proof. vm_refl. Qed.
Lemma D_5d2f4 : decode_any W_5d2f4 = Some (Load SZ8 true 1 2 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d2f8 : bv 32 := 0x04010113.
Lemma F_5d2f8 : fetch_word Asan.M.loaded_segments (0x5d348 : word) = Some W_5d2f8.
Proof. vm_refl. Qed.
Lemma D_5d2f8 : decode_any W_5d2f8 = Some (OpImm ALU_ADD 2 2 64, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d2fc : bv 32 := 0x00008067.
Lemma F_5d2fc : fetch_word Asan.M.loaded_segments (0x5d34c : word) = Some W_5d2fc.
Proof. vm_refl. Qed.
Lemma D_5d2fc : decode_any W_5d2fc = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d424 : bv 32 := 0xf8010113.
Lemma F_5d424 : fetch_word Asan.M.loaded_segments (0x5d474 : word) = Some W_5d424.
Proof. vm_refl. Qed.
Lemma D_5d424 : decode_any W_5d424 = Some (OpImm ALU_ADD 2 2 3968, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d428 : bv 32 := 0x06113c23.
Lemma F_5d428 : fetch_word Asan.M.loaded_segments (0x5d478 : word) = Some W_5d428.
Proof. vm_refl. Qed.
Lemma D_5d428 : decode_any W_5d428 = Some (Store SZ8 2 1 120, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d42c : bv 32 := 0x06813823.
Lemma F_5d42c : fetch_word Asan.M.loaded_segments (0x5d47c : word) = Some W_5d42c.
Proof. vm_refl. Qed.
Lemma D_5d42c : decode_any W_5d42c = Some (Store SZ8 2 8 112, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d430 : bv 32 := 0x06913423.
Lemma F_5d430 : fetch_word Asan.M.loaded_segments (0x5d480 : word) = Some W_5d430.
Proof. vm_refl. Qed.
Lemma D_5d430 : decode_any W_5d430 = Some (Store SZ8 2 9 104, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d434 : bv 32 := 0x07213023.
Lemma F_5d434 : fetch_word Asan.M.loaded_segments (0x5d484 : word) = Some W_5d434.
Proof. vm_refl. Qed.
Lemma D_5d434 : decode_any W_5d434 = Some (Store SZ8 2 18 96, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d438 : bv 32 := 0x05313c23.
Lemma F_5d438 : fetch_word Asan.M.loaded_segments (0x5d488 : word) = Some W_5d438.
Proof. vm_refl. Qed.
Lemma D_5d438 : decode_any W_5d438 = Some (Store SZ8 2 19 88, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d43c : bv 32 := 0x05413823.
Lemma F_5d43c : fetch_word Asan.M.loaded_segments (0x5d48c : word) = Some W_5d43c.
Proof. vm_refl. Qed.
Lemma D_5d43c : decode_any W_5d43c = Some (Store SZ8 2 20 80, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d440 : bv 32 := 0x05513423.
Lemma F_5d440 : fetch_word Asan.M.loaded_segments (0x5d490 : word) = Some W_5d440.
Proof. vm_refl. Qed.
Lemma D_5d440 : decode_any W_5d440 = Some (Store SZ8 2 21 72, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d444 : bv 32 := 0x05613023.
Lemma F_5d444 : fetch_word Asan.M.loaded_segments (0x5d494 : word) = Some W_5d444.
Proof. vm_refl. Qed.
Lemma D_5d444 : decode_any W_5d444 = Some (Store SZ8 2 22 64, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d448 : bv 32 := 0x03713c23.
Lemma F_5d448 : fetch_word Asan.M.loaded_segments (0x5d498 : word) = Some W_5d448.
Proof. vm_refl. Qed.
Lemma D_5d448 : decode_any W_5d448 = Some (Store SZ8 2 23 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d44c : bv 32 := 0x03813823.
Lemma F_5d44c : fetch_word Asan.M.loaded_segments (0x5d49c : word) = Some W_5d44c.
Proof. vm_refl. Qed.
Lemma D_5d44c : decode_any W_5d44c = Some (Store SZ8 2 24 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d450 : bv 32 := 0x03913423.
Lemma F_5d450 : fetch_word Asan.M.loaded_segments (0x5d4a0 : word) = Some W_5d450.
Proof. vm_refl. Qed.
Lemma D_5d450 : decode_any W_5d450 = Some (Store SZ8 2 25 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d454 : bv 32 := 0x03a13023.
Lemma F_5d454 : fetch_word Asan.M.loaded_segments (0x5d4a4 : word) = Some W_5d454.
Proof. vm_refl. Qed.
Lemma D_5d454 : decode_any W_5d454 = Some (Store SZ8 2 26 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d458 : bv 32 := 0x01b13c23.
Lemma F_5d458 : fetch_word Asan.M.loaded_segments (0x5d4a8 : word) = Some W_5d458.
Proof. vm_refl. Qed.
Lemma D_5d458 : decode_any W_5d458 = Some (Store SZ8 2 27 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d45c : bv 32 := 0x00078a93.
Lemma F_5d45c : fetch_word Asan.M.loaded_segments (0x5d4ac : word) = Some W_5d45c.
Proof. vm_refl. Qed.
Lemma D_5d45c : decode_any W_5d45c = Some (OpImm ALU_ADD 21 15 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d460 : bv 32 := 0x00070b13.
Lemma F_5d460 : fetch_word Asan.M.loaded_segments (0x5d4b0 : word) = Some W_5d460.
Proof. vm_refl. Qed.
Lemma D_5d460 : decode_any W_5d460 = Some (OpImm ALU_ADD 22 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d464 : bv 32 := 0x00068913.
Lemma F_5d464 : fetch_word Asan.M.loaded_segments (0x5d4b4 : word) = Some W_5d464.
Proof. vm_refl. Qed.
Lemma D_5d464 : decode_any W_5d464 = Some (OpImm ALU_ADD 18 13 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d468 : bv 32 := 0x00058993.
Lemma F_5d468 : fetch_word Asan.M.loaded_segments (0x5d4b8 : word) = Some W_5d468.
Proof. vm_refl. Qed.
Lemma D_5d468 : decode_any W_5d468 = Some (OpImm ALU_ADD 19 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d46c : bv 32 := 0x00050a13.
Lemma F_5d46c : fetch_word Asan.M.loaded_segments (0x5d4bc : word) = Some W_5d46c.
Proof. vm_refl. Qed.
Lemma D_5d46c : decode_any W_5d46c = Some (OpImm ALU_ADD 20 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d470 : bv 32 := 0x00000513.
Lemma F_5d470 : fetch_word Asan.M.loaded_segments (0x5d4c0 : word) = Some W_5d470.
Proof. vm_refl. Qed.
Lemma D_5d470 : decode_any W_5d470 = Some (OpImm ALU_ADD 10 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d474 : bv 32 := 0x00100d93.
Lemma F_5d474 : fetch_word Asan.M.loaded_segments (0x5d4c4 : word) = Some W_5d474.
Proof. vm_refl. Qed.
Lemma D_5d474 : decode_any W_5d474 = Some (OpImm ALU_ADD 27 0 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d478 : bv 32 := 0x020a3603.
Lemma F_5d478 : fetch_word Asan.M.loaded_segments (0x5d4c8 : word) = Some W_5d478.
Proof. vm_refl. Qed.
Lemma D_5d478 : decode_any W_5d478 = Some (Load SZ8 true 12 20 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d47c : bv 32 := 0x030a3403.
Lemma F_5d47c : fetch_word Asan.M.loaded_segments (0x5d4cc : word) = Some W_5d47c.
Proof. vm_refl. Qed.
Lemma D_5d47c : decode_any W_5d47c = Some (Load SZ8 true 8 20 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d480 : bv 32 := 0x00769693.
Lemma F_5d480 : fetch_word Asan.M.loaded_segments (0x5d4d0 : word) = Some W_5d480.
Proof. vm_refl. Qed.
Lemma D_5d480 : decode_any W_5d480 = Some (ShiftImm ALU_SLL 13 13 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d484 : bv 32 := 0x02091713.
Lemma F_5d484 : fetch_word Asan.M.loaded_segments (0x5d4d4 : word) = Some W_5d484.
Proof. vm_refl. Qed.
Lemma D_5d484 : decode_any W_5d484 = Some (ShiftImm ALU_SLL 14 18 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d488 : bv 32 := 0x00700793.
Lemma F_5d488 : fetch_word Asan.M.loaded_segments (0x5d4d8 : word) = Some W_5d488.
Proof. vm_refl. Qed.
Lemma D_5d488 : decode_any W_5d488 = Some (OpImm ALU_ADD 15 0 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d48c : bv 32 := 0xfff00593.
Lemma F_5d48c : fetch_word Asan.M.loaded_segments (0x5d4dc : word) = Some W_5d48c.
Proof. vm_refl. Qed.
Lemma D_5d48c : decode_any W_5d48c = Some (OpImm ALU_ADD 11 0 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d490 : bv 32 := 0x03dd9c13.
Lemma F_5d490 : fetch_word Asan.M.loaded_segments (0x5d4e0 : word) = Some W_5d490.
Proof. vm_refl. Qed.
Lemma D_5d490 : decode_any W_5d490 = Some (ShiftImm ALU_SLL 24 27 61, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d494 : bv 32 := 0x01d79793.
Lemma F_5d494 : fetch_word Asan.M.loaded_segments (0x5d4e4 : word) = Some W_5d494.
Proof. vm_refl. Qed.
Lemma D_5d494 : decode_any W_5d494 = Some (ShiftImm ALU_SLL 15 15 29, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d498 : bv 32 := 0x028d9b93.
Lemma F_5d498 : fetch_word Asan.M.loaded_segments (0x5d4e8 : word) = Some W_5d498.
Proof. vm_refl. Qed.
Lemma D_5d498 : decode_any W_5d498 = Some (ShiftImm ALU_SLL 23 27 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d49c : bv 32 := 0x001b8813.
Lemma F_5d49c : fetch_word Asan.M.loaded_segments (0x5d4ec : word) = Some W_5d49c.
Proof. vm_refl. Qed.
Lemma D_5d49c : decode_any W_5d49c = Some (OpImm ALU_ADD 16 23 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d4a0 : bv 32 := 0x01481813.
Lemma F_5d4a0 : fetch_word Asan.M.loaded_segments (0x5d4f0 : word) = Some W_5d4a0.
Proof. vm_refl. Qed.
Lemma D_5d4a0 : decode_any W_5d4a0 = Some (ShiftImm ALU_SLL 16 16 20, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d4a4 : bv 32 := 0x00d40433.
Lemma F_5d4a4 : fetch_word Asan.M.loaded_segments (0x5d4f4 : word) = Some W_5d4a4.
Proof. vm_refl. Qed.
Lemma D_5d4a4 : decode_any W_5d4a4 = Some (Op ALU_ADD 8 8 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d4a8 : bv 32 := 0x00e60633.
Lemma F_5d4a8 : fetch_word Asan.M.loaded_segments (0x5d4f8 : word) = Some W_5d4a8.
Proof. vm_refl. Qed.
Lemma D_5d4a8 : decode_any W_5d4a8 = Some (Op ALU_ADD 12 12 14, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d4ac : bv 32 := 0xfff80d13.
Lemma F_5d4ac : fetch_word Asan.M.loaded_segments (0x5d4fc : word) = Some W_5d4ac.
Proof. vm_refl. Qed.
Lemma D_5d4ac : decode_any W_5d4ac = Some (OpImm ALU_ADD 26 16 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d4b0 : bv 32 := 0x00f60cb3.
Lemma F_5d4b0 : fetch_word Asan.M.loaded_segments (0x5d500 : word) = Some W_5d4b0.
Proof. vm_refl. Qed.
Lemma D_5d4b0 : decode_any W_5d4b0 = Some (Op ALU_ADD 25 12 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d4b4 : bv 32 := 0x00043683.
Lemma F_5d4b4 : fetch_word Asan.M.loaded_segments (0x5d504 : word) = Some W_5d4b4.
Proof. vm_refl. Qed.
Lemma D_5d4b4 : decode_any W_5d4b4 = Some (Load SZ8 true 13 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d4b8 : bv 32 := 0x00840713.
Lemma F_5d4b8 : fetch_word Asan.M.loaded_segments (0x5d508 : word) = Some W_5d4b8.
Proof. vm_refl. Qed.
Lemma D_5d4b8 : decode_any W_5d4b8 = Some (OpImm ALU_ADD 14 8 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d4bc : bv 32 := 0x00e13823.
Lemma F_5d4bc : fetch_word Asan.M.loaded_segments (0x5d50c : word) = Some W_5d4bc.
Proof. vm_refl. Qed.
Lemma D_5d4bc : decode_any W_5d4bc = Some (Store SZ8 2 14 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d4c0 : bv 32 := 0x03cd9d93.
Lemma F_5d4c0 : fetch_word Asan.M.loaded_segments (0x5d510 : word) = Some W_5d4c0.
Proof. vm_refl. Qed.
Lemma D_5d4c0 : decode_any W_5d4c0 = Some (ShiftImm ALU_SLL 27 27 60, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d4c4 : bv 32 := 0x5dc00893.
Lemma F_5d4c4 : fetch_word Asan.M.loaded_segments (0x5d514 : word) = Some W_5d4c4.
Proof. vm_refl. Qed.
Lemma D_5d4c4 : decode_any W_5d4c4 = Some (OpImm ALU_ADD 17 0 1500, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d4c8 : bv 32 := 0x03d59493.
Lemma F_5d4c8 : fetch_word Asan.M.loaded_segments (0x5d518 : word) = Some W_5d4c8.
Proof. vm_refl. Qed.
Lemma D_5d4c8 : decode_any W_5d4c8 = Some (ShiftImm ALU_SLL 9 11 61, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d4cc : bv 32 := 0xfff48493.
Lemma F_5d4cc : fetch_word Asan.M.loaded_segments (0x5d51c : word) = Some W_5d4cc.
Proof. vm_refl. Qed.
Lemma D_5d4cc : decode_any W_5d4cc = Some (OpImm ALU_ADD 9 9 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d4d0 : bv 32 := 0x01a6f733.
Lemma F_5d4d0 : fetch_word Asan.M.loaded_segments (0x5d520 : word) = Some W_5d4d0.
Proof. vm_refl. Qed.
Lemma D_5d4d0 : decode_any W_5d4d0 = Some (Op ALU_AND 14 13 26, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d4d4 : bv 32 := 0x02071663.
Lemma F_5d4d4 : fetch_word Asan.M.loaded_segments (0x5d524 : word) = Some W_5d4d4.
Proof. vm_refl. Qed.
Lemma D_5d4d4 : decode_any W_5d4d4 = Some (Branch BC_NE 14 0 44, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d4d8 : bv 32 := 0x01b6e733.
Lemma F_5d4d8 : fetch_word Asan.M.loaded_segments (0x5d528 : word) = Some W_5d4d8.
Proof. vm_refl. Qed.
Lemma D_5d4d8 : decode_any W_5d4d8 = Some (Op ALU_OR 14 13 27, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d4dc : bv 32 := 0x00e5f7b3.
Lemma F_5d4dc : fetch_word Asan.M.loaded_segments (0x5d52c : word) = Some W_5d4dc.
Proof. vm_refl. Qed.
Lemma D_5d4dc : decode_any W_5d4dc = Some (Op ALU_AND 15 11 14, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d4e0 : bv 32 := 0x1604372f.
Lemma F_5d4e0 : fetch_word Asan.M.loaded_segments (0x5d530 : word) = Some W_5d4e0.
Proof. vm_refl. Qed.
Lemma D_5d4e0 : decode_any W_5d4e0 = Some (Lr AD true true 14 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d4e4 : bv 32 := 0x00d71663.
Lemma F_5d4e4 : fetch_word Asan.M.loaded_segments (0x5d534 : word) = Some W_5d4e4.
Proof. vm_refl. Qed.
Lemma D_5d4e4 : decode_any W_5d4e4 = Some (Branch BC_NE 14 13 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d4e8 : bv 32 := 0x1af4382f.
Lemma F_5d4e8 : fetch_word Asan.M.loaded_segments (0x5d538 : word) = Some W_5d4e8.
Proof. vm_refl. Qed.
Lemma D_5d4e8 : decode_any W_5d4e8 = Some (Sc AD false true 16 8 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d4ec : bv 32 := 0xfe081ae3.
Lemma F_5d4ec : fetch_word Asan.M.loaded_segments (0x5d53c : word) = Some W_5d4ec.
Proof. vm_refl. Qed.
Lemma D_5d4ec : decode_any W_5d4ec = Some (Branch BC_NE 16 0 8180, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d4f0 : bv 32 := 0x08d70063.
Lemma F_5d4f0 : fetch_word Asan.M.loaded_segments (0x5d540 : word) = Some W_5d4f0.
Proof. vm_refl. Qed.
Lemma D_5d4f0 : decode_any W_5d4f0 = Some (Branch BC_EQ 14 13 128, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d570 : bv 32 := 0x01043483.
Lemma F_5d570 : fetch_word Asan.M.loaded_segments (0x5d5c0 : word) = Some W_5d570.
Proof. vm_refl. Qed.
Lemma D_5d570 : decode_any W_5d570 = Some (Load SZ8 true 9 8 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d574 : bv 32 := 0x01548bb3.
Lemma F_5d574 : fetch_word Asan.M.loaded_segments (0x5d5c4 : word) = Some W_5d574.
Proof. vm_refl. Qed.
Lemma D_5d574 : decode_any W_5d574 = Some (Op ALU_ADD 23 9 21, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d578 : bv 32 := 0x000a0513.
Lemma F_5d578 : fetch_word Asan.M.loaded_segments (0x5d5c8 : word) = Some W_5d578.
Proof. vm_refl. Qed.
Lemma D_5d578 : decode_any W_5d578 = Some (OpImm ALU_ADD 10 20 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d57c : bv 32 := 0x00040593.
Lemma F_5d57c : fetch_word Asan.M.loaded_segments (0x5d5cc : word) = Some W_5d57c.
Proof. vm_refl. Qed.
Lemma D_5d57c : decode_any W_5d57c = Some (OpImm ALU_ADD 11 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d580 : bv 32 := 0x000b8693.
Lemma F_5d580 : fetch_word Asan.M.loaded_segments (0x5d5d0 : word) = Some W_5d580.
Proof. vm_refl. Qed.
Lemma D_5d580 : decode_any W_5d580 = Some (OpImm ALU_ADD 13 23 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d584 : bv 32 := 0x1c8000ef.
Lemma F_5d584 : fetch_word Asan.M.loaded_segments (0x5d5d4 : word) = Some W_5d584.
Proof. vm_refl. Qed.
Lemma D_5d584 : decode_any W_5d584 = Some (Jal 1 456, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d588 : bv 32 := 0x18050463.
Lemma F_5d588 : fetch_word Asan.M.loaded_segments (0x5d5d8 : word) = Some W_5d588.
Proof. vm_refl. Qed.
Lemma D_5d588 : decode_any W_5d588 = Some (Branch BC_EQ 10 0 392, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d58c : bv 32 := 0x020a8463.
Lemma F_5d58c : fetch_word Asan.M.loaded_segments (0x5d5dc : word) = Some W_5d58c.
Proof. vm_refl. Qed.
Lemma D_5d58c : decode_any W_5d58c = Some (Branch BC_EQ 21 0 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d590 : bv 32 := 0x00249493.
Lemma F_5d590 : fetch_word Asan.M.loaded_segments (0x5d5e0 : word) = Some W_5d590.
Proof. vm_refl. Qed.
Lemma D_5d590 : decode_any W_5d590 = Some (ShiftImm ALU_SLL 9 9 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d594 : bv 32 := 0x009c8cb3.
Lemma F_5d594 : fetch_word Asan.M.loaded_segments (0x5d5e4 : word) = Some W_5d594.
Proof. vm_refl. Qed.
Lemma D_5d594 : decode_any W_5d594 = Some (Op ALU_ADD 25 25 9, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d598 : bv 32 := 0x002a9513.
Lemma F_5d598 : fetch_word Asan.M.loaded_segments (0x5d5e8 : word) = Some W_5d598.
Proof. vm_refl. Qed.
Lemma D_5d598 : decode_any W_5d598 = Some (ShiftImm ALU_SLL 10 21 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d59c : bv 32 := 0x00ab0533.
Lemma F_5d59c : fetch_word Asan.M.loaded_segments (0x5d5ec : word) = Some W_5d59c.
Proof. vm_refl. Qed.
Lemma D_5d59c : decode_any W_5d59c = Some (Op ALU_ADD 10 22 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d5a0 : bv 32 := 0x000b2583.
Lemma F_5d5a0 : fetch_word Asan.M.loaded_segments (0x5d5f0 : word) = Some W_5d5a0.
Proof. vm_refl. Qed.
Lemma D_5d5a0 : decode_any W_5d5a0 = Some (Load SZ4 true 11 22 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d5a4 : bv 32 := 0x004b0b13.
Lemma F_5d5a4 : fetch_word Asan.M.loaded_segments (0x5d5f4 : word) = Some W_5d5a4.
Proof. vm_refl. Qed.
Lemma D_5d5a4 : decode_any W_5d5a4 = Some (OpImm ALU_ADD 22 22 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d5a8 : bv 32 := 0x00bca023.
Lemma F_5d5a8 : fetch_word Asan.M.loaded_segments (0x5d5f8 : word) = Some W_5d5a8.
Proof. vm_refl. Qed.
Lemma D_5d5a8 : decode_any W_5d5a8 = Some (Store SZ4 25 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d5ac : bv 32 := 0x004c8c93.
Lemma F_5d5ac : fetch_word Asan.M.loaded_segments (0x5d5fc : word) = Some W_5d5ac.
Proof. vm_refl. Qed.
Lemma D_5d5ac : decode_any W_5d5ac = Some (OpImm ALU_ADD 25 25 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d5b0 : bv 32 := 0xfeab18e3.
Lemma F_5d5b0 : fetch_word Asan.M.loaded_segments (0x5d600 : word) = Some W_5d5b0.
Proof. vm_refl. Qed.
Lemma D_5d5b0 : decode_any W_5d5b0 = Some (Branch BC_NE 22 10 8176, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d5b4 : bv 32 := 0x05043503.
Lemma F_5d5b4 : fetch_word Asan.M.loaded_segments (0x5d604 : word) = Some W_5d5b4.
Proof. vm_refl. Qed.
Lemma D_5d5b4 : decode_any W_5d5b4 = Some (Load SZ8 true 10 8 80, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d5b8 : bv 32 := 0x01743823.
Lemma F_5d5b8 : fetch_word Asan.M.loaded_segments (0x5d608 : word) = Some W_5d5b8.
Proof. vm_refl. Qed.
Lemma D_5d5b8 : decode_any W_5d5b8 = Some (Store SZ8 8 23 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d5bc : bv 32 := 0x01550533.
Lemma F_5d5bc : fetch_word Asan.M.loaded_segments (0x5d60c : word) = Some W_5d5bc.
Proof. vm_refl. Qed.
Lemma D_5d5bc : decode_any W_5d5bc = Some (Op ALU_ADD 10 10 21, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d5c0 : bv 32 := 0x04a43823.
Lemma F_5d5c0 : fetch_word Asan.M.loaded_segments (0x5d610 : word) = Some W_5d5c0.
Proof. vm_refl. Qed.
Lemma D_5d5c0 : decode_any W_5d5c0 = Some (Store SZ8 8 10 80, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d5c4 : bv 32 := 0x000a0513.
Lemma F_5d5c4 : fetch_word Asan.M.loaded_segments (0x5d614 : word) = Some W_5d5c4.
Proof. vm_refl. Qed.
Lemma D_5d5c4 : decode_any W_5d5c4 = Some (OpImm ALU_ADD 10 20 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d5c8 : bv 32 := 0x00098593.
Lemma F_5d5c8 : fetch_word Asan.M.loaded_segments (0x5d618 : word) = Some W_5d5c8.
Proof. vm_refl. Qed.
Lemma D_5d5c8 : decode_any W_5d5c8 = Some (OpImm ALU_ADD 11 19 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d5cc : bv 32 := 0x00090613.
Lemma F_5d5cc : fetch_word Asan.M.loaded_segments (0x5d61c : word) = Some W_5d5cc.
Proof. vm_refl. Qed.
Lemma D_5d5cc : decode_any W_5d5cc = Some (OpImm ALU_ADD 12 18 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d5d0 : bv 32 := 0x00000693.
Lemma F_5d5d0 : fetch_word Asan.M.loaded_segments (0x5d620 : word) = Some W_5d5d0.
Proof. vm_refl. Qed.
Lemma D_5d5d0 : decode_any W_5d5d0 = Some (OpImm ALU_ADD 13 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d5d4 : bv 32 := 0x2f8000ef.
Lemma F_5d5d4 : fetch_word Asan.M.loaded_segments (0x5d624 : word) = Some W_5d5d4.
Proof. vm_refl. Qed.
Lemma D_5d5d4 : decode_any W_5d5d4 = Some (Jal 1 760, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d5d8 : bv 32 := 0x00043503.
Lemma F_5d5d8 : fetch_word Asan.M.loaded_segments (0x5d628 : word) = Some W_5d5d8.
Proof. vm_refl. Qed.
Lemma D_5d5d8 : decode_any W_5d5d8 = Some (Load SZ8 true 10 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d5dc : bv 32 := 0xfff00813.
Lemma F_5d5dc : fetch_word Asan.M.loaded_segments (0x5d62c : word) = Some W_5d5dc.
Proof. vm_refl. Qed.
Lemma D_5d5dc : decode_any W_5d5dc = Some (OpImm ALU_ADD 16 0 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d5e0 : bv 32 := 0x00300613.
Lemma F_5d5e0 : fetch_word Asan.M.loaded_segments (0x5d630 : word) = Some W_5d5e0.
Proof. vm_refl. Qed.
Lemma D_5d5e0 : decode_any W_5d5e0 = Some (OpImm ALU_ADD 12 0 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d5e4 : bv 32 := 0x001005b7.
Lemma F_5d5e4 : fetch_word Asan.M.loaded_segments (0x5d634 : word) = Some W_5d5e4.
Proof. vm_refl. Qed.
Lemma D_5d5e4 : decode_any W_5d5e4 = Some (Lui 11 256, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d5e8 : bv 32 := 0xfffb3697.
Lemma F_5d5e8 : fetch_word Asan.M.loaded_segments (0x5d638 : word) = Some W_5d5e8.
Proof. vm_refl. Qed.
Lemma D_5d5e8 : decode_any W_5d5e8 = Some (Auipc 13 1048499, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d5ec : bv 32 := 0x03c81713.
Lemma F_5d5ec : fetch_word Asan.M.loaded_segments (0x5d63c : word) = Some W_5d5ec.
Proof. vm_refl. Qed.
Lemma D_5d5ec : decode_any W_5d5ec = Some (ShiftImm ALU_SLL 14 16 60, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d5f0 : bv 32 := 0x03d61613.
Lemma F_5d5f0 : fetch_word Asan.M.loaded_segments (0x5d640 : word) = Some W_5d5f0.
Proof. vm_refl. Qed.
Lemma D_5d5f0 : decode_any W_5d5f0 = Some (ShiftImm ALU_SLL 12 12 61, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d5f4 : bv 32 := 0xfff58593.
Lemma F_5d5f4 : fetch_word Asan.M.loaded_segments (0x5d644 : word) = Some W_5d5f4.
Proof. vm_refl. Qed.
Lemma D_5d5f4 : decode_any W_5d5f4 = Some (OpImm ALU_ADD 11 11 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d5f8 : bv 32 := 0xe086b683.
Lemma F_5d5f8 : fetch_word Asan.M.loaded_segments (0x5d648 : word) = Some W_5d5f8.
Proof. vm_refl. Qed.
Lemma D_5d5f8 : decode_any W_5d5f8 = Some (Load SZ8 true 13 13 3592, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d5fc : bv 32 := 0xfff70713.
Lemma F_5d5fc : fetch_word Asan.M.loaded_segments (0x5d64c : word) = Some W_5d5fc.
Proof. vm_refl. Qed.
Lemma D_5d5fc : decode_any W_5d5fc = Some (OpImm ALU_ADD 14 14 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d600 : bv 32 := 0x02859793.
Lemma F_5d600 : fetch_word Asan.M.loaded_segments (0x5d650 : word) = Some W_5d600.
Proof. vm_refl. Qed.
Lemma D_5d600 : decode_any W_5d600 = Some (ShiftImm ALU_SLL 15 11 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d604 : bv 32 := 0x02881813.
Lemma F_5d604 : fetch_word Asan.M.loaded_segments (0x5d654 : word) = Some W_5d604.
Proof. vm_refl. Qed.
Lemma D_5d604 : decode_any W_5d604 = Some (ShiftImm ALU_SLL 16 16 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d608 : bv 32 := 0x00100893.
Lemma F_5d608 : fetch_word Asan.M.loaded_segments (0x5d658 : word) = Some W_5d608.
Proof. vm_refl. Qed.
Lemma D_5d608 : decode_any W_5d608 = Some (OpImm ALU_ADD 17 0 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d60c : bv 32 := 0x03e89893.
Lemma F_5d60c : fetch_word Asan.M.loaded_segments (0x5d65c : word) = Some W_5d60c.
Proof. vm_refl. Qed.
Lemma D_5d60c : decode_any W_5d60c = Some (ShiftImm ALU_SLL 17 17 62, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d610 : bv 32 := 0x01c0006f.
Lemma F_5d610 : fetch_word Asan.M.loaded_segments (0x5d660 : word) = Some W_5d610.
Proof. vm_refl. Qed.
Lemma D_5d610 : decode_any W_5d610 = Some (Jal 0 28, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d614 : bv 32 := 0x1604332f.
Lemma F_5d614 : fetch_word Asan.M.loaded_segments (0x5d664 : word) = Some W_5d614.
Proof. vm_refl. Qed.
Lemma D_5d614 : decode_any W_5d614 = Some (Lr AD true true 6 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d618 : bv 32 := 0x00a31663.
Lemma F_5d618 : fetch_word Asan.M.loaded_segments (0x5d668 : word) = Some W_5d618.
Proof. vm_refl. Qed.
Lemma D_5d618 : decode_any W_5d618 = Some (Branch BC_NE 6 10 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d61c : bv 32 := 0x1a5433af.
Lemma F_5d61c : fetch_word Asan.M.loaded_segments (0x5d66c : word) = Some W_5d61c.
Proof. vm_refl. Qed.
Lemma D_5d61c : decode_any W_5d61c = Some (Sc AD false true 7 8 5, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d620 : bv 32 := 0xfe039ae3.
Lemma F_5d620 : fetch_word Asan.M.loaded_segments (0x5d670 : word) = Some W_5d620.
Proof. vm_refl. Qed.
Lemma D_5d620 : decode_any W_5d620 = Some (Branch BC_NE 7 0 8180, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d624 : bv 32 := 0x06a30463.
Lemma F_5d624 : fetch_word Asan.M.loaded_segments (0x5d674 : word) = Some W_5d624.
Proof. vm_refl. Qed.
Lemma D_5d624 : decode_any W_5d624 = Some (Branch BC_EQ 6 10 104, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d62c : bv 32 := 0x00c575b3.
Lemma F_5d62c : fetch_word Asan.M.loaded_segments (0x5d67c : word) = Some W_5d62c.
Proof. vm_refl. Qed.
Lemma D_5d62c : decode_any W_5d62c = Some (Op ALU_AND 11 10 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d630 : bv 32 := 0x00e572b3.
Lemma F_5d630 : fetch_word Asan.M.loaded_segments (0x5d680 : word) = Some W_5d630.
Proof. vm_refl. Qed.
Lemma D_5d630 : decode_any W_5d630 = Some (Op ALU_AND 5 10 14, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d634 : bv 32 := 0x02059663.
Lemma F_5d634 : fetch_word Asan.M.loaded_segments (0x5d684 : word) = Some W_5d634.
Proof. vm_refl. Qed.
Lemma D_5d634 : decode_any W_5d634 = Some (Branch BC_NE 11 0 44, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d638 : bv 32 := 0x00f575b3.
Lemma F_5d638 : fetch_word Asan.M.loaded_segments (0x5d688 : word) = Some W_5d638.
Proof. vm_refl. Qed.
Lemma D_5d638 : decode_any W_5d638 = Some (Op ALU_AND 11 10 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d63c : bv 32 := 0x02058263.
Lemma F_5d63c : fetch_word Asan.M.loaded_segments (0x5d68c : word) = Some W_5d63c.
Proof. vm_refl. Qed.
Lemma D_5d63c : decode_any W_5d63c = Some (Branch BC_EQ 11 0 36, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d660 : bv 32 := 0x018575b3.
Lemma F_5d660 : fetch_word Asan.M.loaded_segments (0x5d6b0 : word) = Some W_5d660.
Proof. vm_refl. Qed.
Lemma D_5d660 : decode_any W_5d660 = Some (Op ALU_AND 11 10 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d664 : bv 32 := 0x00b035b3.
Lemma F_5d664 : fetch_word Asan.M.loaded_segments (0x5d6b4 : word) = Some W_5d664.
Proof. vm_refl. Qed.
Lemma D_5d664 : decode_any W_5d664 = Some (Op ALU_SLTU 11 0 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d668 : bv 32 := 0x01455313.
Lemma F_5d668 : fetch_word Asan.M.loaded_segments (0x5d6b8 : word) = Some W_5d668.
Proof. vm_refl. Qed.
Lemma D_5d668 : decode_any W_5d668 = Some (ShiftImm ALU_SRL 6 10 20, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d66c : bv 32 := 0xfff58593.
Lemma F_5d66c : fetch_word Asan.M.loaded_segments (0x5d6bc : word) = Some W_5d66c.
Proof. vm_refl. Qed.
Lemma D_5d66c : decode_any W_5d66c = Some (OpImm ALU_ADD 11 11 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d670 : bv 32 := 0x00b375b3.
Lemma F_5d670 : fetch_word Asan.M.loaded_segments (0x5d6c0 : word) = Some W_5d670.
Proof. vm_refl. Qed.
Lemma D_5d670 : decode_any W_5d670 = Some (Op ALU_AND 11 6 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d674 : bv 32 := 0x02c59593.
Lemma F_5d674 : fetch_word Asan.M.loaded_segments (0x5d6c4 : word) = Some W_5d674.
Proof. vm_refl. Qed.
Lemma D_5d674 : decode_any W_5d674 = Some (ShiftImm ALU_SLL 11 11 44, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d678 : bv 32 := 0x02c5d593.
Lemma F_5d678 : fetch_word Asan.M.loaded_segments (0x5d6c8 : word) = Some W_5d678.
Proof. vm_refl. Qed.
Lemma D_5d678 : decode_any W_5d678 = Some (ShiftImm ALU_SRL 11 11 44, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d67c : bv 32 := 0xf8058ce3.
Lemma F_5d67c : fetch_word Asan.M.loaded_segments (0x5d6cc : word) = Some W_5d67c.
Proof. vm_refl. Qed.
Lemma D_5d67c : decode_any W_5d67c = Some (Branch BC_EQ 11 0 8088, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d68c : bv 32 := 0x0a059c63.
Lemma F_5d68c : fetch_word Asan.M.loaded_segments (0x5d6dc : word) = Some W_5d68c.
Proof. vm_refl. Qed.
Lemma D_5d68c : decode_any W_5d68c = Some (Branch BC_NE 11 0 184, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d690 : bv 32 := 0x07813083.
Lemma F_5d690 : fetch_word Asan.M.loaded_segments (0x5d6e0 : word) = Some W_5d690.
Proof. vm_refl. Qed.
Lemma D_5d690 : decode_any W_5d690 = Some (Load SZ8 true 1 2 120, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d694 : bv 32 := 0x07013403.
Lemma F_5d694 : fetch_word Asan.M.loaded_segments (0x5d6e4 : word) = Some W_5d694.
Proof. vm_refl. Qed.
Lemma D_5d694 : decode_any W_5d694 = Some (Load SZ8 true 8 2 112, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d698 : bv 32 := 0x06813483.
Lemma F_5d698 : fetch_word Asan.M.loaded_segments (0x5d6e8 : word) = Some W_5d698.
Proof. vm_refl. Qed.
Lemma D_5d698 : decode_any W_5d698 = Some (Load SZ8 true 9 2 104, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d69c : bv 32 := 0x06013903.
Lemma F_5d69c : fetch_word Asan.M.loaded_segments (0x5d6ec : word) = Some W_5d69c.
Proof. vm_refl. Qed.
Lemma D_5d69c : decode_any W_5d69c = Some (Load SZ8 true 18 2 96, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d6a0 : bv 32 := 0x05813983.
Lemma F_5d6a0 : fetch_word Asan.M.loaded_segments (0x5d6f0 : word) = Some W_5d6a0.
Proof. vm_refl. Qed.
Lemma D_5d6a0 : decode_any W_5d6a0 = Some (Load SZ8 true 19 2 88, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d6a4 : bv 32 := 0x05013a03.
Lemma F_5d6a4 : fetch_word Asan.M.loaded_segments (0x5d6f4 : word) = Some W_5d6a4.
Proof. vm_refl. Qed.
Lemma D_5d6a4 : decode_any W_5d6a4 = Some (Load SZ8 true 20 2 80, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d6a8 : bv 32 := 0x04813a83.
Lemma F_5d6a8 : fetch_word Asan.M.loaded_segments (0x5d6f8 : word) = Some W_5d6a8.
Proof. vm_refl. Qed.
Lemma D_5d6a8 : decode_any W_5d6a8 = Some (Load SZ8 true 21 2 72, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d6ac : bv 32 := 0x04013b03.
Lemma F_5d6ac : fetch_word Asan.M.loaded_segments (0x5d6fc : word) = Some W_5d6ac.
Proof. vm_refl. Qed.
Lemma D_5d6ac : decode_any W_5d6ac = Some (Load SZ8 true 22 2 64, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d6b0 : bv 32 := 0x03813b83.
Lemma F_5d6b0 : fetch_word Asan.M.loaded_segments (0x5d700 : word) = Some W_5d6b0.
Proof. vm_refl. Qed.
Lemma D_5d6b0 : decode_any W_5d6b0 = Some (Load SZ8 true 23 2 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d6b4 : bv 32 := 0x03013c03.
Lemma F_5d6b4 : fetch_word Asan.M.loaded_segments (0x5d704 : word) = Some W_5d6b4.
Proof. vm_refl. Qed.
Lemma D_5d6b4 : decode_any W_5d6b4 = Some (Load SZ8 true 24 2 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d6b8 : bv 32 := 0x02813c83.
Lemma F_5d6b8 : fetch_word Asan.M.loaded_segments (0x5d708 : word) = Some W_5d6b8.
Proof. vm_refl. Qed.
Lemma D_5d6b8 : decode_any W_5d6b8 = Some (Load SZ8 true 25 2 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d6bc : bv 32 := 0x02013d03.
Lemma F_5d6bc : fetch_word Asan.M.loaded_segments (0x5d70c : word) = Some W_5d6bc.
Proof. vm_refl. Qed.
Lemma D_5d6bc : decode_any W_5d6bc = Some (Load SZ8 true 26 2 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d6c0 : bv 32 := 0x01813d83.
Lemma F_5d6c0 : fetch_word Asan.M.loaded_segments (0x5d710 : word) = Some W_5d6c0.
Proof. vm_refl. Qed.
Lemma D_5d6c0 : decode_any W_5d6c0 = Some (Load SZ8 true 27 2 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d6c4 : bv 32 := 0x08010113.
Lemma F_5d6c4 : fetch_word Asan.M.loaded_segments (0x5d714 : word) = Some W_5d6c4.
Proof. vm_refl. Qed.
Lemma D_5d6c4 : decode_any W_5d6c4 = Some (OpImm ALU_ADD 2 2 128, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d6c8 : bv 32 := 0x00008067.
Lemma F_5d6c8 : fetch_word Asan.M.loaded_segments (0x5d718 : word) = Some W_5d6c8.
Proof. vm_refl. Qed.
Lemma D_5d6c8 : decode_any W_5d6c8 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d74c : bv 32 := 0xfd010113.
Lemma F_5d74c : fetch_word Asan.M.loaded_segments (0x5d79c : word) = Some W_5d74c.
Proof. vm_refl. Qed.
Lemma D_5d74c : decode_any W_5d74c = Some (OpImm ALU_ADD 2 2 4048, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d750 : bv 32 := 0x02113423.
Lemma F_5d750 : fetch_word Asan.M.loaded_segments (0x5d7a0 : word) = Some W_5d750.
Proof. vm_refl. Qed.
Lemma D_5d750 : decode_any W_5d750 = Some (Store SZ8 2 1 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d754 : bv 32 := 0x02813023.
Lemma F_5d754 : fetch_word Asan.M.loaded_segments (0x5d7a4 : word) = Some W_5d754.
Proof. vm_refl. Qed.
Lemma D_5d754 : decode_any W_5d754 = Some (Store SZ8 2 8 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d758 : bv 32 := 0x00913c23.
Lemma F_5d758 : fetch_word Asan.M.loaded_segments (0x5d7a8 : word) = Some W_5d758.
Proof. vm_refl. Qed.
Lemma D_5d758 : decode_any W_5d758 = Some (Store SZ8 2 9 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d75c : bv 32 := 0x01213823.
Lemma F_5d75c : fetch_word Asan.M.loaded_segments (0x5d7ac : word) = Some W_5d75c.
Proof. vm_refl. Qed.
Lemma D_5d75c : decode_any W_5d75c = Some (Store SZ8 2 18 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d760 : bv 32 := 0x01313423.
Lemma F_5d760 : fetch_word Asan.M.loaded_segments (0x5d7b0 : word) = Some W_5d760.
Proof. vm_refl. Qed.
Lemma D_5d760 : decode_any W_5d760 = Some (Store SZ8 2 19 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d764 : bv 32 := 0x0185b703.
Lemma F_5d764 : fetch_word Asan.M.loaded_segments (0x5d7b4 : word) = Some W_5d764.
Proof. vm_refl. Qed.
Lemma D_5d764 : decode_any W_5d764 = Some (Load SZ8 true 14 11 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d768 : bv 32 := 0x00269793.
Lemma F_5d768 : fetch_word Asan.M.loaded_segments (0x5d7b8 : word) = Some W_5d768.
Proof. vm_refl. Qed.
Lemma D_5d768 : decode_any W_5d768 = Some (ShiftImm ALU_SLL 15 13 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d76c : bv 32 := 0x00100693.
Lemma F_5d76c : fetch_word Asan.M.loaded_segments (0x5d7bc : word) = Some W_5d76c.
Proof. vm_refl. Qed.
Lemma D_5d76c : decode_any W_5d76c = Some (OpImm ALU_ADD 13 0 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d770 : bv 32 := 0x0cf77063.
Lemma F_5d770 : fetch_word Asan.M.loaded_segments (0x5d7c0 : word) = Some W_5d770.
Proof. vm_refl. Qed.
Lemma D_5d770 : decode_any W_5d770 = Some (Branch BC_GEU 14 15 192, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d774 : bv 32 := 0x000406b7.
Lemma F_5d774 : fetch_word Asan.M.loaded_segments (0x5d7c4 : word) = Some W_5d774.
Proof. vm_refl. Qed.
Lemma D_5d774 : decode_any W_5d774 = Some (Lui 13 64, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d778 : bv 32 := 0xfff6869b.
Lemma F_5d778 : fetch_word Asan.M.loaded_segments (0x5d7c8 : word) = Some W_5d778.
Proof. vm_refl. Qed.
Lemma D_5d778 : decode_any W_5d778 = Some (OpImm32 13 13 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d77c : bv 32 := 0x00d786b3.
Lemma F_5d77c : fetch_word Asan.M.loaded_segments (0x5d7cc : word) = Some W_5d77c.
Proof. vm_refl. Qed.
Lemma D_5d77c : decode_any W_5d77c = Some (Op ALU_ADD 13 15 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d780 : bv 32 := 0xfffc0437.
Lemma F_5d780 : fetch_word Asan.M.loaded_segments (0x5d7d0 : word) = Some W_5d780.
Proof. vm_refl. Qed.
Lemma D_5d780 : decode_any W_5d780 = Some (Lui 8 1048512, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d784 : bv 32 := 0x0086f433.
Lemma F_5d784 : fetch_word Asan.M.loaded_segments (0x5d7d4 : word) = Some W_5d784.
Proof. vm_refl. Qed.
Lemma D_5d784 : decode_any W_5d784 = Some (Op ALU_AND 8 13 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d788 : bv 32 := 0x200006b7.
Lemma F_5d788 : fetch_word Asan.M.loaded_segments (0x5d7d8 : word) = Some W_5d788.
Proof. vm_refl. Qed.
Lemma D_5d788 : decode_any W_5d788 = Some (Lui 13 131072, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d78c : bv 32 := 0x0016869b.
Lemma F_5d78c : fetch_word Asan.M.loaded_segments (0x5d7dc : word) = Some W_5d78c.
Proof. vm_refl. Qed.
Lemma D_5d78c : decode_any W_5d78c = Some (OpImm32 13 13 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d790 : bv 32 := 0x0cd47063.
Lemma F_5d790 : fetch_word Asan.M.loaded_segments (0x5d7e0 : word) = Some W_5d790.
Proof. vm_refl. Qed.
Lemma D_5d790 : decode_any W_5d790 = Some (Branch BC_GEU 8 13 192, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d794 : bv 32 := 0x03854683.
Lemma F_5d794 : fetch_word Asan.M.loaded_segments (0x5d7e4 : word) = Some W_5d794.
Proof. vm_refl. Qed.
Lemma D_5d794 : decode_any W_5d794 = Some (Load SZ1 false 13 10 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d798 : bv 32 := 0x00700793.
Lemma F_5d798 : fetch_word Asan.M.loaded_segments (0x5d7e8 : word) = Some W_5d798.
Proof. vm_refl. Qed.
Lemma D_5d798 : decode_any W_5d798 = Some (OpImm ALU_ADD 15 0 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d79c : bv 32 := 0x01d79793.
Lemma F_5d79c : fetch_word Asan.M.loaded_segments (0x5d7ec : word) = Some W_5d79c.
Proof. vm_refl. Qed.
Lemma D_5d79c : decode_any W_5d79c = Some (ShiftImm ALU_SLL 15 15 29, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d7a0 : bv 32 := 0x00f60633.
Lemma F_5d7a0 : fetch_word Asan.M.loaded_segments (0x5d7f0 : word) = Some W_5d7a0.
Proof. vm_refl. Qed.
Lemma D_5d7a0 : decode_any W_5d7a0 = Some (Op ALU_ADD 12 12 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d7a4 : bv 32 := 0x00c704b3.
Lemma F_5d7a4 : fetch_word Asan.M.loaded_segments (0x5d7f4 : word) = Some W_5d7a4.
Proof. vm_refl. Qed.
Lemma D_5d7a4 : decode_any W_5d7a4 = Some (Op ALU_ADD 9 14 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d7a8 : bv 32 := 0x02068463.
Lemma F_5d7a8 : fetch_word Asan.M.loaded_segments (0x5d7f8 : word) = Some W_5d7a8.
Proof. vm_refl. Qed.
Lemma D_5d7a8 : decode_any W_5d7a8 = Some (Branch BC_EQ 13 0 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d7d0 : bv 32 := 0x00058993.
Lemma F_5d7d0 : fetch_word Asan.M.loaded_segments (0x5d820 : word) = Some W_5d7d0.
Proof. vm_refl. Qed.
Lemma D_5d7d0 : decode_any W_5d7d0 = Some (OpImm ALU_ADD 19 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d7d4 : bv 32 := 0x40e40933.
Lemma F_5d7d4 : fetch_word Asan.M.loaded_segments (0x5d824 : word) = Some W_5d7d4.
Proof. vm_refl. Qed.
Lemma D_5d7d4 : decode_any W_5d7d4 = Some (Op ALU_SUB 18 8 14, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d7d8 : bv 32 := 0xfffbd597.
Lemma F_5d7d8 : fetch_word Asan.M.loaded_segments (0x5d828 : word) = Some W_5d7d8.
Proof. vm_refl. Qed.
Lemma D_5d7d8 : decode_any W_5d7d8 = Some (Auipc 11 1048509, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d7dc : bv 32 := 0x93358693.
Lemma F_5d7dc : fetch_word Asan.M.loaded_segments (0x5d82c : word) = Some W_5d7dc.
Proof. vm_refl. Qed.
Lemma D_5d7dc : decode_any W_5d7dc = Some (OpImm ALU_ADD 13 11 2355, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d7e0 : bv 32 := 0x00048593.
Lemma F_5d7e0 : fetch_word Asan.M.loaded_segments (0x5d830 : word) = Some W_5d7e0.
Proof. vm_refl. Qed.
Lemma D_5d7e0 : decode_any W_5d7e0 = Some (OpImm ALU_ADD 11 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d7e4 : bv 32 := 0x00090613.
Lemma F_5d7e4 : fetch_word Asan.M.loaded_segments (0x5d834 : word) = Some W_5d7e4.
Proof. vm_refl. Qed.
Lemma D_5d7e4 : decode_any W_5d7e4 = Some (OpImm ALU_ADD 12 18 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d7e8 : bv 32 := 0x141400ef.
Lemma F_5d7e8 : fetch_word Asan.M.loaded_segments (0x5d838 : word) = Some W_5d7e8.
Proof. vm_refl. Qed.
Lemma D_5d7e8 : decode_any W_5d7e8 = Some (Jal 1 264512, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d7ec : bv 32 := 0x08050263.
Lemma F_5d7ec : fetch_word Asan.M.loaded_segments (0x5d83c : word) = Some W_5d7ec.
Proof. vm_refl. Qed.
Lemma D_5d7ec : decode_any W_5d7ec = Some (Branch BC_EQ 10 0 132, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d7f0 : bv 32 := 0x00050713.
Lemma F_5d7f0 : fetch_word Asan.M.loaded_segments (0x5d840 : word) = Some W_5d7f0.
Proof. vm_refl. Qed.
Lemma D_5d7f0 : decode_any W_5d7f0 = Some (OpImm ALU_ADD 14 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d7f4 : bv 32 := 0x08a49263.
Lemma F_5d7f4 : fetch_word Asan.M.loaded_segments (0x5d844 : word) = Some W_5d7f4.
Proof. vm_refl. Qed.
Lemma D_5d7f4 : decode_any W_5d7f4 = Some (Branch BC_NE 9 10 132, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d7f8 : bv 32 := 0x0fa00613.
Lemma F_5d7f8 : fetch_word Asan.M.loaded_segments (0x5d848 : word) = Some W_5d7f8.
Proof. vm_refl. Qed.
Lemma D_5d7f8 : decode_any W_5d7f8 = Some (OpImm ALU_ADD 12 0 250, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d7fc : bv 32 := 0x00048513.
Lemma F_5d7fc : fetch_word Asan.M.loaded_segments (0x5d84c : word) = Some W_5d7fc.
Proof. vm_refl. Qed.
Lemma D_5d7fc : decode_any W_5d7fc = Some (OpImm ALU_ADD 10 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d800 : bv 32 := 0x00090593.
Lemma F_5d800 : fetch_word Asan.M.loaded_segments (0x5d850 : word) = Some W_5d800.
Proof. vm_refl. Qed.
Lemma D_5d800 : decode_any W_5d800 = Some (OpImm ALU_ADD 11 18 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d804 : bv 32 := 0x091250ef.
Lemma F_5d804 : fetch_word Asan.M.loaded_segments (0x5d854 : word) = Some W_5d804.
Proof. vm_refl. Qed.
Lemma D_5d804 : decode_any W_5d804 = Some (Jal 1 153744, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d808 : bv 32 := 0x0052d0ef.
Lemma F_5d808 : fetch_word Asan.M.loaded_segments (0x5d858 : word) = Some W_5d808.
Proof. vm_refl. Qed.
Lemma D_5d808 : decode_any W_5d808 = Some (Jal 1 186372, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d80c : bv 32 := 0x05053583.
Lemma F_5d80c : fetch_word Asan.M.loaded_segments (0x5d85c : word) = Some W_5d80c.
Proof. vm_refl. Qed.
Lemma D_5d80c : decode_any W_5d80c = Some (Load SZ8 true 11 10 80, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d810 : bv 32 := 0x04853603.
Lemma F_5d810 : fetch_word Asan.M.loaded_segments (0x5d860 : word) = Some W_5d810.
Proof. vm_refl. Qed.
Lemma D_5d810 : decode_any W_5d810 = Some (Load SZ8 true 12 10 72, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d814 : bv 32 := 0x012585b3.
Lemma F_5d814 : fetch_word Asan.M.loaded_segments (0x5d864 : word) = Some W_5d814.
Proof. vm_refl. Qed.
Lemma D_5d814 : decode_any W_5d814 = Some (Op ALU_ADD 11 11 18, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d818 : bv 32 := 0x00160613.
Lemma F_5d818 : fetch_word Asan.M.loaded_segments (0x5d868 : word) = Some W_5d818.
Proof. vm_refl. Qed.
Lemma D_5d818 : decode_any W_5d818 = Some (OpImm ALU_ADD 12 12 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d81c : bv 32 := 0x04c53423.
Lemma F_5d81c : fetch_word Asan.M.loaded_segments (0x5d86c : word) = Some W_5d81c.
Proof. vm_refl. Qed.
Lemma D_5d81c : decode_any W_5d81c = Some (Store SZ8 10 12 72, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d820 : bv 32 := 0x04b53823.
Lemma F_5d820 : fetch_word Asan.M.loaded_segments (0x5d870 : word) = Some W_5d820.
Proof. vm_refl. Qed.
Lemma D_5d820 : decode_any W_5d820 = Some (Store SZ8 10 11 80, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d824 : bv 32 := 0x00098593.
Lemma F_5d824 : fetch_word Asan.M.loaded_segments (0x5d874 : word) = Some W_5d824.
Proof. vm_refl. Qed.
Lemma D_5d824 : decode_any W_5d824 = Some (OpImm ALU_ADD 11 19 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d828 : bv 32 := 0x0085bc23.
Lemma F_5d828 : fetch_word Asan.M.loaded_segments (0x5d878 : word) = Some W_5d828.
Proof. vm_refl. Qed.
Lemma D_5d828 : decode_any W_5d828 = Some (Store SZ8 11 8 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d82c : bv 32 := 0x00100693.
Lemma F_5d82c : fetch_word Asan.M.loaded_segments (0x5d87c : word) = Some W_5d82c.
Proof. vm_refl. Qed.
Lemma D_5d82c : decode_any W_5d82c = Some (OpImm ALU_ADD 13 0 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d830 : bv 32 := 0x00068513.
Lemma F_5d830 : fetch_word Asan.M.loaded_segments (0x5d880 : word) = Some W_5d830.
Proof. vm_refl. Qed.
Lemma D_5d830 : decode_any W_5d830 = Some (OpImm ALU_ADD 10 13 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d834 : bv 32 := 0x02813083.
Lemma F_5d834 : fetch_word Asan.M.loaded_segments (0x5d884 : word) = Some W_5d834.
Proof. vm_refl. Qed.
Lemma D_5d834 : decode_any W_5d834 = Some (Load SZ8 true 1 2 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d838 : bv 32 := 0x02013403.
Lemma F_5d838 : fetch_word Asan.M.loaded_segments (0x5d888 : word) = Some W_5d838.
Proof. vm_refl. Qed.
Lemma D_5d838 : decode_any W_5d838 = Some (Load SZ8 true 8 2 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d83c : bv 32 := 0x01813483.
Lemma F_5d83c : fetch_word Asan.M.loaded_segments (0x5d88c : word) = Some W_5d83c.
Proof. vm_refl. Qed.
Lemma D_5d83c : decode_any W_5d83c = Some (Load SZ8 true 9 2 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d840 : bv 32 := 0x01013903.
Lemma F_5d840 : fetch_word Asan.M.loaded_segments (0x5d890 : word) = Some W_5d840.
Proof. vm_refl. Qed.
Lemma D_5d840 : decode_any W_5d840 = Some (Load SZ8 true 18 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d844 : bv 32 := 0x00813983.
Lemma F_5d844 : fetch_word Asan.M.loaded_segments (0x5d894 : word) = Some W_5d844.
Proof. vm_refl. Qed.
Lemma D_5d844 : decode_any W_5d844 = Some (Load SZ8 true 19 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d848 : bv 32 := 0x03010113.
Lemma F_5d848 : fetch_word Asan.M.loaded_segments (0x5d898 : word) = Some W_5d848.
Proof. vm_refl. Qed.
Lemma D_5d848 : decode_any W_5d848 = Some (OpImm ALU_ADD 2 2 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d84c : bv 32 := 0x00008067.
Lemma F_5d84c : fetch_word Asan.M.loaded_segments (0x5d89c : word) = Some W_5d84c.
Proof. vm_refl. Qed.
Lemma D_5d84c : decode_any W_5d84c = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d8cc : bv 32 := 0xfb010113.
Lemma F_5d8cc : fetch_word Asan.M.loaded_segments (0x5d91c : word) = Some W_5d8cc.
Proof. vm_refl. Qed.
Lemma D_5d8cc : decode_any W_5d8cc = Some (OpImm ALU_ADD 2 2 4016, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d8d0 : bv 32 := 0x04113423.
Lemma F_5d8d0 : fetch_word Asan.M.loaded_segments (0x5d920 : word) = Some W_5d8d0.
Proof. vm_refl. Qed.
Lemma D_5d8d0 : decode_any W_5d8d0 = Some (Store SZ8 2 1 72, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d8d4 : bv 32 := 0x04813023.
Lemma F_5d8d4 : fetch_word Asan.M.loaded_segments (0x5d924 : word) = Some W_5d8d4.
Proof. vm_refl. Qed.
Lemma D_5d8d4 : decode_any W_5d8d4 = Some (Store SZ8 2 8 64, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d8d8 : bv 32 := 0x02913c23.
Lemma F_5d8d8 : fetch_word Asan.M.loaded_segments (0x5d928 : word) = Some W_5d8d8.
Proof. vm_refl. Qed.
Lemma D_5d8d8 : decode_any W_5d8d8 = Some (Store SZ8 2 9 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d8dc : bv 32 := 0x03213823.
Lemma F_5d8dc : fetch_word Asan.M.loaded_segments (0x5d92c : word) = Some W_5d8dc.
Proof. vm_refl. Qed.
Lemma D_5d8dc : decode_any W_5d8dc = Some (Store SZ8 2 18 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d8e0 : bv 32 := 0x03313423.
Lemma F_5d8e0 : fetch_word Asan.M.loaded_segments (0x5d930 : word) = Some W_5d8e0.
Proof. vm_refl. Qed.
Lemma D_5d8e0 : decode_any W_5d8e0 = Some (Store SZ8 2 19 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d8e4 : bv 32 := 0x03413023.
Lemma F_5d8e4 : fetch_word Asan.M.loaded_segments (0x5d934 : word) = Some W_5d8e4.
Proof. vm_refl. Qed.
Lemma D_5d8e4 : decode_any W_5d8e4 = Some (Store SZ8 2 20 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d8e8 : bv 32 := 0x01513c23.
Lemma F_5d8e8 : fetch_word Asan.M.loaded_segments (0x5d938 : word) = Some W_5d8e8.
Proof. vm_refl. Qed.
Lemma D_5d8e8 : decode_any W_5d8e8 = Some (Store SZ8 2 21 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d8ec : bv 32 := 0x01613823.
Lemma F_5d8ec : fetch_word Asan.M.loaded_segments (0x5d93c : word) = Some W_5d8ec.
Proof. vm_refl. Qed.
Lemma D_5d8ec : decode_any W_5d8ec = Some (Store SZ8 2 22 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d8f0 : bv 32 := 0x01713423.
Lemma F_5d8f0 : fetch_word Asan.M.loaded_segments (0x5d940 : word) = Some W_5d8f0.
Proof. vm_refl. Qed.
Lemma D_5d8f0 : decode_any W_5d8f0 = Some (Store SZ8 2 23 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d8f4 : bv 32 := 0x00068a93.
Lemma F_5d8f4 : fetch_word Asan.M.loaded_segments (0x5d944 : word) = Some W_5d8f4.
Proof. vm_refl. Qed.
Lemma D_5d8f4 : decode_any W_5d8f4 = Some (OpImm ALU_ADD 21 13 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d8f8 : bv 32 := 0x00060493.
Lemma F_5d8f8 : fetch_word Asan.M.loaded_segments (0x5d948 : word) = Some W_5d8f8.
Proof. vm_refl. Qed.
Lemma D_5d8f8 : decode_any W_5d8f8 = Some (OpImm ALU_ADD 9 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d8fc : bv 32 := 0x00058413.
Lemma F_5d8fc : fetch_word Asan.M.loaded_segments (0x5d94c : word) = Some W_5d8fc.
Proof. vm_refl. Qed.
Lemma D_5d8fc : decode_any W_5d8fc = Some (OpImm ALU_ADD 8 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d900 : bv 32 := 0x00050993.
Lemma F_5d900 : fetch_word Asan.M.loaded_segments (0x5d950 : word) = Some W_5d900.
Proof. vm_refl. Qed.
Lemma D_5d900 : decode_any W_5d900 = Some (OpImm ALU_ADD 19 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d904 : bv 32 := 0x03053b03.
Lemma F_5d904 : fetch_word Asan.M.loaded_segments (0x5d954 : word) = Some W_5d904.
Proof. vm_refl. Qed.
Lemma D_5d904 : decode_any W_5d904 = Some (Load SZ8 true 22 10 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d908 : bv 32 := 0x01f00513.
Lemma F_5d908 : fetch_word Asan.M.loaded_segments (0x5d958 : word) = Some W_5d908.
Proof. vm_refl. Qed.
Lemma D_5d908 : decode_any W_5d908 = Some (OpImm ALU_ADD 10 0 31, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d90c : bv 32 := 0x00761593.
Lemma F_5d90c : fetch_word Asan.M.loaded_segments (0x5d95c : word) = Some W_5d90c.
Proof. vm_refl. Qed.
Lemma D_5d90c : decode_any W_5d90c = Some (ShiftImm ALU_SLL 11 12 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d910 : bv 32 := 0x18a60863.
Lemma F_5d910 : fetch_word Asan.M.loaded_segments (0x5d960 : word) = Some W_5d910.
Proof. vm_refl. Qed.
Lemma D_5d910 : decode_any W_5d910 = Some (Branch BC_EQ 12 10 400, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d914 : bv 32 := 0x01000513.
Lemma F_5d914 : fetch_word Asan.M.loaded_segments (0x5d964 : word) = Some W_5d914.
Proof. vm_refl. Qed.
Lemma D_5d914 : decode_any W_5d914 = Some (OpImm ALU_ADD 10 0 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d918 : bv 32 := 0x00956663.
Lemma F_5d918 : fetch_word Asan.M.loaded_segments (0x5d968 : word) = Some W_5d918.
Proof. vm_refl. Qed.
Lemma D_5d918 : decode_any W_5d918 = Some (Branch BC_LTU 10 9 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d91c : bv 32 := 0x00549913.
Lemma F_5d91c : fetch_word Asan.M.loaded_segments (0x5d96c : word) = Some W_5d91c.
Proof. vm_refl. Qed.
Lemma D_5d91c : decode_any W_5d91c = Some (ShiftImm ALU_SLL 18 9 5, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d920 : bv 32 := 0x0280006f.
Lemma F_5d920 : fetch_word Asan.M.loaded_segments (0x5d970 : word) = Some W_5d920.
Proof. vm_refl. Qed.
Lemma D_5d920 : decode_any W_5d920 = Some (Jal 0 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d924 : bv 32 := 0xff048513.
Lemma F_5d924 : fetch_word Asan.M.loaded_segments (0x5d974 : word) = Some W_5d924.
Proof. vm_refl. Qed.
Lemma D_5d924 : decode_any W_5d924 = Some (OpImm ALU_ADD 10 9 4080, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d928 : bv 32 := 0x20000613.
Lemma F_5d928 : fetch_word Asan.M.loaded_segments (0x5d978 : word) = Some W_5d928.
Proof. vm_refl. Qed.
Lemma D_5d928 : decode_any W_5d928 = Some (OpImm ALU_ADD 12 0 512, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d92c : bv 32 := 0x03f49693.
Lemma F_5d92c : fetch_word Asan.M.loaded_segments (0x5d97c : word) = Some W_5d92c.
Proof. vm_refl. Qed.
Lemma D_5d92c : decode_any W_5d92c = Some (ShiftImm ALU_SLL 13 9 63, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d930 : bv 32 := 0x00155513.
Lemma F_5d930 : fetch_word Asan.M.loaded_segments (0x5d980 : word) = Some W_5d930.
Proof. vm_refl. Qed.
Lemma D_5d930 : decode_any W_5d930 = Some (ShiftImm ALU_SRL 10 10 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d934 : bv 32 := 0x00a61933.
Lemma F_5d934 : fetch_word Asan.M.loaded_segments (0x5d984 : word) = Some W_5d934.
Proof. vm_refl. Qed.
Lemma D_5d934 : decode_any W_5d934 = Some (Op ALU_SLL 18 12 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d938 : bv 32 := 0x00195513.
Lemma F_5d938 : fetch_word Asan.M.loaded_segments (0x5d988 : word) = Some W_5d938.
Proof. vm_refl. Qed.
Lemma D_5d938 : decode_any W_5d938 = Some (ShiftImm ALU_SRL 10 18 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d93c : bv 32 := 0x43f6d693.
Lemma F_5d93c : fetch_word Asan.M.loaded_segments (0x5d98c : word) = Some W_5d93c.
Proof. vm_refl. Qed.
Lemma D_5d93c : decode_any W_5d93c = Some (ShiftImm ALU_SRA 13 13 63, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d940 : bv 32 := 0x00a6f533.
Lemma F_5d940 : fetch_word Asan.M.loaded_segments (0x5d990 : word) = Some W_5d940.
Proof. vm_refl. Qed.
Lemma D_5d940 : decode_any W_5d940 = Some (Op ALU_AND 10 13 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d944 : bv 32 := 0x01250933.
Lemma F_5d944 : fetch_word Asan.M.loaded_segments (0x5d994 : word) = Some W_5d944.
Proof. vm_refl. Qed.
Lemma D_5d944 : decode_any W_5d944 = Some (Op ALU_ADD 18 10 18, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d948 : bv 32 := 0x00103517.
Lemma F_5d948 : fetch_word Asan.M.loaded_segments (0x5d998 : word) = Some W_5d948.
Proof. vm_refl. Qed.
Lemma D_5d948 : decode_any W_5d948 = Some (Auipc 10 259, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d94c : bv 32 := 0x26053a03.
Lemma F_5d94c : fetch_word Asan.M.loaded_segments (0x5d99c : word) = Some W_5d94c.
Proof. vm_refl. Qed.
Lemma D_5d94c : decode_any W_5d94c = Some (Load SZ8 true 20 10 608, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d950 : bv 32 := 0x000a3503.
Lemma F_5d950 : fetch_word Asan.M.loaded_segments (0x5d9a0 : word) = Some W_5d950.
Proof. vm_refl. Qed.
Lemma D_5d950 : decode_any W_5d950 = Some (Load SZ8 true 10 20 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d954 : bv 32 := 0x00bb0b33.
Lemma F_5d954 : fetch_word Asan.M.loaded_segments (0x5d9a4 : word) = Some W_5d954.
Proof. vm_refl. Qed.
Lemma D_5d954 : decode_any W_5d954 = Some (Op ALU_ADD 22 22 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d958 : bv 32 := 0x00050a63.
Lemma F_5d958 : fetch_word Asan.M.loaded_segments (0x5d9a8 : word) = Some W_5d958.
Proof. vm_refl. Qed.
Lemma D_5d958 : decode_any W_5d958 = Some (Branch BC_EQ 10 0 20, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d95c : bv 32 := 0x010b3a03.
Lemma F_5d95c : fetch_word Asan.M.loaded_segments (0x5d9ac : word) = Some W_5d95c.
Proof. vm_refl. Qed.
Lemma D_5d95c : decode_any W_5d95c = Some (Load SZ8 true 20 22 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d960 : bv 32 := 0x032a05b3.
Lemma F_5d960 : fetch_word Asan.M.loaded_segments (0x5d9b0 : word) = Some W_5d960.
Proof. vm_refl. Qed.
Lemma D_5d960 : decode_any W_5d960 = Some (Mul M_MUL 11 20 18, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d964 : bv 32 := 0x00a5fe63.
Lemma F_5d964 : fetch_word Asan.M.loaded_segments (0x5d9b4 : word) = Some W_5d964.
Proof. vm_refl. Qed.
Lemma D_5d964 : decode_any W_5d964 = Some (Branch BC_GEU 11 10 28, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d968 : bv 32 := 0x10c0006f.
Lemma F_5d968 : fetch_word Asan.M.loaded_segments (0x5d9b8 : word) = Some W_5d968.
Proof. vm_refl. Qed.
Lemma D_5d968 : decode_any W_5d968 = Some (Jal 0 268, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d980 : bv 32 := 0x050b3583.
Lemma F_5d980 : fetch_word Asan.M.loaded_segments (0x5d9d0 : word) = Some W_5d980.
Proof. vm_refl. Qed.
Lemma D_5d980 : decode_any W_5d980 = Some (Load SZ8 true 11 22 80, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d984 : bv 32 := 0x058b3603.
Lemma F_5d984 : fetch_word Asan.M.loaded_segments (0x5d9d4 : word) = Some W_5d984.
Proof. vm_refl. Qed.
Lemma D_5d984 : decode_any W_5d984 = Some (Load SZ8 true 12 22 88, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d988 : bv 32 := 0x40c585b3.
Lemma F_5d988 : fetch_word Asan.M.loaded_segments (0x5d9d8 : word) = Some W_5d988.
Proof. vm_refl. Qed.
Lemma D_5d988 : decode_any W_5d988 = Some (Op ALU_SUB 11 11 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d98c : bv 32 := 0x032585b3.
Lemma F_5d98c : fetch_word Asan.M.loaded_segments (0x5d9dc : word) = Some W_5d98c.
Proof. vm_refl. Qed.
Lemma D_5d98c : decode_any W_5d98c = Some (Mul M_MUL 11 11 18, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d990 : bv 32 := 0x0ea5e263.
Lemma F_5d990 : fetch_word Asan.M.loaded_segments (0x5d9e0 : word) = Some W_5d990.
Proof. vm_refl. Qed.
Lemma D_5d990 : decode_any W_5d990 = Some (Branch BC_LTU 11 10 228, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d994 : bv 32 := 0x020a9a63.
Lemma F_5d994 : fetch_word Asan.M.loaded_segments (0x5d9e4 : word) = Some W_5d994.
Proof. vm_refl. Qed.
Lemma D_5d994 : decode_any W_5d994 = Some (Branch BC_NE 21 0 52, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d998 : bv 32 := 0x0289a583.
Lemma F_5d998 : fetch_word Asan.M.loaded_segments (0x5d9e8 : word) = Some W_5d998.
Proof. vm_refl. Qed.
Lemma D_5d998 : decode_any W_5d998 = Some (Load SZ4 true 11 19 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5d99c : bv 32 := 0x0c05cc63.
Lemma F_5d99c : fetch_word Asan.M.loaded_segments (0x5d9ec : word) = Some W_5d99c.
Proof. vm_refl. Qed.
Lemma D_5d99c : decode_any W_5d99c = Some (Branch BC_LT 11 0 216, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5da74 : bv 32 := 0x04813083.
Lemma F_5da74 : fetch_word Asan.M.loaded_segments (0x5dac4 : word) = Some W_5da74.
Proof. vm_refl. Qed.
Lemma D_5da74 : decode_any W_5da74 = Some (Load SZ8 true 1 2 72, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5da78 : bv 32 := 0x04013403.
Lemma F_5da78 : fetch_word Asan.M.loaded_segments (0x5dac8 : word) = Some W_5da78.
Proof. vm_refl. Qed.
Lemma D_5da78 : decode_any W_5da78 = Some (Load SZ8 true 8 2 64, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5da7c : bv 32 := 0x03813483.
Lemma F_5da7c : fetch_word Asan.M.loaded_segments (0x5dacc : word) = Some W_5da7c.
Proof. vm_refl. Qed.
Lemma D_5da7c : decode_any W_5da7c = Some (Load SZ8 true 9 2 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5da80 : bv 32 := 0x03013903.
Lemma F_5da80 : fetch_word Asan.M.loaded_segments (0x5dad0 : word) = Some W_5da80.
Proof. vm_refl. Qed.
Lemma D_5da80 : decode_any W_5da80 = Some (Load SZ8 true 18 2 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5da84 : bv 32 := 0x02813983.
Lemma F_5da84 : fetch_word Asan.M.loaded_segments (0x5dad4 : word) = Some W_5da84.
Proof. vm_refl. Qed.
Lemma D_5da84 : decode_any W_5da84 = Some (Load SZ8 true 19 2 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5da88 : bv 32 := 0x02013a03.
Lemma F_5da88 : fetch_word Asan.M.loaded_segments (0x5dad8 : word) = Some W_5da88.
Proof. vm_refl. Qed.
Lemma D_5da88 : decode_any W_5da88 = Some (Load SZ8 true 20 2 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5da8c : bv 32 := 0x01813a83.
Lemma F_5da8c : fetch_word Asan.M.loaded_segments (0x5dadc : word) = Some W_5da8c.
Proof. vm_refl. Qed.
Lemma D_5da8c : decode_any W_5da8c = Some (Load SZ8 true 21 2 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5da90 : bv 32 := 0x01013b03.
Lemma F_5da90 : fetch_word Asan.M.loaded_segments (0x5dae0 : word) = Some W_5da90.
Proof. vm_refl. Qed.
Lemma D_5da90 : decode_any W_5da90 = Some (Load SZ8 true 22 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5da94 : bv 32 := 0x00813b83.
Lemma F_5da94 : fetch_word Asan.M.loaded_segments (0x5dae4 : word) = Some W_5da94.
Proof. vm_refl. Qed.
Lemma D_5da94 : decode_any W_5da94 = Some (Load SZ8 true 23 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5da98 : bv 32 := 0x05010113.
Lemma F_5da98 : fetch_word Asan.M.loaded_segments (0x5dae8 : word) = Some W_5da98.
Proof. vm_refl. Qed.
Lemma D_5da98 : decode_any W_5da98 = Some (OpImm ALU_ADD 2 2 80, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5da9c : bv 32 := 0x00008067.
Lemma F_5da9c : fetch_word Asan.M.loaded_segments (0x5daec : word) = Some W_5da9c.
Proof. vm_refl. Qed.
Lemma D_5da9c : decode_any W_5da9c = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

