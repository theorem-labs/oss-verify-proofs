(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)

From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.coturn.FuzzStunClient.images Require Import Asan.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.

(* [comment removed for export] *)
Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

(* [comment removed for export] *)
Definition W_a40b0 : bv 32 := 0x0ff5f593.
Lemma F_a40b0 : fetch_word Asan.M.loaded_segments (0xa40b0 : word) = Some W_a40b0.
Proof. vm_refl. Qed.
Lemma D_a40b0 : decode_any W_a40b0 = Some (OpImm ALU_AND 11 11 255, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a40b4 : bv 32 := 0x00757693.
Lemma F_a40b4 : fetch_word Asan.M.loaded_segments (0xa40b4 : word) = Some W_a40b4.
Proof. vm_refl. Qed.
Lemma D_a40b4 : decode_any W_a40b4 = Some (OpImm ALU_AND 13 10 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a40b8 : bv 32 := 0x00c03733.
Lemma F_a40b8 : fetch_word Asan.M.loaded_segments (0xa40b8 : word) = Some W_a40b8.
Proof. vm_refl. Qed.
Lemma D_a40b8 : decode_any W_a40b8 = Some (Op ALU_SLTU 14 0 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a40bc : bv 32 := 0x02068c63.
Lemma F_a40bc : fetch_word Asan.M.loaded_segments (0xa40bc : word) = Some W_a40bc.
Proof. vm_refl. Qed.
Lemma D_a40bc : decode_any W_a40bc = Some (Branch BC_EQ 13 0 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a40c0 : bv 32 := 0x02060a63.
Lemma F_a40c0 : fetch_word Asan.M.loaded_segments (0xa40c0 : word) = Some W_a40c0.
Proof. vm_refl. Qed.
Lemma D_a40c0 : decode_any W_a40c0 = Some (Branch BC_EQ 12 0 52, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a40c4 : bv 32 := 0x00150793.
Lemma F_a40c4 : fetch_word Asan.M.loaded_segments (0xa40c4 : word) = Some W_a40c4.
Proof. vm_refl. Qed.
Lemma D_a40c4 : decode_any W_a40c4 = Some (OpImm ALU_ADD 15 10 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a40c8 : bv 32 := 0x00100813.
Lemma F_a40c8 : fetch_word Asan.M.loaded_segments (0xa40c8 : word) = Some W_a40c8.
Proof. vm_refl. Qed.
Lemma D_a40c8 : decode_any W_a40c8 = Some (OpImm ALU_ADD 16 0 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a40cc : bv 32 := 0x00054703.
Lemma F_a40cc : fetch_word Asan.M.loaded_segments (0xa40cc : word) = Some W_a40cc.
Proof. vm_refl. Qed.
Lemma D_a40cc : decode_any W_a40cc = Some (Load SZ1 false 14 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a40d0 : bv 32 := 0x00060693.
Lemma F_a40d0 : fetch_word Asan.M.loaded_segments (0xa40d0 : word) = Some W_a40d0.
Proof. vm_refl. Qed.
Lemma D_a40d0 : decode_any W_a40d0 = Some (OpImm ALU_ADD 13 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a40d4 : bv 32 := 0x06b70e63.
Lemma F_a40d4 : fetch_word Asan.M.loaded_segments (0xa40d4 : word) = Some W_a40d4.
Proof. vm_refl. Qed.
Lemma D_a40d4 : decode_any W_a40d4 = Some (Branch BC_EQ 14 11 124, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a40d8 : bv 32 := 0x00150513.
Lemma F_a40d8 : fetch_word Asan.M.loaded_segments (0xa40d8 : word) = Some W_a40d8.
Proof. vm_refl. Qed.
Lemma D_a40d8 : decode_any W_a40d8 = Some (OpImm ALU_ADD 10 10 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a40dc : bv 32 := 0xfff68613.
Lemma F_a40dc : fetch_word Asan.M.loaded_segments (0xa40dc : word) = Some W_a40dc.
Proof. vm_refl. Qed.
Lemma D_a40dc : decode_any W_a40dc = Some (OpImm ALU_ADD 12 13 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a40e0 : bv 32 := 0x0077f893.
Lemma F_a40e0 : fetch_word Asan.M.loaded_segments (0xa40e0 : word) = Some W_a40e0.
Proof. vm_refl. Qed.
Lemma D_a40e0 : decode_any W_a40e0 = Some (OpImm ALU_AND 17 15 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a40e4 : bv 32 := 0x00c03733.
Lemma F_a40e4 : fetch_word Asan.M.loaded_segments (0xa40e4 : word) = Some W_a40e4.
Proof. vm_refl. Qed.
Lemma D_a40e4 : decode_any W_a40e4 = Some (Op ALU_SLTU 14 0 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a40e8 : bv 32 := 0x00088663.
Lemma F_a40e8 : fetch_word Asan.M.loaded_segments (0xa40e8 : word) = Some W_a40e8.
Proof. vm_refl. Qed.
Lemma D_a40e8 : decode_any W_a40e8 = Some (Branch BC_EQ 17 0 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a40ec : bv 32 := 0x00178793.
Lemma F_a40ec : fetch_word Asan.M.loaded_segments (0xa40ec : word) = Some W_a40ec.
Proof. vm_refl. Qed.
Lemma D_a40ec : decode_any W_a40ec = Some (OpImm ALU_ADD 15 15 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a40f0 : bv 32 := 0xfd069ee3.
Lemma F_a40f0 : fetch_word Asan.M.loaded_segments (0xa40f0 : word) = Some W_a40f0.
Proof. vm_refl. Qed.
Lemma D_a40f0 : decode_any W_a40f0 = Some (Branch BC_NE 13 16 8156, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a40f4 : bv 32 := 0x06070863.
Lemma F_a40f4 : fetch_word Asan.M.loaded_segments (0xa40f4 : word) = Some W_a40f4.
Proof. vm_refl. Qed.
Lemma D_a40f4 : decode_any W_a40f4 = Some (Branch BC_EQ 14 0 112, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a40f8 : bv 32 := 0x00054683.
Lemma F_a40f8 : fetch_word Asan.M.loaded_segments (0xa40f8 : word) = Some W_a40f8.
Proof. vm_refl. Qed.
Lemma D_a40f8 : decode_any W_a40f8 = Some (Load SZ1 false 13 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a40fc : bv 32 := 0x04b68663.
Lemma F_a40fc : fetch_word Asan.M.loaded_segments (0xa40fc : word) = Some W_a40fc.
Proof. vm_refl. Qed.
Lemma D_a40fc : decode_any W_a40fc = Some (Branch BC_EQ 13 11 76, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a4100 : bv 32 := 0x00800693.
Lemma F_a4100 : fetch_word Asan.M.loaded_segments (0xa4100 : word) = Some W_a4100.
Proof. vm_refl. Qed.
Lemma D_a4100 : decode_any W_a4100 = Some (OpImm ALU_ADD 13 0 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a4104 : bv 32 := 0x04d66263.
Lemma F_a4104 : fetch_word Asan.M.loaded_segments (0xa4104 : word) = Some W_a4104.
Proof. vm_refl. Qed.
Lemma D_a4104 : decode_any W_a4104 = Some (Branch BC_LTU 12 13 68, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a4108 : bv 32 := 0xfff6c697.
Lemma F_a4108 : fetch_word Asan.M.loaded_segments (0xa4108 : word) = Some W_a4108.
Proof. vm_refl. Qed.
Lemma D_a4108 : decode_any W_a4108 = Some (Auipc 13 1048428, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a410c : bv 32 := 0x2786b683.
Lemma F_a410c : fetch_word Asan.M.loaded_segments (0xa410c : word) = Some W_a410c.
Proof. vm_refl. Qed.
Lemma D_a410c : decode_any W_a410c = Some (Load SZ8 true 13 13 632, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a4110 : bv 32 := 0xfff6c717.
Lemma F_a4110 : fetch_word Asan.M.loaded_segments (0xa4110 : word) = Some W_a4110.
Proof. vm_refl. Qed.
Lemma D_a4110 : decode_any W_a4110 = Some (Auipc 14 1048428, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a4114 : bv 32 := 0x25073703.
Lemma F_a4114 : fetch_word Asan.M.loaded_segments (0xa4114 : word) = Some W_a4114.
Proof. vm_refl. Qed.
Lemma D_a4114 : decode_any W_a4114 = Some (Load SZ8 true 14 14 592, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a4118 : bv 32 := 0x00168793.
Lemma F_a4118 : fetch_word Asan.M.loaded_segments (0xa4118 : word) = Some W_a4118.
Proof. vm_refl. Qed.
Lemma D_a4118 : decode_any W_a4118 = Some (OpImm ALU_ADD 15 13 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a411c : bv 32 := 0x02f587b3.
Lemma F_a411c : fetch_word Asan.M.loaded_segments (0xa411c : word) = Some W_a411c.
Proof. vm_refl. Qed.
Lemma D_a411c : decode_any W_a411c = Some (Mul M_MUL 15 11 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a4120 : bv 32 := 0x00700813.
Lemma F_a4120 : fetch_word Asan.M.loaded_segments (0xa4120 : word) = Some W_a4120.
Proof. vm_refl. Qed.
Lemma D_a4120 : decode_any W_a4120 = Some (OpImm ALU_ADD 16 0 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a4124 : bv 32 := 0x00053883.
Lemma F_a4124 : fetch_word Asan.M.loaded_segments (0xa4124 : word) = Some W_a4124.
Proof. vm_refl. Qed.
Lemma D_a4124 : decode_any W_a4124 = Some (Load SZ8 true 17 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a4128 : bv 32 := 0x00f8c8b3.
Lemma F_a4128 : fetch_word Asan.M.loaded_segments (0xa4128 : word) = Some W_a4128.
Proof. vm_refl. Qed.
Lemma D_a4128 : decode_any W_a4128 = Some (Op ALU_XOR 17 17 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a412c : bv 32 := 0x411682b3.
Lemma F_a412c : fetch_word Asan.M.loaded_segments (0xa412c : word) = Some W_a412c.
Proof. vm_refl. Qed.
Lemma D_a412c : decode_any W_a412c = Some (Op ALU_SUB 5 13 17, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a4130 : bv 32 := 0x0112e8b3.
Lemma F_a4130 : fetch_word Asan.M.loaded_segments (0xa4130 : word) = Some W_a4130.
Proof. vm_refl. Qed.
Lemma D_a4130 : decode_any W_a4130 = Some (Op ALU_OR 17 5 17, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a4134 : bv 32 := 0x00e8f8b3.
Lemma F_a4134 : fetch_word Asan.M.loaded_segments (0xa4134 : word) = Some W_a4134.
Proof. vm_refl. Qed.
Lemma D_a4134 : decode_any W_a4134 = Some (Op ALU_AND 17 17 14, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a4138 : bv 32 := 0x02e89a63.
Lemma F_a4138 : fetch_word Asan.M.loaded_segments (0xa4138 : word) = Some W_a4138.
Proof. vm_refl. Qed.
Lemma D_a4138 : decode_any W_a4138 = Some (Branch BC_NE 17 14 52, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a413c : bv 32 := 0xff860613.
Lemma F_a413c : fetch_word Asan.M.loaded_segments (0xa413c : word) = Some W_a413c.
Proof. vm_refl. Qed.
Lemma D_a413c : decode_any W_a413c = Some (OpImm ALU_ADD 12 12 4088, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a4140 : bv 32 := 0x00850513.
Lemma F_a4140 : fetch_word Asan.M.loaded_segments (0xa4140 : word) = Some W_a4140.
Proof. vm_refl. Qed.
Lemma D_a4140 : decode_any W_a4140 = Some (OpImm ALU_ADD 10 10 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a4144 : bv 32 := 0xfec860e3.
Lemma F_a4144 : fetch_word Asan.M.loaded_segments (0xa4144 : word) = Some W_a4144.
Proof. vm_refl. Qed.
Lemma D_a4144 : decode_any W_a4144 = Some (Branch BC_LTU 16 12 8160, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a4148 : bv 32 := 0x00060693.
Lemma F_a4148 : fetch_word Asan.M.loaded_segments (0xa4148 : word) = Some W_a4148.
Proof. vm_refl. Qed.
Lemma D_a4148 : decode_any W_a4148 = Some (OpImm ALU_ADD 13 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a414c : bv 32 := 0x00060c63.
Lemma F_a414c : fetch_word Asan.M.loaded_segments (0xa414c : word) = Some W_a414c.
Proof. vm_refl. Qed.
Lemma D_a414c : decode_any W_a414c = Some (Branch BC_EQ 12 0 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a4150 : bv 32 := 0x00054603.
Lemma F_a4150 : fetch_word Asan.M.loaded_segments (0xa4150 : word) = Some W_a4150.
Proof. vm_refl. Qed.
Lemma D_a4150 : decode_any W_a4150 = Some (Load SZ1 false 12 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a4154 : bv 32 := 0x00b60a63.
Lemma F_a4154 : fetch_word Asan.M.loaded_segments (0xa4154 : word) = Some W_a4154.
Proof. vm_refl. Qed.
Lemma D_a4154 : decode_any W_a4154 = Some (Branch BC_EQ 12 11 20, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a4158 : bv 32 := 0xfff68693.
Lemma F_a4158 : fetch_word Asan.M.loaded_segments (0xa4158 : word) = Some W_a4158.
Proof. vm_refl. Qed.
Lemma D_a4158 : decode_any W_a4158 = Some (OpImm ALU_ADD 13 13 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a415c : bv 32 := 0x00150513.
Lemma F_a415c : fetch_word Asan.M.loaded_segments (0xa415c : word) = Some W_a415c.
Proof. vm_refl. Qed.
Lemma D_a415c : decode_any W_a415c = Some (OpImm ALU_ADD 10 10 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a4160 : bv 32 := 0xfe0698e3.
Lemma F_a4160 : fetch_word Asan.M.loaded_segments (0xa4160 : word) = Some W_a4160.
Proof. vm_refl. Qed.
Lemma D_a4160 : decode_any W_a4160 = Some (Branch BC_NE 13 0 8176, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a4164 : bv 32 := 0x00000513.
Lemma F_a4164 : fetch_word Asan.M.loaded_segments (0xa4164 : word) = Some W_a4164.
Proof. vm_refl. Qed.
Lemma D_a4164 : decode_any W_a4164 = Some (OpImm ALU_ADD 10 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a4168 : bv 32 := 0x00008067.
Lemma F_a4168 : fetch_word Asan.M.loaded_segments (0xa4168 : word) = Some W_a4168.
Proof. vm_refl. Qed.
Lemma D_a4168 : decode_any W_a4168 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a416c : bv 32 := 0x00060693.
Lemma F_a416c : fetch_word Asan.M.loaded_segments (0xa416c : word) = Some W_a416c.
Proof. vm_refl. Qed.
Lemma D_a416c : decode_any W_a416c = Some (OpImm ALU_ADD 13 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a4170 : bv 32 := 0x00054603.
Lemma F_a4170 : fetch_word Asan.M.loaded_segments (0xa4170 : word) = Some W_a4170.
Proof. vm_refl. Qed.
Lemma D_a4170 : decode_any W_a4170 = Some (Load SZ1 false 12 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a4174 : bv 32 := 0xfeb612e3.
Lemma F_a4174 : fetch_word Asan.M.loaded_segments (0xa4174 : word) = Some W_a4174.
Proof. vm_refl. Qed.
Lemma D_a4174 : decode_any W_a4174 = Some (Branch BC_NE 12 11 8164, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a4178 : bv 32 := 0xff1ff06f.
Lemma F_a4178 : fetch_word Asan.M.loaded_segments (0xa4178 : word) = Some W_a4178.
Proof. vm_refl. Qed.
Lemma D_a4178 : decode_any W_a4178 = Some (Jal 0 2097136, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a4a38 : bv 32 := 0xfe010113.
Lemma F_a4a38 : fetch_word Asan.M.loaded_segments (0xa4a38 : word) = Some W_a4a38.
Proof. vm_refl. Qed.
Lemma D_a4a38 : decode_any W_a4a38 = Some (OpImm ALU_ADD 2 2 4064, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a4a3c : bv 32 := 0x00113c23.
Lemma F_a4a3c : fetch_word Asan.M.loaded_segments (0xa4a3c : word) = Some W_a4a3c.
Proof. vm_refl. Qed.
Lemma D_a4a3c : decode_any W_a4a3c = Some (Store SZ8 2 1 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a4a40 : bv 32 := 0x00813823.
Lemma F_a4a40 : fetch_word Asan.M.loaded_segments (0xa4a40 : word) = Some W_a4a40.
Proof. vm_refl. Qed.
Lemma D_a4a40 : decode_any W_a4a40 = Some (Store SZ8 2 8 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a4a44 : bv 32 := 0x00913423.
Lemma F_a4a44 : fetch_word Asan.M.loaded_segments (0xa4a44 : word) = Some W_a4a44.
Proof. vm_refl. Qed.
Lemma D_a4a44 : decode_any W_a4a44 = Some (Store SZ8 2 9 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a4a48 : bv 32 := 0x00058413.
Lemma F_a4a48 : fetch_word Asan.M.loaded_segments (0xa4a48 : word) = Some W_a4a48.
Proof. vm_refl. Qed.
Lemma D_a4a48 : decode_any W_a4a48 = Some (OpImm ALU_ADD 8 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a4a4c : bv 32 := 0x00050493.
Lemma F_a4a4c : fetch_word Asan.M.loaded_segments (0xa4a4c : word) = Some W_a4a4c.
Proof. vm_refl. Qed.
Lemma D_a4a4c : decode_any W_a4a4c = Some (OpImm ALU_ADD 9 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a4a50 : bv 32 := 0x00000593.
Lemma F_a4a50 : fetch_word Asan.M.loaded_segments (0xa4a50 : word) = Some W_a4a50.
Proof. vm_refl. Qed.
Lemma D_a4a50 : decode_any W_a4a50 = Some (OpImm ALU_ADD 11 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a4a54 : bv 32 := 0x00040613.
Lemma F_a4a54 : fetch_word Asan.M.loaded_segments (0xa4a54 : word) = Some W_a4a54.
Proof. vm_refl. Qed.
Lemma D_a4a54 : decode_any W_a4a54 = Some (OpImm ALU_ADD 12 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a4a58 : bv 32 := 0xff09f0ef.
Lemma F_a4a58 : fetch_word Asan.M.loaded_segments (0xa4a58 : word) = Some W_a4a58.
Proof. vm_refl. Qed.
Lemma D_a4a58 : decode_any W_a4a58 = Some (Jal 1 1701872, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a4a5c : bv 32 := 0x00050463.
Lemma F_a4a5c : fetch_word Asan.M.loaded_segments (0xa4a5c : word) = Some W_a4a5c.
Proof. vm_refl. Qed.
Lemma D_a4a5c : decode_any W_a4a5c = Some (Branch BC_EQ 10 0 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a4a60 : bv 32 := 0x40950433.
Lemma F_a4a60 : fetch_word Asan.M.loaded_segments (0xa4a60 : word) = Some W_a4a60.
Proof. vm_refl. Qed.
Lemma D_a4a60 : decode_any W_a4a60 = Some (Op ALU_SUB 8 10 9, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a4a64 : bv 32 := 0x00040513.
Lemma F_a4a64 : fetch_word Asan.M.loaded_segments (0xa4a64 : word) = Some W_a4a64.
Proof. vm_refl. Qed.
Lemma D_a4a64 : decode_any W_a4a64 = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a4a68 : bv 32 := 0x01813083.
Lemma F_a4a68 : fetch_word Asan.M.loaded_segments (0xa4a68 : word) = Some W_a4a68.
Proof. vm_refl. Qed.
Lemma D_a4a68 : decode_any W_a4a68 = Some (Load SZ8 true 1 2 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a4a6c : bv 32 := 0x01013403.
Lemma F_a4a6c : fetch_word Asan.M.loaded_segments (0xa4a6c : word) = Some W_a4a6c.
Proof. vm_refl. Qed.
Lemma D_a4a6c : decode_any W_a4a6c = Some (Load SZ8 true 8 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a4a70 : bv 32 := 0x00813483.
Lemma F_a4a70 : fetch_word Asan.M.loaded_segments (0xa4a70 : word) = Some W_a4a70.
Proof. vm_refl. Qed.
Lemma D_a4a70 : decode_any W_a4a70 = Some (Load SZ8 true 9 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a4a74 : bv 32 := 0x02010113.
Lemma F_a4a74 : fetch_word Asan.M.loaded_segments (0xa4a74 : word) = Some W_a4a74.
Proof. vm_refl. Qed.
Lemma D_a4a74 : decode_any W_a4a74 = Some (OpImm ALU_ADD 2 2 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a4a78 : bv 32 := 0x00008067.
Lemma F_a4a78 : fetch_word Asan.M.loaded_segments (0xa4a78 : word) = Some W_a4a78.
Proof. vm_refl. Qed.
Lemma D_a4a78 : decode_any W_a4a78 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.
