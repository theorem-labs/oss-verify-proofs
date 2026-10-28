(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
(* [comment removed for export] *)

From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.H Require GcFlushS23.   (* [comment removed for export] *)
From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OssFuzzTheorems.leptonica.pix_orient_fuzzer.images Require Import Ubsan.
Open Scope bv_scope.
#[local] Hint Extern 0 (BvWf _ _) => (lazymatch goal with |- BvWf ?n ?v => is_closed_term n; is_closed_term v end; exact I) : typeclass_instances.   (* [comment removed for export] *)

(* [comment removed for export] *)
Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

Definition W_80000 : bv 32 := 0x01d31463.
Lemma F_80000 : fetch_word Ubsan.M.loaded_segments (0x80000 : word) = Some W_80000.
Proof. vm_refl. Qed.
Lemma D_80000 : decode_any W_80000 = Some (Branch BC_NE 6 29 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_80004 : bv 32 := 0x4f00206f.
Lemma F_80004 : fetch_word Ubsan.M.loaded_segments (0x80004 : word) = Some W_80004.
Proof. vm_refl. Qed.
Lemma D_80004 : decode_any W_80004 = Some (Jal 0 9456, 4%Z).
Proof. vm_refl. Qed.

Definition W_80008 : bv 32 := 0x00a8beb3.
Lemma F_80008 : fetch_word Ubsan.M.loaded_segments (0x80008 : word) = Some W_80008.
Proof. vm_refl. Qed.
Lemma D_80008 : decode_any W_80008 = Some (Op ALU_SLTU 29 17 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_8000c : bv 32 := 0x000e2e13.
Lemma F_8000c : fetch_word Ubsan.M.loaded_segments (0x8000c : word) = Some W_8000c.
Proof. vm_refl. Qed.
Lemma D_8000c : decode_any W_8000c = Some (OpImm ALU_SLT 28 28 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_80010 : bv 32 := 0x01cece33.
Lemma F_80010 : fetch_word Ubsan.M.loaded_segments (0x80010 : word) = Some W_80010.
Proof. vm_refl. Qed.
Lemma D_80010 : decode_any W_80010 = Some (Op ALU_XOR 28 29 28, 4%Z).
Proof. vm_refl. Qed.

Definition W_80014 : bv 32 := 0x001e4e13.
Lemma F_80014 : fetch_word Ubsan.M.loaded_segments (0x80014 : word) = Some W_80014.
Proof. vm_refl. Qed.
Lemma D_80014 : decode_any W_80014 = Some (OpImm ALU_XOR 28 28 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_80018 : bv 32 := 0x000e1463.
Lemma F_80018 : fetch_word Ubsan.M.loaded_segments (0x80018 : word) = Some W_80018.
Proof. vm_refl. Qed.
Lemma D_80018 : decode_any W_80018 = Some (Branch BC_NE 28 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_8001c : bv 32 := 0x4d80206f.
Lemma F_8001c : fetch_word Ubsan.M.loaded_segments (0x8001c : word) = Some W_8001c.
Proof. vm_refl. Qed.
Lemma D_8001c : decode_any W_8001c = Some (Jal 0 9432, 4%Z).
Proof. vm_refl. Qed.

Definition W_80020 : bv 32 := 0x405cde1b.
Lemma F_80020 : fetch_word Ubsan.M.loaded_segments (0x80020 : word) = Some W_80020.
Proof. vm_refl. Qed.
Lemma D_80020 : decode_any W_80020 = Some (ShiftImm32 ALU_SRA 28 25 5, 4%Z).
Proof. vm_refl. Qed.

Definition W_80024 : bv 32 := 0x002e1a13.
Lemma F_80024 : fetch_word Ubsan.M.loaded_segments (0x80024 : word) = Some W_80024.
Proof. vm_refl. Qed.
Lemma D_80024 : decode_any W_80024 = Some (ShiftImm ALU_SLL 20 28 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_80028 : bv 32 := 0x01488a33.
Lemma F_80028 : fetch_word Ubsan.M.loaded_segments (0x80028 : word) = Some W_80028.
Proof. vm_refl. Qed.
Lemma D_80028 : decode_any W_80028 = Some (Op ALU_ADD 20 17 20, 4%Z).
Proof. vm_refl. Qed.

Definition W_8002c : bv 32 := 0x001a3e93.
Lemma F_8002c : fetch_word Ubsan.M.loaded_segments (0x8002c : word) = Some W_8002c.
Proof. vm_refl. Qed.
Lemma D_8002c : decode_any W_8002c = Some (OpImm ALU_SLTU 29 20 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_80030 : bv 32 := 0x01d31463.
Lemma F_80030 : fetch_word Ubsan.M.loaded_segments (0x80030 : word) = Some W_80030.
Proof. vm_refl. Qed.
Lemma D_80030 : decode_any W_80030 = Some (Branch BC_NE 6 29 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_80034 : bv 32 := 0x4c00206f.
Lemma F_80034 : fetch_word Ubsan.M.loaded_segments (0x80034 : word) = Some W_80034.
Proof. vm_refl. Qed.
Lemma D_80034 : decode_any W_80034 = Some (Jal 0 9408, 4%Z).
Proof. vm_refl. Qed.

Definition W_80038 : bv 32 := 0x011a38b3.
Lemma F_80038 : fetch_word Ubsan.M.loaded_segments (0x80038 : word) = Some W_80038.
Proof. vm_refl. Qed.
Lemma D_80038 : decode_any W_80038 = Some (Op ALU_SLTU 17 20 17, 4%Z).
Proof. vm_refl. Qed.

Definition W_8003c : bv 32 := 0x000e2313.
Lemma F_8003c : fetch_word Ubsan.M.loaded_segments (0x8003c : word) = Some W_8003c.
Proof. vm_refl. Qed.
Lemma D_8003c : decode_any W_8003c = Some (OpImm ALU_SLT 6 28 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_80040 : bv 32 := 0x0068c8b3.
Lemma F_80040 : fetch_word Ubsan.M.loaded_segments (0x80040 : word) = Some W_80040.
Proof. vm_refl. Qed.
Lemma D_80040 : decode_any W_80040 = Some (Op ALU_XOR 17 17 6, 4%Z).
Proof. vm_refl. Qed.

Definition W_80044 : bv 32 := 0x0018c893.
Lemma F_80044 : fetch_word Ubsan.M.loaded_segments (0x80044 : word) = Some W_80044.
Proof. vm_refl. Qed.
Lemma D_80044 : decode_any W_80044 = Some (OpImm ALU_XOR 17 17 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_80048 : bv 32 := 0x00089463.
Lemma F_80048 : fetch_word Ubsan.M.loaded_segments (0x80048 : word) = Some W_80048.
Proof. vm_refl. Qed.
Lemma D_80048 : decode_any W_80048 = Some (Branch BC_NE 17 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_8004c : bv 32 := 0x4a80206f.
Lemma F_8004c : fetch_word Ubsan.M.loaded_segments (0x8004c : word) = Some W_8004c.
Proof. vm_refl. Qed.
Lemma D_8004c : decode_any W_8004c = Some (Jal 0 9384, 4%Z).
Proof. vm_refl. Qed.

Definition W_80050 : bv 32 := 0x05813883.
Lemma F_80050 : fetch_word Ubsan.M.loaded_segments (0x80050 : word) = Some W_80050.
Proof. vm_refl. Qed.
Lemma D_80050 : decode_any W_80050 = Some (Load SZ8 true 17 2 88, 4%Z).
Proof. vm_refl. Qed.

Definition W_80054 : bv 32 := 0x02588e33.
Lemma F_80054 : fetch_word Ubsan.M.loaded_segments (0x80054 : word) = Some W_80054.
Proof. vm_refl. Qed.
Lemma D_80054 : decode_any W_80054 = Some (Mul M_MUL 28 17 5, 4%Z).
Proof. vm_refl. Qed.

Definition W_80058 : bv 32 := 0x025888bb.
Lemma F_80058 : fetch_word Ubsan.M.loaded_segments (0x80058 : word) = Some W_80058.
Proof. vm_refl. Qed.
Lemma D_80058 : decode_any W_80058 = Some (Mul32 M_MUL 17 17 5, 4%Z).
Proof. vm_refl. Qed.

Definition W_8005c : bv 32 := 0x01c88463.
Lemma F_8005c : fetch_word Ubsan.M.loaded_segments (0x8005c : word) = Some W_8005c.
Proof. vm_refl. Qed.
Lemma D_8005c : decode_any W_8005c = Some (Branch BC_EQ 17 28 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_80060 : bv 32 := 0x4940206f.
Lemma F_80060 : fetch_word Ubsan.M.loaded_segments (0x80060 : word) = Some W_80060.
Proof. vm_refl. Qed.
Lemma D_80060 : decode_any W_80060 = Some (Jal 0 9364, 4%Z).
Proof. vm_refl. Qed.

Definition W_80064 : bv 32 := 0x000e0e1b.
Lemma F_80064 : fetch_word Ubsan.M.loaded_segments (0x80064 : word) = Some W_80064.
Proof. vm_refl. Qed.
Lemma D_80064 : decode_any W_80064 = Some (OpImm32 28 28 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_80068 : bv 32 := 0x002e1313.
Lemma F_80068 : fetch_word Ubsan.M.loaded_segments (0x80068 : word) = Some W_80068.
Proof. vm_refl. Qed.
Lemma D_80068 : decode_any W_80068 = Some (ShiftImm ALU_SLL 6 28 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_8006c : bv 32 := 0x01330333.
Lemma F_8006c : fetch_word Ubsan.M.loaded_segments (0x8006c : word) = Some W_8006c.
Proof. vm_refl. Qed.
Lemma D_8006c : decode_any W_8006c = Some (Op ALU_ADD 6 6 19, 4%Z).
Proof. vm_refl. Qed.

Definition W_80070 : bv 32 := 0x013038b3.
Lemma F_80070 : fetch_word Ubsan.M.loaded_segments (0x80070 : word) = Some W_80070.
Proof. vm_refl. Qed.
Lemma D_80070 : decode_any W_80070 = Some (Op ALU_SLTU 17 0 19, 4%Z).
Proof. vm_refl. Qed.

Definition W_80074 : bv 32 := 0x00133e93.
Lemma F_80074 : fetch_word Ubsan.M.loaded_segments (0x80074 : word) = Some W_80074.
Proof. vm_refl. Qed.
Lemma D_80074 : decode_any W_80074 = Some (OpImm ALU_SLTU 29 6 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_80078 : bv 32 := 0x01d89463.
Lemma F_80078 : fetch_word Ubsan.M.loaded_segments (0x80078 : word) = Some W_80078.
Proof. vm_refl. Qed.
Lemma D_80078 : decode_any W_80078 = Some (Branch BC_NE 17 29 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_8007c : bv 32 := 0x4780206f.
Lemma F_8007c : fetch_word Ubsan.M.loaded_segments (0x8007c : word) = Some W_8007c.
Proof. vm_refl. Qed.
Lemma D_8007c : decode_any W_8007c = Some (Jal 0 9336, 4%Z).
Proof. vm_refl. Qed.

Definition W_80080 : bv 32 := 0x01333eb3.
Lemma F_80080 : fetch_word Ubsan.M.loaded_segments (0x80080 : word) = Some W_80080.
Proof. vm_refl. Qed.
Lemma D_80080 : decode_any W_80080 = Some (Op ALU_SLTU 29 6 19, 4%Z).
Proof. vm_refl. Qed.

Definition W_80084 : bv 32 := 0x000e2e13.
Lemma F_80084 : fetch_word Ubsan.M.loaded_segments (0x80084 : word) = Some W_80084.
Proof. vm_refl. Qed.
Lemma D_80084 : decode_any W_80084 = Some (OpImm ALU_SLT 28 28 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_80088 : bv 32 := 0x01cece33.
Lemma F_80088 : fetch_word Ubsan.M.loaded_segments (0x80088 : word) = Some W_80088.
Proof. vm_refl. Qed.
Lemma D_80088 : decode_any W_80088 = Some (Op ALU_XOR 28 29 28, 4%Z).
Proof. vm_refl. Qed.

Definition W_8008c : bv 32 := 0x001e4e13.
Lemma F_8008c : fetch_word Ubsan.M.loaded_segments (0x8008c : word) = Some W_8008c.
Proof. vm_refl. Qed.
Lemma D_8008c : decode_any W_8008c = Some (OpImm ALU_XOR 28 28 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_80090 : bv 32 := 0x000e1463.
Lemma F_80090 : fetch_word Ubsan.M.loaded_segments (0x80090 : word) = Some W_80090.
Proof. vm_refl. Qed.
Lemma D_80090 : decode_any W_80090 = Some (Branch BC_NE 28 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_80094 : bv 32 := 0x4600206f.
Lemma F_80094 : fetch_word Ubsan.M.loaded_segments (0x80094 : word) = Some W_80094.
Proof. vm_refl. Qed.
Lemma D_80094 : decode_any W_80094 = Some (Jal 0 9312, 4%Z).
Proof. vm_refl. Qed.

Definition W_80098 : bv 32 := 0x005dde1b.
Lemma F_80098 : fetch_word Ubsan.M.loaded_segments (0x80098 : word) = Some W_80098.
Proof. vm_refl. Qed.
Lemma D_80098 : decode_any W_80098 = Some (ShiftImm32 ALU_SRL 28 27 5, 4%Z).
Proof. vm_refl. Qed.

Definition W_8009c : bv 32 := 0x002e1e13.
Lemma F_8009c : fetch_word Ubsan.M.loaded_segments (0x8009c : word) = Some W_8009c.
Proof. vm_refl. Qed.
Lemma D_8009c : decode_any W_8009c = Some (ShiftImm ALU_SLL 28 28 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_800a0 : bv 32 := 0x006e0ab3.
Lemma F_800a0 : fetch_word Ubsan.M.loaded_segments (0x800a0 : word) = Some W_800a0.
Proof. vm_refl. Qed.
Lemma D_800a0 : decode_any W_800a0 = Some (Op ALU_ADD 21 28 6, 4%Z).
Proof. vm_refl. Qed.

Definition W_800a4 : bv 32 := 0x006af463.
Lemma F_800a4 : fetch_word Ubsan.M.loaded_segments (0x800a4 : word) = Some W_800a4.
Proof. vm_refl. Qed.
Lemma D_800a4 : decode_any W_800a4 = Some (Branch BC_GEU 21 6 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_800a8 : bv 32 := 0x44c0206f.
Lemma F_800a8 : fetch_word Ubsan.M.loaded_segments (0x800a8 : word) = Some W_800a8.
Proof. vm_refl. Qed.
Lemma D_800a8 : decode_any W_800a8 = Some (Jal 0 9292, 4%Z).
Proof. vm_refl. Qed.

Definition W_800ac : bv 32 := 0x001ab313.
Lemma F_800ac : fetch_word Ubsan.M.loaded_segments (0x800ac : word) = Some W_800ac.
Proof. vm_refl. Qed.
Lemma D_800ac : decode_any W_800ac = Some (OpImm ALU_SLTU 6 21 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_800b0 : bv 32 := 0x0068c8b3.
Lemma F_800b0 : fetch_word Ubsan.M.loaded_segments (0x800b0 : word) = Some W_800b0.
Proof. vm_refl. Qed.
Lemma D_800b0 : decode_any W_800b0 = Some (Op ALU_XOR 17 17 6, 4%Z).
Proof. vm_refl. Qed.

Definition W_800b4 : bv 32 := 0x00089463.
Lemma F_800b4 : fetch_word Ubsan.M.loaded_segments (0x800b4 : word) = Some W_800b4.
Proof. vm_refl. Qed.
Lemma D_800b4 : decode_any W_800b4 = Some (Branch BC_NE 17 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_800b8 : bv 32 := 0x43c0206f.
Lemma F_800b8 : fetch_word Ubsan.M.loaded_segments (0x800b8 : word) = Some W_800b8.
Proof. vm_refl. Qed.
Lemma D_800b8 : decode_any W_800b8 = Some (Jal 0 9276, 4%Z).
Proof. vm_refl. Qed.

Definition W_800bc : bv 32 := 0x010787b3.
Lemma F_800bc : fetch_word Ubsan.M.loaded_segments (0x800bc : word) = Some W_800bc.
Proof. vm_refl. Qed.
Lemma D_800bc : decode_any W_800bc = Some (Op ALU_ADD 15 15 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_800c0 : bv 32 := 0x0007ab83.
Lemma F_800c0 : fetch_word Ubsan.M.loaded_segments (0x800c0 : word) = Some W_800c0.
Proof. vm_refl. Qed.
Lemma D_800c0 : decode_any W_800c0 = Some (Load SZ4 true 23 15 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_800c4 : bv 32 := 0x40c4043b.
Lemma F_800c4 : fetch_word Ubsan.M.loaded_segments (0x800c4 : word) = Some W_800c4.
Proof. vm_refl. Qed.
Lemma D_800c4 : decode_any W_800c4 = Some (Op32 ALU_SUB 8 8 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_800c8 : bv 32 := 0x74c4f063.
Lemma F_800c8 : fetch_word Ubsan.M.loaded_segments (0x800c8 : word) = Some W_800c8.
Proof. vm_refl. Qed.
Lemma D_800c8 : decode_any W_800c8 = Some (Branch BC_GEU 9 12 1856, 4%Z).
Proof. vm_refl. Qed.

Definition W_800cc : bv 32 := 0x0204061b.
Lemma F_800cc : fetch_word Ubsan.M.loaded_segments (0x800cc : word) = Some W_800cc.
Proof. vm_refl. Qed.
Lemma D_800cc : decode_any W_800cc = Some (OpImm32 12 8 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_800d0 : bv 32 := 0x02000793.
Lemma F_800d0 : fetch_word Ubsan.M.loaded_segments (0x800d0 : word) = Some W_800d0.
Proof. vm_refl. Qed.
Lemma D_800d0 : decode_any W_800d0 = Some (OpImm ALU_ADD 15 0 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_800d4 : bv 32 := 0x00c7f463.
Lemma F_800d4 : fetch_word Ubsan.M.loaded_segments (0x800d4 : word) = Some W_800d4.
Proof. vm_refl. Qed.
Lemma D_800d4 : decode_any W_800d4 = Some (Branch BC_GEU 15 12 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_800d8 : bv 32 := 0x41c0206f.
Lemma F_800d8 : fetch_word Ubsan.M.loaded_segments (0x800d8 : word) = Some W_800d8.
Proof. vm_refl. Qed.
Lemma D_800d8 : decode_any W_800d8 = Some (Jal 0 9244, 4%Z).
Proof. vm_refl. Qed.

Definition W_800dc : bv 32 := 0x00261613.
Lemma F_800dc : fetch_word Ubsan.M.loaded_segments (0x800dc : word) = Some W_800dc.
Proof. vm_refl. Qed.
Lemma D_800dc : decode_any W_800dc = Some (ShiftImm ALU_SLL 12 12 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_800e0 : bv 32 := 0xfff9f797.
Lemma F_800e0 : fetch_word Ubsan.M.loaded_segments (0x800e0 : word) = Some W_800e0.
Proof. vm_refl. Qed.
Lemma D_800e0 : decode_any W_800e0 = Some (Auipc 15 1048479, 4%Z).
Proof. vm_refl. Qed.

Definition W_800e4 : bv 32 := 0x3e478793.
Lemma F_800e4 : fetch_word Ubsan.M.loaded_segments (0x800e4 : word) = Some W_800e4.
Proof. vm_refl. Qed.
Lemma D_800e4 : decode_any W_800e4 = Some (OpImm ALU_ADD 15 15 996, 4%Z).
Proof. vm_refl. Qed.

Definition W_800e8 : bv 32 := 0xfff7c813.
Lemma F_800e8 : fetch_word Ubsan.M.loaded_segments (0x800e8 : word) = Some W_800e8.
Proof. vm_refl. Qed.
Lemma D_800e8 : decode_any W_800e8 = Some (OpImm ALU_XOR 16 15 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_800ec : bv 32 := 0x00c87463.
Lemma F_800ec : fetch_word Ubsan.M.loaded_segments (0x800ec : word) = Some W_800ec.
Proof. vm_refl. Qed.
Lemma D_800ec : decode_any W_800ec = Some (Branch BC_GEU 16 12 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_800f0 : bv 32 := 0x4040206f.
Lemma F_800f0 : fetch_word Ubsan.M.loaded_segments (0x800f0 : word) = Some W_800f0.
Proof. vm_refl. Qed.
Lemma D_800f0 : decode_any W_800f0 = Some (Jal 0 9220, 4%Z).
Proof. vm_refl. Qed.

Definition W_800f4 : bv 32 := 0x00000f93.
Lemma F_800f4 : fetch_word Ubsan.M.loaded_segments (0x800f4 : word) = Some W_800f4.
Proof. vm_refl. Qed.
Lemma D_800f4 : decode_any W_800f4 = Some (OpImm ALU_ADD 31 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_800f8 : bv 32 := 0x00000413.
Lemma F_800f8 : fetch_word Ubsan.M.loaded_segments (0x800f8 : word) = Some W_800f8.
Proof. vm_refl. Qed.
Lemma D_800f8 : decode_any W_800f8 = Some (OpImm ALU_ADD 8 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_800fc : bv 32 := 0x00000913.
Lemma F_800fc : fetch_word Ubsan.M.loaded_segments (0x800fc : word) = Some W_800fc.
Proof. vm_refl. Qed.
Lemma D_800fc : decode_any W_800fc = Some (OpImm ALU_ADD 18 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_80100 : bv 32 := 0x00c78633.
Lemma F_80100 : fetch_word Ubsan.M.loaded_segments (0x80100 : word) = Some W_80100.
Proof. vm_refl. Qed.
Lemma D_80100 : decode_any W_80100 = Some (Op ALU_ADD 12 15 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_80104 : bv 32 := 0x00062783.
Lemma F_80104 : fetch_word Ubsan.M.loaded_segments (0x80104 : word) = Some W_80104.
Proof. vm_refl. Qed.
Lemma D_80104 : decode_any W_80104 = Some (Load SZ4 true 15 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_80108 : bv 32 := 0x00100613.
Lemma F_80108 : fetch_word Ubsan.M.loaded_segments (0x80108 : word) = Some W_80108.
Proof. vm_refl. Qed.
Lemma D_80108 : decode_any W_80108 = Some (OpImm ALU_ADD 12 0 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_8010c : bv 32 := 0x0177fbb3.
Lemma F_8010c : fetch_word Ubsan.M.loaded_segments (0x8010c : word) = Some W_8010c.
Proof. vm_refl. Qed.
Lemma D_8010c : decode_any W_8010c = Some (Op ALU_AND 23 15 23, 4%Z).
Proof. vm_refl. Qed.

Definition W_80110 : bv 32 := 0x5cd0006f.
Lemma F_80110 : fetch_word Ubsan.M.loaded_segments (0x80110 : word) = Some W_80110.
Proof. vm_refl. Qed.
Lemma D_80110 : decode_any W_80110 = Some (Jal 0 3532, 4%Z).
Proof. vm_refl. Qed.

Definition W_80114 : bv 32 := 0x01f47613.
Lemma F_80114 : fetch_word Ubsan.M.loaded_segments (0x80114 : word) = Some W_80114.
Proof. vm_refl. Qed.
Lemma D_80114 : decode_any W_80114 = Some (OpImm ALU_AND 12 8 31, 4%Z).
Proof. vm_refl. Qed.

Definition W_80118 : bv 32 := 0x1e060263.
Lemma F_80118 : fetch_word Ubsan.M.loaded_segments (0x80118 : word) = Some W_80118.
Proof. vm_refl. Qed.
Lemma D_80118 : decode_any W_80118 = Some (Branch BC_EQ 12 0 484, 4%Z).
Proof. vm_refl. Qed.

Definition W_8011c : bv 32 := 0x00261693.
Lemma F_8011c : fetch_word Ubsan.M.loaded_segments (0x8011c : word) = Some W_8011c.
Proof. vm_refl. Qed.
Lemma D_8011c : decode_any W_8011c = Some (ShiftImm ALU_SLL 13 12 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_80120 : bv 32 := 0xfff9f797.
Lemma F_80120 : fetch_word Ubsan.M.loaded_segments (0x80120 : word) = Some W_80120.
Proof. vm_refl. Qed.
Lemma D_80120 : decode_any W_80120 = Some (Auipc 15 1048479, 4%Z).
Proof. vm_refl. Qed.

Definition W_80124 : bv 32 := 0x3a478793.
Lemma F_80124 : fetch_word Ubsan.M.loaded_segments (0x80124 : word) = Some W_80124.
Proof. vm_refl. Qed.
Lemma D_80124 : decode_any W_80124 = Some (OpImm ALU_ADD 15 15 932, 4%Z).
Proof. vm_refl. Qed.

Definition W_80128 : bv 32 := 0xfff7c813.
Lemma F_80128 : fetch_word Ubsan.M.loaded_segments (0x80128 : word) = Some W_80128.
Proof. vm_refl. Qed.
Lemma D_80128 : decode_any W_80128 = Some (OpImm ALU_XOR 16 15 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_8012c : bv 32 := 0x00d87463.
Lemma F_8012c : fetch_word Ubsan.M.loaded_segments (0x8012c : word) = Some W_8012c.
Proof. vm_refl. Qed.
Lemma D_8012c : decode_any W_8012c = Some (Branch BC_GEU 16 13 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_80130 : bv 32 := 0x3c40206f.
Lemma F_80130 : fetch_word Ubsan.M.loaded_segments (0x80130 : word) = Some W_80130.
Proof. vm_refl. Qed.
Lemma D_80130 : decode_any W_80130 = Some (Jal 0 9156, 4%Z).
Proof. vm_refl. Qed.

Definition W_80134 : bv 32 := 0x00d786b3.
Lemma F_80134 : fetch_word Ubsan.M.loaded_segments (0x80134 : word) = Some W_80134.
Proof. vm_refl. Qed.
Lemma D_80134 : decode_any W_80134 = Some (Op ALU_ADD 13 15 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_80138 : bv 32 := 0x0006ae03.
Lemma F_80138 : fetch_word Ubsan.M.loaded_segments (0x80138 : word) = Some W_80138.
Proof. vm_refl. Qed.
Lemma D_80138 : decode_any W_80138 = Some (Load SZ4 true 28 13 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_8013c : bv 32 := 0x1c00006f.
Lemma F_8013c : fetch_word Ubsan.M.loaded_segments (0x8013c : word) = Some W_8013c.
Proof. vm_refl. Qed.
Lemma D_8013c : decode_any W_8013c = Some (Jal 0 448, 4%Z).
Proof. vm_refl. Qed.

Definition W_80140 : bv 32 := 0x00163793.
Lemma F_80140 : fetch_word Ubsan.M.loaded_segments (0x80140 : word) = Some W_80140.
Proof. vm_refl. Qed.
Lemma D_80140 : decode_any W_80140 = Some (OpImm ALU_SLTU 15 12 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_80144 : bv 32 := 0x0010b813.
Lemma F_80144 : fetch_word Ubsan.M.loaded_segments (0x80144 : word) = Some W_80144.
Proof. vm_refl. Qed.
Lemma D_80144 : decode_any W_80144 = Some (OpImm ALU_SLTU 16 1 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_80148 : bv 32 := 0x02000a13.
Lemma F_80148 : fetch_word Ubsan.M.loaded_segments (0x80148 : word) = Some W_80148.
Proof. vm_refl. Qed.
Lemma D_80148 : decode_any W_80148 = Some (OpImm ALU_ADD 20 0 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_8014c : bv 32 := 0x40ca08b3.
Lemma F_8014c : fetch_word Ubsan.M.loaded_segments (0x8014c : word) = Some W_8014c.
Proof. vm_refl. Qed.
Lemma D_8014c : decode_any W_8014c = Some (Op ALU_SUB 17 20 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_80150 : bv 32 := 0x401a0ab3.
Lemma F_80150 : fetch_word Ubsan.M.loaded_segments (0x80150 : word) = Some W_80150.
Proof. vm_refl. Qed.
Lemma D_80150 : decode_any W_80150 = Some (Op ALU_SUB 21 20 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_80154 : bv 32 := 0xfff80813.
Lemma F_80154 : fetch_word Ubsan.M.loaded_segments (0x80154 : word) = Some W_80154.
Proof. vm_refl. Qed.
Lemma D_80154 : decode_any W_80154 = Some (OpImm ALU_ADD 16 16 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_80158 : bv 32 := 0xfff78793.
Lemma F_80158 : fetch_word Ubsan.M.loaded_segments (0x80158 : word) = Some W_80158.
Proof. vm_refl. Qed.
Lemma D_80158 : decode_any W_80158 = Some (OpImm ALU_ADD 15 15 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_8015c : bv 32 := 0x01587bb3.
Lemma F_8015c : fetch_word Ubsan.M.loaded_segments (0x8015c : word) = Some W_8015c.
Proof. vm_refl. Qed.
Lemma D_8015c : decode_any W_8015c = Some (Op ALU_AND 23 16 21, 4%Z).
Proof. vm_refl. Qed.

Definition W_80160 : bv 32 := 0x0117f7b3.
Lemma F_80160 : fetch_word Ubsan.M.loaded_segments (0x80160 : word) = Some W_80160.
Proof. vm_refl. Qed.
Lemma D_80160 : decode_any W_80160 = Some (Op ALU_AND 15 15 17, 4%Z).
Proof. vm_refl. Qed.

Definition W_80164 : bv 32 := 0x0177b833.
Lemma F_80164 : fetch_word Ubsan.M.loaded_segments (0x80164 : word) = Some W_80164.
Proof. vm_refl. Qed.
Lemma D_80164 : decode_any W_80164 = Some (Op ALU_SLTU 16 15 23, 4%Z).
Proof. vm_refl. Qed.

Definition W_80168 : bv 32 := 0x00184813.
Lemma F_80168 : fetch_word Ubsan.M.loaded_segments (0x80168 : word) = Some W_80168.
Proof. vm_refl. Qed.
Lemma D_80168 : decode_any W_80168 = Some (OpImm ALU_XOR 16 16 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_8016c : bv 32 := 0x40fb8eb3.
Lemma F_8016c : fetch_word Ubsan.M.loaded_segments (0x8016c : word) = Some W_8016c.
Proof. vm_refl. Qed.
Lemma D_8016c : decode_any W_8016c = Some (Op ALU_SUB 29 23 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_80170 : bv 32 := 0x00581813.
Lemma F_80170 : fetch_word Ubsan.M.loaded_segments (0x80170 : word) = Some W_80170.
Proof. vm_refl. Qed.
Lemma D_80170 : decode_any W_80170 = Some (ShiftImm ALU_SLL 16 16 5, 4%Z).
Proof. vm_refl. Qed.

Definition W_80174 : bv 32 := 0x010e8eb3.
Lemma F_80174 : fetch_word Ubsan.M.loaded_segments (0x80174 : word) = Some W_80174.
Proof. vm_refl. Qed.
Lemma D_80174 : decode_any W_80174 = Some (Op ALU_ADD 29 29 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_80178 : bv 32 := 0x01da7463.
Lemma F_80178 : fetch_word Ubsan.M.loaded_segments (0x80178 : word) = Some W_80178.
Proof. vm_refl. Qed.
Lemma D_80178 : decode_any W_80178 = Some (Branch BC_GEU 20 29 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_8017c : bv 32 := 0x3780206f.
Lemma F_8017c : fetch_word Ubsan.M.loaded_segments (0x8017c : word) = Some W_8017c.
Proof. vm_refl. Qed.
Lemma D_8017c : decode_any W_8017c = Some (Jal 0 9080, 4%Z).
Proof. vm_refl. Qed.

Definition W_80180 : bv 32 := 0x000e8f1b.
Lemma F_80180 : fetch_word Ubsan.M.loaded_segments (0x80180 : word) = Some W_80180.
Proof. vm_refl. Qed.
Lemma D_80180 : decode_any W_80180 = Some (OpImm32 30 29 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_80184 : bv 32 := 0xfff9f797.
Lemma F_80184 : fetch_word Ubsan.M.loaded_segments (0x80184 : word) = Some W_80184.
Proof. vm_refl. Qed.
Lemma D_80184 : decode_any W_80184 = Some (Auipc 15 1048479, 4%Z).
Proof. vm_refl. Qed.

Definition W_80188 : bv 32 := 0x002f1313.
Lemma F_80188 : fetch_word Ubsan.M.loaded_segments (0x80188 : word) = Some W_80188.
Proof. vm_refl. Qed.
Lemma D_80188 : decode_any W_80188 = Some (ShiftImm ALU_SLL 6 30 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_8018c : bv 32 := 0x2bc78813.
Lemma F_8018c : fetch_word Ubsan.M.loaded_segments (0x8018c : word) = Some W_8018c.
Proof. vm_refl. Qed.
Lemma D_8018c : decode_any W_8018c = Some (OpImm ALU_ADD 16 15 700, 4%Z).
Proof. vm_refl. Qed.

Definition W_80190 : bv 32 := 0xfff84793.
Lemma F_80190 : fetch_word Ubsan.M.loaded_segments (0x80190 : word) = Some W_80190.
Proof. vm_refl. Qed.
Lemma D_80190 : decode_any W_80190 = Some (OpImm ALU_XOR 15 16 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_80194 : bv 32 := 0x0067f463.
Lemma F_80194 : fetch_word Ubsan.M.loaded_segments (0x80194 : word) = Some W_80194.
Proof. vm_refl. Qed.
Lemma D_80194 : decode_any W_80194 = Some (Branch BC_GEU 15 6 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_80198 : bv 32 := 0x35c0206f.
Lemma F_80198 : fetch_word Ubsan.M.loaded_segments (0x80198 : word) = Some W_80198.
Proof. vm_refl. Qed.
Lemma D_80198 : decode_any W_80198 = Some (Jal 0 9052, 4%Z).
Proof. vm_refl. Qed.

Definition W_8019c : bv 32 := 0x00680333.
Lemma F_8019c : fetch_word Ubsan.M.loaded_segments (0x8019c : word) = Some W_8019c.
Proof. vm_refl. Qed.
Lemma D_8019c : decode_any W_8019c = Some (Op ALU_ADD 6 16 6, 4%Z).
Proof. vm_refl. Qed.

Definition W_801a0 : bv 32 := 0x00032f83.
Lemma F_801a0 : fetch_word Ubsan.M.loaded_segments (0x801a0 : word) = Some W_801a0.
Proof. vm_refl. Qed.
Lemma D_801a0 : decode_any W_801a0 = Some (Load SZ4 true 31 6 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_801a4 : bv 32 := 0x52008463.
Lemma F_801a4 : fetch_word Ubsan.M.loaded_segments (0x801a4 : word) = Some W_801a4.
Proof. vm_refl. Qed.
Lemma D_801a4 : decode_any W_801a4 = Some (Branch BC_EQ 1 0 1320, 4%Z).
Proof. vm_refl. Qed.

Definition W_801a8 : bv 32 := 0x002a9e13.
Lemma F_801a8 : fetch_word Ubsan.M.loaded_segments (0x801a8 : word) = Some W_801a8.
Proof. vm_refl. Qed.
Lemma D_801a8 : decode_any W_801a8 = Some (ShiftImm ALU_SLL 28 21 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_801ac : bv 32 := 0x01c7f463.
Lemma F_801ac : fetch_word Ubsan.M.loaded_segments (0x801ac : word) = Some W_801ac.
Proof. vm_refl. Qed.
Lemma D_801ac : decode_any W_801ac = Some (Branch BC_GEU 15 28 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_801b0 : bv 32 := 0x3440206f.
Lemma F_801b0 : fetch_word Ubsan.M.loaded_segments (0x801b0 : word) = Some W_801b0.
Proof. vm_refl. Qed.
Lemma D_801b0 : decode_any W_801b0 = Some (Jal 0 9028, 4%Z).
Proof. vm_refl. Qed.

Definition W_801b4 : bv 32 := 0x02770b33.
Lemma F_801b4 : fetch_word Ubsan.M.loaded_segments (0x801b4 : word) = Some W_801b4.
Proof. vm_refl. Qed.
Lemma D_801b4 : decode_any W_801b4 = Some (Mul M_MUL 22 14 7, 4%Z).
Proof. vm_refl. Qed.

Definition W_801b8 : bv 32 := 0x027707bb.
Lemma F_801b8 : fetch_word Ubsan.M.loaded_segments (0x801b8 : word) = Some W_801b8.
Proof. vm_refl. Qed.
Lemma D_801b8 : decode_any W_801b8 = Some (Mul32 M_MUL 15 14 7, 4%Z).
Proof. vm_refl. Qed.

Definition W_801bc : bv 32 := 0x01678463.
Lemma F_801bc : fetch_word Ubsan.M.loaded_segments (0x801bc : word) = Some W_801bc.
Proof. vm_refl. Qed.
Lemma D_801bc : decode_any W_801bc = Some (Branch BC_EQ 15 22 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_801c0 : bv 32 := 0x3340206f.
Lemma F_801c0 : fetch_word Ubsan.M.loaded_segments (0x801c0 : word) = Some W_801c0.
Proof. vm_refl. Qed.
Lemma D_801c0 : decode_any W_801c0 = Some (Jal 0 9012, 4%Z).
Proof. vm_refl. Qed.

Definition W_801c4 : bv 32 := 0x000b0b1b.
Lemma F_801c4 : fetch_word Ubsan.M.loaded_segments (0x801c4 : word) = Some W_801c4.
Proof. vm_refl. Qed.
Lemma D_801c4 : decode_any W_801c4 = Some (OpImm32 22 22 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_801c8 : bv 32 := 0x002b1793.
Lemma F_801c8 : fetch_word Ubsan.M.loaded_segments (0x801c8 : word) = Some W_801c8.
Proof. vm_refl. Qed.
Lemma D_801c8 : decode_any W_801c8 = Some (ShiftImm ALU_SLL 15 22 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_801cc : bv 32 := 0x00a787b3.
Lemma F_801cc : fetch_word Ubsan.M.loaded_segments (0x801cc : word) = Some W_801cc.
Proof. vm_refl. Qed.
Lemma D_801cc : decode_any W_801cc = Some (Op ALU_ADD 15 15 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_801d0 : bv 32 := 0x00a03333.
Lemma F_801d0 : fetch_word Ubsan.M.loaded_segments (0x801d0 : word) = Some W_801d0.
Proof. vm_refl. Qed.
Lemma D_801d0 : decode_any W_801d0 = Some (Op ALU_SLTU 6 0 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_801d4 : bv 32 := 0x0017bd13.
Lemma F_801d4 : fetch_word Ubsan.M.loaded_segments (0x801d4 : word) = Some W_801d4.
Proof. vm_refl. Qed.
Lemma D_801d4 : decode_any W_801d4 = Some (OpImm ALU_SLTU 26 15 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_801d8 : bv 32 := 0x01a31463.
Lemma F_801d8 : fetch_word Ubsan.M.loaded_segments (0x801d8 : word) = Some W_801d8.
Proof. vm_refl. Qed.
Lemma D_801d8 : decode_any W_801d8 = Some (Branch BC_NE 6 26 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_801dc : bv 32 := 0x3180206f.
Lemma F_801dc : fetch_word Ubsan.M.loaded_segments (0x801dc : word) = Some W_801dc.
Proof. vm_refl. Qed.
Lemma D_801dc : decode_any W_801dc = Some (Jal 0 8984, 4%Z).
Proof. vm_refl. Qed.

Definition W_801e0 : bv 32 := 0x00a7bd33.
Lemma F_801e0 : fetch_word Ubsan.M.loaded_segments (0x801e0 : word) = Some W_801e0.
Proof. vm_refl. Qed.
Lemma D_801e0 : decode_any W_801e0 = Some (Op ALU_SLTU 26 15 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_801e4 : bv 32 := 0x000b2b13.
Lemma F_801e4 : fetch_word Ubsan.M.loaded_segments (0x801e4 : word) = Some W_801e4.
Proof. vm_refl. Qed.
Lemma D_801e4 : decode_any W_801e4 = Some (OpImm ALU_SLT 22 22 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_801e8 : bv 32 := 0x016d4b33.
Lemma F_801e8 : fetch_word Ubsan.M.loaded_segments (0x801e8 : word) = Some W_801e8.
Proof. vm_refl. Qed.
Lemma D_801e8 : decode_any W_801e8 = Some (Op ALU_XOR 22 26 22, 4%Z).
Proof. vm_refl. Qed.

Definition W_801ec : bv 32 := 0x001b4b13.
Lemma F_801ec : fetch_word Ubsan.M.loaded_segments (0x801ec : word) = Some W_801ec.
Proof. vm_refl. Qed.
Lemma D_801ec : decode_any W_801ec = Some (OpImm ALU_XOR 22 22 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_801f0 : bv 32 := 0x000b1463.
Lemma F_801f0 : fetch_word Ubsan.M.loaded_segments (0x801f0 : word) = Some W_801f0.
Proof. vm_refl. Qed.
Lemma D_801f0 : decode_any W_801f0 = Some (Branch BC_NE 22 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_801f4 : bv 32 := 0x3000206f.
Lemma F_801f4 : fetch_word Ubsan.M.loaded_segments (0x801f4 : word) = Some W_801f4.
Proof. vm_refl. Qed.
Lemma D_801f4 : decode_any W_801f4 = Some (Jal 0 8960, 4%Z).
Proof. vm_refl. Qed.

Definition W_801f8 : bv 32 := 0x405cdb1b.
Lemma F_801f8 : fetch_word Ubsan.M.loaded_segments (0x801f8 : word) = Some W_801f8.
Proof. vm_refl. Qed.
Lemma D_801f8 : decode_any W_801f8 = Some (ShiftImm32 ALU_SRA 22 25 5, 4%Z).
Proof. vm_refl. Qed.

Definition W_801fc : bv 32 := 0x002b1c93.
Lemma F_801fc : fetch_word Ubsan.M.loaded_segments (0x801fc : word) = Some W_801fc.
Proof. vm_refl. Qed.
Lemma D_801fc : decode_any W_801fc = Some (ShiftImm ALU_SLL 25 22 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_80200 : bv 32 := 0x01978cb3.
Lemma F_80200 : fetch_word Ubsan.M.loaded_segments (0x80200 : word) = Some W_80200.
Proof. vm_refl. Qed.
Lemma D_80200 : decode_any W_80200 = Some (Op ALU_ADD 25 15 25, 4%Z).
Proof. vm_refl. Qed.

Definition W_80204 : bv 32 := 0x001cbd13.
Lemma F_80204 : fetch_word Ubsan.M.loaded_segments (0x80204 : word) = Some W_80204.
Proof. vm_refl. Qed.
Lemma D_80204 : decode_any W_80204 = Some (OpImm ALU_SLTU 26 25 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_80208 : bv 32 := 0x01a31463.
Lemma F_80208 : fetch_word Ubsan.M.loaded_segments (0x80208 : word) = Some W_80208.
Proof. vm_refl. Qed.
Lemma D_80208 : decode_any W_80208 = Some (Branch BC_NE 6 26 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_8020c : bv 32 := 0x2e80206f.
Lemma F_8020c : fetch_word Ubsan.M.loaded_segments (0x8020c : word) = Some W_8020c.
Proof. vm_refl. Qed.
Lemma D_8020c : decode_any W_8020c = Some (Jal 0 8936, 4%Z).
Proof. vm_refl. Qed.

Definition W_80210 : bv 32 := 0x00fcb7b3.
Lemma F_80210 : fetch_word Ubsan.M.loaded_segments (0x80210 : word) = Some W_80210.
Proof. vm_refl. Qed.
Lemma D_80210 : decode_any W_80210 = Some (Op ALU_SLTU 15 25 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_80214 : bv 32 := 0x000b2313.
Lemma F_80214 : fetch_word Ubsan.M.loaded_segments (0x80214 : word) = Some W_80214.
Proof. vm_refl. Qed.
Lemma D_80214 : decode_any W_80214 = Some (OpImm ALU_SLT 6 22 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_80218 : bv 32 := 0x0067c7b3.
Lemma F_80218 : fetch_word Ubsan.M.loaded_segments (0x80218 : word) = Some W_80218.
Proof. vm_refl. Qed.
Lemma D_80218 : decode_any W_80218 = Some (Op ALU_XOR 15 15 6, 4%Z).
Proof. vm_refl. Qed.

Definition W_8021c : bv 32 := 0x0017c793.
Lemma F_8021c : fetch_word Ubsan.M.loaded_segments (0x8021c : word) = Some W_8021c.
Proof. vm_refl. Qed.
Lemma D_8021c : decode_any W_8021c = Some (OpImm ALU_XOR 15 15 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_80220 : bv 32 := 0x00079463.
Lemma F_80220 : fetch_word Ubsan.M.loaded_segments (0x80220 : word) = Some W_80220.
Proof. vm_refl. Qed.
Lemma D_80220 : decode_any W_80220 = Some (Branch BC_NE 15 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_80224 : bv 32 := 0x2d00206f.
Lemma F_80224 : fetch_word Ubsan.M.loaded_segments (0x80224 : word) = Some W_80224.
Proof. vm_refl. Qed.
Lemma D_80224 : decode_any W_80224 = Some (Jal 0 8912, 4%Z).
Proof. vm_refl. Qed.

Definition W_80228 : bv 32 := 0x05813303.
Lemma F_80228 : fetch_word Ubsan.M.loaded_segments (0x80228 : word) = Some W_80228.
Proof. vm_refl. Qed.
Lemma D_80228 : decode_any W_80228 = Some (Load SZ8 true 6 2 88, 4%Z).
Proof. vm_refl. Qed.

Definition W_8022c : bv 32 := 0x025307b3.
Lemma F_8022c : fetch_word Ubsan.M.loaded_segments (0x8022c : word) = Some W_8022c.
Proof. vm_refl. Qed.
Lemma D_8022c : decode_any W_8022c = Some (Mul M_MUL 15 6 5, 4%Z).
Proof. vm_refl. Qed.

Definition W_80230 : bv 32 := 0x0253033b.
Lemma F_80230 : fetch_word Ubsan.M.loaded_segments (0x80230 : word) = Some W_80230.
Proof. vm_refl. Qed.
Lemma D_80230 : decode_any W_80230 = Some (Mul32 M_MUL 6 6 5, 4%Z).
Proof. vm_refl. Qed.

Definition W_80234 : bv 32 := 0x00f30463.
Lemma F_80234 : fetch_word Ubsan.M.loaded_segments (0x80234 : word) = Some W_80234.
Proof. vm_refl. Qed.
Lemma D_80234 : decode_any W_80234 = Some (Branch BC_EQ 6 15 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_80238 : bv 32 := 0x2bc0206f.
Lemma F_80238 : fetch_word Ubsan.M.loaded_segments (0x80238 : word) = Some W_80238.
Proof. vm_refl. Qed.
Lemma D_80238 : decode_any W_80238 = Some (Jal 0 8892, 4%Z).
Proof. vm_refl. Qed.

Definition W_8023c : bv 32 := 0x0007879b.
Lemma F_8023c : fetch_word Ubsan.M.loaded_segments (0x8023c : word) = Some W_8023c.
Proof. vm_refl. Qed.
Lemma D_8023c : decode_any W_8023c = Some (OpImm32 15 15 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_80240 : bv 32 := 0x00279b13.
Lemma F_80240 : fetch_word Ubsan.M.loaded_segments (0x80240 : word) = Some W_80240.
Proof. vm_refl. Qed.
Lemma D_80240 : decode_any W_80240 = Some (ShiftImm ALU_SLL 22 15 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_80244 : bv 32 := 0x013b0b33.
Lemma F_80244 : fetch_word Ubsan.M.loaded_segments (0x80244 : word) = Some W_80244.
Proof. vm_refl. Qed.
Lemma D_80244 : decode_any W_80244 = Some (Op ALU_ADD 22 22 19, 4%Z).
Proof. vm_refl. Qed.

Definition W_80248 : bv 32 := 0x01303333.
Lemma F_80248 : fetch_word Ubsan.M.loaded_segments (0x80248 : word) = Some W_80248.
Proof. vm_refl. Qed.
Lemma D_80248 : decode_any W_80248 = Some (Op ALU_SLTU 6 0 19, 4%Z).
Proof. vm_refl. Qed.

Definition W_8024c : bv 32 := 0x001b3d13.
Lemma F_8024c : fetch_word Ubsan.M.loaded_segments (0x8024c : word) = Some W_8024c.
Proof. vm_refl. Qed.
Lemma D_8024c : decode_any W_8024c = Some (OpImm ALU_SLTU 26 22 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_80250 : bv 32 := 0x01a31463.
Lemma F_80250 : fetch_word Ubsan.M.loaded_segments (0x80250 : word) = Some W_80250.
Proof. vm_refl. Qed.
Lemma D_80250 : decode_any W_80250 = Some (Branch BC_NE 6 26 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_80254 : bv 32 := 0x2a00206f.
Lemma F_80254 : fetch_word Ubsan.M.loaded_segments (0x80254 : word) = Some W_80254.
Proof. vm_refl. Qed.
Lemma D_80254 : decode_any W_80254 = Some (Jal 0 8864, 4%Z).
Proof. vm_refl. Qed.

Definition W_80258 : bv 32 := 0x013b3d33.
Lemma F_80258 : fetch_word Ubsan.M.loaded_segments (0x80258 : word) = Some W_80258.
Proof. vm_refl. Qed.
Lemma D_80258 : decode_any W_80258 = Some (Op ALU_SLTU 26 22 19, 4%Z).
Proof. vm_refl. Qed.

Definition W_8025c : bv 32 := 0x0007a793.
Lemma F_8025c : fetch_word Ubsan.M.loaded_segments (0x8025c : word) = Some W_8025c.
Proof. vm_refl. Qed.
Lemma D_8025c : decode_any W_8025c = Some (OpImm ALU_SLT 15 15 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_80260 : bv 32 := 0x00fd47b3.
Lemma F_80260 : fetch_word Ubsan.M.loaded_segments (0x80260 : word) = Some W_80260.
Proof. vm_refl. Qed.
Lemma D_80260 : decode_any W_80260 = Some (Op ALU_XOR 15 26 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_80264 : bv 32 := 0x0017c793.
Lemma F_80264 : fetch_word Ubsan.M.loaded_segments (0x80264 : word) = Some W_80264.
Proof. vm_refl. Qed.
Lemma D_80264 : decode_any W_80264 = Some (OpImm ALU_XOR 15 15 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_80268 : bv 32 := 0x00079463.
Lemma F_80268 : fetch_word Ubsan.M.loaded_segments (0x80268 : word) = Some W_80268.
Proof. vm_refl. Qed.
Lemma D_80268 : decode_any W_80268 = Some (Branch BC_NE 15 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_8026c : bv 32 := 0x2880206f.
Lemma F_8026c : fetch_word Ubsan.M.loaded_segments (0x8026c : word) = Some W_8026c.
Proof. vm_refl. Qed.
Lemma D_8026c : decode_any W_8026c = Some (Jal 0 8840, 4%Z).
Proof. vm_refl. Qed.

Definition W_80270 : bv 32 := 0x005dd79b.
Lemma F_80270 : fetch_word Ubsan.M.loaded_segments (0x80270 : word) = Some W_80270.
Proof. vm_refl. Qed.
Lemma D_80270 : decode_any W_80270 = Some (ShiftImm32 ALU_SRL 15 27 5, 4%Z).
Proof. vm_refl. Qed.

Definition W_80274 : bv 32 := 0x00279793.
Lemma F_80274 : fetch_word Ubsan.M.loaded_segments (0x80274 : word) = Some W_80274.
Proof. vm_refl. Qed.
Lemma D_80274 : decode_any W_80274 = Some (ShiftImm ALU_SLL 15 15 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_80278 : bv 32 := 0x00fb07b3.
Lemma F_80278 : fetch_word Ubsan.M.loaded_segments (0x80278 : word) = Some W_80278.
Proof. vm_refl. Qed.
Lemma D_80278 : decode_any W_80278 = Some (Op ALU_ADD 15 22 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_8027c : bv 32 := 0x0167f463.
Lemma F_8027c : fetch_word Ubsan.M.loaded_segments (0x8027c : word) = Some W_8027c.
Proof. vm_refl. Qed.
Lemma D_8027c : decode_any W_8027c = Some (Branch BC_GEU 15 22 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_80280 : bv 32 := 0x2740206f.
Lemma F_80280 : fetch_word Ubsan.M.loaded_segments (0x80280 : word) = Some W_80280.
Proof. vm_refl. Qed.
Lemma D_80280 : decode_any W_80280 = Some (Jal 0 8820, 4%Z).
Proof. vm_refl. Qed.

Definition W_80284 : bv 32 := 0x0017bb13.
Lemma F_80284 : fetch_word Ubsan.M.loaded_segments (0x80284 : word) = Some W_80284.
Proof. vm_refl. Qed.
Lemma D_80284 : decode_any W_80284 = Some (OpImm ALU_SLTU 22 15 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_80288 : bv 32 := 0x01634333.
Lemma F_80288 : fetch_word Ubsan.M.loaded_segments (0x80288 : word) = Some W_80288.
Proof. vm_refl. Qed.
Lemma D_80288 : decode_any W_80288 = Some (Op ALU_XOR 6 6 22, 4%Z).
Proof. vm_refl. Qed.

Definition W_8028c : bv 32 := 0x00031463.
Lemma F_8028c : fetch_word Ubsan.M.loaded_segments (0x8028c : word) = Some W_8028c.
Proof. vm_refl. Qed.
Lemma D_8028c : decode_any W_8028c = Some (Branch BC_NE 6 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_80290 : bv 32 := 0x2640206f.
Lemma F_80290 : fetch_word Ubsan.M.loaded_segments (0x80290 : word) = Some W_80290.
Proof. vm_refl. Qed.
Lemma D_80290 : decode_any W_80290 = Some (Jal 0 8804, 4%Z).
Proof. vm_refl. Qed.

Definition W_80294 : bv 32 := 0x01c80833.
Lemma F_80294 : fetch_word Ubsan.M.loaded_segments (0x80294 : word) = Some W_80294.
Proof. vm_refl. Qed.
Lemma D_80294 : decode_any W_80294 = Some (Op ALU_ADD 16 16 28, 4%Z).
Proof. vm_refl. Qed.

Definition W_80298 : bv 32 := 0x00082d83.
Lemma F_80298 : fetch_word Ubsan.M.loaded_segments (0x80298 : word) = Some W_80298.
Proof. vm_refl. Qed.
Lemma D_80298 : decode_any W_80298 = Some (Load SZ4 true 27 16 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_8029c : bv 32 := 0x00c0b633.
Lemma F_8029c : fetch_word Ubsan.M.loaded_segments (0x8029c : word) = Some W_8029c.
Proof. vm_refl. Qed.
Lemma D_8029c : decode_any W_8029c = Some (Op ALU_SLTU 12 1 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_802a0 : bv 32 := 0x00c13823.
Lemma F_802a0 : fetch_word Ubsan.M.loaded_segments (0x802a0 : word) = Some W_802a0.
Proof. vm_refl. Qed.
Lemma D_802a0 : decode_any W_802a0 = Some (Store SZ8 2 12 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_802a4 : bv 32 := 0x0098b633.
Lemma F_802a4 : fetch_word Ubsan.M.loaded_segments (0x802a4 : word) = Some W_802a4.
Proof. vm_refl. Qed.
Lemma D_802a4 : decode_any W_802a4 = Some (Op ALU_SLTU 12 17 9, 4%Z).
Proof. vm_refl. Qed.

Definition W_802a8 : bv 32 := 0x00164d13.
Lemma F_802a8 : fetch_word Ubsan.M.loaded_segments (0x802a8 : word) = Some W_802a8.
Proof. vm_refl. Qed.
Lemma D_802a8 : decode_any W_802a8 = Some (OpImm ALU_XOR 26 12 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_802ac : bv 32 := 0x4354f863.
Lemma F_802ac : fetch_word Ubsan.M.loaded_segments (0x802ac : word) = Some W_802ac.
Proof. vm_refl. Qed.
Lemma D_802ac : decode_any W_802ac = Some (Branch BC_GEU 9 21 1072, 4%Z).
Proof. vm_refl. Qed.

Definition W_802b0 : bv 32 := 0x4154063b.
Lemma F_802b0 : fetch_word Ubsan.M.loaded_segments (0x802b0 : word) = Some W_802b0.
Proof. vm_refl. Qed.
Lemma D_802b0 : decode_any W_802b0 = Some (Op32 ALU_SUB 12 8 21, 4%Z).
Proof. vm_refl. Qed.

Definition W_802b4 : bv 32 := 0x0206061b.
Lemma F_802b4 : fetch_word Ubsan.M.loaded_segments (0x802b4 : word) = Some W_802b4.
Proof. vm_refl. Qed.
Lemma D_802b4 : decode_any W_802b4 = Some (OpImm32 12 12 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_802b8 : bv 32 := 0x02000813.
Lemma F_802b8 : fetch_word Ubsan.M.loaded_segments (0x802b8 : word) = Some W_802b8.
Proof. vm_refl. Qed.
Lemma D_802b8 : decode_any W_802b8 = Some (OpImm ALU_ADD 16 0 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_802bc : bv 32 := 0x00c87463.
Lemma F_802bc : fetch_word Ubsan.M.loaded_segments (0x802bc : word) = Some W_802bc.
Proof. vm_refl. Qed.
Lemma D_802bc : decode_any W_802bc = Some (Branch BC_GEU 16 12 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_802c0 : bv 32 := 0x2340206f.
Lemma F_802c0 : fetch_word Ubsan.M.loaded_segments (0x802c0 : word) = Some W_802c0.
Proof. vm_refl. Qed.
Lemma D_802c0 : decode_any W_802c0 = Some (Jal 0 8756, 4%Z).
Proof. vm_refl. Qed.

Definition W_802c4 : bv 32 := 0x00261613.
Lemma F_802c4 : fetch_word Ubsan.M.loaded_segments (0x802c4 : word) = Some W_802c4.
Proof. vm_refl. Qed.
Lemma D_802c4 : decode_any W_802c4 = Some (ShiftImm ALU_SLL 12 12 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_802c8 : bv 32 := 0xfff9f817.
Lemma F_802c8 : fetch_word Ubsan.M.loaded_segments (0x802c8 : word) = Some W_802c8.
Proof. vm_refl. Qed.
Lemma D_802c8 : decode_any W_802c8 = Some (Auipc 16 1048479, 4%Z).
Proof. vm_refl. Qed.

Definition W_802cc : bv 32 := 0x1fc80813.
Lemma F_802cc : fetch_word Ubsan.M.loaded_segments (0x802cc : word) = Some W_802cc.
Proof. vm_refl. Qed.
Lemma D_802cc : decode_any W_802cc = Some (OpImm ALU_ADD 16 16 508, 4%Z).
Proof. vm_refl. Qed.

Definition W_802d0 : bv 32 := 0xfff84893.
Lemma F_802d0 : fetch_word Ubsan.M.loaded_segments (0x802d0 : word) = Some W_802d0.
Proof. vm_refl. Qed.
Lemma D_802d0 : decode_any W_802d0 = Some (OpImm ALU_XOR 17 16 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_802d4 : bv 32 := 0x00c8f463.
Lemma F_802d4 : fetch_word Ubsan.M.loaded_segments (0x802d4 : word) = Some W_802d4.
Proof. vm_refl. Qed.
Lemma D_802d4 : decode_any W_802d4 = Some (Branch BC_GEU 17 12 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_802d8 : bv 32 := 0x21c0206f.
Lemma F_802d8 : fetch_word Ubsan.M.loaded_segments (0x802d8 : word) = Some W_802d8.
Proof. vm_refl. Qed.
Lemma D_802d8 : decode_any W_802d8 = Some (Jal 0 8732, 4%Z).
Proof. vm_refl. Qed.

Definition W_802dc : bv 32 := 0x06013823.
Lemma F_802dc : fetch_word Ubsan.M.loaded_segments (0x802dc : word) = Some W_802dc.
Proof. vm_refl. Qed.
Lemma D_802dc : decode_any W_802dc = Some (Store SZ8 2 0 112, 4%Z).
Proof. vm_refl. Qed.

Definition W_802e0 : bv 32 := 0x00000913.
Lemma F_802e0 : fetch_word Ubsan.M.loaded_segments (0x802e0 : word) = Some W_802e0.
Proof. vm_refl. Qed.
Lemma D_802e0 : decode_any W_802e0 = Some (OpImm ALU_ADD 18 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_802e4 : bv 32 := 0x00000313.
Lemma F_802e4 : fetch_word Ubsan.M.loaded_segments (0x802e4 : word) = Some W_802e4.
Proof. vm_refl. Qed.
Lemma D_802e4 : decode_any W_802e4 = Some (OpImm ALU_ADD 6 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_802e8 : bv 32 := 0x00c80633.
Lemma F_802e8 : fetch_word Ubsan.M.loaded_segments (0x802e8 : word) = Some W_802e8.
Proof. vm_refl. Qed.
Lemma D_802e8 : decode_any W_802e8 = Some (Op ALU_ADD 12 16 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_802ec : bv 32 := 0x00062603.
Lemma F_802ec : fetch_word Ubsan.M.loaded_segments (0x802ec : word) = Some W_802ec.
Proof. vm_refl. Qed.
Lemma D_802ec : decode_any W_802ec = Some (Load SZ4 true 12 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_802f0 : bv 32 := 0x00100813.
Lemma F_802f0 : fetch_word Ubsan.M.loaded_segments (0x802f0 : word) = Some W_802f0.
Proof. vm_refl. Qed.
Lemma D_802f0 : decode_any W_802f0 = Some (OpImm ALU_ADD 16 0 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_802f4 : bv 32 := 0x01b67db3.
Lemma F_802f4 : fetch_word Ubsan.M.loaded_segments (0x802f4 : word) = Some W_802f4.
Proof. vm_refl. Qed.
Lemma D_802f4 : decode_any W_802f4 = Some (Op ALU_AND 27 12 27, 4%Z).
Proof. vm_refl. Qed.

Definition W_802f8 : bv 32 := 0x5500006f.
Lemma F_802f8 : fetch_word Ubsan.M.loaded_segments (0x802f8 : word) = Some W_802f8.
Proof. vm_refl. Qed.
Lemma D_802f8 : decode_any W_802f8 = Some (Jal 0 1360, 4%Z).
Proof. vm_refl. Qed.

Definition W_802fc : bv 32 := 0x025307b3.
Lemma F_802fc : fetch_word Ubsan.M.loaded_segments (0x802fc : word) = Some W_802fc.
Proof. vm_refl. Qed.
Lemma D_802fc : decode_any W_802fc = Some (Mul M_MUL 15 6 5, 4%Z).
Proof. vm_refl. Qed.

Definition W_80300 : bv 32 := 0x025306bb.
Lemma F_80300 : fetch_word Ubsan.M.loaded_segments (0x80300 : word) = Some W_80300.
Proof. vm_refl. Qed.
Lemma D_80300 : decode_any W_80300 = Some (Mul32 M_MUL 13 6 5, 4%Z).
Proof. vm_refl. Qed.

Definition W_80304 : bv 32 := 0x00f68463.
Lemma F_80304 : fetch_word Ubsan.M.loaded_segments (0x80304 : word) = Some W_80304.
Proof. vm_refl. Qed.
Lemma D_80304 : decode_any W_80304 = Some (Branch BC_EQ 13 15 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_80308 : bv 32 := 0x1ec0206f.
Lemma F_80308 : fetch_word Ubsan.M.loaded_segments (0x80308 : word) = Some W_80308.
Proof. vm_refl. Qed.
Lemma D_80308 : decode_any W_80308 = Some (Jal 0 8684, 4%Z).
Proof. vm_refl. Qed.

Definition W_8030c : bv 32 := 0x0007879b.
Lemma F_8030c : fetch_word Ubsan.M.loaded_segments (0x8030c : word) = Some W_8030c.
Proof. vm_refl. Qed.
Lemma D_8030c : decode_any W_8030c = Some (OpImm32 15 15 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_80310 : bv 32 := 0x00279413.
Lemma F_80310 : fetch_word Ubsan.M.loaded_segments (0x80310 : word) = Some W_80310.
Proof. vm_refl. Qed.
Lemma D_80310 : decode_any W_80310 = Some (ShiftImm ALU_SLL 8 15 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_80314 : bv 32 := 0x013406b3.
Lemma F_80314 : fetch_word Ubsan.M.loaded_segments (0x80314 : word) = Some W_80314.
Proof. vm_refl. Qed.
Lemma D_80314 : decode_any W_80314 = Some (Op ALU_ADD 13 8 19, 4%Z).
Proof. vm_refl. Qed.

Definition W_80318 : bv 32 := 0x01303833.
Lemma F_80318 : fetch_word Ubsan.M.loaded_segments (0x80318 : word) = Some W_80318.
Proof. vm_refl. Qed.
Lemma D_80318 : decode_any W_80318 = Some (Op ALU_SLTU 16 0 19, 4%Z).
Proof. vm_refl. Qed.

Definition W_8031c : bv 32 := 0x0016b893.
Lemma F_8031c : fetch_word Ubsan.M.loaded_segments (0x8031c : word) = Some W_8031c.
Proof. vm_refl. Qed.
Lemma D_8031c : decode_any W_8031c = Some (OpImm ALU_SLTU 17 13 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_80320 : bv 32 := 0x01181463.
Lemma F_80320 : fetch_word Ubsan.M.loaded_segments (0x80320 : word) = Some W_80320.
Proof. vm_refl. Qed.
Lemma D_80320 : decode_any W_80320 = Some (Branch BC_NE 16 17 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_80324 : bv 32 := 0x1d00206f.
Lemma F_80324 : fetch_word Ubsan.M.loaded_segments (0x80324 : word) = Some W_80324.
Proof. vm_refl. Qed.
Lemma D_80324 : decode_any W_80324 = Some (Jal 0 8656, 4%Z).
Proof. vm_refl. Qed.

Definition W_80328 : bv 32 := 0x0136b8b3.
Lemma F_80328 : fetch_word Ubsan.M.loaded_segments (0x80328 : word) = Some W_80328.
Proof. vm_refl. Qed.
Lemma D_80328 : decode_any W_80328 = Some (Op ALU_SLTU 17 13 19, 4%Z).
Proof. vm_refl. Qed.

Definition W_8032c : bv 32 := 0x0007a793.
Lemma F_8032c : fetch_word Ubsan.M.loaded_segments (0x8032c : word) = Some W_8032c.
Proof. vm_refl. Qed.
Lemma D_8032c : decode_any W_8032c = Some (OpImm ALU_SLT 15 15 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_80330 : bv 32 := 0x00f8c7b3.
Lemma F_80330 : fetch_word Ubsan.M.loaded_segments (0x80330 : word) = Some W_80330.
Proof. vm_refl. Qed.
Lemma D_80330 : decode_any W_80330 = Some (Op ALU_XOR 15 17 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_80334 : bv 32 := 0x0017c793.
Lemma F_80334 : fetch_word Ubsan.M.loaded_segments (0x80334 : word) = Some W_80334.
Proof. vm_refl. Qed.
Lemma D_80334 : decode_any W_80334 = Some (OpImm ALU_XOR 15 15 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_80338 : bv 32 := 0x00079463.
Lemma F_80338 : fetch_word Ubsan.M.loaded_segments (0x80338 : word) = Some W_80338.
Proof. vm_refl. Qed.
Lemma D_80338 : decode_any W_80338 = Some (Branch BC_NE 15 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_8033c : bv 32 := 0x1b80206f.
Lemma F_8033c : fetch_word Ubsan.M.loaded_segments (0x8033c : word) = Some W_8033c.
Proof. vm_refl. Qed.
Lemma D_8033c : decode_any W_8033c = Some (Jal 0 8632, 4%Z).
Proof. vm_refl. Qed.

Definition W_80340 : bv 32 := 0x005dd91b.
Lemma F_80340 : fetch_word Ubsan.M.loaded_segments (0x80340 : word) = Some W_80340.
Proof. vm_refl. Qed.
Lemma D_80340 : decode_any W_80340 = Some (ShiftImm32 ALU_SRL 18 27 5, 4%Z).
Proof. vm_refl. Qed.

Definition W_80344 : bv 32 := 0x00291913.
Lemma F_80344 : fetch_word Ubsan.M.loaded_segments (0x80344 : word) = Some W_80344.
Proof. vm_refl. Qed.
Lemma D_80344 : decode_any W_80344 = Some (ShiftImm ALU_SLL 18 18 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_80348 : bv 32 := 0x012688b3.
Lemma F_80348 : fetch_word Ubsan.M.loaded_segments (0x80348 : word) = Some W_80348.
Proof. vm_refl. Qed.
Lemma D_80348 : decode_any W_80348 = Some (Op ALU_ADD 17 13 18, 4%Z).
Proof. vm_refl. Qed.

Definition W_8034c : bv 32 := 0x00d8f463.
Lemma F_8034c : fetch_word Ubsan.M.loaded_segments (0x8034c : word) = Some W_8034c.
Proof. vm_refl. Qed.
Lemma D_8034c : decode_any W_8034c = Some (Branch BC_GEU 17 13 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_80350 : bv 32 := 0x1a40206f.
Lemma F_80350 : fetch_word Ubsan.M.loaded_segments (0x80350 : word) = Some W_80350.
Proof. vm_refl. Qed.
Lemma D_80350 : decode_any W_80350 = Some (Jal 0 8612, 4%Z).
Proof. vm_refl. Qed.

Definition W_80354 : bv 32 := 0x0018b693.
Lemma F_80354 : fetch_word Ubsan.M.loaded_segments (0x80354 : word) = Some W_80354.
Proof. vm_refl. Qed.
Lemma D_80354 : decode_any W_80354 = Some (OpImm ALU_SLTU 13 17 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_80358 : bv 32 := 0x00d846b3.
Lemma F_80358 : fetch_word Ubsan.M.loaded_segments (0x80358 : word) = Some W_80358.
Proof. vm_refl. Qed.
Lemma D_80358 : decode_any W_80358 = Some (Op ALU_XOR 13 16 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_8035c : bv 32 := 0x00069463.
Lemma F_8035c : fetch_word Ubsan.M.loaded_segments (0x8035c : word) = Some W_8035c.
Proof. vm_refl. Qed.
Lemma D_8035c : decode_any W_8035c = Some (Branch BC_NE 13 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_80360 : bv 32 := 0x1940206f.
Lemma F_80360 : fetch_word Ubsan.M.loaded_segments (0x80360 : word) = Some W_80360.
Proof. vm_refl. Qed.
Lemma D_80360 : decode_any W_80360 = Some (Jal 0 8596, 4%Z).
Proof. vm_refl. Qed.

Definition W_80364 : bv 32 := 0x027707b3.
Lemma F_80364 : fetch_word Ubsan.M.loaded_segments (0x80364 : word) = Some W_80364.
Proof. vm_refl. Qed.
Lemma D_80364 : decode_any W_80364 = Some (Mul M_MUL 15 14 7, 4%Z).
Proof. vm_refl. Qed.

Definition W_80368 : bv 32 := 0x027706bb.
Lemma F_80368 : fetch_word Ubsan.M.loaded_segments (0x80368 : word) = Some W_80368.
Proof. vm_refl. Qed.
Lemma D_80368 : decode_any W_80368 = Some (Mul32 M_MUL 13 14 7, 4%Z).
Proof. vm_refl. Qed.

Definition W_8036c : bv 32 := 0x00f68463.
Lemma F_8036c : fetch_word Ubsan.M.loaded_segments (0x8036c : word) = Some W_8036c.
Proof. vm_refl. Qed.
Lemma D_8036c : decode_any W_8036c = Some (Branch BC_EQ 13 15 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_80370 : bv 32 := 0x1840206f.
Lemma F_80370 : fetch_word Ubsan.M.loaded_segments (0x80370 : word) = Some W_80370.
Proof. vm_refl. Qed.
Lemma D_80370 : decode_any W_80370 = Some (Jal 0 8580, 4%Z).
Proof. vm_refl. Qed.

Definition W_80374 : bv 32 := 0x0007879b.
Lemma F_80374 : fetch_word Ubsan.M.loaded_segments (0x80374 : word) = Some W_80374.
Proof. vm_refl. Qed.
Lemma D_80374 : decode_any W_80374 = Some (OpImm32 15 15 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_80378 : bv 32 := 0x00279b13.
Lemma F_80378 : fetch_word Ubsan.M.loaded_segments (0x80378 : word) = Some W_80378.
Proof. vm_refl. Qed.
Lemma D_80378 : decode_any W_80378 = Some (ShiftImm ALU_SLL 22 15 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_8037c : bv 32 := 0x00ab06b3.
Lemma F_8037c : fetch_word Ubsan.M.loaded_segments (0x8037c : word) = Some W_8037c.
Proof. vm_refl. Qed.
Lemma D_8037c : decode_any W_8037c = Some (Op ALU_ADD 13 22 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_80380 : bv 32 := 0x00a032b3.
Lemma F_80380 : fetch_word Ubsan.M.loaded_segments (0x80380 : word) = Some W_80380.
Proof. vm_refl. Qed.
Lemma D_80380 : decode_any W_80380 = Some (Op ALU_SLTU 5 0 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_80384 : bv 32 := 0x0016b313.
Lemma F_80384 : fetch_word Ubsan.M.loaded_segments (0x80384 : word) = Some W_80384.
Proof. vm_refl. Qed.
Lemma D_80384 : decode_any W_80384 = Some (OpImm ALU_SLTU 6 13 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_80388 : bv 32 := 0x00629463.
Lemma F_80388 : fetch_word Ubsan.M.loaded_segments (0x80388 : word) = Some W_80388.
Proof. vm_refl. Qed.
Lemma D_80388 : decode_any W_80388 = Some (Branch BC_NE 5 6 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_8038c : bv 32 := 0x1680206f.
Lemma F_8038c : fetch_word Ubsan.M.loaded_segments (0x8038c : word) = Some W_8038c.
Proof. vm_refl. Qed.
Lemma D_8038c : decode_any W_8038c = Some (Jal 0 8552, 4%Z).
Proof. vm_refl. Qed.

Definition W_80390 : bv 32 := 0x00a6b333.
Lemma F_80390 : fetch_word Ubsan.M.loaded_segments (0x80390 : word) = Some W_80390.
Proof. vm_refl. Qed.
Lemma D_80390 : decode_any W_80390 = Some (Op ALU_SLTU 6 13 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_80394 : bv 32 := 0x0007a793.
Lemma F_80394 : fetch_word Ubsan.M.loaded_segments (0x80394 : word) = Some W_80394.
Proof. vm_refl. Qed.
Lemma D_80394 : decode_any W_80394 = Some (OpImm ALU_SLT 15 15 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_80398 : bv 32 := 0x00f347b3.
Lemma F_80398 : fetch_word Ubsan.M.loaded_segments (0x80398 : word) = Some W_80398.
Proof. vm_refl. Qed.
Lemma D_80398 : decode_any W_80398 = Some (Op ALU_XOR 15 6 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_8039c : bv 32 := 0x0017c793.
Lemma F_8039c : fetch_word Ubsan.M.loaded_segments (0x8039c : word) = Some W_8039c.
Proof. vm_refl. Qed.
Lemma D_8039c : decode_any W_8039c = Some (OpImm ALU_XOR 15 15 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_803a0 : bv 32 := 0x00079463.
Lemma F_803a0 : fetch_word Ubsan.M.loaded_segments (0x803a0 : word) = Some W_803a0.
Proof. vm_refl. Qed.
Lemma D_803a0 : decode_any W_803a0 = Some (Branch BC_NE 15 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_803a4 : bv 32 := 0x1500206f.
Lemma F_803a4 : fetch_word Ubsan.M.loaded_segments (0x803a4 : word) = Some W_803a4.
Proof. vm_refl. Qed.
Lemma D_803a4 : decode_any W_803a4 = Some (Jal 0 8528, 4%Z).
Proof. vm_refl. Qed.

Definition W_803a8 : bv 32 := 0x405cd79b.
Lemma F_803a8 : fetch_word Ubsan.M.loaded_segments (0x803a8 : word) = Some W_803a8.
Proof. vm_refl. Qed.
Lemma D_803a8 : decode_any W_803a8 = Some (ShiftImm32 ALU_SRA 15 25 5, 4%Z).
Proof. vm_refl. Qed.

Definition W_803ac : bv 32 := 0x00279b93.
Lemma F_803ac : fetch_word Ubsan.M.loaded_segments (0x803ac : word) = Some W_803ac.
Proof. vm_refl. Qed.
Lemma D_803ac : decode_any W_803ac = Some (ShiftImm ALU_SLL 23 15 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_803b0 : bv 32 := 0x017683b3.
Lemma F_803b0 : fetch_word Ubsan.M.loaded_segments (0x803b0 : word) = Some W_803b0.
Proof. vm_refl. Qed.
Lemma D_803b0 : decode_any W_803b0 = Some (Op ALU_ADD 7 13 23, 4%Z).
Proof. vm_refl. Qed.

Definition W_803b4 : bv 32 := 0x0013b313.
Lemma F_803b4 : fetch_word Ubsan.M.loaded_segments (0x803b4 : word) = Some W_803b4.
Proof. vm_refl. Qed.
Lemma D_803b4 : decode_any W_803b4 = Some (OpImm ALU_SLTU 6 7 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_803b8 : bv 32 := 0x00629463.
Lemma F_803b8 : fetch_word Ubsan.M.loaded_segments (0x803b8 : word) = Some W_803b8.
Proof. vm_refl. Qed.
Lemma D_803b8 : decode_any W_803b8 = Some (Branch BC_NE 5 6 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_803bc : bv 32 := 0x1380206f.
Lemma F_803bc : fetch_word Ubsan.M.loaded_segments (0x803bc : word) = Some W_803bc.
Proof. vm_refl. Qed.
Lemma D_803bc : decode_any W_803bc = Some (Jal 0 8504, 4%Z).
Proof. vm_refl. Qed.

Definition W_803c0 : bv 32 := 0x00d3b6b3.
Lemma F_803c0 : fetch_word Ubsan.M.loaded_segments (0x803c0 : word) = Some W_803c0.
Proof. vm_refl. Qed.
Lemma D_803c0 : decode_any W_803c0 = Some (Op ALU_SLTU 13 7 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_803c4 : bv 32 := 0x0007a793.
Lemma F_803c4 : fetch_word Ubsan.M.loaded_segments (0x803c4 : word) = Some W_803c4.
Proof. vm_refl. Qed.
Lemma D_803c4 : decode_any W_803c4 = Some (OpImm ALU_SLT 15 15 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_803c8 : bv 32 := 0x00f6c6b3.
Lemma F_803c8 : fetch_word Ubsan.M.loaded_segments (0x803c8 : word) = Some W_803c8.
Proof. vm_refl. Qed.
Lemma D_803c8 : decode_any W_803c8 = Some (Op ALU_XOR 13 13 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_803cc : bv 32 := 0x0016c693.
Lemma F_803cc : fetch_word Ubsan.M.loaded_segments (0x803cc : word) = Some W_803cc.
Proof. vm_refl. Qed.
Lemma D_803cc : decode_any W_803cc = Some (OpImm ALU_XOR 13 13 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_803d0 : bv 32 := 0x00069463.
Lemma F_803d0 : fetch_word Ubsan.M.loaded_segments (0x803d0 : word) = Some W_803d0.
Proof. vm_refl. Qed.
Lemma D_803d0 : decode_any W_803d0 = Some (Branch BC_NE 13 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_803d4 : bv 32 := 0x1200206f.
Lemma F_803d4 : fetch_word Ubsan.M.loaded_segments (0x803d4 : word) = Some W_803d4.
Proof. vm_refl. Qed.
Lemma D_803d4 : decode_any W_803d4 = Some (Jal 0 8480, 4%Z).
Proof. vm_refl. Qed.

Definition W_803d8 : bv 32 := 0xfff9e697.
Lemma F_803d8 : fetch_word Ubsan.M.loaded_segments (0x803d8 : word) = Some W_803d8.
Proof. vm_refl. Qed.
Lemma D_803d8 : decode_any W_803d8 = Some (Auipc 13 1048478, 4%Z).
Proof. vm_refl. Qed.

Definition W_803dc : bv 32 := 0xfff58793.
Lemma F_803dc : fetch_word Ubsan.M.loaded_segments (0x803dc : word) = Some W_803dc.
Proof. vm_refl. Qed.
Lemma D_803dc : decode_any W_803dc = Some (OpImm ALU_ADD 15 11 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_803e0 : bv 32 := 0x00d00313.
Lemma F_803e0 : fetch_word Ubsan.M.loaded_segments (0x803e0 : word) = Some W_803e0.
Proof. vm_refl. Qed.
Lemma D_803e0 : decode_any W_803e0 = Some (OpImm ALU_ADD 6 0 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_803e4 : bv 32 := 0x13968693.
Lemma F_803e4 : fetch_word Ubsan.M.loaded_segments (0x803e4 : word) = Some W_803e4.
Proof. vm_refl. Qed.
Lemma D_803e4 : decode_any W_803e4 = Some (OpImm ALU_ADD 13 13 313, 4%Z).
Proof. vm_refl. Qed.

Definition W_803e8 : bv 32 := 0x00f37463.
Lemma F_803e8 : fetch_word Ubsan.M.loaded_segments (0x803e8 : word) = Some W_803e8.
Proof. vm_refl. Qed.
Lemma D_803e8 : decode_any W_803e8 = Some (Branch BC_GEU 6 15 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_803ec : bv 32 := 0x0100106f.
Lemma F_803ec : fetch_word Ubsan.M.loaded_segments (0x803ec : word) = Some W_803ec.
Proof. vm_refl. Qed.
Lemma D_803ec : decode_any W_803ec = Some (Jal 0 4112, 4%Z).
Proof. vm_refl. Qed.

Definition W_803f0 : bv 32 := 0x00279793.
Lemma F_803f0 : fetch_word Ubsan.M.loaded_segments (0x803f0 : word) = Some W_803f0.
Proof. vm_refl. Qed.
Lemma D_803f0 : decode_any W_803f0 = Some (ShiftImm ALU_SLL 15 15 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_803f4 : bv 32 := 0xfff9f317.
Lemma F_803f4 : fetch_word Ubsan.M.loaded_segments (0x803f4 : word) = Some W_803f4.
Proof. vm_refl. Qed.
Lemma D_803f4 : decode_any W_803f4 = Some (Auipc 6 1048479, 4%Z).
Proof. vm_refl. Qed.

Definition W_803f8 : bv 32 := 0x01430313.
Lemma F_803f8 : fetch_word Ubsan.M.loaded_segments (0x803f8 : word) = Some W_803f8.
Proof. vm_refl. Qed.
Lemma D_803f8 : decode_any W_803f8 = Some (OpImm ALU_ADD 6 6 20, 4%Z).
Proof. vm_refl. Qed.

Definition W_803fc : bv 32 := 0x006787b3.
Lemma F_803fc : fetch_word Ubsan.M.loaded_segments (0x803fc : word) = Some W_803fc.
Proof. vm_refl. Qed.
Lemma D_803fc : decode_any W_803fc = Some (Op ALU_ADD 15 15 6, 4%Z).
Proof. vm_refl. Qed.

Definition W_80400 : bv 32 := 0x0007a783.
Lemma F_80400 : fetch_word Ubsan.M.loaded_segments (0x80400 : word) = Some W_80400.
Proof. vm_refl. Qed.
Lemma D_80400 : decode_any W_80400 = Some (Load SZ4 true 15 15 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_80404 : bv 32 := 0x006787b3.
Lemma F_80404 : fetch_word Ubsan.M.loaded_segments (0x80404 : word) = Some W_80404.
Proof. vm_refl. Qed.
Lemma D_80404 : decode_any W_80404 = Some (Op ALU_ADD 15 15 6, 4%Z).
Proof. vm_refl. Qed.

Definition W_80408 : bv 32 := 0x00078067.
Lemma F_80408 : fetch_word Ubsan.M.loaded_segments (0x80408 : word) = Some W_80408.
Proof. vm_refl. Qed.
Lemma D_80408 : decode_any W_80408 = Some (Jalr 0 15 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_8040c : bv 32 := 0x00000593.
Lemma F_8040c : fetch_word Ubsan.M.loaded_segments (0x8040c : word) = Some W_8040c.
Proof. vm_refl. Qed.
Lemma D_8040c : decode_any W_8040c = Some (OpImm ALU_ADD 11 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_80410 : bv 32 := 0x00000693.
Lemma F_80410 : fetch_word Ubsan.M.loaded_segments (0x80410 : word) = Some W_80410.
Proof. vm_refl. Qed.
Lemma D_80410 : decode_any W_80410 = Some (OpImm ALU_ADD 13 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_80414 : bv 32 := 0x00000c93.
Lemma F_80414 : fetch_word Ubsan.M.loaded_segments (0x80414 : word) = Some W_80414.
Proof. vm_refl. Qed.
Lemma D_80414 : decode_any W_80414 = Some (OpImm ALU_ADD 25 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_80418 : bv 32 := 0x015a07b3.
Lemma F_80418 : fetch_word Ubsan.M.loaded_segments (0x80418 : word) = Some W_80418.
Proof. vm_refl. Qed.
Lemma D_80418 : decode_any W_80418 = Some (Op ALU_ADD 15 20 21, 4%Z).
Proof. vm_refl. Qed.

Definition W_8041c : bv 32 := 0xfffe4a13.
Lemma F_8041c : fetch_word Ubsan.M.loaded_segments (0x8041c : word) = Some W_8041c.
Proof. vm_refl. Qed.
Lemma D_8041c : decode_any W_8041c = Some (OpImm ALU_XOR 20 28 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_80420 : bv 32 := 0x016b8b33.
Lemma F_80420 : fetch_word Ubsan.M.loaded_segments (0x80420 : word) = Some W_80420.
Proof. vm_refl. Qed.
Lemma D_80420 : decode_any W_80420 = Some (Op ALU_ADD 22 23 22, 4%Z).
Proof. vm_refl. Qed.

Definition W_80424 : bv 32 := 0x0039fa93.
Lemma F_80424 : fetch_word Ubsan.M.loaded_segments (0x80424 : word) = Some W_80424.
Proof. vm_refl. Qed.
Lemma D_80424 : decode_any W_80424 = Some (OpImm ALU_AND 21 19 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_80428 : bv 32 := 0x00890433.
Lemma F_80428 : fetch_word Ubsan.M.loaded_segments (0x80428 : word) = Some W_80428.
Proof. vm_refl. Qed.
Lemma D_80428 : decode_any W_80428 = Some (Op ALU_ADD 8 18 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_8042c : bv 32 := 0x43ffd313.
Lemma F_8042c : fetch_word Ubsan.M.loaded_segments (0x8042c : word) = Some W_8042c.
Proof. vm_refl. Qed.
Lemma D_8042c : decode_any W_8042c = Some (ShiftImm ALU_SRA 6 31 63, 4%Z).
Proof. vm_refl. Qed.

Definition W_80430 : bv 32 := 0x01f37333.
Lemma F_80430 : fetch_word Ubsan.M.loaded_segments (0x80430 : word) = Some W_80430.
Proof. vm_refl. Qed.
Lemma D_80430 : decode_any W_80430 = Some (Op ALU_AND 6 6 31, 4%Z).
Proof. vm_refl. Qed.

Definition W_80434 : bv 32 := 0x00357f93.
Lemma F_80434 : fetch_word Ubsan.M.loaded_segments (0x80434 : word) = Some W_80434.
Proof. vm_refl. Qed.
Lemma D_80434 : decode_any W_80434 = Some (OpImm ALU_AND 31 10 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_80438 : bv 32 := 0x41be893b.
Lemma F_80438 : fetch_word Ubsan.M.loaded_segments (0x80438 : word) = Some W_80438.
Proof. vm_refl. Qed.
Lemma D_80438 : decode_any W_80438 = Some (Op32 ALU_SUB 18 29 27, 4%Z).
Proof. vm_refl. Qed.

Definition W_8043c : bv 32 := 0x41e787bb.
Lemma F_8043c : fetch_word Ubsan.M.loaded_segments (0x8043c : word) = Some W_8043c.
Proof. vm_refl. Qed.
Lemma D_8043c : decode_any W_8043c = Some (Op32 ALU_SUB 15 15 30, 4%Z).
Proof. vm_refl. Qed.

Definition W_80440 : bv 32 := 0x02000f13.
Lemma F_80440 : fetch_word Ubsan.M.loaded_segments (0x80440 : word) = Some W_80440.
Proof. vm_refl. Qed.
Lemma D_80440 : decode_any W_80440 = Some (OpImm ALU_ADD 30 0 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_80444 : bv 32 := 0x01650533.
Lemma F_80444 : fetch_word Ubsan.M.loaded_segments (0x80444 : word) = Some W_80444.
Proof. vm_refl. Qed.
Lemma D_80444 : decode_any W_80444 = Some (Op ALU_ADD 10 10 22, 4%Z).
Proof. vm_refl. Qed.

Definition W_80448 : bv 32 := 0x008989b3.
Lemma F_80448 : fetch_word Ubsan.M.loaded_segments (0x80448 : word) = Some W_80448.
Proof. vm_refl. Qed.
Lemma D_80448 : decode_any W_80448 = Some (Op ALU_ADD 19 19 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_8044c : bv 32 := 0x006787b3.
Lemma F_8044c : fetch_word Ubsan.M.loaded_segments (0x8044c : word) = Some W_8044c.
Proof. vm_refl. Qed.
Lemma D_8044c : decode_any W_8044c = Some (Op ALU_ADD 15 15 6, 4%Z).
Proof. vm_refl. Qed.

Definition W_80450 : bv 32 := 0x41d787bb.
Lemma F_80450 : fetch_word Ubsan.M.loaded_segments (0x80450 : word) = Some W_80450.
Proof. vm_refl. Qed.
Lemma D_80450 : decode_any W_80450 = Some (Op32 ALU_SUB 15 15 29, 4%Z).
Proof. vm_refl. Qed.

Definition W_80454 : bv 32 := 0x43f7d313.
Lemma F_80454 : fetch_word Ubsan.M.loaded_segments (0x80454 : word) = Some W_80454.
Proof. vm_refl. Qed.
Lemma D_80454 : decode_any W_80454 = Some (ShiftImm ALU_SRA 6 15 63, 4%Z).
Proof. vm_refl. Qed.

Definition W_80458 : bv 32 := 0x00f377b3.
Lemma F_80458 : fetch_word Ubsan.M.loaded_segments (0x80458 : word) = Some W_80458.
Proof. vm_refl. Qed.
Lemma D_80458 : decode_any W_80458 = Some (Op ALU_AND 15 6 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_8045c : bv 32 := 0x00f907b3.
Lemma F_8045c : fetch_word Ubsan.M.loaded_segments (0x8045c : word) = Some W_8045c.
Proof. vm_refl. Qed.
Lemma D_8045c : decode_any W_8045c = Some (Op ALU_ADD 15 18 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_80460 : bv 32 := 0x0057d79b.
Lemma F_80460 : fetch_word Ubsan.M.loaded_segments (0x80460 : word) = Some W_80460.
Proof. vm_refl. Qed.
Lemma D_80460 : decode_any W_80460 = Some (ShiftImm32 ALU_SRL 15 15 5, 4%Z).
Proof. vm_refl. Qed.

Definition W_80464 : bv 32 := 0x40f00eb3.
Lemma F_80464 : fetch_word Ubsan.M.loaded_segments (0x80464 : word) = Some W_80464.
Proof. vm_refl. Qed.
Lemma D_80464 : decode_any W_80464 = Some (Op ALU_SUB 29 0 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_80468 : bv 32 := 0xffb00413.
Lemma F_80468 : fetch_word Ubsan.M.loaded_segments (0x80468 : word) = Some W_80468.
Proof. vm_refl. Qed.
Lemma D_80468 : decode_any W_80468 = Some (OpImm ALU_ADD 8 0 4091, 4%Z).
Proof. vm_refl. Qed.

Definition W_8046c : bv 32 := 0x05813083.
Lemma F_8046c : fetch_word Ubsan.M.loaded_segments (0x8046c : word) = Some W_8046c.
Proof. vm_refl. Qed.
Lemma D_8046c : decode_any W_8046c = Some (Load SZ8 true 1 2 88, 4%Z).
Proof. vm_refl. Qed.

Definition W_80470 : bv 32 := 0x03c0006f.
Lemma F_80470 : fetch_word Ubsan.M.loaded_segments (0x80470 : word) = Some W_80470.
Proof. vm_refl. Qed.
Lemma D_80470 : decode_any W_80470 = Some (Jal 0 60, 4%Z).
Proof. vm_refl. Qed.

Definition W_80474 : bv 32 := 0x00092303.
Lemma F_80474 : fetch_word Ubsan.M.loaded_segments (0x80474 : word) = Some W_80474.
Proof. vm_refl. Qed.
Lemma D_80474 : decode_any W_80474 = Some (Load SZ4 true 6 18 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_80478 : bv 32 := 0x0007a783.
Lemma F_80478 : fetch_word Ubsan.M.loaded_segments (0x80478 : word) = Some W_80478.
Proof. vm_refl. Qed.
Lemma D_80478 : decode_any W_80478 = Some (Load SZ4 true 15 15 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_8047c : bv 32 := 0x01437b33.
Lemma F_8047c : fetch_word Ubsan.M.loaded_segments (0x8047c : word) = Some W_8047c.
Proof. vm_refl. Qed.
Lemma D_8047c : decode_any W_8047c = Some (Op ALU_AND 22 6 20, 4%Z).
Proof. vm_refl. Qed.

Definition W_80480 : bv 32 := 0x0067e7b3.
Lemma F_80480 : fetch_word Ubsan.M.loaded_segments (0x80480 : word) = Some W_80480.
Proof. vm_refl. Qed.
Lemma D_80480 : decode_any W_80480 = Some (Op ALU_OR 15 15 6, 4%Z).
Proof. vm_refl. Qed.

Definition W_80484 : bv 32 := 0xfff7c793.
Lemma F_80484 : fetch_word Ubsan.M.loaded_segments (0x80484 : word) = Some W_80484.
Proof. vm_refl. Qed.
Lemma D_80484 : decode_any W_80484 = Some (OpImm ALU_XOR 15 15 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_80488 : bv 32 := 0x00fe77b3.
Lemma F_80488 : fetch_word Ubsan.M.loaded_segments (0x80488 : word) = Some W_80488.
Proof. vm_refl. Qed.
Lemma D_80488 : decode_any W_80488 = Some (Op ALU_AND 15 28 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_8048c : bv 32 := 0x0167e7b3.
Lemma F_8048c : fetch_word Ubsan.M.loaded_segments (0x8048c : word) = Some W_8048c.
Proof. vm_refl. Qed.
Lemma D_8048c : decode_any W_8048c = Some (Op ALU_OR 15 15 22, 4%Z).
Proof. vm_refl. Qed.

Definition W_80490 : bv 32 := 0x00f92023.
Lemma F_80490 : fetch_word Ubsan.M.loaded_segments (0x80490 : word) = Some W_80490.
Proof. vm_refl. Qed.
Lemma D_80490 : decode_any W_80490 = Some (Store SZ4 18 15 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_80494 : bv 32 := 0x001c8c9b.
Lemma F_80494 : fetch_word Ubsan.M.loaded_segments (0x80494 : word) = Some W_80494.
Proof. vm_refl. Qed.
Lemma D_80494 : decode_any W_80494 = Some (OpImm32 25 25 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_80498 : bv 32 := 0x00e686bb.
Lemma F_80498 : fetch_word Ubsan.M.loaded_segments (0x80498 : word) = Some W_80498.
Proof. vm_refl. Qed.
Lemma D_80498 : decode_any W_80498 = Some (Op32 ALU_ADD 13 13 14, 4%Z).
Proof. vm_refl. Qed.

Definition W_8049c : bv 32 := 0x001585bb.
Lemma F_8049c : fetch_word Ubsan.M.loaded_segments (0x8049c : word) = Some W_8049c.
Proof. vm_refl. Qed.
Lemma D_8049c : decode_any W_8049c = Some (Op32 ALU_ADD 11 11 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_804a0 : bv 32 := 0x08013783.
Lemma F_804a0 : fetch_word Ubsan.M.loaded_segments (0x804a0 : word) = Some W_804a0.
Proof. vm_refl. Qed.
Lemma D_804a0 : decode_any W_804a0 = Some (Load SZ8 true 15 2 128, 4%Z).
Proof. vm_refl. Qed.

Definition W_804a4 : bv 32 := 0x00fc9463.
Lemma F_804a4 : fetch_word Ubsan.M.loaded_segments (0x804a4 : word) = Some W_804a4.
Proof. vm_refl. Qed.
Lemma D_804a4 : decode_any W_804a4 = Some (Branch BC_NE 25 15 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_804a8 : bv 32 := 0x1100706f.
Lemma F_804a8 : fetch_word Ubsan.M.loaded_segments (0x804a8 : word) = Some W_804a8.
Proof. vm_refl. Qed.
Lemma D_804a8 : decode_any W_804a8 = Some (Jal 0 28944, 4%Z).
Proof. vm_refl. Qed.

Definition W_804ac : bv 32 := 0x021c8333.
Lemma F_804ac : fetch_word Ubsan.M.loaded_segments (0x804ac : word) = Some W_804ac.
Proof. vm_refl. Qed.
Lemma D_804ac : decode_any W_804ac = Some (Mul M_MUL 6 25 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_804b0 : bv 32 := 0x021c87bb.
Lemma F_804b0 : fetch_word Ubsan.M.loaded_segments (0x804b0 : word) = Some W_804b0.
Proof. vm_refl. Qed.
Lemma D_804b0 : decode_any W_804b0 = Some (Mul32 M_MUL 15 25 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_804b4 : bv 32 := 0x00678463.
Lemma F_804b4 : fetch_word Ubsan.M.loaded_segments (0x804b4 : word) = Some W_804b4.
Proof. vm_refl. Qed.
Lemma D_804b4 : decode_any W_804b4 = Some (Branch BC_EQ 15 6 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_804b8 : bv 32 := 0x03c0206f.
Lemma F_804b8 : fetch_word Ubsan.M.loaded_segments (0x804b8 : word) = Some W_804b8.
Proof. vm_refl. Qed.
Lemma D_804b8 : decode_any W_804b8 = Some (Jal 0 8252, 4%Z).
Proof. vm_refl. Qed.

Definition W_804bc : bv 32 := 0x0003031b.
Lemma F_804bc : fetch_word Ubsan.M.loaded_segments (0x804bc : word) = Some W_804bc.
Proof. vm_refl. Qed.
Lemma D_804bc : decode_any W_804bc = Some (OpImm32 6 6 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_804c0 : bv 32 := 0x00231793.
Lemma F_804c0 : fetch_word Ubsan.M.loaded_segments (0x804c0 : word) = Some W_804c0.
Proof. vm_refl. Qed.
Lemma D_804c0 : decode_any W_804c0 = Some (ShiftImm ALU_SLL 15 6 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_804c4 : bv 32 := 0x00f887b3.
Lemma F_804c4 : fetch_word Ubsan.M.loaded_segments (0x804c4 : word) = Some W_804c4.
Proof. vm_refl. Qed.
Lemma D_804c4 : decode_any W_804c4 = Some (Op ALU_ADD 15 17 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_804c8 : bv 32 := 0x0017b913.
Lemma F_804c8 : fetch_word Ubsan.M.loaded_segments (0x804c8 : word) = Some W_804c8.
Proof. vm_refl. Qed.
Lemma D_804c8 : decode_any W_804c8 = Some (OpImm ALU_SLTU 18 15 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_804cc : bv 32 := 0x01281463.
Lemma F_804cc : fetch_word Ubsan.M.loaded_segments (0x804cc : word) = Some W_804cc.
Proof. vm_refl. Qed.
Lemma D_804cc : decode_any W_804cc = Some (Branch BC_NE 16 18 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_804d0 : bv 32 := 0x0240206f.
Lemma F_804d0 : fetch_word Ubsan.M.loaded_segments (0x804d0 : word) = Some W_804d0.
Proof. vm_refl. Qed.
Lemma D_804d0 : decode_any W_804d0 = Some (Jal 0 8228, 4%Z).
Proof. vm_refl. Qed.

Definition W_804d4 : bv 32 := 0x0117b933.
Lemma F_804d4 : fetch_word Ubsan.M.loaded_segments (0x804d4 : word) = Some W_804d4.
Proof. vm_refl. Qed.
Lemma D_804d4 : decode_any W_804d4 = Some (Op ALU_SLTU 18 15 17, 4%Z).
Proof. vm_refl. Qed.

Definition W_804d8 : bv 32 := 0x00032313.
Lemma F_804d8 : fetch_word Ubsan.M.loaded_segments (0x804d8 : word) = Some W_804d8.
Proof. vm_refl. Qed.
Lemma D_804d8 : decode_any W_804d8 = Some (OpImm ALU_SLT 6 6 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_804dc : bv 32 := 0x00694333.
Lemma F_804dc : fetch_word Ubsan.M.loaded_segments (0x804dc : word) = Some W_804dc.
Proof. vm_refl. Qed.
Lemma D_804dc : decode_any W_804dc = Some (Op ALU_XOR 6 18 6, 4%Z).
Proof. vm_refl. Qed.

Definition W_804e0 : bv 32 := 0x00134313.
Lemma F_804e0 : fetch_word Ubsan.M.loaded_segments (0x804e0 : word) = Some W_804e0.
Proof. vm_refl. Qed.
Lemma D_804e0 : decode_any W_804e0 = Some (OpImm ALU_XOR 6 6 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_804e4 : bv 32 := 0x00031463.
Lemma F_804e4 : fetch_word Ubsan.M.loaded_segments (0x804e4 : word) = Some W_804e4.
Proof. vm_refl. Qed.
Lemma D_804e4 : decode_any W_804e4 = Some (Branch BC_NE 6 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_804e8 : bv 32 := 0x00c0206f.
Lemma F_804e8 : fetch_word Ubsan.M.loaded_segments (0x804e8 : word) = Some W_804e8.
Proof. vm_refl. Qed.
Lemma D_804e8 : decode_any W_804e8 = Some (Jal 0 8204, 4%Z).
Proof. vm_refl. Qed.

Definition W_804ec : bv 32 := 0x02ec8333.
Lemma F_804ec : fetch_word Ubsan.M.loaded_segments (0x804ec : word) = Some W_804ec.
Proof. vm_refl. Qed.
Lemma D_804ec : decode_any W_804ec = Some (Mul M_MUL 6 25 14, 4%Z).
Proof. vm_refl. Qed.

Definition W_804f0 : bv 32 := 0x02ec893b.
Lemma F_804f0 : fetch_word Ubsan.M.loaded_segments (0x804f0 : word) = Some W_804f0.
Proof. vm_refl. Qed.
Lemma D_804f0 : decode_any W_804f0 = Some (Mul32 M_MUL 18 25 14, 4%Z).
Proof. vm_refl. Qed.

Definition W_804f4 : bv 32 := 0x00690463.
Lemma F_804f4 : fetch_word Ubsan.M.loaded_segments (0x804f4 : word) = Some W_804f4.
Proof. vm_refl. Qed.
Lemma D_804f4 : decode_any W_804f4 = Some (Branch BC_EQ 18 6 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_804f8 : bv 32 := 0x7fd0106f.
Lemma F_804f8 : fetch_word Ubsan.M.loaded_segments (0x804f8 : word) = Some W_804f8.
Proof. vm_refl. Qed.
Lemma D_804f8 : decode_any W_804f8 = Some (Jal 0 8188, 4%Z).
Proof. vm_refl. Qed.

Definition W_804fc : bv 32 := 0x0003031b.
Lemma F_804fc : fetch_word Ubsan.M.loaded_segments (0x804fc : word) = Some W_804fc.
Proof. vm_refl. Qed.
Lemma D_804fc : decode_any W_804fc = Some (OpImm32 6 6 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_80500 : bv 32 := 0x00231913.
Lemma F_80500 : fetch_word Ubsan.M.loaded_segments (0x80500 : word) = Some W_80500.
Proof. vm_refl. Qed.
Lemma D_80500 : decode_any W_80500 = Some (ShiftImm ALU_SLL 18 6 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_80504 : bv 32 := 0x00790933.
Lemma F_80504 : fetch_word Ubsan.M.loaded_segments (0x80504 : word) = Some W_80504.
Proof. vm_refl. Qed.
Lemma D_80504 : decode_any W_80504 = Some (Op ALU_ADD 18 18 7, 4%Z).
Proof. vm_refl. Qed.

Definition W_80508 : bv 32 := 0x00193b13.
Lemma F_80508 : fetch_word Ubsan.M.loaded_segments (0x80508 : word) = Some W_80508.
Proof. vm_refl. Qed.
Lemma D_80508 : decode_any W_80508 = Some (OpImm ALU_SLTU 22 18 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_8050c : bv 32 := 0x01629463.
Lemma F_8050c : fetch_word Ubsan.M.loaded_segments (0x8050c : word) = Some W_8050c.
Proof. vm_refl. Qed.
Lemma D_8050c : decode_any W_8050c = Some (Branch BC_NE 5 22 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_80510 : bv 32 := 0x7e50106f.
Lemma F_80510 : fetch_word Ubsan.M.loaded_segments (0x80510 : word) = Some W_80510.
Proof. vm_refl. Qed.
Lemma D_80510 : decode_any W_80510 = Some (Jal 0 8164, 4%Z).
Proof. vm_refl. Qed.

Definition W_80514 : bv 32 := 0x00793b33.
Lemma F_80514 : fetch_word Ubsan.M.loaded_segments (0x80514 : word) = Some W_80514.
Proof. vm_refl. Qed.
Lemma D_80514 : decode_any W_80514 = Some (Op ALU_SLTU 22 18 7, 4%Z).
Proof. vm_refl. Qed.

Definition W_80518 : bv 32 := 0x00032313.
Lemma F_80518 : fetch_word Ubsan.M.loaded_segments (0x80518 : word) = Some W_80518.
Proof. vm_refl. Qed.
Lemma D_80518 : decode_any W_80518 = Some (OpImm ALU_SLT 6 6 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_8051c : bv 32 := 0x006b4333.
Lemma F_8051c : fetch_word Ubsan.M.loaded_segments (0x8051c : word) = Some W_8051c.
Proof. vm_refl. Qed.
Lemma D_8051c : decode_any W_8051c = Some (Op ALU_XOR 6 22 6, 4%Z).
Proof. vm_refl. Qed.

Definition W_80520 : bv 32 := 0x00134313.
Lemma F_80520 : fetch_word Ubsan.M.loaded_segments (0x80520 : word) = Some W_80520.
Proof. vm_refl. Qed.
Lemma D_80520 : decode_any W_80520 = Some (OpImm ALU_XOR 6 6 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_80524 : bv 32 := 0x00031463.
Lemma F_80524 : fetch_word Ubsan.M.loaded_segments (0x80524 : word) = Some W_80524.
Proof. vm_refl. Qed.
Lemma D_80524 : decode_any W_80524 = Some (Branch BC_NE 6 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_80528 : bv 32 := 0x7cd0106f.
Lemma F_80528 : fetch_word Ubsan.M.loaded_segments (0x80528 : word) = Some W_80528.
Proof. vm_refl. Qed.
Lemma D_80528 : decode_any W_80528 = Some (Jal 0 8140, 4%Z).
Proof. vm_refl. Qed.

Definition W_8052c : bv 32 := 0x07e4ee63.
Lemma F_8052c : fetch_word Ubsan.M.loaded_segments (0x8052c : word) = Some W_8052c.
Proof. vm_refl. Qed.
Lemma D_8052c : decode_any W_8052c = Some (Branch BC_LTU 9 30 124, 4%Z).
Proof. vm_refl. Qed.

Definition W_80530 : bv 32 := 0x000a8463.
Lemma F_80530 : fetch_word Ubsan.M.loaded_segments (0x80530 : word) = Some W_80530.
Proof. vm_refl. Qed.
Lemma D_80530 : decode_any W_80530 = Some (Branch BC_EQ 21 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_80534 : bv 32 := 0x7c10106f.
Lemma F_80534 : fetch_word Ubsan.M.loaded_segments (0x80534 : word) = Some W_80534.
Proof. vm_refl. Qed.
Lemma D_80534 : decode_any W_80534 = Some (Jal 0 8128, 4%Z).
Proof. vm_refl. Qed.

Definition W_80538 : bv 32 := 0x00000793.
Lemma F_80538 : fetch_word Ubsan.M.loaded_segments (0x80538 : word) = Some W_80538.
Proof. vm_refl. Qed.
Lemma D_80538 : decode_any W_80538 = Some (OpImm ALU_ADD 15 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_8053c : bv 32 := 0x00269913.
Lemma F_8053c : fetch_word Ubsan.M.loaded_segments (0x8053c : word) = Some W_8053c.
Proof. vm_refl. Qed.
Lemma D_8053c : decode_any W_8053c = Some (ShiftImm ALU_SLL 18 13 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_80540 : bv 32 := 0x00259b13.
Lemma F_80540 : fetch_word Ubsan.M.loaded_segments (0x80540 : word) = Some W_80540.
Proof. vm_refl. Qed.
Lemma D_80540 : decode_any W_80540 = Some (ShiftImm ALU_SLL 22 11 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_80544 : bv 32 := 0x01250933.
Lemma F_80544 : fetch_word Ubsan.M.loaded_segments (0x80544 : word) = Some W_80544.
Proof. vm_refl. Qed.
Lemma D_80544 : decode_any W_80544 = Some (Op ALU_ADD 18 10 18, 4%Z).
Proof. vm_refl. Qed.

Definition W_80548 : bv 32 := 0x01698b33.
Lemma F_80548 : fetch_word Ubsan.M.loaded_segments (0x80548 : word) = Some W_80548.
Proof. vm_refl. Qed.
Lemma D_80548 : decode_any W_80548 = Some (Op ALU_ADD 22 19 22, 4%Z).
Proof. vm_refl. Qed.

Definition W_8054c : bv 32 := 0x000e8b93.
Lemma F_8054c : fetch_word Ubsan.M.loaded_segments (0x8054c : word) = Some W_8054c.
Proof. vm_refl. Qed.
Lemma D_8054c : decode_any W_8054c = Some (OpImm ALU_ADD 23 29 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_80550 : bv 32 := 0x00fb0333.
Lemma F_80550 : fetch_word Ubsan.M.loaded_segments (0x80550 : word) = Some W_80550.
Proof. vm_refl. Qed.
Lemma D_80550 : decode_any W_80550 = Some (Op ALU_ADD 6 22 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_80554 : bv 32 := 0x00031463.
Lemma F_80554 : fetch_word Ubsan.M.loaded_segments (0x80554 : word) = Some W_80554.
Proof. vm_refl. Qed.
Lemma D_80554 : decode_any W_80554 = Some (Branch BC_NE 6 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_80558 : bv 32 := 0x79d0106f.
Lemma F_80558 : fetch_word Ubsan.M.loaded_segments (0x80558 : word) = Some W_80558.
Proof. vm_refl. Qed.
Lemma D_80558 : decode_any W_80558 = Some (Jal 0 8092, 4%Z).
Proof. vm_refl. Qed.

Definition W_8055c : bv 32 := 0x000f8463.
Lemma F_8055c : fetch_word Ubsan.M.loaded_segments (0x8055c : word) = Some W_8055c.
Proof. vm_refl. Qed.
Lemma D_8055c : decode_any W_8055c = Some (Branch BC_EQ 31 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_80560 : bv 32 := 0x7950106f.
Lemma F_80560 : fetch_word Ubsan.M.loaded_segments (0x80560 : word) = Some W_80560.
Proof. vm_refl. Qed.
Lemma D_80560 : decode_any W_80560 = Some (Jal 0 8084, 4%Z).
Proof. vm_refl. Qed.

Definition W_80564 : bv 32 := 0x00f90c33.
Lemma F_80564 : fetch_word Ubsan.M.loaded_segments (0x80564 : word) = Some W_80564.
Proof. vm_refl. Qed.
Lemma D_80564 : decode_any W_80564 = Some (Op ALU_ADD 24 18 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_80568 : bv 32 := 0x000c1463.
Lemma F_80568 : fetch_word Ubsan.M.loaded_segments (0x80568 : word) = Some W_80568.
Proof. vm_refl. Qed.
Lemma D_80568 : decode_any W_80568 = Some (Branch BC_NE 24 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_8056c : bv 32 := 0x7890106f.
Lemma F_8056c : fetch_word Ubsan.M.loaded_segments (0x8056c : word) = Some W_8056c.
Proof. vm_refl. Qed.
Lemma D_8056c : decode_any W_8056c = Some (Jal 0 8072, 4%Z).
Proof. vm_refl. Qed.

Definition W_80570 : bv 32 := 0x00032d03.
Lemma F_80570 : fetch_word Ubsan.M.loaded_segments (0x80570 : word) = Some W_80570.
Proof. vm_refl. Qed.
Lemma D_80570 : decode_any W_80570 = Some (Load SZ4 true 26 6 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_80574 : bv 32 := 0x000c2d83.
Lemma F_80574 : fetch_word Ubsan.M.loaded_segments (0x80574 : word) = Some W_80574.
Proof. vm_refl. Qed.
Lemma D_80574 : decode_any W_80574 = Some (Load SZ4 true 27 24 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_80578 : bv 32 := 0x01aded33.
Lemma F_80578 : fetch_word Ubsan.M.loaded_segments (0x80578 : word) = Some W_80578.
Proof. vm_refl. Qed.
Lemma D_80578 : decode_any W_80578 = Some (Op ALU_OR 26 27 26, 4%Z).
Proof. vm_refl. Qed.

Definition W_8057c : bv 32 := 0xfffd4d13.
Lemma F_8057c : fetch_word Ubsan.M.loaded_segments (0x8057c : word) = Some W_8057c.
Proof. vm_refl. Qed.
Lemma D_8057c : decode_any W_8057c = Some (OpImm ALU_XOR 26 26 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_80580 : bv 32 := 0x01ac2023.
Lemma F_80580 : fetch_word Ubsan.M.loaded_segments (0x80580 : word) = Some W_80580.
Proof. vm_refl. Qed.
Lemma D_80580 : decode_any W_80580 = Some (Store SZ4 24 26 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_80584 : bv 32 := 0x01847463.
Lemma F_80584 : fetch_word Ubsan.M.loaded_segments (0x80584 : word) = Some W_80584.
Proof. vm_refl. Qed.
Lemma D_80584 : decode_any W_80584 = Some (Branch BC_GEU 8 24 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_80588 : bv 32 := 0x76d0106f.
Lemma F_80588 : fetch_word Ubsan.M.loaded_segments (0x80588 : word) = Some W_80588.
Proof. vm_refl. Qed.
Lemma D_80588 : decode_any W_80588 = Some (Jal 0 8044, 4%Z).
Proof. vm_refl. Qed.

Definition W_8058c : bv 32 := 0x00647463.
Lemma F_8058c : fetch_word Ubsan.M.loaded_segments (0x8058c : word) = Some W_8058c.
Proof. vm_refl. Qed.
Lemma D_8058c : decode_any W_8058c = Some (Branch BC_GEU 8 6 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_80590 : bv 32 := 0x7650106f.
Lemma F_80590 : fetch_word Ubsan.M.loaded_segments (0x80590 : word) = Some W_80590.
Proof. vm_refl. Qed.
Lemma D_80590 : decode_any W_80590 = Some (Jal 0 8036, 4%Z).
Proof. vm_refl. Qed.

Definition W_80594 : bv 32 := 0x001b8b9b.
Lemma F_80594 : fetch_word Ubsan.M.loaded_segments (0x80594 : word) = Some W_80594.
Proof. vm_refl. Qed.
Lemma D_80594 : decode_any W_80594 = Some (OpImm32 23 23 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_80598 : bv 32 := 0x00478793.
Lemma F_80598 : fetch_word Ubsan.M.loaded_segments (0x80598 : word) = Some W_80598.
Proof. vm_refl. Qed.
Lemma D_80598 : decode_any W_80598 = Some (OpImm ALU_ADD 15 15 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_8059c : bv 32 := 0xfa0b9ae3.
Lemma F_8059c : fetch_word Ubsan.M.loaded_segments (0x8059c : word) = Some W_8059c.
Proof. vm_refl. Qed.
Lemma D_8059c : decode_any W_8059c = Some (Branch BC_NE 23 0 8116, 4%Z).
Proof. vm_refl. Qed.

Definition W_805a0 : bv 32 := 0x00f90933.
Lemma F_805a0 : fetch_word Ubsan.M.loaded_segments (0x805a0 : word) = Some W_805a0.
Proof. vm_refl. Qed.
Lemma D_805a0 : decode_any W_805a0 = Some (Op ALU_ADD 18 18 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_805a4 : bv 32 := 0x00fb07b3.
Lemma F_805a4 : fetch_word Ubsan.M.loaded_segments (0x805a4 : word) = Some W_805a4.
Proof. vm_refl. Qed.
Lemma D_805a4 : decode_any W_805a4 = Some (Op ALU_ADD 15 22 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_805a8 : bv 32 := 0xee0606e3.
Lemma F_805a8 : fetch_word Ubsan.M.loaded_segments (0x805a8 : word) = Some W_805a8.
Proof. vm_refl. Qed.
Lemma D_805a8 : decode_any W_805a8 = Some (Branch BC_EQ 12 0 7916, 4%Z).
Proof. vm_refl. Qed.

Definition W_805ac : bv 32 := 0x00091463.
Lemma F_805ac : fetch_word Ubsan.M.loaded_segments (0x805ac : word) = Some W_805ac.
Proof. vm_refl. Qed.
Lemma D_805ac : decode_any W_805ac = Some (Branch BC_NE 18 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_805b0 : bv 32 := 0x7450106f.
Lemma F_805b0 : fetch_word Ubsan.M.loaded_segments (0x805b0 : word) = Some W_805b0.
Proof. vm_refl. Qed.
Lemma D_805b0 : decode_any W_805b0 = Some (Jal 0 8004, 4%Z).
Proof. vm_refl. Qed.

Definition W_805b4 : bv 32 := 0x00397313.
Lemma F_805b4 : fetch_word Ubsan.M.loaded_segments (0x805b4 : word) = Some W_805b4.
Proof. vm_refl. Qed.
Lemma D_805b4 : decode_any W_805b4 = Some (OpImm ALU_AND 6 18 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_805b8 : bv 32 := 0x00030463.
Lemma F_805b8 : fetch_word Ubsan.M.loaded_segments (0x805b8 : word) = Some W_805b8.
Proof. vm_refl. Qed.
Lemma D_805b8 : decode_any W_805b8 = Some (Branch BC_EQ 6 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_805bc : bv 32 := 0x7390106f.
Lemma F_805bc : fetch_word Ubsan.M.loaded_segments (0x805bc : word) = Some W_805bc.
Proof. vm_refl. Qed.
Lemma D_805bc : decode_any W_805bc = Some (Jal 0 7992, 4%Z).
Proof. vm_refl. Qed.

Definition W_805c0 : bv 32 := 0x00079463.
Lemma F_805c0 : fetch_word Ubsan.M.loaded_segments (0x805c0 : word) = Some W_805c0.
Proof. vm_refl. Qed.
Lemma D_805c0 : decode_any W_805c0 = Some (Branch BC_NE 15 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_805c4 : bv 32 := 0x7310106f.
Lemma F_805c4 : fetch_word Ubsan.M.loaded_segments (0x805c4 : word) = Some W_805c4.
Proof. vm_refl. Qed.
Lemma D_805c4 : decode_any W_805c4 = Some (Jal 0 7984, 4%Z).
Proof. vm_refl. Qed.

Definition W_805c8 : bv 32 := 0x0037f313.
Lemma F_805c8 : fetch_word Ubsan.M.loaded_segments (0x805c8 : word) = Some W_805c8.
Proof. vm_refl. Qed.
Lemma D_805c8 : decode_any W_805c8 = Some (OpImm ALU_AND 6 15 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_805cc : bv 32 := 0xea0304e3.
Lemma F_805cc : fetch_word Ubsan.M.loaded_segments (0x805cc : word) = Some W_805cc.
Proof. vm_refl. Qed.
Lemma D_805cc : decode_any W_805cc = Some (Branch BC_EQ 6 0 7848, 4%Z).
Proof. vm_refl. Qed.

Definition W_805d0 : bv 32 := 0x7250106f.
Lemma F_805d0 : fetch_word Ubsan.M.loaded_segments (0x805d0 : word) = Some W_805d0.
Proof. vm_refl. Qed.
Lemma D_805d0 : decode_any W_805d0 = Some (Jal 0 7972, 4%Z).
Proof. vm_refl. Qed.

Definition W_805d4 : bv 32 := 0x00545f9b.
Lemma F_805d4 : fetch_word Ubsan.M.loaded_segments (0x805d4 : word) = Some W_805d4.
Proof. vm_refl. Qed.
Lemma D_805d4 : decode_any W_805d4 = Some (ShiftImm32 ALU_SRL 31 8 5, 4%Z).
Proof. vm_refl. Qed.

Definition W_805d8 : bv 32 := 0x0e0f86e3.
Lemma F_805d8 : fetch_word Ubsan.M.loaded_segments (0x805d8 : word) = Some W_805d8.
Proof. vm_refl. Qed.
Lemma D_805d8 : decode_any W_805d8 = Some (Branch BC_EQ 31 0 2284, 4%Z).
Proof. vm_refl. Qed.

Definition W_805dc : bv 32 := 0x02770833.
Lemma F_805dc : fetch_word Ubsan.M.loaded_segments (0x805dc : word) = Some W_805dc.
Proof. vm_refl. Qed.
Lemma D_805dc : decode_any W_805dc = Some (Mul M_MUL 16 14 7, 4%Z).
Proof. vm_refl. Qed.

Definition W_805e0 : bv 32 := 0x0277063b.
Lemma F_805e0 : fetch_word Ubsan.M.loaded_segments (0x805e0 : word) = Some W_805e0.
Proof. vm_refl. Qed.
Lemma D_805e0 : decode_any W_805e0 = Some (Mul32 M_MUL 12 14 7, 4%Z).
Proof. vm_refl. Qed.

Definition W_805e4 : bv 32 := 0x01060463.
Lemma F_805e4 : fetch_word Ubsan.M.loaded_segments (0x805e4 : word) = Some W_805e4.
Proof. vm_refl. Qed.
Lemma D_805e4 : decode_any W_805e4 = Some (Branch BC_EQ 12 16 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_805e8 : bv 32 := 0x70d0106f.
Lemma F_805e8 : fetch_word Ubsan.M.loaded_segments (0x805e8 : word) = Some W_805e8.
Proof. vm_refl. Qed.
Lemma D_805e8 : decode_any W_805e8 = Some (Jal 0 7948, 4%Z).
Proof. vm_refl. Qed.

Definition W_805ec : bv 32 := 0x0008081b.
Lemma F_805ec : fetch_word Ubsan.M.loaded_segments (0x805ec : word) = Some W_805ec.
Proof. vm_refl. Qed.
Lemma D_805ec : decode_any W_805ec = Some (OpImm32 16 16 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_805f0 : bv 32 := 0x00281613.
Lemma F_805f0 : fetch_word Ubsan.M.loaded_segments (0x805f0 : word) = Some W_805f0.
Proof. vm_refl. Qed.
Lemma D_805f0 : decode_any W_805f0 = Some (ShiftImm ALU_SLL 12 16 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_805f4 : bv 32 := 0x00a60633.
Lemma F_805f4 : fetch_word Ubsan.M.loaded_segments (0x805f4 : word) = Some W_805f4.
Proof. vm_refl. Qed.
Lemma D_805f4 : decode_any W_805f4 = Some (Op ALU_ADD 12 12 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_805f8 : bv 32 := 0x00a037b3.
Lemma F_805f8 : fetch_word Ubsan.M.loaded_segments (0x805f8 : word) = Some W_805f8.
Proof. vm_refl. Qed.
Lemma D_805f8 : decode_any W_805f8 = Some (Op ALU_SLTU 15 0 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_805fc : bv 32 := 0x00163893.
Lemma F_805fc : fetch_word Ubsan.M.loaded_segments (0x805fc : word) = Some W_805fc.
Proof. vm_refl. Qed.
Lemma D_805fc : decode_any W_805fc = Some (OpImm ALU_SLTU 17 12 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_80600 : bv 32 := 0x01179463.
Lemma F_80600 : fetch_word Ubsan.M.loaded_segments (0x80600 : word) = Some W_80600.
Proof. vm_refl. Qed.
Lemma D_80600 : decode_any W_80600 = Some (Branch BC_NE 15 17 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_80604 : bv 32 := 0x6f10106f.
Lemma F_80604 : fetch_word Ubsan.M.loaded_segments (0x80604 : word) = Some W_80604.
Proof. vm_refl. Qed.
Lemma D_80604 : decode_any W_80604 = Some (Jal 0 7920, 4%Z).
Proof. vm_refl. Qed.

Definition W_80608 : bv 32 := 0x00a638b3.
Lemma F_80608 : fetch_word Ubsan.M.loaded_segments (0x80608 : word) = Some W_80608.
Proof. vm_refl. Qed.
Lemma D_80608 : decode_any W_80608 = Some (Op ALU_SLTU 17 12 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_8060c : bv 32 := 0x00082813.
Lemma F_8060c : fetch_word Ubsan.M.loaded_segments (0x8060c : word) = Some W_8060c.
Proof. vm_refl. Qed.
Lemma D_8060c : decode_any W_8060c = Some (OpImm ALU_SLT 16 16 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_80610 : bv 32 := 0x0108c833.
Lemma F_80610 : fetch_word Ubsan.M.loaded_segments (0x80610 : word) = Some W_80610.
Proof. vm_refl. Qed.
Lemma D_80610 : decode_any W_80610 = Some (Op ALU_XOR 16 17 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_80614 : bv 32 := 0x00184813.
Lemma F_80614 : fetch_word Ubsan.M.loaded_segments (0x80614 : word) = Some W_80614.
Proof. vm_refl. Qed.
Lemma D_80614 : decode_any W_80614 = Some (OpImm ALU_XOR 16 16 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_80618 : bv 32 := 0x00081463.
Lemma F_80618 : fetch_word Ubsan.M.loaded_segments (0x80618 : word) = Some W_80618.
Proof. vm_refl. Qed.
Lemma D_80618 : decode_any W_80618 = Some (Branch BC_NE 16 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_8061c : bv 32 := 0x6d90106f.
Lemma F_8061c : fetch_word Ubsan.M.loaded_segments (0x8061c : word) = Some W_8061c.
Proof. vm_refl. Qed.
Lemma D_8061c : decode_any W_8061c = Some (Jal 0 7896, 4%Z).
Proof. vm_refl. Qed.

Definition W_80620 : bv 32 := 0x405cd81b.
Lemma F_80620 : fetch_word Ubsan.M.loaded_segments (0x80620 : word) = Some W_80620.
Proof. vm_refl. Qed.
Lemma D_80620 : decode_any W_80620 = Some (ShiftImm32 ALU_SRA 16 25 5, 4%Z).
Proof. vm_refl. Qed.

Definition W_80624 : bv 32 := 0x00281413.
Lemma F_80624 : fetch_word Ubsan.M.loaded_segments (0x80624 : word) = Some W_80624.
Proof. vm_refl. Qed.
Lemma D_80624 : decode_any W_80624 = Some (ShiftImm ALU_SLL 8 16 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_80628 : bv 32 := 0x00860433.
Lemma F_80628 : fetch_word Ubsan.M.loaded_segments (0x80628 : word) = Some W_80628.
Proof. vm_refl. Qed.
Lemma D_80628 : decode_any W_80628 = Some (Op ALU_ADD 8 12 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_8062c : bv 32 := 0x00143893.
Lemma F_8062c : fetch_word Ubsan.M.loaded_segments (0x8062c : word) = Some W_8062c.
Proof. vm_refl. Qed.
Lemma D_8062c : decode_any W_8062c = Some (OpImm ALU_SLTU 17 8 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_80630 : bv 32 := 0x01179463.
Lemma F_80630 : fetch_word Ubsan.M.loaded_segments (0x80630 : word) = Some W_80630.
Proof. vm_refl. Qed.
Lemma D_80630 : decode_any W_80630 = Some (Branch BC_NE 15 17 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_80634 : bv 32 := 0x6c10106f.
Lemma F_80634 : fetch_word Ubsan.M.loaded_segments (0x80634 : word) = Some W_80634.
Proof. vm_refl. Qed.
Lemma D_80634 : decode_any W_80634 = Some (Jal 0 7872, 4%Z).
Proof. vm_refl. Qed.

Definition W_80638 : bv 32 := 0x00c43633.
Lemma F_80638 : fetch_word Ubsan.M.loaded_segments (0x80638 : word) = Some W_80638.
Proof. vm_refl. Qed.
Lemma D_80638 : decode_any W_80638 = Some (Op ALU_SLTU 12 8 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_8063c : bv 32 := 0x00082793.
Lemma F_8063c : fetch_word Ubsan.M.loaded_segments (0x8063c : word) = Some W_8063c.
Proof. vm_refl. Qed.
Lemma D_8063c : decode_any W_8063c = Some (OpImm ALU_SLT 15 16 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_80640 : bv 32 := 0x00f64633.
Lemma F_80640 : fetch_word Ubsan.M.loaded_segments (0x80640 : word) = Some W_80640.
Proof. vm_refl. Qed.
Lemma D_80640 : decode_any W_80640 = Some (Op ALU_XOR 12 12 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_80644 : bv 32 := 0x00164613.
Lemma F_80644 : fetch_word Ubsan.M.loaded_segments (0x80644 : word) = Some W_80644.
Proof. vm_refl. Qed.
Lemma D_80644 : decode_any W_80644 = Some (OpImm ALU_XOR 12 12 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_80648 : bv 32 := 0x00061463.
Lemma F_80648 : fetch_word Ubsan.M.loaded_segments (0x80648 : word) = Some W_80648.
Proof. vm_refl. Qed.
Lemma D_80648 : decode_any W_80648 = Some (Branch BC_NE 12 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_8064c : bv 32 := 0x6a90106f.
Lemma F_8064c : fetch_word Ubsan.M.loaded_segments (0x8064c : word) = Some W_8064c.
Proof. vm_refl. Qed.
Lemma D_8064c : decode_any W_8064c = Some (Jal 0 7848, 4%Z).
Proof. vm_refl. Qed.

Definition W_80650 : bv 32 := 0x05813603.
Lemma F_80650 : fetch_word Ubsan.M.loaded_segments (0x80650 : word) = Some W_80650.
Proof. vm_refl. Qed.
Lemma D_80650 : decode_any W_80650 = Some (Load SZ8 true 12 2 88, 4%Z).
Proof. vm_refl. Qed.

Definition W_80654 : bv 32 := 0x02560833.
Lemma F_80654 : fetch_word Ubsan.M.loaded_segments (0x80654 : word) = Some W_80654.
Proof. vm_refl. Qed.
Lemma D_80654 : decode_any W_80654 = Some (Mul M_MUL 16 12 5, 4%Z).
Proof. vm_refl. Qed.

Definition W_80658 : bv 32 := 0x0256063b.
Lemma F_80658 : fetch_word Ubsan.M.loaded_segments (0x80658 : word) = Some W_80658.
Proof. vm_refl. Qed.
Lemma D_80658 : decode_any W_80658 = Some (Mul32 M_MUL 12 12 5, 4%Z).
Proof. vm_refl. Qed.

Definition W_8065c : bv 32 := 0x01060463.
Lemma F_8065c : fetch_word Ubsan.M.loaded_segments (0x8065c : word) = Some W_8065c.
Proof. vm_refl. Qed.
Lemma D_8065c : decode_any W_8065c = Some (Branch BC_EQ 12 16 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_80660 : bv 32 := 0x6950106f.
Lemma F_80660 : fetch_word Ubsan.M.loaded_segments (0x80660 : word) = Some W_80660.
Proof. vm_refl. Qed.
Lemma D_80660 : decode_any W_80660 = Some (Jal 0 7828, 4%Z).
Proof. vm_refl. Qed.

Definition W_80664 : bv 32 := 0x0008081b.
Lemma F_80664 : fetch_word Ubsan.M.loaded_segments (0x80664 : word) = Some W_80664.
Proof. vm_refl. Qed.
Lemma D_80664 : decode_any W_80664 = Some (OpImm32 16 16 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_80668 : bv 32 := 0x00281793.
Lemma F_80668 : fetch_word Ubsan.M.loaded_segments (0x80668 : word) = Some W_80668.
Proof. vm_refl. Qed.
Lemma D_80668 : decode_any W_80668 = Some (ShiftImm ALU_SLL 15 16 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_8066c : bv 32 := 0x013787b3.
Lemma F_8066c : fetch_word Ubsan.M.loaded_segments (0x8066c : word) = Some W_8066c.
Proof. vm_refl. Qed.
Lemma D_8066c : decode_any W_8066c = Some (Op ALU_ADD 15 15 19, 4%Z).
Proof. vm_refl. Qed.

Definition W_80670 : bv 32 := 0x01303633.
Lemma F_80670 : fetch_word Ubsan.M.loaded_segments (0x80670 : word) = Some W_80670.
Proof. vm_refl. Qed.
Lemma D_80670 : decode_any W_80670 = Some (Op ALU_SLTU 12 0 19, 4%Z).
Proof. vm_refl. Qed.

Definition W_80674 : bv 32 := 0x0017b893.
Lemma F_80674 : fetch_word Ubsan.M.loaded_segments (0x80674 : word) = Some W_80674.
Proof. vm_refl. Qed.
Lemma D_80674 : decode_any W_80674 = Some (OpImm ALU_SLTU 17 15 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_80678 : bv 32 := 0x01161463.
Lemma F_80678 : fetch_word Ubsan.M.loaded_segments (0x80678 : word) = Some W_80678.
Proof. vm_refl. Qed.
Lemma D_80678 : decode_any W_80678 = Some (Branch BC_NE 12 17 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_8067c : bv 32 := 0x6790106f.
Lemma F_8067c : fetch_word Ubsan.M.loaded_segments (0x8067c : word) = Some W_8067c.
Proof. vm_refl. Qed.
Lemma D_8067c : decode_any W_8067c = Some (Jal 0 7800, 4%Z).
Proof. vm_refl. Qed.

Definition W_80680 : bv 32 := 0x0137b8b3.
Lemma F_80680 : fetch_word Ubsan.M.loaded_segments (0x80680 : word) = Some W_80680.
Proof. vm_refl. Qed.
Lemma D_80680 : decode_any W_80680 = Some (Op ALU_SLTU 17 15 19, 4%Z).
Proof. vm_refl. Qed.

Definition W_80684 : bv 32 := 0x00082813.
Lemma F_80684 : fetch_word Ubsan.M.loaded_segments (0x80684 : word) = Some W_80684.
Proof. vm_refl. Qed.
Lemma D_80684 : decode_any W_80684 = Some (OpImm ALU_SLT 16 16 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_80688 : bv 32 := 0x0108c833.
Lemma F_80688 : fetch_word Ubsan.M.loaded_segments (0x80688 : word) = Some W_80688.
Proof. vm_refl. Qed.
Lemma D_80688 : decode_any W_80688 = Some (Op ALU_XOR 16 17 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_8068c : bv 32 := 0x00184813.
Lemma F_8068c : fetch_word Ubsan.M.loaded_segments (0x8068c : word) = Some W_8068c.
Proof. vm_refl. Qed.
Lemma D_8068c : decode_any W_8068c = Some (OpImm ALU_XOR 16 16 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_80690 : bv 32 := 0x00081463.
Lemma F_80690 : fetch_word Ubsan.M.loaded_segments (0x80690 : word) = Some W_80690.
Proof. vm_refl. Qed.
Lemma D_80690 : decode_any W_80690 = Some (Branch BC_NE 16 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_80694 : bv 32 := 0x6610106f.
Lemma F_80694 : fetch_word Ubsan.M.loaded_segments (0x80694 : word) = Some W_80694.
Proof. vm_refl. Qed.
Lemma D_80694 : decode_any W_80694 = Some (Jal 0 7776, 4%Z).
Proof. vm_refl. Qed.

Definition W_80698 : bv 32 := 0x005dd81b.
Lemma F_80698 : fetch_word Ubsan.M.loaded_segments (0x80698 : word) = Some W_80698.
Proof. vm_refl. Qed.
Lemma D_80698 : decode_any W_80698 = Some (ShiftImm32 ALU_SRL 16 27 5, 4%Z).
Proof. vm_refl. Qed.

Definition W_8069c : bv 32 := 0x00281813.
Lemma F_8069c : fetch_word Ubsan.M.loaded_segments (0x8069c : word) = Some W_8069c.
Proof. vm_refl. Qed.
Lemma D_8069c : decode_any W_8069c = Some (ShiftImm ALU_SLL 16 16 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_806a0 : bv 32 := 0x00f80933.
Lemma F_806a0 : fetch_word Ubsan.M.loaded_segments (0x806a0 : word) = Some W_806a0.
Proof. vm_refl. Qed.
Lemma D_806a0 : decode_any W_806a0 = Some (Op ALU_ADD 18 16 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_806a4 : bv 32 := 0x00f97463.
Lemma F_806a4 : fetch_word Ubsan.M.loaded_segments (0x806a4 : word) = Some W_806a4.
Proof. vm_refl. Qed.
Lemma D_806a4 : decode_any W_806a4 = Some (Branch BC_GEU 18 15 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_806a8 : bv 32 := 0x64d0106f.
Lemma F_806a8 : fetch_word Ubsan.M.loaded_segments (0x806a8 : word) = Some W_806a8.
Proof. vm_refl. Qed.
Lemma D_806a8 : decode_any W_806a8 = Some (Jal 0 7756, 4%Z).
Proof. vm_refl. Qed.

Definition W_806ac : bv 32 := 0x00193793.
Lemma F_806ac : fetch_word Ubsan.M.loaded_segments (0x806ac : word) = Some W_806ac.
Proof. vm_refl. Qed.
Lemma D_806ac : decode_any W_806ac = Some (OpImm ALU_SLTU 15 18 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_806b0 : bv 32 := 0x00f64633.
Lemma F_806b0 : fetch_word Ubsan.M.loaded_segments (0x806b0 : word) = Some W_806b0.
Proof. vm_refl. Qed.
Lemma D_806b0 : decode_any W_806b0 = Some (Op ALU_XOR 12 12 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_806b4 : bv 32 := 0x00061463.
Lemma F_806b4 : fetch_word Ubsan.M.loaded_segments (0x806b4 : word) = Some W_806b4.
Proof. vm_refl. Qed.
Lemma D_806b4 : decode_any W_806b4 = Some (Branch BC_NE 12 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_806b8 : bv 32 := 0x63d0106f.
Lemma F_806b8 : fetch_word Ubsan.M.loaded_segments (0x806b8 : word) = Some W_806b8.
Proof. vm_refl. Qed.
Lemma D_806b8 : decode_any W_806b8 = Some (Jal 0 7740, 4%Z).
Proof. vm_refl. Qed.

Definition W_806bc : bv 32 := 0x00000b93.
Lemma F_806bc : fetch_word Ubsan.M.loaded_segments (0x806bc : word) = Some W_806bc.
Proof. vm_refl. Qed.
Lemma D_806bc : decode_any W_806bc = Some (OpImm ALU_ADD 23 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_806c0 : bv 32 := 0x00000a13.
Lemma F_806c0 : fetch_word Ubsan.M.loaded_segments (0x806c0 : word) = Some W_806c0.
Proof. vm_refl. Qed.
Lemma D_806c0 : decode_any W_806c0 = Some (OpImm ALU_ADD 20 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_806c4 : bv 32 := 0x00000a93.
Lemma F_806c4 : fetch_word Ubsan.M.loaded_segments (0x806c4 : word) = Some W_806c4.
Proof. vm_refl. Qed.
Lemma D_806c4 : decode_any W_806c4 = Some (OpImm ALU_ADD 21 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_806c8 : bv 32 := 0x1640006f.
Lemma F_806c8 : fetch_word Ubsan.M.loaded_segments (0x806c8 : word) = Some W_806c8.
Proof. vm_refl. Qed.
Lemma D_806c8 : decode_any W_806c8 = Some (Jal 0 356, 4%Z).
Proof. vm_refl. Qed.

Definition W_806cc : bv 32 := 0x00000793.
Lemma F_806cc : fetch_word Ubsan.M.loaded_segments (0x806cc : word) = Some W_806cc.
Proof. vm_refl. Qed.
Lemma D_806cc : decode_any W_806cc = Some (OpImm ALU_ADD 15 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_806d0 : bv 32 := 0x00000c93.
Lemma F_806d0 : fetch_word Ubsan.M.loaded_segments (0x806d0 : word) = Some W_806d0.
Proof. vm_refl. Qed.
Lemma D_806d0 : decode_any W_806d0 = Some (OpImm ALU_ADD 25 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_806d4 : bv 32 := 0x00000a93.
Lemma F_806d4 : fetch_word Ubsan.M.loaded_segments (0x806d4 : word) = Some W_806d4.
Proof. vm_refl. Qed.
Lemma D_806d4 : decode_any W_806d4 = Some (OpImm ALU_ADD 21 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_806d8 : bv 32 := 0x00000d93.
Lemma F_806d8 : fetch_word Ubsan.M.loaded_segments (0x806d8 : word) = Some W_806d8.
Proof. vm_refl. Qed.
Lemma D_806d8 : decode_any W_806d8 = Some (OpImm ALU_ADD 27 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_806dc : bv 32 := 0x4154063b.
Lemma F_806dc : fetch_word Ubsan.M.loaded_segments (0x806dc : word) = Some W_806dc.
Proof. vm_refl. Qed.
Lemma D_806dc : decode_any W_806dc = Some (Op32 ALU_SUB 12 8 21, 4%Z).
Proof. vm_refl. Qed.

Definition W_806e0 : bv 32 := 0x0056561b.
Lemma F_806e0 : fetch_word Ubsan.M.loaded_segments (0x806e0 : word) = Some W_806e0.
Proof. vm_refl. Qed.
Lemma D_806e0 : decode_any W_806e0 = Some (ShiftImm32 ALU_SRL 12 12 5, 4%Z).
Proof. vm_refl. Qed.

Definition W_806e4 : bv 32 := 0x06c13823.
Lemma F_806e4 : fetch_word Ubsan.M.loaded_segments (0x806e4 : word) = Some W_806e4.
Proof. vm_refl. Qed.
Lemma D_806e4 : decode_any W_806e4 = Some (Store SZ8 2 12 112, 4%Z).
Proof. vm_refl. Qed.

Definition W_806e8 : bv 32 := 0x14060863.
Lemma F_806e8 : fetch_word Ubsan.M.loaded_segments (0x806e8 : word) = Some W_806e8.
Proof. vm_refl. Qed.
Lemma D_806e8 : decode_any W_806e8 = Some (Branch BC_EQ 12 0 336, 4%Z).
Proof. vm_refl. Qed.

Definition W_806ec : bv 32 := 0x02770633.
Lemma F_806ec : fetch_word Ubsan.M.loaded_segments (0x806ec : word) = Some W_806ec.
Proof. vm_refl. Qed.
Lemma D_806ec : decode_any W_806ec = Some (Mul M_MUL 12 14 7, 4%Z).
Proof. vm_refl. Qed.

Definition W_806f0 : bv 32 := 0x0277083b.
Lemma F_806f0 : fetch_word Ubsan.M.loaded_segments (0x806f0 : word) = Some W_806f0.
Proof. vm_refl. Qed.
Lemma D_806f0 : decode_any W_806f0 = Some (Mul32 M_MUL 16 14 7, 4%Z).
Proof. vm_refl. Qed.

Definition W_806f4 : bv 32 := 0x00c80463.
Lemma F_806f4 : fetch_word Ubsan.M.loaded_segments (0x806f4 : word) = Some W_806f4.
Proof. vm_refl. Qed.
Lemma D_806f4 : decode_any W_806f4 = Some (Branch BC_EQ 16 12 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_806f8 : bv 32 := 0x5fd0106f.
Lemma F_806f8 : fetch_word Ubsan.M.loaded_segments (0x806f8 : word) = Some W_806f8.
Proof. vm_refl. Qed.
Lemma D_806f8 : decode_any W_806f8 = Some (Jal 0 7676, 4%Z).
Proof. vm_refl. Qed.

Definition W_806fc : bv 32 := 0x0006061b.
Lemma F_806fc : fetch_word Ubsan.M.loaded_segments (0x806fc : word) = Some W_806fc.
Proof. vm_refl. Qed.
Lemma D_806fc : decode_any W_806fc = Some (OpImm32 12 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_80700 : bv 32 := 0x00261813.
Lemma F_80700 : fetch_word Ubsan.M.loaded_segments (0x80700 : word) = Some W_80700.
Proof. vm_refl. Qed.
Lemma D_80700 : decode_any W_80700 = Some (ShiftImm ALU_SLL 16 12 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_80704 : bv 32 := 0x01050833.
Lemma F_80704 : fetch_word Ubsan.M.loaded_segments (0x80704 : word) = Some W_80704.
Proof. vm_refl. Qed.
Lemma D_80704 : decode_any W_80704 = Some (Op ALU_ADD 16 10 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_80708 : bv 32 := 0x00a03333.
Lemma F_80708 : fetch_word Ubsan.M.loaded_segments (0x80708 : word) = Some W_80708.
Proof. vm_refl. Qed.
Lemma D_80708 : decode_any W_80708 = Some (Op ALU_SLTU 6 0 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_8070c : bv 32 := 0x00183893.
Lemma F_8070c : fetch_word Ubsan.M.loaded_segments (0x8070c : word) = Some W_8070c.
Proof. vm_refl. Qed.
Lemma D_8070c : decode_any W_8070c = Some (OpImm ALU_SLTU 17 16 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_80710 : bv 32 := 0x01131463.
Lemma F_80710 : fetch_word Ubsan.M.loaded_segments (0x80710 : word) = Some W_80710.
Proof. vm_refl. Qed.
Lemma D_80710 : decode_any W_80710 = Some (Branch BC_NE 6 17 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_80714 : bv 32 := 0x5e10106f.
Lemma F_80714 : fetch_word Ubsan.M.loaded_segments (0x80714 : word) = Some W_80714.
Proof. vm_refl. Qed.
Lemma D_80714 : decode_any W_80714 = Some (Jal 0 7648, 4%Z).
Proof. vm_refl. Qed.

Definition W_80718 : bv 32 := 0x00a838b3.
Lemma F_80718 : fetch_word Ubsan.M.loaded_segments (0x80718 : word) = Some W_80718.
Proof. vm_refl. Qed.
Lemma D_80718 : decode_any W_80718 = Some (Op ALU_SLTU 17 16 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_8071c : bv 32 := 0x00062613.
Lemma F_8071c : fetch_word Ubsan.M.loaded_segments (0x8071c : word) = Some W_8071c.
Proof. vm_refl. Qed.
Lemma D_8071c : decode_any W_8071c = Some (OpImm ALU_SLT 12 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_80720 : bv 32 := 0x00c8c633.
Lemma F_80720 : fetch_word Ubsan.M.loaded_segments (0x80720 : word) = Some W_80720.
Proof. vm_refl. Qed.
Lemma D_80720 : decode_any W_80720 = Some (Op ALU_XOR 12 17 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_80724 : bv 32 := 0x00164613.
Lemma F_80724 : fetch_word Ubsan.M.loaded_segments (0x80724 : word) = Some W_80724.
Proof. vm_refl. Qed.
Lemma D_80724 : decode_any W_80724 = Some (OpImm ALU_XOR 12 12 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_80728 : bv 32 := 0x00061463.
Lemma F_80728 : fetch_word Ubsan.M.loaded_segments (0x80728 : word) = Some W_80728.
Proof. vm_refl. Qed.
Lemma D_80728 : decode_any W_80728 = Some (Branch BC_NE 12 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_8072c : bv 32 := 0x5c90106f.
Lemma F_8072c : fetch_word Ubsan.M.loaded_segments (0x8072c : word) = Some W_8072c.
Proof. vm_refl. Qed.
Lemma D_8072c : decode_any W_8072c = Some (Jal 0 7624, 4%Z).
Proof. vm_refl. Qed.

Definition W_80730 : bv 32 := 0x000b861b.
Lemma F_80730 : fetch_word Ubsan.M.loaded_segments (0x80730 : word) = Some W_80730.
Proof. vm_refl. Qed.
Lemma D_80730 : decode_any W_80730 = Some (OpImm32 12 23 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_80734 : bv 32 := 0x00c688b3.
Lemma F_80734 : fetch_word Ubsan.M.loaded_segments (0x80734 : word) = Some W_80734.
Proof. vm_refl. Qed.
Lemma D_80734 : decode_any W_80734 = Some (Op ALU_ADD 17 13 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_80738 : bv 32 := 0x00c68e3b.
Lemma F_80738 : fetch_word Ubsan.M.loaded_segments (0x80738 : word) = Some W_80738.
Proof. vm_refl. Qed.
Lemma D_80738 : decode_any W_80738 = Some (Op32 ALU_ADD 28 13 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_8073c : bv 32 := 0x011e0463.
Lemma F_8073c : fetch_word Ubsan.M.loaded_segments (0x8073c : word) = Some W_8073c.
Proof. vm_refl. Qed.
Lemma D_8073c : decode_any W_8073c = Some (Branch BC_EQ 28 17 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_80740 : bv 32 := 0x5b50106f.
Lemma F_80740 : fetch_word Ubsan.M.loaded_segments (0x80740 : word) = Some W_80740.
Proof. vm_refl. Qed.
Lemma D_80740 : decode_any W_80740 = Some (Jal 0 7604, 4%Z).
Proof. vm_refl. Qed.

Definition W_80744 : bv 32 := 0x4058de1b.
Lemma F_80744 : fetch_word Ubsan.M.loaded_segments (0x80744 : word) = Some W_80744.
Proof. vm_refl. Qed.
Lemma D_80744 : decode_any W_80744 = Some (ShiftImm32 ALU_SRA 28 17 5, 4%Z).
Proof. vm_refl. Qed.

Definition W_80748 : bv 32 := 0x002e1893.
Lemma F_80748 : fetch_word Ubsan.M.loaded_segments (0x80748 : word) = Some W_80748.
Proof. vm_refl. Qed.
Lemma D_80748 : decode_any W_80748 = Some (ShiftImm ALU_SLL 17 28 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_8074c : bv 32 := 0x01180933.
Lemma F_8074c : fetch_word Ubsan.M.loaded_segments (0x8074c : word) = Some W_8074c.
Proof. vm_refl. Qed.
Lemma D_8074c : decode_any W_8074c = Some (Op ALU_ADD 18 16 17, 4%Z).
Proof. vm_refl. Qed.

Definition W_80750 : bv 32 := 0x00193413.
Lemma F_80750 : fetch_word Ubsan.M.loaded_segments (0x80750 : word) = Some W_80750.
Proof. vm_refl. Qed.
Lemma D_80750 : decode_any W_80750 = Some (OpImm ALU_SLTU 8 18 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_80754 : bv 32 := 0x00831463.
Lemma F_80754 : fetch_word Ubsan.M.loaded_segments (0x80754 : word) = Some W_80754.
Proof. vm_refl. Qed.
Lemma D_80754 : decode_any W_80754 = Some (Branch BC_NE 6 8 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_80758 : bv 32 := 0x59d0106f.
Lemma F_80758 : fetch_word Ubsan.M.loaded_segments (0x80758 : word) = Some W_80758.
Proof. vm_refl. Qed.
Lemma D_80758 : decode_any W_80758 = Some (Jal 0 7580, 4%Z).
Proof. vm_refl. Qed.

Definition W_8075c : bv 32 := 0x01093833.
Lemma F_8075c : fetch_word Ubsan.M.loaded_segments (0x8075c : word) = Some W_8075c.
Proof. vm_refl. Qed.
Lemma D_8075c : decode_any W_8075c = Some (Op ALU_SLTU 16 18 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_80760 : bv 32 := 0x000e2313.
Lemma F_80760 : fetch_word Ubsan.M.loaded_segments (0x80760 : word) = Some W_80760.
Proof. vm_refl. Qed.
Lemma D_80760 : decode_any W_80760 = Some (OpImm ALU_SLT 6 28 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_80764 : bv 32 := 0x00684833.
Lemma F_80764 : fetch_word Ubsan.M.loaded_segments (0x80764 : word) = Some W_80764.
Proof. vm_refl. Qed.
Lemma D_80764 : decode_any W_80764 = Some (Op ALU_XOR 16 16 6, 4%Z).
Proof. vm_refl. Qed.

Definition W_80768 : bv 32 := 0x00184813.
Lemma F_80768 : fetch_word Ubsan.M.loaded_segments (0x80768 : word) = Some W_80768.
Proof. vm_refl. Qed.
Lemma D_80768 : decode_any W_80768 = Some (OpImm ALU_XOR 16 16 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_8076c : bv 32 := 0x00081463.
Lemma F_8076c : fetch_word Ubsan.M.loaded_segments (0x8076c : word) = Some W_8076c.
Proof. vm_refl. Qed.
Lemma D_8076c : decode_any W_8076c = Some (Branch BC_NE 16 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_80770 : bv 32 := 0x5850106f.
Lemma F_80770 : fetch_word Ubsan.M.loaded_segments (0x80770 : word) = Some W_80770.
Proof. vm_refl. Qed.
Lemma D_80770 : decode_any W_80770 = Some (Jal 0 7556, 4%Z).
Proof. vm_refl. Qed.

Definition W_80774 : bv 32 := 0x05813803.
Lemma F_80774 : fetch_word Ubsan.M.loaded_segments (0x80774 : word) = Some W_80774.
Proof. vm_refl. Qed.
Lemma D_80774 : decode_any W_80774 = Some (Load SZ8 true 16 2 88, 4%Z).
Proof. vm_refl. Qed.

Definition W_80778 : bv 32 := 0x02580333.
Lemma F_80778 : fetch_word Ubsan.M.loaded_segments (0x80778 : word) = Some W_80778.
Proof. vm_refl. Qed.
Lemma D_80778 : decode_any W_80778 = Some (Mul M_MUL 6 16 5, 4%Z).
Proof. vm_refl. Qed.

Definition W_8077c : bv 32 := 0x0258083b.
Lemma F_8077c : fetch_word Ubsan.M.loaded_segments (0x8077c : word) = Some W_8077c.
Proof. vm_refl. Qed.
Lemma D_8077c : decode_any W_8077c = Some (Mul32 M_MUL 16 16 5, 4%Z).
Proof. vm_refl. Qed.

Definition W_80780 : bv 32 := 0x00680463.
Lemma F_80780 : fetch_word Ubsan.M.loaded_segments (0x80780 : word) = Some W_80780.
Proof. vm_refl. Qed.
Lemma D_80780 : decode_any W_80780 = Some (Branch BC_EQ 16 6 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_80784 : bv 32 := 0x5710106f.
Lemma F_80784 : fetch_word Ubsan.M.loaded_segments (0x80784 : word) = Some W_80784.
Proof. vm_refl. Qed.
Lemma D_80784 : decode_any W_80784 = Some (Jal 0 7536, 4%Z).
Proof. vm_refl. Qed.

Definition W_80788 : bv 32 := 0x0003031b.
Lemma F_80788 : fetch_word Ubsan.M.loaded_segments (0x80788 : word) = Some W_80788.
Proof. vm_refl. Qed.
Lemma D_80788 : decode_any W_80788 = Some (OpImm32 6 6 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_8078c : bv 32 := 0x00231813.
Lemma F_8078c : fetch_word Ubsan.M.loaded_segments (0x8078c : word) = Some W_8078c.
Proof. vm_refl. Qed.
Lemma D_8078c : decode_any W_8078c = Some (ShiftImm ALU_SLL 16 6 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_80790 : bv 32 := 0x01098833.
Lemma F_80790 : fetch_word Ubsan.M.loaded_segments (0x80790 : word) = Some W_80790.
Proof. vm_refl. Qed.
Lemma D_80790 : decode_any W_80790 = Some (Op ALU_ADD 16 19 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_80794 : bv 32 := 0x01303e33.
Lemma F_80794 : fetch_word Ubsan.M.loaded_segments (0x80794 : word) = Some W_80794.
Proof. vm_refl. Qed.
Lemma D_80794 : decode_any W_80794 = Some (Op ALU_SLTU 28 0 19, 4%Z).
Proof. vm_refl. Qed.

Definition W_80798 : bv 32 := 0x00183413.
Lemma F_80798 : fetch_word Ubsan.M.loaded_segments (0x80798 : word) = Some W_80798.
Proof. vm_refl. Qed.
Lemma D_80798 : decode_any W_80798 = Some (OpImm ALU_SLTU 8 16 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_8079c : bv 32 := 0x008e1463.
Lemma F_8079c : fetch_word Ubsan.M.loaded_segments (0x8079c : word) = Some W_8079c.
Proof. vm_refl. Qed.
Lemma D_8079c : decode_any W_8079c = Some (Branch BC_NE 28 8 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_807a0 : bv 32 := 0x5550106f.
Lemma F_807a0 : fetch_word Ubsan.M.loaded_segments (0x807a0 : word) = Some W_807a0.
Proof. vm_refl. Qed.
Lemma D_807a0 : decode_any W_807a0 = Some (Jal 0 7508, 4%Z).
Proof. vm_refl. Qed.

Definition W_807a4 : bv 32 := 0x01383433.
Lemma F_807a4 : fetch_word Ubsan.M.loaded_segments (0x807a4 : word) = Some W_807a4.
Proof. vm_refl. Qed.
Lemma D_807a4 : decode_any W_807a4 = Some (Op ALU_SLTU 8 16 19, 4%Z).
Proof. vm_refl. Qed.

Definition W_807a8 : bv 32 := 0x00032313.
Lemma F_807a8 : fetch_word Ubsan.M.loaded_segments (0x807a8 : word) = Some W_807a8.
Proof. vm_refl. Qed.
Lemma D_807a8 : decode_any W_807a8 = Some (OpImm ALU_SLT 6 6 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_807ac : bv 32 := 0x00644333.
Lemma F_807ac : fetch_word Ubsan.M.loaded_segments (0x807ac : word) = Some W_807ac.
Proof. vm_refl. Qed.
Lemma D_807ac : decode_any W_807ac = Some (Op ALU_XOR 6 8 6, 4%Z).
Proof. vm_refl. Qed.

Definition W_807b0 : bv 32 := 0x00134313.
Lemma F_807b0 : fetch_word Ubsan.M.loaded_segments (0x807b0 : word) = Some W_807b0.
Proof. vm_refl. Qed.
Lemma D_807b0 : decode_any W_807b0 = Some (OpImm ALU_XOR 6 6 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_807b4 : bv 32 := 0x00031463.
Lemma F_807b4 : fetch_word Ubsan.M.loaded_segments (0x807b4 : word) = Some W_807b4.
Proof. vm_refl. Qed.
Lemma D_807b4 : decode_any W_807b4 = Some (Branch BC_NE 6 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_807b8 : bv 32 := 0x53d0106f.
Lemma F_807b8 : fetch_word Ubsan.M.loaded_segments (0x807b8 : word) = Some W_807b8.
Proof. vm_refl. Qed.
Lemma D_807b8 : decode_any W_807b8 = Some (Jal 0 7484, 4%Z).
Proof. vm_refl. Qed.

Definition W_807bc : bv 32 := 0x00cc0333.
Lemma F_807bc : fetch_word Ubsan.M.loaded_segments (0x807bc : word) = Some W_807bc.
Proof. vm_refl. Qed.
Lemma D_807bc : decode_any W_807bc = Some (Op ALU_ADD 6 24 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_807c0 : bv 32 := 0x00cc063b.
Lemma F_807c0 : fetch_word Ubsan.M.loaded_segments (0x807c0 : word) = Some W_807c0.
Proof. vm_refl. Qed.
Lemma D_807c0 : decode_any W_807c0 = Some (Op32 ALU_ADD 12 24 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_807c4 : bv 32 := 0x00660463.
Lemma F_807c4 : fetch_word Ubsan.M.loaded_segments (0x807c4 : word) = Some W_807c4.
Proof. vm_refl. Qed.
Lemma D_807c4 : decode_any W_807c4 = Some (Branch BC_EQ 12 6 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_807c8 : bv 32 := 0x52d0106f.
Lemma F_807c8 : fetch_word Ubsan.M.loaded_segments (0x807c8 : word) = Some W_807c8.
Proof. vm_refl. Qed.
Lemma D_807c8 : decode_any W_807c8 = Some (Jal 0 7468, 4%Z).
Proof. vm_refl. Qed.

Definition W_807cc : bv 32 := 0x4053561b.
Lemma F_807cc : fetch_word Ubsan.M.loaded_segments (0x807cc : word) = Some W_807cc.
Proof. vm_refl. Qed.
Lemma D_807cc : decode_any W_807cc = Some (ShiftImm32 ALU_SRA 12 6 5, 4%Z).
Proof. vm_refl. Qed.

Definition W_807d0 : bv 32 := 0x00261313.
Lemma F_807d0 : fetch_word Ubsan.M.loaded_segments (0x807d0 : word) = Some W_807d0.
Proof. vm_refl. Qed.
Lemma D_807d0 : decode_any W_807d0 = Some (ShiftImm ALU_SLL 6 12 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_807d4 : bv 32 := 0x01030333.
Lemma F_807d4 : fetch_word Ubsan.M.loaded_segments (0x807d4 : word) = Some W_807d4.
Proof. vm_refl. Qed.
Lemma D_807d4 : decode_any W_807d4 = Some (Op ALU_ADD 6 6 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_807d8 : bv 32 := 0x00133413.
Lemma F_807d8 : fetch_word Ubsan.M.loaded_segments (0x807d8 : word) = Some W_807d8.
Proof. vm_refl. Qed.
Lemma D_807d8 : decode_any W_807d8 = Some (OpImm ALU_SLTU 8 6 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_807dc : bv 32 := 0x008e1463.
Lemma F_807dc : fetch_word Ubsan.M.loaded_segments (0x807dc : word) = Some W_807dc.
Proof. vm_refl. Qed.
Lemma D_807dc : decode_any W_807dc = Some (Branch BC_NE 28 8 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_807e0 : bv 32 := 0x5150106f.
Lemma F_807e0 : fetch_word Ubsan.M.loaded_segments (0x807e0 : word) = Some W_807e0.
Proof. vm_refl. Qed.
Lemma D_807e0 : decode_any W_807e0 = Some (Jal 0 7444, 4%Z).
Proof. vm_refl. Qed.

Definition W_807e4 : bv 32 := 0x01033833.
Lemma F_807e4 : fetch_word Ubsan.M.loaded_segments (0x807e4 : word) = Some W_807e4.
Proof. vm_refl. Qed.
Lemma D_807e4 : decode_any W_807e4 = Some (Op ALU_SLTU 16 6 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_807e8 : bv 32 := 0x00062613.
Lemma F_807e8 : fetch_word Ubsan.M.loaded_segments (0x807e8 : word) = Some W_807e8.
Proof. vm_refl. Qed.
Lemma D_807e8 : decode_any W_807e8 = Some (OpImm ALU_SLT 12 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_807ec : bv 32 := 0x00c84633.
Lemma F_807ec : fetch_word Ubsan.M.loaded_segments (0x807ec : word) = Some W_807ec.
Proof. vm_refl. Qed.
Lemma D_807ec : decode_any W_807ec = Some (Op ALU_XOR 12 16 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_807f0 : bv 32 := 0x00164613.
Lemma F_807f0 : fetch_word Ubsan.M.loaded_segments (0x807f0 : word) = Some W_807f0.
Proof. vm_refl. Qed.
Lemma D_807f0 : decode_any W_807f0 = Some (OpImm ALU_XOR 12 12 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_807f4 : bv 32 := 0x00061463.
Lemma F_807f4 : fetch_word Ubsan.M.loaded_segments (0x807f4 : word) = Some W_807f4.
Proof. vm_refl. Qed.
Lemma D_807f4 : decode_any W_807f4 = Some (Branch BC_NE 12 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_807f8 : bv 32 := 0x4fd0106f.
Lemma F_807f8 : fetch_word Ubsan.M.loaded_segments (0x807f8 : word) = Some W_807f8.
Proof. vm_refl. Qed.
Lemma D_807f8 : decode_any W_807f8 = Some (Jal 0 7420, 4%Z).
Proof. vm_refl. Qed.

Definition W_807fc : bv 32 := 0x00000813.
Lemma F_807fc : fetch_word Ubsan.M.loaded_segments (0x807fc : word) = Some W_807fc.
Proof. vm_refl. Qed.
Lemma D_807fc : decode_any W_807fc = Some (OpImm ALU_ADD 16 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_80800 : bv 32 := 0x02013023.
Lemma F_80800 : fetch_word Ubsan.M.loaded_segments (0x80800 : word) = Some W_80800.
Proof. vm_refl. Qed.
Lemma D_80800 : decode_any W_80800 = Some (Store SZ8 2 0 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_80804 : bv 32 := 0x04c0006f.
Lemma F_80804 : fetch_word Ubsan.M.loaded_segments (0x80804 : word) = Some W_80804.
Proof. vm_refl. Qed.
Lemma D_80804 : decode_any W_80804 = Some (Jal 0 76, 4%Z).
Proof. vm_refl. Qed.

Definition W_80808 : bv 32 := 0x00545f9b.
Lemma F_80808 : fetch_word Ubsan.M.loaded_segments (0x80808 : word) = Some W_80808.
Proof. vm_refl. Qed.
Lemma D_80808 : decode_any W_80808 = Some (ShiftImm32 ALU_SRL 31 8 5, 4%Z).
Proof. vm_refl. Qed.

Definition W_8080c : bv 32 := 0x6c0f8263.
Lemma F_8080c : fetch_word Ubsan.M.loaded_segments (0x8080c : word) = Some W_8080c.
Proof. vm_refl. Qed.
Lemma D_8080c : decode_any W_8080c = Some (Branch BC_EQ 31 0 1732, 4%Z).
Proof. vm_refl. Qed.

Definition W_80810 : bv 32 := 0x004a0413.
Lemma F_80810 : fetch_word Ubsan.M.loaded_segments (0x80810 : word) = Some W_80810.
Proof. vm_refl. Qed.
Lemma D_80810 : decode_any W_80810 = Some (OpImm ALU_ADD 8 20 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_80814 : bv 32 := 0x00500613.
Lemma F_80814 : fetch_word Ubsan.M.loaded_segments (0x80814 : word) = Some W_80814.
Proof. vm_refl. Qed.
Lemma D_80814 : decode_any W_80814 = Some (OpImm ALU_ADD 12 0 5, 4%Z).
Proof. vm_refl. Qed.

Definition W_80818 : bv 32 := 0x00c47463.
Lemma F_80818 : fetch_word Ubsan.M.loaded_segments (0x80818 : word) = Some W_80818.
Proof. vm_refl. Qed.
Lemma D_80818 : decode_any W_80818 = Some (Branch BC_GEU 8 12 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_8081c : bv 32 := 0x4d90106f.
Lemma F_8081c : fetch_word Ubsan.M.loaded_segments (0x8081c : word) = Some W_8081c.
Proof. vm_refl. Qed.
Lemma D_8081c : decode_any W_8081c = Some (Jal 0 7384, 4%Z).
Proof. vm_refl. Qed.

Definition W_80820 : bv 32 := 0x004a8913.
Lemma F_80820 : fetch_word Ubsan.M.loaded_segments (0x80820 : word) = Some W_80820.
Proof. vm_refl. Qed.
Lemma D_80820 : decode_any W_80820 = Some (OpImm ALU_ADD 18 21 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_80824 : bv 32 := 0x00c97463.
Lemma F_80824 : fetch_word Ubsan.M.loaded_segments (0x80824 : word) = Some W_80824.
Proof. vm_refl. Qed.
Lemma D_80824 : decode_any W_80824 = Some (Branch BC_GEU 18 12 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_80828 : bv 32 := 0x4cd0106f.
Lemma F_80828 : fetch_word Ubsan.M.loaded_segments (0x80828 : word) = Some W_80828.
Proof. vm_refl. Qed.
Lemma D_80828 : decode_any W_80828 = Some (Jal 0 7372, 4%Z).
Proof. vm_refl. Qed.

Definition W_8082c : bv 32 := 0x00000613.
Lemma F_8082c : fetch_word Ubsan.M.loaded_segments (0x8082c : word) = Some W_8082c.
Proof. vm_refl. Qed.
Lemma D_8082c : decode_any W_8082c = Some (OpImm ALU_ADD 12 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_80830 : bv 32 := 0x00000b13.
Lemma F_80830 : fetch_word Ubsan.M.loaded_segments (0x80830 : word) = Some W_80830.
Proof. vm_refl. Qed.
Lemma D_80830 : decode_any W_80830 = Some (OpImm ALU_ADD 22 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_80834 : bv 32 := 0x6ac0006f.
Lemma F_80834 : fetch_word Ubsan.M.loaded_segments (0x80834 : word) = Some W_80834.
Proof. vm_refl. Qed.
Lemma D_80834 : decode_any W_80834 = Some (Jal 0 1708, 4%Z).
Proof. vm_refl. Qed.

Definition W_80838 : bv 32 := 0x00000813.
Lemma F_80838 : fetch_word Ubsan.M.loaded_segments (0x80838 : word) = Some W_80838.
Proof. vm_refl. Qed.
Lemma D_80838 : decode_any W_80838 = Some (OpImm ALU_ADD 16 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_8083c : bv 32 := 0x06013823.
Lemma F_8083c : fetch_word Ubsan.M.loaded_segments (0x8083c : word) = Some W_8083c.
Proof. vm_refl. Qed.
Lemma D_8083c : decode_any W_8083c = Some (Store SZ8 2 0 112, 4%Z).
Proof. vm_refl. Qed.

Definition W_80840 : bv 32 := 0x00000913.
Lemma F_80840 : fetch_word Ubsan.M.loaded_segments (0x80840 : word) = Some W_80840.
Proof. vm_refl. Qed.
Lemma D_80840 : decode_any W_80840 = Some (OpImm ALU_ADD 18 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_80844 : bv 32 := 0x00000313.
Lemma F_80844 : fetch_word Ubsan.M.loaded_segments (0x80844 : word) = Some W_80844.
Proof. vm_refl. Qed.
Lemma D_80844 : decode_any W_80844 = Some (OpImm ALU_ADD 6 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_80848 : bv 32 := 0x00100613.
Lemma F_80848 : fetch_word Ubsan.M.loaded_segments (0x80848 : word) = Some W_80848.
Proof. vm_refl. Qed.
Lemma D_80848 : decode_any W_80848 = Some (OpImm ALU_ADD 12 0 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_8084c : bv 32 := 0x02c13023.
Lemma F_8084c : fetch_word Ubsan.M.loaded_segments (0x8084c : word) = Some W_8084c.
Proof. vm_refl. Qed.
Lemma D_8084c : decode_any W_8084c = Some (Store SZ8 2 12 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_80850 : bv 32 := 0x00968633.
Lemma F_80850 : fetch_word Ubsan.M.loaded_segments (0x80850 : word) = Some W_80850.
Proof. vm_refl. Qed.
Lemma D_80850 : decode_any W_80850 = Some (Op ALU_ADD 12 13 9, 4%Z).
Proof. vm_refl. Qed.

Definition W_80854 : bv 32 := 0x009684bb.
Lemma F_80854 : fetch_word Ubsan.M.loaded_segments (0x80854 : word) = Some W_80854.
Proof. vm_refl. Qed.
Lemma D_80854 : decode_any W_80854 = Some (Op32 ALU_ADD 9 13 9, 4%Z).
Proof. vm_refl. Qed.

Definition W_80858 : bv 32 := 0x00c48463.
Lemma F_80858 : fetch_word Ubsan.M.loaded_segments (0x80858 : word) = Some W_80858.
Proof. vm_refl. Qed.
Lemma D_80858 : decode_any W_80858 = Some (Branch BC_EQ 9 12 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_8085c : bv 32 := 0x4990106f.
Lemma F_8085c : fetch_word Ubsan.M.loaded_segments (0x8085c : word) = Some W_8085c.
Proof. vm_refl. Qed.
Lemma D_8085c : decode_any W_8085c = Some (Jal 0 7320, 4%Z).
Proof. vm_refl. Qed.

Definition W_80860 : bv 32 := 0x01f67b13.
Lemma F_80860 : fetch_word Ubsan.M.loaded_segments (0x80860 : word) = Some W_80860.
Proof. vm_refl. Qed.
Lemma D_80860 : decode_any W_80860 = Some (OpImm ALU_AND 22 12 31, 4%Z).
Proof. vm_refl. Qed.

Definition W_80864 : bv 32 := 0x001b3613.
Lemma F_80864 : fetch_word Ubsan.M.loaded_segments (0x80864 : word) = Some W_80864.
Proof. vm_refl. Qed.
Lemma D_80864 : decode_any W_80864 = Some (OpImm ALU_SLTU 12 22 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_80868 : bv 32 := 0x01066633.
Lemma F_80868 : fetch_word Ubsan.M.loaded_segments (0x80868 : word) = Some W_80868.
Proof. vm_refl. Qed.
Lemma D_80868 : decode_any W_80868 = Some (Op ALU_OR 12 12 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_8086c : bv 32 := 0x41da043b.
Lemma F_8086c : fetch_word Ubsan.M.loaded_segments (0x8086c : word) = Some W_8086c.
Proof. vm_refl. Qed.
Lemma D_8086c : decode_any W_8086c = Some (Op32 ALU_SUB 8 20 29, 4%Z).
Proof. vm_refl. Qed.

Definition W_80870 : bv 32 := 0x00c13c23.
Lemma F_80870 : fetch_word Ubsan.M.loaded_segments (0x80870 : word) = Some W_80870.
Proof. vm_refl. Qed.
Lemma D_80870 : decode_any W_80870 = Some (Store SZ8 2 12 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_80874 : bv 32 := 0x00060863.
Lemma F_80874 : fetch_word Ubsan.M.loaded_segments (0x80874 : word) = Some W_80874.
Proof. vm_refl. Qed.
Lemma D_80874 : decode_any W_80874 = Some (Branch BC_EQ 12 0 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_80878 : bv 32 := 0x00000513.
Lemma F_80878 : fetch_word Ubsan.M.loaded_segments (0x80878 : word) = Some W_80878.
Proof. vm_refl. Qed.
Lemma D_80878 : decode_any W_80878 = Some (OpImm ALU_ADD 10 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_8087c : bv 32 := 0x06013423.
Lemma F_8087c : fetch_word Ubsan.M.loaded_segments (0x8087c : word) = Some W_8087c.
Proof. vm_refl. Qed.
Lemma D_8087c : decode_any W_8087c = Some (Store SZ8 2 0 104, 4%Z).
Proof. vm_refl. Qed.

Definition W_80880 : bv 32 := 0x1940006f.
Lemma F_80880 : fetch_word Ubsan.M.loaded_segments (0x80880 : word) = Some W_80880.
Proof. vm_refl. Qed.
Lemma D_80880 : decode_any W_80880 = Some (Jal 0 404, 4%Z).
Proof. vm_refl. Qed.

Definition W_80884 : bv 32 := 0x002b1493.
Lemma F_80884 : fetch_word Ubsan.M.loaded_segments (0x80884 : word) = Some W_80884.
Proof. vm_refl. Qed.
Lemma D_80884 : decode_any W_80884 = Some (ShiftImm ALU_SLL 9 22 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_80888 : bv 32 := 0xfff9f617.
Lemma F_80888 : fetch_word Ubsan.M.loaded_segments (0x80888 : word) = Some W_80888.
Proof. vm_refl. Qed.
Lemma D_80888 : decode_any W_80888 = Some (Auipc 12 1048479, 4%Z).
Proof. vm_refl. Qed.

Definition W_8088c : bv 32 := 0xc3c60a13.
Lemma F_8088c : fetch_word Ubsan.M.loaded_segments (0x8088c : word) = Some W_8088c.
Proof. vm_refl. Qed.
Lemma D_8088c : decode_any W_8088c = Some (OpImm ALU_ADD 20 12 3132, 4%Z).
Proof. vm_refl. Qed.

Definition W_80890 : bv 32 := 0xfffa4613.
Lemma F_80890 : fetch_word Ubsan.M.loaded_segments (0x80890 : word) = Some W_80890.
Proof. vm_refl. Qed.
Lemma D_80890 : decode_any W_80890 = Some (OpImm ALU_XOR 12 20 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_80894 : bv 32 := 0x00967463.
Lemma F_80894 : fetch_word Ubsan.M.loaded_segments (0x80894 : word) = Some W_80894.
Proof. vm_refl. Qed.
Lemma D_80894 : decode_any W_80894 = Some (Branch BC_GEU 12 9 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_80898 : bv 32 := 0x45d0106f.
Lemma F_80898 : fetch_word Ubsan.M.loaded_segments (0x80898 : word) = Some W_80898.
Proof. vm_refl. Qed.
Lemma D_80898 : decode_any W_80898 = Some (Jal 0 7260, 4%Z).
Proof. vm_refl. Qed.

Definition W_8089c : bv 32 := 0x02770633.
Lemma F_8089c : fetch_word Ubsan.M.loaded_segments (0x8089c : word) = Some W_8089c.
Proof. vm_refl. Qed.
Lemma D_8089c : decode_any W_8089c = Some (Mul M_MUL 12 14 7, 4%Z).
Proof. vm_refl. Qed.

Definition W_808a0 : bv 32 := 0x0277083b.
Lemma F_808a0 : fetch_word Ubsan.M.loaded_segments (0x808a0 : word) = Some W_808a0.
Proof. vm_refl. Qed.
Lemma D_808a0 : decode_any W_808a0 = Some (Mul32 M_MUL 16 14 7, 4%Z).
Proof. vm_refl. Qed.

Definition W_808a4 : bv 32 := 0x00c80463.
Lemma F_808a4 : fetch_word Ubsan.M.loaded_segments (0x808a4 : word) = Some W_808a4.
Proof. vm_refl. Qed.
Lemma D_808a4 : decode_any W_808a4 = Some (Branch BC_EQ 16 12 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_808a8 : bv 32 := 0x44d0106f.
Lemma F_808a8 : fetch_word Ubsan.M.loaded_segments (0x808a8 : word) = Some W_808a8.
Proof. vm_refl. Qed.
Lemma D_808a8 : decode_any W_808a8 = Some (Jal 0 7244, 4%Z).
Proof. vm_refl. Qed.

Definition W_808ac : bv 32 := 0x0006061b.
Lemma F_808ac : fetch_word Ubsan.M.loaded_segments (0x808ac : word) = Some W_808ac.
Proof. vm_refl. Qed.
Lemma D_808ac : decode_any W_808ac = Some (OpImm32 12 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_808b0 : bv 32 := 0x00261393.
Lemma F_808b0 : fetch_word Ubsan.M.loaded_segments (0x808b0 : word) = Some W_808b0.
Proof. vm_refl. Qed.
Lemma D_808b0 : decode_any W_808b0 = Some (ShiftImm ALU_SLL 7 12 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_808b4 : bv 32 := 0x007503b3.
Lemma F_808b4 : fetch_word Ubsan.M.loaded_segments (0x808b4 : word) = Some W_808b4.
Proof. vm_refl. Qed.
Lemma D_808b4 : decode_any W_808b4 = Some (Op ALU_ADD 7 10 7, 4%Z).
Proof. vm_refl. Qed.

Definition W_808b8 : bv 32 := 0x00a03833.
Lemma F_808b8 : fetch_word Ubsan.M.loaded_segments (0x808b8 : word) = Some W_808b8.
Proof. vm_refl. Qed.
Lemma D_808b8 : decode_any W_808b8 = Some (Op ALU_SLTU 16 0 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_808bc : bv 32 := 0x0013be13.
Lemma F_808bc : fetch_word Ubsan.M.loaded_segments (0x808bc : word) = Some W_808bc.
Proof. vm_refl. Qed.
Lemma D_808bc : decode_any W_808bc = Some (OpImm ALU_SLTU 28 7 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_808c0 : bv 32 := 0x01c81463.
Lemma F_808c0 : fetch_word Ubsan.M.loaded_segments (0x808c0 : word) = Some W_808c0.
Proof. vm_refl. Qed.
Lemma D_808c0 : decode_any W_808c0 = Some (Branch BC_NE 16 28 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_808c4 : bv 32 := 0x4310106f.
Lemma F_808c4 : fetch_word Ubsan.M.loaded_segments (0x808c4 : word) = Some W_808c4.
Proof. vm_refl. Qed.
Lemma D_808c4 : decode_any W_808c4 = Some (Jal 0 7216, 4%Z).
Proof. vm_refl. Qed.

Definition W_808c8 : bv 32 := 0x00a3b533.
Lemma F_808c8 : fetch_word Ubsan.M.loaded_segments (0x808c8 : word) = Some W_808c8.
Proof. vm_refl. Qed.
Lemma D_808c8 : decode_any W_808c8 = Some (Op ALU_SLTU 10 7 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_808cc : bv 32 := 0x00062613.
Lemma F_808cc : fetch_word Ubsan.M.loaded_segments (0x808cc : word) = Some W_808cc.
Proof. vm_refl. Qed.
Lemma D_808cc : decode_any W_808cc = Some (OpImm ALU_SLT 12 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_808d0 : bv 32 := 0x00c54533.
Lemma F_808d0 : fetch_word Ubsan.M.loaded_segments (0x808d0 : word) = Some W_808d0.
Proof. vm_refl. Qed.
Lemma D_808d0 : decode_any W_808d0 = Some (Op ALU_XOR 10 10 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_808d4 : bv 32 := 0x00154513.
Lemma F_808d4 : fetch_word Ubsan.M.loaded_segments (0x808d4 : word) = Some W_808d4.
Proof. vm_refl. Qed.
Lemma D_808d4 : decode_any W_808d4 = Some (OpImm ALU_XOR 10 10 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_808d8 : bv 32 := 0x00051463.
Lemma F_808d8 : fetch_word Ubsan.M.loaded_segments (0x808d8 : word) = Some W_808d8.
Proof. vm_refl. Qed.
Lemma D_808d8 : decode_any W_808d8 = Some (Branch BC_NE 10 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_808dc : bv 32 := 0x4190106f.
Lemma F_808dc : fetch_word Ubsan.M.loaded_segments (0x808dc : word) = Some W_808dc.
Proof. vm_refl. Qed.
Lemma D_808dc : decode_any W_808dc = Some (Jal 0 7192, 4%Z).
Proof. vm_refl. Qed.

Definition W_808e0 : bv 32 := 0x000b8b9b.
Lemma F_808e0 : fetch_word Ubsan.M.loaded_segments (0x808e0 : word) = Some W_808e0.
Proof. vm_refl. Qed.
Lemma D_808e0 : decode_any W_808e0 = Some (OpImm32 23 23 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_808e4 : bv 32 := 0x01768533.
Lemma F_808e4 : fetch_word Ubsan.M.loaded_segments (0x808e4 : word) = Some W_808e4.
Proof. vm_refl. Qed.
Lemma D_808e4 : decode_any W_808e4 = Some (Op ALU_ADD 10 13 23, 4%Z).
Proof. vm_refl. Qed.

Definition W_808e8 : bv 32 := 0x0176863b.
Lemma F_808e8 : fetch_word Ubsan.M.loaded_segments (0x808e8 : word) = Some W_808e8.
Proof. vm_refl. Qed.
Lemma D_808e8 : decode_any W_808e8 = Some (Op32 ALU_ADD 12 13 23, 4%Z).
Proof. vm_refl. Qed.

Definition W_808ec : bv 32 := 0x00a60463.
Lemma F_808ec : fetch_word Ubsan.M.loaded_segments (0x808ec : word) = Some W_808ec.
Proof. vm_refl. Qed.
Lemma D_808ec : decode_any W_808ec = Some (Branch BC_EQ 12 10 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_808f0 : bv 32 := 0x4050106f.
Lemma F_808f0 : fetch_word Ubsan.M.loaded_segments (0x808f0 : word) = Some W_808f0.
Proof. vm_refl. Qed.
Lemma D_808f0 : decode_any W_808f0 = Some (Jal 0 7172, 4%Z).
Proof. vm_refl. Qed.

Definition W_808f4 : bv 32 := 0x4055551b.
Lemma F_808f4 : fetch_word Ubsan.M.loaded_segments (0x808f4 : word) = Some W_808f4.
Proof. vm_refl. Qed.
Lemma D_808f4 : decode_any W_808f4 = Some (ShiftImm32 ALU_SRA 10 10 5, 4%Z).
Proof. vm_refl. Qed.

Definition W_808f8 : bv 32 := 0x00251613.
Lemma F_808f8 : fetch_word Ubsan.M.loaded_segments (0x808f8 : word) = Some W_808f8.
Proof. vm_refl. Qed.
Lemma D_808f8 : decode_any W_808f8 = Some (ShiftImm ALU_SLL 12 10 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_808fc : bv 32 := 0x00760633.
Lemma F_808fc : fetch_word Ubsan.M.loaded_segments (0x808fc : word) = Some W_808fc.
Proof. vm_refl. Qed.
Lemma D_808fc : decode_any W_808fc = Some (Op ALU_ADD 12 12 7, 4%Z).
Proof. vm_refl. Qed.

Definition W_80900 : bv 32 := 0x00163693.
Lemma F_80900 : fetch_word Ubsan.M.loaded_segments (0x80900 : word) = Some W_80900.
Proof. vm_refl. Qed.
Lemma D_80900 : decode_any W_80900 = Some (OpImm ALU_SLTU 13 12 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_80904 : bv 32 := 0x00d81463.
Lemma F_80904 : fetch_word Ubsan.M.loaded_segments (0x80904 : word) = Some W_80904.
Proof. vm_refl. Qed.
Lemma D_80904 : decode_any W_80904 = Some (Branch BC_NE 16 13 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_80908 : bv 32 := 0x3ed0106f.
Lemma F_80908 : fetch_word Ubsan.M.loaded_segments (0x80908 : word) = Some W_80908.
Proof. vm_refl. Qed.
Lemma D_80908 : decode_any W_80908 = Some (Jal 0 7148, 4%Z).
Proof. vm_refl. Qed.

Definition W_8090c : bv 32 := 0x007636b3.
Lemma F_8090c : fetch_word Ubsan.M.loaded_segments (0x8090c : word) = Some W_8090c.
Proof. vm_refl. Qed.
Lemma D_8090c : decode_any W_8090c = Some (Op ALU_SLTU 13 12 7, 4%Z).
Proof. vm_refl. Qed.

Definition W_80910 : bv 32 := 0x00052513.
Lemma F_80910 : fetch_word Ubsan.M.loaded_segments (0x80910 : word) = Some W_80910.
Proof. vm_refl. Qed.
Lemma D_80910 : decode_any W_80910 = Some (OpImm ALU_SLT 10 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_80914 : bv 32 := 0x00a6c533.
Lemma F_80914 : fetch_word Ubsan.M.loaded_segments (0x80914 : word) = Some W_80914.
Proof. vm_refl. Qed.
Lemma D_80914 : decode_any W_80914 = Some (Op ALU_XOR 10 13 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_80918 : bv 32 := 0x00154513.
Lemma F_80918 : fetch_word Ubsan.M.loaded_segments (0x80918 : word) = Some W_80918.
Proof. vm_refl. Qed.
Lemma D_80918 : decode_any W_80918 = Some (OpImm ALU_XOR 10 10 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_8091c : bv 32 := 0x00051463.
Lemma F_8091c : fetch_word Ubsan.M.loaded_segments (0x8091c : word) = Some W_8091c.
Proof. vm_refl. Qed.
Lemma D_8091c : decode_any W_8091c = Some (Branch BC_NE 10 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_80920 : bv 32 := 0x3d50106f.
Lemma F_80920 : fetch_word Ubsan.M.loaded_segments (0x80920 : word) = Some W_80920.
Proof. vm_refl. Qed.
Lemma D_80920 : decode_any W_80920 = Some (Jal 0 7124, 4%Z).
Proof. vm_refl. Qed.

Definition W_80924 : bv 32 := 0x07013683.
Lemma F_80924 : fetch_word Ubsan.M.loaded_segments (0x80924 : word) = Some W_80924.
Proof. vm_refl. Qed.
Lemma D_80924 : decode_any W_80924 = Some (Load SZ8 true 13 2 112, 4%Z).
Proof. vm_refl. Qed.

Definition W_80928 : bv 32 := 0x00269693.
Lemma F_80928 : fetch_word Ubsan.M.loaded_segments (0x80928 : word) = Some W_80928.
Proof. vm_refl. Qed.
Lemma D_80928 : decode_any W_80928 = Some (ShiftImm ALU_SLL 13 13 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_8092c : bv 32 := 0x00d60533.
Lemma F_8092c : fetch_word Ubsan.M.loaded_segments (0x8092c : word) = Some W_8092c.
Proof. vm_refl. Qed.
Lemma D_8092c : decode_any W_8092c = Some (Op ALU_ADD 10 12 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_80930 : bv 32 := 0x00c57463.
Lemma F_80930 : fetch_word Ubsan.M.loaded_segments (0x80930 : word) = Some W_80930.
Proof. vm_refl. Qed.
Lemma D_80930 : decode_any W_80930 = Some (Branch BC_GEU 10 12 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_80934 : bv 32 := 0x3c10106f.
Lemma F_80934 : fetch_word Ubsan.M.loaded_segments (0x80934 : word) = Some W_80934.
Proof. vm_refl. Qed.
Lemma D_80934 : decode_any W_80934 = Some (Jal 0 7104, 4%Z).
Proof. vm_refl. Qed.

Definition W_80938 : bv 32 := 0x00153613.
Lemma F_80938 : fetch_word Ubsan.M.loaded_segments (0x80938 : word) = Some W_80938.
Proof. vm_refl. Qed.
Lemma D_80938 : decode_any W_80938 = Some (OpImm ALU_SLTU 12 10 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_8093c : bv 32 := 0x00c84633.
Lemma F_8093c : fetch_word Ubsan.M.loaded_segments (0x8093c : word) = Some W_8093c.
Proof. vm_refl. Qed.
Lemma D_8093c : decode_any W_8093c = Some (Op ALU_XOR 12 16 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_80940 : bv 32 := 0x00061463.
Lemma F_80940 : fetch_word Ubsan.M.loaded_segments (0x80940 : word) = Some W_80940.
Proof. vm_refl. Qed.
Lemma D_80940 : decode_any W_80940 = Some (Branch BC_NE 12 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_80944 : bv 32 := 0x3b10106f.
Lemma F_80944 : fetch_word Ubsan.M.loaded_segments (0x80944 : word) = Some W_80944.
Proof. vm_refl. Qed.
Lemma D_80944 : decode_any W_80944 = Some (Jal 0 7088, 4%Z).
Proof. vm_refl. Qed.

Definition W_80948 : bv 32 := 0x05813803.
Lemma F_80948 : fetch_word Ubsan.M.loaded_segments (0x80948 : word) = Some W_80948.
Proof. vm_refl. Qed.
Lemma D_80948 : decode_any W_80948 = Some (Load SZ8 true 16 2 88, 4%Z).
Proof. vm_refl. Qed.

Definition W_8094c : bv 32 := 0x02580633.
Lemma F_8094c : fetch_word Ubsan.M.loaded_segments (0x8094c : word) = Some W_8094c.
Proof. vm_refl. Qed.
Lemma D_8094c : decode_any W_8094c = Some (Mul M_MUL 12 16 5, 4%Z).
Proof. vm_refl. Qed.

Definition W_80950 : bv 32 := 0x0258083b.
Lemma F_80950 : fetch_word Ubsan.M.loaded_segments (0x80950 : word) = Some W_80950.
Proof. vm_refl. Qed.
Lemma D_80950 : decode_any W_80950 = Some (Mul32 M_MUL 16 16 5, 4%Z).
Proof. vm_refl. Qed.

Definition W_80954 : bv 32 := 0x00c80463.
Lemma F_80954 : fetch_word Ubsan.M.loaded_segments (0x80954 : word) = Some W_80954.
Proof. vm_refl. Qed.
Lemma D_80954 : decode_any W_80954 = Some (Branch BC_EQ 16 12 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_80958 : bv 32 := 0x39d0106f.
Lemma F_80958 : fetch_word Ubsan.M.loaded_segments (0x80958 : word) = Some W_80958.
Proof. vm_refl. Qed.
Lemma D_80958 : decode_any W_80958 = Some (Jal 0 7068, 4%Z).
Proof. vm_refl. Qed.

Definition W_8095c : bv 32 := 0x0006061b.
Lemma F_8095c : fetch_word Ubsan.M.loaded_segments (0x8095c : word) = Some W_8095c.
Proof. vm_refl. Qed.
Lemma D_8095c : decode_any W_8095c = Some (OpImm32 12 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_80960 : bv 32 := 0x00261293.
Lemma F_80960 : fetch_word Ubsan.M.loaded_segments (0x80960 : word) = Some W_80960.
Proof. vm_refl. Qed.
Lemma D_80960 : decode_any W_80960 = Some (ShiftImm ALU_SLL 5 12 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_80964 : bv 32 := 0x005982b3.
Lemma F_80964 : fetch_word Ubsan.M.loaded_segments (0x80964 : word) = Some W_80964.
Proof. vm_refl. Qed.
Lemma D_80964 : decode_any W_80964 = Some (Op ALU_ADD 5 19 5, 4%Z).
Proof. vm_refl. Qed.

Definition W_80968 : bv 32 := 0x01303833.
Lemma F_80968 : fetch_word Ubsan.M.loaded_segments (0x80968 : word) = Some W_80968.
Proof. vm_refl. Qed.
Lemma D_80968 : decode_any W_80968 = Some (Op ALU_SLTU 16 0 19, 4%Z).
Proof. vm_refl. Qed.

Definition W_8096c : bv 32 := 0x0012b393.
Lemma F_8096c : fetch_word Ubsan.M.loaded_segments (0x8096c : word) = Some W_8096c.
Proof. vm_refl. Qed.
Lemma D_8096c : decode_any W_8096c = Some (OpImm ALU_SLTU 7 5 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_80970 : bv 32 := 0x00781463.
Lemma F_80970 : fetch_word Ubsan.M.loaded_segments (0x80970 : word) = Some W_80970.
Proof. vm_refl. Qed.
Lemma D_80970 : decode_any W_80970 = Some (Branch BC_NE 16 7 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_80974 : bv 32 := 0x3810106f.
Lemma F_80974 : fetch_word Ubsan.M.loaded_segments (0x80974 : word) = Some W_80974.
Proof. vm_refl. Qed.
Lemma D_80974 : decode_any W_80974 = Some (Jal 0 7040, 4%Z).
Proof. vm_refl. Qed.

Definition W_80978 : bv 32 := 0x0132b3b3.
Lemma F_80978 : fetch_word Ubsan.M.loaded_segments (0x80978 : word) = Some W_80978.
Proof. vm_refl. Qed.
Lemma D_80978 : decode_any W_80978 = Some (Op ALU_SLTU 7 5 19, 4%Z).
Proof. vm_refl. Qed.

Definition W_8097c : bv 32 := 0x00062613.
Lemma F_8097c : fetch_word Ubsan.M.loaded_segments (0x8097c : word) = Some W_8097c.
Proof. vm_refl. Qed.
Lemma D_8097c : decode_any W_8097c = Some (OpImm ALU_SLT 12 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_80980 : bv 32 := 0x00c3c633.
Lemma F_80980 : fetch_word Ubsan.M.loaded_segments (0x80980 : word) = Some W_80980.
Proof. vm_refl. Qed.
Lemma D_80980 : decode_any W_80980 = Some (Op ALU_XOR 12 7 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_80984 : bv 32 := 0x00164613.
Lemma F_80984 : fetch_word Ubsan.M.loaded_segments (0x80984 : word) = Some W_80984.
Proof. vm_refl. Qed.
Lemma D_80984 : decode_any W_80984 = Some (OpImm ALU_XOR 12 12 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_80988 : bv 32 := 0x00061463.
Lemma F_80988 : fetch_word Ubsan.M.loaded_segments (0x80988 : word) = Some W_80988.
Proof. vm_refl. Qed.
Lemma D_80988 : decode_any W_80988 = Some (Branch BC_NE 12 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_8098c : bv 32 := 0x3690106f.
Lemma F_8098c : fetch_word Ubsan.M.loaded_segments (0x8098c : word) = Some W_8098c.
Proof. vm_refl. Qed.
Lemma D_8098c : decode_any W_8098c = Some (Jal 0 7016, 4%Z).
Proof. vm_refl. Qed.

Definition W_80990 : bv 32 := 0x017c0633.
Lemma F_80990 : fetch_word Ubsan.M.loaded_segments (0x80990 : word) = Some W_80990.
Proof. vm_refl. Qed.
Lemma D_80990 : decode_any W_80990 = Some (Op ALU_ADD 12 24 23, 4%Z).
Proof. vm_refl. Qed.

Definition W_80994 : bv 32 := 0x017c03bb.
Lemma F_80994 : fetch_word Ubsan.M.loaded_segments (0x80994 : word) = Some W_80994.
Proof. vm_refl. Qed.
Lemma D_80994 : decode_any W_80994 = Some (Op32 ALU_ADD 7 24 23, 4%Z).
Proof. vm_refl. Qed.

Definition W_80998 : bv 32 := 0x00c38463.
Lemma F_80998 : fetch_word Ubsan.M.loaded_segments (0x80998 : word) = Some W_80998.
Proof. vm_refl. Qed.
Lemma D_80998 : decode_any W_80998 = Some (Branch BC_EQ 7 12 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_8099c : bv 32 := 0x3590106f.
Lemma F_8099c : fetch_word Ubsan.M.loaded_segments (0x8099c : word) = Some W_8099c.
Proof. vm_refl. Qed.
Lemma D_8099c : decode_any W_8099c = Some (Jal 0 7000, 4%Z).
Proof. vm_refl. Qed.

Definition W_809a0 : bv 32 := 0x4056561b.
Lemma F_809a0 : fetch_word Ubsan.M.loaded_segments (0x809a0 : word) = Some W_809a0.
Proof. vm_refl. Qed.
Lemma D_809a0 : decode_any W_809a0 = Some (ShiftImm32 ALU_SRA 12 12 5, 4%Z).
Proof. vm_refl. Qed.

Definition W_809a4 : bv 32 := 0x00261393.
Lemma F_809a4 : fetch_word Ubsan.M.loaded_segments (0x809a4 : word) = Some W_809a4.
Proof. vm_refl. Qed.
Lemma D_809a4 : decode_any W_809a4 = Some (ShiftImm ALU_SLL 7 12 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_809a8 : bv 32 := 0x005383b3.
Lemma F_809a8 : fetch_word Ubsan.M.loaded_segments (0x809a8 : word) = Some W_809a8.
Proof. vm_refl. Qed.
Lemma D_809a8 : decode_any W_809a8 = Some (Op ALU_ADD 7 7 5, 4%Z).
Proof. vm_refl. Qed.

Definition W_809ac : bv 32 := 0x0013be13.
Lemma F_809ac : fetch_word Ubsan.M.loaded_segments (0x809ac : word) = Some W_809ac.
Proof. vm_refl. Qed.
Lemma D_809ac : decode_any W_809ac = Some (OpImm ALU_SLTU 28 7 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_809b0 : bv 32 := 0x01c81463.
Lemma F_809b0 : fetch_word Ubsan.M.loaded_segments (0x809b0 : word) = Some W_809b0.
Proof. vm_refl. Qed.
Lemma D_809b0 : decode_any W_809b0 = Some (Branch BC_NE 16 28 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_809b4 : bv 32 := 0x3410106f.
Lemma F_809b4 : fetch_word Ubsan.M.loaded_segments (0x809b4 : word) = Some W_809b4.
Proof. vm_refl. Qed.
Lemma D_809b4 : decode_any W_809b4 = Some (Jal 0 6976, 4%Z).
Proof. vm_refl. Qed.

Definition W_809b8 : bv 32 := 0x0053b2b3.
Lemma F_809b8 : fetch_word Ubsan.M.loaded_segments (0x809b8 : word) = Some W_809b8.
Proof. vm_refl. Qed.
Lemma D_809b8 : decode_any W_809b8 = Some (Op ALU_SLTU 5 7 5, 4%Z).
Proof. vm_refl. Qed.

Definition W_809bc : bv 32 := 0x00062613.
Lemma F_809bc : fetch_word Ubsan.M.loaded_segments (0x809bc : word) = Some W_809bc.
Proof. vm_refl. Qed.
Lemma D_809bc : decode_any W_809bc = Some (OpImm ALU_SLT 12 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_809c0 : bv 32 := 0x00c2c633.
Lemma F_809c0 : fetch_word Ubsan.M.loaded_segments (0x809c0 : word) = Some W_809c0.
Proof. vm_refl. Qed.
Lemma D_809c0 : decode_any W_809c0 = Some (Op ALU_XOR 12 5 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_809c4 : bv 32 := 0x00164613.
Lemma F_809c4 : fetch_word Ubsan.M.loaded_segments (0x809c4 : word) = Some W_809c4.
Proof. vm_refl. Qed.
Lemma D_809c4 : decode_any W_809c4 = Some (OpImm ALU_XOR 12 12 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_809c8 : bv 32 := 0x00061463.
Lemma F_809c8 : fetch_word Ubsan.M.loaded_segments (0x809c8 : word) = Some W_809c8.
Proof. vm_refl. Qed.
Lemma D_809c8 : decode_any W_809c8 = Some (Branch BC_NE 12 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_809cc : bv 32 := 0x3290106f.
Lemma F_809cc : fetch_word Ubsan.M.loaded_segments (0x809cc : word) = Some W_809cc.
Proof. vm_refl. Qed.
Lemma D_809cc : decode_any W_809cc = Some (Jal 0 6952, 4%Z).
Proof. vm_refl. Qed.

Definition W_809d0 : bv 32 := 0x007686b3.
Lemma F_809d0 : fetch_word Ubsan.M.loaded_segments (0x809d0 : word) = Some W_809d0.
Proof. vm_refl. Qed.
Lemma D_809d0 : decode_any W_809d0 = Some (Op ALU_ADD 13 13 7, 4%Z).
Proof. vm_refl. Qed.

Definition W_809d4 : bv 32 := 0x0076f463.
Lemma F_809d4 : fetch_word Ubsan.M.loaded_segments (0x809d4 : word) = Some W_809d4.
Proof. vm_refl. Qed.
Lemma D_809d4 : decode_any W_809d4 = Some (Branch BC_GEU 13 7 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_809d8 : bv 32 := 0x31d0106f.
Lemma F_809d8 : fetch_word Ubsan.M.loaded_segments (0x809d8 : word) = Some W_809d8.
Proof. vm_refl. Qed.
Lemma D_809d8 : decode_any W_809d8 = Some (Jal 0 6940, 4%Z).
Proof. vm_refl. Qed.

Definition W_809dc : bv 32 := 0x0016b613.
Lemma F_809dc : fetch_word Ubsan.M.loaded_segments (0x809dc : word) = Some W_809dc.
Proof. vm_refl. Qed.
Lemma D_809dc : decode_any W_809dc = Some (OpImm ALU_SLTU 12 13 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_809e0 : bv 32 := 0x00c84633.
Lemma F_809e0 : fetch_word Ubsan.M.loaded_segments (0x809e0 : word) = Some W_809e0.
Proof. vm_refl. Qed.
Lemma D_809e0 : decode_any W_809e0 = Some (Op ALU_XOR 12 16 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_809e4 : bv 32 := 0x00061463.
Lemma F_809e4 : fetch_word Ubsan.M.loaded_segments (0x809e4 : word) = Some W_809e4.
Proof. vm_refl. Qed.
Lemma D_809e4 : decode_any W_809e4 = Some (Branch BC_NE 12 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_809e8 : bv 32 := 0x30d0106f.
Lemma F_809e8 : fetch_word Ubsan.M.loaded_segments (0x809e8 : word) = Some W_809e8.
Proof. vm_refl. Qed.
Lemma D_809e8 : decode_any W_809e8 = Some (Jal 0 6924, 4%Z).
Proof. vm_refl. Qed.

Definition W_809ec : bv 32 := 0x009a04b3.
Lemma F_809ec : fetch_word Ubsan.M.loaded_segments (0x809ec : word) = Some W_809ec.
Proof. vm_refl. Qed.
Lemma D_809ec : decode_any W_809ec = Some (Op ALU_ADD 9 20 9, 4%Z).
Proof. vm_refl. Qed.

Definition W_809f0 : bv 32 := 0x0004a603.
Lemma F_809f0 : fetch_word Ubsan.M.loaded_segments (0x809f0 : word) = Some W_809f0.
Proof. vm_refl. Qed.
Lemma D_809f0 : decode_any W_809f0 = Some (Load SZ4 true 12 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_809f4 : bv 32 := 0x06c13023.
Lemma F_809f4 : fetch_word Ubsan.M.loaded_segments (0x809f4 : word) = Some W_809f4.
Proof. vm_refl. Qed.
Lemma D_809f4 : decode_any W_809f4 = Some (Store SZ8 2 12 96, 4%Z).
Proof. vm_refl. Qed.

Definition W_809f8 : bv 32 := 0x07013603.
Lemma F_809f8 : fetch_word Ubsan.M.loaded_segments (0x809f8 : word) = Some W_809f8.
Proof. vm_refl. Qed.
Lemma D_809f8 : decode_any W_809f8 = Some (Load SZ8 true 12 2 112, 4%Z).
Proof. vm_refl. Qed.

Definition W_809fc : bv 32 := 0x00261613.
Lemma F_809fc : fetch_word Ubsan.M.loaded_segments (0x809fc : word) = Some W_809fc.
Proof. vm_refl. Qed.
Lemma D_809fc : decode_any W_809fc = Some (ShiftImm ALU_SLL 12 12 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_80a00 : bv 32 := 0x00c38633.
Lemma F_80a00 : fetch_word Ubsan.M.loaded_segments (0x80a00 : word) = Some W_80a00.
Proof. vm_refl. Qed.
Lemma D_80a00 : decode_any W_80a00 = Some (Op ALU_ADD 12 7 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_80a04 : bv 32 := 0x06c13423.
Lemma F_80a04 : fetch_word Ubsan.M.loaded_segments (0x80a04 : word) = Some W_80a04.
Proof. vm_refl. Qed.
Lemma D_80a04 : decode_any W_80a04 = Some (Store SZ8 2 12 104, 4%Z).
Proof. vm_refl. Qed.

Definition W_80a08 : bv 32 := 0x01642633.
Lemma F_80a08 : fetch_word Ubsan.M.loaded_segments (0x80a08 : word) = Some W_80a08.
Proof. vm_refl. Qed.
Lemma D_80a08 : decode_any W_80a08 = Some (Op ALU_SLT 12 8 22, 4%Z).
Proof. vm_refl. Qed.

Definition W_80a0c : bv 32 := 0x00164613.
Lemma F_80a0c : fetch_word Ubsan.M.loaded_segments (0x80a0c : word) = Some W_80a0c.
Proof. vm_refl. Qed.
Lemma D_80a0c : decode_any W_80a0c = Some (OpImm ALU_XOR 12 12 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_80a10 : bv 32 := 0x00c13423.
Lemma F_80a10 : fetch_word Ubsan.M.loaded_segments (0x80a10 : word) = Some W_80a10.
Proof. vm_refl. Qed.
Lemma D_80a10 : decode_any W_80a10 = Some (Store SZ8 2 12 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_80a14 : bv 32 := 0xfff92697.
Lemma F_80a14 : fetch_word Ubsan.M.loaded_segments (0x80a14 : word) = Some W_80a14.
Proof. vm_refl. Qed.
Lemma D_80a14 : decode_any W_80a14 = Some (Auipc 13 1048466, 4%Z).
Proof. vm_refl. Qed.

Definition W_80a18 : bv 32 := 0xfff58613.
Lemma F_80a18 : fetch_word Ubsan.M.loaded_segments (0x80a18 : word) = Some W_80a18.
Proof. vm_refl. Qed.
Lemma D_80a18 : decode_any W_80a18 = Some (OpImm ALU_ADD 12 11 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_80a1c : bv 32 := 0x00d00813.
Lemma F_80a1c : fetch_word Ubsan.M.loaded_segments (0x80a1c : word) = Some W_80a1c.
Proof. vm_refl. Qed.
Lemma D_80a1c : decode_any W_80a1c = Some (OpImm ALU_ADD 16 0 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_80a20 : bv 32 := 0xd9768693.
Lemma F_80a20 : fetch_word Ubsan.M.loaded_segments (0x80a20 : word) = Some W_80a20.
Proof. vm_refl. Qed.
Lemma D_80a20 : decode_any W_80a20 = Some (OpImm ALU_ADD 13 13 3479, 4%Z).
Proof. vm_refl. Qed.

Definition W_80a24 : bv 32 := 0x1cc86ce3.
Lemma F_80a24 : fetch_word Ubsan.M.loaded_segments (0x80a24 : word) = Some W_80a24.
Proof. vm_refl. Qed.
Lemma D_80a24 : decode_any W_80a24 = Some (Branch BC_LTU 16 12 2520, 4%Z).
Proof. vm_refl. Qed.

Definition W_80a28 : bv 32 := 0x00261613.
Lemma F_80a28 : fetch_word Ubsan.M.loaded_segments (0x80a28 : word) = Some W_80a28.
Proof. vm_refl. Qed.
Lemma D_80a28 : decode_any W_80a28 = Some (ShiftImm ALU_SLL 12 12 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_80a2c : bv 32 := 0xfff9f817.
Lemma F_80a2c : fetch_word Ubsan.M.loaded_segments (0x80a2c : word) = Some W_80a2c.
Proof. vm_refl. Qed.
Lemma D_80a2c : decode_any W_80a2c = Some (Auipc 16 1048479, 4%Z).
Proof. vm_refl. Qed.

Definition W_80a30 : bv 32 := 0x96c80813.
Lemma F_80a30 : fetch_word Ubsan.M.loaded_segments (0x80a30 : word) = Some W_80a30.
Proof. vm_refl. Qed.
Lemma D_80a30 : decode_any W_80a30 = Some (OpImm ALU_ADD 16 16 2412, 4%Z).
Proof. vm_refl. Qed.

Definition W_80a34 : bv 32 := 0x01060633.
Lemma F_80a34 : fetch_word Ubsan.M.loaded_segments (0x80a34 : word) = Some W_80a34.
Proof. vm_refl. Qed.
Lemma D_80a34 : decode_any W_80a34 = Some (Op ALU_ADD 12 12 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_80a38 : bv 32 := 0x00062603.
Lemma F_80a38 : fetch_word Ubsan.M.loaded_segments (0x80a38 : word) = Some W_80a38.
Proof. vm_refl. Qed.
Lemma D_80a38 : decode_any W_80a38 = Some (Load SZ4 true 12 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_80a3c : bv 32 := 0x01060633.
Lemma F_80a3c : fetch_word Ubsan.M.loaded_segments (0x80a3c : word) = Some W_80a3c.
Proof. vm_refl. Qed.
Lemma D_80a3c : decode_any W_80a3c = Some (Op ALU_ADD 12 12 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_80a40 : bv 32 := 0x05813803.
Lemma F_80a40 : fetch_word Ubsan.M.loaded_segments (0x80a40 : word) = Some W_80a40.
Proof. vm_refl. Qed.
Lemma D_80a40 : decode_any W_80a40 = Some (Load SZ8 true 16 2 88, 4%Z).
Proof. vm_refl. Qed.

Definition W_80a44 : bv 32 := 0x00082813.
Lemma F_80a44 : fetch_word Ubsan.M.loaded_segments (0x80a44 : word) = Some W_80a44.
Proof. vm_refl. Qed.
Lemma D_80a44 : decode_any W_80a44 = Some (OpImm ALU_SLT 16 16 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_80a48 : bv 32 := 0x07013c23.
Lemma F_80a48 : fetch_word Ubsan.M.loaded_segments (0x80a48 : word) = Some W_80a48.
Proof. vm_refl. Qed.
Lemma D_80a48 : decode_any W_80a48 = Some (Store SZ8 2 16 120, 4%Z).
Proof. vm_refl. Qed.

Definition W_80a4c : bv 32 := 0x00060067.
Lemma F_80a4c : fetch_word Ubsan.M.loaded_segments (0x80a4c : word) = Some W_80a4c.
Proof. vm_refl. Qed.
Lemma D_80a4c : decode_any W_80a4c = Some (Jalr 0 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_80a50 : bv 32 := 0x18008263.
Lemma F_80a50 : fetch_word Ubsan.M.loaded_segments (0x80a50 : word) = Some W_80a50.
Proof. vm_refl. Qed.
Lemma D_80a50 : decode_any W_80a50 = Some (Branch BC_EQ 1 0 388, 4%Z).
Proof. vm_refl. Qed.

Definition W_80a54 : bv 32 := 0x00000593.
Lemma F_80a54 : fetch_word Ubsan.M.loaded_segments (0x80a54 : word) = Some W_80a54.
Proof. vm_refl. Qed.
Lemma D_80a54 : decode_any W_80a54 = Some (OpImm ALU_ADD 11 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_80a58 : bv 32 := 0xffffc613.
Lemma F_80a58 : fetch_word Ubsan.M.loaded_segments (0x80a58 : word) = Some W_80a58.
Proof. vm_refl. Qed.
Lemma D_80a58 : decode_any W_80a58 = Some (OpImm ALU_XOR 12 31 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_80a5c : bv 32 := 0x00c13023.
Lemma F_80a5c : fetch_word Ubsan.M.loaded_segments (0x80a5c : word) = Some W_80a5c.
Proof. vm_refl. Qed.
Lemma D_80a5c : decode_any W_80a5c = Some (Store SZ8 2 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_80a60 : bv 32 := 0xfffdc293.
Lemma F_80a60 : fetch_word Ubsan.M.loaded_segments (0x80a60 : word) = Some W_80a60.
Proof. vm_refl. Qed.
Lemma D_80a60 : decode_any W_80a60 = Some (OpImm ALU_XOR 5 27 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_80a64 : bv 32 := 0x00271393.
Lemma F_80a64 : fetch_word Ubsan.M.loaded_segments (0x80a64 : word) = Some W_80a64.
Proof. vm_refl. Qed.
Lemma D_80a64 : decode_any W_80a64 = Some (ShiftImm ALU_SLL 7 14 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_80a68 : bv 32 := 0x05813683.
Lemma F_80a68 : fetch_word Ubsan.M.loaded_segments (0x80a68 : word) = Some W_80a68.
Proof. vm_refl. Qed.
Lemma D_80a68 : decode_any W_80a68 = Some (Load SZ8 true 13 2 88, 4%Z).
Proof. vm_refl. Qed.

Definition W_80a6c : bv 32 := 0x00269693.
Lemma F_80a6c : fetch_word Ubsan.M.loaded_segments (0x80a6c : word) = Some W_80a6c.
Proof. vm_refl. Qed.
Lemma D_80a6c : decode_any W_80a6c = Some (ShiftImm ALU_SLL 13 13 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_80a70 : bv 32 := 0x003cfb93.
Lemma F_80a70 : fetch_word Ubsan.M.loaded_segments (0x80a70 : word) = Some W_80a70.
Proof. vm_refl. Qed.
Lemma D_80a70 : decode_any W_80a70 = Some (OpImm ALU_AND 23 25 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_80a74 : bv 32 := 0x0037f613.
Lemma F_80a74 : fetch_word Ubsan.M.loaded_segments (0x80a74 : word) = Some W_80a74.
Proof. vm_refl. Qed.
Lemma D_80a74 : decode_any W_80a74 = Some (OpImm ALU_AND 12 15 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_80a78 : bv 32 := 0x05013483.
Lemma F_80a78 : fetch_word Ubsan.M.loaded_segments (0x80a78 : word) = Some W_80a78.
Proof. vm_refl. Qed.
Lemma D_80a78 : decode_any W_80a78 = Some (Load SZ8 true 9 2 80, 4%Z).
Proof. vm_refl. Qed.

Definition W_80a7c : bv 32 := 0x02813803.
Lemma F_80a7c : fetch_word Ubsan.M.loaded_segments (0x80a7c : word) = Some W_80a7c.
Proof. vm_refl. Qed.
Lemma D_80a7c : decode_any W_80a7c = Some (Load SZ8 true 16 2 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_80a80 : bv 32 := 0x4098083b.
Lemma F_80a80 : fetch_word Ubsan.M.loaded_segments (0x80a80 : word) = Some W_80a80.
Proof. vm_refl. Qed.
Lemma D_80a80 : decode_any W_80a80 = Some (Op32 ALU_SUB 16 16 9, 4%Z).
Proof. vm_refl. Qed.

Definition W_80a84 : bv 32 := 0x03813883.
Lemma F_80a84 : fetch_word Ubsan.M.loaded_segments (0x80a84 : word) = Some W_80a84.
Proof. vm_refl. Qed.
Lemma D_80a84 : decode_any W_80a84 = Some (Load SZ8 true 17 2 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_80a88 : bv 32 := 0x03013e03.
Lemma F_80a88 : fetch_word Ubsan.M.loaded_segments (0x80a88 : word) = Some W_80a88.
Proof. vm_refl. Qed.
Lemma D_80a88 : decode_any W_80a88 = Some (Load SZ8 true 28 2 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_80a8c : bv 32 := 0x011e08b3.
Lemma F_80a8c : fetch_word Ubsan.M.loaded_segments (0x80a8c : word) = Some W_80a8c.
Proof. vm_refl. Qed.
Lemma D_80a8c : decode_any W_80a8c = Some (Op ALU_ADD 17 28 17, 4%Z).
Proof. vm_refl. Qed.

Definition W_80a90 : bv 32 := 0x04813a03.
Lemma F_80a90 : fetch_word Ubsan.M.loaded_segments (0x80a90 : word) = Some W_80a90.
Proof. vm_refl. Qed.
Lemma D_80a90 : decode_any W_80a90 = Some (Load SZ8 true 20 2 72, 4%Z).
Proof. vm_refl. Qed.

Definition W_80a94 : bv 32 := 0x43fa5e13.
Lemma F_80a94 : fetch_word Ubsan.M.loaded_segments (0x80a94 : word) = Some W_80a94.
Proof. vm_refl. Qed.
Lemma D_80a94 : decode_any W_80a94 = Some (ShiftImm ALU_SRA 28 20 63, 4%Z).
Proof. vm_refl. Qed.

Definition W_80a98 : bv 32 := 0x01013983.
Lemma F_80a98 : fetch_word Ubsan.M.loaded_segments (0x80a98 : word) = Some W_80a98.
Proof. vm_refl. Qed.
Lemma D_80a98 : decode_any W_80a98 = Some (Load SZ8 true 19 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_80a9c : bv 32 := 0x0019f993.
Lemma F_80a9c : fetch_word Ubsan.M.loaded_segments (0x80a9c : word) = Some W_80a9c.
Proof. vm_refl. Qed.
Lemma D_80a9c : decode_any W_80a9c = Some (OpImm ALU_AND 19 19 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_80aa0 : bv 32 := 0x001d7c13.
Lemma F_80aa0 : fetch_word Ubsan.M.loaded_segments (0x80aa0 : word) = Some W_80aa0.
Proof. vm_refl. Qed.
Lemma D_80aa0 : decode_any W_80aa0 = Some (OpImm ALU_AND 24 26 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_80aa4 : bv 32 := 0x01f00093.
Lemma F_80aa4 : fetch_word Ubsan.M.loaded_segments (0x80aa4 : word) = Some W_80aa4.
Proof. vm_refl. Qed.
Lemma D_80aa4 : decode_any W_80aa4 = Some (OpImm ALU_ADD 1 0 31, 4%Z).
Proof. vm_refl. Qed.

Definition W_80aa8 : bv 32 := 0x014e7e33.
Lemma F_80aa8 : fetch_word Ubsan.M.loaded_segments (0x80aa8 : word) = Some W_80aa8.
Proof. vm_refl. Qed.
Lemma D_80aa8 : decode_any W_80aa8 = Some (Op ALU_AND 28 28 20, 4%Z).
Proof. vm_refl. Qed.

Definition W_80aac : bv 32 := 0x409888bb.
Lemma F_80aac : fetch_word Ubsan.M.loaded_segments (0x80aac : word) = Some W_80aac.
Proof. vm_refl. Qed.
Lemma D_80aac : decode_any W_80aac = Some (Op32 ALU_SUB 17 17 9, 4%Z).
Proof. vm_refl. Qed.

Definition W_80ab0 : bv 32 := 0x00d78a33.
Lemma F_80ab0 : fetch_word Ubsan.M.loaded_segments (0x80ab0 : word) = Some W_80ab0.
Proof. vm_refl. Qed.
Lemma D_80ab0 : decode_any W_80ab0 = Some (Op ALU_ADD 20 15 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_80ab4 : bv 32 := 0x00163b13.
Lemma F_80ab4 : fetch_word Ubsan.M.loaded_segments (0x80ab4 : word) = Some W_80ab4.
Proof. vm_refl. Qed.
Lemma D_80ab4 : decode_any W_80ab4 = Some (OpImm ALU_SLTU 22 12 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_80ab8 : bv 32 := 0x04013603.
Lemma F_80ab8 : fetch_word Ubsan.M.loaded_segments (0x80ab8 : word) = Some W_80ab8.
Proof. vm_refl. Qed.
Lemma D_80ab8 : decode_any W_80ab8 = Some (Load SZ8 true 12 2 64, 4%Z).
Proof. vm_refl. Qed.

Definition W_80abc : bv 32 := 0x40c8863b.
Lemma F_80abc : fetch_word Ubsan.M.loaded_segments (0x80abc : word) = Some W_80abc.
Proof. vm_refl. Qed.
Lemma D_80abc : decode_any W_80abc = Some (Op32 ALU_SUB 12 17 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_80ac0 : bv 32 := 0x01c6063b.
Lemma F_80ac0 : fetch_word Ubsan.M.loaded_segments (0x80ac0 : word) = Some W_80ac0.
Proof. vm_refl. Qed.
Lemma D_80ac0 : decode_any W_80ac0 = Some (Op32 ALU_ADD 12 12 28, 4%Z).
Proof. vm_refl. Qed.

Definition W_80ac4 : bv 32 := 0x43f65893.
Lemma F_80ac4 : fetch_word Ubsan.M.loaded_segments (0x80ac4 : word) = Some W_80ac4.
Proof. vm_refl. Qed.
Lemma D_80ac4 : decode_any W_80ac4 = Some (ShiftImm ALU_SRA 17 12 63, 4%Z).
Proof. vm_refl. Qed.

Definition W_80ac8 : bv 32 := 0x00c8f633.
Lemma F_80ac8 : fetch_word Ubsan.M.loaded_segments (0x80ac8 : word) = Some W_80ac8.
Proof. vm_refl. Qed.
Lemma D_80ac8 : decode_any W_80ac8 = Some (Op ALU_AND 12 17 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_80acc : bv 32 := 0x40c80e3b.
Lemma F_80acc : fetch_word Ubsan.M.loaded_segments (0x80acc : word) = Some W_80acc.
Proof. vm_refl. Qed.
Lemma D_80acc : decode_any W_80acc = Some (Op32 ALU_SUB 28 16 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_80ad0 : bv 32 := 0x00072493.
Lemma F_80ad0 : fetch_word Ubsan.M.loaded_segments (0x80ad0 : word) = Some W_80ad0.
Proof. vm_refl. Qed.
Lemma D_80ad0 : decode_any W_80ad0 = Some (OpImm ALU_SLT 9 14 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_80ad4 : bv 32 := 0x000c8813.
Lemma F_80ad4 : fetch_word Ubsan.M.loaded_segments (0x80ad4 : word) = Some W_80ad4.
Proof. vm_refl. Qed.
Lemma D_80ad4 : decode_any W_80ad4 = Some (OpImm ALU_ADD 16 25 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_80ad8 : bv 32 := 0x00b78d33.
Lemma F_80ad8 : fetch_word Ubsan.M.loaded_segments (0x80ad8 : word) = Some W_80ad8.
Proof. vm_refl. Qed.
Lemma D_80ad8 : decode_any W_80ad8 = Some (Op ALU_ADD 26 15 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_80adc : bv 32 := 0x01a03633.
Lemma F_80adc : fetch_word Ubsan.M.loaded_segments (0x80adc : word) = Some W_80adc.
Proof. vm_refl. Qed.
Lemma D_80adc : decode_any W_80adc = Some (Op ALU_SLTU 12 0 26, 4%Z).
Proof. vm_refl. Qed.

Definition W_80ae0 : bv 32 := 0x00cb7633.
Lemma F_80ae0 : fetch_word Ubsan.M.loaded_segments (0x80ae0 : word) = Some W_80ae0.
Proof. vm_refl. Qed.
Lemma D_80ae0 : decode_any W_80ae0 = Some (Op ALU_AND 12 22 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_80ae4 : bv 32 := 0x04098a63.
Lemma F_80ae4 : fetch_word Ubsan.M.loaded_segments (0x80ae4 : word) = Some W_80ae4.
Proof. vm_refl. Qed.
Lemma D_80ae4 : decode_any W_80ae4 = Some (Branch BC_EQ 19 0 84, 4%Z).
Proof. vm_refl. Qed.

Definition W_80ae8 : bv 32 := 0x00061463.
Lemma F_80ae8 : fetch_word Ubsan.M.loaded_segments (0x80ae8 : word) = Some W_80ae8.
Proof. vm_refl. Qed.
Lemma D_80ae8 : decode_any W_80ae8 = Some (Branch BC_NE 12 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_80aec : bv 32 := 0x2090106f.
Lemma F_80aec : fetch_word Ubsan.M.loaded_segments (0x80aec : word) = Some W_80aec.
Proof. vm_refl. Qed.
Lemma D_80aec : decode_any W_80aec = Some (Jal 0 6664, 4%Z).
Proof. vm_refl. Qed.

Definition W_80af0 : bv 32 := 0x02000613.
Lemma F_80af0 : fetch_word Ubsan.M.loaded_segments (0x80af0 : word) = Some W_80af0.
Proof. vm_refl. Qed.
Lemma D_80af0 : decode_any W_80af0 = Some (OpImm ALU_ADD 12 0 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_80af4 : bv 32 := 0x00cf1463.
Lemma F_80af4 : fetch_word Ubsan.M.loaded_segments (0x80af4 : word) = Some W_80af4.
Proof. vm_refl. Qed.
Lemma D_80af4 : decode_any W_80af4 = Some (Branch BC_NE 30 12 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_80af8 : bv 32 := 0x1fd0106f.
Lemma F_80af8 : fetch_word Ubsan.M.loaded_segments (0x80af8 : word) = Some W_80af8.
Proof. vm_refl. Qed.
Lemma D_80af8 : decode_any W_80af8 = Some (Jal 0 6652, 4%Z).
Proof. vm_refl. Qed.

Definition W_80afc : bv 32 := 0x000d2603.
Lemma F_80afc : fetch_word Ubsan.M.loaded_segments (0x80afc : word) = Some W_80afc.
Proof. vm_refl. Qed.
Lemma D_80afc : decode_any W_80afc = Some (Load SZ4 true 12 26 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_80b00 : bv 32 := 0x01d61abb.
Lemma F_80b00 : fetch_word Ubsan.M.loaded_segments (0x80b00 : word) = Some W_80b00.
Proof. vm_refl. Qed.
Lemma D_80b00 : decode_any W_80b00 = Some (Op32 ALU_SLL 21 12 29, 4%Z).
Proof. vm_refl. Qed.

Definition W_80b04 : bv 32 := 0x040c1663.
Lemma F_80b04 : fetch_word Ubsan.M.loaded_segments (0x80b04 : word) = Some W_80b04.
Proof. vm_refl. Qed.
Lemma D_80b04 : decode_any W_80b04 = Some (Branch BC_NE 24 0 76, 4%Z).
Proof. vm_refl. Qed.

Definition W_80b08 : bv 32 := 0xffb00613.
Lemma F_80b08 : fetch_word Ubsan.M.loaded_segments (0x80b08 : word) = Some W_80b08.
Proof. vm_refl. Qed.
Lemma D_80b08 : decode_any W_80b08 = Some (OpImm ALU_ADD 12 0 4091, 4%Z).
Proof. vm_refl. Qed.

Definition W_80b0c : bv 32 := 0x01a67463.
Lemma F_80b0c : fetch_word Ubsan.M.loaded_segments (0x80b0c : word) = Some W_80b0c.
Proof. vm_refl. Qed.
Lemma D_80b0c : decode_any W_80b0c = Some (Branch BC_GEU 12 26 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_80b10 : bv 32 := 0x1e50106f.
Lemma F_80b10 : fetch_word Ubsan.M.loaded_segments (0x80b10 : word) = Some W_80b10.
Proof. vm_refl. Qed.
Lemma D_80b10 : decode_any W_80b10 = Some (Jal 0 6628, 4%Z).
Proof. vm_refl. Qed.

Definition W_80b14 : bv 32 := 0x0080f463.
Lemma F_80b14 : fetch_word Ubsan.M.loaded_segments (0x80b14 : word) = Some W_80b14.
Proof. vm_refl. Qed.
Lemma D_80b14 : decode_any W_80b14 = Some (Branch BC_GEU 1 8 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_80b18 : bv 32 := 0x1dd0106f.
Lemma F_80b18 : fetch_word Ubsan.M.loaded_segments (0x80b18 : word) = Some W_80b18.
Proof. vm_refl. Qed.
Lemma D_80b18 : decode_any W_80b18 = Some (Jal 0 6620, 4%Z).
Proof. vm_refl. Qed.

Definition W_80b1c : bv 32 := 0x004d2603.
Lemma F_80b1c : fetch_word Ubsan.M.loaded_segments (0x80b1c : word) = Some W_80b1c.
Proof. vm_refl. Qed.
Lemma D_80b1c : decode_any W_80b1c = Some (Load SZ4 true 12 26 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_80b20 : bv 32 := 0x00013883.
Lemma F_80b20 : fetch_word Ubsan.M.loaded_segments (0x80b20 : word) = Some W_80b20.
Proof. vm_refl. Qed.
Lemma D_80b20 : decode_any W_80b20 = Some (Load SZ8 true 17 2 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_80b24 : bv 32 := 0x011af8b3.
Lemma F_80b24 : fetch_word Ubsan.M.loaded_segments (0x80b24 : word) = Some W_80b24.
Proof. vm_refl. Qed.
Lemma D_80b24 : decode_any W_80b24 = Some (Op ALU_AND 17 21 17, 4%Z).
Proof. vm_refl. Qed.

Definition W_80b28 : bv 32 := 0x0086563b.
Lemma F_80b28 : fetch_word Ubsan.M.loaded_segments (0x80b28 : word) = Some W_80b28.
Proof. vm_refl. Qed.
Lemma D_80b28 : decode_any W_80b28 = Some (Op32 ALU_SRL 12 12 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_80b2c : bv 32 := 0x01f67633.
Lemma F_80b2c : fetch_word Ubsan.M.loaded_segments (0x80b2c : word) = Some W_80b2c.
Proof. vm_refl. Qed.
Lemma D_80b2c : decode_any W_80b2c = Some (Op ALU_AND 12 12 31, 4%Z).
Proof. vm_refl. Qed.

Definition W_80b30 : bv 32 := 0x01166ab3.
Lemma F_80b30 : fetch_word Ubsan.M.loaded_segments (0x80b30 : word) = Some W_80b30.
Proof. vm_refl. Qed.
Lemma D_80b30 : decode_any W_80b30 = Some (Op ALU_OR 21 12 17, 4%Z).
Proof. vm_refl. Qed.

Definition W_80b34 : bv 32 := 0x01c0006f.
Lemma F_80b34 : fetch_word Ubsan.M.loaded_segments (0x80b34 : word) = Some W_80b34.
Proof. vm_refl. Qed.
Lemma D_80b34 : decode_any W_80b34 = Some (Jal 0 28, 4%Z).
Proof. vm_refl. Qed.

Definition W_80b38 : bv 32 := 0x00061463.
Lemma F_80b38 : fetch_word Ubsan.M.loaded_segments (0x80b38 : word) = Some W_80b38.
Proof. vm_refl. Qed.
Lemma D_80b38 : decode_any W_80b38 = Some (Branch BC_NE 12 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_80b3c : bv 32 := 0x1b90106f.
Lemma F_80b3c : fetch_word Ubsan.M.loaded_segments (0x80b3c : word) = Some W_80b3c.
Proof. vm_refl. Qed.
Lemma D_80b3c : decode_any W_80b3c = Some (Jal 0 6584, 4%Z).
Proof. vm_refl. Qed.

Definition W_80b40 : bv 32 := 0x0080f463.
Lemma F_80b40 : fetch_word Ubsan.M.loaded_segments (0x80b40 : word) = Some W_80b40.
Proof. vm_refl. Qed.
Lemma D_80b40 : decode_any W_80b40 = Some (Branch BC_GEU 1 8 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_80b44 : bv 32 := 0x1b10106f.
Lemma F_80b44 : fetch_word Ubsan.M.loaded_segments (0x80b44 : word) = Some W_80b44.
Proof. vm_refl. Qed.
Lemma D_80b44 : decode_any W_80b44 = Some (Jal 0 6576, 4%Z).
Proof. vm_refl. Qed.

Definition W_80b48 : bv 32 := 0x000d2603.
Lemma F_80b48 : fetch_word Ubsan.M.loaded_segments (0x80b48 : word) = Some W_80b48.
Proof. vm_refl. Qed.
Lemma D_80b48 : decode_any W_80b48 = Some (Load SZ4 true 12 26 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_80b4c : bv 32 := 0x00865abb.
Lemma F_80b4c : fetch_word Ubsan.M.loaded_segments (0x80b4c : word) = Some W_80b4c.
Proof. vm_refl. Qed.
Lemma D_80b4c : decode_any W_80b4c = Some (Op32 ALU_SRL 21 12 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_80b50 : bv 32 := 0x000b8463.
Lemma F_80b50 : fetch_word Ubsan.M.loaded_segments (0x80b50 : word) = Some W_80b50.
Proof. vm_refl. Qed.
Lemma D_80b50 : decode_any W_80b50 = Some (Branch BC_EQ 23 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_80b54 : bv 32 := 0x1a10106f.
Lemma F_80b54 : fetch_word Ubsan.M.loaded_segments (0x80b54 : word) = Some W_80b54.
Proof. vm_refl. Qed.
Lemma D_80b54 : decode_any W_80b54 = Some (Jal 0 6560, 4%Z).
Proof. vm_refl. Qed.

Definition W_80b58 : bv 32 := 0x000c9463.
Lemma F_80b58 : fetch_word Ubsan.M.loaded_segments (0x80b58 : word) = Some W_80b58.
Proof. vm_refl. Qed.
Lemma D_80b58 : decode_any W_80b58 = Some (Branch BC_NE 25 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_80b5c : bv 32 := 0x1990106f.
Lemma F_80b5c : fetch_word Ubsan.M.loaded_segments (0x80b5c : word) = Some W_80b5c.
Proof. vm_refl. Qed.
Lemma D_80b5c : decode_any W_80b5c = Some (Jal 0 6552, 4%Z).
Proof. vm_refl. Qed.

Definition W_80b60 : bv 32 := 0x000ca603.
Lemma F_80b60 : fetch_word Ubsan.M.loaded_segments (0x80b60 : word) = Some W_80b60.
Proof. vm_refl. Qed.
Lemma D_80b60 : decode_any W_80b60 = Some (Load SZ4 true 12 25 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_80b64 : bv 32 := 0x005678b3.
Lemma F_80b64 : fetch_word Ubsan.M.loaded_segments (0x80b64 : word) = Some W_80b64.
Proof. vm_refl. Qed.
Lemma D_80b64 : decode_any W_80b64 = Some (Op ALU_AND 17 12 5, 4%Z).
Proof. vm_refl. Qed.

Definition W_80b68 : bv 32 := 0x01566633.
Lemma F_80b68 : fetch_word Ubsan.M.loaded_segments (0x80b68 : word) = Some W_80b68.
Proof. vm_refl. Qed.
Lemma D_80b68 : decode_any W_80b68 = Some (Op ALU_OR 12 12 21, 4%Z).
Proof. vm_refl. Qed.

Definition W_80b6c : bv 32 := 0xfff64613.
Lemma F_80b6c : fetch_word Ubsan.M.loaded_segments (0x80b6c : word) = Some W_80b6c.
Proof. vm_refl. Qed.
Lemma D_80b6c : decode_any W_80b6c = Some (OpImm ALU_XOR 12 12 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_80b70 : bv 32 := 0x00cdf633.
Lemma F_80b70 : fetch_word Ubsan.M.loaded_segments (0x80b70 : word) = Some W_80b70.
Proof. vm_refl. Qed.
Lemma D_80b70 : decode_any W_80b70 = Some (Op ALU_AND 12 27 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_80b74 : bv 32 := 0x01166633.
Lemma F_80b74 : fetch_word Ubsan.M.loaded_segments (0x80b74 : word) = Some W_80b74.
Proof. vm_refl. Qed.
Lemma D_80b74 : decode_any W_80b74 = Some (Op ALU_OR 12 12 17, 4%Z).
Proof. vm_refl. Qed.

Definition W_80b78 : bv 32 := 0x01038ab3.
Lemma F_80b78 : fetch_word Ubsan.M.loaded_segments (0x80b78 : word) = Some W_80b78.
Proof. vm_refl. Qed.
Lemma D_80b78 : decode_any W_80b78 = Some (Op ALU_ADD 21 7 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_80b7c : bv 32 := 0x00cca023.
Lemma F_80b7c : fetch_word Ubsan.M.loaded_segments (0x80b7c : word) = Some W_80b7c.
Proof. vm_refl. Qed.
Lemma D_80b7c : decode_any W_80b7c = Some (Store SZ4 25 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_80b80 : bv 32 := 0x000a9463.
Lemma F_80b80 : fetch_word Ubsan.M.loaded_segments (0x80b80 : word) = Some W_80b80.
Proof. vm_refl. Qed.
Lemma D_80b80 : decode_any W_80b80 = Some (Branch BC_NE 21 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_80b84 : bv 32 := 0x1710106f.
Lemma F_80b84 : fetch_word Ubsan.M.loaded_segments (0x80b84 : word) = Some W_80b84.
Proof. vm_refl. Qed.
Lemma D_80b84 : decode_any W_80b84 = Some (Jal 0 6512, 4%Z).
Proof. vm_refl. Qed.

Definition W_80b88 : bv 32 := 0x010ab633.
Lemma F_80b88 : fetch_word Ubsan.M.loaded_segments (0x80b88 : word) = Some W_80b88.
Proof. vm_refl. Qed.
Lemma D_80b88 : decode_any W_80b88 = Some (Op ALU_SLTU 12 21 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_80b8c : bv 32 := 0x00964633.
Lemma F_80b8c : fetch_word Ubsan.M.loaded_segments (0x80b8c : word) = Some W_80b8c.
Proof. vm_refl. Qed.
Lemma D_80b8c : decode_any W_80b8c = Some (Op ALU_XOR 12 12 9, 4%Z).
Proof. vm_refl. Qed.

Definition W_80b90 : bv 32 := 0x00164613.
Lemma F_80b90 : fetch_word Ubsan.M.loaded_segments (0x80b90 : word) = Some W_80b90.
Proof. vm_refl. Qed.
Lemma D_80b90 : decode_any W_80b90 = Some (OpImm ALU_XOR 12 12 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_80b94 : bv 32 := 0x00061463.
Lemma F_80b94 : fetch_word Ubsan.M.loaded_segments (0x80b94 : word) = Some W_80b94.
Proof. vm_refl. Qed.
Lemma D_80b94 : decode_any W_80b94 = Some (Branch BC_NE 12 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_80b98 : bv 32 := 0x15d0106f.
Lemma F_80b98 : fetch_word Ubsan.M.loaded_segments (0x80b98 : word) = Some W_80b98.
Proof. vm_refl. Qed.
Lemma D_80b98 : decode_any W_80b98 = Some (Jal 0 6492, 4%Z).
Proof. vm_refl. Qed.

Definition W_80b9c : bv 32 := 0x00ba0633.
Lemma F_80b9c : fetch_word Ubsan.M.loaded_segments (0x80b9c : word) = Some W_80b9c.
Proof. vm_refl. Qed.
Lemma D_80b9c : decode_any W_80b9c = Some (Op ALU_ADD 12 20 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_80ba0 : bv 32 := 0x00061463.
Lemma F_80ba0 : fetch_word Ubsan.M.loaded_segments (0x80ba0 : word) = Some W_80ba0.
Proof. vm_refl. Qed.
Lemma D_80ba0 : decode_any W_80ba0 = Some (Branch BC_NE 12 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_80ba4 : bv 32 := 0x1510106f.
Lemma F_80ba4 : fetch_word Ubsan.M.loaded_segments (0x80ba4 : word) = Some W_80ba4.
Proof. vm_refl. Qed.
Lemma D_80ba4 : decode_any W_80ba4 = Some (Jal 0 6480, 4%Z).
Proof. vm_refl. Qed.

Definition W_80ba8 : bv 32 := 0x01a63633.
Lemma F_80ba8 : fetch_word Ubsan.M.loaded_segments (0x80ba8 : word) = Some W_80ba8.
Proof. vm_refl. Qed.
Lemma D_80ba8 : decode_any W_80ba8 = Some (Op ALU_SLTU 12 12 26, 4%Z).
Proof. vm_refl. Qed.

Definition W_80bac : bv 32 := 0x07813803.
Lemma F_80bac : fetch_word Ubsan.M.loaded_segments (0x80bac : word) = Some W_80bac.
Proof. vm_refl. Qed.
Lemma D_80bac : decode_any W_80bac = Some (Load SZ8 true 16 2 120, 4%Z).
Proof. vm_refl. Qed.

Definition W_80bb0 : bv 32 := 0x01064633.
Lemma F_80bb0 : fetch_word Ubsan.M.loaded_segments (0x80bb0 : word) = Some W_80bb0.
Proof. vm_refl. Qed.
Lemma D_80bb0 : decode_any W_80bb0 = Some (Op ALU_XOR 12 12 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_80bb4 : bv 32 := 0x00164613.
Lemma F_80bb4 : fetch_word Ubsan.M.loaded_segments (0x80bb4 : word) = Some W_80bb4.
Proof. vm_refl. Qed.
Lemma D_80bb4 : decode_any W_80bb4 = Some (OpImm ALU_XOR 12 12 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_80bb8 : bv 32 := 0x00061463.
Lemma F_80bb8 : fetch_word Ubsan.M.loaded_segments (0x80bb8 : word) = Some W_80bb8.
Proof. vm_refl. Qed.
Lemma D_80bb8 : decode_any W_80bb8 = Some (Branch BC_NE 12 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_80bbc : bv 32 := 0x1390106f.
Lemma F_80bbc : fetch_word Ubsan.M.loaded_segments (0x80bbc : word) = Some W_80bbc.
Proof. vm_refl. Qed.
Lemma D_80bbc : decode_any W_80bbc = Some (Jal 0 6456, 4%Z).
Proof. vm_refl. Qed.

Definition W_80bc0 : bv 32 := 0x001e0e1b.
Lemma F_80bc0 : fetch_word Ubsan.M.loaded_segments (0x80bc0 : word) = Some W_80bc0.
Proof. vm_refl. Qed.
Lemma D_80bc0 : decode_any W_80bc0 = Some (OpImm32 28 28 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_80bc4 : bv 32 := 0x00d585b3.
Lemma F_80bc4 : fetch_word Ubsan.M.loaded_segments (0x80bc4 : word) = Some W_80bc4.
Proof. vm_refl. Qed.
Lemma D_80bc4 : decode_any W_80bc4 = Some (Op ALU_ADD 11 11 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_80bc8 : bv 32 := 0x007c8cb3.
Lemma F_80bc8 : fetch_word Ubsan.M.loaded_segments (0x80bc8 : word) = Some W_80bc8.
Proof. vm_refl. Qed.
Lemma D_80bc8 : decode_any W_80bc8 = Some (Op ALU_ADD 25 25 7, 4%Z).
Proof. vm_refl. Qed.

Definition W_80bcc : bv 32 := 0x000a8813.
Lemma F_80bcc : fetch_word Ubsan.M.loaded_segments (0x80bcc : word) = Some W_80bcc.
Proof. vm_refl. Qed.
Lemma D_80bcc : decode_any W_80bcc = Some (OpImm ALU_ADD 16 21 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_80bd0 : bv 32 := 0xf00e14e3.
Lemma F_80bd0 : fetch_word Ubsan.M.loaded_segments (0x80bd0 : word) = Some W_80bd0.
Proof. vm_refl. Qed.
Lemma D_80bd0 : decode_any W_80bd0 = Some (Branch BC_NE 28 0 7944, 4%Z).
Proof. vm_refl. Qed.

Definition W_80bd4 : bv 32 := 0x02013583.
Lemma F_80bd4 : fetch_word Ubsan.M.loaded_segments (0x80bd4 : word) = Some W_80bd4.
Proof. vm_refl. Qed.
Lemma D_80bd4 : decode_any W_80bd4 = Some (Load SZ8 true 11 2 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_80bd8 : bv 32 := 0x16059e63.
Lemma F_80bd8 : fetch_word Ubsan.M.loaded_segments (0x80bd8 : word) = Some W_80bd8.
Proof. vm_refl. Qed.
Lemma D_80bd8 : decode_any W_80bd8 = Some (Branch BC_NE 11 0 380, 4%Z).
Proof. vm_refl. Qed.

Definition W_80bdc : bv 32 := 0xffffc693.
Lemma F_80bdc : fetch_word Ubsan.M.loaded_segments (0x80bdc : word) = Some W_80bdc.
Proof. vm_refl. Qed.
Lemma D_80bdc : decode_any W_80bdc = Some (OpImm ALU_XOR 13 31 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_80be0 : bv 32 := 0x00271293.
Lemma F_80be0 : fetch_word Ubsan.M.loaded_segments (0x80be0 : word) = Some W_80be0.
Proof. vm_refl. Qed.
Lemma D_80be0 : decode_any W_80be0 = Some (ShiftImm ALU_SLL 5 14 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_80be4 : bv 32 := 0x05813383.
Lemma F_80be4 : fetch_word Ubsan.M.loaded_segments (0x80be4 : word) = Some W_80be4.
Proof. vm_refl. Qed.
Lemma D_80be4 : decode_any W_80be4 = Some (Load SZ8 true 7 2 88, 4%Z).
Proof. vm_refl. Qed.

Definition W_80be8 : bv 32 := 0x00239393.
Lemma F_80be8 : fetch_word Ubsan.M.loaded_segments (0x80be8 : word) = Some W_80be8.
Proof. vm_refl. Qed.
Lemma D_80be8 : decode_any W_80be8 = Some (ShiftImm ALU_SLL 7 7 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_80bec : bv 32 := 0x00337613.
Lemma F_80bec : fetch_word Ubsan.M.loaded_segments (0x80bec : word) = Some W_80bec.
Proof. vm_refl. Qed.
Lemma D_80bec : decode_any W_80bec = Some (OpImm ALU_AND 12 6 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_80bf0 : bv 32 := 0x00397793.
Lemma F_80bf0 : fetch_word Ubsan.M.loaded_segments (0x80bf0 : word) = Some W_80bf0.
Proof. vm_refl. Qed.
Lemma D_80bf0 : decode_any W_80bf0 = Some (OpImm ALU_AND 15 18 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_80bf4 : bv 32 := 0x07013a03.
Lemma F_80bf4 : fetch_word Ubsan.M.loaded_segments (0x80bf4 : word) = Some W_80bf4.
Proof. vm_refl. Qed.
Lemma D_80bf4 : decode_any W_80bf4 = Some (Load SZ8 true 20 2 112, 4%Z).
Proof. vm_refl. Qed.

Definition W_80bf8 : bv 32 := 0x002a1a13.
Lemma F_80bf8 : fetch_word Ubsan.M.loaded_segments (0x80bf8 : word) = Some W_80bf8.
Proof. vm_refl. Qed.
Lemma D_80bf8 : decode_any W_80bf8 = Some (ShiftImm ALU_SLL 20 20 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_80bfc : bv 32 := 0x00072b93.
Lemma F_80bfc : fetch_word Ubsan.M.loaded_segments (0x80bfc : word) = Some W_80bfc.
Proof. vm_refl. Qed.
Lemma D_80bfc : decode_any W_80bfc = Some (OpImm ALU_SLT 23 14 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_80c00 : bv 32 := 0x02000c93.
Lemma F_80c00 : fetch_word Ubsan.M.loaded_segments (0x80c00 : word) = Some W_80c00.
Proof. vm_refl. Qed.
Lemma D_80c00 : decode_any W_80c00 = Some (OpImm ALU_ADD 25 0 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_80c04 : bv 32 := 0xffb00d13.
Lemma F_80c04 : fetch_word Ubsan.M.loaded_segments (0x80c04 : word) = Some W_80c04.
Proof. vm_refl. Qed.
Lemma D_80c04 : decode_any W_80c04 = Some (OpImm ALU_ADD 26 0 4091, 4%Z).
Proof. vm_refl. Qed.

Definition W_80c08 : bv 32 := 0x0017b793.
Lemma F_80c08 : fetch_word Ubsan.M.loaded_segments (0x80c08 : word) = Some W_80c08.
Proof. vm_refl. Qed.
Lemma D_80c08 : decode_any W_80c08 = Some (OpImm ALU_SLTU 15 15 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_80c0c : bv 32 := 0x02f13023.
Lemma F_80c0c : fetch_word Ubsan.M.loaded_segments (0x80c0c : word) = Some W_80c0c.
Proof. vm_refl. Qed.
Lemma D_80c0c : decode_any W_80c0c = Some (Store SZ8 2 15 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_80c10 : bv 32 := 0x00163613.
Lemma F_80c10 : fetch_word Ubsan.M.loaded_segments (0x80c10 : word) = Some W_80c10.
Proof. vm_refl. Qed.
Lemma D_80c10 : decode_any W_80c10 = Some (OpImm ALU_SLTU 12 12 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_80c14 : bv 32 := 0x00c13823.
Lemma F_80c14 : fetch_word Ubsan.M.loaded_segments (0x80c14 : word) = Some W_80c14.
Proof. vm_refl. Qed.
Lemma D_80c14 : decode_any W_80c14 = Some (Store SZ8 2 12 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_80c18 : bv 32 := 0x01f00993.
Lemma F_80c18 : fetch_word Ubsan.M.loaded_segments (0x80c18 : word) = Some W_80c18.
Proof. vm_refl. Qed.
Lemma D_80c18 : decode_any W_80c18 = Some (OpImm ALU_ADD 19 0 31, 4%Z).
Proof. vm_refl. Qed.

Definition W_80c1c : bv 32 := 0x00030b13.
Lemma F_80c1c : fetch_word Ubsan.M.loaded_segments (0x80c1c : word) = Some W_80c1c.
Proof. vm_refl. Qed.
Lemma D_80c1c : decode_any W_80c1c = Some (OpImm ALU_ADD 22 6 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_80c20 : bv 32 := 0x00090c13.
Lemma F_80c20 : fetch_word Ubsan.M.loaded_segments (0x80c20 : word) = Some W_80c20.
Proof. vm_refl. Qed.
Lemma D_80c20 : decode_any W_80c20 = Some (OpImm ALU_ADD 24 18 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_80c24 : bv 32 := 0x07013603.
Lemma F_80c24 : fetch_word Ubsan.M.loaded_segments (0x80c24 : word) = Some W_80c24.
Proof. vm_refl. Qed.
Lemma D_80c24 : decode_any W_80c24 = Some (Load SZ8 true 12 2 112, 4%Z).
Proof. vm_refl. Qed.

Definition W_80c28 : bv 32 := 0x0a060e63.
Lemma F_80c28 : fetch_word Ubsan.M.loaded_segments (0x80c28 : word) = Some W_80c28.
Proof. vm_refl. Qed.
Lemma D_80c28 : decode_any W_80c28 = Some (Branch BC_EQ 12 0 188, 4%Z).
Proof. vm_refl. Qed.

Definition W_80c2c : bv 32 := 0x00000d93.
Lemma F_80c2c : fetch_word Ubsan.M.loaded_segments (0x80c2c : word) = Some W_80c2c.
Proof. vm_refl. Qed.
Lemma D_80c2c : decode_any W_80c2c = Some (OpImm ALU_ADD 27 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_80c30 : bv 32 := 0x00603833.
Lemma F_80c30 : fetch_word Ubsan.M.loaded_segments (0x80c30 : word) = Some W_80c30.
Proof. vm_refl. Qed.
Lemma D_80c30 : decode_any W_80c30 = Some (Op ALU_SLTU 16 0 6, 4%Z).
Proof. vm_refl. Qed.

Definition W_80c34 : bv 32 := 0x01203e33.
Lemma F_80c34 : fetch_word Ubsan.M.loaded_segments (0x80c34 : word) = Some W_80c34.
Proof. vm_refl. Qed.
Lemma D_80c34 : decode_any W_80c34 = Some (Op ALU_SLTU 28 0 18, 4%Z).
Proof. vm_refl. Qed.

Definition W_80c38 : bv 32 := 0x01013603.
Lemma F_80c38 : fetch_word Ubsan.M.loaded_segments (0x80c38 : word) = Some W_80c38.
Proof. vm_refl. Qed.
Lemma D_80c38 : decode_any W_80c38 = Some (Load SZ8 true 12 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_80c3c : bv 32 := 0x010674b3.
Lemma F_80c3c : fetch_word Ubsan.M.loaded_segments (0x80c3c : word) = Some W_80c3c.
Proof. vm_refl. Qed.
Lemma D_80c3c : decode_any W_80c3c = Some (Op ALU_AND 9 12 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_80c40 : bv 32 := 0x02013603.
Lemma F_80c40 : fetch_word Ubsan.M.loaded_segments (0x80c40 : word) = Some W_80c40.
Proof. vm_refl. Qed.
Lemma D_80c40 : decode_any W_80c40 = Some (Load SZ8 true 12 2 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_80c44 : bv 32 := 0x01c67ab3.
Lemma F_80c44 : fetch_word Ubsan.M.loaded_segments (0x80c44 : word) = Some W_80c44.
Proof. vm_refl. Qed.
Lemma D_80c44 : decode_any W_80c44 = Some (Op ALU_AND 21 12 28, 4%Z).
Proof. vm_refl. Qed.

Definition W_80c48 : bv 32 := 0x01bb0633.
Lemma F_80c48 : fetch_word Ubsan.M.loaded_segments (0x80c48 : word) = Some W_80c48.
Proof. vm_refl. Qed.
Lemma D_80c48 : decode_any W_80c48 = Some (Op ALU_ADD 12 22 27, 4%Z).
Proof. vm_refl. Qed.

Definition W_80c4c : bv 32 := 0x00667463.
Lemma F_80c4c : fetch_word Ubsan.M.loaded_segments (0x80c4c : word) = Some W_80c4c.
Proof. vm_refl. Qed.
Lemma D_80c4c : decode_any W_80c4c = Some (Branch BC_GEU 12 6 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_80c50 : bv 32 := 0x0a50106f.
Lemma F_80c50 : fetch_word Ubsan.M.loaded_segments (0x80c50 : word) = Some W_80c50.
Proof. vm_refl. Qed.
Lemma D_80c50 : decode_any W_80c50 = Some (Jal 0 6308, 4%Z).
Proof. vm_refl. Qed.

Definition W_80c54 : bv 32 := 0x00163613.
Lemma F_80c54 : fetch_word Ubsan.M.loaded_segments (0x80c54 : word) = Some W_80c54.
Proof. vm_refl. Qed.
Lemma D_80c54 : decode_any W_80c54 = Some (OpImm ALU_SLTU 12 12 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_80c58 : bv 32 := 0x00c84633.
Lemma F_80c58 : fetch_word Ubsan.M.loaded_segments (0x80c58 : word) = Some W_80c58.
Proof. vm_refl. Qed.
Lemma D_80c58 : decode_any W_80c58 = Some (Op ALU_XOR 12 16 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_80c5c : bv 32 := 0x00061463.
Lemma F_80c5c : fetch_word Ubsan.M.loaded_segments (0x80c5c : word) = Some W_80c5c.
Proof. vm_refl. Qed.
Lemma D_80c5c : decode_any W_80c5c = Some (Branch BC_NE 12 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_80c60 : bv 32 := 0x0950106f.
Lemma F_80c60 : fetch_word Ubsan.M.loaded_segments (0x80c60 : word) = Some W_80c60.
Proof. vm_refl. Qed.
Lemma D_80c60 : decode_any W_80c60 = Some (Jal 0 6292, 4%Z).
Proof. vm_refl. Qed.

Definition W_80c64 : bv 32 := 0x00049463.
Lemma F_80c64 : fetch_word Ubsan.M.loaded_segments (0x80c64 : word) = Some W_80c64.
Proof. vm_refl. Qed.
Lemma D_80c64 : decode_any W_80c64 = Some (Branch BC_NE 9 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_80c68 : bv 32 := 0x08d0106f.
Lemma F_80c68 : fetch_word Ubsan.M.loaded_segments (0x80c68 : word) = Some W_80c68.
Proof. vm_refl. Qed.
Lemma D_80c68 : decode_any W_80c68 = Some (Jal 0 6284, 4%Z).
Proof. vm_refl. Qed.

Definition W_80c6c : bv 32 := 0x019f1463.
Lemma F_80c6c : fetch_word Ubsan.M.loaded_segments (0x80c6c : word) = Some W_80c6c.
Proof. vm_refl. Qed.
Lemma D_80c6c : decode_any W_80c6c = Some (Branch BC_NE 30 25 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_80c70 : bv 32 := 0x0850106f.
Lemma F_80c70 : fetch_word Ubsan.M.loaded_segments (0x80c70 : word) = Some W_80c70.
Proof. vm_refl. Qed.
Lemma D_80c70 : decode_any W_80c70 = Some (Jal 0 6276, 4%Z).
Proof. vm_refl. Qed.

Definition W_80c74 : bv 32 := 0x01b30633.
Lemma F_80c74 : fetch_word Ubsan.M.loaded_segments (0x80c74 : word) = Some W_80c74.
Proof. vm_refl. Qed.
Lemma D_80c74 : decode_any W_80c74 = Some (Op ALU_ADD 12 6 27, 4%Z).
Proof. vm_refl. Qed.

Definition W_80c78 : bv 32 := 0x00cd7463.
Lemma F_80c78 : fetch_word Ubsan.M.loaded_segments (0x80c78 : word) = Some W_80c78.
Proof. vm_refl. Qed.
Lemma D_80c78 : decode_any W_80c78 = Some (Branch BC_GEU 26 12 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_80c7c : bv 32 := 0x0790106f.
Lemma F_80c7c : fetch_word Ubsan.M.loaded_segments (0x80c7c : word) = Some W_80c7c.
Proof. vm_refl. Qed.
Lemma D_80c7c : decode_any W_80c7c = Some (Jal 0 6264, 4%Z).
Proof. vm_refl. Qed.

Definition W_80c80 : bv 32 := 0x0089f463.
Lemma F_80c80 : fetch_word Ubsan.M.loaded_segments (0x80c80 : word) = Some W_80c80.
Proof. vm_refl. Qed.
Lemma D_80c80 : decode_any W_80c80 = Some (Branch BC_GEU 19 8 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_80c84 : bv 32 := 0x0710106f.
Lemma F_80c84 : fetch_word Ubsan.M.loaded_segments (0x80c84 : word) = Some W_80c84.
Proof. vm_refl. Qed.
Lemma D_80c84 : decode_any W_80c84 = Some (Jal 0 6256, 4%Z).
Proof. vm_refl. Qed.

Definition W_80c88 : bv 32 := 0x01bc07b3.
Lemma F_80c88 : fetch_word Ubsan.M.loaded_segments (0x80c88 : word) = Some W_80c88.
Proof. vm_refl. Qed.
Lemma D_80c88 : decode_any W_80c88 = Some (Op ALU_ADD 15 24 27, 4%Z).
Proof. vm_refl. Qed.

Definition W_80c8c : bv 32 := 0x0127f463.
Lemma F_80c8c : fetch_word Ubsan.M.loaded_segments (0x80c8c : word) = Some W_80c8c.
Proof. vm_refl. Qed.
Lemma D_80c8c : decode_any W_80c8c = Some (Branch BC_GEU 15 18 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_80c90 : bv 32 := 0x0650106f.
Lemma F_80c90 : fetch_word Ubsan.M.loaded_segments (0x80c90 : word) = Some W_80c90.
Proof. vm_refl. Qed.
Lemma D_80c90 : decode_any W_80c90 = Some (Jal 0 6244, 4%Z).
Proof. vm_refl. Qed.

Definition W_80c94 : bv 32 := 0x0017b793.
Lemma F_80c94 : fetch_word Ubsan.M.loaded_segments (0x80c94 : word) = Some W_80c94.
Proof. vm_refl. Qed.
Lemma D_80c94 : decode_any W_80c94 = Some (OpImm ALU_SLTU 15 15 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_80c98 : bv 32 := 0x00fe47b3.
Lemma F_80c98 : fetch_word Ubsan.M.loaded_segments (0x80c98 : word) = Some W_80c98.
Proof. vm_refl. Qed.
Lemma D_80c98 : decode_any W_80c98 = Some (Op ALU_XOR 15 28 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_80c9c : bv 32 := 0x00079463.
Lemma F_80c9c : fetch_word Ubsan.M.loaded_segments (0x80c9c : word) = Some W_80c9c.
Proof. vm_refl. Qed.
Lemma D_80c9c : decode_any W_80c9c = Some (Branch BC_NE 15 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_80ca0 : bv 32 := 0x0550106f.
Lemma F_80ca0 : fetch_word Ubsan.M.loaded_segments (0x80ca0 : word) = Some W_80ca0.
Proof. vm_refl. Qed.
Lemma D_80ca0 : decode_any W_80ca0 = Some (Jal 0 6228, 4%Z).
Proof. vm_refl. Qed.

Definition W_80ca4 : bv 32 := 0x000a9463.
Lemma F_80ca4 : fetch_word Ubsan.M.loaded_segments (0x80ca4 : word) = Some W_80ca4.
Proof. vm_refl. Qed.
Lemma D_80ca4 : decode_any W_80ca4 = Some (Branch BC_NE 21 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_80ca8 : bv 32 := 0x04d0106f.
Lemma F_80ca8 : fetch_word Ubsan.M.loaded_segments (0x80ca8 : word) = Some W_80ca8.
Proof. vm_refl. Qed.
Lemma D_80ca8 : decode_any W_80ca8 = Some (Jal 0 6220, 4%Z).
Proof. vm_refl. Qed.

Definition W_80cac : bv 32 := 0x00062783.
Lemma F_80cac : fetch_word Ubsan.M.loaded_segments (0x80cac : word) = Some W_80cac.
Proof. vm_refl. Qed.
Lemma D_80cac : decode_any W_80cac = Some (Load SZ4 true 15 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_80cb0 : bv 32 := 0x00462603.
Lemma F_80cb0 : fetch_word Ubsan.M.loaded_segments (0x80cb0 : word) = Some W_80cb0.
Proof. vm_refl. Qed.
Lemma D_80cb0 : decode_any W_80cb0 = Some (Load SZ4 true 12 12 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_80cb4 : bv 32 := 0x01b908b3.
Lemma F_80cb4 : fetch_word Ubsan.M.loaded_segments (0x80cb4 : word) = Some W_80cb4.
Proof. vm_refl. Qed.
Lemma D_80cb4 : decode_any W_80cb4 = Some (Op ALU_ADD 17 18 27, 4%Z).
Proof. vm_refl. Qed.

Definition W_80cb8 : bv 32 := 0x0008a083.
Lemma F_80cb8 : fetch_word Ubsan.M.loaded_segments (0x80cb8 : word) = Some W_80cb8.
Proof. vm_refl. Qed.
Lemma D_80cb8 : decode_any W_80cb8 = Some (Load SZ4 true 1 17 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_80cbc : bv 32 := 0x01d797bb.
Lemma F_80cbc : fetch_word Ubsan.M.loaded_segments (0x80cbc : word) = Some W_80cbc.
Proof. vm_refl. Qed.
Lemma D_80cbc : decode_any W_80cbc = Some (Op32 ALU_SLL 15 15 29, 4%Z).
Proof. vm_refl. Qed.

Definition W_80cc0 : bv 32 := 0x0086563b.
Lemma F_80cc0 : fetch_word Ubsan.M.loaded_segments (0x80cc0 : word) = Some W_80cc0.
Proof. vm_refl. Qed.
Lemma D_80cc0 : decode_any W_80cc0 = Some (Op32 ALU_SRL 12 12 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_80cc4 : bv 32 := 0x00d7f7b3.
Lemma F_80cc4 : fetch_word Ubsan.M.loaded_segments (0x80cc4 : word) = Some W_80cc4.
Proof. vm_refl. Qed.
Lemma D_80cc4 : decode_any W_80cc4 = Some (Op ALU_AND 15 15 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_80cc8 : bv 32 := 0x01f67633.
Lemma F_80cc8 : fetch_word Ubsan.M.loaded_segments (0x80cc8 : word) = Some W_80cc8.
Proof. vm_refl. Qed.
Lemma D_80cc8 : decode_any W_80cc8 = Some (Op ALU_AND 12 12 31, 4%Z).
Proof. vm_refl. Qed.

Definition W_80ccc : bv 32 := 0x00f66633.
Lemma F_80ccc : fetch_word Ubsan.M.loaded_segments (0x80ccc : word) = Some W_80ccc.
Proof. vm_refl. Qed.
Lemma D_80ccc : decode_any W_80ccc = Some (Op ALU_OR 12 12 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_80cd0 : bv 32 := 0x00166633.
Lemma F_80cd0 : fetch_word Ubsan.M.loaded_segments (0x80cd0 : word) = Some W_80cd0.
Proof. vm_refl. Qed.
Lemma D_80cd0 : decode_any W_80cd0 = Some (Op ALU_OR 12 12 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_80cd4 : bv 32 := 0xfff64613.
Lemma F_80cd4 : fetch_word Ubsan.M.loaded_segments (0x80cd4 : word) = Some W_80cd4.
Proof. vm_refl. Qed.
Lemma D_80cd4 : decode_any W_80cd4 = Some (OpImm ALU_XOR 12 12 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_80cd8 : bv 32 := 0x004d8d93.
Lemma F_80cd8 : fetch_word Ubsan.M.loaded_segments (0x80cd8 : word) = Some W_80cd8.
Proof. vm_refl. Qed.
Lemma D_80cd8 : decode_any W_80cd8 = Some (OpImm ALU_ADD 27 27 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_80cdc : bv 32 := 0x00c8a023.
Lemma F_80cdc : fetch_word Ubsan.M.loaded_segments (0x80cdc : word) = Some W_80cdc.
Proof. vm_refl. Qed.
Lemma D_80cdc : decode_any W_80cdc = Some (Store SZ4 17 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_80ce0 : bv 32 := 0xf7ba14e3.
Lemma F_80ce0 : fetch_word Ubsan.M.loaded_segments (0x80ce0 : word) = Some W_80ce0.
Proof. vm_refl. Qed.
Lemma D_80ce0 : decode_any W_80ce0 = Some (Branch BC_NE 20 27 8040, 4%Z).
Proof. vm_refl. Qed.

Definition W_80ce4 : bv 32 := 0x00590633.
Lemma F_80ce4 : fetch_word Ubsan.M.loaded_segments (0x80ce4 : word) = Some W_80ce4.
Proof. vm_refl. Qed.
Lemma D_80ce4 : decode_any W_80ce4 = Some (Op ALU_ADD 12 18 5, 4%Z).
Proof. vm_refl. Qed.

Definition W_80ce8 : bv 32 := 0x012037b3.
Lemma F_80ce8 : fetch_word Ubsan.M.loaded_segments (0x80ce8 : word) = Some W_80ce8.
Proof. vm_refl. Qed.
Lemma D_80ce8 : decode_any W_80ce8 = Some (Op ALU_SLTU 15 0 18, 4%Z).
Proof. vm_refl. Qed.

Definition W_80cec : bv 32 := 0x00163813.
Lemma F_80cec : fetch_word Ubsan.M.loaded_segments (0x80cec : word) = Some W_80cec.
Proof. vm_refl. Qed.
Lemma D_80cec : decode_any W_80cec = Some (OpImm ALU_SLTU 16 12 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_80cf0 : bv 32 := 0x01079463.
Lemma F_80cf0 : fetch_word Ubsan.M.loaded_segments (0x80cf0 : word) = Some W_80cf0.
Proof. vm_refl. Qed.
Lemma D_80cf0 : decode_any W_80cf0 = Some (Branch BC_NE 15 16 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_80cf4 : bv 32 := 0x0010106f.
Lemma F_80cf4 : fetch_word Ubsan.M.loaded_segments (0x80cf4 : word) = Some W_80cf4.
Proof. vm_refl. Qed.
Lemma D_80cf4 : decode_any W_80cf4 = Some (Jal 0 6144, 4%Z).
Proof. vm_refl. Qed.

Definition W_80cf8 : bv 32 := 0x01263633.
Lemma F_80cf8 : fetch_word Ubsan.M.loaded_segments (0x80cf8 : word) = Some W_80cf8.
Proof. vm_refl. Qed.
Lemma D_80cf8 : decode_any W_80cf8 = Some (Op ALU_SLTU 12 12 18, 4%Z).
Proof. vm_refl. Qed.

Definition W_80cfc : bv 32 := 0x01764633.
Lemma F_80cfc : fetch_word Ubsan.M.loaded_segments (0x80cfc : word) = Some W_80cfc.
Proof. vm_refl. Qed.
Lemma D_80cfc : decode_any W_80cfc = Some (Op ALU_XOR 12 12 23, 4%Z).
Proof. vm_refl. Qed.

Definition W_80d00 : bv 32 := 0x00164613.
Lemma F_80d00 : fetch_word Ubsan.M.loaded_segments (0x80d00 : word) = Some W_80d00.
Proof. vm_refl. Qed.
Lemma D_80d00 : decode_any W_80d00 = Some (OpImm ALU_XOR 12 12 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_80d04 : bv 32 := 0x00061463.
Lemma F_80d04 : fetch_word Ubsan.M.loaded_segments (0x80d04 : word) = Some W_80d04.
Proof. vm_refl. Qed.
Lemma D_80d04 : decode_any W_80d04 = Some (Branch BC_NE 12 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_80d08 : bv 32 := 0x7ec0106f.
Lemma F_80d08 : fetch_word Ubsan.M.loaded_segments (0x80d08 : word) = Some W_80d08.
Proof. vm_refl. Qed.
Lemma D_80d08 : decode_any W_80d08 = Some (Jal 0 6124, 4%Z).
Proof. vm_refl. Qed.

Definition W_80d0c : bv 32 := 0x00638633.
Lemma F_80d0c : fetch_word Ubsan.M.loaded_segments (0x80d0c : word) = Some W_80d0c.
Proof. vm_refl. Qed.
Lemma D_80d0c : decode_any W_80d0c = Some (Op ALU_ADD 12 7 6, 4%Z).
Proof. vm_refl. Qed.

Definition W_80d10 : bv 32 := 0x006037b3.
Lemma F_80d10 : fetch_word Ubsan.M.loaded_segments (0x80d10 : word) = Some W_80d10.
Proof. vm_refl. Qed.
Lemma D_80d10 : decode_any W_80d10 = Some (Op ALU_SLTU 15 0 6, 4%Z).
Proof. vm_refl. Qed.

Definition W_80d14 : bv 32 := 0x00163813.
Lemma F_80d14 : fetch_word Ubsan.M.loaded_segments (0x80d14 : word) = Some W_80d14.
Proof. vm_refl. Qed.
Lemma D_80d14 : decode_any W_80d14 = Some (OpImm ALU_SLTU 16 12 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_80d18 : bv 32 := 0x01079463.
Lemma F_80d18 : fetch_word Ubsan.M.loaded_segments (0x80d18 : word) = Some W_80d18.
Proof. vm_refl. Qed.
Lemma D_80d18 : decode_any W_80d18 = Some (Branch BC_NE 15 16 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_80d1c : bv 32 := 0x7d80106f.
Lemma F_80d1c : fetch_word Ubsan.M.loaded_segments (0x80d1c : word) = Some W_80d1c.
Proof. vm_refl. Qed.
Lemma D_80d1c : decode_any W_80d1c = Some (Jal 0 6104, 4%Z).
Proof. vm_refl. Qed.

Definition W_80d20 : bv 32 := 0x006637b3.
Lemma F_80d20 : fetch_word Ubsan.M.loaded_segments (0x80d20 : word) = Some W_80d20.
Proof. vm_refl. Qed.
Lemma D_80d20 : decode_any W_80d20 = Some (Op ALU_SLTU 15 12 6, 4%Z).
Proof. vm_refl. Qed.

Definition W_80d24 : bv 32 := 0x07813803.
Lemma F_80d24 : fetch_word Ubsan.M.loaded_segments (0x80d24 : word) = Some W_80d24.
Proof. vm_refl. Qed.
Lemma D_80d24 : decode_any W_80d24 = Some (Load SZ8 true 16 2 120, 4%Z).
Proof. vm_refl. Qed.

Definition W_80d28 : bv 32 := 0x0107c7b3.
Lemma F_80d28 : fetch_word Ubsan.M.loaded_segments (0x80d28 : word) = Some W_80d28.
Proof. vm_refl. Qed.
Lemma D_80d28 : decode_any W_80d28 = Some (Op ALU_XOR 15 15 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_80d2c : bv 32 := 0x0017c793.
Lemma F_80d2c : fetch_word Ubsan.M.loaded_segments (0x80d2c : word) = Some W_80d2c.
Proof. vm_refl. Qed.
Lemma D_80d2c : decode_any W_80d2c = Some (OpImm ALU_XOR 15 15 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_80d30 : bv 32 := 0x00079463.
Lemma F_80d30 : fetch_word Ubsan.M.loaded_segments (0x80d30 : word) = Some W_80d30.
Proof. vm_refl. Qed.
Lemma D_80d30 : decode_any W_80d30 = Some (Branch BC_NE 15 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_80d34 : bv 32 := 0x7c00106f.
Lemma F_80d34 : fetch_word Ubsan.M.loaded_segments (0x80d34 : word) = Some W_80d34.
Proof. vm_refl. Qed.
Lemma D_80d34 : decode_any W_80d34 = Some (Jal 0 6080, 4%Z).
Proof. vm_refl. Qed.

Definition W_80d38 : bv 32 := 0x00590933.
Lemma F_80d38 : fetch_word Ubsan.M.loaded_segments (0x80d38 : word) = Some W_80d38.
Proof. vm_refl. Qed.
Lemma D_80d38 : decode_any W_80d38 = Some (Op ALU_ADD 18 18 5, 4%Z).
Proof. vm_refl. Qed.

Definition W_80d3c : bv 32 := 0x0015859b.
Lemma F_80d3c : fetch_word Ubsan.M.loaded_segments (0x80d3c : word) = Some W_80d3c.
Proof. vm_refl. Qed.
Lemma D_80d3c : decode_any W_80d3c = Some (OpImm32 11 11 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_80d40 : bv 32 := 0x005c0c33.
Lemma F_80d40 : fetch_word Ubsan.M.loaded_segments (0x80d40 : word) = Some W_80d40.
Proof. vm_refl. Qed.
Lemma D_80d40 : decode_any W_80d40 = Some (Op ALU_ADD 24 24 5, 4%Z).
Proof. vm_refl. Qed.

Definition W_80d44 : bv 32 := 0x007b0b33.
Lemma F_80d44 : fetch_word Ubsan.M.loaded_segments (0x80d44 : word) = Some W_80d44.
Proof. vm_refl. Qed.
Lemma D_80d44 : decode_any W_80d44 = Some (Op ALU_ADD 22 22 7, 4%Z).
Proof. vm_refl. Qed.

Definition W_80d48 : bv 32 := 0x00060313.
Lemma F_80d48 : fetch_word Ubsan.M.loaded_segments (0x80d48 : word) = Some W_80d48.
Proof. vm_refl. Qed.
Lemma D_80d48 : decode_any W_80d48 = Some (OpImm ALU_ADD 6 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_80d4c : bv 32 := 0x08013603.
Lemma F_80d4c : fetch_word Ubsan.M.loaded_segments (0x80d4c : word) = Some W_80d4c.
Proof. vm_refl. Qed.
Lemma D_80d4c : decode_any W_80d4c = Some (Load SZ8 true 12 2 128, 4%Z).
Proof. vm_refl. Qed.

Definition W_80d50 : bv 32 := 0xecc59ae3.
Lemma F_80d50 : fetch_word Ubsan.M.loaded_segments (0x80d50 : word) = Some W_80d50.
Proof. vm_refl. Qed.
Lemma D_80d50 : decode_any W_80d50 = Some (Branch BC_NE 11 12 7892, 4%Z).
Proof. vm_refl. Qed.

Definition W_80d54 : bv 32 := 0x01813583.
Lemma F_80d54 : fetch_word Ubsan.M.loaded_segments (0x80d54 : word) = Some W_80d54.
Proof. vm_refl. Qed.
Lemma D_80d54 : decode_any W_80d54 = Some (Load SZ8 true 11 2 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_80d58 : bv 32 := 0x00058463.
Lemma F_80d58 : fetch_word Ubsan.M.loaded_segments (0x80d58 : word) = Some W_80d58.
Proof. vm_refl. Qed.
Lemma D_80d58 : decode_any W_80d58 = Some (Branch BC_EQ 11 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_80d5c : bv 32 := 0x05d0606f.
Lemma F_80d5c : fetch_word Ubsan.M.loaded_segments (0x80d5c : word) = Some W_80d5c.
Proof. vm_refl. Qed.
Lemma D_80d5c : decode_any W_80d5c = Some (Jal 0 26716, 4%Z).
Proof. vm_refl. Qed.

Definition W_80d60 : bv 32 := 0x06813583.
Lemma F_80d60 : fetch_word Ubsan.M.loaded_segments (0x80d60 : word) = Some W_80d60.
Proof. vm_refl. Qed.
Lemma D_80d60 : decode_any W_80d60 = Some (Load SZ8 true 11 2 104, 4%Z).
Proof. vm_refl. Qed.

Definition W_80d64 : bv 32 := 0x0035f593.
Lemma F_80d64 : fetch_word Ubsan.M.loaded_segments (0x80d64 : word) = Some W_80d64.
Proof. vm_refl. Qed.
Lemma D_80d64 : decode_any W_80d64 = Some (OpImm ALU_AND 11 11 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_80d68 : bv 32 := 0x00058463.
Lemma F_80d68 : fetch_word Ubsan.M.loaded_segments (0x80d68 : word) = Some W_80d68.
Proof. vm_refl. Qed.
Lemma D_80d68 : decode_any W_80d68 = Some (Branch BC_EQ 11 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_80d6c : bv 32 := 0x7880106f.
Lemma F_80d6c : fetch_word Ubsan.M.loaded_segments (0x80d6c : word) = Some W_80d6c.
Proof. vm_refl. Qed.
Lemma D_80d6c : decode_any W_80d6c = Some (Jal 0 6024, 4%Z).
Proof. vm_refl. Qed.

Definition W_80d70 : bv 32 := 0xffffc613.
Lemma F_80d70 : fetch_word Ubsan.M.loaded_segments (0x80d70 : word) = Some W_80d70.
Proof. vm_refl. Qed.
Lemma D_80d70 : decode_any W_80d70 = Some (OpImm ALU_XOR 12 31 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_80d74 : bv 32 := 0x06013683.
Lemma F_80d74 : fetch_word Ubsan.M.loaded_segments (0x80d74 : word) = Some W_80d74.
Proof. vm_refl. Qed.
Lemma D_80d74 : decode_any W_80d74 = Some (Load SZ8 true 13 2 96, 4%Z).
Proof. vm_refl. Qed.

Definition W_80d78 : bv 32 := 0xfff6c693.
Lemma F_80d78 : fetch_word Ubsan.M.loaded_segments (0x80d78 : word) = Some W_80d78.
Proof. vm_refl. Qed.
Lemma D_80d78 : decode_any W_80d78 = Some (OpImm ALU_XOR 13 13 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_80d7c : bv 32 := 0x00271793.
Lemma F_80d7c : fetch_word Ubsan.M.loaded_segments (0x80d7c : word) = Some W_80d7c.
Proof. vm_refl. Qed.
Lemma D_80d7c : decode_any W_80d7c = Some (ShiftImm ALU_SLL 15 14 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_80d80 : bv 32 := 0x05813303.
Lemma F_80d80 : fetch_word Ubsan.M.loaded_segments (0x80d80 : word) = Some W_80d80.
Proof. vm_refl. Qed.
Lemma D_80d80 : decode_any W_80d80 = Some (Load SZ8 true 6 2 88, 4%Z).
Proof. vm_refl. Qed.

Definition W_80d84 : bv 32 := 0x00231313.
Lemma F_80d84 : fetch_word Ubsan.M.loaded_segments (0x80d84 : word) = Some W_80d84.
Proof. vm_refl. Qed.
Lemma D_80d84 : decode_any W_80d84 = Some (ShiftImm ALU_SLL 6 6 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_80d88 : bv 32 := 0x00357893.
Lemma F_80d88 : fetch_word Ubsan.M.loaded_segments (0x80d88 : word) = Some W_80d88.
Proof. vm_refl. Qed.
Lemma D_80d88 : decode_any W_80d88 = Some (OpImm ALU_AND 17 10 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_80d8c : bv 32 := 0x05013903.
Lemma F_80d8c : fetch_word Ubsan.M.loaded_segments (0x80d8c : word) = Some W_80d8c.
Proof. vm_refl. Qed.
Lemma D_80d8c : decode_any W_80d8c = Some (Load SZ8 true 18 2 80, 4%Z).
Proof. vm_refl. Qed.

Definition W_80d90 : bv 32 := 0x02813803.
Lemma F_80d90 : fetch_word Ubsan.M.loaded_segments (0x80d90 : word) = Some W_80d90.
Proof. vm_refl. Qed.
Lemma D_80d90 : decode_any W_80d90 = Some (Load SZ8 true 16 2 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_80d94 : bv 32 := 0x412804bb.
Lemma F_80d94 : fetch_word Ubsan.M.loaded_segments (0x80d94 : word) = Some W_80d94.
Proof. vm_refl. Qed.
Lemma D_80d94 : decode_any W_80d94 = Some (Op32 ALU_SUB 9 16 18, 4%Z).
Proof. vm_refl. Qed.

Definition W_80d98 : bv 32 := 0x03813383.
Lemma F_80d98 : fetch_word Ubsan.M.loaded_segments (0x80d98 : word) = Some W_80d98.
Proof. vm_refl. Qed.
Lemma D_80d98 : decode_any W_80d98 = Some (Load SZ8 true 7 2 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_80d9c : bv 32 := 0x03013803.
Lemma F_80d9c : fetch_word Ubsan.M.loaded_segments (0x80d9c : word) = Some W_80d9c.
Proof. vm_refl. Qed.
Lemma D_80d9c : decode_any W_80d9c = Some (Load SZ8 true 16 2 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_80da0 : bv 32 := 0x007803b3.
Lemma F_80da0 : fetch_word Ubsan.M.loaded_segments (0x80da0 : word) = Some W_80da0.
Proof. vm_refl. Qed.
Lemma D_80da0 : decode_any W_80da0 = Some (Op ALU_ADD 7 16 7, 4%Z).
Proof. vm_refl. Qed.

Definition W_80da4 : bv 32 := 0x04813283.
Lemma F_80da4 : fetch_word Ubsan.M.loaded_segments (0x80da4 : word) = Some W_80da4.
Proof. vm_refl. Qed.
Lemma D_80da4 : decode_any W_80da4 = Some (Load SZ8 true 5 2 72, 4%Z).
Proof. vm_refl. Qed.

Definition W_80da8 : bv 32 := 0x43f2d813.
Lemma F_80da8 : fetch_word Ubsan.M.loaded_segments (0x80da8 : word) = Some W_80da8.
Proof. vm_refl. Qed.
Lemma D_80da8 : decode_any W_80da8 = Some (ShiftImm ALU_SRA 16 5 63, 4%Z).
Proof. vm_refl. Qed.

Definition W_80dac : bv 32 := 0x00587e33.
Lemma F_80dac : fetch_word Ubsan.M.loaded_segments (0x80dac : word) = Some W_80dac.
Proof. vm_refl. Qed.
Lemma D_80dac : decode_any W_80dac = Some (Op ALU_AND 28 16 5, 4%Z).
Proof. vm_refl. Qed.

Definition W_80db0 : bv 32 := 0x02000813.
Lemma F_80db0 : fetch_word Ubsan.M.loaded_segments (0x80db0 : word) = Some W_80db0.
Proof. vm_refl. Qed.
Lemma D_80db0 : decode_any W_80db0 = Some (OpImm ALU_ADD 16 0 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_80db4 : bv 32 := 0x00813283.
Lemma F_80db4 : fetch_word Ubsan.M.loaded_segments (0x80db4 : word) = Some W_80db4.
Proof. vm_refl. Qed.
Lemma D_80db4 : decode_any W_80db4 = Some (Load SZ8 true 5 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_80db8 : bv 32 := 0x0012f293.
Lemma F_80db8 : fetch_word Ubsan.M.loaded_segments (0x80db8 : word) = Some W_80db8.
Proof. vm_refl. Qed.
Lemma D_80db8 : decode_any W_80db8 = Some (OpImm ALU_AND 5 5 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_80dbc : bv 32 := 0x00072713.
Lemma F_80dbc : fetch_word Ubsan.M.loaded_segments (0x80dbc : word) = Some W_80dbc.
Proof. vm_refl. Qed.
Lemma D_80dbc : decode_any W_80dbc = Some (OpImm ALU_SLT 14 14 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_80dc0 : bv 32 := 0x01c38e33.
Lemma F_80dc0 : fetch_word Ubsan.M.loaded_segments (0x80dc0 : word) = Some W_80dc0.
Proof. vm_refl. Qed.
Lemma D_80dc0 : decode_any W_80dc0 = Some (Op ALU_ADD 28 7 28, 4%Z).
Proof. vm_refl. Qed.

Definition W_80dc4 : bv 32 := 0xffb00393.
Lemma F_80dc4 : fetch_word Ubsan.M.loaded_segments (0x80dc4 : word) = Some W_80dc4.
Proof. vm_refl. Qed.
Lemma D_80dc4 : decode_any W_80dc4 = Some (OpImm ALU_ADD 7 0 4091, 4%Z).
Proof. vm_refl. Qed.

Definition W_80dc8 : bv 32 := 0x412e093b.
Lemma F_80dc8 : fetch_word Ubsan.M.loaded_segments (0x80dc8 : word) = Some W_80dc8.
Proof. vm_refl. Qed.
Lemma D_80dc8 : decode_any W_80dc8 = Some (Op32 ALU_SUB 18 28 18, 4%Z).
Proof. vm_refl. Qed.

Definition W_80dcc : bv 32 := 0x06813e03.
Lemma F_80dcc : fetch_word Ubsan.M.loaded_segments (0x80dcc : word) = Some W_80dcc.
Proof. vm_refl. Qed.
Lemma D_80dcc : decode_any W_80dcc = Some (Load SZ8 true 28 2 104, 4%Z).
Proof. vm_refl. Qed.

Definition W_80dd0 : bv 32 := 0x006e0e33.
Lemma F_80dd0 : fetch_word Ubsan.M.loaded_segments (0x80dd0 : word) = Some W_80dd0.
Proof. vm_refl. Qed.
Lemma D_80dd0 : decode_any W_80dd0 = Some (Op ALU_ADD 28 28 6, 4%Z).
Proof. vm_refl. Qed.

Definition W_80dd4 : bv 32 := 0x04013983.
Lemma F_80dd4 : fetch_word Ubsan.M.loaded_segments (0x80dd4 : word) = Some W_80dd4.
Proof. vm_refl. Qed.
Lemma D_80dd4 : decode_any W_80dd4 = Some (Load SZ8 true 19 2 64, 4%Z).
Proof. vm_refl. Qed.

Definition W_80dd8 : bv 32 := 0x4139093b.
Lemma F_80dd8 : fetch_word Ubsan.M.loaded_segments (0x80dd8 : word) = Some W_80dd8.
Proof. vm_refl. Qed.
Lemma D_80dd8 : decode_any W_80dd8 = Some (Op32 ALU_SUB 18 18 19, 4%Z).
Proof. vm_refl. Qed.

Definition W_80ddc : bv 32 := 0x43f95993.
Lemma F_80ddc : fetch_word Ubsan.M.loaded_segments (0x80ddc : word) = Some W_80ddc.
Proof. vm_refl. Qed.
Lemma D_80ddc : decode_any W_80ddc = Some (ShiftImm ALU_SRA 19 18 63, 4%Z).
Proof. vm_refl. Qed.

Definition W_80de0 : bv 32 := 0x0129f933.
Lemma F_80de0 : fetch_word Ubsan.M.loaded_segments (0x80de0 : word) = Some W_80de0.
Proof. vm_refl. Qed.
Lemma D_80de0 : decode_any W_80de0 = Some (Op ALU_AND 18 19 18, 4%Z).
Proof. vm_refl. Qed.

Definition W_80de4 : bv 32 := 0x412484bb.
Lemma F_80de4 : fetch_word Ubsan.M.loaded_segments (0x80de4 : word) = Some W_80de4.
Proof. vm_refl. Qed.
Lemma D_80de4 : decode_any W_80de4 = Some (Op32 ALU_SUB 9 9 18, 4%Z).
Proof. vm_refl. Qed.

Definition W_80de8 : bv 32 := 0x01f00993.
Lemma F_80de8 : fetch_word Ubsan.M.loaded_segments (0x80de8 : word) = Some W_80de8.
Proof. vm_refl. Qed.
Lemma D_80de8 : decode_any W_80de8 = Some (OpImm ALU_ADD 19 0 31, 4%Z).
Proof. vm_refl. Qed.

Definition W_80dec : bv 32 := 0x00050a13.
Lemma F_80dec : fetch_word Ubsan.M.loaded_segments (0x80dec : word) = Some W_80dec.
Proof. vm_refl. Qed.
Lemma D_80dec : decode_any W_80dec = Some (OpImm ALU_ADD 20 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_80df0 : bv 32 := 0x06813a83.
Lemma F_80df0 : fetch_word Ubsan.M.loaded_segments (0x80df0 : word) = Some W_80df0.
Proof. vm_refl. Qed.
Lemma D_80df0 : decode_any W_80df0 = Some (Load SZ8 true 21 2 104, 4%Z).
Proof. vm_refl. Qed.

Definition W_80df4 : bv 32 := 0x00ba8ab3.
Lemma F_80df4 : fetch_word Ubsan.M.loaded_segments (0x80df4 : word) = Some W_80df4.
Proof. vm_refl. Qed.
Lemma D_80df4 : decode_any W_80df4 = Some (Op ALU_ADD 21 21 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_80df8 : bv 32 := 0x000a9463.
Lemma F_80df8 : fetch_word Ubsan.M.loaded_segments (0x80df8 : word) = Some W_80df8.
Proof. vm_refl. Qed.
Lemma D_80df8 : decode_any W_80df8 = Some (Branch BC_NE 21 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_80dfc : bv 32 := 0x6f80106f.
Lemma F_80dfc : fetch_word Ubsan.M.loaded_segments (0x80dfc : word) = Some W_80dfc.
Proof. vm_refl. Qed.
Lemma D_80dfc : decode_any W_80dfc = Some (Jal 0 5880, 4%Z).
Proof. vm_refl. Qed.

Definition W_80e00 : bv 32 := 0x010f1463.
Lemma F_80e00 : fetch_word Ubsan.M.loaded_segments (0x80e00 : word) = Some W_80e00.
Proof. vm_refl. Qed.
Lemma D_80e00 : decode_any W_80e00 = Some (Branch BC_NE 30 16 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_80e04 : bv 32 := 0x6f00106f.
Lemma F_80e04 : fetch_word Ubsan.M.loaded_segments (0x80e04 : word) = Some W_80e04.
Proof. vm_refl. Qed.
Lemma D_80e04 : decode_any W_80e04 = Some (Jal 0 5872, 4%Z).
Proof. vm_refl. Qed.

Definition W_80e08 : bv 32 := 0x000aa903.
Lemma F_80e08 : fetch_word Ubsan.M.loaded_segments (0x80e08 : word) = Some W_80e08.
Proof. vm_refl. Qed.
Lemma D_80e08 : decode_any W_80e08 = Some (Load SZ4 true 18 21 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_80e0c : bv 32 := 0x01d91b3b.
Lemma F_80e0c : fetch_word Ubsan.M.loaded_segments (0x80e0c : word) = Some W_80e0c.
Proof. vm_refl. Qed.
Lemma D_80e0c : decode_any W_80e0c = Some (Op32 ALU_SLL 22 18 29, 4%Z).
Proof. vm_refl. Qed.

Definition W_80e10 : bv 32 := 0x02029463.
Lemma F_80e10 : fetch_word Ubsan.M.loaded_segments (0x80e10 : word) = Some W_80e10.
Proof. vm_refl. Qed.
Lemma D_80e10 : decode_any W_80e10 = Some (Branch BC_NE 5 0 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_80e14 : bv 32 := 0x0153f463.
Lemma F_80e14 : fetch_word Ubsan.M.loaded_segments (0x80e14 : word) = Some W_80e14.
Proof. vm_refl. Qed.
Lemma D_80e14 : decode_any W_80e14 = Some (Branch BC_GEU 7 21 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_80e18 : bv 32 := 0x6dc0106f.
Lemma F_80e18 : fetch_word Ubsan.M.loaded_segments (0x80e18 : word) = Some W_80e18.
Proof. vm_refl. Qed.
Lemma D_80e18 : decode_any W_80e18 = Some (Jal 0 5852, 4%Z).
Proof. vm_refl. Qed.

Definition W_80e1c : bv 32 := 0x0089f463.
Lemma F_80e1c : fetch_word Ubsan.M.loaded_segments (0x80e1c : word) = Some W_80e1c.
Proof. vm_refl. Qed.
Lemma D_80e1c : decode_any W_80e1c = Some (Branch BC_GEU 19 8 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_80e20 : bv 32 := 0x6d40106f.
Lemma F_80e20 : fetch_word Ubsan.M.loaded_segments (0x80e20 : word) = Some W_80e20.
Proof. vm_refl. Qed.
Lemma D_80e20 : decode_any W_80e20 = Some (Jal 0 5844, 4%Z).
Proof. vm_refl. Qed.

Definition W_80e24 : bv 32 := 0x004aa903.
Lemma F_80e24 : fetch_word Ubsan.M.loaded_segments (0x80e24 : word) = Some W_80e24.
Proof. vm_refl. Qed.
Lemma D_80e24 : decode_any W_80e24 = Some (Load SZ4 true 18 21 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_80e28 : bv 32 := 0x00cb7b33.
Lemma F_80e28 : fetch_word Ubsan.M.loaded_segments (0x80e28 : word) = Some W_80e28.
Proof. vm_refl. Qed.
Lemma D_80e28 : decode_any W_80e28 = Some (Op ALU_AND 22 22 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_80e2c : bv 32 := 0x0089593b.
Lemma F_80e2c : fetch_word Ubsan.M.loaded_segments (0x80e2c : word) = Some W_80e2c.
Proof. vm_refl. Qed.
Lemma D_80e2c : decode_any W_80e2c = Some (Op32 ALU_SRL 18 18 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_80e30 : bv 32 := 0x01f97933.
Lemma F_80e30 : fetch_word Ubsan.M.loaded_segments (0x80e30 : word) = Some W_80e30.
Proof. vm_refl. Qed.
Lemma D_80e30 : decode_any W_80e30 = Some (Op ALU_AND 18 18 31, 4%Z).
Proof. vm_refl. Qed.

Definition W_80e34 : bv 32 := 0x01696b33.
Lemma F_80e34 : fetch_word Ubsan.M.loaded_segments (0x80e34 : word) = Some W_80e34.
Proof. vm_refl. Qed.
Lemma D_80e34 : decode_any W_80e34 = Some (Op ALU_OR 22 18 22, 4%Z).
Proof. vm_refl. Qed.

Definition W_80e38 : bv 32 := 0x00088463.
Lemma F_80e38 : fetch_word Ubsan.M.loaded_segments (0x80e38 : word) = Some W_80e38.
Proof. vm_refl. Qed.
Lemma D_80e38 : decode_any W_80e38 = Some (Branch BC_EQ 17 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_80e3c : bv 32 := 0x6b80106f.
Lemma F_80e3c : fetch_word Ubsan.M.loaded_segments (0x80e3c : word) = Some W_80e3c.
Proof. vm_refl. Qed.
Lemma D_80e3c : decode_any W_80e3c = Some (Jal 0 5816, 4%Z).
Proof. vm_refl. Qed.

Definition W_80e40 : bv 32 := 0x00051463.
Lemma F_80e40 : fetch_word Ubsan.M.loaded_segments (0x80e40 : word) = Some W_80e40.
Proof. vm_refl. Qed.
Lemma D_80e40 : decode_any W_80e40 = Some (Branch BC_NE 10 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_80e44 : bv 32 := 0x6b00106f.
Lemma F_80e44 : fetch_word Ubsan.M.loaded_segments (0x80e44 : word) = Some W_80e44.
Proof. vm_refl. Qed.
Lemma D_80e44 : decode_any W_80e44 = Some (Jal 0 5808, 4%Z).
Proof. vm_refl. Qed.

Definition W_80e48 : bv 32 := 0x00052903.
Lemma F_80e48 : fetch_word Ubsan.M.loaded_segments (0x80e48 : word) = Some W_80e48.
Proof. vm_refl. Qed.
Lemma D_80e48 : decode_any W_80e48 = Some (Load SZ4 true 18 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_80e4c : bv 32 := 0x00d97bb3.
Lemma F_80e4c : fetch_word Ubsan.M.loaded_segments (0x80e4c : word) = Some W_80e4c.
Proof. vm_refl. Qed.
Lemma D_80e4c : decode_any W_80e4c = Some (Op ALU_AND 23 18 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_80e50 : bv 32 := 0x01696933.
Lemma F_80e50 : fetch_word Ubsan.M.loaded_segments (0x80e50 : word) = Some W_80e50.
Proof. vm_refl. Qed.
Lemma D_80e50 : decode_any W_80e50 = Some (Op ALU_OR 18 18 22, 4%Z).
Proof. vm_refl. Qed.

Definition W_80e54 : bv 32 := 0xfff94913.
Lemma F_80e54 : fetch_word Ubsan.M.loaded_segments (0x80e54 : word) = Some W_80e54.
Proof. vm_refl. Qed.
Lemma D_80e54 : decode_any W_80e54 = Some (OpImm ALU_XOR 18 18 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_80e58 : bv 32 := 0x06013b03.
Lemma F_80e58 : fetch_word Ubsan.M.loaded_segments (0x80e58 : word) = Some W_80e58.
Proof. vm_refl. Qed.
Lemma D_80e58 : decode_any W_80e58 = Some (Load SZ8 true 22 2 96, 4%Z).
Proof. vm_refl. Qed.

Definition W_80e5c : bv 32 := 0x012b7933.
Lemma F_80e5c : fetch_word Ubsan.M.loaded_segments (0x80e5c : word) = Some W_80e5c.
Proof. vm_refl. Qed.
Lemma D_80e5c : decode_any W_80e5c = Some (Op ALU_AND 18 22 18, 4%Z).
Proof. vm_refl. Qed.

Definition W_80e60 : bv 32 := 0x01796933.
Lemma F_80e60 : fetch_word Ubsan.M.loaded_segments (0x80e60 : word) = Some W_80e60.
Proof. vm_refl. Qed.
Lemma D_80e60 : decode_any W_80e60 = Some (Op ALU_OR 18 18 23, 4%Z).
Proof. vm_refl. Qed.

Definition W_80e64 : bv 32 := 0x01478b33.
Lemma F_80e64 : fetch_word Ubsan.M.loaded_segments (0x80e64 : word) = Some W_80e64.
Proof. vm_refl. Qed.
Lemma D_80e64 : decode_any W_80e64 = Some (Op ALU_ADD 22 15 20, 4%Z).
Proof. vm_refl. Qed.

Definition W_80e68 : bv 32 := 0x01252023.
Lemma F_80e68 : fetch_word Ubsan.M.loaded_segments (0x80e68 : word) = Some W_80e68.
Proof. vm_refl. Qed.
Lemma D_80e68 : decode_any W_80e68 = Some (Store SZ4 10 18 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_80e6c : bv 32 := 0x000b1463.
Lemma F_80e6c : fetch_word Ubsan.M.loaded_segments (0x80e6c : word) = Some W_80e6c.
Proof. vm_refl. Qed.
Lemma D_80e6c : decode_any W_80e6c = Some (Branch BC_NE 22 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_80e70 : bv 32 := 0x6840106f.
Lemma F_80e70 : fetch_word Ubsan.M.loaded_segments (0x80e70 : word) = Some W_80e70.
Proof. vm_refl. Qed.
Lemma D_80e70 : decode_any W_80e70 = Some (Jal 0 5764, 4%Z).
Proof. vm_refl. Qed.

Definition W_80e74 : bv 32 := 0x014b3933.
Lemma F_80e74 : fetch_word Ubsan.M.loaded_segments (0x80e74 : word) = Some W_80e74.
Proof. vm_refl. Qed.
Lemma D_80e74 : decode_any W_80e74 = Some (Op ALU_SLTU 18 22 20, 4%Z).
Proof. vm_refl. Qed.

Definition W_80e78 : bv 32 := 0x00e94933.
Lemma F_80e78 : fetch_word Ubsan.M.loaded_segments (0x80e78 : word) = Some W_80e78.
Proof. vm_refl. Qed.
Lemma D_80e78 : decode_any W_80e78 = Some (Op ALU_XOR 18 18 14, 4%Z).
Proof. vm_refl. Qed.

Definition W_80e7c : bv 32 := 0x00194913.
Lemma F_80e7c : fetch_word Ubsan.M.loaded_segments (0x80e7c : word) = Some W_80e7c.
Proof. vm_refl. Qed.
Lemma D_80e7c : decode_any W_80e7c = Some (OpImm ALU_XOR 18 18 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_80e80 : bv 32 := 0x00091463.
Lemma F_80e80 : fetch_word Ubsan.M.loaded_segments (0x80e80 : word) = Some W_80e80.
Proof. vm_refl. Qed.
Lemma D_80e80 : decode_any W_80e80 = Some (Branch BC_NE 18 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_80e84 : bv 32 := 0x6700106f.
Lemma F_80e84 : fetch_word Ubsan.M.loaded_segments (0x80e84 : word) = Some W_80e84.
Proof. vm_refl. Qed.
Lemma D_80e84 : decode_any W_80e84 = Some (Jal 0 5744, 4%Z).
Proof. vm_refl. Qed.

Definition W_80e88 : bv 32 := 0x00be0a33.
Lemma F_80e88 : fetch_word Ubsan.M.loaded_segments (0x80e88 : word) = Some W_80e88.
Proof. vm_refl. Qed.
Lemma D_80e88 : decode_any W_80e88 = Some (Op ALU_ADD 20 28 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_80e8c : bv 32 := 0x000a1463.
Lemma F_80e8c : fetch_word Ubsan.M.loaded_segments (0x80e8c : word) = Some W_80e8c.
Proof. vm_refl. Qed.
Lemma D_80e8c : decode_any W_80e8c = Some (Branch BC_NE 20 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_80e90 : bv 32 := 0x6640106f.
Lemma F_80e90 : fetch_word Ubsan.M.loaded_segments (0x80e90 : word) = Some W_80e90.
Proof. vm_refl. Qed.
Lemma D_80e90 : decode_any W_80e90 = Some (Jal 0 5732, 4%Z).
Proof. vm_refl. Qed.

Definition W_80e94 : bv 32 := 0x015a3933.
Lemma F_80e94 : fetch_word Ubsan.M.loaded_segments (0x80e94 : word) = Some W_80e94.
Proof. vm_refl. Qed.
Lemma D_80e94 : decode_any W_80e94 = Some (Op ALU_SLTU 18 20 21, 4%Z).
Proof. vm_refl. Qed.

Definition W_80e98 : bv 32 := 0x07813a03.
Lemma F_80e98 : fetch_word Ubsan.M.loaded_segments (0x80e98 : word) = Some W_80e98.
Proof. vm_refl. Qed.
Lemma D_80e98 : decode_any W_80e98 = Some (Load SZ8 true 20 2 120, 4%Z).
Proof. vm_refl. Qed.

Definition W_80e9c : bv 32 := 0x01494933.
Lemma F_80e9c : fetch_word Ubsan.M.loaded_segments (0x80e9c : word) = Some W_80e9c.
Proof. vm_refl. Qed.
Lemma D_80e9c : decode_any W_80e9c = Some (Op ALU_XOR 18 18 20, 4%Z).
Proof. vm_refl. Qed.

Definition W_80ea0 : bv 32 := 0x00194913.
Lemma F_80ea0 : fetch_word Ubsan.M.loaded_segments (0x80ea0 : word) = Some W_80ea0.
Proof. vm_refl. Qed.
Lemma D_80ea0 : decode_any W_80ea0 = Some (OpImm ALU_XOR 18 18 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_80ea4 : bv 32 := 0x00091463.
Lemma F_80ea4 : fetch_word Ubsan.M.loaded_segments (0x80ea4 : word) = Some W_80ea4.
Proof. vm_refl. Qed.
Lemma D_80ea4 : decode_any W_80ea4 = Some (Branch BC_NE 18 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_80ea8 : bv 32 := 0x64c0106f.
Lemma F_80ea8 : fetch_word Ubsan.M.loaded_segments (0x80ea8 : word) = Some W_80ea8.
Proof. vm_refl. Qed.
Lemma D_80ea8 : decode_any W_80ea8 = Some (Jal 0 5708, 4%Z).
Proof. vm_refl. Qed.

Definition W_80eac : bv 32 := 0x0014849b.
Lemma F_80eac : fetch_word Ubsan.M.loaded_segments (0x80eac : word) = Some W_80eac.
Proof. vm_refl. Qed.
Lemma D_80eac : decode_any W_80eac = Some (OpImm32 9 9 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_80eb0 : bv 32 := 0x006585b3.
Lemma F_80eb0 : fetch_word Ubsan.M.loaded_segments (0x80eb0 : word) = Some W_80eb0.
Proof. vm_refl. Qed.
Lemma D_80eb0 : decode_any W_80eb0 = Some (Op ALU_ADD 11 11 6, 4%Z).
Proof. vm_refl. Qed.

Definition W_80eb4 : bv 32 := 0x00f50533.
Lemma F_80eb4 : fetch_word Ubsan.M.loaded_segments (0x80eb4 : word) = Some W_80eb4.
Proof. vm_refl. Qed.
Lemma D_80eb4 : decode_any W_80eb4 = Some (Op ALU_ADD 10 10 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_80eb8 : bv 32 := 0x000b0a13.
Lemma F_80eb8 : fetch_word Ubsan.M.loaded_segments (0x80eb8 : word) = Some W_80eb8.
Proof. vm_refl. Qed.
Lemma D_80eb8 : decode_any W_80eb8 = Some (OpImm ALU_ADD 20 22 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_80ebc : bv 32 := 0xf2049ae3.
Lemma F_80ebc : fetch_word Ubsan.M.loaded_segments (0x80ebc : word) = Some W_80ebc.
Proof. vm_refl. Qed.
Lemma D_80ebc : decode_any W_80ebc = Some (Branch BC_NE 9 0 7988, 4%Z).
Proof. vm_refl. Qed.

Definition W_80ec0 : bv 32 := 0x6f80606f.
Lemma F_80ec0 : fetch_word Ubsan.M.loaded_segments (0x80ec0 : word) = Some W_80ec0.
Proof. vm_refl. Qed.
Lemma D_80ec0 : decode_any W_80ec0 = Some (Jal 0 26360, 4%Z).
Proof. vm_refl. Qed.

Definition W_80ec4 : bv 32 := 0x00000b93.
Lemma F_80ec4 : fetch_word Ubsan.M.loaded_segments (0x80ec4 : word) = Some W_80ec4.
Proof. vm_refl. Qed.
Lemma D_80ec4 : decode_any W_80ec4 = Some (OpImm ALU_ADD 23 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_80ec8 : bv 32 := 0x00000a13.
Lemma F_80ec8 : fetch_word Ubsan.M.loaded_segments (0x80ec8 : word) = Some W_80ec8.
Proof. vm_refl. Qed.
Lemma D_80ec8 : decode_any W_80ec8 = Some (OpImm ALU_ADD 20 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_80ecc : bv 32 := 0x00000a93.
Lemma F_80ecc : fetch_word Ubsan.M.loaded_segments (0x80ecc : word) = Some W_80ecc.
Proof. vm_refl. Qed.
Lemma D_80ecc : decode_any W_80ecc = Some (OpImm ALU_ADD 21 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_80ed0 : bv 32 := 0x00000613.
Lemma F_80ed0 : fetch_word Ubsan.M.loaded_segments (0x80ed0 : word) = Some W_80ed0.
Proof. vm_refl. Qed.
Lemma D_80ed0 : decode_any W_80ed0 = Some (OpImm ALU_ADD 12 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_80ed4 : bv 32 := 0x00000413.
Lemma F_80ed4 : fetch_word Ubsan.M.loaded_segments (0x80ed4 : word) = Some W_80ed4.
Proof. vm_refl. Qed.
Lemma D_80ed4 : decode_any W_80ed4 = Some (OpImm ALU_ADD 8 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_80ed8 : bv 32 := 0x00000913.
Lemma F_80ed8 : fetch_word Ubsan.M.loaded_segments (0x80ed8 : word) = Some W_80ed8.
Proof. vm_refl. Qed.
Lemma D_80ed8 : decode_any W_80ed8 = Some (OpImm ALU_ADD 18 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_80edc : bv 32 := 0x00100b13.
Lemma F_80edc : fetch_word Ubsan.M.loaded_segments (0x80edc : word) = Some W_80edc.
Proof. vm_refl. Qed.
Lemma D_80edc : decode_any W_80edc = Some (OpImm ALU_ADD 22 0 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_80ee0 : bv 32 := 0x009687b3.
Lemma F_80ee0 : fetch_word Ubsan.M.loaded_segments (0x80ee0 : word) = Some W_80ee0.
Proof. vm_refl. Qed.
Lemma D_80ee0 : decode_any W_80ee0 = Some (Op ALU_ADD 15 13 9, 4%Z).
Proof. vm_refl. Qed.

Definition W_80ee4 : bv 32 := 0x009686bb.
Lemma F_80ee4 : fetch_word Ubsan.M.loaded_segments (0x80ee4 : word) = Some W_80ee4.
Proof. vm_refl. Qed.
Lemma D_80ee4 : decode_any W_80ee4 = Some (Op32 ALU_ADD 13 13 9, 4%Z).
Proof. vm_refl. Qed.

Definition W_80ee8 : bv 32 := 0x00f68463.
Lemma F_80ee8 : fetch_word Ubsan.M.loaded_segments (0x80ee8 : word) = Some W_80ee8.
Proof. vm_refl. Qed.
Lemma D_80ee8 : decode_any W_80ee8 = Some (Branch BC_EQ 13 15 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_80eec : bv 32 := 0x6080106f.
Lemma F_80eec : fetch_word Ubsan.M.loaded_segments (0x80eec : word) = Some W_80eec.
Proof. vm_refl. Qed.
Lemma D_80eec : decode_any W_80eec = Some (Jal 0 5640, 4%Z).
Proof. vm_refl. Qed.

Definition W_80ef0 : bv 32 := 0x01f7f793.
Lemma F_80ef0 : fetch_word Ubsan.M.loaded_segments (0x80ef0 : word) = Some W_80ef0.
Proof. vm_refl. Qed.
Lemma D_80ef0 : decode_any W_80ef0 = Some (OpImm ALU_AND 15 15 31, 4%Z).
Proof. vm_refl. Qed.

Definition W_80ef4 : bv 32 := 0x0017b493.
Lemma F_80ef4 : fetch_word Ubsan.M.loaded_segments (0x80ef4 : word) = Some W_80ef4.
Proof. vm_refl. Qed.
Lemma D_80ef4 : decode_any W_80ef4 = Some (OpImm ALU_SLTU 9 15 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_80ef8 : bv 32 := 0x00c4e4b3.
Lemma F_80ef8 : fetch_word Ubsan.M.loaded_segments (0x80ef8 : word) = Some W_80ef8.
Proof. vm_refl. Qed.
Lemma D_80ef8 : decode_any W_80ef8 = Some (Op ALU_OR 9 9 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_80efc : bv 32 := 0x00048863.
Lemma F_80efc : fetch_word Ubsan.M.loaded_segments (0x80efc : word) = Some W_80efc.
Proof. vm_refl. Qed.
Lemma D_80efc : decode_any W_80efc = Some (Branch BC_EQ 9 0 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_80f00 : bv 32 := 0x00000513.
Lemma F_80f00 : fetch_word Ubsan.M.loaded_segments (0x80f00 : word) = Some W_80f00.
Proof. vm_refl. Qed.
Lemma D_80f00 : decode_any W_80f00 = Some (OpImm ALU_ADD 10 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_80f04 : bv 32 := 0x00000f13.
Lemma F_80f04 : fetch_word Ubsan.M.loaded_segments (0x80f04 : word) = Some W_80f04.
Proof. vm_refl. Qed.
Lemma D_80f04 : decode_any W_80f04 = Some (OpImm ALU_ADD 30 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_80f08 : bv 32 := 0x18c0006f.
Lemma F_80f08 : fetch_word Ubsan.M.loaded_segments (0x80f08 : word) = Some W_80f08.
Proof. vm_refl. Qed.
Lemma D_80f08 : decode_any W_80f08 = Some (Jal 0 396, 4%Z).
Proof. vm_refl. Qed.

Definition W_80f0c : bv 32 := 0x00279613.
Lemma F_80f0c : fetch_word Ubsan.M.loaded_segments (0x80f0c : word) = Some W_80f0c.
Proof. vm_refl. Qed.
Lemma D_80f0c : decode_any W_80f0c = Some (ShiftImm ALU_SLL 12 15 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_80f10 : bv 32 := 0xfff9e697.
Lemma F_80f10 : fetch_word Ubsan.M.loaded_segments (0x80f10 : word) = Some W_80f10.
Proof. vm_refl. Qed.
Lemma D_80f10 : decode_any W_80f10 = Some (Auipc 13 1048478, 4%Z).
Proof. vm_refl. Qed.

Definition W_80f14 : bv 32 := 0x5b468693.
Lemma F_80f14 : fetch_word Ubsan.M.loaded_segments (0x80f14 : word) = Some W_80f14.
Proof. vm_refl. Qed.
Lemma D_80f14 : decode_any W_80f14 = Some (OpImm ALU_ADD 13 13 1460, 4%Z).
Proof. vm_refl. Qed.

Definition W_80f18 : bv 32 := 0xfff6c793.
Lemma F_80f18 : fetch_word Ubsan.M.loaded_segments (0x80f18 : word) = Some W_80f18.
Proof. vm_refl. Qed.
Lemma D_80f18 : decode_any W_80f18 = Some (OpImm ALU_XOR 15 13 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_80f1c : bv 32 := 0x00c7f463.
Lemma F_80f1c : fetch_word Ubsan.M.loaded_segments (0x80f1c : word) = Some W_80f1c.
Proof. vm_refl. Qed.
Lemma D_80f1c : decode_any W_80f1c = Some (Branch BC_GEU 15 12 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_80f20 : bv 32 := 0x5d40106f.
Lemma F_80f20 : fetch_word Ubsan.M.loaded_segments (0x80f20 : word) = Some W_80f20.
Proof. vm_refl. Qed.
Lemma D_80f20 : decode_any W_80f20 = Some (Jal 0 5588, 4%Z).
Proof. vm_refl. Qed.

Definition W_80f24 : bv 32 := 0x00c68633.
Lemma F_80f24 : fetch_word Ubsan.M.loaded_segments (0x80f24 : word) = Some W_80f24.
Proof. vm_refl. Qed.
Lemma D_80f24 : decode_any W_80f24 = Some (Op ALU_ADD 12 13 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_80f28 : bv 32 := 0x00062e83.
Lemma F_80f28 : fetch_word Ubsan.M.loaded_segments (0x80f28 : word) = Some W_80f28.
Proof. vm_refl. Qed.
Lemma D_80f28 : decode_any W_80f28 = Some (Load SZ4 true 29 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_80f2c : bv 32 := 0x04008663.
Lemma F_80f2c : fetch_word Ubsan.M.loaded_segments (0x80f2c : word) = Some W_80f2c.
Proof. vm_refl. Qed.
Lemma D_80f2c : decode_any W_80f2c = Some (Branch BC_EQ 1 0 76, 4%Z).
Proof. vm_refl. Qed.

Definition W_80f30 : bv 32 := 0x004a0513.
Lemma F_80f30 : fetch_word Ubsan.M.loaded_segments (0x80f30 : word) = Some W_80f30.
Proof. vm_refl. Qed.
Lemma D_80f30 : decode_any W_80f30 = Some (OpImm ALU_ADD 10 20 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_80f34 : bv 32 := 0x00500613.
Lemma F_80f34 : fetch_word Ubsan.M.loaded_segments (0x80f34 : word) = Some W_80f34.
Proof. vm_refl. Qed.
Lemma D_80f34 : decode_any W_80f34 = Some (OpImm ALU_ADD 12 0 5, 4%Z).
Proof. vm_refl. Qed.

Definition W_80f38 : bv 32 := 0x00c57463.
Lemma F_80f38 : fetch_word Ubsan.M.loaded_segments (0x80f38 : word) = Some W_80f38.
Proof. vm_refl. Qed.
Lemma D_80f38 : decode_any W_80f38 = Some (Branch BC_GEU 10 12 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_80f3c : bv 32 := 0x5b80106f.
Lemma F_80f3c : fetch_word Ubsan.M.loaded_segments (0x80f3c : word) = Some W_80f3c.
Proof. vm_refl. Qed.
Lemma D_80f3c : decode_any W_80f3c = Some (Jal 0 5560, 4%Z).
Proof. vm_refl. Qed.

Definition W_80f40 : bv 32 := 0x002f9f13.
Lemma F_80f40 : fetch_word Ubsan.M.loaded_segments (0x80f40 : word) = Some W_80f40.
Proof. vm_refl. Qed.
Lemma D_80f40 : decode_any W_80f40 = Some (ShiftImm ALU_SLL 30 31 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_80f44 : bv 32 := 0xfff54613.
Lemma F_80f44 : fetch_word Ubsan.M.loaded_segments (0x80f44 : word) = Some W_80f44.
Proof. vm_refl. Qed.
Lemma D_80f44 : decode_any W_80f44 = Some (OpImm ALU_XOR 12 10 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_80f48 : bv 32 := 0x01e67463.
Lemma F_80f48 : fetch_word Ubsan.M.loaded_segments (0x80f48 : word) = Some W_80f48.
Proof. vm_refl. Qed.
Lemma D_80f48 : decode_any W_80f48 = Some (Branch BC_GEU 12 30 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_80f4c : bv 32 := 0x5a80106f.
Lemma F_80f4c : fetch_word Ubsan.M.loaded_segments (0x80f4c : word) = Some W_80f4c.
Proof. vm_refl. Qed.
Lemma D_80f4c : decode_any W_80f4c = Some (Jal 0 5544, 4%Z).
Proof. vm_refl. Qed.

Definition W_80f50 : bv 32 := 0x004a8613.
Lemma F_80f50 : fetch_word Ubsan.M.loaded_segments (0x80f50 : word) = Some W_80f50.
Proof. vm_refl. Qed.
Lemma D_80f50 : decode_any W_80f50 = Some (OpImm ALU_ADD 12 21 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_80f54 : bv 32 := 0x00500693.
Lemma F_80f54 : fetch_word Ubsan.M.loaded_segments (0x80f54 : word) = Some W_80f54.
Proof. vm_refl. Qed.
Lemma D_80f54 : decode_any W_80f54 = Some (OpImm ALU_ADD 13 0 5, 4%Z).
Proof. vm_refl. Qed.

Definition W_80f58 : bv 32 := 0x00d67463.
Lemma F_80f58 : fetch_word Ubsan.M.loaded_segments (0x80f58 : word) = Some W_80f58.
Proof. vm_refl. Qed.
Lemma D_80f58 : decode_any W_80f58 = Some (Branch BC_GEU 12 13 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_80f5c : bv 32 := 0x5980106f.
Lemma F_80f5c : fetch_word Ubsan.M.loaded_segments (0x80f5c : word) = Some W_80f5c.
Proof. vm_refl. Qed.
Lemma D_80f5c : decode_any W_80f5c = Some (Jal 0 5528, 4%Z).
Proof. vm_refl. Qed.

Definition W_80f60 : bv 32 := 0xfff64693.
Lemma F_80f60 : fetch_word Ubsan.M.loaded_segments (0x80f60 : word) = Some W_80f60.
Proof. vm_refl. Qed.
Lemma D_80f60 : decode_any W_80f60 = Some (OpImm ALU_XOR 13 12 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_80f64 : bv 32 := 0x01e6f463.
Lemma F_80f64 : fetch_word Ubsan.M.loaded_segments (0x80f64 : word) = Some W_80f64.
Proof. vm_refl. Qed.
Lemma D_80f64 : decode_any W_80f64 = Some (Branch BC_GEU 13 30 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_80f68 : bv 32 := 0x58c0106f.
Lemma F_80f68 : fetch_word Ubsan.M.loaded_segments (0x80f68 : word) = Some W_80f68.
Proof. vm_refl. Qed.
Lemma D_80f68 : decode_any W_80f68 = Some (Jal 0 5516, 4%Z).
Proof. vm_refl. Qed.

Definition W_80f6c : bv 32 := 0x01e50533.
Lemma F_80f6c : fetch_word Ubsan.M.loaded_segments (0x80f6c : word) = Some W_80f6c.
Proof. vm_refl. Qed.
Lemma D_80f6c : decode_any W_80f6c = Some (Op ALU_ADD 10 10 30, 4%Z).
Proof. vm_refl. Qed.

Definition W_80f70 : bv 32 := 0x01e60f33.
Lemma F_80f70 : fetch_word Ubsan.M.loaded_segments (0x80f70 : word) = Some W_80f70.
Proof. vm_refl. Qed.
Lemma D_80f70 : decode_any W_80f70 = Some (Op ALU_ADD 30 12 30, 4%Z).
Proof. vm_refl. Qed.

Definition W_80f74 : bv 32 := 0x1200006f.
Lemma F_80f74 : fetch_word Ubsan.M.loaded_segments (0x80f74 : word) = Some W_80f74.
Proof. vm_refl. Qed.
Lemma D_80f74 : decode_any W_80f74 = Some (Jal 0 288, 4%Z).
Proof. vm_refl. Qed.

Definition W_80f78 : bv 32 := 0x027707b3.
Lemma F_80f78 : fetch_word Ubsan.M.loaded_segments (0x80f78 : word) = Some W_80f78.
Proof. vm_refl. Qed.
Lemma D_80f78 : decode_any W_80f78 = Some (Mul M_MUL 15 14 7, 4%Z).
Proof. vm_refl. Qed.

Definition W_80f7c : bv 32 := 0x0277063b.
Lemma F_80f7c : fetch_word Ubsan.M.loaded_segments (0x80f7c : word) = Some W_80f7c.
Proof. vm_refl. Qed.
Lemma D_80f7c : decode_any W_80f7c = Some (Mul32 M_MUL 12 14 7, 4%Z).
Proof. vm_refl. Qed.

Definition W_80f80 : bv 32 := 0x00f60463.
Lemma F_80f80 : fetch_word Ubsan.M.loaded_segments (0x80f80 : word) = Some W_80f80.
Proof. vm_refl. Qed.
Lemma D_80f80 : decode_any W_80f80 = Some (Branch BC_EQ 12 15 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_80f84 : bv 32 := 0x5700106f.
Lemma F_80f84 : fetch_word Ubsan.M.loaded_segments (0x80f84 : word) = Some W_80f84.
Proof. vm_refl. Qed.
Lemma D_80f84 : decode_any W_80f84 = Some (Jal 0 5488, 4%Z).
Proof. vm_refl. Qed.

Definition W_80f88 : bv 32 := 0x0007879b.
Lemma F_80f88 : fetch_word Ubsan.M.loaded_segments (0x80f88 : word) = Some W_80f88.
Proof. vm_refl. Qed.
Lemma D_80f88 : decode_any W_80f88 = Some (OpImm32 15 15 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_80f8c : bv 32 := 0x00279693.
Lemma F_80f8c : fetch_word Ubsan.M.loaded_segments (0x80f8c : word) = Some W_80f8c.
Proof. vm_refl. Qed.
Lemma D_80f8c : decode_any W_80f8c = Some (ShiftImm ALU_SLL 13 15 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_80f90 : bv 32 := 0x00a686b3.
Lemma F_80f90 : fetch_word Ubsan.M.loaded_segments (0x80f90 : word) = Some W_80f90.
Proof. vm_refl. Qed.
Lemma D_80f90 : decode_any W_80f90 = Some (Op ALU_ADD 13 13 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_80f94 : bv 32 := 0x00a03633.
Lemma F_80f94 : fetch_word Ubsan.M.loaded_segments (0x80f94 : word) = Some W_80f94.
Proof. vm_refl. Qed.
Lemma D_80f94 : decode_any W_80f94 = Some (Op ALU_SLTU 12 0 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_80f98 : bv 32 := 0x0016b813.
Lemma F_80f98 : fetch_word Ubsan.M.loaded_segments (0x80f98 : word) = Some W_80f98.
Proof. vm_refl. Qed.
Lemma D_80f98 : decode_any W_80f98 = Some (OpImm ALU_SLTU 16 13 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_80f9c : bv 32 := 0x01061463.
Lemma F_80f9c : fetch_word Ubsan.M.loaded_segments (0x80f9c : word) = Some W_80f9c.
Proof. vm_refl. Qed.
Lemma D_80f9c : decode_any W_80f9c = Some (Branch BC_NE 12 16 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_80fa0 : bv 32 := 0x5540106f.
Lemma F_80fa0 : fetch_word Ubsan.M.loaded_segments (0x80fa0 : word) = Some W_80fa0.
Proof. vm_refl. Qed.
Lemma D_80fa0 : decode_any W_80fa0 = Some (Jal 0 5460, 4%Z).
Proof. vm_refl. Qed.

Definition W_80fa4 : bv 32 := 0x00a6b533.
Lemma F_80fa4 : fetch_word Ubsan.M.loaded_segments (0x80fa4 : word) = Some W_80fa4.
Proof. vm_refl. Qed.
Lemma D_80fa4 : decode_any W_80fa4 = Some (Op ALU_SLTU 10 13 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_80fa8 : bv 32 := 0x0007a793.
Lemma F_80fa8 : fetch_word Ubsan.M.loaded_segments (0x80fa8 : word) = Some W_80fa8.
Proof. vm_refl. Qed.
Lemma D_80fa8 : decode_any W_80fa8 = Some (OpImm ALU_SLT 15 15 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_80fac : bv 32 := 0x00f54533.
Lemma F_80fac : fetch_word Ubsan.M.loaded_segments (0x80fac : word) = Some W_80fac.
Proof. vm_refl. Qed.
Lemma D_80fac : decode_any W_80fac = Some (Op ALU_XOR 10 10 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_80fb0 : bv 32 := 0x00154513.
Lemma F_80fb0 : fetch_word Ubsan.M.loaded_segments (0x80fb0 : word) = Some W_80fb0.
Proof. vm_refl. Qed.
Lemma D_80fb0 : decode_any W_80fb0 = Some (OpImm ALU_XOR 10 10 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_80fb4 : bv 32 := 0x00051463.
Lemma F_80fb4 : fetch_word Ubsan.M.loaded_segments (0x80fb4 : word) = Some W_80fb4.
Proof. vm_refl. Qed.
Lemma D_80fb4 : decode_any W_80fb4 = Some (Branch BC_NE 10 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_80fb8 : bv 32 := 0x53c0106f.
Lemma F_80fb8 : fetch_word Ubsan.M.loaded_segments (0x80fb8 : word) = Some W_80fb8.
Proof. vm_refl. Qed.
Lemma D_80fb8 : decode_any W_80fb8 = Some (Jal 0 5436, 4%Z).
Proof. vm_refl. Qed.

Definition W_80fbc : bv 32 := 0x405cd51b.
Lemma F_80fbc : fetch_word Ubsan.M.loaded_segments (0x80fbc : word) = Some W_80fbc.
Proof. vm_refl. Qed.
Lemma D_80fbc : decode_any W_80fbc = Some (ShiftImm32 ALU_SRA 10 25 5, 4%Z).
Proof. vm_refl. Qed.

Definition W_80fc0 : bv 32 := 0x00251793.
Lemma F_80fc0 : fetch_word Ubsan.M.loaded_segments (0x80fc0 : word) = Some W_80fc0.
Proof. vm_refl. Qed.
Lemma D_80fc0 : decode_any W_80fc0 = Some (ShiftImm ALU_SLL 15 10 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_80fc4 : bv 32 := 0x00d787b3.
Lemma F_80fc4 : fetch_word Ubsan.M.loaded_segments (0x80fc4 : word) = Some W_80fc4.
Proof. vm_refl. Qed.
Lemma D_80fc4 : decode_any W_80fc4 = Some (Op ALU_ADD 15 15 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_80fc8 : bv 32 := 0x0017b813.
Lemma F_80fc8 : fetch_word Ubsan.M.loaded_segments (0x80fc8 : word) = Some W_80fc8.
Proof. vm_refl. Qed.
Lemma D_80fc8 : decode_any W_80fc8 = Some (OpImm ALU_SLTU 16 15 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_80fcc : bv 32 := 0x01061463.
Lemma F_80fcc : fetch_word Ubsan.M.loaded_segments (0x80fcc : word) = Some W_80fcc.
Proof. vm_refl. Qed.
Lemma D_80fcc : decode_any W_80fcc = Some (Branch BC_NE 12 16 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_80fd0 : bv 32 := 0x5240106f.
Lemma F_80fd0 : fetch_word Ubsan.M.loaded_segments (0x80fd0 : word) = Some W_80fd0.
Proof. vm_refl. Qed.
Lemma D_80fd0 : decode_any W_80fd0 = Some (Jal 0 5412, 4%Z).
Proof. vm_refl. Qed.

Definition W_80fd4 : bv 32 := 0x00d7b6b3.
Lemma F_80fd4 : fetch_word Ubsan.M.loaded_segments (0x80fd4 : word) = Some W_80fd4.
Proof. vm_refl. Qed.
Lemma D_80fd4 : decode_any W_80fd4 = Some (Op ALU_SLTU 13 15 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_80fd8 : bv 32 := 0x00052513.
Lemma F_80fd8 : fetch_word Ubsan.M.loaded_segments (0x80fd8 : word) = Some W_80fd8.
Proof. vm_refl. Qed.
Lemma D_80fd8 : decode_any W_80fd8 = Some (OpImm ALU_SLT 10 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_80fdc : bv 32 := 0x00a6c533.
Lemma F_80fdc : fetch_word Ubsan.M.loaded_segments (0x80fdc : word) = Some W_80fdc.
Proof. vm_refl. Qed.
Lemma D_80fdc : decode_any W_80fdc = Some (Op ALU_XOR 10 13 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_80fe0 : bv 32 := 0x00154513.
Lemma F_80fe0 : fetch_word Ubsan.M.loaded_segments (0x80fe0 : word) = Some W_80fe0.
Proof. vm_refl. Qed.
Lemma D_80fe0 : decode_any W_80fe0 = Some (OpImm ALU_XOR 10 10 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_80fe4 : bv 32 := 0x00051463.
Lemma F_80fe4 : fetch_word Ubsan.M.loaded_segments (0x80fe4 : word) = Some W_80fe4.
Proof. vm_refl. Qed.
Lemma D_80fe4 : decode_any W_80fe4 = Some (Branch BC_NE 10 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_80fe8 : bv 32 := 0x50c0106f.
Lemma F_80fe8 : fetch_word Ubsan.M.loaded_segments (0x80fe8 : word) = Some W_80fe8.
Proof. vm_refl. Qed.
Lemma D_80fe8 : decode_any W_80fe8 = Some (Jal 0 5388, 4%Z).
Proof. vm_refl. Qed.

Definition W_80fec : bv 32 := 0x002f9f13.
Lemma F_80fec : fetch_word Ubsan.M.loaded_segments (0x80fec : word) = Some W_80fec.
Proof. vm_refl. Qed.
Lemma D_80fec : decode_any W_80fec = Some (ShiftImm ALU_SLL 30 31 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_80ff0 : bv 32 := 0x01e78533.
Lemma F_80ff0 : fetch_word Ubsan.M.loaded_segments (0x80ff0 : word) = Some W_80ff0.
Proof. vm_refl. Qed.
Lemma D_80ff0 : decode_any W_80ff0 = Some (Op ALU_ADD 10 15 30, 4%Z).
Proof. vm_refl. Qed.

Definition W_80ff4 : bv 32 := 0x00f57463.
Lemma F_80ff4 : fetch_word Ubsan.M.loaded_segments (0x80ff4 : word) = Some W_80ff4.
Proof. vm_refl. Qed.
Lemma D_80ff4 : decode_any W_80ff4 = Some (Branch BC_GEU 10 15 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_80ff8 : bv 32 := 0x4fc0106f.
Lemma F_80ff8 : fetch_word Ubsan.M.loaded_segments (0x80ff8 : word) = Some W_80ff8.
Proof. vm_refl. Qed.
Lemma D_80ff8 : decode_any W_80ff8 = Some (Jal 0 5372, 4%Z).
Proof. vm_refl. Qed.

Definition W_80ffc : bv 32 := 0x00153693.
Lemma F_80ffc : fetch_word Ubsan.M.loaded_segments (0x80ffc : word) = Some W_80ffc.
Proof. vm_refl. Qed.
Lemma D_80ffc : decode_any W_80ffc = Some (OpImm ALU_SLTU 13 10 1, 4%Z).
Proof. vm_refl. Qed.
