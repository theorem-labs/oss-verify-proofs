(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OssFuzzTheorems.openssl.pem.images Require Import Asan.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.

(* [comment removed for export] *)
Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

(* [comment removed for export] *)
Definition W_55f044 : bv 32 := 0x0e060a63.
Lemma F_55f044 : fetch_word Asan.M.loaded_segments (0x526914 : word) = Some W_55f044.
Proof. vm_refl. Qed.
Lemma D_55f044 : decode_any W_55f044 = Some (Branch BC_EQ 12 0 244, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_55f048 : bv 32 := 0x00b50023.
Lemma F_55f048 : fetch_word Asan.M.loaded_segments (0x526918 : word) = Some W_55f048.
Proof. vm_refl. Qed.
Lemma D_55f048 : decode_any W_55f048 = Some (Store SZ1 10 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_55f04c : bv 32 := 0x00c506b3.
Lemma F_55f04c : fetch_word Asan.M.loaded_segments (0x52691c : word) = Some W_55f04c.
Proof. vm_refl. Qed.
Lemma D_55f04c : decode_any W_55f04c = Some (Op ALU_ADD 13 10 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_55f050 : bv 32 := 0x00300713.
Lemma F_55f050 : fetch_word Asan.M.loaded_segments (0x526920 : word) = Some W_55f050.
Proof. vm_refl. Qed.
Lemma D_55f050 : decode_any W_55f050 = Some (OpImm ALU_ADD 14 0 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_55f054 : bv 32 := 0xfeb68fa3.
Lemma F_55f054 : fetch_word Asan.M.loaded_segments (0x526924 : word) = Some W_55f054.
Proof. vm_refl. Qed.
Lemma D_55f054 : decode_any W_55f054 = Some (Store SZ1 13 11 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_55f058 : bv 32 := 0x0ee66063.
Lemma F_55f058 : fetch_word Asan.M.loaded_segments (0x526928 : word) = Some W_55f058.
Proof. vm_refl. Qed.
Lemma D_55f058 : decode_any W_55f058 = Some (Branch BC_LTU 12 14 224, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_55f05c : bv 32 := 0x00b500a3.
Lemma F_55f05c : fetch_word Asan.M.loaded_segments (0x52692c : word) = Some W_55f05c.
Proof. vm_refl. Qed.
Lemma D_55f05c : decode_any W_55f05c = Some (Store SZ1 10 11 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_55f060 : bv 32 := 0x00b50123.
Lemma F_55f060 : fetch_word Asan.M.loaded_segments (0x526930 : word) = Some W_55f060.
Proof. vm_refl. Qed.
Lemma D_55f060 : decode_any W_55f060 = Some (Store SZ1 10 11 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_55f064 : bv 32 := 0x00700713.
Lemma F_55f064 : fetch_word Asan.M.loaded_segments (0x526934 : word) = Some W_55f064.
Proof. vm_refl. Qed.
Lemma D_55f064 : decode_any W_55f064 = Some (OpImm ALU_ADD 14 0 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_55f068 : bv 32 := 0xfeb68ea3.
Lemma F_55f068 : fetch_word Asan.M.loaded_segments (0x526938 : word) = Some W_55f068.
Proof. vm_refl. Qed.
Lemma D_55f068 : decode_any W_55f068 = Some (Store SZ1 13 11 4093, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_55f06c : bv 32 := 0xfeb68f23.
Lemma F_55f06c : fetch_word Asan.M.loaded_segments (0x52693c : word) = Some W_55f06c.
Proof. vm_refl. Qed.
Lemma D_55f06c : decode_any W_55f06c = Some (Store SZ1 13 11 4094, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_55f070 : bv 32 := 0x0ce66463.
Lemma F_55f070 : fetch_word Asan.M.loaded_segments (0x526940 : word) = Some W_55f070.
Proof. vm_refl. Qed.
Lemma D_55f070 : decode_any W_55f070 = Some (Branch BC_LTU 12 14 200, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_55f074 : bv 32 := 0x00b501a3.
Lemma F_55f074 : fetch_word Asan.M.loaded_segments (0x526944 : word) = Some W_55f074.
Proof. vm_refl. Qed.
Lemma D_55f074 : decode_any W_55f074 = Some (Store SZ1 10 11 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_55f078 : bv 32 := 0x00900793.
Lemma F_55f078 : fetch_word Asan.M.loaded_segments (0x526948 : word) = Some W_55f078.
Proof. vm_refl. Qed.
Lemma D_55f078 : decode_any W_55f078 = Some (OpImm ALU_ADD 15 0 9, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_55f07c : bv 32 := 0xfeb68e23.
Lemma F_55f07c : fetch_word Asan.M.loaded_segments (0x52694c : word) = Some W_55f07c.
Proof. vm_refl. Qed.
Lemma D_55f07c : decode_any W_55f07c = Some (Store SZ1 13 11 4092, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_55f080 : bv 32 := 0x0af66c63.
Lemma F_55f080 : fetch_word Asan.M.loaded_segments (0x526950 : word) = Some W_55f080.
Proof. vm_refl. Qed.
Lemma D_55f080 : decode_any W_55f080 = Some (Branch BC_LTU 12 15 184, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_55f084 : bv 32 := 0x40a006bb.
Lemma F_55f084 : fetch_word Asan.M.loaded_segments (0x526954 : word) = Some W_55f084.
Proof. vm_refl. Qed.
Lemma D_55f084 : decode_any W_55f084 = Some (Op32 ALU_SUB 13 0 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_55f088 : bv 32 := 0x03859813.
Lemma F_55f088 : fetch_word Asan.M.loaded_segments (0x526958 : word) = Some W_55f088.
Proof. vm_refl. Qed.
Lemma D_55f088 : decode_any W_55f088 = Some (ShiftImm ALU_SLL 16 11 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_55f08c : bv 32 := 0x101015b7.
Lemma F_55f08c : fetch_word Asan.M.loaded_segments (0x52695c : word) = Some W_55f08c.
Proof. vm_refl. Qed.
Lemma D_55f08c : decode_any W_55f08c = Some (Lui 11 65793, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_55f090 : bv 32 := 0x0036f693.
Lemma F_55f090 : fetch_word Asan.M.loaded_segments (0x526960 : word) = Some W_55f090.
Proof. vm_refl. Qed.
Lemma D_55f090 : decode_any W_55f090 = Some (OpImm ALU_AND 13 13 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_55f094 : bv 32 := 0x00459713.
Lemma F_55f094 : fetch_word Asan.M.loaded_segments (0x526964 : word) = Some W_55f094.
Proof. vm_refl. Qed.
Lemma D_55f094 : decode_any W_55f094 = Some (ShiftImm ALU_SLL 14 11 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_55f098 : bv 32 := 0x40d60633.
Lemma F_55f098 : fetch_word Asan.M.loaded_segments (0x526968 : word) = Some W_55f098.
Proof. vm_refl. Qed.
Lemma D_55f098 : decode_any W_55f098 = Some (Op ALU_SUB 12 12 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_55f09c : bv 32 := 0x00d505b3.
Lemma F_55f09c : fetch_word Asan.M.loaded_segments (0x52696c : word) = Some W_55f09c.
Proof. vm_refl. Qed.
Lemma D_55f09c : decode_any W_55f09c = Some (Op ALU_ADD 11 10 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_55f0a0 : bv 32 := 0x10070693.
Lemma F_55f0a0 : fetch_word Asan.M.loaded_segments (0x526970 : word) = Some W_55f0a0.
Proof. vm_refl. Qed.
Lemma D_55f0a0 : decode_any W_55f0a0 = Some (OpImm ALU_ADD 13 14 256, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_55f0a4 : bv 32 := 0xffc67713.
Lemma F_55f0a4 : fetch_word Asan.M.loaded_segments (0x526974 : word) = Some W_55f0a4.
Proof. vm_refl. Qed.
Lemma D_55f0a4 : decode_any W_55f0a4 = Some (OpImm ALU_AND 14 12 4092, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_55f0a8 : bv 32 := 0x02d83633.
Lemma F_55f0a8 : fetch_word Asan.M.loaded_segments (0x526978 : word) = Some W_55f0a8.
Proof. vm_refl. Qed.
Lemma D_55f0a8 : decode_any W_55f0a8 = Some (Mul M_MULHU 12 16 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_55f0ac : bv 32 := 0x00c5a023.
Lemma F_55f0ac : fetch_word Asan.M.loaded_segments (0x52697c : word) = Some W_55f0ac.
Proof. vm_refl. Qed.
Lemma D_55f0ac : decode_any W_55f0ac = Some (Store SZ4 11 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_55f0b0 : bv 32 := 0x00e586b3.
Lemma F_55f0b0 : fetch_word Asan.M.loaded_segments (0x526980 : word) = Some W_55f0b0.
Proof. vm_refl. Qed.
Lemma D_55f0b0 : decode_any W_55f0b0 = Some (Op ALU_ADD 13 11 14, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_55f0b4 : bv 32 := 0xfec6ae23.
Lemma F_55f0b4 : fetch_word Asan.M.loaded_segments (0x526984 : word) = Some W_55f0b4.
Proof. vm_refl. Qed.
Lemma D_55f0b4 : decode_any W_55f0b4 = Some (Store SZ4 13 12 4092, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_55f0b8 : bv 32 := 0x08f76063.
Lemma F_55f0b8 : fetch_word Asan.M.loaded_segments (0x526988 : word) = Some W_55f0b8.
Proof. vm_refl. Qed.
Lemma D_55f0b8 : decode_any W_55f0b8 = Some (Branch BC_LTU 14 15 128, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_55f0bc : bv 32 := 0x00c5a223.
Lemma F_55f0bc : fetch_word Asan.M.loaded_segments (0x52698c : word) = Some W_55f0bc.
Proof. vm_refl. Qed.
Lemma D_55f0bc : decode_any W_55f0bc = Some (Store SZ4 11 12 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_55f0c0 : bv 32 := 0x00c5a423.
Lemma F_55f0c0 : fetch_word Asan.M.loaded_segments (0x526990 : word) = Some W_55f0c0.
Proof. vm_refl. Qed.
Lemma D_55f0c0 : decode_any W_55f0c0 = Some (Store SZ4 11 12 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_55f0c4 : bv 32 := 0x01900793.
Lemma F_55f0c4 : fetch_word Asan.M.loaded_segments (0x526994 : word) = Some W_55f0c4.
Proof. vm_refl. Qed.
Lemma D_55f0c4 : decode_any W_55f0c4 = Some (OpImm ALU_ADD 15 0 25, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_55f0c8 : bv 32 := 0xfec6aa23.
Lemma F_55f0c8 : fetch_word Asan.M.loaded_segments (0x526998 : word) = Some W_55f0c8.
Proof. vm_refl. Qed.
Lemma D_55f0c8 : decode_any W_55f0c8 = Some (Store SZ4 13 12 4084, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_55f0cc : bv 32 := 0xfec6ac23.
Lemma F_55f0cc : fetch_word Asan.M.loaded_segments (0x52699c : word) = Some W_55f0cc.
Proof. vm_refl. Qed.
Lemma D_55f0cc : decode_any W_55f0cc = Some (Store SZ4 13 12 4088, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_55f0d0 : bv 32 := 0x06f76463.
Lemma F_55f0d0 : fetch_word Asan.M.loaded_segments (0x5269a0 : word) = Some W_55f0d0.
Proof. vm_refl. Qed.
Lemma D_55f0d0 : decode_any W_55f0d0 = Some (Branch BC_LTU 14 15 104, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_55f0d4 : bv 32 := 0x00c5a623.
Lemma F_55f0d4 : fetch_word Asan.M.loaded_segments (0x5269a4 : word) = Some W_55f0d4.
Proof. vm_refl. Qed.
Lemma D_55f0d4 : decode_any W_55f0d4 = Some (Store SZ4 11 12 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_55f0d8 : bv 32 := 0x00c5a823.
Lemma F_55f0d8 : fetch_word Asan.M.loaded_segments (0x5269a8 : word) = Some W_55f0d8.
Proof. vm_refl. Qed.
Lemma D_55f0d8 : decode_any W_55f0d8 = Some (Store SZ4 11 12 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_55f0dc : bv 32 := 0x00c5aa23.
Lemma F_55f0dc : fetch_word Asan.M.loaded_segments (0x5269ac : word) = Some W_55f0dc.
Proof. vm_refl. Qed.
Lemma D_55f0dc : decode_any W_55f0dc = Some (Store SZ4 11 12 20, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_55f0e0 : bv 32 := 0x00c5ac23.
Lemma F_55f0e0 : fetch_word Asan.M.loaded_segments (0x5269b0 : word) = Some W_55f0e0.
Proof. vm_refl. Qed.
Lemma D_55f0e0 : decode_any W_55f0e0 = Some (Store SZ4 11 12 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_55f0e4 : bv 32 := 0x0045f793.
Lemma F_55f0e4 : fetch_word Asan.M.loaded_segments (0x5269b4 : word) = Some W_55f0e4.
Proof. vm_refl. Qed.
Lemma D_55f0e4 : decode_any W_55f0e4 = Some (OpImm ALU_AND 15 11 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_55f0e8 : bv 32 := 0x02000813.
Lemma F_55f0e8 : fetch_word Asan.M.loaded_segments (0x5269b8 : word) = Some W_55f0e8.
Proof. vm_refl. Qed.
Lemma D_55f0e8 : decode_any W_55f0e8 = Some (OpImm ALU_ADD 16 0 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_55f0ec : bv 32 := 0x01878793.
Lemma F_55f0ec : fetch_word Asan.M.loaded_segments (0x5269bc : word) = Some W_55f0ec.
Proof. vm_refl. Qed.
Lemma D_55f0ec : decode_any W_55f0ec = Some (OpImm ALU_ADD 15 15 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_55f0f0 : bv 32 := 0x40f70733.
Lemma F_55f0f0 : fetch_word Asan.M.loaded_segments (0x5269c0 : word) = Some W_55f0f0.
Proof. vm_refl. Qed.
Lemma D_55f0f0 : decode_any W_55f0f0 = Some (Op ALU_SUB 14 14 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_55f0f4 : bv 32 := 0xfec6a223.
Lemma F_55f0f4 : fetch_word Asan.M.loaded_segments (0x5269c4 : word) = Some W_55f0f4.
Proof. vm_refl. Qed.
Lemma D_55f0f4 : decode_any W_55f0f4 = Some (Store SZ4 13 12 4068, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_55f0f8 : bv 32 := 0xfec6a423.
Lemma F_55f0f8 : fetch_word Asan.M.loaded_segments (0x5269c8 : word) = Some W_55f0f8.
Proof. vm_refl. Qed.
Lemma D_55f0f8 : decode_any W_55f0f8 = Some (Store SZ4 13 12 4072, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_55f0fc : bv 32 := 0xfec6a623.
Lemma F_55f0fc : fetch_word Asan.M.loaded_segments (0x5269cc : word) = Some W_55f0fc.
Proof. vm_refl. Qed.
Lemma D_55f0fc : decode_any W_55f0fc = Some (Store SZ4 13 12 4076, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_55f100 : bv 32 := 0xfec6a823.
Lemma F_55f100 : fetch_word Asan.M.loaded_segments (0x5269d0 : word) = Some W_55f100.
Proof. vm_refl. Qed.
Lemma D_55f100 : decode_any W_55f100 = Some (Store SZ4 13 12 4080, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_55f104 : bv 32 := 0x03076a63.
Lemma F_55f104 : fetch_word Asan.M.loaded_segments (0x5269d4 : word) = Some W_55f104.
Proof. vm_refl. Qed.
Lemma D_55f104 : decode_any W_55f104 = Some (Branch BC_LTU 14 16 52, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_55f108 : bv 32 := 0x02061613.
Lemma F_55f108 : fetch_word Asan.M.loaded_segments (0x5269d8 : word) = Some W_55f108.
Proof. vm_refl. Qed.
Lemma D_55f108 : decode_any W_55f108 = Some (ShiftImm ALU_SLL 12 12 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_55f10c : bv 32 := 0x00f585b3.
Lemma F_55f10c : fetch_word Asan.M.loaded_segments (0x5269dc : word) = Some W_55f10c.
Proof. vm_refl. Qed.
Lemma D_55f10c : decode_any W_55f10c = Some (Op ALU_ADD 11 11 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_55f110 : bv 32 := 0x02065693.
Lemma F_55f110 : fetch_word Asan.M.loaded_segments (0x5269e0 : word) = Some W_55f110.
Proof. vm_refl. Qed.
Lemma D_55f110 : decode_any W_55f110 = Some (ShiftImm ALU_SRL 13 12 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_55f114 : bv 32 := 0x00d66633.
Lemma F_55f114 : fetch_word Asan.M.loaded_segments (0x5269e4 : word) = Some W_55f114.
Proof. vm_refl. Qed.
Lemma D_55f114 : decode_any W_55f114 = Some (Op ALU_OR 12 12 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_55f118 : bv 32 := 0x01f00693.
Lemma F_55f118 : fetch_word Asan.M.loaded_segments (0x5269e8 : word) = Some W_55f118.
Proof. vm_refl. Qed.
Lemma D_55f118 : decode_any W_55f118 = Some (OpImm ALU_ADD 13 0 31, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_55f11c : bv 32 := 0x00c5b023.
Lemma F_55f11c : fetch_word Asan.M.loaded_segments (0x5269ec : word) = Some W_55f11c.
Proof. vm_refl. Qed.
Lemma D_55f11c : decode_any W_55f11c = Some (Store SZ8 11 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_55f120 : bv 32 := 0x00c5b423.
Lemma F_55f120 : fetch_word Asan.M.loaded_segments (0x5269f0 : word) = Some W_55f120.
Proof. vm_refl. Qed.
Lemma D_55f120 : decode_any W_55f120 = Some (Store SZ8 11 12 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_55f124 : bv 32 := 0x00c5b823.
Lemma F_55f124 : fetch_word Asan.M.loaded_segments (0x5269f4 : word) = Some W_55f124.
Proof. vm_refl. Qed.
Lemma D_55f124 : decode_any W_55f124 = Some (Store SZ8 11 12 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_55f128 : bv 32 := 0x00c5bc23.
Lemma F_55f128 : fetch_word Asan.M.loaded_segments (0x5269f8 : word) = Some W_55f128.
Proof. vm_refl. Qed.
Lemma D_55f128 : decode_any W_55f128 = Some (Store SZ8 11 12 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_55f12c : bv 32 := 0xfe070713.
Lemma F_55f12c : fetch_word Asan.M.loaded_segments (0x5269fc : word) = Some W_55f12c.
Proof. vm_refl. Qed.
Lemma D_55f12c : decode_any W_55f12c = Some (OpImm ALU_ADD 14 14 4064, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_55f130 : bv 32 := 0x02058593.
Lemma F_55f130 : fetch_word Asan.M.loaded_segments (0x526a00 : word) = Some W_55f130.
Proof. vm_refl. Qed.
Lemma D_55f130 : decode_any W_55f130 = Some (OpImm ALU_ADD 11 11 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_55f134 : bv 32 := 0xfee6e4e3.
Lemma F_55f134 : fetch_word Asan.M.loaded_segments (0x526a04 : word) = Some W_55f134.
Proof. vm_refl. Qed.
Lemma D_55f134 : decode_any W_55f134 = Some (Branch BC_LTU 13 14 8168, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_55f138 : bv 32 := 0x00008067.
Lemma F_55f138 : fetch_word Asan.M.loaded_segments (0x526a08 : word) = Some W_55f138.
Proof. vm_refl. Qed.
Lemma D_55f138 : decode_any W_55f138 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Abbreviation MSEGS := Asan.M.loaded_segments.
Definition ms_base : Z := 0x526914%Z.
Definition Fo_000 := F_55f044.
Definition Do_000 := D_55f044.
Definition Fo_004 := F_55f048.
Definition Do_004 := D_55f048.
Definition Fo_008 := F_55f04c.
Definition Do_008 := D_55f04c.
Definition Fo_00c := F_55f050.
Definition Do_00c := D_55f050.
Definition Fo_010 := F_55f054.
Definition Do_010 := D_55f054.
Definition Fo_014 := F_55f058.
Definition Do_014 := D_55f058.
Definition Fo_018 := F_55f05c.
Definition Do_018 := D_55f05c.
Definition Fo_01c := F_55f060.
Definition Do_01c := D_55f060.
Definition Fo_020 := F_55f064.
Definition Do_020 := D_55f064.
Definition Fo_024 := F_55f068.
Definition Do_024 := D_55f068.
Definition Fo_028 := F_55f06c.
Definition Do_028 := D_55f06c.
Definition Fo_02c := F_55f070.
Definition Do_02c := D_55f070.
Definition Fo_030 := F_55f074.
Definition Do_030 := D_55f074.
Definition Fo_034 := F_55f078.
Definition Do_034 := D_55f078.
Definition Fo_038 := F_55f07c.
Definition Do_038 := D_55f07c.
Definition Fo_03c := F_55f080.
Definition Do_03c := D_55f080.
Definition Fo_040 := F_55f084.
Definition Do_040 := D_55f084.
Definition Fo_044 := F_55f088.
Definition Do_044 := D_55f088.
Definition Fo_048 := F_55f08c.
Definition Do_048 := D_55f08c.
Definition Fo_04c := F_55f090.
Definition Do_04c := D_55f090.
Definition Fo_050 := F_55f094.
Definition Do_050 := D_55f094.
Definition Fo_054 := F_55f098.
Definition Do_054 := D_55f098.
Definition Fo_058 := F_55f09c.
Definition Do_058 := D_55f09c.
Definition Fo_05c := F_55f0a0.
Definition Do_05c := D_55f0a0.
Definition Fo_060 := F_55f0a4.
Definition Do_060 := D_55f0a4.
Definition Fo_064 := F_55f0a8.
Definition Do_064 := D_55f0a8.
Definition Fo_068 := F_55f0ac.
Definition Do_068 := D_55f0ac.
Definition Fo_06c := F_55f0b0.
Definition Do_06c := D_55f0b0.
Definition Fo_070 := F_55f0b4.
Definition Do_070 := D_55f0b4.
Definition Fo_074 := F_55f0b8.
Definition Do_074 := D_55f0b8.
Definition Fo_078 := F_55f0bc.
Definition Do_078 := D_55f0bc.
Definition Fo_07c := F_55f0c0.
Definition Do_07c := D_55f0c0.
Definition Fo_080 := F_55f0c4.
Definition Do_080 := D_55f0c4.
Definition Fo_084 := F_55f0c8.
Definition Do_084 := D_55f0c8.
Definition Fo_088 := F_55f0cc.
Definition Do_088 := D_55f0cc.
Definition Fo_08c := F_55f0d0.
Definition Do_08c := D_55f0d0.
Definition Fo_090 := F_55f0d4.
Definition Do_090 := D_55f0d4.
Definition Fo_094 := F_55f0d8.
Definition Do_094 := D_55f0d8.
Definition Fo_098 := F_55f0dc.
Definition Do_098 := D_55f0dc.
Definition Fo_09c := F_55f0e0.
Definition Do_09c := D_55f0e0.
Definition Fo_0a0 := F_55f0e4.
Definition Do_0a0 := D_55f0e4.
Definition Fo_0a4 := F_55f0e8.
Definition Do_0a4 := D_55f0e8.
Definition Fo_0a8 := F_55f0ec.
Definition Do_0a8 := D_55f0ec.
Definition Fo_0ac := F_55f0f0.
Definition Do_0ac := D_55f0f0.
Definition Fo_0b0 := F_55f0f4.
Definition Do_0b0 := D_55f0f4.
Definition Fo_0b4 := F_55f0f8.
Definition Do_0b4 := D_55f0f8.
Definition Fo_0b8 := F_55f0fc.
Definition Do_0b8 := D_55f0fc.
Definition Fo_0bc := F_55f100.
Definition Do_0bc := D_55f100.
Definition Fo_0c0 := F_55f104.
Definition Do_0c0 := D_55f104.
Definition Fo_0c4 := F_55f108.
Definition Do_0c4 := D_55f108.
Definition Fo_0c8 := F_55f10c.
Definition Do_0c8 := D_55f10c.
Definition Fo_0cc := F_55f110.
Definition Do_0cc := D_55f110.
Definition Fo_0d0 := F_55f114.
Definition Do_0d0 := D_55f114.
Definition Fo_0d4 := F_55f118.
Definition Do_0d4 := D_55f118.
Definition Fo_0d8 := F_55f11c.
Definition Do_0d8 := D_55f11c.
Definition Fo_0dc := F_55f120.
Definition Do_0dc := D_55f120.
Definition Fo_0e0 := F_55f124.
Definition Do_0e0 := D_55f124.
Definition Fo_0e4 := F_55f128.
Definition Do_0e4 := D_55f128.
Definition Fo_0e8 := F_55f12c.
Definition Do_0e8 := D_55f12c.
Definition Fo_0ec := F_55f130.
Definition Do_0ec := D_55f130.
Definition Fo_0f0 := F_55f134.
Definition Do_0f0 := D_55f134.
Definition Fo_0f4 := F_55f138.
Definition Do_0f4 := D_55f138.
