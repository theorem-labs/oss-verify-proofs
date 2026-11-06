(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.openssl.punycode.images Require Import Asan.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.

(* [comment removed for export] *)
Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

(* [comment removed for export] *)
Definition W_52a8b8 : bv 32 := 0x0e060a63.
Lemma F_52a8b8 : fetch_word Asan.M.loaded_segments (0x52a8ec : word) = Some W_52a8b8.
Proof. vm_refl. Qed.
Lemma D_52a8b8 : decode_any W_52a8b8 = Some (Branch BC_EQ 12 0 244, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52a8bc : bv 32 := 0x00b50023.
Lemma F_52a8bc : fetch_word Asan.M.loaded_segments (0x52a8f0 : word) = Some W_52a8bc.
Proof. vm_refl. Qed.
Lemma D_52a8bc : decode_any W_52a8bc = Some (Store SZ1 10 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52a8c0 : bv 32 := 0x00c506b3.
Lemma F_52a8c0 : fetch_word Asan.M.loaded_segments (0x52a8f4 : word) = Some W_52a8c0.
Proof. vm_refl. Qed.
Lemma D_52a8c0 : decode_any W_52a8c0 = Some (Op ALU_ADD 13 10 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52a8c4 : bv 32 := 0x00300713.
Lemma F_52a8c4 : fetch_word Asan.M.loaded_segments (0x52a8f8 : word) = Some W_52a8c4.
Proof. vm_refl. Qed.
Lemma D_52a8c4 : decode_any W_52a8c4 = Some (OpImm ALU_ADD 14 0 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52a8c8 : bv 32 := 0xfeb68fa3.
Lemma F_52a8c8 : fetch_word Asan.M.loaded_segments (0x52a8fc : word) = Some W_52a8c8.
Proof. vm_refl. Qed.
Lemma D_52a8c8 : decode_any W_52a8c8 = Some (Store SZ1 13 11 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52a8cc : bv 32 := 0x0ee66063.
Lemma F_52a8cc : fetch_word Asan.M.loaded_segments (0x52a900 : word) = Some W_52a8cc.
Proof. vm_refl. Qed.
Lemma D_52a8cc : decode_any W_52a8cc = Some (Branch BC_LTU 12 14 224, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52a8d0 : bv 32 := 0x00b500a3.
Lemma F_52a8d0 : fetch_word Asan.M.loaded_segments (0x52a904 : word) = Some W_52a8d0.
Proof. vm_refl. Qed.
Lemma D_52a8d0 : decode_any W_52a8d0 = Some (Store SZ1 10 11 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52a8d4 : bv 32 := 0x00b50123.
Lemma F_52a8d4 : fetch_word Asan.M.loaded_segments (0x52a908 : word) = Some W_52a8d4.
Proof. vm_refl. Qed.
Lemma D_52a8d4 : decode_any W_52a8d4 = Some (Store SZ1 10 11 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52a8d8 : bv 32 := 0x00700713.
Lemma F_52a8d8 : fetch_word Asan.M.loaded_segments (0x52a90c : word) = Some W_52a8d8.
Proof. vm_refl. Qed.
Lemma D_52a8d8 : decode_any W_52a8d8 = Some (OpImm ALU_ADD 14 0 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52a8dc : bv 32 := 0xfeb68ea3.
Lemma F_52a8dc : fetch_word Asan.M.loaded_segments (0x52a910 : word) = Some W_52a8dc.
Proof. vm_refl. Qed.
Lemma D_52a8dc : decode_any W_52a8dc = Some (Store SZ1 13 11 4093, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52a8e0 : bv 32 := 0xfeb68f23.
Lemma F_52a8e0 : fetch_word Asan.M.loaded_segments (0x52a914 : word) = Some W_52a8e0.
Proof. vm_refl. Qed.
Lemma D_52a8e0 : decode_any W_52a8e0 = Some (Store SZ1 13 11 4094, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52a8e4 : bv 32 := 0x0ce66463.
Lemma F_52a8e4 : fetch_word Asan.M.loaded_segments (0x52a918 : word) = Some W_52a8e4.
Proof. vm_refl. Qed.
Lemma D_52a8e4 : decode_any W_52a8e4 = Some (Branch BC_LTU 12 14 200, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52a8e8 : bv 32 := 0x00b501a3.
Lemma F_52a8e8 : fetch_word Asan.M.loaded_segments (0x52a91c : word) = Some W_52a8e8.
Proof. vm_refl. Qed.
Lemma D_52a8e8 : decode_any W_52a8e8 = Some (Store SZ1 10 11 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52a8ec : bv 32 := 0x00900793.
Lemma F_52a8ec : fetch_word Asan.M.loaded_segments (0x52a920 : word) = Some W_52a8ec.
Proof. vm_refl. Qed.
Lemma D_52a8ec : decode_any W_52a8ec = Some (OpImm ALU_ADD 15 0 9, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52a8f0 : bv 32 := 0xfeb68e23.
Lemma F_52a8f0 : fetch_word Asan.M.loaded_segments (0x52a924 : word) = Some W_52a8f0.
Proof. vm_refl. Qed.
Lemma D_52a8f0 : decode_any W_52a8f0 = Some (Store SZ1 13 11 4092, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52a8f4 : bv 32 := 0x0af66c63.
Lemma F_52a8f4 : fetch_word Asan.M.loaded_segments (0x52a928 : word) = Some W_52a8f4.
Proof. vm_refl. Qed.
Lemma D_52a8f4 : decode_any W_52a8f4 = Some (Branch BC_LTU 12 15 184, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52a8f8 : bv 32 := 0x40a006bb.
Lemma F_52a8f8 : fetch_word Asan.M.loaded_segments (0x52a92c : word) = Some W_52a8f8.
Proof. vm_refl. Qed.
Lemma D_52a8f8 : decode_any W_52a8f8 = Some (Op32 ALU_SUB 13 0 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52a8fc : bv 32 := 0x03859813.
Lemma F_52a8fc : fetch_word Asan.M.loaded_segments (0x52a930 : word) = Some W_52a8fc.
Proof. vm_refl. Qed.
Lemma D_52a8fc : decode_any W_52a8fc = Some (ShiftImm ALU_SLL 16 11 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52a900 : bv 32 := 0x101015b7.
Lemma F_52a900 : fetch_word Asan.M.loaded_segments (0x52a934 : word) = Some W_52a900.
Proof. vm_refl. Qed.
Lemma D_52a900 : decode_any W_52a900 = Some (Lui 11 65793, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52a904 : bv 32 := 0x0036f693.
Lemma F_52a904 : fetch_word Asan.M.loaded_segments (0x52a938 : word) = Some W_52a904.
Proof. vm_refl. Qed.
Lemma D_52a904 : decode_any W_52a904 = Some (OpImm ALU_AND 13 13 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52a908 : bv 32 := 0x00459713.
Lemma F_52a908 : fetch_word Asan.M.loaded_segments (0x52a93c : word) = Some W_52a908.
Proof. vm_refl. Qed.
Lemma D_52a908 : decode_any W_52a908 = Some (ShiftImm ALU_SLL 14 11 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52a90c : bv 32 := 0x40d60633.
Lemma F_52a90c : fetch_word Asan.M.loaded_segments (0x52a940 : word) = Some W_52a90c.
Proof. vm_refl. Qed.
Lemma D_52a90c : decode_any W_52a90c = Some (Op ALU_SUB 12 12 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52a910 : bv 32 := 0x00d505b3.
Lemma F_52a910 : fetch_word Asan.M.loaded_segments (0x52a944 : word) = Some W_52a910.
Proof. vm_refl. Qed.
Lemma D_52a910 : decode_any W_52a910 = Some (Op ALU_ADD 11 10 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52a914 : bv 32 := 0x10070693.
Lemma F_52a914 : fetch_word Asan.M.loaded_segments (0x52a948 : word) = Some W_52a914.
Proof. vm_refl. Qed.
Lemma D_52a914 : decode_any W_52a914 = Some (OpImm ALU_ADD 13 14 256, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52a918 : bv 32 := 0xffc67713.
Lemma F_52a918 : fetch_word Asan.M.loaded_segments (0x52a94c : word) = Some W_52a918.
Proof. vm_refl. Qed.
Lemma D_52a918 : decode_any W_52a918 = Some (OpImm ALU_AND 14 12 4092, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52a91c : bv 32 := 0x02d83633.
Lemma F_52a91c : fetch_word Asan.M.loaded_segments (0x52a950 : word) = Some W_52a91c.
Proof. vm_refl. Qed.
Lemma D_52a91c : decode_any W_52a91c = Some (Mul M_MULHU 12 16 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52a920 : bv 32 := 0x00c5a023.
Lemma F_52a920 : fetch_word Asan.M.loaded_segments (0x52a954 : word) = Some W_52a920.
Proof. vm_refl. Qed.
Lemma D_52a920 : decode_any W_52a920 = Some (Store SZ4 11 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52a924 : bv 32 := 0x00e586b3.
Lemma F_52a924 : fetch_word Asan.M.loaded_segments (0x52a958 : word) = Some W_52a924.
Proof. vm_refl. Qed.
Lemma D_52a924 : decode_any W_52a924 = Some (Op ALU_ADD 13 11 14, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52a928 : bv 32 := 0xfec6ae23.
Lemma F_52a928 : fetch_word Asan.M.loaded_segments (0x52a95c : word) = Some W_52a928.
Proof. vm_refl. Qed.
Lemma D_52a928 : decode_any W_52a928 = Some (Store SZ4 13 12 4092, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52a92c : bv 32 := 0x08f76063.
Lemma F_52a92c : fetch_word Asan.M.loaded_segments (0x52a960 : word) = Some W_52a92c.
Proof. vm_refl. Qed.
Lemma D_52a92c : decode_any W_52a92c = Some (Branch BC_LTU 14 15 128, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52a930 : bv 32 := 0x00c5a223.
Lemma F_52a930 : fetch_word Asan.M.loaded_segments (0x52a964 : word) = Some W_52a930.
Proof. vm_refl. Qed.
Lemma D_52a930 : decode_any W_52a930 = Some (Store SZ4 11 12 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52a934 : bv 32 := 0x00c5a423.
Lemma F_52a934 : fetch_word Asan.M.loaded_segments (0x52a968 : word) = Some W_52a934.
Proof. vm_refl. Qed.
Lemma D_52a934 : decode_any W_52a934 = Some (Store SZ4 11 12 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52a938 : bv 32 := 0x01900793.
Lemma F_52a938 : fetch_word Asan.M.loaded_segments (0x52a96c : word) = Some W_52a938.
Proof. vm_refl. Qed.
Lemma D_52a938 : decode_any W_52a938 = Some (OpImm ALU_ADD 15 0 25, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52a93c : bv 32 := 0xfec6aa23.
Lemma F_52a93c : fetch_word Asan.M.loaded_segments (0x52a970 : word) = Some W_52a93c.
Proof. vm_refl. Qed.
Lemma D_52a93c : decode_any W_52a93c = Some (Store SZ4 13 12 4084, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52a940 : bv 32 := 0xfec6ac23.
Lemma F_52a940 : fetch_word Asan.M.loaded_segments (0x52a974 : word) = Some W_52a940.
Proof. vm_refl. Qed.
Lemma D_52a940 : decode_any W_52a940 = Some (Store SZ4 13 12 4088, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52a944 : bv 32 := 0x06f76463.
Lemma F_52a944 : fetch_word Asan.M.loaded_segments (0x52a978 : word) = Some W_52a944.
Proof. vm_refl. Qed.
Lemma D_52a944 : decode_any W_52a944 = Some (Branch BC_LTU 14 15 104, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52a948 : bv 32 := 0x00c5a623.
Lemma F_52a948 : fetch_word Asan.M.loaded_segments (0x52a97c : word) = Some W_52a948.
Proof. vm_refl. Qed.
Lemma D_52a948 : decode_any W_52a948 = Some (Store SZ4 11 12 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52a94c : bv 32 := 0x00c5a823.
Lemma F_52a94c : fetch_word Asan.M.loaded_segments (0x52a980 : word) = Some W_52a94c.
Proof. vm_refl. Qed.
Lemma D_52a94c : decode_any W_52a94c = Some (Store SZ4 11 12 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52a950 : bv 32 := 0x00c5aa23.
Lemma F_52a950 : fetch_word Asan.M.loaded_segments (0x52a984 : word) = Some W_52a950.
Proof. vm_refl. Qed.
Lemma D_52a950 : decode_any W_52a950 = Some (Store SZ4 11 12 20, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52a954 : bv 32 := 0x00c5ac23.
Lemma F_52a954 : fetch_word Asan.M.loaded_segments (0x52a988 : word) = Some W_52a954.
Proof. vm_refl. Qed.
Lemma D_52a954 : decode_any W_52a954 = Some (Store SZ4 11 12 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52a958 : bv 32 := 0x0045f793.
Lemma F_52a958 : fetch_word Asan.M.loaded_segments (0x52a98c : word) = Some W_52a958.
Proof. vm_refl. Qed.
Lemma D_52a958 : decode_any W_52a958 = Some (OpImm ALU_AND 15 11 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52a95c : bv 32 := 0x02000813.
Lemma F_52a95c : fetch_word Asan.M.loaded_segments (0x52a990 : word) = Some W_52a95c.
Proof. vm_refl. Qed.
Lemma D_52a95c : decode_any W_52a95c = Some (OpImm ALU_ADD 16 0 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52a960 : bv 32 := 0x01878793.
Lemma F_52a960 : fetch_word Asan.M.loaded_segments (0x52a994 : word) = Some W_52a960.
Proof. vm_refl. Qed.
Lemma D_52a960 : decode_any W_52a960 = Some (OpImm ALU_ADD 15 15 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52a964 : bv 32 := 0x40f70733.
Lemma F_52a964 : fetch_word Asan.M.loaded_segments (0x52a998 : word) = Some W_52a964.
Proof. vm_refl. Qed.
Lemma D_52a964 : decode_any W_52a964 = Some (Op ALU_SUB 14 14 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52a968 : bv 32 := 0xfec6a223.
Lemma F_52a968 : fetch_word Asan.M.loaded_segments (0x52a99c : word) = Some W_52a968.
Proof. vm_refl. Qed.
Lemma D_52a968 : decode_any W_52a968 = Some (Store SZ4 13 12 4068, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52a96c : bv 32 := 0xfec6a423.
Lemma F_52a96c : fetch_word Asan.M.loaded_segments (0x52a9a0 : word) = Some W_52a96c.
Proof. vm_refl. Qed.
Lemma D_52a96c : decode_any W_52a96c = Some (Store SZ4 13 12 4072, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52a970 : bv 32 := 0xfec6a623.
Lemma F_52a970 : fetch_word Asan.M.loaded_segments (0x52a9a4 : word) = Some W_52a970.
Proof. vm_refl. Qed.
Lemma D_52a970 : decode_any W_52a970 = Some (Store SZ4 13 12 4076, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52a974 : bv 32 := 0xfec6a823.
Lemma F_52a974 : fetch_word Asan.M.loaded_segments (0x52a9a8 : word) = Some W_52a974.
Proof. vm_refl. Qed.
Lemma D_52a974 : decode_any W_52a974 = Some (Store SZ4 13 12 4080, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52a978 : bv 32 := 0x03076a63.
Lemma F_52a978 : fetch_word Asan.M.loaded_segments (0x52a9ac : word) = Some W_52a978.
Proof. vm_refl. Qed.
Lemma D_52a978 : decode_any W_52a978 = Some (Branch BC_LTU 14 16 52, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52a97c : bv 32 := 0x02061613.
Lemma F_52a97c : fetch_word Asan.M.loaded_segments (0x52a9b0 : word) = Some W_52a97c.
Proof. vm_refl. Qed.
Lemma D_52a97c : decode_any W_52a97c = Some (ShiftImm ALU_SLL 12 12 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52a980 : bv 32 := 0x00f585b3.
Lemma F_52a980 : fetch_word Asan.M.loaded_segments (0x52a9b4 : word) = Some W_52a980.
Proof. vm_refl. Qed.
Lemma D_52a980 : decode_any W_52a980 = Some (Op ALU_ADD 11 11 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52a984 : bv 32 := 0x02065693.
Lemma F_52a984 : fetch_word Asan.M.loaded_segments (0x52a9b8 : word) = Some W_52a984.
Proof. vm_refl. Qed.
Lemma D_52a984 : decode_any W_52a984 = Some (ShiftImm ALU_SRL 13 12 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52a988 : bv 32 := 0x00d66633.
Lemma F_52a988 : fetch_word Asan.M.loaded_segments (0x52a9bc : word) = Some W_52a988.
Proof. vm_refl. Qed.
Lemma D_52a988 : decode_any W_52a988 = Some (Op ALU_OR 12 12 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52a98c : bv 32 := 0x01f00693.
Lemma F_52a98c : fetch_word Asan.M.loaded_segments (0x52a9c0 : word) = Some W_52a98c.
Proof. vm_refl. Qed.
Lemma D_52a98c : decode_any W_52a98c = Some (OpImm ALU_ADD 13 0 31, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52a990 : bv 32 := 0x00c5b023.
Lemma F_52a990 : fetch_word Asan.M.loaded_segments (0x52a9c4 : word) = Some W_52a990.
Proof. vm_refl. Qed.
Lemma D_52a990 : decode_any W_52a990 = Some (Store SZ8 11 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52a994 : bv 32 := 0x00c5b423.
Lemma F_52a994 : fetch_word Asan.M.loaded_segments (0x52a9c8 : word) = Some W_52a994.
Proof. vm_refl. Qed.
Lemma D_52a994 : decode_any W_52a994 = Some (Store SZ8 11 12 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52a998 : bv 32 := 0x00c5b823.
Lemma F_52a998 : fetch_word Asan.M.loaded_segments (0x52a9cc : word) = Some W_52a998.
Proof. vm_refl. Qed.
Lemma D_52a998 : decode_any W_52a998 = Some (Store SZ8 11 12 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52a99c : bv 32 := 0x00c5bc23.
Lemma F_52a99c : fetch_word Asan.M.loaded_segments (0x52a9d0 : word) = Some W_52a99c.
Proof. vm_refl. Qed.
Lemma D_52a99c : decode_any W_52a99c = Some (Store SZ8 11 12 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52a9a0 : bv 32 := 0xfe070713.
Lemma F_52a9a0 : fetch_word Asan.M.loaded_segments (0x52a9d4 : word) = Some W_52a9a0.
Proof. vm_refl. Qed.
Lemma D_52a9a0 : decode_any W_52a9a0 = Some (OpImm ALU_ADD 14 14 4064, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52a9a4 : bv 32 := 0x02058593.
Lemma F_52a9a4 : fetch_word Asan.M.loaded_segments (0x52a9d8 : word) = Some W_52a9a4.
Proof. vm_refl. Qed.
Lemma D_52a9a4 : decode_any W_52a9a4 = Some (OpImm ALU_ADD 11 11 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52a9a8 : bv 32 := 0xfee6e4e3.
Lemma F_52a9a8 : fetch_word Asan.M.loaded_segments (0x52a9dc : word) = Some W_52a9a8.
Proof. vm_refl. Qed.
Lemma D_52a9a8 : decode_any W_52a9a8 = Some (Branch BC_LTU 13 14 8168, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52a9ac : bv 32 := 0x00008067.
Lemma F_52a9ac : fetch_word Asan.M.loaded_segments (0x52a9e0 : word) = Some W_52a9ac.
Proof. vm_refl. Qed.
Lemma D_52a9ac : decode_any W_52a9ac = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Abbreviation MSEGS := Asan.M.loaded_segments.
Definition ms_base : Z := 0x52a8ec%Z.
Definition Fo_000 := F_52a8b8.
Definition Do_000 := D_52a8b8.
Definition Fo_004 := F_52a8bc.
Definition Do_004 := D_52a8bc.
Definition Fo_008 := F_52a8c0.
Definition Do_008 := D_52a8c0.
Definition Fo_00c := F_52a8c4.
Definition Do_00c := D_52a8c4.
Definition Fo_010 := F_52a8c8.
Definition Do_010 := D_52a8c8.
Definition Fo_014 := F_52a8cc.
Definition Do_014 := D_52a8cc.
Definition Fo_018 := F_52a8d0.
Definition Do_018 := D_52a8d0.
Definition Fo_01c := F_52a8d4.
Definition Do_01c := D_52a8d4.
Definition Fo_020 := F_52a8d8.
Definition Do_020 := D_52a8d8.
Definition Fo_024 := F_52a8dc.
Definition Do_024 := D_52a8dc.
Definition Fo_028 := F_52a8e0.
Definition Do_028 := D_52a8e0.
Definition Fo_02c := F_52a8e4.
Definition Do_02c := D_52a8e4.
Definition Fo_030 := F_52a8e8.
Definition Do_030 := D_52a8e8.
Definition Fo_034 := F_52a8ec.
Definition Do_034 := D_52a8ec.
Definition Fo_038 := F_52a8f0.
Definition Do_038 := D_52a8f0.
Definition Fo_03c := F_52a8f4.
Definition Do_03c := D_52a8f4.
Definition Fo_040 := F_52a8f8.
Definition Do_040 := D_52a8f8.
Definition Fo_044 := F_52a8fc.
Definition Do_044 := D_52a8fc.
Definition Fo_048 := F_52a900.
Definition Do_048 := D_52a900.
Definition Fo_04c := F_52a904.
Definition Do_04c := D_52a904.
Definition Fo_050 := F_52a908.
Definition Do_050 := D_52a908.
Definition Fo_054 := F_52a90c.
Definition Do_054 := D_52a90c.
Definition Fo_058 := F_52a910.
Definition Do_058 := D_52a910.
Definition Fo_05c := F_52a914.
Definition Do_05c := D_52a914.
Definition Fo_060 := F_52a918.
Definition Do_060 := D_52a918.
Definition Fo_064 := F_52a91c.
Definition Do_064 := D_52a91c.
Definition Fo_068 := F_52a920.
Definition Do_068 := D_52a920.
Definition Fo_06c := F_52a924.
Definition Do_06c := D_52a924.
Definition Fo_070 := F_52a928.
Definition Do_070 := D_52a928.
Definition Fo_074 := F_52a92c.
Definition Do_074 := D_52a92c.
Definition Fo_078 := F_52a930.
Definition Do_078 := D_52a930.
Definition Fo_07c := F_52a934.
Definition Do_07c := D_52a934.
Definition Fo_080 := F_52a938.
Definition Do_080 := D_52a938.
Definition Fo_084 := F_52a93c.
Definition Do_084 := D_52a93c.
Definition Fo_088 := F_52a940.
Definition Do_088 := D_52a940.
Definition Fo_08c := F_52a944.
Definition Do_08c := D_52a944.
Definition Fo_090 := F_52a948.
Definition Do_090 := D_52a948.
Definition Fo_094 := F_52a94c.
Definition Do_094 := D_52a94c.
Definition Fo_098 := F_52a950.
Definition Do_098 := D_52a950.
Definition Fo_09c := F_52a954.
Definition Do_09c := D_52a954.
Definition Fo_0a0 := F_52a958.
Definition Do_0a0 := D_52a958.
Definition Fo_0a4 := F_52a95c.
Definition Do_0a4 := D_52a95c.
Definition Fo_0a8 := F_52a960.
Definition Do_0a8 := D_52a960.
Definition Fo_0ac := F_52a964.
Definition Do_0ac := D_52a964.
Definition Fo_0b0 := F_52a968.
Definition Do_0b0 := D_52a968.
Definition Fo_0b4 := F_52a96c.
Definition Do_0b4 := D_52a96c.
Definition Fo_0b8 := F_52a970.
Definition Do_0b8 := D_52a970.
Definition Fo_0bc := F_52a974.
Definition Do_0bc := D_52a974.
Definition Fo_0c0 := F_52a978.
Definition Do_0c0 := D_52a978.
Definition Fo_0c4 := F_52a97c.
Definition Do_0c4 := D_52a97c.
Definition Fo_0c8 := F_52a980.
Definition Do_0c8 := D_52a980.
Definition Fo_0cc := F_52a984.
Definition Do_0cc := D_52a984.
Definition Fo_0d0 := F_52a988.
Definition Do_0d0 := D_52a988.
Definition Fo_0d4 := F_52a98c.
Definition Do_0d4 := D_52a98c.
Definition Fo_0d8 := F_52a990.
Definition Do_0d8 := D_52a990.
Definition Fo_0dc := F_52a994.
Definition Do_0dc := D_52a994.
Definition Fo_0e0 := F_52a998.
Definition Do_0e0 := D_52a998.
Definition Fo_0e4 := F_52a99c.
Definition Do_0e4 := D_52a99c.
Definition Fo_0e8 := F_52a9a0.
Definition Do_0e8 := D_52a9a0.
Definition Fo_0ec := F_52a9a4.
Definition Do_0ec := D_52a9a4.
Definition Fo_0f0 := F_52a9a8.
Definition Do_0f0 := D_52a9a8.
Definition Fo_0f4 := F_52a9ac.
Definition Do_0f4 := D_52a9ac.
