(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.simdjson.fuzz_utf8.images Require Import Ubsan.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. (* [comment removed for export] *)
Open Scope bv_scope.

(* [comment removed for export] *)
Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

(* [comment removed for export] *)
Definition W_bf868 : bv 32 := 0x00f57593.
Lemma F_bf868 : fetch_word Ubsan.M.loaded_segments (0xbfa20 : word) = Some W_bf868.
Proof. vm_refl. Qed.
Lemma D_bf868 : decode_any W_bf868 = Some (OpImm ALU_AND 11 10 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_bf86c : bv 32 := 0x00058463.
Lemma F_bf86c : fetch_word Ubsan.M.loaded_segments (0xbfa24 : word) = Some W_bf86c.
Proof. vm_refl. Qed.
Lemma D_bf86c : decode_any W_bf86c = Some (Branch BC_EQ 11 0 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_bf870 : bv 32 := 0x00000023.
Lemma F_bf870 : fetch_word Ubsan.M.loaded_segments (0xbfa28 : word) = Some W_bf870.
Proof. vm_refl. Qed.
Lemma D_bf870 : decode_any W_bf870 = Some (Store SZ1 0 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_bf874 : bv 32 := 0xffc54603.
Lemma F_bf874 : fetch_word Ubsan.M.loaded_segments (0xbfa2c : word) = Some W_bf874.
Proof. vm_refl. Qed.
Lemma D_bf874 : decode_any W_bf874 = Some (Load SZ1 false 12 10 4092, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_bf878 : bv 32 := 0xffd54683.
Lemma F_bf878 : fetch_word Ubsan.M.loaded_segments (0xbfa30 : word) = Some W_bf878.
Proof. vm_refl. Qed.
Lemma D_bf878 : decode_any W_bf878 = Some (Load SZ1 false 13 10 4093, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_bf87c : bv 32 := 0xffe55583.
Lemma F_bf87c : fetch_word Ubsan.M.loaded_segments (0xbfa34 : word) = Some W_bf87c.
Proof. vm_refl. Qed.
Lemma D_bf87c : decode_any W_bf87c = Some (Load SZ2 false 11 10 4094, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_bf880 : bv 32 := 0x00060e63.
Lemma F_bf880 : fetch_word Ubsan.M.loaded_segments (0xbfa38 : word) = Some W_bf880.
Proof. vm_refl. Qed.
Lemma D_bf880 : decode_any W_bf880 = Some (Branch BC_EQ 12 0 28, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_bf884 : bv 32 := 0x00058463.
Lemma F_bf884 : fetch_word Ubsan.M.loaded_segments (0xbfa3c : word) = Some W_bf884.
Proof. vm_refl. Qed.
Lemma D_bf884 : decode_any W_bf884 = Some (Branch BC_EQ 11 0 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_bf888 : bv 32 := 0x00000023.
Lemma F_bf888 : fetch_word Ubsan.M.loaded_segments (0xbfa40 : word) = Some W_bf888.
Proof. vm_refl. Qed.
Lemma D_bf888 : decode_any W_bf888 = Some (Store SZ1 0 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_bf88c : bv 32 := 0xff856583.
Lemma F_bf88c : fetch_word Ubsan.M.loaded_segments (0xbfa44 : word) = Some W_bf88c.
Proof. vm_refl. Qed.
Lemma D_bf88c : decode_any W_bf88c = Some (Load SZ4 false 11 10 4088, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_bf890 : bv 32 := 0x0105d613.
Lemma F_bf890 : fetch_word Ubsan.M.loaded_segments (0xbfa48 : word) = Some W_bf890.
Proof. vm_refl. Qed.
Lemma D_bf890 : decode_any W_bf890 = Some (ShiftImm ALU_SRL 12 11 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_bf894 : bv 32 := 0x00061463.
Lemma F_bf894 : fetch_word Ubsan.M.loaded_segments (0xbfa4c : word) = Some W_bf894.
Proof. vm_refl. Qed.
Lemma D_bf894 : decode_any W_bf894 = Some (Branch BC_NE 12 0 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_bf898 : bv 32 := 0x00000023.
Lemma F_bf898 : fetch_word Ubsan.M.loaded_segments (0xbfa50 : word) = Some W_bf898.
Proof. vm_refl. Qed.
Lemma D_bf898 : decode_any W_bf898 = Some (Store SZ1 0 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_bf89c : bv 32 := 0x00459613.
Lemma F_bf89c : fetch_word Ubsan.M.loaded_segments (0xbfa54 : word) = Some W_bf89c.
Proof. vm_refl. Qed.
Lemma D_bf89c : decode_any W_bf89c = Some (ShiftImm ALU_SLL 12 11 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_bf8a0 : bv 32 := 0x40c50633.
Lemma F_bf8a0 : fetch_word Ubsan.M.loaded_segments (0xbfa58 : word) = Some W_bf8a0.
Proof. vm_refl. Qed.
Lemma D_bf8a0 : decode_any W_bf8a0 = Some (Op ALU_SUB 12 10 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_bf8a4 : bv 32 := 0xff063503.
Lemma F_bf8a4 : fetch_word Ubsan.M.loaded_segments (0xbfa5c : word) = Some W_bf8a4.
Proof. vm_refl. Qed.
Lemma D_bf8a4 : decode_any W_bf8a4 = Some (Load SZ8 true 10 12 4080, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_bf8a8 : bv 32 := 0x01053703.
Lemma F_bf8a8 : fetch_word Ubsan.M.loaded_segments (0xbfa60 : word) = Some W_bf8a8.
Proof. vm_refl. Qed.
Lemma D_bf8a8 : decode_any W_bf8a8 = Some (Load SZ8 true 14 10 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_bf8ac : bv 32 := 0xff060613.
Lemma F_bf8ac : fetch_word Ubsan.M.loaded_segments (0xbfa64 : word) = Some W_bf8ac.
Proof. vm_refl. Qed.
Lemma D_bf8ac : decode_any W_bf8ac = Some (OpImm ALU_ADD 12 12 4080, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_bf8b0 : bv 32 := 0x01f6f693.
Lemma F_bf8b0 : fetch_word Ubsan.M.loaded_segments (0xbfa68 : word) = Some W_bf8b0.
Proof. vm_refl. Qed.
Lemma D_bf8b0 : decode_any W_bf8b0 = Some (OpImm ALU_AND 13 13 31, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_bf8b4 : bv 32 := 0x00c70463.
Lemma F_bf8b4 : fetch_word Ubsan.M.loaded_segments (0xbfa6c : word) = Some W_bf8b4.
Proof. vm_refl. Qed.
Lemma D_bf8b4 : decode_any W_bf8b4 = Some (Branch BC_EQ 14 12 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_bf8b8 : bv 32 := 0x00000023.
Lemma F_bf8b8 : fetch_word Ubsan.M.loaded_segments (0xbfa70 : word) = Some W_bf8b8.
Proof. vm_refl. Qed.
Lemma D_bf8b8 : decode_any W_bf8b8 = Some (Store SZ1 0 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_bf8bc : bv 32 := 0x02053603.
Lemma F_bf8bc : fetch_word Ubsan.M.loaded_segments (0xbfa74 : word) = Some W_bf8bc.
Proof. vm_refl. Qed.
Lemma D_bf8bc : decode_any W_bf8bc = Some (Load SZ8 true 12 10 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_bf8c0 : bv 32 := 0x01f67713.
Lemma F_bf8c0 : fetch_word Ubsan.M.loaded_segments (0xbfa78 : word) = Some W_bf8c0.
Proof. vm_refl. Qed.
Lemma D_bf8c0 : decode_any W_bf8c0 = Some (OpImm ALU_AND 14 12 31, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_bf8c4 : bv 32 := 0x00d77463.
Lemma F_bf8c4 : fetch_word Ubsan.M.loaded_segments (0xbfa7c : word) = Some W_bf8c4.
Proof. vm_refl. Qed.
Lemma D_bf8c4 : decode_any W_bf8c4 = Some (Branch BC_GEU 14 13 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_bf8c8 : bv 32 := 0x00000023.
Lemma F_bf8c8 : fetch_word Ubsan.M.loaded_segments (0xbfa80 : word) = Some W_bf8c8.
Proof. vm_refl. Qed.
Lemma D_bf8c8 : decode_any W_bf8c8 = Some (Store SZ1 0 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_bf8cc : bv 32 := 0x01852783.
Lemma F_bf8cc : fetch_word Ubsan.M.loaded_segments (0xbfa84 : word) = Some W_bf8cc.
Proof. vm_refl. Qed.
Lemma D_bf8cc : decode_any W_bf8cc = Some (Load SZ4 true 15 10 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_bf8d0 : bv 32 := 0x00100713.
Lemma F_bf8d0 : fetch_word Ubsan.M.loaded_segments (0xbfa88 : word) = Some W_bf8d0.
Proof. vm_refl. Qed.
Lemma D_bf8d0 : decode_any W_bf8d0 = Some (OpImm ALU_ADD 14 0 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_bf8d4 : bv 32 := 0x00d7173b.
Lemma F_bf8d4 : fetch_word Ubsan.M.loaded_segments (0xbfa8c : word) = Some W_bf8d4.
Proof. vm_refl. Qed.
Lemma D_bf8d4 : decode_any W_bf8d4 = Some (Op32 ALU_SLL 14 14 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_bf8d8 : bv 32 := 0x00e7f7b3.
Lemma F_bf8d8 : fetch_word Ubsan.M.loaded_segments (0xbfa90 : word) = Some W_bf8d8.
Proof. vm_refl. Qed.
Lemma D_bf8d8 : decode_any W_bf8d8 = Some (Op ALU_AND 15 15 14, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_bf8dc : bv 32 := 0x00078463.
Lemma F_bf8dc : fetch_word Ubsan.M.loaded_segments (0xbfa94 : word) = Some W_bf8dc.
Proof. vm_refl. Qed.
Lemma D_bf8dc : decode_any W_bf8dc = Some (Branch BC_EQ 15 0 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_bf8e0 : bv 32 := 0x00000023.
Lemma F_bf8e0 : fetch_word Ubsan.M.loaded_segments (0xbfa98 : word) = Some W_bf8e0.
Proof. vm_refl. Qed.
Lemma D_bf8e0 : decode_any W_bf8e0 = Some (Store SZ1 0 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_bf8e4 : bv 32 := 0x01c52783.
Lemma F_bf8e4 : fetch_word Ubsan.M.loaded_segments (0xbfa9c : word) = Some W_bf8e4.
Proof. vm_refl. Qed.
Lemma D_bf8e4 : decode_any W_bf8e4 = Some (Load SZ4 true 15 10 28, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_bf8e8 : bv 32 := 0x00e7f733.
Lemma F_bf8e8 : fetch_word Ubsan.M.loaded_segments (0xbfaa0 : word) = Some W_bf8e8.
Proof. vm_refl. Qed.
Lemma D_bf8e8 : decode_any W_bf8e8 = Some (Op ALU_AND 14 15 14, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_bf8ec : bv 32 := 0x00070463.
Lemma F_bf8ec : fetch_word Ubsan.M.loaded_segments (0xbfaa4 : word) = Some W_bf8ec.
Proof. vm_refl. Qed.
Lemma D_bf8ec : decode_any W_bf8ec = Some (Branch BC_EQ 14 0 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_bf8f0 : bv 32 := 0x00000023.
Lemma F_bf8f0 : fetch_word Ubsan.M.loaded_segments (0xbfaa8 : word) = Some W_bf8f0.
Proof. vm_refl. Qed.
Lemma D_bf8f0 : decode_any W_bf8f0 = Some (Store SZ1 0 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_bf8f4 : bv 32 := 0xfffff737.
Lemma F_bf8f4 : fetch_word Ubsan.M.loaded_segments (0xbfaac : word) = Some W_bf8f4.
Proof. vm_refl. Qed.
Lemma D_bf8f4 : decode_any W_bf8f4 = Some (Lui 14 1048575, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_bf8f8 : bv 32 := 0x0004e797.
Lemma F_bf8f8 : fetch_word Ubsan.M.loaded_segments (0xbfab0 : word) = Some W_bf8f8.
Proof. vm_refl. Qed.
Lemma D_bf8f8 : decode_any W_bf8f8 = Some (Auipc 15 78, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_bf8fc : bv 32 := 0x00e57733.
Lemma F_bf8fc : fetch_word Ubsan.M.loaded_segments (0xbfab4 : word) = Some W_bf8fc.
Proof. vm_refl. Qed.
Lemma D_bf8fc : decode_any W_bf8fc = Some (Op ALU_AND 14 10 14, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_bf900 : bv 32 := 0x00073703.
Lemma F_bf900 : fetch_word Ubsan.M.loaded_segments (0xbfab8 : word) = Some W_bf900.
Proof. vm_refl. Qed.
Lemma D_bf900 : decode_any W_bf900 = Some (Load SZ8 true 14 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_bf904 : bv 32 := 0x3d87b783.
Lemma F_bf904 : fetch_word Ubsan.M.loaded_segments (0xbfabc : word) = Some W_bf904.
Proof. vm_refl. Qed.
Lemma D_bf904 : decode_any W_bf904 = Some (Load SZ8 true 15 15 984, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_bf908 : bv 32 := 0x00f70463.
Lemma F_bf908 : fetch_word Ubsan.M.loaded_segments (0xbfac0 : word) = Some W_bf908.
Proof. vm_refl. Qed.
Lemma D_bf908 : decode_any W_bf908 = Some (Branch BC_EQ 14 15 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_bf90c : bv 32 := 0x00000023.
Lemma F_bf90c : fetch_word Ubsan.M.loaded_segments (0xbfac4 : word) = Some W_bf90c.
Proof. vm_refl. Qed.
Lemma D_bf90c : decode_any W_bf90c = Some (Store SZ1 0 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_bf910 : bv 32 := 0x03461713.
Lemma F_bf910 : fetch_word Ubsan.M.loaded_segments (0xbfac8 : word) = Some W_bf910.
Proof. vm_refl. Qed.
Lemma D_bf910 : decode_any W_bf910 = Some (ShiftImm ALU_SLL 14 12 52, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_bf914 : bv 32 := 0x03a75713.
Lemma F_bf914 : fetch_word Ubsan.M.loaded_segments (0xbfacc : word) = Some W_bf914.
Proof. vm_refl. Qed.
Lemma D_bf914 : decode_any W_bf914 = Some (ShiftImm ALU_SRL 14 14 58, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_bf918 : bv 32 := 0x02f00793.
Lemma F_bf918 : fetch_word Ubsan.M.loaded_segments (0xbfad0 : word) = Some W_bf918.
Proof. vm_refl. Qed.
Lemma D_bf918 : decode_any W_bf918 = Some (OpImm ALU_ADD 15 0 47, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_bf91c : bv 32 := 0x02e7ea63.
Lemma F_bf91c : fetch_word Ubsan.M.loaded_segments (0xbfad4 : word) = Some W_bf91c.
Proof. vm_refl. Qed.
Lemma D_bf91c : decode_any W_bf91c = Some (Branch BC_LTU 15 14 52, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_bf920 : bv 32 := 0x00171713.
Lemma F_bf920 : fetch_word Ubsan.M.loaded_segments (0xbfad8 : word) = Some W_bf920.
Proof. vm_refl. Qed.
Lemma D_bf920 : decode_any W_bf920 = Some (ShiftImm ALU_SLL 14 14 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_bf924 : bv 32 := 0xfff62797.
Lemma F_bf924 : fetch_word Ubsan.M.loaded_segments (0xbfadc : word) = Some W_bf924.
Proof. vm_refl. Qed.
Lemma D_bf924 : decode_any W_bf924 = Some (Auipc 15 1048418, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_bf928 : bv 32 := 0xa7478793.
Lemma F_bf928 : fetch_word Ubsan.M.loaded_segments (0xbfae0 : word) = Some W_bf928.
Proof. vm_refl. Qed.
Lemma D_bf928 : decode_any W_bf928 = Some (OpImm ALU_ADD 15 15 2676, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_bf92c : bv 32 := 0x00e78733.
Lemma F_bf92c : fetch_word Ubsan.M.loaded_segments (0xbfae4 : word) = Some W_bf92c.
Proof. vm_refl. Qed.
Lemma D_bf92c : decode_any W_bf92c = Some (Op ALU_ADD 14 15 14, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_bf930 : bv 32 := 0x00075703.
Lemma F_bf930 : fetch_word Ubsan.M.loaded_segments (0xbfae8 : word) = Some W_bf930.
Proof. vm_refl. Qed.
Lemma D_bf930 : decode_any W_bf930 = Some (Load SZ2 false 14 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_bf934 : bv 32 := 0x02d707b3.
Lemma F_bf934 : fetch_word Ubsan.M.loaded_segments (0xbfaec : word) = Some W_bf934.
Proof. vm_refl. Qed.
Lemma D_bf934 : decode_any W_bf934 = Some (Mul M_MUL 15 14 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_bf938 : bv 32 := 0x00f5f463.
Lemma F_bf938 : fetch_word Ubsan.M.loaded_segments (0xbfaf0 : word) = Some W_bf938.
Proof. vm_refl. Qed.
Lemma D_bf938 : decode_any W_bf938 = Some (Branch BC_GEU 11 15 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_bf93c : bv 32 := 0x00000023.
Lemma F_bf93c : fetch_word Ubsan.M.loaded_segments (0xbfaf4 : word) = Some W_bf93c.
Proof. vm_refl. Qed.
Lemma D_bf93c : decode_any W_bf93c = Some (Store SZ1 0 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_bf940 : bv 32 := 0x00168693.
Lemma F_bf940 : fetch_word Ubsan.M.loaded_segments (0xbfaf8 : word) = Some W_bf940.
Proof. vm_refl. Qed.
Lemma D_bf940 : decode_any W_bf940 = Some (OpImm ALU_ADD 13 13 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_bf944 : bv 32 := 0x02e686b3.
Lemma F_bf944 : fetch_word Ubsan.M.loaded_segments (0xbfafc : word) = Some W_bf944.
Proof. vm_refl. Qed.
Lemma D_bf944 : decode_any W_bf944 = Some (Mul M_MUL 13 13 14, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_bf948 : bv 32 := 0x00d5f863.
Lemma F_bf948 : fetch_word Ubsan.M.loaded_segments (0xbfb00 : word) = Some W_bf948.
Proof. vm_refl. Qed.
Lemma D_bf948 : decode_any W_bf948 = Some (Branch BC_GEU 11 13 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_bf94c : bv 32 := 0x0100006f.
Lemma F_bf94c : fetch_word Ubsan.M.loaded_segments (0xbfb04 : word) = Some W_bf94c.
Proof. vm_refl. Qed.
Lemma D_bf94c : decode_any W_bf94c = Some (Jal 0 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_bf950 : bv 32 := 0x03f00693.
Lemma F_bf950 : fetch_word Ubsan.M.loaded_segments (0xbfb08 : word) = Some W_bf950.
Proof. vm_refl. Qed.
Lemma D_bf950 : decode_any W_bf950 = Some (OpImm ALU_ADD 13 0 63, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_bf954 : bv 32 := 0x00d70463.
Lemma F_bf954 : fetch_word Ubsan.M.loaded_segments (0xbfb0c : word) = Some W_bf954.
Proof. vm_refl. Qed.
Lemma D_bf954 : decode_any W_bf954 = Some (Branch BC_EQ 14 13 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_bf958 : bv 32 := 0x00000023.
Lemma F_bf958 : fetch_word Ubsan.M.loaded_segments (0xbfb10 : word) = Some W_bf958.
Proof. vm_refl. Qed.
Lemma D_bf958 : decode_any W_bf958 = Some (Store SZ1 0 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_bf95c : bv 32 := 0x00c65613.
Lemma F_bf95c : fetch_word Ubsan.M.loaded_segments (0xbfb14 : word) = Some W_bf95c.
Proof. vm_refl. Qed.
Lemma D_bf95c : decode_any W_bf95c = Some (ShiftImm ALU_SRL 12 12 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_bf960 : bv 32 := 0x00060a63.
Lemma F_bf960 : fetch_word Ubsan.M.loaded_segments (0xbfb18 : word) = Some W_bf960.
Proof. vm_refl. Qed.
Lemma D_bf960 : decode_any W_bf960 = Some (Branch BC_EQ 12 0 20, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_bf964 : bv 32 := 0x00861613.
Lemma F_bf964 : fetch_word Ubsan.M.loaded_segments (0xbfb1c : word) = Some W_bf964.
Proof. vm_refl. Qed.
Lemma D_bf964 : decode_any W_bf964 = Some (ShiftImm ALU_SLL 12 12 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_bf968 : bv 32 := 0xfff60613.
Lemma F_bf968 : fetch_word Ubsan.M.loaded_segments (0xbfb20 : word) = Some W_bf968.
Proof. vm_refl. Qed.
Lemma D_bf968 : decode_any W_bf968 = Some (OpImm ALU_ADD 12 12 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_bf96c : bv 32 := 0x00b67463.
Lemma F_bf96c : fetch_word Ubsan.M.loaded_segments (0xbfb24 : word) = Some W_bf96c.
Proof. vm_refl. Qed.
Lemma D_bf96c : decode_any W_bf96c = Some (Branch BC_GEU 12 11 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_bf970 : bv 32 := 0x00000023.
Lemma F_bf970 : fetch_word Ubsan.M.loaded_segments (0xbfb28 : word) = Some W_bf970.
Proof. vm_refl. Qed.
Lemma D_bf970 : decode_any W_bf970 = Some (Store SZ1 0 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_bf974 : bv 32 := 0x00008067.
Lemma F_bf974 : fetch_word Ubsan.M.loaded_segments (0xbfb2c : word) = Some W_bf974.
Proof. vm_refl. Qed.
Lemma D_bf974 : decode_any W_bf974 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.
