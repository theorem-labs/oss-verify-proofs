(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OssFuzzTheorems.mbedtls.fuzz_pkcs7.images Require Import Ubsan.
Open Scope bv_scope.

(* [comment removed for export] *)
Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

(* [comment removed for export] *)
Definition W_3e144 : bv 32 := 0xff010113.
Lemma F_3e144 : fetch_word Ubsan.M.loaded_segments (0x41890 : word) = Some W_3e144.
Proof. vm_refl. Qed.
Lemma D_3e144 : decode_any W_3e144 = Some (OpImm ALU_ADD 2 2 4080, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3e148 : bv 32 := 0x00113423.
Lemma F_3e148 : fetch_word Ubsan.M.loaded_segments (0x41894 : word) = Some W_3e148.
Proof. vm_refl. Qed.
Lemma D_3e148 : decode_any W_3e148 = Some (Store SZ8 2 1 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3e14c : bv 32 := 0x00813023.
Lemma F_3e14c : fetch_word Ubsan.M.loaded_segments (0x41898 : word) = Some W_3e14c.
Proof. vm_refl. Qed.
Lemma D_3e14c : decode_any W_3e14c = Some (Store SZ8 2 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3e150 : bv 32 := 0x608000ef.
Lemma F_3e150 : fetch_word Ubsan.M.loaded_segments (0x4189c : word) = Some W_3e150.
Proof. vm_refl. Qed.
Lemma D_3e150 : decode_any W_3e150 = Some (Jal 1 1544, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3e154 : bv 32 := 0x00053403.
Lemma F_3e154 : fetch_word Ubsan.M.loaded_segments (0x418a0 : word) = Some W_3e154.
Proof. vm_refl. Qed.
Lemma D_3e154 : decode_any W_3e154 = Some (Load SZ8 true 8 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3e158 : bv 32 := 0x12041663.
Lemma F_3e158 : fetch_word Ubsan.M.loaded_segments (0x418a4 : word) = Some W_3e158.
Proof. vm_refl. Qed.
Lemma D_3e158 : decode_any W_3e158 = Some (Branch BC_NE 8 0 300, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3e15c : bv 32 := 0x0003c517.
Lemma F_3e15c : fetch_word Ubsan.M.loaded_segments (0x418a8 : word) = Some W_3e15c.
Proof. vm_refl. Qed.
Lemma D_3e15c : decode_any W_3e15c = Some (Auipc 10 60, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3e160 : bv 32 := 0xec853403.
Lemma F_3e160 : fetch_word Ubsan.M.loaded_segments (0x418ac : word) = Some W_3e160.
Proof. vm_refl. Qed.
Lemma D_3e160 : decode_any W_3e160 = Some (Load SZ8 true 8 10 3784, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3e164 : bv 32 := 0x04040a63.
Lemma F_3e164 : fetch_word Ubsan.M.loaded_segments (0x418b0 : word) = Some W_3e164.
Proof. vm_refl. Qed.
Lemma D_3e164 : decode_any W_3e164 = Some (Branch BC_EQ 8 0 84, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3e1b8 : bv 32 := 0x0000b517.
Lemma F_3e1b8 : fetch_word Ubsan.M.loaded_segments (0x41904 : word) = Some W_3e1b8.
Proof. vm_refl. Qed.
Lemma D_3e1b8 : decode_any W_3e1b8 = Some (Auipc 10 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3e1bc : bv 32 := 0x60453403.
Lemma F_3e1bc : fetch_word Ubsan.M.loaded_segments (0x41908 : word) = Some W_3e1bc.
Proof. vm_refl. Qed.
Lemma D_3e1bc : decode_any W_3e1bc = Some (Load SZ8 true 8 10 1540, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3e1c0 : bv 32 := 0x04040a63.
Lemma F_3e1c0 : fetch_word Ubsan.M.loaded_segments (0x4190c : word) = Some W_3e1c0.
Proof. vm_refl. Qed.
Lemma D_3e1c0 : decode_any W_3e1c0 = Some (Branch BC_EQ 8 0 84, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3e1c4 : bv 32 := 0x08c42503.
Lemma F_3e1c4 : fetch_word Ubsan.M.loaded_segments (0x41910 : word) = Some W_3e1c4.
Proof. vm_refl. Qed.
Lemma D_3e1c4 : decode_any W_3e1c4 = Some (Load SZ4 true 10 8 140, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3e1c8 : bv 32 := 0x00054663.
Lemma F_3e1c8 : fetch_word Ubsan.M.loaded_segments (0x41914 : word) = Some W_3e1c8.
Proof. vm_refl. Qed.
Lemma D_3e1c8 : decode_any W_3e1c8 = Some (Branch BC_LT 10 0 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3e1d4 : bv 32 := 0x02843503.
Lemma F_3e1d4 : fetch_word Ubsan.M.loaded_segments (0x41920 : word) = Some W_3e1d4.
Proof. vm_refl. Qed.
Lemma D_3e1d4 : decode_any W_3e1d4 = Some (Load SZ8 true 10 8 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3e1d8 : bv 32 := 0x03843583.
Lemma F_3e1d8 : fetch_word Ubsan.M.loaded_segments (0x41924 : word) = Some W_3e1d8.
Proof. vm_refl. Qed.
Lemma D_3e1d8 : decode_any W_3e1d8 = Some (Load SZ8 true 11 8 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3e1dc : bv 32 := 0x00b50c63.
Lemma F_3e1dc : fetch_word Ubsan.M.loaded_segments (0x41928 : word) = Some W_3e1dc.
Proof. vm_refl. Qed.
Lemma D_3e1dc : decode_any W_3e1dc = Some (Branch BC_EQ 10 11 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3e1e0 : bv 32 := 0x04843683.
Lemma F_3e1e0 : fetch_word Ubsan.M.loaded_segments (0x4192c : word) = Some W_3e1e0.
Proof. vm_refl. Qed.
Lemma D_3e1e0 : decode_any W_3e1e0 = Some (Load SZ8 true 13 8 72, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3e1e4 : bv 32 := 0x00040513.
Lemma F_3e1e4 : fetch_word Ubsan.M.loaded_segments (0x41930 : word) = Some W_3e1e4.
Proof. vm_refl. Qed.
Lemma D_3e1e4 : decode_any W_3e1e4 = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3e1e8 : bv 32 := 0x00000593.
Lemma F_3e1e8 : fetch_word Ubsan.M.loaded_segments (0x41934 : word) = Some W_3e1e8.
Proof. vm_refl. Qed.
Lemma D_3e1e8 : decode_any W_3e1e8 = Some (OpImm ALU_ADD 11 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3e1ec : bv 32 := 0x00000613.
Lemma F_3e1ec : fetch_word Ubsan.M.loaded_segments (0x41938 : word) = Some W_3e1ec.
Proof. vm_refl. Qed.
Lemma D_3e1ec : decode_any W_3e1ec = Some (OpImm ALU_ADD 12 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3e1f0 : bv 32 := 0x000680e7.
Lemma F_3e1f0 : fetch_word Ubsan.M.loaded_segments (0x4193c : word) = Some W_3e1f0.
Proof. vm_refl. Qed.
Lemma D_3e1f0 : decode_any W_3e1f0 = Some (Jalr 1 13 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3e1f4 : bv 32 := 0x00843503.
Lemma F_3e1f4 : fetch_word Ubsan.M.loaded_segments (0x41940 : word) = Some W_3e1f4.
Proof. vm_refl. Qed.
Lemma D_3e1f4 : decode_any W_3e1f4 = Some (Load SZ8 true 10 8 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3e1f8 : bv 32 := 0x01043583.
Lemma F_3e1f8 : fetch_word Ubsan.M.loaded_segments (0x41944 : word) = Some W_3e1f8.
Proof. vm_refl. Qed.
Lemma D_3e1f8 : decode_any W_3e1f8 = Some (Load SZ8 true 11 8 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3e1fc : bv 32 := 0x00b50c63.
Lemma F_3e1fc : fetch_word Ubsan.M.loaded_segments (0x41948 : word) = Some W_3e1fc.
Proof. vm_refl. Qed.
Lemma D_3e1fc : decode_any W_3e1fc = Some (Branch BC_EQ 10 11 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3e214 : bv 32 := 0x0000b517.
Lemma F_3e214 : fetch_word Ubsan.M.loaded_segments (0x41960 : word) = Some W_3e214.
Proof. vm_refl. Qed.
Lemma D_3e214 : decode_any W_3e214 = Some (Auipc 10 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3e218 : bv 32 := 0x4b853403.
Lemma F_3e218 : fetch_word Ubsan.M.loaded_segments (0x41964 : word) = Some W_3e218.
Proof. vm_refl. Qed.
Lemma D_3e218 : decode_any W_3e218 = Some (Load SZ8 true 8 10 1208, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3e21c : bv 32 := 0x0a040e63.
Lemma F_3e21c : fetch_word Ubsan.M.loaded_segments (0x41968 : word) = Some W_3e21c.
Proof. vm_refl. Qed.
Lemma D_3e21c : decode_any W_3e21c = Some (Branch BC_EQ 8 0 188, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3e220 : bv 32 := 0x08c42503.
Lemma F_3e220 : fetch_word Ubsan.M.loaded_segments (0x4196c : word) = Some W_3e220.
Proof. vm_refl. Qed.
Lemma D_3e220 : decode_any W_3e220 = Some (Load SZ4 true 10 8 140, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3e224 : bv 32 := 0x00054663.
Lemma F_3e224 : fetch_word Ubsan.M.loaded_segments (0x41970 : word) = Some W_3e224.
Proof. vm_refl. Qed.
Lemma D_3e224 : decode_any W_3e224 = Some (Branch BC_LT 10 0 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3e230 : bv 32 := 0x02843503.
Lemma F_3e230 : fetch_word Ubsan.M.loaded_segments (0x4197c : word) = Some W_3e230.
Proof. vm_refl. Qed.
Lemma D_3e230 : decode_any W_3e230 = Some (Load SZ8 true 10 8 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3e234 : bv 32 := 0x03843583.
Lemma F_3e234 : fetch_word Ubsan.M.loaded_segments (0x41980 : word) = Some W_3e234.
Proof. vm_refl. Qed.
Lemma D_3e234 : decode_any W_3e234 = Some (Load SZ8 true 11 8 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3e238 : bv 32 := 0x00b50c63.
Lemma F_3e238 : fetch_word Ubsan.M.loaded_segments (0x41984 : word) = Some W_3e238.
Proof. vm_refl. Qed.
Lemma D_3e238 : decode_any W_3e238 = Some (Branch BC_EQ 10 11 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3e250 : bv 32 := 0x00843503.
Lemma F_3e250 : fetch_word Ubsan.M.loaded_segments (0x4199c : word) = Some W_3e250.
Proof. vm_refl. Qed.
Lemma D_3e250 : decode_any W_3e250 = Some (Load SZ8 true 10 8 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3e254 : bv 32 := 0x01043583.
Lemma F_3e254 : fetch_word Ubsan.M.loaded_segments (0x419a0 : word) = Some W_3e254.
Proof. vm_refl. Qed.
Lemma D_3e254 : decode_any W_3e254 = Some (Load SZ8 true 11 8 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3e258 : bv 32 := 0x08b50063.
Lemma F_3e258 : fetch_word Ubsan.M.loaded_segments (0x419a4 : word) = Some W_3e258.
Proof. vm_refl. Qed.
Lemma D_3e258 : decode_any W_3e258 = Some (Branch BC_EQ 10 11 128, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3e2d8 : bv 32 := 0x00813083.
Lemma F_3e2d8 : fetch_word Ubsan.M.loaded_segments (0x41a24 : word) = Some W_3e2d8.
Proof. vm_refl. Qed.
Lemma D_3e2d8 : decode_any W_3e2d8 = Some (Load SZ8 true 1 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3e2dc : bv 32 := 0x00013403.
Lemma F_3e2dc : fetch_word Ubsan.M.loaded_segments (0x41a28 : word) = Some W_3e2dc.
Proof. vm_refl. Qed.
Lemma D_3e2dc : decode_any W_3e2dc = Some (Load SZ8 true 8 2 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3e2e0 : bv 32 := 0x01010113.
Lemma F_3e2e0 : fetch_word Ubsan.M.loaded_segments (0x41a2c : word) = Some W_3e2e0.
Proof. vm_refl. Qed.
Lemma D_3e2e0 : decode_any W_3e2e0 = Some (OpImm ALU_ADD 2 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3e2e4 : bv 32 := 0x00008067.
Lemma F_3e2e4 : fetch_word Ubsan.M.loaded_segments (0x41a30 : word) = Some W_3e2e4.
Proof. vm_refl. Qed.
Lemma D_3e2e4 : decode_any W_3e2e4 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3e2e8 : bv 32 := 0xf9010113.
Lemma F_3e2e8 : fetch_word Ubsan.M.loaded_segments (0x41a34 : word) = Some W_3e2e8.
Proof. vm_refl. Qed.
Lemma D_3e2e8 : decode_any W_3e2e8 = Some (OpImm ALU_ADD 2 2 3984, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3e2ec : bv 32 := 0x06113423.
Lemma F_3e2ec : fetch_word Ubsan.M.loaded_segments (0x41a38 : word) = Some W_3e2ec.
Proof. vm_refl. Qed.
Lemma D_3e2ec : decode_any W_3e2ec = Some (Store SZ8 2 1 104, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3e2f0 : bv 32 := 0x06813023.
Lemma F_3e2f0 : fetch_word Ubsan.M.loaded_segments (0x41a3c : word) = Some W_3e2f0.
Proof. vm_refl. Qed.
Lemma D_3e2f0 : decode_any W_3e2f0 = Some (Store SZ8 2 8 96, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3e2f4 : bv 32 := 0x04913c23.
Lemma F_3e2f4 : fetch_word Ubsan.M.loaded_segments (0x41a40 : word) = Some W_3e2f4.
Proof. vm_refl. Qed.
Lemma D_3e2f4 : decode_any W_3e2f4 = Some (Store SZ8 2 9 88, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3e2f8 : bv 32 := 0x05213823.
Lemma F_3e2f8 : fetch_word Ubsan.M.loaded_segments (0x41a44 : word) = Some W_3e2f8.
Proof. vm_refl. Qed.
Lemma D_3e2f8 : decode_any W_3e2f8 = Some (Store SZ8 2 18 80, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3e2fc : bv 32 := 0x05313423.
Lemma F_3e2fc : fetch_word Ubsan.M.loaded_segments (0x41a48 : word) = Some W_3e2fc.
Proof. vm_refl. Qed.
Lemma D_3e2fc : decode_any W_3e2fc = Some (Store SZ8 2 19 72, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3e300 : bv 32 := 0x05413023.
Lemma F_3e300 : fetch_word Ubsan.M.loaded_segments (0x41a4c : word) = Some W_3e300.
Proof. vm_refl. Qed.
Lemma D_3e300 : decode_any W_3e300 = Some (Store SZ8 2 20 64, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3e304 : bv 32 := 0x03513c23.
Lemma F_3e304 : fetch_word Ubsan.M.loaded_segments (0x41a50 : word) = Some W_3e304.
Proof. vm_refl. Qed.
Lemma D_3e304 : decode_any W_3e304 = Some (Store SZ8 2 21 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3e308 : bv 32 := 0x03613823.
Lemma F_3e308 : fetch_word Ubsan.M.loaded_segments (0x41a54 : word) = Some W_3e308.
Proof. vm_refl. Qed.
Lemma D_3e308 : decode_any W_3e308 = Some (Store SZ8 2 22 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3e30c : bv 32 := 0x00060413.
Lemma F_3e30c : fetch_word Ubsan.M.loaded_segments (0x41a58 : word) = Some W_3e30c.
Proof. vm_refl. Qed.
Lemma D_3e30c : decode_any W_3e30c = Some (OpImm ALU_ADD 8 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3e310 : bv 32 := 0x00050493.
Lemma F_3e310 : fetch_word Ubsan.M.loaded_segments (0x41a5c : word) = Some W_3e310.
Proof. vm_refl. Qed.
Lemma D_3e310 : decode_any W_3e310 = Some (OpImm ALU_ADD 9 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3e314 : bv 32 := 0x0000a517.
Lemma F_3e314 : fetch_word Ubsan.M.loaded_segments (0x41a60 : word) = Some W_3e314.
Proof. vm_refl. Qed.
Lemma D_3e314 : decode_any W_3e314 = Some (Auipc 10 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3e318 : bv 32 := 0x27853a83.
Lemma F_3e318 : fetch_word Ubsan.M.loaded_segments (0x41a64 : word) = Some W_3e318.
Proof. vm_refl. Qed.
Lemma D_3e318 : decode_any W_3e318 = Some (Load SZ8 true 21 10 632, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3e31c : bv 32 := 0x000ab503.
Lemma F_3e31c : fetch_word Ubsan.M.loaded_segments (0x41a68 : word) = Some W_3e31c.
Proof. vm_refl. Qed.
Lemma D_3e31c : decode_any W_3e31c = Some (Load SZ8 true 10 21 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3e320 : bv 32 := 0x02a13423.
Lemma F_3e320 : fetch_word Ubsan.M.loaded_segments (0x41a6c : word) = Some W_3e320.
Proof. vm_refl. Qed.
Lemma D_3e320 : decode_any W_3e320 = Some (Store SZ8 2 10 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3e324 : bv 32 := 0x0284b503.
Lemma F_3e324 : fetch_word Ubsan.M.loaded_segments (0x41a70 : word) = Some W_3e324.
Proof. vm_refl. Qed.
Lemma D_3e324 : decode_any W_3e324 = Some (Load SZ8 true 10 9 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3e328 : bv 32 := 0x0384b603.
Lemma F_3e328 : fetch_word Ubsan.M.loaded_segments (0x41a74 : word) = Some W_3e328.
Proof. vm_refl. Qed.
Lemma D_3e328 : decode_any W_3e328 = Some (Load SZ8 true 12 9 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3e32c : bv 32 := 0x40c50b33.
Lemma F_3e32c : fetch_word Ubsan.M.loaded_segments (0x41a78 : word) = Some W_3e32c.
Proof. vm_refl. Qed.
Lemma D_3e32c : decode_any W_3e32c = Some (Op ALU_SUB 22 10 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3e330 : bv 32 := 0x00c546b3.
Lemma F_3e330 : fetch_word Ubsan.M.loaded_segments (0x41a7c : word) = Some W_3e330.
Proof. vm_refl. Qed.
Lemma D_3e330 : decode_any W_3e330 = Some (Op ALU_XOR 13 10 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3e334 : bv 32 := 0x00c13423.
Lemma F_3e334 : fetch_word Ubsan.M.loaded_segments (0x41a80 : word) = Some W_3e334.
Proof. vm_refl. Qed.
Lemma D_3e334 : decode_any W_3e334 = Some (Store SZ8 2 12 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3e338 : bv 32 := 0x01613823.
Lemma F_3e338 : fetch_word Ubsan.M.loaded_segments (0x41a84 : word) = Some W_3e338.
Proof. vm_refl. Qed.
Lemma D_3e338 : decode_any W_3e338 = Some (Store SZ8 2 22 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3e33c : bv 32 := 0x00b13c23.
Lemma F_3e33c : fetch_word Ubsan.M.loaded_segments (0x41a88 : word) = Some W_3e33c.
Proof. vm_refl. Qed.
Lemma D_3e33c : decode_any W_3e33c = Some (Store SZ8 2 11 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3e340 : bv 32 := 0x02813023.
Lemma F_3e340 : fetch_word Ubsan.M.loaded_segments (0x41a8c : word) = Some W_3e340.
Proof. vm_refl. Qed.
Lemma D_3e340 : decode_any W_3e340 = Some (Store SZ8 2 8 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3e344 : bv 32 := 0x008b0b33.
Lemma F_3e344 : fetch_word Ubsan.M.loaded_segments (0x41a90 : word) = Some W_3e344.
Proof. vm_refl. Qed.
Lemma D_3e344 : decode_any W_3e344 = Some (Op ALU_ADD 22 22 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3e348 : bv 32 := 0x00d03933.
Lemma F_3e348 : fetch_word Ubsan.M.loaded_segments (0x41a94 : word) = Some W_3e348.
Proof. vm_refl. Qed.
Lemma D_3e348 : decode_any W_3e348 = Some (Op ALU_SLTU 18 0 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3e34c : bv 32 := 0x00c50663.
Lemma F_3e34c : fetch_word Ubsan.M.loaded_segments (0x41a98 : word) = Some W_3e34c.
Proof. vm_refl. Qed.
Lemma D_3e34c : decode_any W_3e34c = Some (Branch BC_EQ 10 12 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3e350 : bv 32 := 0x00810993.
Lemma F_3e350 : fetch_word Ubsan.M.loaded_segments (0x41a9c : word) = Some W_3e350.
Proof. vm_refl. Qed.
Lemma D_3e350 : decode_any W_3e350 = Some (OpImm ALU_ADD 19 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3e354 : bv 32 := 0x0080006f.
Lemma F_3e354 : fetch_word Ubsan.M.loaded_segments (0x41aa0 : word) = Some W_3e354.
Proof. vm_refl. Qed.
Lemma D_3e354 : decode_any W_3e354 = Some (Jal 0 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3e358 : bv 32 := 0x01810993.
Lemma F_3e358 : fetch_word Ubsan.M.loaded_segments (0x41aa4 : word) = Some W_3e358.
Proof. vm_refl. Qed.
Lemma D_3e358 : decode_any W_3e358 = Some (OpImm ALU_ADD 19 2 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3e35c : bv 32 := 0x0784a503.
Lemma F_3e35c : fetch_word Ubsan.M.loaded_segments (0x41aa8 : word) = Some W_3e35c.
Proof. vm_refl. Qed.
Lemma D_3e35c : decode_any W_3e35c = Some (Load SZ4 true 10 9 120, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3e360 : bv 32 := 0x00190913.
Lemma F_3e360 : fetch_word Ubsan.M.loaded_segments (0x41aac : word) = Some W_3e360.
Proof. vm_refl. Qed.
Lemma D_3e360 : decode_any W_3e360 = Some (OpImm ALU_ADD 18 18 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3e364 : bv 32 := 0x04200893.
Lemma F_3e364 : fetch_word Ubsan.M.loaded_segments (0x41ab0 : word) = Some W_3e364.
Proof. vm_refl. Qed.
Lemma D_3e364 : decode_any W_3e364 = Some (OpImm ALU_ADD 17 0 66, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3e368 : bv 32 := 0x00098593.
Lemma F_3e368 : fetch_word Ubsan.M.loaded_segments (0x41ab4 : word) = Some W_3e368.
Proof. vm_refl. Qed.
Lemma D_3e368 : decode_any W_3e368 = Some (OpImm ALU_ADD 11 19 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3e36c : bv 32 := 0x00090613.
Lemma F_3e36c : fetch_word Ubsan.M.loaded_segments (0x41ab8 : word) = Some W_3e36c.
Proof. vm_refl. Qed.
Lemma D_3e36c : decode_any W_3e36c = Some (OpImm ALU_ADD 12 18 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3e370 : bv 32 := 0x00000073.
Lemma F_3e370 : fetch_word Ubsan.M.loaded_segments (0x41abc : word) = Some W_3e370.
Proof. vm_refl. Qed.
Lemma E_3e370 : is_ecall W_3e370 = true.
Proof. reflexivity. Qed.

(* [comment removed for export] *)
Definition W_3e374 : bv 32 := 0xe69fd0ef.
Lemma F_3e374 : fetch_word Ubsan.M.loaded_segments (0x41ac0 : word) = Some W_3e374.
Proof. vm_refl. Qed.
Lemma D_3e374 : decode_any W_3e374 = Some (Jal 1 2088552, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3e378 : bv 32 := 0x09651863.
Lemma F_3e378 : fetch_word Ubsan.M.loaded_segments (0x41ac4 : word) = Some W_3e378.
Proof. vm_refl. Qed.
Lemma D_3e378 : decode_any W_3e378 = Some (Branch BC_NE 10 22 144, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3e37c : bv 32 := 0x0584b503.
Lemma F_3e37c : fetch_word Ubsan.M.loaded_segments (0x41ac8 : word) = Some W_3e37c.
Proof. vm_refl. Qed.
Lemma D_3e37c : decode_any W_3e37c = Some (Load SZ8 true 10 9 88, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3e380 : bv 32 := 0x0604b583.
Lemma F_3e380 : fetch_word Ubsan.M.loaded_segments (0x41acc : word) = Some W_3e380.
Proof. vm_refl. Qed.
Lemma D_3e380 : decode_any W_3e380 = Some (Load SZ8 true 11 9 96, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3e384 : bv 32 := 0x00b505b3.
Lemma F_3e384 : fetch_word Ubsan.M.loaded_segments (0x41ad0 : word) = Some W_3e384.
Proof. vm_refl. Qed.
Lemma D_3e384 : decode_any W_3e384 = Some (Op ALU_ADD 11 10 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3e388 : bv 32 := 0x02b4b023.
Lemma F_3e388 : fetch_word Ubsan.M.loaded_segments (0x41ad4 : word) = Some W_3e388.
Proof. vm_refl. Qed.
Lemma D_3e388 : decode_any W_3e388 = Some (Store SZ8 9 11 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3e38c : bv 32 := 0x02a4b423.
Lemma F_3e38c : fetch_word Ubsan.M.loaded_segments (0x41ad8 : word) = Some W_3e38c.
Proof. vm_refl. Qed.
Lemma D_3e38c : decode_any W_3e38c = Some (Store SZ8 9 10 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3e390 : bv 32 := 0x02a4bc23.
Lemma F_3e390 : fetch_word Ubsan.M.loaded_segments (0x41adc : word) = Some W_3e390.
Proof. vm_refl. Qed.
Lemma D_3e390 : decode_any W_3e390 = Some (Store SZ8 9 10 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3e394 : bv 32 := 0x00040513.
Lemma F_3e394 : fetch_word Ubsan.M.loaded_segments (0x41ae0 : word) = Some W_3e394.
Proof. vm_refl. Qed.
Lemma D_3e394 : decode_any W_3e394 = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3e398 : bv 32 := 0x000ab583.
Lemma F_3e398 : fetch_word Ubsan.M.loaded_segments (0x41ae4 : word) = Some W_3e398.
Proof. vm_refl. Qed.
Lemma D_3e398 : decode_any W_3e398 = Some (Load SZ8 true 11 21 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3e39c : bv 32 := 0x02813603.
Lemma F_3e39c : fetch_word Ubsan.M.loaded_segments (0x41ae8 : word) = Some W_3e39c.
Proof. vm_refl. Qed.
Lemma D_3e39c : decode_any W_3e39c = Some (Load SZ8 true 12 2 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3e3a0 : bv 32 := 0x0cc59a63.
Lemma F_3e3a0 : fetch_word Ubsan.M.loaded_segments (0x41aec : word) = Some W_3e3a0.
Proof. vm_refl. Qed.
Lemma D_3e3a0 : decode_any W_3e3a0 = Some (Branch BC_NE 11 12 212, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3e3a4 : bv 32 := 0x06813083.
Lemma F_3e3a4 : fetch_word Ubsan.M.loaded_segments (0x41af0 : word) = Some W_3e3a4.
Proof. vm_refl. Qed.
Lemma D_3e3a4 : decode_any W_3e3a4 = Some (Load SZ8 true 1 2 104, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3e3a8 : bv 32 := 0x06013403.
Lemma F_3e3a8 : fetch_word Ubsan.M.loaded_segments (0x41af4 : word) = Some W_3e3a8.
Proof. vm_refl. Qed.
Lemma D_3e3a8 : decode_any W_3e3a8 = Some (Load SZ8 true 8 2 96, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3e3ac : bv 32 := 0x05813483.
Lemma F_3e3ac : fetch_word Ubsan.M.loaded_segments (0x41af8 : word) = Some W_3e3ac.
Proof. vm_refl. Qed.
Lemma D_3e3ac : decode_any W_3e3ac = Some (Load SZ8 true 9 2 88, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3e3b0 : bv 32 := 0x05013903.
Lemma F_3e3b0 : fetch_word Ubsan.M.loaded_segments (0x41afc : word) = Some W_3e3b0.
Proof. vm_refl. Qed.
Lemma D_3e3b0 : decode_any W_3e3b0 = Some (Load SZ8 true 18 2 80, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3e3b4 : bv 32 := 0x04813983.
Lemma F_3e3b4 : fetch_word Ubsan.M.loaded_segments (0x41b00 : word) = Some W_3e3b4.
Proof. vm_refl. Qed.
Lemma D_3e3b4 : decode_any W_3e3b4 = Some (Load SZ8 true 19 2 72, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3e3b8 : bv 32 := 0x04013a03.
Lemma F_3e3b8 : fetch_word Ubsan.M.loaded_segments (0x41b04 : word) = Some W_3e3b8.
Proof. vm_refl. Qed.
Lemma D_3e3b8 : decode_any W_3e3b8 = Some (Load SZ8 true 20 2 64, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3e3bc : bv 32 := 0x03813a83.
Lemma F_3e3bc : fetch_word Ubsan.M.loaded_segments (0x41b08 : word) = Some W_3e3bc.
Proof. vm_refl. Qed.
Lemma D_3e3bc : decode_any W_3e3bc = Some (Load SZ8 true 21 2 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3e3c0 : bv 32 := 0x03013b03.
Lemma F_3e3c0 : fetch_word Ubsan.M.loaded_segments (0x41b0c : word) = Some W_3e3c0.
Proof. vm_refl. Qed.
Lemma D_3e3c0 : decode_any W_3e3c0 = Some (Load SZ8 true 22 2 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3e3c4 : bv 32 := 0x07010113.
Lemma F_3e3c4 : fetch_word Ubsan.M.loaded_segments (0x41b10 : word) = Some W_3e3c4.
Proof. vm_refl. Qed.
Lemma D_3e3c4 : decode_any W_3e3c4 = Some (OpImm ALU_ADD 2 2 112, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3e3c8 : bv 32 := 0x00008067.
Lemma F_3e3c8 : fetch_word Ubsan.M.loaded_segments (0x41b14 : word) = Some W_3e3c8.
Proof. vm_refl. Qed.
Lemma D_3e3c8 : decode_any W_3e3c8 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3e3cc : bv 32 := 0x00800713.
Lemma F_3e3cc : fetch_word Ubsan.M.loaded_segments (0x41b18 : word) = Some W_3e3cc.
Proof. vm_refl. Qed.
Lemma D_3e3cc : decode_any W_3e3cc = Some (OpImm ALU_ADD 14 0 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3e3d0 : bv 32 := 0x000a0593.
Lemma F_3e3d0 : fetch_word Ubsan.M.loaded_segments (0x41b1c : word) = Some W_3e3d0.
Proof. vm_refl. Qed.
Lemma D_3e3d0 : decode_any W_3e3d0 = Some (OpImm ALU_ADD 11 20 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3e3d4 : bv 32 := 0x00e98733.
Lemma F_3e3d4 : fetch_word Ubsan.M.loaded_segments (0x41b20 : word) = Some W_3e3d4.
Proof. vm_refl. Qed.
Lemma D_3e3d4 : decode_any W_3e3d4 = Some (Op ALU_ADD 14 19 14, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3e3d8 : bv 32 := 0x00073783.
Lemma F_3e3d8 : fetch_word Ubsan.M.loaded_segments (0x41b24 : word) = Some W_3e3d8.
Proof. vm_refl. Qed.
Lemma D_3e3d8 : decode_any W_3e3d8 = Some (Load SZ8 true 15 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3e3dc : bv 32 := 0x40ab0b33.
Lemma F_3e3dc : fetch_word Ubsan.M.loaded_segments (0x41b28 : word) = Some W_3e3dc.
Proof. vm_refl. Qed.
Lemma D_3e3dc : decode_any W_3e3dc = Some (Op ALU_SUB 22 22 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3e3e0 : bv 32 := 0x0784a503.
Lemma F_3e3e0 : fetch_word Ubsan.M.loaded_segments (0x41b2c : word) = Some W_3e3e0.
Proof. vm_refl. Qed.
Lemma D_3e3e0 : decode_any W_3e3e0 = Some (Load SZ4 true 10 9 120, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3e3e4 : bv 32 := 0x40c9093b.
Lemma F_3e3e4 : fetch_word Ubsan.M.loaded_segments (0x41b30 : word) = Some W_3e3e4.
Proof. vm_refl. Qed.
Lemma D_3e3e4 : decode_any W_3e3e4 = Some (Op32 ALU_SUB 18 18 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3e3e8 : bv 32 := 0x40d787b3.
Lemma F_3e3e8 : fetch_word Ubsan.M.loaded_segments (0x41b34 : word) = Some W_3e3e8.
Proof. vm_refl. Qed.
Lemma D_3e3e8 : decode_any W_3e3e8 = Some (Op ALU_SUB 15 15 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3e3ec : bv 32 := 0x00f73023.
Lemma F_3e3ec : fetch_word Ubsan.M.loaded_segments (0x41b38 : word) = Some W_3e3ec.
Proof. vm_refl. Qed.
Lemma D_3e3ec : decode_any W_3e3ec = Some (Store SZ8 14 15 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3e3f0 : bv 32 := 0x04200893.
Lemma F_3e3f0 : fetch_word Ubsan.M.loaded_segments (0x41b3c : word) = Some W_3e3f0.
Proof. vm_refl. Qed.
Lemma D_3e3f0 : decode_any W_3e3f0 = Some (OpImm ALU_ADD 17 0 66, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3e3f4 : bv 32 := 0x00090613.
Lemma F_3e3f4 : fetch_word Ubsan.M.loaded_segments (0x41b40 : word) = Some W_3e3f4.
Proof. vm_refl. Qed.
Lemma D_3e3f4 : decode_any W_3e3f4 = Some (OpImm ALU_ADD 12 18 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3e3f8 : bv 32 := 0x00000073.
Lemma F_3e3f8 : fetch_word Ubsan.M.loaded_segments (0x41b44 : word) = Some W_3e3f8.
Proof. vm_refl. Qed.
Lemma E_3e3f8 : is_ecall W_3e3f8 = true.
Proof. reflexivity. Qed.

(* [comment removed for export] *)
Definition W_3e3fc : bv 32 := 0xde1fd0ef.
Lemma F_3e3fc : fetch_word Ubsan.M.loaded_segments (0x41b48 : word) = Some W_3e3fc.
Proof. vm_refl. Qed.
Lemma D_3e3fc : decode_any W_3e3fc = Some (Jal 1 2088416, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3e400 : bv 32 := 0x000a0993.
Lemma F_3e400 : fetch_word Ubsan.M.loaded_segments (0x41b4c : word) = Some W_3e400.
Proof. vm_refl. Qed.
Lemma D_3e400 : decode_any W_3e400 = Some (OpImm ALU_ADD 19 20 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3e404 : bv 32 := 0xf7650ce3.
Lemma F_3e404 : fetch_word Ubsan.M.loaded_segments (0x41b50 : word) = Some W_3e404.
Proof. vm_refl. Qed.
Lemma D_3e404 : decode_any W_3e404 = Some (Branch BC_EQ 10 22 8056, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3e408 : bv 32 := 0x02054c63.
Lemma F_3e408 : fetch_word Ubsan.M.loaded_segments (0x41b54 : word) = Some W_3e408.
Proof. vm_refl. Qed.
Lemma D_3e408 : decode_any W_3e408 = Some (Branch BC_LT 10 0 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3e40c : bv 32 := 0x0089b583.
Lemma F_3e40c : fetch_word Ubsan.M.loaded_segments (0x41b58 : word) = Some W_3e40c.
Proof. vm_refl. Qed.
Lemma D_3e40c : decode_any W_3e40c = Some (Load SZ8 true 11 19 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3e410 : bv 32 := 0x00a5b633.
Lemma F_3e410 : fetch_word Ubsan.M.loaded_segments (0x41b5c : word) = Some W_3e410.
Proof. vm_refl. Qed.
Lemma D_3e410 : decode_any W_3e410 = Some (Op ALU_SLTU 12 11 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3e414 : bv 32 := 0x00461a13.
Lemma F_3e414 : fetch_word Ubsan.M.loaded_segments (0x41b60 : word) = Some W_3e414.
Proof. vm_refl. Qed.
Lemma D_3e414 : decode_any W_3e414 = Some (ShiftImm ALU_SLL 20 12 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3e418 : bv 32 := 0x01498a33.
Lemma F_3e418 : fetch_word Ubsan.M.loaded_segments (0x41b64 : word) = Some W_3e418.
Proof. vm_refl. Qed.
Lemma D_3e418 : decode_any W_3e418 = Some (Op ALU_ADD 20 19 20, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3e41c : bv 32 := 0x000a3703.
Lemma F_3e41c : fetch_word Ubsan.M.loaded_segments (0x41b68 : word) = Some W_3e41c.
Proof. vm_refl. Qed.
Lemma D_3e41c : decode_any W_3e41c = Some (Load SZ8 true 14 20 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3e420 : bv 32 := 0x40c006b3.
Lemma F_3e420 : fetch_word Ubsan.M.loaded_segments (0x41b6c : word) = Some W_3e420.
Proof. vm_refl. Qed.
Lemma D_3e420 : decode_any W_3e420 = Some (Op ALU_SUB 13 0 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3e424 : bv 32 := 0x00b6f6b3.
Lemma F_3e424 : fetch_word Ubsan.M.loaded_segments (0x41b70 : word) = Some W_3e424.
Proof. vm_refl. Qed.
Lemma D_3e424 : decode_any W_3e424 = Some (Op ALU_AND 13 13 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3e428 : bv 32 := 0x40d506b3.
Lemma F_3e428 : fetch_word Ubsan.M.loaded_segments (0x41b74 : word) = Some W_3e428.
Proof. vm_refl. Qed.
Lemma D_3e428 : decode_any W_3e428 = Some (Op ALU_SUB 13 10 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3e42c : bv 32 := 0x00d70733.
Lemma F_3e42c : fetch_word Ubsan.M.loaded_segments (0x41b78 : word) = Some W_3e42c.
Proof. vm_refl. Qed.
Lemma D_3e42c : decode_any W_3e42c = Some (Op ALU_ADD 14 14 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3e430 : bv 32 := 0x00ea3023.
Lemma F_3e430 : fetch_word Ubsan.M.loaded_segments (0x41b7c : word) = Some W_3e430.
Proof. vm_refl. Qed.
Lemma D_3e430 : decode_any W_3e430 = Some (Store SZ8 20 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3e434 : bv 32 := 0xf8a5fce3.
Lemma F_3e434 : fetch_word Ubsan.M.loaded_segments (0x41b80 : word) = Some W_3e434.
Proof. vm_refl. Qed.
Lemma D_3e434 : decode_any W_3e434 = Some (Branch BC_GEU 11 10 8088, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3e438 : bv 32 := 0x01800713.
Lemma F_3e438 : fetch_word Ubsan.M.loaded_segments (0x41b84 : word) = Some W_3e438.
Proof. vm_refl. Qed.
Lemma D_3e438 : decode_any W_3e438 = Some (OpImm ALU_ADD 14 0 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3e43c : bv 32 := 0xf95ff06f.
Lemma F_3e43c : fetch_word Ubsan.M.loaded_segments (0x41b88 : word) = Some W_3e43c.
Proof. vm_refl. Qed.
Lemma D_3e43c : decode_any W_3e43c = Some (Jal 0 2097044, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3e758 : bv 32 := 0xff010113.
Lemma F_3e758 : fetch_word Ubsan.M.loaded_segments (0x41ea4 : word) = Some W_3e758.
Proof. vm_refl. Qed.
Lemma D_3e758 : decode_any W_3e758 = Some (OpImm ALU_ADD 2 2 4080, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3e75c : bv 32 := 0x00113423.
Lemma F_3e75c : fetch_word Ubsan.M.loaded_segments (0x41ea8 : word) = Some W_3e75c.
Proof. vm_refl. Qed.
Lemma D_3e75c : decode_any W_3e75c = Some (Store SZ8 2 1 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3e760 : bv 32 := 0x00813023.
Lemma F_3e760 : fetch_word Ubsan.M.loaded_segments (0x41eac : word) = Some W_3e760.
Proof. vm_refl. Qed.
Lemma D_3e760 : decode_any W_3e760 = Some (Store SZ8 2 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3e764 : bv 32 := 0x0003c517.
Lemma F_3e764 : fetch_word Ubsan.M.loaded_segments (0x41eb0 : word) = Some W_3e764.
Proof. vm_refl. Qed.
Lemma D_3e764 : decode_any W_3e764 = Some (Auipc 10 60, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3e768 : bv 32 := 0x8c850413.
Lemma F_3e768 : fetch_word Ubsan.M.loaded_segments (0x41eb4 : word) = Some W_3e768.
Proof. vm_refl. Qed.
Lemma D_3e768 : decode_any W_3e768 = Some (OpImm ALU_ADD 8 10 2248, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3e76c : bv 32 := 0x00040513.
Lemma F_3e76c : fetch_word Ubsan.M.loaded_segments (0x41eb8 : word) = Some W_3e76c.
Proof. vm_refl. Qed.
Lemma D_3e76c : decode_any W_3e76c = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3e770 : bv 32 := 0x0c4050ef.
Lemma F_3e770 : fetch_word Ubsan.M.loaded_segments (0x41ebc : word) = Some W_3e770.
Proof. vm_refl. Qed.
Lemma D_3e770 : decode_any W_3e770 = Some (Jal 1 20676, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3e774 : bv 32 := 0x00840513.
Lemma F_3e774 : fetch_word Ubsan.M.loaded_segments (0x41ec0 : word) = Some W_3e774.
Proof. vm_refl. Qed.
Lemma D_3e774 : decode_any W_3e774 = Some (OpImm ALU_ADD 10 8 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3e778 : bv 32 := 0x00813083.
Lemma F_3e778 : fetch_word Ubsan.M.loaded_segments (0x41ec4 : word) = Some W_3e778.
Proof. vm_refl. Qed.
Lemma D_3e778 : decode_any W_3e778 = Some (Load SZ8 true 1 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3e77c : bv 32 := 0x00013403.
Lemma F_3e77c : fetch_word Ubsan.M.loaded_segments (0x41ec8 : word) = Some W_3e77c.
Proof. vm_refl. Qed.
Lemma D_3e77c : decode_any W_3e77c = Some (Load SZ8 true 8 2 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3e780 : bv 32 := 0x01010113.
Lemma F_3e780 : fetch_word Ubsan.M.loaded_segments (0x41ecc : word) = Some W_3e780.
Proof. vm_refl. Qed.
Lemma D_3e780 : decode_any W_3e780 = Some (OpImm ALU_ADD 2 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3e784 : bv 32 := 0x00008067.
Lemma F_3e784 : fetch_word Ubsan.M.loaded_segments (0x41ed0 : word) = Some W_3e784.
Proof. vm_refl. Qed.
Lemma D_3e784 : decode_any W_3e784 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.
