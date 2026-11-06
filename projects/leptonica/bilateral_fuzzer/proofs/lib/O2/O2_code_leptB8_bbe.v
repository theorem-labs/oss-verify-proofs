(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
(* [comment removed for export] *)

From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.H Require GcFlushS2.   (* [comment removed for export] *)
From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.leptonica.bilateral_fuzzer.images Require Import Plain.
Open Scope bv_scope.

(* [comment removed for export] *)
Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

(* [comment removed for export] *)
Definition W_1a144 : bv 32 := 0x00050663.
Lemma F_1a144 : fetch_word Plain.M.loaded_segments (0x1a19c : word) = Some W_1a144.
Proof. vm_refl. Qed.
Lemma D_1a144 : decode_any W_1a144 = Some (Branch BC_EQ 10 0 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1a148 : bv 32 := 0x00852503.
Lemma F_1a148 : fetch_word Plain.M.loaded_segments (0x1a1a0 : word) = Some W_1a148.
Proof. vm_refl. Qed.
Lemma D_1a148 : decode_any W_1a148 = Some (Load SZ4 true 10 10 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1a14c : bv 32 := 0x00008067.
Lemma F_1a14c : fetch_word Plain.M.loaded_segments (0x1a1a4 : word) = Some W_1a14c.
Proof. vm_refl. Qed.
Lemma D_1a14c : decode_any W_1a14c = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1a244 : bv 32 := 0x00050663.
Lemma F_1a244 : fetch_word Plain.M.loaded_segments (0x1a29c : word) = Some W_1a244.
Proof. vm_refl. Qed.
Lemma D_1a244 : decode_any W_1a244 = Some (Branch BC_EQ 10 0 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1a248 : bv 32 := 0x03053503.
Lemma F_1a248 : fetch_word Plain.M.loaded_segments (0x1a2a0 : word) = Some W_1a248.
Proof. vm_refl. Qed.
Lemma D_1a248 : decode_any W_1a248 = Some (Load SZ8 true 10 10 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1a24c : bv 32 := 0x00008067.
Lemma F_1a24c : fetch_word Plain.M.loaded_segments (0x1a2a4 : word) = Some W_1a24c.
Proof. vm_refl. Qed.
Lemma D_1a24c : decode_any W_1a24c = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2e98c : bv 32 := 0xfc010113.
Lemma F_2e98c : fetch_word Plain.M.loaded_segments (0x2e9e4 : word) = Some W_2e98c.
Proof. vm_refl. Qed.
Lemma D_2e98c : decode_any W_2e98c = Some (OpImm ALU_ADD 2 2 4032, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2e990 : bv 32 := 0x02113c23.
Lemma F_2e990 : fetch_word Plain.M.loaded_segments (0x2e9e8 : word) = Some W_2e990.
Proof. vm_refl. Qed.
Lemma D_2e990 : decode_any W_2e990 = Some (Store SZ8 2 1 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2e994 : bv 32 := 0x02813823.
Lemma F_2e994 : fetch_word Plain.M.loaded_segments (0x2e9ec : word) = Some W_2e994.
Proof. vm_refl. Qed.
Lemma D_2e994 : decode_any W_2e994 = Some (Store SZ8 2 8 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2e998 : bv 32 := 0x02913423.
Lemma F_2e998 : fetch_word Plain.M.loaded_segments (0x2e9f0 : word) = Some W_2e998.
Proof. vm_refl. Qed.
Lemma D_2e998 : decode_any W_2e998 = Some (Store SZ8 2 9 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2e99c : bv 32 := 0x02813027.
Lemma F_2e99c : fetch_word Plain.M.loaded_segments (0x2e9f4 : word) = Some W_2e99c.
Proof. vm_refl. Qed.
Lemma D_2e99c : decode_any W_2e99c = Some (FStore FMT_D 2 8 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2e9a0 : bv 32 := 0x00913c27.
Lemma F_2e9a0 : fetch_word Plain.M.loaded_segments (0x2e9f8 : word) = Some W_2e9a0.
Proof. vm_refl. Qed.
Lemma D_2e9a0 : decode_any W_2e9a0 = Some (FStore FMT_D 2 9 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2e9a4 : bv 32 := 0x04050c63.
Lemma F_2e9a4 : fetch_word Plain.M.loaded_segments (0x2e9fc : word) = Some W_2e9a4.
Proof. vm_refl. Qed.
Lemma D_2e9a4 : decode_any W_2e9a4 = Some (Branch BC_EQ 10 0 88, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2e9a8 : bv 32 := 0x20b58453.
Lemma F_2e9a8 : fetch_word Plain.M.loaded_segments (0x2ea00 : word) = Some W_2e9a8.
Proof. vm_refl. Qed.
Lemma D_2e9a8 : decode_any W_2e9a8 = Some (Fsgnj F_SGNJ FMT_S 8 11 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2e9ac : bv 32 := 0x20a504d3.
Lemma F_2e9ac : fetch_word Plain.M.loaded_segments (0x2ea04 : word) = Some W_2e9ac.
Proof. vm_refl. Qed.
Lemma D_2e9ac : decode_any W_2e9ac = Some (Fsgnj F_SGNJ FMT_S 9 10 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2e9b0 : bv 32 := 0x00050413.
Lemma F_2e9b0 : fetch_word Plain.M.loaded_segments (0x2ea08 : word) = Some W_2e9b0.
Proof. vm_refl. Qed.
Lemma D_2e9b0 : decode_any W_2e9b0 = Some (OpImm ALU_ADD 8 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2e9b4 : bv 32 := 0xf90eb0ef.
Lemma F_2e9b4 : fetch_word Plain.M.loaded_segments (0x2ea0c : word) = Some W_2e9b4.
Proof. vm_refl. Qed.
Lemma D_2e9b4 : decode_any W_2e9b4 = Some (Jal 1 2013072, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2e9b8 : bv 32 := 0x00800593.
Lemma F_2e9b8 : fetch_word Plain.M.loaded_segments (0x2ea10 : word) = Some W_2e9b8.
Proof. vm_refl. Qed.
Lemma D_2e9b8 : decode_any W_2e9b8 = Some (OpImm ALU_ADD 11 0 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2e9bc : bv 32 := 0x00b50663.
Lemma F_2e9bc : fetch_word Plain.M.loaded_segments (0x2ea14 : word) = Some W_2e9bc.
Proof. vm_refl. Qed.
Lemma D_2e9bc : decode_any W_2e9bc = Some (Branch BC_EQ 10 11 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2e9c0 : bv 32 := 0x02000593.
Lemma F_2e9c0 : fetch_word Plain.M.loaded_segments (0x2ea18 : word) = Some W_2e9c0.
Proof. vm_refl. Qed.
Lemma D_2e9c0 : decode_any W_2e9c0 = Some (OpImm ALU_ADD 11 0 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2e9c4 : bv 32 := 0x06b51063.
Lemma F_2e9c4 : fetch_word Plain.M.loaded_segments (0x2ea1c : word) = Some W_2e9c4.
Proof. vm_refl. Qed.
Lemma D_2e9c4 : decode_any W_2e9c4 = Some (Branch BC_NE 10 11 96, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2e9c8 : bv 32 := 0x00040513.
Lemma F_2e9c8 : fetch_word Plain.M.loaded_segments (0x2ea20 : word) = Some W_2e9c8.
Proof. vm_refl. Qed.
Lemma D_2e9c8 : decode_any W_2e9c8 = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2e9cc : bv 32 := 0x879eb0ef.
Lemma F_2e9cc : fetch_word Plain.M.loaded_segments (0x2ea24 : word) = Some W_2e9cc.
Proof. vm_refl. Qed.
Lemma D_2e9cc : decode_any W_2e9cc = Some (Jal 1 2013304, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2e9d0 : bv 32 := 0x06050e63.
Lemma F_2e9d0 : fetch_word Plain.M.loaded_segments (0x2ea28 : word) = Some W_2e9d0.
Proof. vm_refl. Qed.
Lemma D_2e9d0 : decode_any W_2e9d0 = Some (Branch BC_EQ 10 0 124, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2e9d4 : bv 32 := 0x0000a517.
Lemma F_2e9d4 : fetch_word Plain.M.loaded_segments (0x2ea2c : word) = Some W_2e9d4.
Proof. vm_refl. Qed.
Lemma D_2e9d4 : decode_any W_2e9d4 = Some (Auipc 10 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2e9d8 : bv 32 := 0xa4453503.
Lemma F_2e9d8 : fetch_word Plain.M.loaded_segments (0x2ea30 : word) = Some W_2e9d8.
Proof. vm_refl. Qed.
Lemma D_2e9d8 : decode_any W_2e9d8 = Some (Load SZ8 true 10 10 2628, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2e9dc : bv 32 := 0x00052503.
Lemma F_2e9dc : fetch_word Plain.M.loaded_segments (0x2ea34 : word) = Some W_2e9dc.
Proof. vm_refl. Qed.
Lemma D_2e9dc : decode_any W_2e9dc = Some (Load SZ4 true 10 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2e9e0 : bv 32 := 0x00500593.
Lemma F_2e9e0 : fetch_word Plain.M.loaded_segments (0x2ea38 : word) = Some W_2e9e0.
Proof. vm_refl. Qed.
Lemma D_2e9e0 : decode_any W_2e9e0 = Some (OpImm ALU_ADD 11 0 5, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2e9e4 : bv 32 := 0x14a5c263.
Lemma F_2e9e4 : fetch_word Plain.M.loaded_segments (0x2ea3c : word) = Some W_2e9e4.
Proof. vm_refl. Qed.
Lemma D_2e9e4 : decode_any W_2e9e4 = Some (Branch BC_LT 11 10 324, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2e9e8 : bv 32 := 0xfffe3517.
Lemma F_2e9e8 : fetch_word Plain.M.loaded_segments (0x2ea40 : word) = Some W_2e9e8.
Proof. vm_refl. Qed.
Lemma D_2e9e8 : decode_any W_2e9e8 = Some (Auipc 10 1048547, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2e9ec : bv 32 := 0xfffe3597.
Lemma F_2e9ec : fetch_word Plain.M.loaded_segments (0x2ea44 : word) = Some W_2e9ec.
Proof. vm_refl. Qed.
Lemma D_2e9ec : decode_any W_2e9ec = Some (Auipc 11 1048547, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2e9f0 : bv 32 := 0xb7850513.
Lemma F_2e9f0 : fetch_word Plain.M.loaded_segments (0x2ea48 : word) = Some W_2e9f0.
Proof. vm_refl. Qed.
Lemma D_2e9f0 : decode_any W_2e9f0 = Some (OpImm ALU_ADD 10 10 2936, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2e9f4 : bv 32 := 0x55058593.
Lemma F_2e9f4 : fetch_word Plain.M.loaded_segments (0x2ea4c : word) = Some W_2e9f4.
Proof. vm_refl. Qed.
Lemma D_2e9f4 : decode_any W_2e9f4 = Some (OpImm ALU_ADD 11 11 1360, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2e9f8 : bv 32 := 0x1100006f.
Lemma F_2e9f8 : fetch_word Plain.M.loaded_segments (0x2ea50 : word) = Some W_2e9f8.
Proof. vm_refl. Qed.
Lemma D_2e9f8 : decode_any W_2e9f8 = Some (Jal 0 272, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2ea24 : bv 32 := 0x0000a517.
Lemma F_2ea24 : fetch_word Plain.M.loaded_segments (0x2ea7c : word) = Some W_2ea24.
Proof. vm_refl. Qed.
Lemma D_2ea24 : decode_any W_2ea24 = Some (Auipc 10 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2ea28 : bv 32 := 0x9f453503.
Lemma F_2ea28 : fetch_word Plain.M.loaded_segments (0x2ea80 : word) = Some W_2ea28.
Proof. vm_refl. Qed.
Lemma D_2ea28 : decode_any W_2ea28 = Some (Load SZ8 true 10 10 2548, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2ea2c : bv 32 := 0x00052503.
Lemma F_2ea2c : fetch_word Plain.M.loaded_segments (0x2ea84 : word) = Some W_2ea2c.
Proof. vm_refl. Qed.
Lemma D_2ea2c : decode_any W_2ea2c = Some (Load SZ4 true 10 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2ea30 : bv 32 := 0x00500593.
Lemma F_2ea30 : fetch_word Plain.M.loaded_segments (0x2ea88 : word) = Some W_2ea30.
Proof. vm_refl. Qed.
Lemma D_2ea30 : decode_any W_2ea30 = Some (OpImm ALU_ADD 11 0 5, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2ea34 : bv 32 := 0x0ea5ca63.
Lemma F_2ea34 : fetch_word Plain.M.loaded_segments (0x2ea8c : word) = Some W_2ea34.
Proof. vm_refl. Qed.
Lemma D_2ea34 : decode_any W_2ea34 = Some (Branch BC_LT 11 10 244, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2ea38 : bv 32 := 0xfffe3517.
Lemma F_2ea38 : fetch_word Plain.M.loaded_segments (0x2ea90 : word) = Some W_2ea38.
Proof. vm_refl. Qed.
Lemma D_2ea38 : decode_any W_2ea38 = Some (Auipc 10 1048547, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2ea3c : bv 32 := 0xfffe3597.
Lemma F_2ea3c : fetch_word Plain.M.loaded_segments (0x2ea94 : word) = Some W_2ea3c.
Proof. vm_refl. Qed.
Lemma D_2ea3c : decode_any W_2ea3c = Some (Auipc 11 1048547, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2ea40 : bv 32 := 0xbb150513.
Lemma F_2ea40 : fetch_word Plain.M.loaded_segments (0x2ea98 : word) = Some W_2ea40.
Proof. vm_refl. Qed.
Lemma D_2ea40 : decode_any W_2ea40 = Some (OpImm ALU_ADD 10 10 2993, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2ea44 : bv 32 := 0x50058593.
Lemma F_2ea44 : fetch_word Plain.M.loaded_segments (0x2ea9c : word) = Some W_2ea44.
Proof. vm_refl. Qed.
Lemma D_2ea44 : decode_any W_2ea44 = Some (OpImm ALU_ADD 11 11 1280, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2ea48 : bv 32 := 0x0c00006f.
Lemma F_2ea48 : fetch_word Plain.M.loaded_segments (0x2eaa0 : word) = Some W_2ea48.
Proof. vm_refl. Qed.
Lemma D_2ea48 : decode_any W_2ea48 = Some (Jal 0 192, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2ea4c : bv 32 := 0xf00007d3.
Lemma F_2ea4c : fetch_word Plain.M.loaded_segments (0x2eaa4 : word) = Some W_2ea4c.
Proof. vm_refl. Qed.
Lemma D_2ea4c : decode_any W_2ea4c = Some (Fmv FMV_F_X FMT_S 15 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2ea50 : bv 32 := 0xa0f48553.
Lemma F_2ea50 : fetch_word Plain.M.loaded_segments (0x2eaa8 : word) = Some W_2ea50.
Proof. vm_refl. Qed.
Lemma D_2ea50 : decode_any W_2ea50 = Some (Fcmp F_LE FMT_S 10 9 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2ea54 : bv 32 := 0x06051463.
Lemma F_2ea54 : fetch_word Plain.M.loaded_segments (0x2eaac : word) = Some W_2ea54.
Proof. vm_refl. Qed.
Lemma D_2ea54 : decode_any W_2ea54 = Some (Branch BC_NE 10 0 104, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2ea58 : bv 32 := 0xa0f40553.
Lemma F_2ea58 : fetch_word Plain.M.loaded_segments (0x2eab0 : word) = Some W_2ea58.
Proof. vm_refl. Qed.
Lemma D_2ea58 : decode_any W_2ea58 = Some (Fcmp F_LE FMT_S 10 8 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2ea5c : bv 32 := 0x08051463.
Lemma F_2ea5c : fetch_word Plain.M.loaded_segments (0x2eab4 : word) = Some W_2ea5c.
Proof. vm_refl. Qed.
Lemma D_2ea5c : decode_any W_2ea5c = Some (Branch BC_NE 10 0 136, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2ea60 : bv 32 := 0x0094f7d3.
Lemma F_2ea60 : fetch_word Plain.M.loaded_segments (0x2eab8 : word) = Some W_2ea60.
Proof. vm_refl. Qed.
Lemma D_2ea60 : decode_any W_2ea60 = Some (Fari F_ADD FMT_S 15 9 9 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2ea64 : bv 32 := 0xc0079553.
Lemma F_2ea64 : fetch_word Plain.M.loaded_segments (0x2eabc : word) = Some W_2ea64.
Proof. vm_refl. Qed.
Lemma D_2ea64 : decode_any W_2ea64 = Some (Fcvt FC_W FC_S 10 15 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2ea68 : bv 32 := 0x3f8005b7.
Lemma F_2ea68 : fetch_word Plain.M.loaded_segments (0x2eac0 : word) = Some W_2ea68.
Proof. vm_refl. Qed.
Lemma D_2ea68 : decode_any W_2ea68 = Some (Lui 11 260096, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2ea6c : bv 32 := 0xf00585d3.
Lemma F_2ea6c : fetch_word Plain.M.loaded_segments (0x2eac4 : word) = Some W_2ea6c.
Proof. vm_refl. Qed.
Lemma D_2ea6c : decode_any W_2ea6c = Some (Fmv FMV_F_X FMT_S 11 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2ea70 : bv 32 := 0x00050593.
Lemma F_2ea70 : fetch_word Plain.M.loaded_segments (0x2eac8 : word) = Some W_2ea70.
Proof. vm_refl. Qed.
Lemma D_2ea70 : decode_any W_2ea70 = Some (OpImm ALU_ADD 11 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2ea74 : bv 32 := 0x20948553.
Lemma F_2ea74 : fetch_word Plain.M.loaded_segments (0x2eacc : word) = Some W_2ea74.
Proof. vm_refl. Qed.
Lemma D_2ea74 : decode_any W_2ea74 = Some (Fsgnj F_SGNJ FMT_S 10 9 9, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2ea78 : bv 32 := 0xd30fe0ef.
Lemma F_2ea78 : fetch_word Plain.M.loaded_segments (0x2ead0 : word) = Some W_2ea78.
Proof. vm_refl. Qed.
Lemma D_2ea78 : decode_any W_2ea78 = Some (Jal 1 2090288, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2ea7c : bv 32 := 0x00050493.
Lemma F_2ea7c : fetch_word Plain.M.loaded_segments (0x2ead4 : word) = Some W_2ea7c.
Proof. vm_refl. Qed.
Lemma D_2ea7c : decode_any W_2ea7c = Some (OpImm ALU_ADD 9 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2ea80 : bv 32 := 0x00a13823.
Lemma F_2ea80 : fetch_word Plain.M.loaded_segments (0x2ead8 : word) = Some W_2ea80.
Proof. vm_refl. Qed.
Lemma D_2ea80 : decode_any W_2ea80 = Some (Store SZ8 2 10 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2ea84 : bv 32 := 0x20840553.
Lemma F_2ea84 : fetch_word Plain.M.loaded_segments (0x2eadc : word) = Some W_2ea84.
Proof. vm_refl. Qed.
Lemma D_2ea84 : decode_any W_2ea84 = Some (Fsgnj F_SGNJ FMT_S 10 8 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2ea88 : bv 32 := 0x0c0000ef.
Lemma F_2ea88 : fetch_word Plain.M.loaded_segments (0x2eae0 : word) = Some W_2ea88.
Proof. vm_refl. Qed.
Lemma D_2ea88 : decode_any W_2ea88 = Some (Jal 1 192, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2ea8c : bv 32 := 0x00050613.
Lemma F_2ea8c : fetch_word Plain.M.loaded_segments (0x2eae4 : word) = Some W_2ea8c.
Proof. vm_refl. Qed.
Lemma D_2ea8c : decode_any W_2ea8c = Some (OpImm ALU_ADD 12 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2ea90 : bv 32 := 0x00a13423.
Lemma F_2ea90 : fetch_word Plain.M.loaded_segments (0x2eae8 : word) = Some W_2ea90.
Proof. vm_refl. Qed.
Lemma D_2ea90 : decode_any W_2ea90 = Some (Store SZ8 2 10 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2ea94 : bv 32 := 0x00040513.
Lemma F_2ea94 : fetch_word Plain.M.loaded_segments (0x2eaec : word) = Some W_2ea94.
Proof. vm_refl. Qed.
Lemma D_2ea94 : decode_any W_2ea94 = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2ea98 : bv 32 := 0x00048593.
Lemma F_2ea98 : fetch_word Plain.M.loaded_segments (0x2eaf0 : word) = Some W_2ea98.
Proof. vm_refl. Qed.
Lemma D_2ea98 : decode_any W_2ea98 = Some (OpImm ALU_ADD 11 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2ea9c : bv 32 := 0x865ff0ef.
Lemma F_2ea9c : fetch_word Plain.M.loaded_segments (0x2eaf4 : word) = Some W_2ea9c.
Proof. vm_refl. Qed.
Lemma D_2ea9c : decode_any W_2ea9c = Some (Jal 1 2095204, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2eaa0 : bv 32 := 0x00050413.
Lemma F_2eaa0 : fetch_word Plain.M.loaded_segments (0x2eaf8 : word) = Some W_2eaa0.
Proof. vm_refl. Qed.
Lemma D_2eaa0 : decode_any W_2eaa0 = Some (OpImm ALU_ADD 8 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2eaa4 : bv 32 := 0x01010513.
Lemma F_2eaa4 : fetch_word Plain.M.loaded_segments (0x2eafc : word) = Some W_2eaa4.
Proof. vm_refl. Qed.
Lemma D_2eaa4 : decode_any W_2eaa4 = Some (OpImm ALU_ADD 10 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2eaa8 : bv 32 := 0xd21fd0ef.
Lemma F_2eaa8 : fetch_word Plain.M.loaded_segments (0x2eb00 : word) = Some W_2eaa8.
Proof. vm_refl. Qed.
Lemma D_2eaa8 : decode_any W_2eaa8 = Some (Jal 1 2088224, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2eaac : bv 32 := 0x00810513.
Lemma F_2eaac : fetch_word Plain.M.loaded_segments (0x2eb04 : word) = Some W_2eaac.
Proof. vm_refl. Qed.
Lemma D_2eaac : decode_any W_2eaac = Some (OpImm ALU_ADD 10 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2eab0 : bv 32 := 0xd19fd0ef.
Lemma F_2eab0 : fetch_word Plain.M.loaded_segments (0x2eb08 : word) = Some W_2eab0.
Proof. vm_refl. Qed.
Lemma D_2eab0 : decode_any W_2eab0 = Some (Jal 1 2088216, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2eab4 : bv 32 := 0x00040513.
Lemma F_2eab4 : fetch_word Plain.M.loaded_segments (0x2eb0c : word) = Some W_2eab4.
Proof. vm_refl. Qed.
Lemma D_2eab4 : decode_any W_2eab4 = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2eab8 : bv 32 := 0x0740006f.
Lemma F_2eab8 : fetch_word Plain.M.loaded_segments (0x2eb10 : word) = Some W_2eab8.
Proof. vm_refl. Qed.
Lemma D_2eab8 : decode_any W_2eab8 = Some (Jal 0 116, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2eb08 : bv 32 := 0x00000613.
Lemma F_2eb08 : fetch_word Plain.M.loaded_segments (0x2eb60 : word) = Some W_2eb08.
Proof. vm_refl. Qed.
Lemma D_2eb08 : decode_any W_2eb08 = Some (OpImm ALU_ADD 12 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2eb0c : bv 32 := 0x03813083.
Lemma F_2eb0c : fetch_word Plain.M.loaded_segments (0x2eb64 : word) = Some W_2eb0c.
Proof. vm_refl. Qed.
Lemma D_2eb0c : decode_any W_2eb0c = Some (Load SZ8 true 1 2 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2eb10 : bv 32 := 0x03013403.
Lemma F_2eb10 : fetch_word Plain.M.loaded_segments (0x2eb68 : word) = Some W_2eb10.
Proof. vm_refl. Qed.
Lemma D_2eb10 : decode_any W_2eb10 = Some (Load SZ8 true 8 2 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2eb14 : bv 32 := 0x02813483.
Lemma F_2eb14 : fetch_word Plain.M.loaded_segments (0x2eb6c : word) = Some W_2eb14.
Proof. vm_refl. Qed.
Lemma D_2eb14 : decode_any W_2eb14 = Some (Load SZ8 true 9 2 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2eb18 : bv 32 := 0x02013407.
Lemma F_2eb18 : fetch_word Plain.M.loaded_segments (0x2eb70 : word) = Some W_2eb18.
Proof. vm_refl. Qed.
Lemma D_2eb18 : decode_any W_2eb18 = Some (FLoad FMT_D 8 2 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2eb1c : bv 32 := 0x01813487.
Lemma F_2eb1c : fetch_word Plain.M.loaded_segments (0x2eb74 : word) = Some W_2eb1c.
Proof. vm_refl. Qed.
Lemma D_2eb1c : decode_any W_2eb1c = Some (FLoad FMT_D 9 2 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2eb20 : bv 32 := 0x04010113.
Lemma F_2eb20 : fetch_word Plain.M.loaded_segments (0x2eb78 : word) = Some W_2eb20.
Proof. vm_refl. Qed.
Lemma D_2eb20 : decode_any W_2eb20 = Some (OpImm ALU_ADD 2 2 64, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2eb24 : bv 32 := 0x8f8e906f.
Lemma F_2eb24 : fetch_word Plain.M.loaded_segments (0x2eb7c : word) = Some W_2eb24.
Proof. vm_refl. Qed.
Lemma D_2eb24 : decode_any W_2eb24 = Some (Jal 0 2003192, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2eb2c : bv 32 := 0x03813083.
Lemma F_2eb2c : fetch_word Plain.M.loaded_segments (0x2eb84 : word) = Some W_2eb2c.
Proof. vm_refl. Qed.
Lemma D_2eb2c : decode_any W_2eb2c = Some (Load SZ8 true 1 2 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2eb30 : bv 32 := 0x03013403.
Lemma F_2eb30 : fetch_word Plain.M.loaded_segments (0x2eb88 : word) = Some W_2eb30.
Proof. vm_refl. Qed.
Lemma D_2eb30 : decode_any W_2eb30 = Some (Load SZ8 true 8 2 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2eb34 : bv 32 := 0x02813483.
Lemma F_2eb34 : fetch_word Plain.M.loaded_segments (0x2eb8c : word) = Some W_2eb34.
Proof. vm_refl. Qed.
Lemma D_2eb34 : decode_any W_2eb34 = Some (Load SZ8 true 9 2 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2eb38 : bv 32 := 0x02013407.
Lemma F_2eb38 : fetch_word Plain.M.loaded_segments (0x2eb90 : word) = Some W_2eb38.
Proof. vm_refl. Qed.
Lemma D_2eb38 : decode_any W_2eb38 = Some (FLoad FMT_D 8 2 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2eb3c : bv 32 := 0x01813487.
Lemma F_2eb3c : fetch_word Plain.M.loaded_segments (0x2eb94 : word) = Some W_2eb3c.
Proof. vm_refl. Qed.
Lemma D_2eb3c : decode_any W_2eb3c = Some (FLoad FMT_D 9 2 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2eb40 : bv 32 := 0x04010113.
Lemma F_2eb40 : fetch_word Plain.M.loaded_segments (0x2eb98 : word) = Some W_2eb40.
Proof. vm_refl. Qed.
Lemma D_2eb40 : decode_any W_2eb40 = Some (OpImm ALU_ADD 2 2 64, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2eb44 : bv 32 := 0x00008067.
Lemma F_2eb44 : fetch_word Plain.M.loaded_segments (0x2eb9c : word) = Some W_2eb44.
Proof. vm_refl. Qed.
Lemma D_2eb44 : decode_any W_2eb44 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.
