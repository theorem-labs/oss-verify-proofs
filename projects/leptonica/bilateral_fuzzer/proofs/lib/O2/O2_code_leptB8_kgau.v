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
Definition W_2cfa8 : bv 32 := 0xf7010113.
Lemma F_2cfa8 : fetch_word Plain.M.loaded_segments (0x2d000 : word) = Some W_2cfa8.
Proof. vm_refl. Qed.
Lemma D_2cfa8 : decode_any W_2cfa8 = Some (OpImm ALU_ADD 2 2 3952, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2cfac : bv 32 := 0x08113423.
Lemma F_2cfac : fetch_word Plain.M.loaded_segments (0x2d004 : word) = Some W_2cfac.
Proof. vm_refl. Qed.
Lemma D_2cfac : decode_any W_2cfac = Some (Store SZ8 2 1 136, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2cfb0 : bv 32 := 0x08813023.
Lemma F_2cfb0 : fetch_word Plain.M.loaded_segments (0x2d008 : word) = Some W_2cfb0.
Proof. vm_refl. Qed.
Lemma D_2cfb0 : decode_any W_2cfb0 = Some (Store SZ8 2 8 128, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2cfb4 : bv 32 := 0x06913c23.
Lemma F_2cfb4 : fetch_word Plain.M.loaded_segments (0x2d00c : word) = Some W_2cfb4.
Proof. vm_refl. Qed.
Lemma D_2cfb4 : decode_any W_2cfb4 = Some (Store SZ8 2 9 120, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2cfb8 : bv 32 := 0x07213823.
Lemma F_2cfb8 : fetch_word Plain.M.loaded_segments (0x2d010 : word) = Some W_2cfb8.
Proof. vm_refl. Qed.
Lemma D_2cfb8 : decode_any W_2cfb8 = Some (Store SZ8 2 18 112, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2cfbc : bv 32 := 0x07313423.
Lemma F_2cfbc : fetch_word Plain.M.loaded_segments (0x2d014 : word) = Some W_2cfbc.
Proof. vm_refl. Qed.
Lemma D_2cfbc : decode_any W_2cfbc = Some (Store SZ8 2 19 104, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2cfc0 : bv 32 := 0x07413023.
Lemma F_2cfc0 : fetch_word Plain.M.loaded_segments (0x2d018 : word) = Some W_2cfc0.
Proof. vm_refl. Qed.
Lemma D_2cfc0 : decode_any W_2cfc0 = Some (Store SZ8 2 20 96, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2cfc4 : bv 32 := 0x05513c23.
Lemma F_2cfc4 : fetch_word Plain.M.loaded_segments (0x2d01c : word) = Some W_2cfc4.
Proof. vm_refl. Qed.
Lemma D_2cfc4 : decode_any W_2cfc4 = Some (Store SZ8 2 21 88, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2cfc8 : bv 32 := 0x05613823.
Lemma F_2cfc8 : fetch_word Plain.M.loaded_segments (0x2d020 : word) = Some W_2cfc8.
Proof. vm_refl. Qed.
Lemma D_2cfc8 : decode_any W_2cfc8 = Some (Store SZ8 2 22 80, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2cfcc : bv 32 := 0x05713423.
Lemma F_2cfcc : fetch_word Plain.M.loaded_segments (0x2d024 : word) = Some W_2cfcc.
Proof. vm_refl. Qed.
Lemma D_2cfcc : decode_any W_2cfcc = Some (Store SZ8 2 23 72, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2cfd0 : bv 32 := 0x05813023.
Lemma F_2cfd0 : fetch_word Plain.M.loaded_segments (0x2d028 : word) = Some W_2cfd0.
Proof. vm_refl. Qed.
Lemma D_2cfd0 : decode_any W_2cfd0 = Some (Store SZ8 2 24 64, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2cfd4 : bv 32 := 0x03913c23.
Lemma F_2cfd4 : fetch_word Plain.M.loaded_segments (0x2d02c : word) = Some W_2cfd4.
Proof. vm_refl. Qed.
Lemma D_2cfd4 : decode_any W_2cfd4 = Some (Store SZ8 2 25 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2cfd8 : bv 32 := 0x03a13823.
Lemma F_2cfd8 : fetch_word Plain.M.loaded_segments (0x2d030 : word) = Some W_2cfd8.
Proof. vm_refl. Qed.
Lemma D_2cfd8 : decode_any W_2cfd8 = Some (Store SZ8 2 26 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2cfdc : bv 32 := 0x03b13423.
Lemma F_2cfdc : fetch_word Plain.M.loaded_segments (0x2d034 : word) = Some W_2cfdc.
Proof. vm_refl. Qed.
Lemma D_2cfdc : decode_any W_2cfdc = Some (Store SZ8 2 27 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2cfe0 : bv 32 := 0x02813027.
Lemma F_2cfe0 : fetch_word Plain.M.loaded_segments (0x2d038 : word) = Some W_2cfe0.
Proof. vm_refl. Qed.
Lemma D_2cfe0 : decode_any W_2cfe0 = Some (FStore FMT_D 2 8 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2cfe4 : bv 32 := 0x00913c27.
Lemma F_2cfe4 : fetch_word Plain.M.loaded_segments (0x2d03c : word) = Some W_2cfe4.
Proof. vm_refl. Qed.
Lemma D_2cfe4 : decode_any W_2cfe4 = Some (FStore FMT_D 2 9 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2cfe8 : bv 32 := 0x20b58453.
Lemma F_2cfe8 : fetch_word Plain.M.loaded_segments (0x2d040 : word) = Some W_2cfe8.
Proof. vm_refl. Qed.
Lemma D_2cfe8 : decode_any W_2cfe8 = Some (Fsgnj F_SGNJ FMT_S 8 11 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2cfec : bv 32 := 0x20a504d3.
Lemma F_2cfec : fetch_word Plain.M.loaded_segments (0x2d044 : word) = Some W_2cfec.
Proof. vm_refl. Qed.
Lemma D_2cfec : decode_any W_2cfec = Some (Fsgnj F_SGNJ FMT_S 9 10 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2cff0 : bv 32 := 0x00058413.
Lemma F_2cff0 : fetch_word Plain.M.loaded_segments (0x2d048 : word) = Some W_2cff0.
Proof. vm_refl. Qed.
Lemma D_2cff0 : decode_any W_2cff0 = Some (OpImm ALU_ADD 8 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2cff4 : bv 32 := 0x00050a13.
Lemma F_2cff4 : fetch_word Plain.M.loaded_segments (0x2d04c : word) = Some W_2cff4.
Proof. vm_refl. Qed.
Lemma D_2cff4 : decode_any W_2cff4 = Some (OpImm ALU_ADD 20 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2cff8 : bv 32 := 0x0015949b.
Lemma F_2cff8 : fetch_word Plain.M.loaded_segments (0x2d050 : word) = Some W_2cff8.
Proof. vm_refl. Qed.
Lemma D_2cff8 : decode_any W_2cff8 = Some (ShiftImm32 ALU_SLL 9 11 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2cffc : bv 32 := 0x0015199b.
Lemma F_2cffc : fetch_word Plain.M.loaded_segments (0x2d054 : word) = Some W_2cffc.
Proof. vm_refl. Qed.
Lemma D_2cffc : decode_any W_2cffc = Some (ShiftImm32 ALU_SLL 19 10 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2d000 : bv 32 := 0x00148593.
Lemma F_2d000 : fetch_word Plain.M.loaded_segments (0x2d058 : word) = Some W_2d000.
Proof. vm_refl. Qed.
Lemma D_2d000 : decode_any W_2d000 = Some (OpImm ALU_ADD 11 9 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2d004 : bv 32 := 0x00198513.
Lemma F_2d004 : fetch_word Plain.M.loaded_segments (0x2d05c : word) = Some W_2d004.
Proof. vm_refl. Qed.
Lemma D_2d004 : decode_any W_2d004 = Some (OpImm ALU_ADD 10 19 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2d008 : bv 32 := 0xd9cff0ef.
Lemma F_2d008 : fetch_word Plain.M.loaded_segments (0x2d060 : word) = Some W_2d008.
Proof. vm_refl. Qed.
Lemma D_2d008 : decode_any W_2d008 = Some (Jal 1 2094492, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2d00c : bv 32 := 0x10050c63.
Lemma F_2d00c : fetch_word Plain.M.loaded_segments (0x2d064 : word) = Some W_2d00c.
Proof. vm_refl. Qed.
Lemma D_2d00c : decode_any W_2d00c = Some (Branch BC_EQ 10 0 280, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2d010 : bv 32 := 0x00050913.
Lemma F_2d010 : fetch_word Plain.M.loaded_segments (0x2d068 : word) = Some W_2d010.
Proof. vm_refl. Qed.
Lemma D_2d010 : decode_any W_2d010 = Some (OpImm ALU_ADD 18 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2d014 : bv 32 := 0x01452423.
Lemma F_2d014 : fetch_word Plain.M.loaded_segments (0x2d06c : word) = Some W_2d014.
Proof. vm_refl. Qed.
Lemma D_2d014 : decode_any W_2d014 = Some (Store SZ4 10 20 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2d018 : bv 32 := 0x00852623.
Lemma F_2d018 : fetch_word Plain.M.loaded_segments (0x2d070 : word) = Some W_2d018.
Proof. vm_refl. Qed.
Lemma D_2d018 : decode_any W_2d018 = Some (Store SZ4 10 8 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2d01c : bv 32 := 0x160a4c63.
Lemma F_2d01c : fetch_word Plain.M.loaded_segments (0x2d074 : word) = Some W_2d01c.
Proof. vm_refl. Qed.
Lemma D_2d01c : decode_any W_2d01c = Some (Branch BC_LT 20 0 376, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2d020 : bv 32 := 0x01413423.
Lemma F_2d020 : fetch_word Plain.M.loaded_segments (0x2d078 : word) = Some W_2d020.
Proof. vm_refl. Qed.
Lemma D_2d020 : decode_any W_2d020 = Some (Store SZ8 2 20 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2d024 : bv 32 := 0x00000b13.
Lemma F_2d024 : fetch_word Plain.M.loaded_segments (0x2d07c : word) = Some W_2d024.
Proof. vm_refl. Qed.
Lemma D_2d024 : decode_any W_2d024 = Some (OpImm ALU_ADD 22 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2d028 : bv 32 := 0x420487d3.
Lemma F_2d028 : fetch_word Plain.M.loaded_segments (0x2d080 : word) = Some W_2d028.
Proof. vm_refl. Qed.
Lemma D_2d028 : decode_any W_2d028 = Some (Fcvt FC_D FC_S 15 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2d02c : bv 32 := 0x00902533.
Lemma F_2d02c : fetch_word Plain.M.loaded_segments (0x2d084 : word) = Some W_2d02c.
Proof. vm_refl. Qed.
Lemma D_2d02c : decode_any W_2d02c = Some (Op ALU_SLT 10 0 9, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2d030 : bv 32 := 0x0019e593.
Lemma F_2d030 : fetch_word Plain.M.loaded_segments (0x2d088 : word) = Some W_2d030.
Proof. vm_refl. Qed.
Lemma D_2d030 : decode_any W_2d030 = Some (OpImm ALU_OR 11 19 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2d034 : bv 32 := 0x00b13823.
Lemma F_2d034 : fetch_word Plain.M.loaded_segments (0x2d08c : word) = Some W_2d034.
Proof. vm_refl. Qed.
Lemma D_2d034 : decode_any W_2d034 = Some (Store SZ8 2 11 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2d038 : bv 32 := 0x0000b597.
Lemma F_2d038 : fetch_word Plain.M.loaded_segments (0x2d090 : word) = Some W_2d038.
Proof. vm_refl. Qed.
Lemma D_2d038 : decode_any W_2d038 = Some (Auipc 11 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2d03c : bv 32 := 0x00500c13.
Lemma F_2d03c : fetch_word Plain.M.loaded_segments (0x2d094 : word) = Some W_2d03c.
Proof. vm_refl. Qed.
Lemma D_2d03c : decode_any W_2d03c = Some (OpImm ALU_ADD 24 0 5, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2d040 : bv 32 := 0xfffe4617.
Lemma F_2d040 : fetch_word Plain.M.loaded_segments (0x2d098 : word) = Some W_2d040.
Proof. vm_refl. Qed.
Lemma D_2d040 : decode_any W_2d040 = Some (Auipc 12 1048548, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2d044 : bv 32 := 0xfffe4697.
Lemma F_2d044 : fetch_word Plain.M.loaded_segments (0x2d09c : word) = Some W_2d044.
Proof. vm_refl. Qed.
Lemma D_2d044 : decode_any W_2d044 = Some (Auipc 13 1048548, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2d048 : bv 32 := 0x02f7f753.
Lemma F_2d048 : fetch_word Plain.M.loaded_segments (0x2d0a0 : word) = Some W_2d048.
Proof. vm_refl. Qed.
Lemma D_2d048 : decode_any W_2d048 = Some (Fari F_ADD FMT_D 14 15 15 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2d04c : bv 32 := 0x40a00533.
Lemma F_2d04c : fetch_word Plain.M.loaded_segments (0x2d0a4 : word) = Some W_2d04c.
Proof. vm_refl. Qed.
Lemma D_2d04c : decode_any W_2d04c = Some (Op ALU_SUB 10 0 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2d050 : bv 32 := 0x3e05bc83.
Lemma F_2d050 : fetch_word Plain.M.loaded_segments (0x2d0a8 : word) = Some W_2d050.
Proof. vm_refl. Qed.
Lemma D_2d050 : decode_any W_2d050 = Some (Load SZ8 true 25 11 992, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2d054 : bv 32 := 0x5d160993.
Lemma F_2d054 : fetch_word Plain.M.loaded_segments (0x2d0ac : word) = Some W_2d054.
Proof. vm_refl. Qed.
Lemma D_2d054 : decode_any W_2d054 = Some (OpImm ALU_ADD 19 12 1489, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2d058 : bv 32 := 0xbe368a13.
Lemma F_2d058 : fetch_word Plain.M.loaded_segments (0x2d0b0 : word) = Some W_2d058.
Proof. vm_refl. Qed.
Lemma D_2d058 : decode_any W_2d058 = Some (OpImm ALU_ADD 20 13 3043, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2d05c : bv 32 := 0x12f774d3.
Lemma F_2d05c : fetch_word Plain.M.loaded_segments (0x2d0b4 : word) = Some W_2d05c.
Proof. vm_refl. Qed.
Lemma D_2d05c : decode_any W_2d05c = Some (Fari F_MUL FMT_D 9 14 15 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2d060 : bv 32 := 0x00957533.
Lemma F_2d060 : fetch_word Plain.M.loaded_segments (0x2d0b8 : word) = Some W_2d060.
Proof. vm_refl. Qed.
Lemma D_2d060 : decode_any W_2d060 = Some (Op ALU_AND 10 10 9, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2d064 : bv 32 := 0x00156d13.
Lemma F_2d064 : fetch_word Plain.M.loaded_segments (0x2d0bc : word) = Some W_2d064.
Proof. vm_refl. Qed.
Lemma D_2d064 : decode_any W_2d064 = Some (OpImm ALU_OR 26 10 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2d068 : bv 32 := 0xfffe4517.
Lemma F_2d068 : fetch_word Plain.M.loaded_segments (0x2d0c0 : word) = Some W_2d068.
Proof. vm_refl. Qed.
Lemma D_2d068 : decode_any W_2d068 = Some (Auipc 10 1048548, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2d06c : bv 32 := 0xcd450a93.
Lemma F_2d06c : fetch_word Plain.M.loaded_segments (0x2d0c4 : word) = Some W_2d06c.
Proof. vm_refl. Qed.
Lemma D_2d06c : decode_any W_2d06c = Some (OpImm ALU_ADD 21 10 3284, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2d070 : bv 32 := 0x0100006f.
Lemma F_2d070 : fetch_word Plain.M.loaded_segments (0x2d0c8 : word) = Some W_2d070.
Proof. vm_refl. Qed.
Lemma D_2d070 : decode_any W_2d070 = Some (Jal 0 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2d074 : bv 32 := 0x001b0b13.
Lemma F_2d074 : fetch_word Plain.M.loaded_segments (0x2d0cc : word) = Some W_2d074.
Proof. vm_refl. Qed.
Lemma D_2d074 : decode_any W_2d074 = Some (OpImm ALU_ADD 22 22 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2d078 : bv 32 := 0x01013503.
Lemma F_2d078 : fetch_word Plain.M.loaded_segments (0x2d0d0 : word) = Some W_2d078.
Proof. vm_refl. Qed.
Lemma D_2d078 : decode_any W_2d078 = Some (Load SZ8 true 10 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2d07c : bv 32 := 0x10ab0c63.
Lemma F_2d07c : fetch_word Plain.M.loaded_segments (0x2d0d4 : word) = Some W_2d07c.
Proof. vm_refl. Qed.
Lemma D_2d07c : decode_any W_2d07c = Some (Branch BC_EQ 22 10 280, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2d080 : bv 32 := 0xfe044ae3.
Lemma F_2d080 : fetch_word Plain.M.loaded_segments (0x2d0d8 : word) = Some W_2d080.
Proof. vm_refl. Qed.
Lemma D_2d080 : decode_any W_2d080 = Some (Branch BC_LT 8 0 8180, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2d084 : bv 32 := 0x00000d93.
Lemma F_2d084 : fetch_word Plain.M.loaded_segments (0x2d0dc : word) = Some W_2d084.
Proof. vm_refl. Qed.
Lemma D_2d084 : decode_any W_2d084 = Some (OpImm ALU_ADD 27 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2d088 : bv 32 := 0x00813503.
Lemma F_2d088 : fetch_word Plain.M.loaded_segments (0x2d0e0 : word) = Some W_2d088.
Proof. vm_refl. Qed.
Lemma D_2d088 : decode_any W_2d088 = Some (Load SZ8 true 10 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2d08c : bv 32 := 0x40ab053b.
Lemma F_2d08c : fetch_word Plain.M.loaded_segments (0x2d0e4 : word) = Some W_2d08c.
Proof. vm_refl. Qed.
Lemma D_2d08c : decode_any W_2d08c = Some (Op32 ALU_SUB 10 22 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2d090 : bv 32 := 0x02a504b3.
Lemma F_2d090 : fetch_word Plain.M.loaded_segments (0x2d0e8 : word) = Some W_2d090.
Proof. vm_refl. Qed.
Lemma D_2d090 : decode_any W_2d090 = Some (Mul M_MUL 9 10 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2d094 : bv 32 := 0x003b1b93.
Lemma F_2d094 : fetch_word Plain.M.loaded_segments (0x2d0ec : word) = Some W_2d094.
Proof. vm_refl. Qed.
Lemma D_2d094 : decode_any W_2d094 = Some (ShiftImm ALU_SLL 23 22 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2d098 : bv 32 := 0x0280006f.
Lemma F_2d098 : fetch_word Plain.M.loaded_segments (0x2d0f0 : word) = Some W_2d098.
Proof. vm_refl. Qed.
Lemma D_2d098 : decode_any W_2d098 = Some (Jal 0 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2d09c : bv 32 := 0x01093503.
Lemma F_2d09c : fetch_word Plain.M.loaded_segments (0x2d0f4 : word) = Some W_2d09c.
Proof. vm_refl. Qed.
Lemma D_2d09c : decode_any W_2d09c = Some (Load SZ8 true 10 18 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2d0a0 : bv 32 := 0x01750533.
Lemma F_2d0a0 : fetch_word Plain.M.loaded_segments (0x2d0f8 : word) = Some W_2d0a0.
Proof. vm_refl. Qed.
Lemma D_2d0a0 : decode_any W_2d0a0 = Some (Op ALU_ADD 10 10 23, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2d0a4 : bv 32 := 0x00053503.
Lemma F_2d0a4 : fetch_word Plain.M.loaded_segments (0x2d0fc : word) = Some W_2d0a4.
Proof. vm_refl. Qed.
Lemma D_2d0a4 : decode_any W_2d0a4 = Some (Load SZ8 true 10 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2d0a8 : bv 32 := 0x10a477d3.
Lemma F_2d0a8 : fetch_word Plain.M.loaded_segments (0x2d100 : word) = Some W_2d0a8.
Proof. vm_refl. Qed.
Lemma D_2d0a8 : decode_any W_2d0a8 = Some (Fari F_MUL FMT_S 15 8 10 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2d0ac : bv 32 := 0x002d9593.
Lemma F_2d0ac : fetch_word Plain.M.loaded_segments (0x2d104 : word) = Some W_2d0ac.
Proof. vm_refl. Qed.
Lemma D_2d0ac : decode_any W_2d0ac = Some (ShiftImm ALU_SLL 11 27 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2d0b0 : bv 32 := 0x00b50533.
Lemma F_2d0b0 : fetch_word Plain.M.loaded_segments (0x2d108 : word) = Some W_2d0b0.
Proof. vm_refl. Qed.
Lemma D_2d0b0 : decode_any W_2d0b0 = Some (Op ALU_ADD 10 10 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2d0b4 : bv 32 := 0x00f52027.
Lemma F_2d0b4 : fetch_word Plain.M.loaded_segments (0x2d10c : word) = Some W_2d0b4.
Proof. vm_refl. Qed.
Lemma D_2d0b4 : decode_any W_2d0b4 = Some (FStore FMT_S 10 15 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2d0b8 : bv 32 := 0x001d8d93.
Lemma F_2d0b8 : fetch_word Plain.M.loaded_segments (0x2d110 : word) = Some W_2d0b8.
Proof. vm_refl. Qed.
Lemma D_2d0b8 : decode_any W_2d0b8 = Some (OpImm ALU_ADD 27 27 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2d0bc : bv 32 := 0xfbad8ce3.
Lemma F_2d0bc : fetch_word Plain.M.loaded_segments (0x2d114 : word) = Some W_2d0bc.
Proof. vm_refl. Qed.
Lemma D_2d0bc : decode_any W_2d0bc = Some (Branch BC_EQ 27 26 8120, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2d0c0 : bv 32 := 0x408d853b.
Lemma F_2d0c0 : fetch_word Plain.M.loaded_segments (0x2d118 : word) = Some W_2d0c0.
Proof. vm_refl. Qed.
Lemma D_2d0c0 : decode_any W_2d0c0 = Some (Op32 ALU_SUB 10 27 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2d0c4 : bv 32 := 0x02a50533.
Lemma F_2d0c4 : fetch_word Plain.M.loaded_segments (0x2d11c : word) = Some W_2d0c4.
Proof. vm_refl. Qed.
Lemma D_2d0c4 : decode_any W_2d0c4 = Some (Mul M_MUL 10 10 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2d0c8 : bv 32 := 0x00950533.
Lemma F_2d0c8 : fetch_word Plain.M.loaded_segments (0x2d120 : word) = Some W_2d0c8.
Proof. vm_refl. Qed.
Lemma D_2d0c8 : decode_any W_2d0c8 = Some (Op ALU_ADD 10 10 9, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2d0cc : bv 32 := 0xd01577d3.
Lemma F_2d0cc : fetch_word Plain.M.loaded_segments (0x2d124 : word) = Some W_2d0cc.
Proof. vm_refl. Qed.
Lemma D_2d0cc : decode_any W_2d0cc = Some (Fcvt FC_S FC_WU 15 10 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2d0d0 : bv 32 := 0x20f797d3.
Lemma F_2d0d0 : fetch_word Plain.M.loaded_segments (0x2d128 : word) = Some W_2d0d0.
Proof. vm_refl. Qed.
Lemma D_2d0d0 : decode_any W_2d0d0 = Some (Fsgnj F_SGNJN FMT_S 15 15 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2d0d4 : bv 32 := 0x420787d3.
Lemma F_2d0d4 : fetch_word Plain.M.loaded_segments (0x2d12c : word) = Some W_2d0d4.
Proof. vm_refl. Qed.
Lemma D_2d0d4 : decode_any W_2d0d4 = Some (Fcvt FC_D FC_S 15 15 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2d0d8 : bv 32 := 0x1a97f7d3.
Lemma F_2d0d8 : fetch_word Plain.M.loaded_segments (0x2d130 : word) = Some W_2d0d8.
Proof. vm_refl. Qed.
Lemma D_2d0d8 : decode_any W_2d0d8 = Some (Fari F_DIV FMT_D 15 15 9 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2d0dc : bv 32 := 0x4017f553.
Lemma F_2d0dc : fetch_word Plain.M.loaded_segments (0x2d134 : word) = Some W_2d0dc.
Proof. vm_refl. Qed.
Lemma D_2d0dc : decode_any W_2d0dc = Some (Fcvt FC_S FC_D 10 15 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2d0e0 : bv 32 := 0x080040ef.
Lemma F_2d0e0 : fetch_word Plain.M.loaded_segments (0x2d138 : word) = Some W_2d0e0.
Proof. vm_refl. Qed.
Lemma D_2d0e0 : decode_any W_2d0e0 = Some (Jal 1 16512, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2d0e4 : bv 32 := 0x00092503.
Lemma F_2d0e4 : fetch_word Plain.M.loaded_segments (0x2d13c : word) = Some W_2d0e4.
Proof. vm_refl. Qed.
Lemma D_2d0e4 : decode_any W_2d0e4 = Some (Load SZ4 true 10 18 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2d0e8 : bv 32 := 0x02ab5063.
Lemma F_2d0e8 : fetch_word Plain.M.loaded_segments (0x2d140 : word) = Some W_2d0e8.
Proof. vm_refl. Qed.
Lemma D_2d0e8 : decode_any W_2d0e8 = Some (Branch BC_GE 22 10 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2d0ec : bv 32 := 0x00492503.
Lemma F_2d0ec : fetch_word Plain.M.loaded_segments (0x2d144 : word) = Some W_2d0ec.
Proof. vm_refl. Qed.
Lemma D_2d0ec : decode_any W_2d0ec = Some (Load SZ4 true 10 18 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2d0f0 : bv 32 := 0xfaadc6e3.
Lemma F_2d0f0 : fetch_word Plain.M.loaded_segments (0x2d148 : word) = Some W_2d0f0.
Proof. vm_refl. Qed.
Lemma D_2d0f0 : decode_any W_2d0f0 = Some (Branch BC_LT 27 10 8108, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2d194 : bv 32 := 0x00090513.
Lemma F_2d194 : fetch_word Plain.M.loaded_segments (0x2d1ec : word) = Some W_2d194.
Proof. vm_refl. Qed.
Lemma D_2d194 : decode_any W_2d194 = Some (OpImm ALU_ADD 10 18 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2d198 : bv 32 := 0x08813083.
Lemma F_2d198 : fetch_word Plain.M.loaded_segments (0x2d1f0 : word) = Some W_2d198.
Proof. vm_refl. Qed.
Lemma D_2d198 : decode_any W_2d198 = Some (Load SZ8 true 1 2 136, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2d19c : bv 32 := 0x08013403.
Lemma F_2d19c : fetch_word Plain.M.loaded_segments (0x2d1f4 : word) = Some W_2d19c.
Proof. vm_refl. Qed.
Lemma D_2d19c : decode_any W_2d19c = Some (Load SZ8 true 8 2 128, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2d1a0 : bv 32 := 0x07813483.
Lemma F_2d1a0 : fetch_word Plain.M.loaded_segments (0x2d1f8 : word) = Some W_2d1a0.
Proof. vm_refl. Qed.
Lemma D_2d1a0 : decode_any W_2d1a0 = Some (Load SZ8 true 9 2 120, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2d1a4 : bv 32 := 0x07013903.
Lemma F_2d1a4 : fetch_word Plain.M.loaded_segments (0x2d1fc : word) = Some W_2d1a4.
Proof. vm_refl. Qed.
Lemma D_2d1a4 : decode_any W_2d1a4 = Some (Load SZ8 true 18 2 112, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2d1a8 : bv 32 := 0x06813983.
Lemma F_2d1a8 : fetch_word Plain.M.loaded_segments (0x2d200 : word) = Some W_2d1a8.
Proof. vm_refl. Qed.
Lemma D_2d1a8 : decode_any W_2d1a8 = Some (Load SZ8 true 19 2 104, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2d1ac : bv 32 := 0x06013a03.
Lemma F_2d1ac : fetch_word Plain.M.loaded_segments (0x2d204 : word) = Some W_2d1ac.
Proof. vm_refl. Qed.
Lemma D_2d1ac : decode_any W_2d1ac = Some (Load SZ8 true 20 2 96, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2d1b0 : bv 32 := 0x05813a83.
Lemma F_2d1b0 : fetch_word Plain.M.loaded_segments (0x2d208 : word) = Some W_2d1b0.
Proof. vm_refl. Qed.
Lemma D_2d1b0 : decode_any W_2d1b0 = Some (Load SZ8 true 21 2 88, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2d1b4 : bv 32 := 0x05013b03.
Lemma F_2d1b4 : fetch_word Plain.M.loaded_segments (0x2d20c : word) = Some W_2d1b4.
Proof. vm_refl. Qed.
Lemma D_2d1b4 : decode_any W_2d1b4 = Some (Load SZ8 true 22 2 80, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2d1b8 : bv 32 := 0x04813b83.
Lemma F_2d1b8 : fetch_word Plain.M.loaded_segments (0x2d210 : word) = Some W_2d1b8.
Proof. vm_refl. Qed.
Lemma D_2d1b8 : decode_any W_2d1b8 = Some (Load SZ8 true 23 2 72, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2d1bc : bv 32 := 0x04013c03.
Lemma F_2d1bc : fetch_word Plain.M.loaded_segments (0x2d214 : word) = Some W_2d1bc.
Proof. vm_refl. Qed.
Lemma D_2d1bc : decode_any W_2d1bc = Some (Load SZ8 true 24 2 64, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2d1c0 : bv 32 := 0x03813c83.
Lemma F_2d1c0 : fetch_word Plain.M.loaded_segments (0x2d218 : word) = Some W_2d1c0.
Proof. vm_refl. Qed.
Lemma D_2d1c0 : decode_any W_2d1c0 = Some (Load SZ8 true 25 2 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2d1c4 : bv 32 := 0x03013d03.
Lemma F_2d1c4 : fetch_word Plain.M.loaded_segments (0x2d21c : word) = Some W_2d1c4.
Proof. vm_refl. Qed.
Lemma D_2d1c4 : decode_any W_2d1c4 = Some (Load SZ8 true 26 2 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2d1c8 : bv 32 := 0x02813d83.
Lemma F_2d1c8 : fetch_word Plain.M.loaded_segments (0x2d220 : word) = Some W_2d1c8.
Proof. vm_refl. Qed.
Lemma D_2d1c8 : decode_any W_2d1c8 = Some (Load SZ8 true 27 2 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2d1cc : bv 32 := 0x02013407.
Lemma F_2d1cc : fetch_word Plain.M.loaded_segments (0x2d224 : word) = Some W_2d1cc.
Proof. vm_refl. Qed.
Lemma D_2d1cc : decode_any W_2d1cc = Some (FLoad FMT_D 8 2 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2d1d0 : bv 32 := 0x01813487.
Lemma F_2d1d0 : fetch_word Plain.M.loaded_segments (0x2d228 : word) = Some W_2d1d0.
Proof. vm_refl. Qed.
Lemma D_2d1d0 : decode_any W_2d1d0 = Some (FLoad FMT_D 9 2 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2d1d4 : bv 32 := 0x09010113.
Lemma F_2d1d4 : fetch_word Plain.M.loaded_segments (0x2d22c : word) = Some W_2d1d4.
Proof. vm_refl. Qed.
Lemma D_2d1d4 : decode_any W_2d1d4 = Some (OpImm ALU_ADD 2 2 144, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2d1d8 : bv 32 := 0x00008067.
Lemma F_2d1d8 : fetch_word Plain.M.loaded_segments (0x2d230 : word) = Some W_2d1d8.
Proof. vm_refl. Qed.
Lemma D_2d1d8 : decode_any W_2d1d8 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.
