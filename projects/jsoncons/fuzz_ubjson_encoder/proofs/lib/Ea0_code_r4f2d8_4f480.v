(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
(* [comment removed for export] *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require BvWfKernel.

From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.jsoncons.fuzz_ubjson_encoder.images Require Import Asan.
Open Scope bv_scope.

Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

Definition W_659b4 : bv 32 := 0x060a0063.
Lemma F_659b4 : fetch_word Asan.M.loaded_segments (0x65a04 : word) = Some W_659b4.
Proof. vm_refl. Qed.
Lemma D_659b4 : decode_any W_659b4 = Some (Branch BC_EQ 20 0 96, 4%Z).
Proof. vm_refl. Qed.

Definition W_659b8 : bv 32 := 0x0a051c63.
Lemma F_659b8 : fetch_word Asan.M.loaded_segments (0x65a08 : word) = Some W_659b8.
Proof. vm_refl. Qed.
Lemma D_659b8 : decode_any W_659b8 = Some (Branch BC_NE 10 0 184, 4%Z).
Proof. vm_refl. Qed.

Definition W_659cc : bv 32 := 0xfbf48593.
Lemma F_659cc : fetch_word Asan.M.loaded_segments (0x65a1c : word) = Some W_659cc.
Proof. vm_refl. Qed.
Lemma D_659cc : decode_any W_659cc = Some (OpImm ALU_ADD 11 9 4031, 4%Z).
Proof. vm_refl. Qed.

Definition W_659d0 : bv 32 := 0xfbf00613.
Lemma F_659d0 : fetch_word Asan.M.loaded_segments (0x65a20 : word) = Some W_659d0.
Proof. vm_refl. Qed.
Lemma D_659d0 : decode_any W_659d0 = Some (OpImm ALU_ADD 12 0 4031, 4%Z).
Proof. vm_refl. Qed.

Definition W_659d4 : bv 32 := 0x12b67663.
Lemma F_659d4 : fetch_word Asan.M.loaded_segments (0x65a24 : word) = Some W_659d4.
Proof. vm_refl. Qed.
Lemma D_659d4 : decode_any W_659d4 = Some (Branch BC_GEU 12 11 300, 4%Z).
Proof. vm_refl. Qed.

Definition W_659d8 : bv 32 := 0x000d3597.
Lemma F_659d8 : fetch_word Asan.M.loaded_segments (0x65a28 : word) = Some W_659d8.
Proof. vm_refl. Qed.
Lemma D_659d8 : decode_any W_659d8 = Some (Auipc 11 211, 4%Z).
Proof. vm_refl. Qed.

Definition W_659dc : bv 32 := 0x7905b583.
Lemma F_659dc : fetch_word Asan.M.loaded_segments (0x65a2c : word) = Some W_659dc.
Proof. vm_refl. Qed.
Lemma D_659dc : decode_any W_659dc = Some (Load SZ8 true 11 11 1936, 4%Z).
Proof. vm_refl. Qed.

Definition W_659e0 : bv 32 := 0x009906b3.
Lemma F_659e0 : fetch_word Asan.M.loaded_segments (0x65a30 : word) = Some W_659e0.
Proof. vm_refl. Qed.
Lemma D_659e0 : decode_any W_659e0 = Some (Op ALU_ADD 13 18 9, 4%Z).
Proof. vm_refl. Qed.

Definition W_659e4 : bv 32 := 0x0005b603.
Lemma F_659e4 : fetch_word Asan.M.loaded_segments (0x65a34 : word) = Some W_659e4.
Proof. vm_refl. Qed.
Lemma D_659e4 : decode_any W_659e4 = Some (Load SZ8 true 12 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_659e8 : bv 32 := 0x00395593.
Lemma F_659e8 : fetch_word Asan.M.loaded_segments (0x65a38 : word) = Some W_659e8.
Proof. vm_refl. Qed.
Lemma D_659e8 : decode_any W_659e8 = Some (ShiftImm ALU_SRL 11 18 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_659ec : bv 32 := 0xfff68693.
Lemma F_659ec : fetch_word Asan.M.loaded_segments (0x65a3c : word) = Some W_659ec.
Proof. vm_refl. Qed.
Lemma D_659ec : decode_any W_659ec = Some (OpImm ALU_ADD 13 13 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_659f0 : bv 32 := 0x0036d713.
Lemma F_659f0 : fetch_word Asan.M.loaded_segments (0x65a40 : word) = Some W_659f0.
Proof. vm_refl. Qed.
Lemma D_659f0 : decode_any W_659f0 = Some (ShiftImm ALU_SRL 14 13 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_659f4 : bv 32 := 0x00b605b3.
Lemma F_659f4 : fetch_word Asan.M.loaded_segments (0x65a44 : word) = Some W_659f4.
Proof. vm_refl. Qed.
Lemma D_659f4 : decode_any W_659f4 = Some (Op ALU_ADD 11 12 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_659f8 : bv 32 := 0x00e60633.
Lemma F_659f8 : fetch_word Asan.M.loaded_segments (0x65a48 : word) = Some W_659f8.
Proof. vm_refl. Qed.
Lemma D_659f8 : decode_any W_659f8 = Some (Op ALU_ADD 12 12 14, 4%Z).
Proof. vm_refl. Qed.

Definition W_659fc : bv 32 := 0xff85f713.
Lemma F_659fc : fetch_word Asan.M.loaded_segments (0x65a4c : word) = Some W_659fc.
Proof. vm_refl. Qed.
Lemma D_659fc : decode_any W_659fc = Some (OpImm ALU_AND 14 11 4088, 4%Z).
Proof. vm_refl. Qed.

Definition W_65a00 : bv 32 := 0xff867793.
Lemma F_65a00 : fetch_word Asan.M.loaded_segments (0x65a50 : word) = Some W_65a00.
Proof. vm_refl. Qed.
Lemma D_65a00 : decode_any W_65a00 = Some (OpImm ALU_AND 15 12 4088, 4%Z).
Proof. vm_refl. Qed.

Definition W_65a04 : bv 32 := 0x00073703.
Lemma F_65a04 : fetch_word Asan.M.loaded_segments (0x65a54 : word) = Some W_65a04.
Proof. vm_refl. Qed.
Lemma D_65a04 : decode_any W_65a04 = Some (Load SZ8 true 14 14 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_65a08 : bv 32 := 0x0007b783.
Lemma F_65a08 : fetch_word Asan.M.loaded_segments (0x65a58 : word) = Some W_65a08.
Proof. vm_refl. Qed.
Lemma D_65a08 : decode_any W_65a08 = Some (Load SZ8 true 15 15 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_65a0c : bv 32 := 0x00e7e733.
Lemma F_65a0c : fetch_word Asan.M.loaded_segments (0x65a5c : word) = Some W_65a0c.
Proof. vm_refl. Qed.
Lemma D_65a0c : decode_any W_65a0c = Some (Op ALU_OR 14 15 14, 4%Z).
Proof. vm_refl. Qed.

Definition W_65a10 : bv 32 := 0x0e071c63.
Lemma F_65a10 : fetch_word Asan.M.loaded_segments (0x65a60 : word) = Some W_65a10.
Proof. vm_refl. Qed.
Lemma D_65a10 : decode_any W_65a10 = Some (Branch BC_NE 14 0 248, 4%Z).
Proof. vm_refl. Qed.

Definition W_65a70 : bv 32 := 0x412504b3.
Lemma F_65a70 : fetch_word Asan.M.loaded_segments (0x65ac0 : word) = Some W_65a70.
Proof. vm_refl. Qed.
Lemma D_65a70 : decode_any W_65a70 = Some (Op ALU_SUB 9 10 18, 4%Z).
Proof. vm_refl. Qed.

Definition W_65a74 : bv 32 := 0x00148493.
Lemma F_65a74 : fetch_word Asan.M.loaded_segments (0x65ac4 : word) = Some W_65a74.
Proof. vm_refl. Qed.
Lemma D_65a74 : decode_any W_65a74 = Some (OpImm ALU_ADD 9 9 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_65a78 : bv 32 := 0xfff94593.
Lemma F_65a78 : fetch_word Asan.M.loaded_segments (0x65ac8 : word) = Some W_65a78.
Proof. vm_refl. Qed.
Lemma D_65a78 : decode_any W_65a78 = Some (OpImm ALU_XOR 11 18 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_65a7c : bv 32 := 0x80040a13.
Lemma F_65a7c : fetch_word Asan.M.loaded_segments (0x65acc : word) = Some W_65a7c.
Proof. vm_refl. Qed.
Lemma D_65a7c : decode_any W_65a7c = Some (OpImm ALU_ADD 20 8 2048, 4%Z).
Proof. vm_refl. Qed.

Definition W_65a80 : bv 32 := 0xfb0a0a13.
Lemma F_65a80 : fetch_word Asan.M.loaded_segments (0x65ad0 : word) = Some W_65a80.
Proof. vm_refl. Qed.
Lemma D_65a80 : decode_any W_65a80 = Some (OpImm ALU_ADD 20 20 4016, 4%Z).
Proof. vm_refl. Qed.

Definition W_65a84 : bv 32 := 0xf495f4e3.
Lemma F_65a84 : fetch_word Asan.M.loaded_segments (0x65ad4 : word) = Some W_65a84.
Proof. vm_refl. Qed.
Lemma D_65a84 : decode_any W_65a84 = Some (Branch BC_GEU 11 9 8008, 4%Z).
Proof. vm_refl. Qed.

Definition W_65b00 : bv 32 := 0x02049e63.
Lemma F_65b00 : fetch_word Asan.M.loaded_segments (0x65b50 : word) = Some W_65b00.
Proof. vm_refl. Qed.
Lemma D_65b00 : decode_any W_65b00 = Some (Branch BC_NE 9 0 60, 4%Z).
Proof. vm_refl. Qed.

Definition W_65b3c : bv 32 := 0x00050a93.
Lemma F_65b3c : fetch_word Asan.M.loaded_segments (0x65b8c : word) = Some W_65b3c.
Proof. vm_refl. Qed.
Lemma D_65b3c : decode_any W_65b3c = Some (OpImm ALU_ADD 21 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_65b40 : bv 32 := 0x00090513.
Lemma F_65b40 : fetch_word Asan.M.loaded_segments (0x65b90 : word) = Some W_65b40.
Proof. vm_refl. Qed.
Lemma D_65b40 : decode_any W_65b40 = Some (OpImm ALU_ADD 10 18 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_65b44 : bv 32 := 0x00048593.
Lemma F_65b44 : fetch_word Asan.M.loaded_segments (0x65b94 : word) = Some W_65b44.
Proof. vm_refl. Qed.
Lemma D_65b44 : decode_any W_65b44 = Some (OpImm ALU_ADD 11 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_65b48 : bv 32 := 0x2ac160ef.
Lemma F_65b48 : fetch_word Asan.M.loaded_segments (0x65b98 : word) = Some W_65b48.
Proof. vm_refl. Qed.
Lemma D_65b48 : decode_any W_65b48 = Some (Jal 1 90796, 4%Z).
Proof. vm_refl. Qed.

Definition W_65b4c : bv 32 := 0x00050913.
Lemma F_65b4c : fetch_word Asan.M.loaded_segments (0x65b9c : word) = Some W_65b4c.
Proof. vm_refl. Qed.
Lemma D_65b4c : decode_any W_65b4c = Some (OpImm ALU_ADD 18 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_65b50 : bv 32 := 0x000a8513.
Lemma F_65b50 : fetch_word Asan.M.loaded_segments (0x65ba0 : word) = Some W_65b50.
Proof. vm_refl. Qed.
Lemma D_65b50 : decode_any W_65b50 = Some (OpImm ALU_ADD 10 21 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_65b54 : bv 32 := 0xec0900e3.
Lemma F_65b54 : fetch_word Asan.M.loaded_segments (0x65ba4 : word) = Some W_65b54.
Proof. vm_refl. Qed.
Lemma D_65b54 : decode_any W_65b54 = Some (Branch BC_EQ 18 0 7872, 4%Z).
Proof. vm_refl. Qed.
