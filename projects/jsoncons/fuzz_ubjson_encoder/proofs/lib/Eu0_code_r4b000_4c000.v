(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
(* [comment removed for export] *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require BvWfKernel.

From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.jsoncons.fuzz_ubjson_encoder.images Require Import Ubsan.
Open Scope bv_scope.

Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

Definition W_9cfb0 : bv 32 := 0x00008067.
Lemma F_9cfb0 : fetch_word Ubsan.M.loaded_segments (0x9d008 : word) = Some W_9cfb0.
Proof. vm_refl. Qed.
Lemma D_9cfb0 : decode_any W_9cfb0 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_9cfb4 : bv 32 := 0xe8010113.
Lemma F_9cfb4 : fetch_word Ubsan.M.loaded_segments (0x9d00c : word) = Some W_9cfb4.
Proof. vm_refl. Qed.
Lemma D_9cfb4 : decode_any W_9cfb4 = Some (OpImm ALU_ADD 2 2 3712, 4%Z).
Proof. vm_refl. Qed.

Definition W_9cfb8 : bv 32 := 0x16113c23.
Lemma F_9cfb8 : fetch_word Ubsan.M.loaded_segments (0x9d010 : word) = Some W_9cfb8.
Proof. vm_refl. Qed.
Lemma D_9cfb8 : decode_any W_9cfb8 = Some (Store SZ8 2 1 376, 4%Z).
Proof. vm_refl. Qed.

Definition W_9cfbc : bv 32 := 0x16813823.
Lemma F_9cfbc : fetch_word Ubsan.M.loaded_segments (0x9d014 : word) = Some W_9cfbc.
Proof. vm_refl. Qed.
Lemma D_9cfbc : decode_any W_9cfbc = Some (Store SZ8 2 8 368, 4%Z).
Proof. vm_refl. Qed.

Definition W_9cfc0 : bv 32 := 0x16913423.
Lemma F_9cfc0 : fetch_word Ubsan.M.loaded_segments (0x9d018 : word) = Some W_9cfc0.
Proof. vm_refl. Qed.
Lemma D_9cfc0 : decode_any W_9cfc0 = Some (Store SZ8 2 9 360, 4%Z).
Proof. vm_refl. Qed.

Definition W_9cfc4 : bv 32 := 0x17213023.
Lemma F_9cfc4 : fetch_word Ubsan.M.loaded_segments (0x9d01c : word) = Some W_9cfc4.
Proof. vm_refl. Qed.
Lemma D_9cfc4 : decode_any W_9cfc4 = Some (Store SZ8 2 18 352, 4%Z).
Proof. vm_refl. Qed.

Definition W_9cfc8 : bv 32 := 0x00058413.
Lemma F_9cfc8 : fetch_word Ubsan.M.loaded_segments (0x9d020 : word) = Some W_9cfc8.
Proof. vm_refl. Qed.
Lemma D_9cfc8 : decode_any W_9cfc8 = Some (OpImm ALU_ADD 8 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_9cfcc : bv 32 := 0x00050493.
Lemma F_9cfcc : fetch_word Ubsan.M.loaded_segments (0x9d024 : word) = Some W_9cfcc.
Proof. vm_refl. Qed.
Lemma D_9cfcc : decode_any W_9cfcc = Some (OpImm ALU_ADD 9 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_9cfd0 : bv 32 := 0x03010513.
Lemma F_9cfd0 : fetch_word Ubsan.M.loaded_segments (0x9d028 : word) = Some W_9cfd0.
Proof. vm_refl. Qed.
Lemma D_9cfd0 : decode_any W_9cfd0 = Some (OpImm ALU_ADD 10 2 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_9cfd4 : bv 32 := 0x13000613.
Lemma F_9cfd4 : fetch_word Ubsan.M.loaded_segments (0x9d02c : word) = Some W_9cfd4.
Proof. vm_refl. Qed.
Lemma D_9cfd4 : decode_any W_9cfd4 = Some (OpImm ALU_ADD 12 0 304, 4%Z).
Proof. vm_refl. Qed.

Definition W_9cfd8 : bv 32 := 0x00000593.
Lemma F_9cfd8 : fetch_word Ubsan.M.loaded_segments (0x9d030 : word) = Some W_9cfd8.
Proof. vm_refl. Qed.
Lemma D_9cfd8 : decode_any W_9cfd8 = Some (OpImm ALU_ADD 11 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_9cfdc : bv 32 := 0x554110ef.
Lemma F_9cfdc : fetch_word Ubsan.M.loaded_segments (0x9d034 : word) = Some W_9cfdc.
Proof. vm_refl. Qed.
Lemma D_9cfdc : decode_any W_9cfdc = Some (Jal 1 70996, 4%Z).
Proof. vm_refl. Qed.

Definition W_9cfe0 : bv 32 := 0x0001d517.
Lemma F_9cfe0 : fetch_word Ubsan.M.loaded_segments (0x9d038 : word) = Some W_9cfe0.
Proof. vm_refl. Qed.
Lemma D_9cfe0 : decode_any W_9cfe0 = Some (Auipc 10 29, 4%Z).
Proof. vm_refl. Qed.

Definition W_9cfe4 : bv 32 := 0xdc053503.
Lemma F_9cfe4 : fetch_word Ubsan.M.loaded_segments (0x9d03c : word) = Some W_9cfe4.
Proof. vm_refl. Qed.
Lemma D_9cfe4 : decode_any W_9cfe4 = Some (Load SZ8 true 10 10 3520, 4%Z).
Proof. vm_refl. Qed.

Definition W_9cfe8 : bv 32 := 0x00953023.
Lemma F_9cfe8 : fetch_word Ubsan.M.loaded_segments (0x9d040 : word) = Some W_9cfe8.
Proof. vm_refl. Qed.
Lemma D_9cfe8 : decode_any W_9cfe8 = Some (Store SZ8 10 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_9cfec : bv 32 := 0x0004b503.
Lemma F_9cfec : fetch_word Ubsan.M.loaded_segments (0x9d044 : word) = Some W_9cfec.
Proof. vm_refl. Qed.
Lemma D_9cfec : decode_any W_9cfec = Some (Load SZ8 true 10 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_9cff0 : bv 32 := 0x00848493.
Lemma F_9cff0 : fetch_word Ubsan.M.loaded_segments (0x9d048 : word) = Some W_9cff0.
Proof. vm_refl. Qed.
Lemma D_9cff0 : decode_any W_9cff0 = Some (OpImm ALU_ADD 9 9 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_9cff4 : bv 32 := 0xfe051ce3.
Lemma F_9cff4 : fetch_word Ubsan.M.loaded_segments (0x9d04c : word) = Some W_9cff4.
Proof. vm_refl. Qed.
Lemma D_9cff4 : decode_any W_9cff4 = Some (Branch BC_NE 10 0 8184, 4%Z).
Proof. vm_refl. Qed.

Definition W_9cff8 : bv 32 := 0x00050517.
Lemma F_9cff8 : fetch_word Ubsan.M.loaded_segments (0x9d050 : word) = Some W_9cff8.
Proof. vm_refl. Qed.
Lemma D_9cff8 : decode_any W_9cff8 = Some (Auipc 10 80, 4%Z).
Proof. vm_refl. Qed.

Definition W_9cffc : bv 32 := 0xe0050913.
Lemma F_9cffc : fetch_word Ubsan.M.loaded_segments (0x9d054 : word) = Some W_9cffc.
Proof. vm_refl. Qed.
Lemma D_9cffc : decode_any W_9cffc = Some (OpImm ALU_ADD 18 10 3584, 4%Z).
Proof. vm_refl. Qed.

Definition W_9d000 : bv 32 := 0x00993423.
Lemma F_9d000 : fetch_word Ubsan.M.loaded_segments (0x9d058 : word) = Some W_9d000.
Proof. vm_refl. Qed.
Lemma D_9d000 : decode_any W_9d000 = Some (Store SZ8 18 9 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_9d004 : bv 32 := 0x0004b583.
Lemma F_9d004 : fetch_word Ubsan.M.loaded_segments (0x9d05c : word) = Some W_9d004.
Proof. vm_refl. Qed.
Lemma D_9d004 : decode_any W_9d004 = Some (Load SZ8 true 11 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_9d008 : bv 32 := 0x04058c63.
Lemma F_9d008 : fetch_word Ubsan.M.loaded_segments (0x9d060 : word) = Some W_9d008.
Proof. vm_refl. Qed.
Lemma D_9d008 : decode_any W_9d008 = Some (Branch BC_EQ 11 0 88, 4%Z).
Proof. vm_refl. Qed.

Definition W_9d00c : bv 32 := 0x01048493.
Lemma F_9d00c : fetch_word Ubsan.M.loaded_segments (0x9d064 : word) = Some W_9d00c.
Proof. vm_refl. Qed.
Lemma D_9d00c : decode_any W_9d00c = Some (OpImm ALU_ADD 9 9 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_9d010 : bv 32 := 0x02500513.
Lemma F_9d010 : fetch_word Ubsan.M.loaded_segments (0x9d068 : word) = Some W_9d010.
Proof. vm_refl. Qed.
Lemma D_9d010 : decode_any W_9d010 = Some (OpImm ALU_ADD 10 0 37, 4%Z).
Proof. vm_refl. Qed.

Definition W_9d014 : bv 32 := 0x03010613.
Lemma F_9d014 : fetch_word Ubsan.M.loaded_segments (0x9d06c : word) = Some W_9d014.
Proof. vm_refl. Qed.
Lemma D_9d014 : decode_any W_9d014 = Some (OpImm ALU_ADD 12 2 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_9d018 : bv 32 := 0x0100006f.
Lemma F_9d018 : fetch_word Ubsan.M.loaded_segments (0x9d070 : word) = Some W_9d018.
Proof. vm_refl. Qed.
Lemma D_9d018 : decode_any W_9d018 = Some (Jal 0 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_9d01c : bv 32 := 0x0004b583.
Lemma F_9d01c : fetch_word Ubsan.M.loaded_segments (0x9d074 : word) = Some W_9d01c.
Proof. vm_refl. Qed.
Lemma D_9d01c : decode_any W_9d01c = Some (Load SZ8 true 11 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_9d020 : bv 32 := 0x01048493.
Lemma F_9d020 : fetch_word Ubsan.M.loaded_segments (0x9d078 : word) = Some W_9d020.
Proof. vm_refl. Qed.
Lemma D_9d020 : decode_any W_9d020 = Some (OpImm ALU_ADD 9 9 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_9d024 : bv 32 := 0x00058e63.
Lemma F_9d024 : fetch_word Ubsan.M.loaded_segments (0x9d07c : word) = Some W_9d024.
Proof. vm_refl. Qed.
Lemma D_9d024 : decode_any W_9d024 = Some (Branch BC_EQ 11 0 28, 4%Z).
Proof. vm_refl. Qed.

Definition W_9d028 : bv 32 := 0xfeb56ae3.
Lemma F_9d028 : fetch_word Ubsan.M.loaded_segments (0x9d080 : word) = Some W_9d028.
Proof. vm_refl. Qed.
Lemma D_9d028 : decode_any W_9d028 = Some (Branch BC_LTU 10 11 8180, 4%Z).
Proof. vm_refl. Qed.

Definition W_9d02c : bv 32 := 0xff84b683.
Lemma F_9d02c : fetch_word Ubsan.M.loaded_segments (0x9d084 : word) = Some W_9d02c.
Proof. vm_refl. Qed.
Lemma D_9d02c : decode_any W_9d02c = Some (Load SZ8 true 13 9 4088, 4%Z).
Proof. vm_refl. Qed.

Definition W_9d030 : bv 32 := 0x00359593.
Lemma F_9d030 : fetch_word Ubsan.M.loaded_segments (0x9d088 : word) = Some W_9d030.
Proof. vm_refl. Qed.
Lemma D_9d030 : decode_any W_9d030 = Some (ShiftImm ALU_SLL 11 11 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_9d034 : bv 32 := 0x00b605b3.
Lemma F_9d034 : fetch_word Ubsan.M.loaded_segments (0x9d08c : word) = Some W_9d034.
Proof. vm_refl. Qed.
Lemma D_9d034 : decode_any W_9d034 = Some (Op ALU_ADD 11 12 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_9d038 : bv 32 := 0x00d5b023.
Lemma F_9d038 : fetch_word Ubsan.M.loaded_segments (0x9d090 : word) = Some W_9d038.
Proof. vm_refl. Qed.
Lemma D_9d038 : decode_any W_9d038 = Some (Store SZ8 11 13 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_9d03c : bv 32 := 0xfe1ff06f.
Lemma F_9d03c : fetch_word Ubsan.M.loaded_segments (0x9d094 : word) = Some W_9d03c.
Proof. vm_refl. Qed.
Lemma D_9d03c : decode_any W_9d03c = Some (Jal 0 2097120, 4%Z).
Proof. vm_refl. Qed.

Definition W_9d040 : bv 32 := 0x0b013583.
Lemma F_9d040 : fetch_word Ubsan.M.loaded_segments (0x9d098 : word) = Some W_9d040.
Proof. vm_refl. Qed.
Lemma D_9d040 : decode_any W_9d040 = Some (Load SZ8 true 11 2 176, 4%Z).
Proof. vm_refl. Qed.

Definition W_9d044 : bv 32 := 0x13013503.
Lemma F_9d044 : fetch_word Ubsan.M.loaded_segments (0x9d09c : word) = Some W_9d044.
Proof. vm_refl. Qed.
Lemma D_9d044 : decode_any W_9d044 = Some (Load SZ8 true 10 2 304, 4%Z).
Proof. vm_refl. Qed.

Definition W_9d048 : bv 32 := 0x00050617.
Lemma F_9d048 : fetch_word Ubsan.M.loaded_segments (0x9d0a0 : word) = Some W_9d048.
Proof. vm_refl. Qed.
Lemma D_9d048 : decode_any W_9d048 = Some (Auipc 12 80, 4%Z).
Proof. vm_refl. Qed.

Definition W_9d04c : bv 32 := 0xe0b63c23.
Lemma F_9d04c : fetch_word Ubsan.M.loaded_segments (0x9d0a4 : word) = Some W_9d04c.
Proof. vm_refl. Qed.
Lemma D_9d04c : decode_any W_9d04c = Some (Store SZ8 12 11 3608, 4%Z).
Proof. vm_refl. Qed.

Definition W_9d050 : bv 32 := 0x00050c63.
Lemma F_9d050 : fetch_word Ubsan.M.loaded_segments (0x9d0a8 : word) = Some W_9d050.
Proof. vm_refl. Qed.
Lemma D_9d050 : decode_any W_9d050 = Some (Branch BC_EQ 10 0 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_9d068 : bv 32 := 0x06013503.
Lemma F_9d068 : fetch_word Ubsan.M.loaded_segments (0x9d0c0 : word) = Some W_9d068.
Proof. vm_refl. Qed.
Lemma D_9d068 : decode_any W_9d068 = Some (Load SZ8 true 10 2 96, 4%Z).
Proof. vm_refl. Qed.

Definition W_9d06c : bv 32 := 0x02a93823.
Lemma F_9d06c : fetch_word Ubsan.M.loaded_segments (0x9d0c4 : word) = Some W_9d06c.
Proof. vm_refl. Qed.
Lemma D_9d06c : decode_any W_9d06c = Some (Store SZ8 18 10 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_9d070 : bv 32 := 0x00041463.
Lemma F_9d070 : fetch_word Ubsan.M.loaded_segments (0x9d0c8 : word) = Some W_9d070.
Proof. vm_refl. Qed.
Lemma D_9d070 : decode_any W_9d070 = Some (Branch BC_NE 8 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_9d078 : bv 32 := 0x00041663.
Lemma F_9d078 : fetch_word Ubsan.M.loaded_segments (0x9d0d0 : word) = Some W_9d078.
Proof. vm_refl. Qed.
Lemma D_9d078 : decode_any W_9d078 = Some (Branch BC_NE 8 0 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_9d084 : bv 32 := 0x0001d517.
Lemma F_9d084 : fetch_word Ubsan.M.loaded_segments (0x9d0dc : word) = Some W_9d084.
Proof. vm_refl. Qed.
Lemma D_9d084 : decode_any W_9d084 = Some (Auipc 10 29, 4%Z).
Proof. vm_refl. Qed.

Definition W_9d088 : bv 32 := 0xd2453583.
Lemma F_9d088 : fetch_word Ubsan.M.loaded_segments (0x9d0e0 : word) = Some W_9d088.
Proof. vm_refl. Qed.
Lemma D_9d088 : decode_any W_9d088 = Some (Load SZ8 true 11 10 3364, 4%Z).
Proof. vm_refl. Qed.

Definition W_9d08c : bv 32 := 0x0001d517.
Lemma F_9d08c : fetch_word Ubsan.M.loaded_segments (0x9d0e4 : word) = Some W_9d08c.
Proof. vm_refl. Qed.
Lemma D_9d08c : decode_any W_9d08c = Some (Auipc 10 29, 4%Z).
Proof. vm_refl. Qed.

Definition W_9d090 : bv 32 := 0xd2453503.
Lemma F_9d090 : fetch_word Ubsan.M.loaded_segments (0x9d0e8 : word) = Some W_9d090.
Proof. vm_refl. Qed.
Lemma D_9d090 : decode_any W_9d090 = Some (Load SZ8 true 10 10 3364, 4%Z).
Proof. vm_refl. Qed.

Definition W_9d094 : bv 32 := 0x0085b023.
Lemma F_9d094 : fetch_word Ubsan.M.loaded_segments (0x9d0ec : word) = Some W_9d094.
Proof. vm_refl. Qed.
Lemma D_9d094 : decode_any W_9d094 = Some (Store SZ8 11 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_9d098 : bv 32 := 0x00140593.
Lemma F_9d098 : fetch_word Ubsan.M.loaded_segments (0x9d0f0 : word) = Some W_9d098.
Proof. vm_refl. Qed.
Lemma D_9d098 : decode_any W_9d098 = Some (OpImm ALU_ADD 11 8 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_9d09c : bv 32 := 0x00853023.
Lemma F_9d09c : fetch_word Ubsan.M.loaded_segments (0x9d0f4 : word) = Some W_9d09c.
Proof. vm_refl. Qed.
Lemma D_9d09c : decode_any W_9d09c = Some (Store SZ8 10 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_9d0a0 : bv 32 := 0x02f00613.
Lemma F_9d0a0 : fetch_word Ubsan.M.loaded_segments (0x9d0f8 : word) = Some W_9d0a0.
Proof. vm_refl. Qed.
Lemma D_9d0a0 : decode_any W_9d0a0 = Some (OpImm ALU_ADD 12 0 47, 4%Z).
Proof. vm_refl. Qed.

Definition W_9d0a4 : bv 32 := 0x00c0006f.
Lemma F_9d0a4 : fetch_word Ubsan.M.loaded_segments (0x9d0fc : word) = Some W_9d0a4.
Proof. vm_refl. Qed.
Lemma D_9d0a4 : decode_any W_9d0a4 = Some (Jal 0 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_9d0a8 : bv 32 := 0x00b53023.
Lemma F_9d0a8 : fetch_word Ubsan.M.loaded_segments (0x9d100 : word) = Some W_9d0a8.
Proof. vm_refl. Qed.
Lemma D_9d0a8 : decode_any W_9d0a8 = Some (Store SZ8 10 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_9d0ac : bv 32 := 0x00158593.
Lemma F_9d0ac : fetch_word Ubsan.M.loaded_segments (0x9d104 : word) = Some W_9d0ac.
Proof. vm_refl. Qed.
Lemma D_9d0ac : decode_any W_9d0ac = Some (OpImm ALU_ADD 11 11 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_9d0b0 : bv 32 := 0xfff5c683.
Lemma F_9d0b0 : fetch_word Ubsan.M.loaded_segments (0x9d108 : word) = Some W_9d0b0.
Proof. vm_refl. Qed.
Lemma D_9d0b0 : decode_any W_9d0b0 = Some (Load SZ1 false 13 11 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_9d0b4 : bv 32 := 0xfec68ae3.
Lemma F_9d0b4 : fetch_word Ubsan.M.loaded_segments (0x9d10c : word) = Some W_9d0b4.
Proof. vm_refl. Qed.
Lemma D_9d0b4 : decode_any W_9d0b4 = Some (Branch BC_EQ 13 12 8180, 4%Z).
Proof. vm_refl. Qed.

Definition W_9d0b8 : bv 32 := 0xfe069ae3.
Lemma F_9d0b8 : fetch_word Ubsan.M.loaded_segments (0x9d110 : word) = Some W_9d0b8.
Proof. vm_refl. Qed.
Lemma D_9d0b8 : decode_any W_9d0b8 = Some (Branch BC_NE 13 0 8180, 4%Z).
Proof. vm_refl. Qed.

Definition W_9d0bc : bv 32 := 0x03010513.
Lemma F_9d0bc : fetch_word Ubsan.M.loaded_segments (0x9d114 : word) = Some W_9d0bc.
Proof. vm_refl. Qed.
Lemma D_9d0bc : decode_any W_9d0bc = Some (OpImm ALU_ADD 10 2 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_9d0c0 : bv 32 := 0x214000ef.
Lemma F_9d0c0 : fetch_word Ubsan.M.loaded_segments (0x9d118 : word) = Some W_9d0c0.
Proof. vm_refl. Qed.
Lemma D_9d0c0 : decode_any W_9d0c0 = Some (Jal 1 532, 4%Z).
Proof. vm_refl. Qed.

Definition W_9d0c4 : bv 32 := 0x0f813503.
Lemma F_9d0c4 : fetch_word Ubsan.M.loaded_segments (0x9d11c : word) = Some W_9d0c4.
Proof. vm_refl. Qed.
Lemma D_9d0c4 : decode_any W_9d0c4 = Some (Load SZ8 true 10 2 248, 4%Z).
Proof. vm_refl. Qed.

Definition W_9d0c8 : bv 32 := 0x1ad000ef.
Lemma F_9d0c8 : fetch_word Ubsan.M.loaded_segments (0x9d120 : word) = Some W_9d0c8.
Proof. vm_refl. Qed.
Lemma D_9d0c8 : decode_any W_9d0c8 = Some (Jal 1 2476, 4%Z).
Proof. vm_refl. Qed.

Definition W_9d0cc : bv 32 := 0x08813503.
Lemma F_9d0cc : fetch_word Ubsan.M.loaded_segments (0x9d124 : word) = Some W_9d0cc.
Proof. vm_refl. Qed.
Lemma D_9d0cc : decode_any W_9d0cc = Some (Load SZ8 true 10 2 136, 4%Z).
Proof. vm_refl. Qed.

Definition W_9d0d0 : bv 32 := 0x09013583.
Lemma F_9d0d0 : fetch_word Ubsan.M.loaded_segments (0x9d128 : word) = Some W_9d0d0.
Proof. vm_refl. Qed.
Lemma D_9d0d0 : decode_any W_9d0d0 = Some (Load SZ8 true 11 2 144, 4%Z).
Proof. vm_refl. Qed.

Definition W_9d0d4 : bv 32 := 0x00b51c63.
Lemma F_9d0d4 : fetch_word Ubsan.M.loaded_segments (0x9d12c : word) = Some W_9d0d4.
Proof. vm_refl. Qed.
Lemma D_9d0d4 : decode_any W_9d0d4 = Some (Branch BC_NE 10 11 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_9d0d8 : bv 32 := 0x09813503.
Lemma F_9d0d8 : fetch_word Ubsan.M.loaded_segments (0x9d130 : word) = Some W_9d0d8.
Proof. vm_refl. Qed.
Lemma D_9d0d8 : decode_any W_9d0d8 = Some (Load SZ8 true 10 2 152, 4%Z).
Proof. vm_refl. Qed.

Definition W_9d0dc : bv 32 := 0x0a013583.
Lemma F_9d0dc : fetch_word Ubsan.M.loaded_segments (0x9d134 : word) = Some W_9d0dc.
Proof. vm_refl. Qed.
Lemma D_9d0dc : decode_any W_9d0dc = Some (Load SZ8 true 11 2 160, 4%Z).
Proof. vm_refl. Qed.

Definition W_9d0e0 : bv 32 := 0x00b51663.
Lemma F_9d0e0 : fetch_word Ubsan.M.loaded_segments (0x9d138 : word) = Some W_9d0e0.
Proof. vm_refl. Qed.
Lemma D_9d0e0 : decode_any W_9d0e0 = Some (Branch BC_NE 10 11 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_9d0e4 : bv 32 := 0x0e813503.
Lemma F_9d0e4 : fetch_word Ubsan.M.loaded_segments (0x9d13c : word) = Some W_9d0e4.
Proof. vm_refl. Qed.
Lemma D_9d0e4 : decode_any W_9d0e4 = Some (Load SZ8 true 10 2 232, 4%Z).
Proof. vm_refl. Qed.

Definition W_9d0e8 : bv 32 := 0x0e050063.
Lemma F_9d0e8 : fetch_word Ubsan.M.loaded_segments (0x9d140 : word) = Some W_9d0e8.
Proof. vm_refl. Qed.
Lemma D_9d0e8 : decode_any W_9d0e8 = Some (Branch BC_EQ 10 0 224, 4%Z).
Proof. vm_refl. Qed.

Definition W_9d1c8 : bv 32 := 0x17813083.
Lemma F_9d1c8 : fetch_word Ubsan.M.loaded_segments (0x9d220 : word) = Some W_9d1c8.
Proof. vm_refl. Qed.
Lemma D_9d1c8 : decode_any W_9d1c8 = Some (Load SZ8 true 1 2 376, 4%Z).
Proof. vm_refl. Qed.

Definition W_9d1cc : bv 32 := 0x17013403.
Lemma F_9d1cc : fetch_word Ubsan.M.loaded_segments (0x9d224 : word) = Some W_9d1cc.
Proof. vm_refl. Qed.
Lemma D_9d1cc : decode_any W_9d1cc = Some (Load SZ8 true 8 2 368, 4%Z).
Proof. vm_refl. Qed.

Definition W_9d1d0 : bv 32 := 0x16813483.
Lemma F_9d1d0 : fetch_word Ubsan.M.loaded_segments (0x9d228 : word) = Some W_9d1d0.
Proof. vm_refl. Qed.
Lemma D_9d1d0 : decode_any W_9d1d0 = Some (Load SZ8 true 9 2 360, 4%Z).
Proof. vm_refl. Qed.

Definition W_9d1d4 : bv 32 := 0x16013903.
Lemma F_9d1d4 : fetch_word Ubsan.M.loaded_segments (0x9d22c : word) = Some W_9d1d4.
Proof. vm_refl. Qed.
Lemma D_9d1d4 : decode_any W_9d1d4 = Some (Load SZ8 true 18 2 352, 4%Z).
Proof. vm_refl. Qed.

Definition W_9d1d8 : bv 32 := 0x18010113.
Lemma F_9d1d8 : fetch_word Ubsan.M.loaded_segments (0x9d230 : word) = Some W_9d1d8.
Proof. vm_refl. Qed.
Lemma D_9d1d8 : decode_any W_9d1d8 = Some (OpImm ALU_ADD 2 2 384, 4%Z).
Proof. vm_refl. Qed.

Definition W_9d1dc : bv 32 := 0x00008067.
Lemma F_9d1dc : fetch_word Ubsan.M.loaded_segments (0x9d234 : word) = Some W_9d1dc.
Proof. vm_refl. Qed.
Lemma D_9d1dc : decode_any W_9d1dc = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_9d1e0 : bv 32 := 0xfe010113.
Lemma F_9d1e0 : fetch_word Ubsan.M.loaded_segments (0x9d238 : word) = Some W_9d1e0.
Proof. vm_refl. Qed.
Lemma D_9d1e0 : decode_any W_9d1e0 = Some (OpImm ALU_ADD 2 2 4064, 4%Z).
Proof. vm_refl. Qed.

Definition W_9d1e4 : bv 32 := 0x00113c23.
Lemma F_9d1e4 : fetch_word Ubsan.M.loaded_segments (0x9d23c : word) = Some W_9d1e4.
Proof. vm_refl. Qed.
Lemma D_9d1e4 : decode_any W_9d1e4 = Some (Store SZ8 2 1 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_9d1e8 : bv 32 := 0x00813823.
Lemma F_9d1e8 : fetch_word Ubsan.M.loaded_segments (0x9d240 : word) = Some W_9d1e8.
Proof. vm_refl. Qed.
Lemma D_9d1e8 : decode_any W_9d1e8 = Some (Store SZ8 2 8 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_9d1ec : bv 32 := 0x00913423.
Lemma F_9d1ec : fetch_word Ubsan.M.loaded_segments (0x9d244 : word) = Some W_9d1ec.
Proof. vm_refl. Qed.
Lemma D_9d1ec : decode_any W_9d1ec = Some (Store SZ8 2 9 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_9d1f0 : bv 32 := 0xdc1ff0ef.
Lemma F_9d1f0 : fetch_word Ubsan.M.loaded_segments (0x9d248 : word) = Some W_9d1f0.
Proof. vm_refl. Qed.
Lemma D_9d1f0 : decode_any W_9d1f0 = Some (Jal 1 2096576, 4%Z).
Proof. vm_refl. Qed.

Definition W_9d1f4 : bv 32 := 0x0001d517.
Lemma F_9d1f4 : fetch_word Ubsan.M.loaded_segments (0x9d24c : word) = Some W_9d1f4.
Proof. vm_refl. Qed.
Lemma D_9d1f4 : decode_any W_9d1f4 = Some (Auipc 10 29, 4%Z).
Proof. vm_refl. Qed.

Definition W_9d1f8 : bv 32 := 0x0001d597.
Lemma F_9d1f8 : fetch_word Ubsan.M.loaded_segments (0x9d250 : word) = Some W_9d1f8.
Proof. vm_refl. Qed.
Lemma D_9d1f8 : decode_any W_9d1f8 = Some (Auipc 11 29, 4%Z).
Proof. vm_refl. Qed.

Definition W_9d1fc : bv 32 := 0xbc453403.
Lemma F_9d1fc : fetch_word Ubsan.M.loaded_segments (0x9d254 : word) = Some W_9d1fc.
Proof. vm_refl. Qed.
Lemma D_9d1fc : decode_any W_9d1fc = Some (Load SZ8 true 8 10 3012, 4%Z).
Proof. vm_refl. Qed.

Definition W_9d200 : bv 32 := 0xbc85b483.
Lemma F_9d200 : fetch_word Ubsan.M.loaded_segments (0x9d258 : word) = Some W_9d200.
Proof. vm_refl. Qed.
Lemma D_9d200 : decode_any W_9d200 = Some (Load SZ8 true 9 11 3016, 4%Z).
Proof. vm_refl. Qed.

Definition W_9d204 : bv 32 := 0x0084fa63.
Lemma F_9d204 : fetch_word Ubsan.M.loaded_segments (0x9d25c : word) = Some W_9d204.
Proof. vm_refl. Qed.
Lemma D_9d204 : decode_any W_9d204 = Some (Branch BC_GEU 9 8 20, 4%Z).
Proof. vm_refl. Qed.

Definition W_9d208 : bv 32 := 0x0004b503.
Lemma F_9d208 : fetch_word Ubsan.M.loaded_segments (0x9d260 : word) = Some W_9d208.
Proof. vm_refl. Qed.
Lemma D_9d208 : decode_any W_9d208 = Some (Load SZ8 true 10 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_9d20c : bv 32 := 0x000500e7.
Lemma F_9d20c : fetch_word Ubsan.M.loaded_segments (0x9d264 : word) = Some W_9d20c.
Proof. vm_refl. Qed.
Lemma D_9d20c : decode_any W_9d20c = Some (Jalr 1 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_9d210 : bv 32 := 0x00848493.
Lemma F_9d210 : fetch_word Ubsan.M.loaded_segments (0x9d268 : word) = Some W_9d210.
Proof. vm_refl. Qed.
Lemma D_9d210 : decode_any W_9d210 = Some (OpImm ALU_ADD 9 9 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_9d214 : bv 32 := 0xfe84eae3.
Lemma F_9d214 : fetch_word Ubsan.M.loaded_segments (0x9d26c : word) = Some W_9d214.
Proof. vm_refl. Qed.
Lemma D_9d214 : decode_any W_9d214 = Some (Branch BC_LTU 9 8 8180, 4%Z).
Proof. vm_refl. Qed.

Definition W_9d218 : bv 32 := 0x01813083.
Lemma F_9d218 : fetch_word Ubsan.M.loaded_segments (0x9d270 : word) = Some W_9d218.
Proof. vm_refl. Qed.
Lemma D_9d218 : decode_any W_9d218 = Some (Load SZ8 true 1 2 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_9d21c : bv 32 := 0x01013403.
Lemma F_9d21c : fetch_word Ubsan.M.loaded_segments (0x9d274 : word) = Some W_9d21c.
Proof. vm_refl. Qed.
Lemma D_9d21c : decode_any W_9d21c = Some (Load SZ8 true 8 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_9d220 : bv 32 := 0x00813483.
Lemma F_9d220 : fetch_word Ubsan.M.loaded_segments (0x9d278 : word) = Some W_9d220.
Proof. vm_refl. Qed.
Lemma D_9d220 : decode_any W_9d220 = Some (Load SZ8 true 9 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_9d224 : bv 32 := 0x02010113.
Lemma F_9d224 : fetch_word Ubsan.M.loaded_segments (0x9d27c : word) = Some W_9d224.
Proof. vm_refl. Qed.
Lemma D_9d224 : decode_any W_9d224 = Some (OpImm ALU_ADD 2 2 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_9d228 : bv 32 := 0x00008067.
Lemma F_9d228 : fetch_word Ubsan.M.loaded_segments (0x9d280 : word) = Some W_9d228.
Proof. vm_refl. Qed.
Lemma D_9d228 : decode_any W_9d228 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_9d22c : bv 32 := 0xfe010113.
Lemma F_9d22c : fetch_word Ubsan.M.loaded_segments (0x9d284 : word) = Some W_9d22c.
Proof. vm_refl. Qed.
Lemma D_9d22c : decode_any W_9d22c = Some (OpImm ALU_ADD 2 2 4064, 4%Z).
Proof. vm_refl. Qed.

Definition W_9d230 : bv 32 := 0x00113c23.
Lemma F_9d230 : fetch_word Ubsan.M.loaded_segments (0x9d288 : word) = Some W_9d230.
Proof. vm_refl. Qed.
Lemma D_9d230 : decode_any W_9d230 = Some (Store SZ8 2 1 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_9d234 : bv 32 := 0x00813823.
Lemma F_9d234 : fetch_word Ubsan.M.loaded_segments (0x9d28c : word) = Some W_9d234.
Proof. vm_refl. Qed.
Lemma D_9d234 : decode_any W_9d234 = Some (Store SZ8 2 8 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_9d238 : bv 32 := 0x00913423.
Lemma F_9d238 : fetch_word Ubsan.M.loaded_segments (0x9d290 : word) = Some W_9d238.
Proof. vm_refl. Qed.
Lemma D_9d238 : decode_any W_9d238 = Some (Store SZ8 2 9 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_9d23c : bv 32 := 0x01213023.
Lemma F_9d23c : fetch_word Ubsan.M.loaded_segments (0x9d294 : word) = Some W_9d23c.
Proof. vm_refl. Qed.
Lemma D_9d23c : decode_any W_9d23c = Some (Store SZ8 2 18 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_9d240 : bv 32 := 0x00060413.
Lemma F_9d240 : fetch_word Ubsan.M.loaded_segments (0x9d298 : word) = Some W_9d240.
Proof. vm_refl. Qed.
Lemma D_9d240 : decode_any W_9d240 = Some (OpImm ALU_ADD 8 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_9d244 : bv 32 := 0x00058493.
Lemma F_9d244 : fetch_word Ubsan.M.loaded_segments (0x9d29c : word) = Some W_9d244.
Proof. vm_refl. Qed.
Lemma D_9d244 : decode_any W_9d244 = Some (OpImm ALU_ADD 9 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_9d248 : bv 32 := 0x00050913.
Lemma F_9d248 : fetch_word Ubsan.M.loaded_segments (0x9d2a0 : word) = Some W_9d248.
Proof. vm_refl. Qed.
Lemma D_9d248 : decode_any W_9d248 = Some (OpImm ALU_ADD 18 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_9d24c : bv 32 := 0x00063583.
Lemma F_9d24c : fetch_word Ubsan.M.loaded_segments (0x9d2a4 : word) = Some W_9d24c.
Proof. vm_refl. Qed.
Lemma D_9d24c : decode_any W_9d24c = Some (Load SZ8 true 11 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_9d250 : bv 32 := 0x00349513.
Lemma F_9d250 : fetch_word Ubsan.M.loaded_segments (0x9d2a8 : word) = Some W_9d250.
Proof. vm_refl. Qed.
Lemma D_9d250 : decode_any W_9d250 = Some (ShiftImm ALU_SLL 10 9 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_9d254 : bv 32 := 0x00a60533.
Lemma F_9d254 : fetch_word Ubsan.M.loaded_segments (0x9d2ac : word) = Some W_9d254.
Proof. vm_refl. Qed.
Lemma D_9d254 : decode_any W_9d254 = Some (Op ALU_ADD 10 12 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_9d258 : bv 32 := 0x00850513.
Lemma F_9d258 : fetch_word Ubsan.M.loaded_segments (0x9d2b0 : word) = Some W_9d258.
Proof. vm_refl. Qed.
Lemma D_9d258 : decode_any W_9d258 = Some (OpImm ALU_ADD 10 10 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_9d25c : bv 32 := 0xd59ff0ef.
Lemma F_9d25c : fetch_word Ubsan.M.loaded_segments (0x9d2b4 : word) = Some W_9d25c.
Proof. vm_refl. Qed.
Lemma D_9d25c : decode_any W_9d25c = Some (Jal 1 2096472, 4%Z).
Proof. vm_refl. Qed.

Definition W_9d260 : bv 32 := 0x00000517.
Lemma F_9d260 : fetch_word Ubsan.M.loaded_segments (0x9d2b8 : word) = Some W_9d260.
Proof. vm_refl. Qed.
Lemma D_9d260 : decode_any W_9d260 = Some (Auipc 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_9d264 : bv 32 := 0x02c50313.
Lemma F_9d264 : fetch_word Ubsan.M.loaded_segments (0x9d2bc : word) = Some W_9d264.
Proof. vm_refl. Qed.
Lemma D_9d264 : decode_any W_9d264 = Some (OpImm ALU_ADD 6 10 44, 4%Z).
Proof. vm_refl. Qed.

Definition W_9d268 : bv 32 := 0x00090513.
Lemma F_9d268 : fetch_word Ubsan.M.loaded_segments (0x9d2c0 : word) = Some W_9d268.
Proof. vm_refl. Qed.
Lemma D_9d268 : decode_any W_9d268 = Some (OpImm ALU_ADD 10 18 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_9d26c : bv 32 := 0x00048593.
Lemma F_9d26c : fetch_word Ubsan.M.loaded_segments (0x9d2c4 : word) = Some W_9d26c.
Proof. vm_refl. Qed.
Lemma D_9d26c : decode_any W_9d26c = Some (OpImm ALU_ADD 11 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_9d270 : bv 32 := 0x00040613.
Lemma F_9d270 : fetch_word Ubsan.M.loaded_segments (0x9d2c8 : word) = Some W_9d270.
Proof. vm_refl. Qed.
Lemma D_9d270 : decode_any W_9d270 = Some (OpImm ALU_ADD 12 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_9d274 : bv 32 := 0x01813083.
Lemma F_9d274 : fetch_word Ubsan.M.loaded_segments (0x9d2cc : word) = Some W_9d274.
Proof. vm_refl. Qed.
Lemma D_9d274 : decode_any W_9d274 = Some (Load SZ8 true 1 2 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_9d278 : bv 32 := 0x01013403.
Lemma F_9d278 : fetch_word Ubsan.M.loaded_segments (0x9d2d0 : word) = Some W_9d278.
Proof. vm_refl. Qed.
Lemma D_9d278 : decode_any W_9d278 = Some (Load SZ8 true 8 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_9d27c : bv 32 := 0x00813483.
Lemma F_9d27c : fetch_word Ubsan.M.loaded_segments (0x9d2d4 : word) = Some W_9d27c.
Proof. vm_refl. Qed.
Lemma D_9d27c : decode_any W_9d27c = Some (Load SZ8 true 9 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_9d280 : bv 32 := 0x00013903.
Lemma F_9d280 : fetch_word Ubsan.M.loaded_segments (0x9d2d8 : word) = Some W_9d280.
Proof. vm_refl. Qed.
Lemma D_9d280 : decode_any W_9d280 = Some (Load SZ8 true 18 2 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_9d284 : bv 32 := 0x02010113.
Lemma F_9d284 : fetch_word Ubsan.M.loaded_segments (0x9d2dc : word) = Some W_9d284.
Proof. vm_refl. Qed.
Lemma D_9d284 : decode_any W_9d284 = Some (OpImm ALU_ADD 2 2 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_9d288 : bv 32 := 0x00030067.
Lemma F_9d288 : fetch_word Ubsan.M.loaded_segments (0x9d2e0 : word) = Some W_9d288.
Proof. vm_refl. Qed.
Lemma D_9d288 : decode_any W_9d288 = Some (Jalr 0 6 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_9d28c : bv 32 := 0xfd010113.
Lemma F_9d28c : fetch_word Ubsan.M.loaded_segments (0x9d2e4 : word) = Some W_9d28c.
Proof. vm_refl. Qed.
Lemma D_9d28c : decode_any W_9d28c = Some (OpImm ALU_ADD 2 2 4048, 4%Z).
Proof. vm_refl. Qed.

Definition W_9d290 : bv 32 := 0x02113423.
Lemma F_9d290 : fetch_word Ubsan.M.loaded_segments (0x9d2e8 : word) = Some W_9d290.
Proof. vm_refl. Qed.
Lemma D_9d290 : decode_any W_9d290 = Some (Store SZ8 2 1 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_9d294 : bv 32 := 0x02813023.
Lemma F_9d294 : fetch_word Ubsan.M.loaded_segments (0x9d2ec : word) = Some W_9d294.
Proof. vm_refl. Qed.
Lemma D_9d294 : decode_any W_9d294 = Some (Store SZ8 2 8 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_9d298 : bv 32 := 0x00913c23.
Lemma F_9d298 : fetch_word Ubsan.M.loaded_segments (0x9d2f0 : word) = Some W_9d298.
Proof. vm_refl. Qed.
Lemma D_9d298 : decode_any W_9d298 = Some (Store SZ8 2 9 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_9d29c : bv 32 := 0x01213823.
Lemma F_9d29c : fetch_word Ubsan.M.loaded_segments (0x9d2f4 : word) = Some W_9d29c.
Proof. vm_refl. Qed.
Lemma D_9d29c : decode_any W_9d29c = Some (Store SZ8 2 18 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_9d2a0 : bv 32 := 0x01313423.
Lemma F_9d2a0 : fetch_word Ubsan.M.loaded_segments (0x9d2f8 : word) = Some W_9d2a0.
Proof. vm_refl. Qed.
Lemma D_9d2a0 : decode_any W_9d2a0 = Some (Store SZ8 2 19 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_9d2a4 : bv 32 := 0x00060413.
Lemma F_9d2a4 : fetch_word Ubsan.M.loaded_segments (0x9d2fc : word) = Some W_9d2a4.
Proof. vm_refl. Qed.
Lemma D_9d2a4 : decode_any W_9d2a4 = Some (OpImm ALU_ADD 8 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_9d2a8 : bv 32 := 0x00058493.
Lemma F_9d2a8 : fetch_word Ubsan.M.loaded_segments (0x9d300 : word) = Some W_9d2a8.
Proof. vm_refl. Qed.
Lemma D_9d2a8 : decode_any W_9d2a8 = Some (OpImm ALU_ADD 9 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_9d2ac : bv 32 := 0x00050913.
Lemma F_9d2ac : fetch_word Ubsan.M.loaded_segments (0x9d304 : word) = Some W_9d2ac.
Proof. vm_refl. Qed.
Lemma D_9d2ac : decode_any W_9d2ac = Some (OpImm ALU_ADD 18 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_9d2b0 : bv 32 := 0x00359513.
Lemma F_9d2b0 : fetch_word Ubsan.M.loaded_segments (0x9d308 : word) = Some W_9d2b0.
Proof. vm_refl. Qed.
Lemma D_9d2b0 : decode_any W_9d2b0 = Some (ShiftImm ALU_SLL 10 11 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_9d2b4 : bv 32 := 0x00a60533.
Lemma F_9d2b4 : fetch_word Ubsan.M.loaded_segments (0x9d30c : word) = Some W_9d2b4.
Proof. vm_refl. Qed.
Lemma D_9d2b4 : decode_any W_9d2b4 = Some (Op ALU_ADD 10 12 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_9d2b8 : bv 32 := 0x00850993.
Lemma F_9d2b8 : fetch_word Ubsan.M.loaded_segments (0x9d310 : word) = Some W_9d2b8.
Proof. vm_refl. Qed.
Lemma D_9d2b8 : decode_any W_9d2b8 = Some (OpImm ALU_ADD 19 10 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_9d2bc : bv 32 := 0xf25ff0ef.
Lemma F_9d2bc : fetch_word Ubsan.M.loaded_segments (0x9d314 : word) = Some W_9d2bc.
Proof. vm_refl. Qed.
Lemma D_9d2bc : decode_any W_9d2bc = Some (Jal 1 2096932, 4%Z).
Proof. vm_refl. Qed.

Definition W_9d2c0 : bv 32 := 0x00048513.
Lemma F_9d2c0 : fetch_word Ubsan.M.loaded_segments (0x9d318 : word) = Some W_9d2c0.
Proof. vm_refl. Qed.
Lemma D_9d2c0 : decode_any W_9d2c0 = Some (OpImm ALU_ADD 10 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_9d2c4 : bv 32 := 0x00040593.
Lemma F_9d2c4 : fetch_word Ubsan.M.loaded_segments (0x9d31c : word) = Some W_9d2c4.
Proof. vm_refl. Qed.
Lemma D_9d2c4 : decode_any W_9d2c4 = Some (OpImm ALU_ADD 11 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_9d2c8 : bv 32 := 0x00098613.
Lemma F_9d2c8 : fetch_word Ubsan.M.loaded_segments (0x9d320 : word) = Some W_9d2c8.
Proof. vm_refl. Qed.
Lemma D_9d2c8 : decode_any W_9d2c8 = Some (OpImm ALU_ADD 12 19 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_9d2cc : bv 32 := 0x000900e7.
Lemma F_9d2cc : fetch_word Ubsan.M.loaded_segments (0x9d324 : word) = Some W_9d2cc.
Proof. vm_refl. Qed.
Lemma D_9d2cc : decode_any W_9d2cc = Some (Jalr 1 18 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_9d2d4 : bv 32 := 0xfc010113.
Lemma F_9d2d4 : fetch_word Ubsan.M.loaded_segments (0x9d32c : word) = Some W_9d2d4.
Proof. vm_refl. Qed.
Lemma D_9d2d4 : decode_any W_9d2d4 = Some (OpImm ALU_ADD 2 2 4032, 4%Z).
Proof. vm_refl. Qed.

Definition W_9d2d8 : bv 32 := 0x02113c23.
Lemma F_9d2d8 : fetch_word Ubsan.M.loaded_segments (0x9d330 : word) = Some W_9d2d8.
Proof. vm_refl. Qed.
Lemma D_9d2d8 : decode_any W_9d2d8 = Some (Store SZ8 2 1 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_9d2dc : bv 32 := 0x02813823.
Lemma F_9d2dc : fetch_word Ubsan.M.loaded_segments (0x9d334 : word) = Some W_9d2dc.
Proof. vm_refl. Qed.
Lemma D_9d2dc : decode_any W_9d2dc = Some (Store SZ8 2 8 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_9d2e0 : bv 32 := 0x02913423.
Lemma F_9d2e0 : fetch_word Ubsan.M.loaded_segments (0x9d338 : word) = Some W_9d2e0.
Proof. vm_refl. Qed.
Lemma D_9d2e0 : decode_any W_9d2e0 = Some (Store SZ8 2 9 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_9d2e4 : bv 32 := 0x03213023.
Lemma F_9d2e4 : fetch_word Ubsan.M.loaded_segments (0x9d33c : word) = Some W_9d2e4.
Proof. vm_refl. Qed.
Lemma D_9d2e4 : decode_any W_9d2e4 = Some (Store SZ8 2 18 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_9d2e8 : bv 32 := 0x01313c23.
Lemma F_9d2e8 : fetch_word Ubsan.M.loaded_segments (0x9d340 : word) = Some W_9d2e8.
Proof. vm_refl. Qed.
Lemma D_9d2e8 : decode_any W_9d2e8 = Some (Store SZ8 2 19 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_9d2ec : bv 32 := 0x01413823.
Lemma F_9d2ec : fetch_word Ubsan.M.loaded_segments (0x9d344 : word) = Some W_9d2ec.
Proof. vm_refl. Qed.
Lemma D_9d2ec : decode_any W_9d2ec = Some (Store SZ8 2 20 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_9d2f0 : bv 32 := 0x01513423.
Lemma F_9d2f0 : fetch_word Ubsan.M.loaded_segments (0x9d348 : word) = Some W_9d2f0.
Proof. vm_refl. Qed.
Lemma D_9d2f0 : decode_any W_9d2f0 = Some (Store SZ8 2 21 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_9d2f4 : bv 32 := 0x02853683.
Lemma F_9d2f4 : fetch_word Ubsan.M.loaded_segments (0x9d34c : word) = Some W_9d2f4.
Proof. vm_refl. Qed.
Lemma D_9d2f4 : decode_any W_9d2f4 = Some (Load SZ8 true 13 10 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_9d2f8 : bv 32 := 0x00050597.
Lemma F_9d2f8 : fetch_word Ubsan.M.loaded_segments (0x9d350 : word) = Some W_9d2f8.
Proof. vm_refl. Qed.
Lemma D_9d2f8 : decode_any W_9d2f8 = Some (Auipc 11 80, 4%Z).
Proof. vm_refl. Qed.

Definition W_9d308 : bv 32 := 0x0c068e63.
Lemma F_9d308 : fetch_word Ubsan.M.loaded_segments (0x9d360 : word) = Some W_9d308.
Proof. vm_refl. Qed.
Lemma D_9d308 : decode_any W_9d308 = Some (Branch BC_EQ 13 0 220, 4%Z).
Proof. vm_refl. Qed.

Definition W_9d310 : bv 32 := 0x00000893.
Lemma F_9d310 : fetch_word Ubsan.M.loaded_segments (0x9d368 : word) = Some W_9d310.
Proof. vm_refl. Qed.
Lemma D_9d310 : decode_any W_9d310 = Some (OpImm ALU_ADD 17 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_9d314 : bv 32 := 0x0001e717.
Lemma F_9d314 : fetch_word Ubsan.M.loaded_segments (0x9d36c : word) = Some W_9d314.
Proof. vm_refl. Qed.
Lemma D_9d314 : decode_any W_9d314 = Some (Auipc 14 30, 4%Z).
Proof. vm_refl. Qed.

Definition W_9d318 : bv 32 := 0x01853783.
Lemma F_9d318 : fetch_word Ubsan.M.loaded_segments (0x9d370 : word) = Some W_9d318.
Proof. vm_refl. Qed.
Lemma D_9d318 : decode_any W_9d318 = Some (Load SZ8 true 15 10 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_9d31c : bv 32 := 0x02053503.
Lemma F_9d31c : fetch_word Ubsan.M.loaded_segments (0x9d374 : word) = Some W_9d31c.
Proof. vm_refl. Qed.
Lemma D_9d31c : decode_any W_9d31c = Some (Load SZ8 true 10 10 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_9d320 : bv 32 := 0x00600813.
Lemma F_9d320 : fetch_word Ubsan.M.loaded_segments (0x9d378 : word) = Some W_9d320.
Proof. vm_refl. Qed.
Lemma D_9d320 : decode_any W_9d320 = Some (OpImm ALU_ADD 16 0 6, 4%Z).
Proof. vm_refl. Qed.

Definition W_9d324 : bv 32 := 0x0001d297.
Lemma F_9d324 : fetch_word Ubsan.M.loaded_segments (0x9d37c : word) = Some W_9d324.
Proof. vm_refl. Qed.
Lemma D_9d324 : decode_any W_9d324 = Some (Auipc 5 29, 4%Z).
Proof. vm_refl. Qed.

Definition W_9d328 : bv 32 := 0xdac76f03.
Lemma F_9d328 : fetch_word Ubsan.M.loaded_segments (0x9d380 : word) = Some W_9d328.
Proof. vm_refl. Qed.
Lemma D_9d328 : decode_any W_9d328 = Some (Load SZ4 false 30 14 3500, 4%Z).
Proof. vm_refl. Qed.

Definition W_9d32c : bv 32 := 0x9142b283.
Lemma F_9d32c : fetch_word Ubsan.M.loaded_segments (0x9d384 : word) = Some W_9d32c.
Proof. vm_refl. Qed.
Lemma D_9d32c : decode_any W_9d32c = Some (Load SZ8 true 5 5 2324, 4%Z).
Proof. vm_refl. Qed.

Definition W_9d330 : bv 32 := 0x00200313.
Lemma F_9d330 : fetch_word Ubsan.M.loaded_segments (0x9d388 : word) = Some W_9d330.
Proof. vm_refl. Qed.
Lemma D_9d330 : decode_any W_9d330 = Some (OpImm ALU_ADD 6 0 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_9d334 : bv 32 := 0x00700393.
Lemma F_9d334 : fetch_word Ubsan.M.loaded_segments (0x9d38c : word) = Some W_9d334.
Proof. vm_refl. Qed.
Lemma D_9d334 : decode_any W_9d334 = Some (OpImm ALU_ADD 7 0 7, 4%Z).
Proof. vm_refl. Qed.

Definition W_9d338 : bv 32 := 0x6474ee37.
Lemma F_9d338 : fetch_word Ubsan.M.loaded_segments (0x9d390 : word) = Some W_9d338.
Proof. vm_refl. Qed.
Lemma D_9d338 : decode_any W_9d338 = Some (Lui 28 411470, 4%Z).
Proof. vm_refl. Qed.

Definition W_9d33c : bv 32 := 0x551e0e1b.
Lemma F_9d33c : fetch_word Ubsan.M.loaded_segments (0x9d394 : word) = Some W_9d33c.
Proof. vm_refl. Qed.
Lemma D_9d33c : decode_any W_9d33c = Some (OpImm32 28 28 1361, 4%Z).
Proof. vm_refl. Qed.

Definition W_9d340 : bv 32 := 0x00078e93.
Lemma F_9d340 : fetch_word Ubsan.M.loaded_segments (0x9d398 : word) = Some W_9d340.
Proof. vm_refl. Qed.
Lemma D_9d340 : decode_any W_9d340 = Some (OpImm ALU_ADD 29 15 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_9d344 : bv 32 := 0x0180006f.
Lemma F_9d344 : fetch_word Ubsan.M.loaded_segments (0x9d39c : word) = Some W_9d344.
Proof. vm_refl. Qed.
Lemma D_9d344 : decode_any W_9d344 = Some (Jal 0 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_9d350 : bv 32 := 0xfff68693.
Lemma F_9d350 : fetch_word Ubsan.M.loaded_segments (0x9d3a8 : word) = Some W_9d350.
Proof. vm_refl. Qed.
Lemma D_9d350 : decode_any W_9d350 = Some (OpImm ALU_ADD 13 13 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_9d354 : bv 32 := 0x00ae8eb3.
Lemma F_9d354 : fetch_word Ubsan.M.loaded_segments (0x9d3ac : word) = Some W_9d354.
Proof. vm_refl. Qed.
Lemma D_9d354 : decode_any W_9d354 = Some (Op ALU_ADD 29 29 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_9d358 : bv 32 := 0x04068a63.
Lemma F_9d358 : fetch_word Ubsan.M.loaded_segments (0x9d3b0 : word) = Some W_9d358.
Proof. vm_refl. Qed.
Lemma D_9d358 : decode_any W_9d358 = Some (Branch BC_EQ 13 0 84, 4%Z).
Proof. vm_refl. Qed.

Definition W_9d35c : bv 32 := 0x000ea403.
Lemma F_9d35c : fetch_word Ubsan.M.loaded_segments (0x9d3b4 : word) = Some W_9d35c.
Proof. vm_refl. Qed.
Lemma D_9d35c : decode_any W_9d35c = Some (Load SZ4 true 8 29 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_9d360 : bv 32 := 0xff0404e3.
Lemma F_9d360 : fetch_word Ubsan.M.loaded_segments (0x9d3b8 : word) = Some W_9d360.
Proof. vm_refl. Qed.
Lemma D_9d360 : decode_any W_9d360 = Some (Branch BC_EQ 8 16 8168, 4%Z).
Proof. vm_refl. Qed.

Definition W_9d364 : bv 32 := 0x00028a63.
Lemma F_9d364 : fetch_word Ubsan.M.loaded_segments (0x9d3bc : word) = Some W_9d364.
Proof. vm_refl. Qed.
Lemma D_9d364 : decode_any W_9d364 = Some (Branch BC_EQ 5 0 20, 4%Z).
Proof. vm_refl. Qed.

Definition W_9d378 : bv 32 := 0x000e8f93.
Lemma F_9d378 : fetch_word Ubsan.M.loaded_segments (0x9d3d0 : word) = Some W_9d378.
Proof. vm_refl. Qed.
Lemma D_9d378 : decode_any W_9d378 = Some (OpImm ALU_ADD 31 29 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_9d37c : bv 32 := 0x00740463.
Lemma F_9d37c : fetch_word Ubsan.M.loaded_segments (0x9d3d4 : word) = Some W_9d37c.
Proof. vm_refl. Qed.
Lemma D_9d37c : decode_any W_9d37c = Some (Branch BC_EQ 8 7 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_9d380 : bv 32 := 0x00088f93.
Lemma F_9d380 : fetch_word Ubsan.M.loaded_segments (0x9d3d8 : word) = Some W_9d380.
Proof. vm_refl. Qed.
Lemma D_9d380 : decode_any W_9d380 = Some (OpImm ALU_ADD 31 17 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_9d384 : bv 32 := 0x03c41063.
Lemma F_9d384 : fetch_word Ubsan.M.loaded_segments (0x9d3dc : word) = Some W_9d384.
Proof. vm_refl. Qed.
Lemma D_9d384 : decode_any W_9d384 = Some (Branch BC_NE 8 28 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_9d388 : bv 32 := 0x028eb883.
Lemma F_9d388 : fetch_word Ubsan.M.loaded_segments (0x9d3e0 : word) = Some W_9d388.
Proof. vm_refl. Qed.
Lemma D_9d388 : decode_any W_9d388 = Some (Load SZ8 true 17 29 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_9d38c : bv 32 := 0x011f7c63.
Lemma F_9d38c : fetch_word Ubsan.M.loaded_segments (0x9d3e4 : word) = Some W_9d38c.
Proof. vm_refl. Qed.
Lemma D_9d38c : decode_any W_9d38c = Some (Branch BC_GEU 30 17 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_9d3a4 : bv 32 := 0x000f8893.
Lemma F_9d3a4 : fetch_word Ubsan.M.loaded_segments (0x9d3fc : word) = Some W_9d3a4.
Proof. vm_refl. Qed.
Lemma D_9d3a4 : decode_any W_9d3a4 = Some (OpImm ALU_ADD 17 31 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_9d3a8 : bv 32 := 0xfa9ff06f.
Lemma F_9d3a8 : fetch_word Ubsan.M.loaded_segments (0x9d400 : word) = Some W_9d3a8.
Proof. vm_refl. Qed.
Lemma D_9d3a8 : decode_any W_9d3a8 = Some (Jal 0 2097064, 4%Z).
Proof. vm_refl. Qed.

Definition W_9d3ac : bv 32 := 0x02088c63.
Lemma F_9d3ac : fetch_word Ubsan.M.loaded_segments (0x9d404 : word) = Some W_9d3ac.
Proof. vm_refl. Qed.
Lemma D_9d3ac : decode_any W_9d3ac = Some (Branch BC_EQ 17 0 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_9d3f4 : bv 32 := 0xfff50793.
Lemma F_9d3f4 : fetch_word Ubsan.M.loaded_segments (0x9d44c : word) = Some W_9d3f4.
Proof. vm_refl. Qed.
Lemma D_9d3f4 : decode_any W_9d3f4 = Some (OpImm ALU_ADD 15 10 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_9d3f8 : bv 32 := 0x40e00733.
Lemma F_9d3f8 : fetch_word Ubsan.M.loaded_segments (0x9d450 : word) = Some W_9d3f8.
Proof. vm_refl. Qed.
Lemma D_9d3f8 : decode_any W_9d3f8 = Some (Op ALU_SUB 14 0 14, 4%Z).
Proof. vm_refl. Qed.

Definition W_9d400 : bv 32 := 0x00e7f733.
Lemma F_9d400 : fetch_word Ubsan.M.loaded_segments (0x9d458 : word) = Some W_9d400.
Proof. vm_refl. Qed.
Lemma D_9d400 : decode_any W_9d400 = Some (Op ALU_AND 14 15 14, 4%Z).
Proof. vm_refl. Qed.

Definition W_9d404 : bv 32 := 0x00700793.
Lemma F_9d404 : fetch_word Ubsan.M.loaded_segments (0x9d45c : word) = Some W_9d404.
Proof. vm_refl. Qed.
Lemma D_9d404 : decode_any W_9d404 = Some (OpImm ALU_ADD 15 0 7, 4%Z).
Proof. vm_refl. Qed.

Definition W_9d408 : bv 32 := 0x00d706b3.
Lemma F_9d408 : fetch_word Ubsan.M.loaded_segments (0x9d460 : word) = Some W_9d408.
Proof. vm_refl. Qed.
Lemma D_9d408 : decode_any W_9d408 = Some (Op ALU_ADD 13 14 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_9d414 : bv 32 := 0x00a7e663.
Lemma F_9d414 : fetch_word Ubsan.M.loaded_segments (0x9d46c : word) = Some W_9d414.
Proof. vm_refl. Qed.
Lemma D_9d414 : decode_any W_9d414 = Some (Branch BC_LTU 15 10 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_9d418 : bv 32 := 0x00800513.
Lemma F_9d418 : fetch_word Ubsan.M.loaded_segments (0x9d470 : word) = Some W_9d418.
Proof. vm_refl. Qed.
Lemma D_9d418 : decode_any W_9d418 = Some (OpImm ALU_ADD 10 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_9d430 : bv 32 := 0xff85f593.
Lemma F_9d430 : fetch_word Ubsan.M.loaded_segments (0x9d48c : word) = Some W_9d430.
Proof. vm_refl. Qed.
Lemma D_9d430 : decode_any W_9d430 = Some (OpImm ALU_AND 11 11 4088, 4%Z).
Proof. vm_refl. Qed.

Definition W_9d434 : bv 32 := 0x00b4bc23.
Lemma F_9d434 : fetch_word Ubsan.M.loaded_segments (0x9d490 : word) = Some W_9d434.
Proof. vm_refl. Qed.
Lemma D_9d434 : decode_any W_9d434 = Some (Store SZ8 9 11 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_9d438 : bv 32 := 0x02a4b023.
Lemma F_9d438 : fetch_word Ubsan.M.loaded_segments (0x9d494 : word) = Some W_9d438.
Proof. vm_refl. Qed.
Lemma D_9d438 : decode_any W_9d438 = Some (Store SZ8 9 10 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_9d43c : bv 32 := 0x02d5ea63.
Lemma F_9d43c : fetch_word Ubsan.M.loaded_segments (0x9d498 : word) = Some W_9d43c.
Proof. vm_refl. Qed.
Lemma D_9d43c : decode_any W_9d43c = Some (Branch BC_LTU 11 13 52, 4%Z).
Proof. vm_refl. Qed.

Definition W_9d488 : bv 32 := 0x0284b603.
Lemma F_9d488 : fetch_word Ubsan.M.loaded_segments (0x9d4d4 : word) = Some W_9d488.
Proof. vm_refl. Qed.
Lemma D_9d488 : decode_any W_9d488 = Some (Load SZ8 true 12 9 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_9d4b4 : bv 32 := 0x0c890413.
Lemma F_9d4b4 : fetch_word Ubsan.M.loaded_segments (0x9d500 : word) = Some W_9d4b4.
Proof. vm_refl. Qed.
Lemma D_9d4b4 : decode_any W_9d4b4 = Some (OpImm ALU_ADD 8 18 200, 4%Z).
Proof. vm_refl. Qed.

Definition W_9d508 : bv 32 := 0x01293023.
Lemma F_9d508 : fetch_word Ubsan.M.loaded_segments (0x9d554 : word) = Some W_9d508.
Proof. vm_refl. Qed.
Lemma D_9d508 : decode_any W_9d508 = Some (Store SZ8 18 18 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_9d50c : bv 32 := 0x00040513.
Lemma F_9d50c : fetch_word Ubsan.M.loaded_segments (0x9d558 : word) = Some W_9d50c.
Proof. vm_refl. Qed.
Lemma D_9d50c : decode_any W_9d50c = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_9d510 : bv 32 := 0x16c130ef.
Lemma F_9d510 : fetch_word Ubsan.M.loaded_segments (0x9d55c : word) = Some W_9d510.
Proof. vm_refl. Qed.
Lemma D_9d510 : decode_any W_9d510 = Some (Jal 1 78188, 4%Z).
Proof. vm_refl. Qed.

Definition W_9d514 : bv 32 := 0x04054a63.
Lemma F_9d514 : fetch_word Ubsan.M.loaded_segments (0x9d560 : word) = Some W_9d514.
Proof. vm_refl. Qed.
Lemma D_9d514 : decode_any W_9d514 = Some (Branch BC_LT 10 0 84, 4%Z).
Proof. vm_refl. Qed.

Definition W_9d518 : bv 32 := 0x00051663.
Lemma F_9d518 : fetch_word Ubsan.M.loaded_segments (0x9d564 : word) = Some W_9d518.
Proof. vm_refl. Qed.
Lemma D_9d518 : decode_any W_9d518 = Some (Branch BC_NE 10 0 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_9d51c : bv 32 := 0x00100513.
Lemma F_9d51c : fetch_word Ubsan.M.loaded_segments (0x9d568 : word) = Some W_9d51c.
Proof. vm_refl. Qed.
Lemma D_9d51c : decode_any W_9d51c = Some (OpImm ALU_ADD 10 0 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_9d520 : bv 32 := 0x00a48023.
Lemma F_9d520 : fetch_word Ubsan.M.loaded_segments (0x9d56c : word) = Some W_9d520.
Proof. vm_refl. Qed.
Lemma D_9d520 : decode_any W_9d520 = Some (Store SZ1 9 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_9d524 : bv 32 := 0x00200513.
Lemma F_9d524 : fetch_word Ubsan.M.loaded_segments (0x9d570 : word) = Some W_9d524.
Proof. vm_refl. Qed.
Lemma D_9d524 : decode_any W_9d524 = Some (OpImm ALU_ADD 10 0 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_9d528 : bv 32 := 0x0004f597.
Lemma F_9d528 : fetch_word Ubsan.M.loaded_segments (0x9d574 : word) = Some W_9d528.
Proof. vm_refl. Qed.
Lemma D_9d528 : decode_any W_9d528 = Some (Auipc 11 79, 4%Z).
Proof. vm_refl. Qed.

Definition W_9d52c : bv 32 := 0x02a92423.
Lemma F_9d52c : fetch_word Ubsan.M.loaded_segments (0x9d578 : word) = Some W_9d52c.
Proof. vm_refl. Qed.
Lemma D_9d52c : decode_any W_9d52c = Some (Store SZ4 18 10 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_9d530 : bv 32 := 0x06000893.
Lemma F_9d530 : fetch_word Ubsan.M.loaded_segments (0x9d57c : word) = Some W_9d530.
Proof. vm_refl. Qed.
Lemma D_9d530 : decode_any W_9d530 = Some (OpImm ALU_ADD 17 0 96, 4%Z).
Proof. vm_refl. Qed.

Definition W_9d534 : bv 32 := 0x65458513.
Lemma F_9d534 : fetch_word Ubsan.M.loaded_segments (0x9d580 : word) = Some W_9d534.
Proof. vm_refl. Qed.
Lemma D_9d534 : decode_any W_9d534 = Some (OpImm ALU_ADD 10 11 1620, 4%Z).
Proof. vm_refl. Qed.

Definition W_9d538 : bv 32 := 0x03848593.
Lemma F_9d538 : fetch_word Ubsan.M.loaded_segments (0x9d584 : word) = Some W_9d538.
Proof. vm_refl. Qed.
Lemma D_9d538 : decode_any W_9d538 = Some (OpImm ALU_ADD 11 9 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_9d53c : bv 32 := 0x00000073.
Lemma F_9d53c : fetch_word Ubsan.M.loaded_segments (0x9d588 : word) = Some W_9d53c.
Proof. vm_refl. Qed.
Lemma D_9d53c : decode_any W_9d53c = Some (Ecall, 4%Z).
Proof. vm_refl. Qed.
Lemma E_9d53c : is_ecall W_9d53c = true.
Proof. reflexivity. Qed.

Definition W_9d540 : bv 32 := 0x07890613.
Lemma F_9d540 : fetch_word Ubsan.M.loaded_segments (0x9d58c : word) = Some W_9d540.
Proof. vm_refl. Qed.
Lemma D_9d540 : decode_any W_9d540 = Some (OpImm ALU_ADD 12 18 120, 4%Z).
Proof. vm_refl. Qed.

Definition W_9d544 : bv 32 := 0x02a92023.
Lemma F_9d544 : fetch_word Ubsan.M.loaded_segments (0x9d590 : word) = Some W_9d544.
Proof. vm_refl. Qed.
Lemma D_9d544 : decode_any W_9d544 = Some (Store SZ4 18 10 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_9d548 : bv 32 := 0x08b93c23.
Lemma F_9d548 : fetch_word Ubsan.M.loaded_segments (0x9d594 : word) = Some W_9d548.
Proof. vm_refl. Qed.
Lemma D_9d548 : decode_any W_9d548 = Some (Store SZ8 18 11 152, 4%Z).
Proof. vm_refl. Qed.

Definition W_9d54c : bv 32 := 0x06c93c23.
Lemma F_9d54c : fetch_word Ubsan.M.loaded_segments (0x9d598 : word) = Some W_9d54c.
Proof. vm_refl. Qed.
Lemma D_9d54c : decode_any W_9d54c = Some (Store SZ8 18 12 120, 4%Z).
Proof. vm_refl. Qed.

Definition W_9d550 : bv 32 := 0x00050517.
Lemma F_9d550 : fetch_word Ubsan.M.loaded_segments (0x9d59c : word) = Some W_9d550.
Proof. vm_refl. Qed.
Lemma D_9d550 : decode_any W_9d550 = Some (Auipc 10 80, 4%Z).
Proof. vm_refl. Qed.

Definition W_9d554 : bv 32 := 0x89c53503.
Lemma F_9d554 : fetch_word Ubsan.M.loaded_segments (0x9d5a0 : word) = Some W_9d554.
Proof. vm_refl. Qed.
Lemma D_9d554 : decode_any W_9d554 = Some (Load SZ8 true 10 10 2204, 4%Z).
Proof. vm_refl. Qed.

Definition W_9d558 : bv 32 := 0x01293423.
Lemma F_9d558 : fetch_word Ubsan.M.loaded_segments (0x9d5a4 : word) = Some W_9d558.
Proof. vm_refl. Qed.
Lemma D_9d558 : decode_any W_9d558 = Some (Store SZ8 18 18 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_9d55c : bv 32 := 0x01293823.
Lemma F_9d55c : fetch_word Ubsan.M.loaded_segments (0x9d5a8 : word) = Some W_9d55c.
Proof. vm_refl. Qed.
Lemma D_9d55c : decode_any W_9d55c = Some (Store SZ8 18 18 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_9d560 : bv 32 := 0x00a93c23.
Lemma F_9d560 : fetch_word Ubsan.M.loaded_segments (0x9d5ac : word) = Some W_9d560.
Proof. vm_refl. Qed.
Lemma D_9d560 : decode_any W_9d560 = Some (Store SZ8 18 10 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_9d564 : bv 32 := 0x0080006f.
Lemma F_9d564 : fetch_word Ubsan.M.loaded_segments (0x9d5b0 : word) = Some W_9d564.
Proof. vm_refl. Qed.
Lemma D_9d564 : decode_any W_9d564 = Some (Jal 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_9d56c : bv 32 := 0x03813083.
Lemma F_9d56c : fetch_word Ubsan.M.loaded_segments (0x9d5b8 : word) = Some W_9d56c.
Proof. vm_refl. Qed.
Lemma D_9d56c : decode_any W_9d56c = Some (Load SZ8 true 1 2 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_9d570 : bv 32 := 0x03013403.
Lemma F_9d570 : fetch_word Ubsan.M.loaded_segments (0x9d5bc : word) = Some W_9d570.
Proof. vm_refl. Qed.
Lemma D_9d570 : decode_any W_9d570 = Some (Load SZ8 true 8 2 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_9d574 : bv 32 := 0x02813483.
Lemma F_9d574 : fetch_word Ubsan.M.loaded_segments (0x9d5c0 : word) = Some W_9d574.
Proof. vm_refl. Qed.
Lemma D_9d574 : decode_any W_9d574 = Some (Load SZ8 true 9 2 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_9d578 : bv 32 := 0x02013903.
Lemma F_9d578 : fetch_word Ubsan.M.loaded_segments (0x9d5c4 : word) = Some W_9d578.
Proof. vm_refl. Qed.
Lemma D_9d578 : decode_any W_9d578 = Some (Load SZ8 true 18 2 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_9d57c : bv 32 := 0x01813983.
Lemma F_9d57c : fetch_word Ubsan.M.loaded_segments (0x9d5c8 : word) = Some W_9d57c.
Proof. vm_refl. Qed.
Lemma D_9d57c : decode_any W_9d57c = Some (Load SZ8 true 19 2 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_9d580 : bv 32 := 0x01013a03.
Lemma F_9d580 : fetch_word Ubsan.M.loaded_segments (0x9d5cc : word) = Some W_9d580.
Proof. vm_refl. Qed.
Lemma D_9d580 : decode_any W_9d580 = Some (Load SZ8 true 20 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_9d584 : bv 32 := 0x00813a83.
Lemma F_9d584 : fetch_word Ubsan.M.loaded_segments (0x9d5d0 : word) = Some W_9d584.
Proof. vm_refl. Qed.
Lemma D_9d584 : decode_any W_9d584 = Some (Load SZ8 true 21 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_9d588 : bv 32 := 0x04010113.
Lemma F_9d588 : fetch_word Ubsan.M.loaded_segments (0x9d5d4 : word) = Some W_9d588.
Proof. vm_refl. Qed.
Lemma D_9d588 : decode_any W_9d588 = Some (OpImm ALU_ADD 2 2 64, 4%Z).
Proof. vm_refl. Qed.

Definition W_9d58c : bv 32 := 0x00008067.
Lemma F_9d58c : fetch_word Ubsan.M.loaded_segments (0x9d5d8 : word) = Some W_9d58c.
Proof. vm_refl. Qed.
Lemma D_9d58c : decode_any W_9d58c = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_9d630 : bv 32 := 0x00050593.
Lemma F_9d630 : fetch_word Ubsan.M.loaded_segments (0x9d67c : word) = Some W_9d630.
Proof. vm_refl. Qed.
Lemma D_9d630 : decode_any W_9d630 = Some (OpImm ALU_ADD 11 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_9d634 : bv 32 := 0x05e00893.
Lemma F_9d634 : fetch_word Ubsan.M.loaded_segments (0x9d680 : word) = Some W_9d634.
Proof. vm_refl. Qed.
Lemma D_9d634 : decode_any W_9d634 = Some (OpImm ALU_ADD 17 0 94, 4%Z).
Proof. vm_refl. Qed.

Definition W_9d638 : bv 32 := 0x00000073.
Lemma F_9d638 : fetch_word Ubsan.M.loaded_segments (0x9d684 : word) = Some W_9d638.
Proof. vm_refl. Qed.
Lemma D_9d638 : decode_any W_9d638 = Some (Ecall, 4%Z).
Proof. vm_refl. Qed.
Lemma E_9d638 : is_ecall W_9d638 = true.
Proof. reflexivity. Qed.

Definition W_9d8dc : bv 32 := 0xfe010113.
Lemma F_9d8dc : fetch_word Ubsan.M.loaded_segments (0x9d928 : word) = Some W_9d8dc.
Proof. vm_refl. Qed.
Lemma D_9d8dc : decode_any W_9d8dc = Some (OpImm ALU_ADD 2 2 4064, 4%Z).
Proof. vm_refl. Qed.

Definition W_9d8e0 : bv 32 := 0x00113c23.
Lemma F_9d8e0 : fetch_word Ubsan.M.loaded_segments (0x9d92c : word) = Some W_9d8e0.
Proof. vm_refl. Qed.
Lemma D_9d8e0 : decode_any W_9d8e0 = Some (Store SZ8 2 1 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_9d8e4 : bv 32 := 0x00813823.
Lemma F_9d8e4 : fetch_word Ubsan.M.loaded_segments (0x9d930 : word) = Some W_9d8e4.
Proof. vm_refl. Qed.
Lemma D_9d8e4 : decode_any W_9d8e4 = Some (Store SZ8 2 8 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_9d8e8 : bv 32 := 0x00913423.
Lemma F_9d8e8 : fetch_word Ubsan.M.loaded_segments (0x9d934 : word) = Some W_9d8e8.
Proof. vm_refl. Qed.
Lemma D_9d8e8 : decode_any W_9d8e8 = Some (Store SZ8 2 9 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_9d8ec : bv 32 := 0x0001c517.
Lemma F_9d8ec : fetch_word Ubsan.M.loaded_segments (0x9d938 : word) = Some W_9d8ec.
Proof. vm_refl. Qed.
Lemma D_9d8ec : decode_any W_9d8ec = Some (Auipc 10 28, 4%Z).
Proof. vm_refl. Qed.

Definition W_9d8f0 : bv 32 := 0x0001c597.
Lemma F_9d8f0 : fetch_word Ubsan.M.loaded_segments (0x9d93c : word) = Some W_9d8f0.
Proof. vm_refl. Qed.
Lemma D_9d8f0 : decode_any W_9d8f0 = Some (Auipc 11 28, 4%Z).
Proof. vm_refl. Qed.

Definition W_9d8f4 : bv 32 := 0x4f053503.
Lemma F_9d8f4 : fetch_word Ubsan.M.loaded_segments (0x9d940 : word) = Some W_9d8f4.
Proof. vm_refl. Qed.
Lemma D_9d8f4 : decode_any W_9d8f4 = Some (Load SZ8 true 10 10 1264, 4%Z).
Proof. vm_refl. Qed.

Definition W_9d8f8 : bv 32 := 0x4f45b403.
Lemma F_9d8f8 : fetch_word Ubsan.M.loaded_segments (0x9d944 : word) = Some W_9d8f8.
Proof. vm_refl. Qed.
Lemma D_9d8f8 : decode_any W_9d8f8 = Some (Load SZ8 true 8 11 1268, 4%Z).
Proof. vm_refl. Qed.

Definition W_9d8fc : bv 32 := 0x00a47c63.
Lemma F_9d8fc : fetch_word Ubsan.M.loaded_segments (0x9d948 : word) = Some W_9d8fc.
Proof. vm_refl. Qed.
Lemma D_9d8fc : decode_any W_9d8fc = Some (Branch BC_GEU 8 10 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_9d900 : bv 32 := 0xff853583.
Lemma F_9d900 : fetch_word Ubsan.M.loaded_segments (0x9d94c : word) = Some W_9d900.
Proof. vm_refl. Qed.
Lemma D_9d900 : decode_any W_9d900 = Some (Load SZ8 true 11 10 4088, 4%Z).
Proof. vm_refl. Qed.

Definition W_9d904 : bv 32 := 0xff850493.
Lemma F_9d904 : fetch_word Ubsan.M.loaded_segments (0x9d950 : word) = Some W_9d904.
Proof. vm_refl. Qed.
Lemma D_9d904 : decode_any W_9d904 = Some (OpImm ALU_ADD 9 10 4088, 4%Z).
Proof. vm_refl. Qed.

Definition W_9d908 : bv 32 := 0x000580e7.
Lemma F_9d908 : fetch_word Ubsan.M.loaded_segments (0x9d954 : word) = Some W_9d908.
Proof. vm_refl. Qed.
Lemma D_9d908 : decode_any W_9d908 = Some (Jalr 1 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_9d90c : bv 32 := 0x00048513.
Lemma F_9d90c : fetch_word Ubsan.M.loaded_segments (0x9d958 : word) = Some W_9d90c.
Proof. vm_refl. Qed.
Lemma D_9d90c : decode_any W_9d90c = Some (OpImm ALU_ADD 10 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_9d910 : bv 32 := 0xfe9468e3.
Lemma F_9d910 : fetch_word Ubsan.M.loaded_segments (0x9d95c : word) = Some W_9d910.
Proof. vm_refl. Qed.
Lemma D_9d910 : decode_any W_9d910 = Some (Branch BC_LTU 8 9 8176, 4%Z).
Proof. vm_refl. Qed.

Definition W_9d914 : bv 32 := 0x01813083.
Lemma F_9d914 : fetch_word Ubsan.M.loaded_segments (0x9d960 : word) = Some W_9d914.
Proof. vm_refl. Qed.
Lemma D_9d914 : decode_any W_9d914 = Some (Load SZ8 true 1 2 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_9d918 : bv 32 := 0x01013403.
Lemma F_9d918 : fetch_word Ubsan.M.loaded_segments (0x9d964 : word) = Some W_9d918.
Proof. vm_refl. Qed.
Lemma D_9d918 : decode_any W_9d918 = Some (Load SZ8 true 8 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_9d91c : bv 32 := 0x00813483.
Lemma F_9d91c : fetch_word Ubsan.M.loaded_segments (0x9d968 : word) = Some W_9d91c.
Proof. vm_refl. Qed.
Lemma D_9d91c : decode_any W_9d91c = Some (Load SZ8 true 9 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_9d920 : bv 32 := 0x02010113.
Lemma F_9d920 : fetch_word Ubsan.M.loaded_segments (0x9d96c : word) = Some W_9d920.
Proof. vm_refl. Qed.
Lemma D_9d920 : decode_any W_9d920 = Some (OpImm ALU_ADD 2 2 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_9d924 : bv 32 := 0xfb5ff06f.
Lemma F_9d924 : fetch_word Ubsan.M.loaded_segments (0x9d970 : word) = Some W_9d924.
Proof. vm_refl. Qed.
Lemma D_9d924 : decode_any W_9d924 = Some (Jal 0 2097076, 4%Z).
Proof. vm_refl. Qed.

Definition W_9d928 : bv 32 := 0xff010113.
Lemma F_9d928 : fetch_word Ubsan.M.loaded_segments (0x9d974 : word) = Some W_9d928.
Proof. vm_refl. Qed.
Lemma D_9d928 : decode_any W_9d928 = Some (OpImm ALU_ADD 2 2 4080, 4%Z).
Proof. vm_refl. Qed.

Definition W_9d92c : bv 32 := 0x00113423.
Lemma F_9d92c : fetch_word Ubsan.M.loaded_segments (0x9d978 : word) = Some W_9d92c.
Proof. vm_refl. Qed.
Lemma D_9d92c : decode_any W_9d92c = Some (Store SZ8 2 1 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_9d930 : bv 32 := 0x00813023.
Lemma F_9d930 : fetch_word Ubsan.M.loaded_segments (0x9d97c : word) = Some W_9d930.
Proof. vm_refl. Qed.
Lemma D_9d930 : decode_any W_9d930 = Some (Store SZ8 2 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_9d934 : bv 32 := 0x00000593.
Lemma F_9d934 : fetch_word Ubsan.M.loaded_segments (0x9d980 : word) = Some W_9d934.
Proof. vm_refl. Qed.
Lemma D_9d934 : decode_any W_9d934 = Some (OpImm ALU_ADD 11 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_9d938 : bv 32 := 0x00020613.
Lemma F_9d938 : fetch_word Ubsan.M.loaded_segments (0x9d984 : word) = Some W_9d938.
Proof. vm_refl. Qed.
Lemma D_9d938 : decode_any W_9d938 = Some (OpImm ALU_ADD 12 4 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_9d93c : bv 32 := 0xf5862603.
Lemma F_9d93c : fetch_word Ubsan.M.loaded_segments (0x9d988 : word) = Some W_9d93c.
Proof. vm_refl. Qed.
Lemma D_9d93c : decode_any W_9d93c = Some (Load SZ4 true 12 12 3928, 4%Z).
Proof. vm_refl. Qed.

Definition W_9d940 : bv 32 := 0x0004f697.
Lemma F_9d940 : fetch_word Ubsan.M.loaded_segments (0x9d98c : word) = Some W_9d940.
Proof. vm_refl. Qed.
Lemma D_9d940 : decode_any W_9d940 = Some (Auipc 13 79, 4%Z).
Proof. vm_refl. Qed.

Definition W_9d944 : bv 32 := 0x49c68693.
Lemma F_9d944 : fetch_word Ubsan.M.loaded_segments (0x9d990 : word) = Some W_9d944.
Proof. vm_refl. Qed.
Lemma D_9d944 : decode_any W_9d944 = Some (OpImm ALU_ADD 13 13 1180, 4%Z).
Proof. vm_refl. Qed.

Definition W_9d948 : bv 32 := 0x1606a72f.
Lemma F_9d948 : fetch_word Ubsan.M.loaded_segments (0x9d994 : word) = Some W_9d948.
Proof. vm_refl. Qed.
Lemma D_9d948 : decode_any W_9d948 = Some (Lr AW true true 14 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_9d94c : bv 32 := 0x00b71663.
Lemma F_9d94c : fetch_word Ubsan.M.loaded_segments (0x9d998 : word) = Some W_9d94c.
Proof. vm_refl. Qed.
Lemma D_9d94c : decode_any W_9d94c = Some (Branch BC_NE 14 11 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_9d950 : bv 32 := 0x1ec6a7af.
Lemma F_9d950 : fetch_word Ubsan.M.loaded_segments (0x9d99c : word) = Some W_9d950.
Proof. vm_refl. Qed.
Lemma D_9d950 : decode_any W_9d950 = Some (Sc AW true true 15 13 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_9d954 : bv 32 := 0xfe079ae3.
Lemma F_9d954 : fetch_word Ubsan.M.loaded_segments (0x9d9a0 : word) = Some W_9d954.
Proof. vm_refl. Qed.
Lemma D_9d954 : decode_any W_9d954 = Some (Branch BC_NE 15 0 8180, 4%Z).
Proof. vm_refl. Qed.

Definition W_9d958 : bv 32 := 0x0007059b.
Lemma F_9d958 : fetch_word Ubsan.M.loaded_segments (0x9d9a4 : word) = Some W_9d958.
Proof. vm_refl. Qed.
Lemma D_9d958 : decode_any W_9d958 = Some (OpImm32 11 14 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_9d95c : bv 32 := 0x02c58263.
Lemma F_9d95c : fetch_word Ubsan.M.loaded_segments (0x9d9a8 : word) = Some W_9d95c.
Proof. vm_refl. Qed.
Lemma D_9d95c : decode_any W_9d95c = Some (Branch BC_EQ 11 12 36, 4%Z).
Proof. vm_refl. Qed.

Definition W_9d960 : bv 32 := 0x02058263.
Lemma F_9d960 : fetch_word Ubsan.M.loaded_segments (0x9d9ac : word) = Some W_9d960.
Proof. vm_refl. Qed.
Lemma D_9d960 : decode_any W_9d960 = Some (Branch BC_EQ 11 0 36, 4%Z).
Proof. vm_refl. Qed.

Definition W_9d984 : bv 32 := 0x00050413.
Lemma F_9d984 : fetch_word Ubsan.M.loaded_segments (0x9d9d0 : word) = Some W_9d984.
Proof. vm_refl. Qed.
Lemma D_9d984 : decode_any W_9d984 = Some (OpImm ALU_ADD 8 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_9d988 : bv 32 := 0xcf5ff0ef.
Lemma F_9d988 : fetch_word Ubsan.M.loaded_segments (0x9d9d4 : word) = Some W_9d988.
Proof. vm_refl. Qed.
Lemma D_9d988 : decode_any W_9d988 = Some (Jal 1 2096372, 4%Z).
Proof. vm_refl. Qed.

Definition W_9d98c : bv 32 := 0xf51ff0ef.
Lemma F_9d98c : fetch_word Ubsan.M.loaded_segments (0x9d9d8 : word) = Some W_9d98c.
Proof. vm_refl. Qed.
Lemma D_9d98c : decode_any W_9d98c = Some (Jal 1 2096976, 4%Z).
Proof. vm_refl. Qed.

Definition W_9d990 : bv 32 := 0x63c050ef.
Lemma F_9d990 : fetch_word Ubsan.M.loaded_segments (0x9d9dc : word) = Some W_9d990.
Proof. vm_refl. Qed.
Lemma D_9d990 : decode_any W_9d990 = Some (Jal 1 22076, 4%Z).
Proof. vm_refl. Qed.

Definition W_9d994 : bv 32 := 0x00040513.
Lemma F_9d994 : fetch_word Ubsan.M.loaded_segments (0x9d9e0 : word) = Some W_9d994.
Proof. vm_refl. Qed.
Lemma D_9d994 : decode_any W_9d994 = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_9d998 : bv 32 := 0xc99ff0ef.
Lemma F_9d998 : fetch_word Ubsan.M.loaded_segments (0x9d9e4 : word) = Some W_9d998.
Proof. vm_refl. Qed.
Lemma D_9d998 : decode_any W_9d998 = Some (Jal 1 2096280, 4%Z).
Proof. vm_refl. Qed.

Definition W_9da80 : bv 32 := 0xff010113.
Lemma F_9da80 : fetch_word Ubsan.M.loaded_segments (0x9dacc : word) = Some W_9da80.
Proof. vm_refl. Qed.
Lemma D_9da80 : decode_any W_9da80 = Some (OpImm ALU_ADD 2 2 4080, 4%Z).
Proof. vm_refl. Qed.

Definition W_9da84 : bv 32 := 0x00113423.
Lemma F_9da84 : fetch_word Ubsan.M.loaded_segments (0x9dad0 : word) = Some W_9da84.
Proof. vm_refl. Qed.
Lemma D_9da84 : decode_any W_9da84 = Some (Store SZ8 2 1 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_9da88 : bv 32 := 0x00050e63.
Lemma F_9da88 : fetch_word Ubsan.M.loaded_segments (0x9dad4 : word) = Some W_9da88.
Proof. vm_refl. Qed.
Lemma D_9da88 : decode_any W_9da88 = Some (Branch BC_EQ 10 0 28, 4%Z).
Proof. vm_refl. Qed.

Definition W_9da8c : bv 32 := 0x00050593.
Lemma F_9da8c : fetch_word Ubsan.M.loaded_segments (0x9dad8 : word) = Some W_9da8c.
Proof. vm_refl. Qed.
Lemma D_9da8c : decode_any W_9da8c = Some (OpImm ALU_ADD 11 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_9da90 : bv 32 := 0x0001c517.
Lemma F_9da90 : fetch_word Ubsan.M.loaded_segments (0x9dadc : word) = Some W_9da90.
Proof. vm_refl. Qed.
Lemma D_9da90 : decode_any W_9da90 = Some (Auipc 10 28, 4%Z).
Proof. vm_refl. Qed.

Definition W_9da94 : bv 32 := 0x34453503.
Lemma F_9da94 : fetch_word Ubsan.M.loaded_segments (0x9dae0 : word) = Some W_9da94.
Proof. vm_refl. Qed.
Lemma D_9da94 : decode_any W_9da94 = Some (Load SZ8 true 10 10 836, 4%Z).
Proof. vm_refl. Qed.

Definition W_9da98 : bv 32 := 0x00800613.
Lemma F_9da98 : fetch_word Ubsan.M.loaded_segments (0x9dae4 : word) = Some W_9da98.
Proof. vm_refl. Qed.
Lemma D_9da98 : decode_any W_9da98 = Some (OpImm ALU_ADD 12 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_9da9c : bv 32 := 0x520100ef.
Lemma F_9da9c : fetch_word Ubsan.M.loaded_segments (0x9dae8 : word) = Some W_9da9c.
Proof. vm_refl. Qed.
Lemma D_9da9c : decode_any W_9da9c = Some (Jal 1 66848, 4%Z).
Proof. vm_refl. Qed.

Definition W_9daa0 : bv 32 := 0x01c0006f.
Lemma F_9daa0 : fetch_word Ubsan.M.loaded_segments (0x9daec : word) = Some W_9daa0.
Proof. vm_refl. Qed.
Lemma D_9daa0 : decode_any W_9daa0 = Some (Jal 0 28, 4%Z).
Proof. vm_refl. Qed.

Definition W_9dabc : bv 32 := 0x0001c517.
Lemma F_9dabc : fetch_word Ubsan.M.loaded_segments (0x9db08 : word) = Some W_9dabc.
Proof. vm_refl. Qed.
Lemma D_9dabc : decode_any W_9dabc = Some (Auipc 10 28, 4%Z).
Proof. vm_refl. Qed.

Definition W_9dac0 : bv 32 := 0x31853503.
Lemma F_9dac0 : fetch_word Ubsan.M.loaded_segments (0x9db0c : word) = Some W_9dac0.
Proof. vm_refl. Qed.
Lemma D_9dac0 : decode_any W_9dac0 = Some (Load SZ8 true 10 10 792, 4%Z).
Proof. vm_refl. Qed.

Definition W_9dac4 : bv 32 := 0x000500a3.
Lemma F_9dac4 : fetch_word Ubsan.M.loaded_segments (0x9db10 : word) = Some W_9dac4.
Proof. vm_refl. Qed.
Lemma D_9dac4 : decode_any W_9dac4 = Some (Store SZ1 10 0 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_9dac8 : bv 32 := 0x00053503.
Lemma F_9dac8 : fetch_word Ubsan.M.loaded_segments (0x9db14 : word) = Some W_9dac8.
Proof. vm_refl. Qed.
Lemma D_9dac8 : decode_any W_9dac8 = Some (Load SZ8 true 10 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_9dacc : bv 32 := 0x00020593.
Lemma F_9dacc : fetch_word Ubsan.M.loaded_segments (0x9db18 : word) = Some W_9dacc.
Proof. vm_refl. Qed.
Lemma D_9dacc : decode_any W_9dacc = Some (OpImm ALU_ADD 11 4 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_9dad0 : bv 32 := 0xfea5b823.
Lemma F_9dad0 : fetch_word Ubsan.M.loaded_segments (0x9db1c : word) = Some W_9dad0.
Proof. vm_refl. Qed.
Lemma D_9dad0 : decode_any W_9dad0 = Some (Store SZ8 11 10 4080, 4%Z).
Proof. vm_refl. Qed.

Definition W_9dad4 : bv 32 := 0x00813083.
Lemma F_9dad4 : fetch_word Ubsan.M.loaded_segments (0x9db20 : word) = Some W_9dad4.
Proof. vm_refl. Qed.
Lemma D_9dad4 : decode_any W_9dad4 = Some (Load SZ8 true 1 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_9dad8 : bv 32 := 0x01010113.
Lemma F_9dad8 : fetch_word Ubsan.M.loaded_segments (0x9db24 : word) = Some W_9dad8.
Proof. vm_refl. Qed.
Lemma D_9dad8 : decode_any W_9dad8 = Some (OpImm ALU_ADD 2 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_9dadc : bv 32 := 0x00008067.
Lemma F_9dadc : fetch_word Ubsan.M.loaded_segments (0x9db28 : word) = Some W_9dadc.
Proof. vm_refl. Qed.
Lemma D_9dadc : decode_any W_9dadc = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_9dae8 : bv 32 := 0xfffff5b7.
Lemma F_9dae8 : fetch_word Ubsan.M.loaded_segments (0x9db34 : word) = Some W_9dae8.
Proof. vm_refl. Qed.
Lemma D_9dae8 : decode_any W_9dae8 = Some (Lui 11 1048575, 4%Z).
Proof. vm_refl. Qed.

Definition W_9daec : bv 32 := 0x0015859b.
Lemma F_9daec : fetch_word Ubsan.M.loaded_segments (0x9db38 : word) = Some W_9daec.
Proof. vm_refl. Qed.
Lemma D_9daec : decode_any W_9daec = Some (OpImm32 11 11 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_9daf0 : bv 32 := 0x02b56663.
Lemma F_9daf0 : fetch_word Ubsan.M.loaded_segments (0x9db3c : word) = Some W_9daf0.
Proof. vm_refl. Qed.
Lemma D_9daf0 : decode_any W_9daf0 = Some (Branch BC_LTU 10 11 44, 4%Z).
Proof. vm_refl. Qed.

Definition W_9db1c : bv 32 := 0x00008067.
Lemma F_9db1c : fetch_word Ubsan.M.loaded_segments (0x9db68 : word) = Some W_9db1c.
Proof. vm_refl. Qed.
Lemma D_9db1c : decode_any W_9db1c = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.
