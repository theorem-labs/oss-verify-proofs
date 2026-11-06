(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.

Module D_co8nq.
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.varnish.esi_parse_fuzzer.images Require Import Plain.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.

(* [comment removed for export] *)
Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

(* [comment removed for export] *)
Definition W_2b03c : bv 32 := 0x00f680a3.
Lemma F_2b03c : fetch_word Plain.M.loaded_segments (0x2b03c : word) = Some W_2b03c.
Proof. vm_refl. Qed.
Lemma D_2b03c : decode_any W_2b03c = Some (Store SZ1 13 15 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2b040 : bv 32 := 0x00080693.
Lemma F_2b040 : fetch_word Plain.M.loaded_segments (0x2b040 : word) = Some W_2b040.
Proof. vm_refl. Qed.
Lemma D_2b040 : decode_any W_2b040 = Some (OpImm ALU_ADD 13 16 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2b044 : bv 32 := 0x00167613.
Lemma F_2b044 : fetch_word Plain.M.loaded_segments (0x2b044 : word) = Some W_2b044.
Proof. vm_refl. Qed.
Lemma D_2b044 : decode_any W_2b044 = Some (OpImm ALU_AND 12 12 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2b048 : bv 32 := 0xfc060ee3.
Lemma F_2b048 : fetch_word Plain.M.loaded_segments (0x2b048 : word) = Some W_2b048.
Proof. vm_refl. Qed.
Lemma D_2b048 : decode_any W_2b048 = Some (Branch BC_EQ 12 0 8156, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2b04c : bv 32 := 0x0005c583.
Lemma F_2b04c : fetch_word Plain.M.loaded_segments (0x2b04c : word) = Some W_2b04c.
Proof. vm_refl. Qed.
Lemma D_2b04c : decode_any W_2b04c = Some (Load SZ1 false 11 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2b050 : bv 32 := 0x00b68023.
Lemma F_2b050 : fetch_word Plain.M.loaded_segments (0x2b050 : word) = Some W_2b050.
Proof. vm_refl. Qed.
Lemma D_2b050 : decode_any W_2b050 = Some (Store SZ1 13 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2b054 : bv 32 := 0x00008067.
Lemma F_2b054 : fetch_word Plain.M.loaded_segments (0x2b054 : word) = Some W_2b054.
Proof. vm_refl. Qed.
Lemma D_2b054 : decode_any W_2b054 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2b058 : bv 32 := 0x0e060a63.
Lemma F_2b058 : fetch_word Plain.M.loaded_segments (0x2b058 : word) = Some W_2b058.
Proof. vm_refl. Qed.
Lemma D_2b058 : decode_any W_2b058 = Some (Branch BC_EQ 12 0 244, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2b05c : bv 32 := 0x00b50023.
Lemma F_2b05c : fetch_word Plain.M.loaded_segments (0x2b05c : word) = Some W_2b05c.
Proof. vm_refl. Qed.
Lemma D_2b05c : decode_any W_2b05c = Some (Store SZ1 10 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2b060 : bv 32 := 0x00c506b3.
Lemma F_2b060 : fetch_word Plain.M.loaded_segments (0x2b060 : word) = Some W_2b060.
Proof. vm_refl. Qed.
Lemma D_2b060 : decode_any W_2b060 = Some (Op ALU_ADD 13 10 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2b064 : bv 32 := 0x00300713.
Lemma F_2b064 : fetch_word Plain.M.loaded_segments (0x2b064 : word) = Some W_2b064.
Proof. vm_refl. Qed.
Lemma D_2b064 : decode_any W_2b064 = Some (OpImm ALU_ADD 14 0 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2b068 : bv 32 := 0xfeb68fa3.
Lemma F_2b068 : fetch_word Plain.M.loaded_segments (0x2b068 : word) = Some W_2b068.
Proof. vm_refl. Qed.
Lemma D_2b068 : decode_any W_2b068 = Some (Store SZ1 13 11 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2b06c : bv 32 := 0x0ee66063.
Lemma F_2b06c : fetch_word Plain.M.loaded_segments (0x2b06c : word) = Some W_2b06c.
Proof. vm_refl. Qed.
Lemma D_2b06c : decode_any W_2b06c = Some (Branch BC_LTU 12 14 224, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2b070 : bv 32 := 0x00b500a3.
Lemma F_2b070 : fetch_word Plain.M.loaded_segments (0x2b070 : word) = Some W_2b070.
Proof. vm_refl. Qed.
Lemma D_2b070 : decode_any W_2b070 = Some (Store SZ1 10 11 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2b074 : bv 32 := 0x00b50123.
Lemma F_2b074 : fetch_word Plain.M.loaded_segments (0x2b074 : word) = Some W_2b074.
Proof. vm_refl. Qed.
Lemma D_2b074 : decode_any W_2b074 = Some (Store SZ1 10 11 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2b078 : bv 32 := 0x00700713.
Lemma F_2b078 : fetch_word Plain.M.loaded_segments (0x2b078 : word) = Some W_2b078.
Proof. vm_refl. Qed.
Lemma D_2b078 : decode_any W_2b078 = Some (OpImm ALU_ADD 14 0 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2b07c : bv 32 := 0xfeb68ea3.
Lemma F_2b07c : fetch_word Plain.M.loaded_segments (0x2b07c : word) = Some W_2b07c.
Proof. vm_refl. Qed.
Lemma D_2b07c : decode_any W_2b07c = Some (Store SZ1 13 11 4093, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2b080 : bv 32 := 0xfeb68f23.
Lemma F_2b080 : fetch_word Plain.M.loaded_segments (0x2b080 : word) = Some W_2b080.
Proof. vm_refl. Qed.
Lemma D_2b080 : decode_any W_2b080 = Some (Store SZ1 13 11 4094, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2b084 : bv 32 := 0x0ce66463.
Lemma F_2b084 : fetch_word Plain.M.loaded_segments (0x2b084 : word) = Some W_2b084.
Proof. vm_refl. Qed.
Lemma D_2b084 : decode_any W_2b084 = Some (Branch BC_LTU 12 14 200, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2b088 : bv 32 := 0x00b501a3.
Lemma F_2b088 : fetch_word Plain.M.loaded_segments (0x2b088 : word) = Some W_2b088.
Proof. vm_refl. Qed.
Lemma D_2b088 : decode_any W_2b088 = Some (Store SZ1 10 11 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2b08c : bv 32 := 0x00900793.
Lemma F_2b08c : fetch_word Plain.M.loaded_segments (0x2b08c : word) = Some W_2b08c.
Proof. vm_refl. Qed.
Lemma D_2b08c : decode_any W_2b08c = Some (OpImm ALU_ADD 15 0 9, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2b090 : bv 32 := 0xfeb68e23.
Lemma F_2b090 : fetch_word Plain.M.loaded_segments (0x2b090 : word) = Some W_2b090.
Proof. vm_refl. Qed.
Lemma D_2b090 : decode_any W_2b090 = Some (Store SZ1 13 11 4092, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2b094 : bv 32 := 0x0af66c63.
Lemma F_2b094 : fetch_word Plain.M.loaded_segments (0x2b094 : word) = Some W_2b094.
Proof. vm_refl. Qed.
Lemma D_2b094 : decode_any W_2b094 = Some (Branch BC_LTU 12 15 184, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2b098 : bv 32 := 0x40a006bb.
Lemma F_2b098 : fetch_word Plain.M.loaded_segments (0x2b098 : word) = Some W_2b098.
Proof. vm_refl. Qed.
Lemma D_2b098 : decode_any W_2b098 = Some (Op32 ALU_SUB 13 0 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2b09c : bv 32 := 0x03859813.
Lemma F_2b09c : fetch_word Plain.M.loaded_segments (0x2b09c : word) = Some W_2b09c.
Proof. vm_refl. Qed.
Lemma D_2b09c : decode_any W_2b09c = Some (ShiftImm ALU_SLL 16 11 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2b0a0 : bv 32 := 0x101015b7.
Lemma F_2b0a0 : fetch_word Plain.M.loaded_segments (0x2b0a0 : word) = Some W_2b0a0.
Proof. vm_refl. Qed.
Lemma D_2b0a0 : decode_any W_2b0a0 = Some (Lui 11 65793, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2b0a4 : bv 32 := 0x0036f693.
Lemma F_2b0a4 : fetch_word Plain.M.loaded_segments (0x2b0a4 : word) = Some W_2b0a4.
Proof. vm_refl. Qed.
Lemma D_2b0a4 : decode_any W_2b0a4 = Some (OpImm ALU_AND 13 13 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2b0a8 : bv 32 := 0x00459713.
Lemma F_2b0a8 : fetch_word Plain.M.loaded_segments (0x2b0a8 : word) = Some W_2b0a8.
Proof. vm_refl. Qed.
Lemma D_2b0a8 : decode_any W_2b0a8 = Some (ShiftImm ALU_SLL 14 11 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2b0ac : bv 32 := 0x40d60633.
Lemma F_2b0ac : fetch_word Plain.M.loaded_segments (0x2b0ac : word) = Some W_2b0ac.
Proof. vm_refl. Qed.
Lemma D_2b0ac : decode_any W_2b0ac = Some (Op ALU_SUB 12 12 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2b0b0 : bv 32 := 0x00d505b3.
Lemma F_2b0b0 : fetch_word Plain.M.loaded_segments (0x2b0b0 : word) = Some W_2b0b0.
Proof. vm_refl. Qed.
Lemma D_2b0b0 : decode_any W_2b0b0 = Some (Op ALU_ADD 11 10 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2b0b4 : bv 32 := 0x10070693.
Lemma F_2b0b4 : fetch_word Plain.M.loaded_segments (0x2b0b4 : word) = Some W_2b0b4.
Proof. vm_refl. Qed.
Lemma D_2b0b4 : decode_any W_2b0b4 = Some (OpImm ALU_ADD 13 14 256, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2b0b8 : bv 32 := 0xffc67713.
Lemma F_2b0b8 : fetch_word Plain.M.loaded_segments (0x2b0b8 : word) = Some W_2b0b8.
Proof. vm_refl. Qed.
Lemma D_2b0b8 : decode_any W_2b0b8 = Some (OpImm ALU_AND 14 12 4092, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2b0bc : bv 32 := 0x02d83633.
Lemma F_2b0bc : fetch_word Plain.M.loaded_segments (0x2b0bc : word) = Some W_2b0bc.
Proof. vm_refl. Qed.
Lemma D_2b0bc : decode_any W_2b0bc = Some (Mul M_MULHU 12 16 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2b0c0 : bv 32 := 0x00c5a023.
Lemma F_2b0c0 : fetch_word Plain.M.loaded_segments (0x2b0c0 : word) = Some W_2b0c0.
Proof. vm_refl. Qed.
Lemma D_2b0c0 : decode_any W_2b0c0 = Some (Store SZ4 11 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2b0c4 : bv 32 := 0x00e586b3.
Lemma F_2b0c4 : fetch_word Plain.M.loaded_segments (0x2b0c4 : word) = Some W_2b0c4.
Proof. vm_refl. Qed.
Lemma D_2b0c4 : decode_any W_2b0c4 = Some (Op ALU_ADD 13 11 14, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2b0c8 : bv 32 := 0xfec6ae23.
Lemma F_2b0c8 : fetch_word Plain.M.loaded_segments (0x2b0c8 : word) = Some W_2b0c8.
Proof. vm_refl. Qed.
Lemma D_2b0c8 : decode_any W_2b0c8 = Some (Store SZ4 13 12 4092, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2b0cc : bv 32 := 0x08f76063.
Lemma F_2b0cc : fetch_word Plain.M.loaded_segments (0x2b0cc : word) = Some W_2b0cc.
Proof. vm_refl. Qed.
Lemma D_2b0cc : decode_any W_2b0cc = Some (Branch BC_LTU 14 15 128, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2b0d0 : bv 32 := 0x00c5a223.
Lemma F_2b0d0 : fetch_word Plain.M.loaded_segments (0x2b0d0 : word) = Some W_2b0d0.
Proof. vm_refl. Qed.
Lemma D_2b0d0 : decode_any W_2b0d0 = Some (Store SZ4 11 12 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2b0d4 : bv 32 := 0x00c5a423.
Lemma F_2b0d4 : fetch_word Plain.M.loaded_segments (0x2b0d4 : word) = Some W_2b0d4.
Proof. vm_refl. Qed.
Lemma D_2b0d4 : decode_any W_2b0d4 = Some (Store SZ4 11 12 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2b0d8 : bv 32 := 0x01900793.
Lemma F_2b0d8 : fetch_word Plain.M.loaded_segments (0x2b0d8 : word) = Some W_2b0d8.
Proof. vm_refl. Qed.
Lemma D_2b0d8 : decode_any W_2b0d8 = Some (OpImm ALU_ADD 15 0 25, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2b0dc : bv 32 := 0xfec6aa23.
Lemma F_2b0dc : fetch_word Plain.M.loaded_segments (0x2b0dc : word) = Some W_2b0dc.
Proof. vm_refl. Qed.
Lemma D_2b0dc : decode_any W_2b0dc = Some (Store SZ4 13 12 4084, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2b0e0 : bv 32 := 0xfec6ac23.
Lemma F_2b0e0 : fetch_word Plain.M.loaded_segments (0x2b0e0 : word) = Some W_2b0e0.
Proof. vm_refl. Qed.
Lemma D_2b0e0 : decode_any W_2b0e0 = Some (Store SZ4 13 12 4088, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2b0e4 : bv 32 := 0x06f76463.
Lemma F_2b0e4 : fetch_word Plain.M.loaded_segments (0x2b0e4 : word) = Some W_2b0e4.
Proof. vm_refl. Qed.
Lemma D_2b0e4 : decode_any W_2b0e4 = Some (Branch BC_LTU 14 15 104, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2b0e8 : bv 32 := 0x00c5a623.
Lemma F_2b0e8 : fetch_word Plain.M.loaded_segments (0x2b0e8 : word) = Some W_2b0e8.
Proof. vm_refl. Qed.
Lemma D_2b0e8 : decode_any W_2b0e8 = Some (Store SZ4 11 12 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2b0ec : bv 32 := 0x00c5a823.
Lemma F_2b0ec : fetch_word Plain.M.loaded_segments (0x2b0ec : word) = Some W_2b0ec.
Proof. vm_refl. Qed.
Lemma D_2b0ec : decode_any W_2b0ec = Some (Store SZ4 11 12 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2b0f0 : bv 32 := 0x00c5aa23.
Lemma F_2b0f0 : fetch_word Plain.M.loaded_segments (0x2b0f0 : word) = Some W_2b0f0.
Proof. vm_refl. Qed.
Lemma D_2b0f0 : decode_any W_2b0f0 = Some (Store SZ4 11 12 20, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2b0f4 : bv 32 := 0x00c5ac23.
Lemma F_2b0f4 : fetch_word Plain.M.loaded_segments (0x2b0f4 : word) = Some W_2b0f4.
Proof. vm_refl. Qed.
Lemma D_2b0f4 : decode_any W_2b0f4 = Some (Store SZ4 11 12 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2b0f8 : bv 32 := 0x0045f793.
Lemma F_2b0f8 : fetch_word Plain.M.loaded_segments (0x2b0f8 : word) = Some W_2b0f8.
Proof. vm_refl. Qed.
Lemma D_2b0f8 : decode_any W_2b0f8 = Some (OpImm ALU_AND 15 11 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2b0fc : bv 32 := 0x02000813.
Lemma F_2b0fc : fetch_word Plain.M.loaded_segments (0x2b0fc : word) = Some W_2b0fc.
Proof. vm_refl. Qed.
Lemma D_2b0fc : decode_any W_2b0fc = Some (OpImm ALU_ADD 16 0 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2b100 : bv 32 := 0x01878793.
Lemma F_2b100 : fetch_word Plain.M.loaded_segments (0x2b100 : word) = Some W_2b100.
Proof. vm_refl. Qed.
Lemma D_2b100 : decode_any W_2b100 = Some (OpImm ALU_ADD 15 15 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2b104 : bv 32 := 0x40f70733.
Lemma F_2b104 : fetch_word Plain.M.loaded_segments (0x2b104 : word) = Some W_2b104.
Proof. vm_refl. Qed.
Lemma D_2b104 : decode_any W_2b104 = Some (Op ALU_SUB 14 14 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2b108 : bv 32 := 0xfec6a223.
Lemma F_2b108 : fetch_word Plain.M.loaded_segments (0x2b108 : word) = Some W_2b108.
Proof. vm_refl. Qed.
Lemma D_2b108 : decode_any W_2b108 = Some (Store SZ4 13 12 4068, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2b10c : bv 32 := 0xfec6a423.
Lemma F_2b10c : fetch_word Plain.M.loaded_segments (0x2b10c : word) = Some W_2b10c.
Proof. vm_refl. Qed.
Lemma D_2b10c : decode_any W_2b10c = Some (Store SZ4 13 12 4072, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2b110 : bv 32 := 0xfec6a623.
Lemma F_2b110 : fetch_word Plain.M.loaded_segments (0x2b110 : word) = Some W_2b110.
Proof. vm_refl. Qed.
Lemma D_2b110 : decode_any W_2b110 = Some (Store SZ4 13 12 4076, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2b114 : bv 32 := 0xfec6a823.
Lemma F_2b114 : fetch_word Plain.M.loaded_segments (0x2b114 : word) = Some W_2b114.
Proof. vm_refl. Qed.
Lemma D_2b114 : decode_any W_2b114 = Some (Store SZ4 13 12 4080, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2b118 : bv 32 := 0x03076a63.
Lemma F_2b118 : fetch_word Plain.M.loaded_segments (0x2b118 : word) = Some W_2b118.
Proof. vm_refl. Qed.
Lemma D_2b118 : decode_any W_2b118 = Some (Branch BC_LTU 14 16 52, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2b11c : bv 32 := 0x02061613.
Lemma F_2b11c : fetch_word Plain.M.loaded_segments (0x2b11c : word) = Some W_2b11c.
Proof. vm_refl. Qed.
Lemma D_2b11c : decode_any W_2b11c = Some (ShiftImm ALU_SLL 12 12 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2b120 : bv 32 := 0x00f585b3.
Lemma F_2b120 : fetch_word Plain.M.loaded_segments (0x2b120 : word) = Some W_2b120.
Proof. vm_refl. Qed.
Lemma D_2b120 : decode_any W_2b120 = Some (Op ALU_ADD 11 11 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2b124 : bv 32 := 0x02065693.
Lemma F_2b124 : fetch_word Plain.M.loaded_segments (0x2b124 : word) = Some W_2b124.
Proof. vm_refl. Qed.
Lemma D_2b124 : decode_any W_2b124 = Some (ShiftImm ALU_SRL 13 12 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2b128 : bv 32 := 0x00d66633.
Lemma F_2b128 : fetch_word Plain.M.loaded_segments (0x2b128 : word) = Some W_2b128.
Proof. vm_refl. Qed.
Lemma D_2b128 : decode_any W_2b128 = Some (Op ALU_OR 12 12 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2b12c : bv 32 := 0x01f00693.
Lemma F_2b12c : fetch_word Plain.M.loaded_segments (0x2b12c : word) = Some W_2b12c.
Proof. vm_refl. Qed.
Lemma D_2b12c : decode_any W_2b12c = Some (OpImm ALU_ADD 13 0 31, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2b130 : bv 32 := 0x00c5b023.
Lemma F_2b130 : fetch_word Plain.M.loaded_segments (0x2b130 : word) = Some W_2b130.
Proof. vm_refl. Qed.
Lemma D_2b130 : decode_any W_2b130 = Some (Store SZ8 11 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2b134 : bv 32 := 0x00c5b423.
Lemma F_2b134 : fetch_word Plain.M.loaded_segments (0x2b134 : word) = Some W_2b134.
Proof. vm_refl. Qed.
Lemma D_2b134 : decode_any W_2b134 = Some (Store SZ8 11 12 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2b138 : bv 32 := 0x00c5b823.
Lemma F_2b138 : fetch_word Plain.M.loaded_segments (0x2b138 : word) = Some W_2b138.
Proof. vm_refl. Qed.
Lemma D_2b138 : decode_any W_2b138 = Some (Store SZ8 11 12 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2b13c : bv 32 := 0x00c5bc23.
Lemma F_2b13c : fetch_word Plain.M.loaded_segments (0x2b13c : word) = Some W_2b13c.
Proof. vm_refl. Qed.
Lemma D_2b13c : decode_any W_2b13c = Some (Store SZ8 11 12 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2b140 : bv 32 := 0xfe070713.
Lemma F_2b140 : fetch_word Plain.M.loaded_segments (0x2b140 : word) = Some W_2b140.
Proof. vm_refl. Qed.
Lemma D_2b140 : decode_any W_2b140 = Some (OpImm ALU_ADD 14 14 4064, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2b144 : bv 32 := 0x02058593.
Lemma F_2b144 : fetch_word Plain.M.loaded_segments (0x2b144 : word) = Some W_2b144.
Proof. vm_refl. Qed.
Lemma D_2b144 : decode_any W_2b144 = Some (OpImm ALU_ADD 11 11 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2b148 : bv 32 := 0xfee6e4e3.
Lemma F_2b148 : fetch_word Plain.M.loaded_segments (0x2b148 : word) = Some W_2b148.
Proof. vm_refl. Qed.
Lemma D_2b148 : decode_any W_2b148 = Some (Branch BC_LTU 13 14 8168, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2b14c : bv 32 := 0x00008067.
Lemma F_2b14c : fetch_word Plain.M.loaded_segments (0x2b14c : word) = Some W_2b14c.
Proof. vm_refl. Qed.
Lemma D_2b14c : decode_any W_2b14c = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2b41c : bv 32 := 0xfe010113.
Lemma F_2b41c : fetch_word Plain.M.loaded_segments (0x2b41c : word) = Some W_2b41c.
Proof. vm_refl. Qed.
Lemma D_2b41c : decode_any W_2b41c = Some (OpImm ALU_ADD 2 2 4064, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2b420 : bv 32 := 0x00113c23.
Lemma F_2b420 : fetch_word Plain.M.loaded_segments (0x2b420 : word) = Some W_2b420.
Proof. vm_refl. Qed.
Lemma D_2b420 : decode_any W_2b420 = Some (Store SZ8 2 1 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2b424 : bv 32 := 0x00813823.
Lemma F_2b424 : fetch_word Plain.M.loaded_segments (0x2b424 : word) = Some W_2b424.
Proof. vm_refl. Qed.
Lemma D_2b424 : decode_any W_2b424 = Some (Store SZ8 2 8 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2b428 : bv 32 := 0x00913423.
Lemma F_2b428 : fetch_word Plain.M.loaded_segments (0x2b428 : word) = Some W_2b428.
Proof. vm_refl. Qed.
Lemma D_2b428 : decode_any W_2b428 = Some (Store SZ8 2 9 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2b42c : bv 32 := 0x00058413.
Lemma F_2b42c : fetch_word Plain.M.loaded_segments (0x2b42c : word) = Some W_2b42c.
Proof. vm_refl. Qed.
Lemma D_2b42c : decode_any W_2b42c = Some (OpImm ALU_ADD 8 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2b430 : bv 32 := 0x00050493.
Lemma F_2b430 : fetch_word Plain.M.loaded_segments (0x2b430 : word) = Some W_2b430.
Proof. vm_refl. Qed.
Lemma D_2b430 : decode_any W_2b430 = Some (OpImm ALU_ADD 9 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2b434 : bv 32 := 0x00000593.
Lemma F_2b434 : fetch_word Plain.M.loaded_segments (0x2b434 : word) = Some W_2b434.
Proof. vm_refl. Qed.
Lemma D_2b434 : decode_any W_2b434 = Some (OpImm ALU_ADD 11 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2b438 : bv 32 := 0x00040613.
Lemma F_2b438 : fetch_word Plain.M.loaded_segments (0x2b438 : word) = Some W_2b438.
Proof. vm_refl. Qed.
Lemma D_2b438 : decode_any W_2b438 = Some (OpImm ALU_ADD 12 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2b43c : bv 32 := 0xf1cff0ef.
Lemma F_2b43c : fetch_word Plain.M.loaded_segments (0x2b43c : word) = Some W_2b43c.
Proof. vm_refl. Qed.
Lemma D_2b43c : decode_any W_2b43c = Some (Jal 1 2094876, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2b440 : bv 32 := 0x00050463.
Lemma F_2b440 : fetch_word Plain.M.loaded_segments (0x2b440 : word) = Some W_2b440.
Proof. vm_refl. Qed.
Lemma D_2b440 : decode_any W_2b440 = Some (Branch BC_EQ 10 0 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2b444 : bv 32 := 0x40950433.
Lemma F_2b444 : fetch_word Plain.M.loaded_segments (0x2b444 : word) = Some W_2b444.
Proof. vm_refl. Qed.
Lemma D_2b444 : decode_any W_2b444 = Some (Op ALU_SUB 8 10 9, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2b448 : bv 32 := 0x00040513.
Lemma F_2b448 : fetch_word Plain.M.loaded_segments (0x2b448 : word) = Some W_2b448.
Proof. vm_refl. Qed.
Lemma D_2b448 : decode_any W_2b448 = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2b44c : bv 32 := 0x01813083.
Lemma F_2b44c : fetch_word Plain.M.loaded_segments (0x2b44c : word) = Some W_2b44c.
Proof. vm_refl. Qed.
Lemma D_2b44c : decode_any W_2b44c = Some (Load SZ8 true 1 2 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2b450 : bv 32 := 0x01013403.
Lemma F_2b450 : fetch_word Plain.M.loaded_segments (0x2b450 : word) = Some W_2b450.
Proof. vm_refl. Qed.
Lemma D_2b450 : decode_any W_2b450 = Some (Load SZ8 true 8 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2b454 : bv 32 := 0x00813483.
Lemma F_2b454 : fetch_word Plain.M.loaded_segments (0x2b454 : word) = Some W_2b454.
Proof. vm_refl. Qed.
Lemma D_2b454 : decode_any W_2b454 = Some (Load SZ8 true 9 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2b458 : bv 32 := 0x02010113.
Lemma F_2b458 : fetch_word Plain.M.loaded_segments (0x2b458 : word) = Some W_2b458.
Proof. vm_refl. Qed.
Lemma D_2b458 : decode_any W_2b458 = Some (OpImm ALU_ADD 2 2 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2b45c : bv 32 := 0x00008067.
Lemma F_2b45c : fetch_word Plain.M.loaded_segments (0x2b45c : word) = Some W_2b45c.
Proof. vm_refl. Qed.
Lemma D_2b45c : decode_any W_2b45c = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2b460 : bv 32 := 0x00037597.
Lemma F_2b460 : fetch_word Plain.M.loaded_segments (0x2b460 : word) = Some W_2b460.
Proof. vm_refl. Qed.
Lemma D_2b460 : decode_any W_2b460 = Some (Auipc 11 55, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2b464 : bv 32 := 0xf8b58683.
Lemma F_2b464 : fetch_word Plain.M.loaded_segments (0x2b464 : word) = Some W_2b464.
Proof. vm_refl. Qed.
Lemma D_2b464 : decode_any W_2b464 = Some (Load SZ1 true 13 11 3979, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2b468 : bv 32 := 0x1e068863.
Lemma F_2b468 : fetch_word Plain.M.loaded_segments (0x2b468 : word) = Some W_2b468.
Proof. vm_refl. Qed.
Lemma D_2b468 : decode_any W_2b468 = Some (Branch BC_EQ 13 0 496, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2b658 : bv 32 := 0x00008067.
Lemma F_2b658 : fetch_word Plain.M.loaded_segments (0x2b658 : word) = Some W_2b658.
Proof. vm_refl. Qed.
Lemma D_2b658 : decode_any W_2b658 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2b6e8 : bv 32 := 0x00052583.
Lemma F_2b6e8 : fetch_word Plain.M.loaded_segments (0x2b6e8 : word) = Some W_2b6e8.
Proof. vm_refl. Qed.
Lemma D_2b6e8 : decode_any W_2b6e8 = Some (Load SZ4 true 11 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2b6ec : bv 32 := 0x0005c463.
Lemma F_2b6ec : fetch_word Plain.M.loaded_segments (0x2b6ec : word) = Some W_2b6ec.
Proof. vm_refl. Qed.
Lemma D_2b6ec : decode_any W_2b6ec = Some (Branch BC_LT 11 0 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2b6f0 : bv 32 := 0x00008067.
Lemma F_2b6f0 : fetch_word Plain.M.loaded_segments (0x2b6f0 : word) = Some W_2b6f0.
Proof. vm_refl. Qed.
Lemma D_2b6f0 : decode_any W_2b6f0 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2bd80 : bv 32 := 0x00050213.
Lemma F_2bd80 : fetch_word Plain.M.loaded_segments (0x2bd80 : word) = Some W_2bd80.
Proof. vm_refl. Qed.
Lemma D_2bd80 : decode_any W_2bd80 = Some (OpImm ALU_ADD 4 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2bd84 : bv 32 := 0x00000513.
Lemma F_2bd84 : fetch_word Plain.M.loaded_segments (0x2bd84 : word) = Some W_2bd84.
Proof. vm_refl. Qed.
Lemma D_2bd84 : decode_any W_2bd84 = Some (OpImm ALU_ADD 10 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2bd88 : bv 32 := 0x00008067.
Lemma F_2bd88 : fetch_word Plain.M.loaded_segments (0x2bd88 : word) = Some W_2bd88.
Proof. vm_refl. Qed.
Lemma D_2bd88 : decode_any W_2bd88 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.
End D_co8nq.


Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Acfg.
Import ListNotations.
Local Open Scope Z_scope.

Class BWorld : Type := mkBWorld {
  bw_on : bool;                      (* [comment removed for export] *)
  bw_lim : Z;                        (* [comment removed for export] *)
  bw_lim_ok : if bw_on then True else State.source_alloc_limit <= bw_lim
}.

(* [comment removed for export] *)
Definition bw_pinned : BWorld :=
  {| bw_on := false; bw_lim := State.source_alloc_limit; bw_lim_ok := Z.le_refl _ |}.
Definition bw_premise (lim : Z) : BWorld :=
  {| bw_on := true; bw_lim := lim; bw_lim_ok := I |}.

Section BW.
Context {BW : BWorld}.

(* [comment removed for export] *)
Definition bw_limit (L : Z) : Prop := if bw_on then True else State.source_alloc_limit <= L.

Lemma bw_limit_lim : bw_limit bw_lim.
Proof. unfold bw_limit. exact bw_lim_ok. Qed.

Lemma bw_limit_of_le : forall L, State.source_alloc_limit <= L -> bw_limit L.
Proof. intros L H. unfold bw_limit. destruct bw_on; [exact I | exact H]. Qed.

Lemma bw_limit_off : forall L, bw_on = false -> bw_limit L -> State.source_alloc_limit <= L.
Proof. intros L E H. unfold bw_limit in H. rewrite E in H. exact H. Qed.

(* [comment removed for export] *)
Definition bw_gate (i : SyscallInput) (m : Model) : Prop :=
  if bw_on then alloc_budget_refused_b i m = false else True.

Lemma bw_gate_off : forall i m, bw_on = false -> bw_gate i m.
Proof. intros i m E. unfold bw_gate. rewrite E. exact I. Qed.

Lemma bw_gate_on : forall i m, bw_on = true -> bw_gate i m -> alloc_budget_refused_b i m = false.
Proof. intros i m E H. unfold bw_gate in H. rewrite E in H. exact H. Qed.

Section WithSegs.
Variable segs : list Segment.

(* [comment removed for export] *)
Definition bw_excuse (c : config) : Prop :=
  if bw_on then budget_refused_at segs c else False.

(* [comment removed for export] *)
Definition never_excused (c0 : config) : Prop :=
  forall tr c, star_cfg segs ACFG c0 tr c -> ~ bw_excuse c.

Lemma never_excused_off : bw_on = false -> forall c0, never_excused c0.
Proof. intros E c0 tr c _ H. unfold bw_excuse in H. rewrite E in H. exact H. Qed.

Lemma never_excused_on : forall c0,
  ~ reaches_budget_refused_cfg segs ACFG c0 -> never_excused c0.
Proof.
  intros c0 Hn tr c Hstar Hex. unfold bw_excuse in Hex.
  destruct bw_on; [| exact Hex]. apply Hn. exists tr, c. split; assumption.
Qed.

Lemma never_excused_here : forall c, never_excused c -> ~ bw_excuse c.
Proof. intros c H. exact (H [] c (star_cfg_refl segs ACFG c)). Qed.

Lemma never_excused_star : forall c tr c',
  never_excused c -> star_cfg segs ACFG c tr c' -> never_excused c'.
Proof.
  intros c tr c' H Hstar tr' c'' Hstar'.
  exact (H (tr ++ tr') c'' (star_cfg_trans segs _ _ _ _ _ Hstar Hstar')).
Qed.

Lemma never_excused_step : forall c evs c',
  never_excused c -> sstep_cfg segs ACFG c evs (SNext c') -> never_excused c'.
Proof.
  intros c evs c' H Hss. eapply never_excused_star; [exact H | apply star_cfg_one; exact Hss].
Qed.

(* [comment removed for export] *)
Lemma bw_gate_of_not_excused : forall ms model x8,
  m_halted model = None ->
  ms_svc_pending ms = Some x8 ->
  (forall eff model' evs,
     syscall_spec (sys_input segs ms x8) model (Ok eff model' evs) ->
     m_vm_lazy model' = []) ->
  ~ bw_excuse (mkCfg ms model) ->
  bw_gate (sys_input segs ms x8) model.
Proof.
  intros ms model x8 Hh Hsvc Hlazy Hne. unfold bw_gate, bw_excuse in *.
  destruct bw_on; [| exact I].
  destruct (alloc_budget_refused_b (sys_input segs ms x8) model) eqn:E; [| reflexivity].
  exfalso. apply Hne.
  exact (proj2 (budget_refused_at_no_lazy_syscall segs ms model x8 Hh Hsvc Hlazy) E).
Qed.

Corollary bw_gate_of_never_excused : forall ms model x8,
  m_halted model = None ->
  ms_svc_pending ms = Some x8 ->
  (forall eff model' evs,
     syscall_spec (sys_input segs ms x8) model (Ok eff model' evs) ->
     m_vm_lazy model' = []) ->
  never_excused (mkCfg ms model) ->
  bw_gate (sys_input segs ms x8) model.
Proof.
  intros ms model x8 Hh Hsvc Hlazy Hne.
  apply bw_gate_of_not_excused; [exact Hh | exact Hsvc | exact Hlazy | apply never_excused_here; exact Hne].
Qed.

End WithSegs.
End BW.

(* [comment removed for export] *)
Lemma never_excused_of_premise : forall lim segs c0,
  ~ reaches_budget_refused_cfg segs ACFG c0 -> @never_excused (bw_premise lim) segs c0.
Proof. intros lim segs c0 H. apply never_excused_on. exact H. Qed.

Lemma never_excused_pinned : forall segs c0, @never_excused bw_pinned segs c0.
Proof. intros segs c0. apply never_excused_off. reflexivity. Qed.

(* [comment removed for export] *)
Lemma abr_brk : forall i m, in_sysno i = Z_to_bv 64 214 ->
  alloc_budget_refused_b i m = Sys.Mm.Mmap.brk_budget_refused_b m (in_arg i 0).
Proof. intros i m E. unfold alloc_budget_refused_b. rewrite E. reflexivity. Qed.

Lemma abr_mremap : forall i m, in_sysno i = Z_to_bv 64 216 ->
  alloc_budget_refused_b i m
  = Sys.Mm.Mremap.mremap_budget_refused_b (in_arg i 0) (in_arg i 1) (in_arg i 2) (in_arg i 3) m.
Proof. intros i m E. unfold alloc_budget_refused_b. rewrite E. reflexivity. Qed.

Lemma abr_mmap : forall i m, in_sysno i = Z_to_bv 64 222 ->
  alloc_budget_refused_b i m
  = Sys.Mm.Mmap.mmap_budget_refused_b (in_arg i 0) (in_arg i 1) (in_arg i 2) (in_arg i 3) (in_arg i 4) (in_arg i 5) m.
Proof. intros i m E. unfold alloc_budget_refused_b. rewrite E. reflexivity. Qed.

Lemma abr_mprotect : forall i m, in_sysno i = Z_to_bv 64 226 ->
  alloc_budget_refused_b i m
  = Sys.Mm.Mprotect.mprotect_budget_refused_b (in_arg i 0) (in_arg i 1) (in_arg i 2) m.
Proof. intros i m E. unfold alloc_budget_refused_b. rewrite E. reflexivity. Qed.

Lemma abr_other : forall i m,
  bv_unsigned (in_sysno i) <> 214 -> bv_unsigned (in_sysno i) <> 216 ->
  bv_unsigned (in_sysno i) <> 222 -> bv_unsigned (in_sysno i) <> 226 ->
  alloc_budget_refused_b i m = false.
Proof.
  intros i m H1 H2 H3 H4. apply alloc_budget_refused_b_outside.
  cbn [alloc_mark_sysnos In]. intros [E|[E|[E|[E|[]]]]]; congruence.
Qed.
