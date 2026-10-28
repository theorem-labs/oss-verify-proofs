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
Definition W_3b830 : bv 32 := 0x00008067.
Lemma F_3b830 : fetch_word Ubsan.M.loaded_segments (0x3ef88 : word) = Some W_3b830.
Proof. vm_refl. Qed.
Lemma D_3b830 : decode_any W_3b830 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3b834 : bv 32 := 0xe8010113.
Lemma F_3b834 : fetch_word Ubsan.M.loaded_segments (0x3ef8c : word) = Some W_3b834.
Proof. vm_refl. Qed.
Lemma D_3b834 : decode_any W_3b834 = Some (OpImm ALU_ADD 2 2 3712, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3b838 : bv 32 := 0x16113c23.
Lemma F_3b838 : fetch_word Ubsan.M.loaded_segments (0x3ef90 : word) = Some W_3b838.
Proof. vm_refl. Qed.
Lemma D_3b838 : decode_any W_3b838 = Some (Store SZ8 2 1 376, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3b83c : bv 32 := 0x16813823.
Lemma F_3b83c : fetch_word Ubsan.M.loaded_segments (0x3ef94 : word) = Some W_3b83c.
Proof. vm_refl. Qed.
Lemma D_3b83c : decode_any W_3b83c = Some (Store SZ8 2 8 368, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3b840 : bv 32 := 0x16913423.
Lemma F_3b840 : fetch_word Ubsan.M.loaded_segments (0x3ef98 : word) = Some W_3b840.
Proof. vm_refl. Qed.
Lemma D_3b840 : decode_any W_3b840 = Some (Store SZ8 2 9 360, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3b844 : bv 32 := 0x17213023.
Lemma F_3b844 : fetch_word Ubsan.M.loaded_segments (0x3ef9c : word) = Some W_3b844.
Proof. vm_refl. Qed.
Lemma D_3b844 : decode_any W_3b844 = Some (Store SZ8 2 18 352, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3b848 : bv 32 := 0x00058413.
Lemma F_3b848 : fetch_word Ubsan.M.loaded_segments (0x3efa0 : word) = Some W_3b848.
Proof. vm_refl. Qed.
Lemma D_3b848 : decode_any W_3b848 = Some (OpImm ALU_ADD 8 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3b84c : bv 32 := 0x00050493.
Lemma F_3b84c : fetch_word Ubsan.M.loaded_segments (0x3efa4 : word) = Some W_3b84c.
Proof. vm_refl. Qed.
Lemma D_3b84c : decode_any W_3b84c = Some (OpImm ALU_ADD 9 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3b850 : bv 32 := 0x03010513.
Lemma F_3b850 : fetch_word Ubsan.M.loaded_segments (0x3efa8 : word) = Some W_3b850.
Proof. vm_refl. Qed.
Lemma D_3b850 : decode_any W_3b850 = Some (OpImm ALU_ADD 10 2 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3b854 : bv 32 := 0x13000613.
Lemma F_3b854 : fetch_word Ubsan.M.loaded_segments (0x3efac : word) = Some W_3b854.
Proof. vm_refl. Qed.
Lemma D_3b854 : decode_any W_3b854 = Some (OpImm ALU_ADD 12 0 304, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3b858 : bv 32 := 0x00000593.
Lemma F_3b858 : fetch_word Ubsan.M.loaded_segments (0x3efb0 : word) = Some W_3b858.
Proof. vm_refl. Qed.
Lemma D_3b858 : decode_any W_3b858 = Some (OpImm ALU_ADD 11 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3b85c : bv 32 := 0x691070ef.
Lemma F_3b85c : fetch_word Ubsan.M.loaded_segments (0x3efb4 : word) = Some W_3b85c.
Proof. vm_refl. Qed.
Lemma D_3b85c : decode_any W_3b85c = Some (Jal 1 32400, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3b860 : bv 32 := 0x0000d517.
Lemma F_3b860 : fetch_word Ubsan.M.loaded_segments (0x3efb8 : word) = Some W_3b860.
Proof. vm_refl. Qed.
Lemma D_3b860 : decode_any W_3b860 = Some (Auipc 10 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3b864 : bv 32 := 0xcf853503.
Lemma F_3b864 : fetch_word Ubsan.M.loaded_segments (0x3efbc : word) = Some W_3b864.
Proof. vm_refl. Qed.
Lemma D_3b864 : decode_any W_3b864 = Some (Load SZ8 true 10 10 3320, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3b868 : bv 32 := 0x00953023.
Lemma F_3b868 : fetch_word Ubsan.M.loaded_segments (0x3efc0 : word) = Some W_3b868.
Proof. vm_refl. Qed.
Lemma D_3b868 : decode_any W_3b868 = Some (Store SZ8 10 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3b86c : bv 32 := 0x0004b503.
Lemma F_3b86c : fetch_word Ubsan.M.loaded_segments (0x3efc4 : word) = Some W_3b86c.
Proof. vm_refl. Qed.
Lemma D_3b86c : decode_any W_3b86c = Some (Load SZ8 true 10 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3b870 : bv 32 := 0x00848493.
Lemma F_3b870 : fetch_word Ubsan.M.loaded_segments (0x3efc8 : word) = Some W_3b870.
Proof. vm_refl. Qed.
Lemma D_3b870 : decode_any W_3b870 = Some (OpImm ALU_ADD 9 9 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3b874 : bv 32 := 0xfe051ce3.
Lemma F_3b874 : fetch_word Ubsan.M.loaded_segments (0x3efcc : word) = Some W_3b874.
Proof. vm_refl. Qed.
Lemma D_3b874 : decode_any W_3b874 = Some (Branch BC_NE 10 0 8184, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3b878 : bv 32 := 0x0003e517.
Lemma F_3b878 : fetch_word Ubsan.M.loaded_segments (0x3efd0 : word) = Some W_3b878.
Proof. vm_refl. Qed.
Lemma D_3b878 : decode_any W_3b878 = Some (Auipc 10 62, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3b87c : bv 32 := 0x38050913.
Lemma F_3b87c : fetch_word Ubsan.M.loaded_segments (0x3efd4 : word) = Some W_3b87c.
Proof. vm_refl. Qed.
Lemma D_3b87c : decode_any W_3b87c = Some (OpImm ALU_ADD 18 10 896, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3b880 : bv 32 := 0x00993423.
Lemma F_3b880 : fetch_word Ubsan.M.loaded_segments (0x3efd8 : word) = Some W_3b880.
Proof. vm_refl. Qed.
Lemma D_3b880 : decode_any W_3b880 = Some (Store SZ8 18 9 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3b884 : bv 32 := 0x0004b583.
Lemma F_3b884 : fetch_word Ubsan.M.loaded_segments (0x3efdc : word) = Some W_3b884.
Proof. vm_refl. Qed.
Lemma D_3b884 : decode_any W_3b884 = Some (Load SZ8 true 11 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3b888 : bv 32 := 0x04058c63.
Lemma F_3b888 : fetch_word Ubsan.M.loaded_segments (0x3efe0 : word) = Some W_3b888.
Proof. vm_refl. Qed.
Lemma D_3b888 : decode_any W_3b888 = Some (Branch BC_EQ 11 0 88, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3b88c : bv 32 := 0x01048493.
Lemma F_3b88c : fetch_word Ubsan.M.loaded_segments (0x3efe4 : word) = Some W_3b88c.
Proof. vm_refl. Qed.
Lemma D_3b88c : decode_any W_3b88c = Some (OpImm ALU_ADD 9 9 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3b890 : bv 32 := 0x02500513.
Lemma F_3b890 : fetch_word Ubsan.M.loaded_segments (0x3efe8 : word) = Some W_3b890.
Proof. vm_refl. Qed.
Lemma D_3b890 : decode_any W_3b890 = Some (OpImm ALU_ADD 10 0 37, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3b894 : bv 32 := 0x03010613.
Lemma F_3b894 : fetch_word Ubsan.M.loaded_segments (0x3efec : word) = Some W_3b894.
Proof. vm_refl. Qed.
Lemma D_3b894 : decode_any W_3b894 = Some (OpImm ALU_ADD 12 2 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3b898 : bv 32 := 0x0100006f.
Lemma F_3b898 : fetch_word Ubsan.M.loaded_segments (0x3eff0 : word) = Some W_3b898.
Proof. vm_refl. Qed.
Lemma D_3b898 : decode_any W_3b898 = Some (Jal 0 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3b89c : bv 32 := 0x0004b583.
Lemma F_3b89c : fetch_word Ubsan.M.loaded_segments (0x3eff4 : word) = Some W_3b89c.
Proof. vm_refl. Qed.
Lemma D_3b89c : decode_any W_3b89c = Some (Load SZ8 true 11 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3b8a0 : bv 32 := 0x01048493.
Lemma F_3b8a0 : fetch_word Ubsan.M.loaded_segments (0x3eff8 : word) = Some W_3b8a0.
Proof. vm_refl. Qed.
Lemma D_3b8a0 : decode_any W_3b8a0 = Some (OpImm ALU_ADD 9 9 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3b8a4 : bv 32 := 0x00058e63.
Lemma F_3b8a4 : fetch_word Ubsan.M.loaded_segments (0x3effc : word) = Some W_3b8a4.
Proof. vm_refl. Qed.
Lemma D_3b8a4 : decode_any W_3b8a4 = Some (Branch BC_EQ 11 0 28, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3b8a8 : bv 32 := 0xfeb56ae3.
Lemma F_3b8a8 : fetch_word Ubsan.M.loaded_segments (0x3f000 : word) = Some W_3b8a8.
Proof. vm_refl. Qed.
Lemma D_3b8a8 : decode_any W_3b8a8 = Some (Branch BC_LTU 10 11 8180, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3b8ac : bv 32 := 0xff84b683.
Lemma F_3b8ac : fetch_word Ubsan.M.loaded_segments (0x3f004 : word) = Some W_3b8ac.
Proof. vm_refl. Qed.
Lemma D_3b8ac : decode_any W_3b8ac = Some (Load SZ8 true 13 9 4088, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3b8b0 : bv 32 := 0x00359593.
Lemma F_3b8b0 : fetch_word Ubsan.M.loaded_segments (0x3f008 : word) = Some W_3b8b0.
Proof. vm_refl. Qed.
Lemma D_3b8b0 : decode_any W_3b8b0 = Some (ShiftImm ALU_SLL 11 11 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3b8b4 : bv 32 := 0x00b605b3.
Lemma F_3b8b4 : fetch_word Ubsan.M.loaded_segments (0x3f00c : word) = Some W_3b8b4.
Proof. vm_refl. Qed.
Lemma D_3b8b4 : decode_any W_3b8b4 = Some (Op ALU_ADD 11 12 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3b8b8 : bv 32 := 0x00d5b023.
Lemma F_3b8b8 : fetch_word Ubsan.M.loaded_segments (0x3f010 : word) = Some W_3b8b8.
Proof. vm_refl. Qed.
Lemma D_3b8b8 : decode_any W_3b8b8 = Some (Store SZ8 11 13 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3b8bc : bv 32 := 0xfe1ff06f.
Lemma F_3b8bc : fetch_word Ubsan.M.loaded_segments (0x3f014 : word) = Some W_3b8bc.
Proof. vm_refl. Qed.
Lemma D_3b8bc : decode_any W_3b8bc = Some (Jal 0 2097120, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3b8c0 : bv 32 := 0x0b013583.
Lemma F_3b8c0 : fetch_word Ubsan.M.loaded_segments (0x3f018 : word) = Some W_3b8c0.
Proof. vm_refl. Qed.
Lemma D_3b8c0 : decode_any W_3b8c0 = Some (Load SZ8 true 11 2 176, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3b8c4 : bv 32 := 0x13013503.
Lemma F_3b8c4 : fetch_word Ubsan.M.loaded_segments (0x3f01c : word) = Some W_3b8c4.
Proof. vm_refl. Qed.
Lemma D_3b8c4 : decode_any W_3b8c4 = Some (Load SZ8 true 10 2 304, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3b8c8 : bv 32 := 0x0003e617.
Lemma F_3b8c8 : fetch_word Ubsan.M.loaded_segments (0x3f020 : word) = Some W_3b8c8.
Proof. vm_refl. Qed.
Lemma D_3b8c8 : decode_any W_3b8c8 = Some (Auipc 12 62, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3b8cc : bv 32 := 0x38b63c23.
Lemma F_3b8cc : fetch_word Ubsan.M.loaded_segments (0x3f024 : word) = Some W_3b8cc.
Proof. vm_refl. Qed.
Lemma D_3b8cc : decode_any W_3b8cc = Some (Store SZ8 12 11 920, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3b8d0 : bv 32 := 0x00050c63.
Lemma F_3b8d0 : fetch_word Ubsan.M.loaded_segments (0x3f028 : word) = Some W_3b8d0.
Proof. vm_refl. Qed.
Lemma D_3b8d0 : decode_any W_3b8d0 = Some (Branch BC_EQ 10 0 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3b8e8 : bv 32 := 0x06013503.
Lemma F_3b8e8 : fetch_word Ubsan.M.loaded_segments (0x3f040 : word) = Some W_3b8e8.
Proof. vm_refl. Qed.
Lemma D_3b8e8 : decode_any W_3b8e8 = Some (Load SZ8 true 10 2 96, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3b8ec : bv 32 := 0x02a93823.
Lemma F_3b8ec : fetch_word Ubsan.M.loaded_segments (0x3f044 : word) = Some W_3b8ec.
Proof. vm_refl. Qed.
Lemma D_3b8ec : decode_any W_3b8ec = Some (Store SZ8 18 10 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3b8f0 : bv 32 := 0x00041463.
Lemma F_3b8f0 : fetch_word Ubsan.M.loaded_segments (0x3f048 : word) = Some W_3b8f0.
Proof. vm_refl. Qed.
Lemma D_3b8f0 : decode_any W_3b8f0 = Some (Branch BC_NE 8 0 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3b8f8 : bv 32 := 0x00041663.
Lemma F_3b8f8 : fetch_word Ubsan.M.loaded_segments (0x3f050 : word) = Some W_3b8f8.
Proof. vm_refl. Qed.
Lemma D_3b8f8 : decode_any W_3b8f8 = Some (Branch BC_NE 8 0 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3b904 : bv 32 := 0x0000d517.
Lemma F_3b904 : fetch_word Ubsan.M.loaded_segments (0x3f05c : word) = Some W_3b904.
Proof. vm_refl. Qed.
Lemma D_3b904 : decode_any W_3b904 = Some (Auipc 10 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3b908 : bv 32 := 0xc5c53583.
Lemma F_3b908 : fetch_word Ubsan.M.loaded_segments (0x3f060 : word) = Some W_3b908.
Proof. vm_refl. Qed.
Lemma D_3b908 : decode_any W_3b908 = Some (Load SZ8 true 11 10 3164, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3b90c : bv 32 := 0x0000d517.
Lemma F_3b90c : fetch_word Ubsan.M.loaded_segments (0x3f064 : word) = Some W_3b90c.
Proof. vm_refl. Qed.
Lemma D_3b90c : decode_any W_3b90c = Some (Auipc 10 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3b910 : bv 32 := 0xc5c53503.
Lemma F_3b910 : fetch_word Ubsan.M.loaded_segments (0x3f068 : word) = Some W_3b910.
Proof. vm_refl. Qed.
Lemma D_3b910 : decode_any W_3b910 = Some (Load SZ8 true 10 10 3164, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3b914 : bv 32 := 0x0085b023.
Lemma F_3b914 : fetch_word Ubsan.M.loaded_segments (0x3f06c : word) = Some W_3b914.
Proof. vm_refl. Qed.
Lemma D_3b914 : decode_any W_3b914 = Some (Store SZ8 11 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3b918 : bv 32 := 0x00140593.
Lemma F_3b918 : fetch_word Ubsan.M.loaded_segments (0x3f070 : word) = Some W_3b918.
Proof. vm_refl. Qed.
Lemma D_3b918 : decode_any W_3b918 = Some (OpImm ALU_ADD 11 8 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3b91c : bv 32 := 0x00853023.
Lemma F_3b91c : fetch_word Ubsan.M.loaded_segments (0x3f074 : word) = Some W_3b91c.
Proof. vm_refl. Qed.
Lemma D_3b91c : decode_any W_3b91c = Some (Store SZ8 10 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3b920 : bv 32 := 0x02f00613.
Lemma F_3b920 : fetch_word Ubsan.M.loaded_segments (0x3f078 : word) = Some W_3b920.
Proof. vm_refl. Qed.
Lemma D_3b920 : decode_any W_3b920 = Some (OpImm ALU_ADD 12 0 47, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3b924 : bv 32 := 0x00c0006f.
Lemma F_3b924 : fetch_word Ubsan.M.loaded_segments (0x3f07c : word) = Some W_3b924.
Proof. vm_refl. Qed.
Lemma D_3b924 : decode_any W_3b924 = Some (Jal 0 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3b928 : bv 32 := 0x00b53023.
Lemma F_3b928 : fetch_word Ubsan.M.loaded_segments (0x3f080 : word) = Some W_3b928.
Proof. vm_refl. Qed.
Lemma D_3b928 : decode_any W_3b928 = Some (Store SZ8 10 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3b92c : bv 32 := 0x00158593.
Lemma F_3b92c : fetch_word Ubsan.M.loaded_segments (0x3f084 : word) = Some W_3b92c.
Proof. vm_refl. Qed.
Lemma D_3b92c : decode_any W_3b92c = Some (OpImm ALU_ADD 11 11 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3b930 : bv 32 := 0xfff5c683.
Lemma F_3b930 : fetch_word Ubsan.M.loaded_segments (0x3f088 : word) = Some W_3b930.
Proof. vm_refl. Qed.
Lemma D_3b930 : decode_any W_3b930 = Some (Load SZ1 false 13 11 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3b934 : bv 32 := 0xfec68ae3.
Lemma F_3b934 : fetch_word Ubsan.M.loaded_segments (0x3f08c : word) = Some W_3b934.
Proof. vm_refl. Qed.
Lemma D_3b934 : decode_any W_3b934 = Some (Branch BC_EQ 13 12 8180, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3b938 : bv 32 := 0xfe069ae3.
Lemma F_3b938 : fetch_word Ubsan.M.loaded_segments (0x3f090 : word) = Some W_3b938.
Proof. vm_refl. Qed.
Lemma D_3b938 : decode_any W_3b938 = Some (Branch BC_NE 13 0 8180, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3b93c : bv 32 := 0x03010513.
Lemma F_3b93c : fetch_word Ubsan.M.loaded_segments (0x3f094 : word) = Some W_3b93c.
Proof. vm_refl. Qed.
Lemma D_3b93c : decode_any W_3b93c = Some (OpImm ALU_ADD 10 2 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3b940 : bv 32 := 0x214000ef.
Lemma F_3b940 : fetch_word Ubsan.M.loaded_segments (0x3f098 : word) = Some W_3b940.
Proof. vm_refl. Qed.
Lemma D_3b940 : decode_any W_3b940 = Some (Jal 1 532, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3b944 : bv 32 := 0x0f813503.
Lemma F_3b944 : fetch_word Ubsan.M.loaded_segments (0x3f09c : word) = Some W_3b944.
Proof. vm_refl. Qed.
Lemma D_3b944 : decode_any W_3b944 = Some (Load SZ8 true 10 2 248, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3b948 : bv 32 := 0x021000ef.
Lemma F_3b948 : fetch_word Ubsan.M.loaded_segments (0x3f0a0 : word) = Some W_3b948.
Proof. vm_refl. Qed.
Lemma D_3b948 : decode_any W_3b948 = Some (Jal 1 2080, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3b94c : bv 32 := 0x08813503.
Lemma F_3b94c : fetch_word Ubsan.M.loaded_segments (0x3f0a4 : word) = Some W_3b94c.
Proof. vm_refl. Qed.
Lemma D_3b94c : decode_any W_3b94c = Some (Load SZ8 true 10 2 136, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3b950 : bv 32 := 0x09013583.
Lemma F_3b950 : fetch_word Ubsan.M.loaded_segments (0x3f0a8 : word) = Some W_3b950.
Proof. vm_refl. Qed.
Lemma D_3b950 : decode_any W_3b950 = Some (Load SZ8 true 11 2 144, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3b954 : bv 32 := 0x00b51c63.
Lemma F_3b954 : fetch_word Ubsan.M.loaded_segments (0x3f0ac : word) = Some W_3b954.
Proof. vm_refl. Qed.
Lemma D_3b954 : decode_any W_3b954 = Some (Branch BC_NE 10 11 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3b958 : bv 32 := 0x09813503.
Lemma F_3b958 : fetch_word Ubsan.M.loaded_segments (0x3f0b0 : word) = Some W_3b958.
Proof. vm_refl. Qed.
Lemma D_3b958 : decode_any W_3b958 = Some (Load SZ8 true 10 2 152, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3b95c : bv 32 := 0x0a013583.
Lemma F_3b95c : fetch_word Ubsan.M.loaded_segments (0x3f0b4 : word) = Some W_3b95c.
Proof. vm_refl. Qed.
Lemma D_3b95c : decode_any W_3b95c = Some (Load SZ8 true 11 2 160, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3b960 : bv 32 := 0x00b51663.
Lemma F_3b960 : fetch_word Ubsan.M.loaded_segments (0x3f0b8 : word) = Some W_3b960.
Proof. vm_refl. Qed.
Lemma D_3b960 : decode_any W_3b960 = Some (Branch BC_NE 10 11 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3b964 : bv 32 := 0x0e813503.
Lemma F_3b964 : fetch_word Ubsan.M.loaded_segments (0x3f0bc : word) = Some W_3b964.
Proof. vm_refl. Qed.
Lemma D_3b964 : decode_any W_3b964 = Some (Load SZ8 true 10 2 232, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3b968 : bv 32 := 0x0e050063.
Lemma F_3b968 : fetch_word Ubsan.M.loaded_segments (0x3f0c0 : word) = Some W_3b968.
Proof. vm_refl. Qed.
Lemma D_3b968 : decode_any W_3b968 = Some (Branch BC_EQ 10 0 224, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3ba48 : bv 32 := 0x17813083.
Lemma F_3ba48 : fetch_word Ubsan.M.loaded_segments (0x3f1a0 : word) = Some W_3ba48.
Proof. vm_refl. Qed.
Lemma D_3ba48 : decode_any W_3ba48 = Some (Load SZ8 true 1 2 376, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3ba4c : bv 32 := 0x17013403.
Lemma F_3ba4c : fetch_word Ubsan.M.loaded_segments (0x3f1a4 : word) = Some W_3ba4c.
Proof. vm_refl. Qed.
Lemma D_3ba4c : decode_any W_3ba4c = Some (Load SZ8 true 8 2 368, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3ba50 : bv 32 := 0x16813483.
Lemma F_3ba50 : fetch_word Ubsan.M.loaded_segments (0x3f1a8 : word) = Some W_3ba50.
Proof. vm_refl. Qed.
Lemma D_3ba50 : decode_any W_3ba50 = Some (Load SZ8 true 9 2 360, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3ba54 : bv 32 := 0x16013903.
Lemma F_3ba54 : fetch_word Ubsan.M.loaded_segments (0x3f1ac : word) = Some W_3ba54.
Proof. vm_refl. Qed.
Lemma D_3ba54 : decode_any W_3ba54 = Some (Load SZ8 true 18 2 352, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3ba58 : bv 32 := 0x18010113.
Lemma F_3ba58 : fetch_word Ubsan.M.loaded_segments (0x3f1b0 : word) = Some W_3ba58.
Proof. vm_refl. Qed.
Lemma D_3ba58 : decode_any W_3ba58 = Some (OpImm ALU_ADD 2 2 384, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3ba5c : bv 32 := 0x00008067.
Lemma F_3ba5c : fetch_word Ubsan.M.loaded_segments (0x3f1b4 : word) = Some W_3ba5c.
Proof. vm_refl. Qed.
Lemma D_3ba5c : decode_any W_3ba5c = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3ba60 : bv 32 := 0xfe010113.
Lemma F_3ba60 : fetch_word Ubsan.M.loaded_segments (0x3f1b8 : word) = Some W_3ba60.
Proof. vm_refl. Qed.
Lemma D_3ba60 : decode_any W_3ba60 = Some (OpImm ALU_ADD 2 2 4064, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3ba64 : bv 32 := 0x00113c23.
Lemma F_3ba64 : fetch_word Ubsan.M.loaded_segments (0x3f1bc : word) = Some W_3ba64.
Proof. vm_refl. Qed.
Lemma D_3ba64 : decode_any W_3ba64 = Some (Store SZ8 2 1 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3ba68 : bv 32 := 0x00813823.
Lemma F_3ba68 : fetch_word Ubsan.M.loaded_segments (0x3f1c0 : word) = Some W_3ba68.
Proof. vm_refl. Qed.
Lemma D_3ba68 : decode_any W_3ba68 = Some (Store SZ8 2 8 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3ba6c : bv 32 := 0x00913423.
Lemma F_3ba6c : fetch_word Ubsan.M.loaded_segments (0x3f1c4 : word) = Some W_3ba6c.
Proof. vm_refl. Qed.
Lemma D_3ba6c : decode_any W_3ba6c = Some (Store SZ8 2 9 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3ba70 : bv 32 := 0xdc1ff0ef.
Lemma F_3ba70 : fetch_word Ubsan.M.loaded_segments (0x3f1c8 : word) = Some W_3ba70.
Proof. vm_refl. Qed.
Lemma D_3ba70 : decode_any W_3ba70 = Some (Jal 1 2096576, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3ba74 : bv 32 := 0x0000d517.
Lemma F_3ba74 : fetch_word Ubsan.M.loaded_segments (0x3f1cc : word) = Some W_3ba74.
Proof. vm_refl. Qed.
Lemma D_3ba74 : decode_any W_3ba74 = Some (Auipc 10 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3ba78 : bv 32 := 0x0000d597.
Lemma F_3ba78 : fetch_word Ubsan.M.loaded_segments (0x3f1d0 : word) = Some W_3ba78.
Proof. vm_refl. Qed.
Lemma D_3ba78 : decode_any W_3ba78 = Some (Auipc 11 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3ba7c : bv 32 := 0xafc53403.
Lemma F_3ba7c : fetch_word Ubsan.M.loaded_segments (0x3f1d4 : word) = Some W_3ba7c.
Proof. vm_refl. Qed.
Lemma D_3ba7c : decode_any W_3ba7c = Some (Load SZ8 true 8 10 2812, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3ba80 : bv 32 := 0xb005b483.
Lemma F_3ba80 : fetch_word Ubsan.M.loaded_segments (0x3f1d8 : word) = Some W_3ba80.
Proof. vm_refl. Qed.
Lemma D_3ba80 : decode_any W_3ba80 = Some (Load SZ8 true 9 11 2816, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3ba84 : bv 32 := 0x0084fa63.
Lemma F_3ba84 : fetch_word Ubsan.M.loaded_segments (0x3f1dc : word) = Some W_3ba84.
Proof. vm_refl. Qed.
Lemma D_3ba84 : decode_any W_3ba84 = Some (Branch BC_GEU 9 8 20, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3ba88 : bv 32 := 0x0004b503.
Lemma F_3ba88 : fetch_word Ubsan.M.loaded_segments (0x3f1e0 : word) = Some W_3ba88.
Proof. vm_refl. Qed.
Lemma D_3ba88 : decode_any W_3ba88 = Some (Load SZ8 true 10 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3ba8c : bv 32 := 0x000500e7.
Lemma F_3ba8c : fetch_word Ubsan.M.loaded_segments (0x3f1e4 : word) = Some W_3ba8c.
Proof. vm_refl. Qed.
Lemma D_3ba8c : decode_any W_3ba8c = Some (Jalr 1 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3ba90 : bv 32 := 0x00848493.
Lemma F_3ba90 : fetch_word Ubsan.M.loaded_segments (0x3f1e8 : word) = Some W_3ba90.
Proof. vm_refl. Qed.
Lemma D_3ba90 : decode_any W_3ba90 = Some (OpImm ALU_ADD 9 9 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3ba94 : bv 32 := 0xfe84eae3.
Lemma F_3ba94 : fetch_word Ubsan.M.loaded_segments (0x3f1ec : word) = Some W_3ba94.
Proof. vm_refl. Qed.
Lemma D_3ba94 : decode_any W_3ba94 = Some (Branch BC_LTU 9 8 8180, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3ba98 : bv 32 := 0x01813083.
Lemma F_3ba98 : fetch_word Ubsan.M.loaded_segments (0x3f1f0 : word) = Some W_3ba98.
Proof. vm_refl. Qed.
Lemma D_3ba98 : decode_any W_3ba98 = Some (Load SZ8 true 1 2 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3ba9c : bv 32 := 0x01013403.
Lemma F_3ba9c : fetch_word Ubsan.M.loaded_segments (0x3f1f4 : word) = Some W_3ba9c.
Proof. vm_refl. Qed.
Lemma D_3ba9c : decode_any W_3ba9c = Some (Load SZ8 true 8 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3baa0 : bv 32 := 0x00813483.
Lemma F_3baa0 : fetch_word Ubsan.M.loaded_segments (0x3f1f8 : word) = Some W_3baa0.
Proof. vm_refl. Qed.
Lemma D_3baa0 : decode_any W_3baa0 = Some (Load SZ8 true 9 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3baa4 : bv 32 := 0x02010113.
Lemma F_3baa4 : fetch_word Ubsan.M.loaded_segments (0x3f1fc : word) = Some W_3baa4.
Proof. vm_refl. Qed.
Lemma D_3baa4 : decode_any W_3baa4 = Some (OpImm ALU_ADD 2 2 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3baa8 : bv 32 := 0x00008067.
Lemma F_3baa8 : fetch_word Ubsan.M.loaded_segments (0x3f200 : word) = Some W_3baa8.
Proof. vm_refl. Qed.
Lemma D_3baa8 : decode_any W_3baa8 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3baac : bv 32 := 0xfe010113.
Lemma F_3baac : fetch_word Ubsan.M.loaded_segments (0x3f204 : word) = Some W_3baac.
Proof. vm_refl. Qed.
Lemma D_3baac : decode_any W_3baac = Some (OpImm ALU_ADD 2 2 4064, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3bab0 : bv 32 := 0x00113c23.
Lemma F_3bab0 : fetch_word Ubsan.M.loaded_segments (0x3f208 : word) = Some W_3bab0.
Proof. vm_refl. Qed.
Lemma D_3bab0 : decode_any W_3bab0 = Some (Store SZ8 2 1 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3bab4 : bv 32 := 0x00813823.
Lemma F_3bab4 : fetch_word Ubsan.M.loaded_segments (0x3f20c : word) = Some W_3bab4.
Proof. vm_refl. Qed.
Lemma D_3bab4 : decode_any W_3bab4 = Some (Store SZ8 2 8 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3bab8 : bv 32 := 0x00913423.
Lemma F_3bab8 : fetch_word Ubsan.M.loaded_segments (0x3f210 : word) = Some W_3bab8.
Proof. vm_refl. Qed.
Lemma D_3bab8 : decode_any W_3bab8 = Some (Store SZ8 2 9 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3babc : bv 32 := 0x01213023.
Lemma F_3babc : fetch_word Ubsan.M.loaded_segments (0x3f214 : word) = Some W_3babc.
Proof. vm_refl. Qed.
Lemma D_3babc : decode_any W_3babc = Some (Store SZ8 2 18 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3bac0 : bv 32 := 0x00060413.
Lemma F_3bac0 : fetch_word Ubsan.M.loaded_segments (0x3f218 : word) = Some W_3bac0.
Proof. vm_refl. Qed.
Lemma D_3bac0 : decode_any W_3bac0 = Some (OpImm ALU_ADD 8 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3bac4 : bv 32 := 0x00058493.
Lemma F_3bac4 : fetch_word Ubsan.M.loaded_segments (0x3f21c : word) = Some W_3bac4.
Proof. vm_refl. Qed.
Lemma D_3bac4 : decode_any W_3bac4 = Some (OpImm ALU_ADD 9 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3bac8 : bv 32 := 0x00050913.
Lemma F_3bac8 : fetch_word Ubsan.M.loaded_segments (0x3f220 : word) = Some W_3bac8.
Proof. vm_refl. Qed.
Lemma D_3bac8 : decode_any W_3bac8 = Some (OpImm ALU_ADD 18 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3bacc : bv 32 := 0x00063583.
Lemma F_3bacc : fetch_word Ubsan.M.loaded_segments (0x3f224 : word) = Some W_3bacc.
Proof. vm_refl. Qed.
Lemma D_3bacc : decode_any W_3bacc = Some (Load SZ8 true 11 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3bad0 : bv 32 := 0x00349513.
Lemma F_3bad0 : fetch_word Ubsan.M.loaded_segments (0x3f228 : word) = Some W_3bad0.
Proof. vm_refl. Qed.
Lemma D_3bad0 : decode_any W_3bad0 = Some (ShiftImm ALU_SLL 10 9 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3bad4 : bv 32 := 0x00a60533.
Lemma F_3bad4 : fetch_word Ubsan.M.loaded_segments (0x3f22c : word) = Some W_3bad4.
Proof. vm_refl. Qed.
Lemma D_3bad4 : decode_any W_3bad4 = Some (Op ALU_ADD 10 12 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3bad8 : bv 32 := 0x00850513.
Lemma F_3bad8 : fetch_word Ubsan.M.loaded_segments (0x3f230 : word) = Some W_3bad8.
Proof. vm_refl. Qed.
Lemma D_3bad8 : decode_any W_3bad8 = Some (OpImm ALU_ADD 10 10 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3badc : bv 32 := 0xd59ff0ef.
Lemma F_3badc : fetch_word Ubsan.M.loaded_segments (0x3f234 : word) = Some W_3badc.
Proof. vm_refl. Qed.
Lemma D_3badc : decode_any W_3badc = Some (Jal 1 2096472, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3bae0 : bv 32 := 0x00000517.
Lemma F_3bae0 : fetch_word Ubsan.M.loaded_segments (0x3f238 : word) = Some W_3bae0.
Proof. vm_refl. Qed.
Lemma D_3bae0 : decode_any W_3bae0 = Some (Auipc 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3bae4 : bv 32 := 0x02c50313.
Lemma F_3bae4 : fetch_word Ubsan.M.loaded_segments (0x3f23c : word) = Some W_3bae4.
Proof. vm_refl. Qed.
Lemma D_3bae4 : decode_any W_3bae4 = Some (OpImm ALU_ADD 6 10 44, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3bae8 : bv 32 := 0x00090513.
Lemma F_3bae8 : fetch_word Ubsan.M.loaded_segments (0x3f240 : word) = Some W_3bae8.
Proof. vm_refl. Qed.
Lemma D_3bae8 : decode_any W_3bae8 = Some (OpImm ALU_ADD 10 18 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3baec : bv 32 := 0x00048593.
Lemma F_3baec : fetch_word Ubsan.M.loaded_segments (0x3f244 : word) = Some W_3baec.
Proof. vm_refl. Qed.
Lemma D_3baec : decode_any W_3baec = Some (OpImm ALU_ADD 11 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3baf0 : bv 32 := 0x00040613.
Lemma F_3baf0 : fetch_word Ubsan.M.loaded_segments (0x3f248 : word) = Some W_3baf0.
Proof. vm_refl. Qed.
Lemma D_3baf0 : decode_any W_3baf0 = Some (OpImm ALU_ADD 12 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3baf4 : bv 32 := 0x01813083.
Lemma F_3baf4 : fetch_word Ubsan.M.loaded_segments (0x3f24c : word) = Some W_3baf4.
Proof. vm_refl. Qed.
Lemma D_3baf4 : decode_any W_3baf4 = Some (Load SZ8 true 1 2 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3baf8 : bv 32 := 0x01013403.
Lemma F_3baf8 : fetch_word Ubsan.M.loaded_segments (0x3f250 : word) = Some W_3baf8.
Proof. vm_refl. Qed.
Lemma D_3baf8 : decode_any W_3baf8 = Some (Load SZ8 true 8 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3bafc : bv 32 := 0x00813483.
Lemma F_3bafc : fetch_word Ubsan.M.loaded_segments (0x3f254 : word) = Some W_3bafc.
Proof. vm_refl. Qed.
Lemma D_3bafc : decode_any W_3bafc = Some (Load SZ8 true 9 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3bb00 : bv 32 := 0x00013903.
Lemma F_3bb00 : fetch_word Ubsan.M.loaded_segments (0x3f258 : word) = Some W_3bb00.
Proof. vm_refl. Qed.
Lemma D_3bb00 : decode_any W_3bb00 = Some (Load SZ8 true 18 2 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3bb04 : bv 32 := 0x02010113.
Lemma F_3bb04 : fetch_word Ubsan.M.loaded_segments (0x3f25c : word) = Some W_3bb04.
Proof. vm_refl. Qed.
Lemma D_3bb04 : decode_any W_3bb04 = Some (OpImm ALU_ADD 2 2 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3bb08 : bv 32 := 0x00030067.
Lemma F_3bb08 : fetch_word Ubsan.M.loaded_segments (0x3f260 : word) = Some W_3bb08.
Proof. vm_refl. Qed.
Lemma D_3bb08 : decode_any W_3bb08 = Some (Jalr 0 6 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3bb0c : bv 32 := 0xfd010113.
Lemma F_3bb0c : fetch_word Ubsan.M.loaded_segments (0x3f264 : word) = Some W_3bb0c.
Proof. vm_refl. Qed.
Lemma D_3bb0c : decode_any W_3bb0c = Some (OpImm ALU_ADD 2 2 4048, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3bb10 : bv 32 := 0x02113423.
Lemma F_3bb10 : fetch_word Ubsan.M.loaded_segments (0x3f268 : word) = Some W_3bb10.
Proof. vm_refl. Qed.
Lemma D_3bb10 : decode_any W_3bb10 = Some (Store SZ8 2 1 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3bb14 : bv 32 := 0x02813023.
Lemma F_3bb14 : fetch_word Ubsan.M.loaded_segments (0x3f26c : word) = Some W_3bb14.
Proof. vm_refl. Qed.
Lemma D_3bb14 : decode_any W_3bb14 = Some (Store SZ8 2 8 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3bb18 : bv 32 := 0x00913c23.
Lemma F_3bb18 : fetch_word Ubsan.M.loaded_segments (0x3f270 : word) = Some W_3bb18.
Proof. vm_refl. Qed.
Lemma D_3bb18 : decode_any W_3bb18 = Some (Store SZ8 2 9 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3bb1c : bv 32 := 0x01213823.
Lemma F_3bb1c : fetch_word Ubsan.M.loaded_segments (0x3f274 : word) = Some W_3bb1c.
Proof. vm_refl. Qed.
Lemma D_3bb1c : decode_any W_3bb1c = Some (Store SZ8 2 18 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3bb20 : bv 32 := 0x01313423.
Lemma F_3bb20 : fetch_word Ubsan.M.loaded_segments (0x3f278 : word) = Some W_3bb20.
Proof. vm_refl. Qed.
Lemma D_3bb20 : decode_any W_3bb20 = Some (Store SZ8 2 19 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3bb24 : bv 32 := 0x00060413.
Lemma F_3bb24 : fetch_word Ubsan.M.loaded_segments (0x3f27c : word) = Some W_3bb24.
Proof. vm_refl. Qed.
Lemma D_3bb24 : decode_any W_3bb24 = Some (OpImm ALU_ADD 8 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3bb28 : bv 32 := 0x00058493.
Lemma F_3bb28 : fetch_word Ubsan.M.loaded_segments (0x3f280 : word) = Some W_3bb28.
Proof. vm_refl. Qed.
Lemma D_3bb28 : decode_any W_3bb28 = Some (OpImm ALU_ADD 9 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3bb2c : bv 32 := 0x00050913.
Lemma F_3bb2c : fetch_word Ubsan.M.loaded_segments (0x3f284 : word) = Some W_3bb2c.
Proof. vm_refl. Qed.
Lemma D_3bb2c : decode_any W_3bb2c = Some (OpImm ALU_ADD 18 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3bb30 : bv 32 := 0x00359513.
Lemma F_3bb30 : fetch_word Ubsan.M.loaded_segments (0x3f288 : word) = Some W_3bb30.
Proof. vm_refl. Qed.
Lemma D_3bb30 : decode_any W_3bb30 = Some (ShiftImm ALU_SLL 10 11 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3bb34 : bv 32 := 0x00a60533.
Lemma F_3bb34 : fetch_word Ubsan.M.loaded_segments (0x3f28c : word) = Some W_3bb34.
Proof. vm_refl. Qed.
Lemma D_3bb34 : decode_any W_3bb34 = Some (Op ALU_ADD 10 12 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3bb38 : bv 32 := 0x00850993.
Lemma F_3bb38 : fetch_word Ubsan.M.loaded_segments (0x3f290 : word) = Some W_3bb38.
Proof. vm_refl. Qed.
Lemma D_3bb38 : decode_any W_3bb38 = Some (OpImm ALU_ADD 19 10 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3bb3c : bv 32 := 0xf25ff0ef.
Lemma F_3bb3c : fetch_word Ubsan.M.loaded_segments (0x3f294 : word) = Some W_3bb3c.
Proof. vm_refl. Qed.
Lemma D_3bb3c : decode_any W_3bb3c = Some (Jal 1 2096932, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3bb40 : bv 32 := 0x00048513.
Lemma F_3bb40 : fetch_word Ubsan.M.loaded_segments (0x3f298 : word) = Some W_3bb40.
Proof. vm_refl. Qed.
Lemma D_3bb40 : decode_any W_3bb40 = Some (OpImm ALU_ADD 10 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3bb44 : bv 32 := 0x00040593.
Lemma F_3bb44 : fetch_word Ubsan.M.loaded_segments (0x3f29c : word) = Some W_3bb44.
Proof. vm_refl. Qed.
Lemma D_3bb44 : decode_any W_3bb44 = Some (OpImm ALU_ADD 11 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3bb48 : bv 32 := 0x00098613.
Lemma F_3bb48 : fetch_word Ubsan.M.loaded_segments (0x3f2a0 : word) = Some W_3bb48.
Proof. vm_refl. Qed.
Lemma D_3bb48 : decode_any W_3bb48 = Some (OpImm ALU_ADD 12 19 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3bb4c : bv 32 := 0x000900e7.
Lemma F_3bb4c : fetch_word Ubsan.M.loaded_segments (0x3f2a4 : word) = Some W_3bb4c.
Proof. vm_refl. Qed.
Lemma D_3bb4c : decode_any W_3bb4c = Some (Jalr 1 18 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3bb50 : bv 32 := 0x4a4000ef.
Lemma F_3bb50 : fetch_word Ubsan.M.loaded_segments (0x3f2a8 : word) = Some W_3bb50.
Proof. vm_refl. Qed.
Lemma D_3bb50 : decode_any W_3bb50 = Some (Jal 1 1188, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3bb54 : bv 32 := 0xfc010113.
Lemma F_3bb54 : fetch_word Ubsan.M.loaded_segments (0x3f2ac : word) = Some W_3bb54.
Proof. vm_refl. Qed.
Lemma D_3bb54 : decode_any W_3bb54 = Some (OpImm ALU_ADD 2 2 4032, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3bb58 : bv 32 := 0x02113c23.
Lemma F_3bb58 : fetch_word Ubsan.M.loaded_segments (0x3f2b0 : word) = Some W_3bb58.
Proof. vm_refl. Qed.
Lemma D_3bb58 : decode_any W_3bb58 = Some (Store SZ8 2 1 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3bb5c : bv 32 := 0x02813823.
Lemma F_3bb5c : fetch_word Ubsan.M.loaded_segments (0x3f2b4 : word) = Some W_3bb5c.
Proof. vm_refl. Qed.
Lemma D_3bb5c : decode_any W_3bb5c = Some (Store SZ8 2 8 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3bb60 : bv 32 := 0x02913423.
Lemma F_3bb60 : fetch_word Ubsan.M.loaded_segments (0x3f2b8 : word) = Some W_3bb60.
Proof. vm_refl. Qed.
Lemma D_3bb60 : decode_any W_3bb60 = Some (Store SZ8 2 9 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3bb64 : bv 32 := 0x03213023.
Lemma F_3bb64 : fetch_word Ubsan.M.loaded_segments (0x3f2bc : word) = Some W_3bb64.
Proof. vm_refl. Qed.
Lemma D_3bb64 : decode_any W_3bb64 = Some (Store SZ8 2 18 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3bb68 : bv 32 := 0x01313c23.
Lemma F_3bb68 : fetch_word Ubsan.M.loaded_segments (0x3f2c0 : word) = Some W_3bb68.
Proof. vm_refl. Qed.
Lemma D_3bb68 : decode_any W_3bb68 = Some (Store SZ8 2 19 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3bb6c : bv 32 := 0x01413823.
Lemma F_3bb6c : fetch_word Ubsan.M.loaded_segments (0x3f2c4 : word) = Some W_3bb6c.
Proof. vm_refl. Qed.
Lemma D_3bb6c : decode_any W_3bb6c = Some (Store SZ8 2 20 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3bb70 : bv 32 := 0x01513423.
Lemma F_3bb70 : fetch_word Ubsan.M.loaded_segments (0x3f2c8 : word) = Some W_3bb70.
Proof. vm_refl. Qed.
Lemma D_3bb70 : decode_any W_3bb70 = Some (Store SZ8 2 21 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3bb74 : bv 32 := 0x02853683.
Lemma F_3bb74 : fetch_word Ubsan.M.loaded_segments (0x3f2cc : word) = Some W_3bb74.
Proof. vm_refl. Qed.
Lemma D_3bb74 : decode_any W_3bb74 = Some (Load SZ8 true 13 10 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3bb78 : bv 32 := 0x0003e597.
Lemma F_3bb78 : fetch_word Ubsan.M.loaded_segments (0x3f2d0 : word) = Some W_3bb78.
Proof. vm_refl. Qed.
Lemma D_3bb78 : decode_any W_3bb78 = Some (Auipc 11 62, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)
Definition W_3bb88 : bv 32 := 0x0c068e63.
Lemma F_3bb88 : fetch_word Ubsan.M.loaded_segments (0x3f2e0 : word) = Some W_3bb88.
Proof. vm_refl. Qed.
Lemma D_3bb88 : decode_any W_3bb88 = Some (Branch BC_EQ 13 0 220, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)
Definition W_3bb90 : bv 32 := 0x00000893.
Lemma F_3bb90 : fetch_word Ubsan.M.loaded_segments (0x3f2e8 : word) = Some W_3bb90.
Proof. vm_refl. Qed.
Lemma D_3bb90 : decode_any W_3bb90 = Some (OpImm ALU_ADD 17 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3bb94 : bv 32 := 0x0000e717.
Lemma F_3bb94 : fetch_word Ubsan.M.loaded_segments (0x3f2ec : word) = Some W_3bb94.
Proof. vm_refl. Qed.
Lemma D_3bb94 : decode_any W_3bb94 = Some (Auipc 14 14, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3bb98 : bv 32 := 0x01853783.
Lemma F_3bb98 : fetch_word Ubsan.M.loaded_segments (0x3f2f0 : word) = Some W_3bb98.
Proof. vm_refl. Qed.
Lemma D_3bb98 : decode_any W_3bb98 = Some (Load SZ8 true 15 10 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3bb9c : bv 32 := 0x02053503.
Lemma F_3bb9c : fetch_word Ubsan.M.loaded_segments (0x3f2f4 : word) = Some W_3bb9c.
Proof. vm_refl. Qed.
Lemma D_3bb9c : decode_any W_3bb9c = Some (Load SZ8 true 10 10 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3bba0 : bv 32 := 0x00600813.
Lemma F_3bba0 : fetch_word Ubsan.M.loaded_segments (0x3f2f8 : word) = Some W_3bba0.
Proof. vm_refl. Qed.
Lemma D_3bba0 : decode_any W_3bba0 = Some (OpImm ALU_ADD 16 0 6, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3bba4 : bv 32 := 0x0000d297.
Lemma F_3bba4 : fetch_word Ubsan.M.loaded_segments (0x3f2fc : word) = Some W_3bba4.
Proof. vm_refl. Qed.
Lemma D_3bba4 : decode_any W_3bba4 = Some (Auipc 5 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3bba8 : bv 32 := 0xc2476f03.
Lemma F_3bba8 : fetch_word Ubsan.M.loaded_segments (0x3f300 : word) = Some W_3bba8.
Proof. vm_refl. Qed.
Lemma D_3bba8 : decode_any W_3bba8 = Some (Load SZ4 false 30 14 3108, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3bbac : bv 32 := 0x95c2b283.
Lemma F_3bbac : fetch_word Ubsan.M.loaded_segments (0x3f304 : word) = Some W_3bbac.
Proof. vm_refl. Qed.
Lemma D_3bbac : decode_any W_3bbac = Some (Load SZ8 true 5 5 2396, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3bbb0 : bv 32 := 0x00200313.
Lemma F_3bbb0 : fetch_word Ubsan.M.loaded_segments (0x3f308 : word) = Some W_3bbb0.
Proof. vm_refl. Qed.
Lemma D_3bbb0 : decode_any W_3bbb0 = Some (OpImm ALU_ADD 6 0 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3bbb4 : bv 32 := 0x00700393.
Lemma F_3bbb4 : fetch_word Ubsan.M.loaded_segments (0x3f30c : word) = Some W_3bbb4.
Proof. vm_refl. Qed.
Lemma D_3bbb4 : decode_any W_3bbb4 = Some (OpImm ALU_ADD 7 0 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3bbb8 : bv 32 := 0x6474ee37.
Lemma F_3bbb8 : fetch_word Ubsan.M.loaded_segments (0x3f310 : word) = Some W_3bbb8.
Proof. vm_refl. Qed.
Lemma D_3bbb8 : decode_any W_3bbb8 = Some (Lui 28 411470, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3bbbc : bv 32 := 0x551e0e1b.
Lemma F_3bbbc : fetch_word Ubsan.M.loaded_segments (0x3f314 : word) = Some W_3bbbc.
Proof. vm_refl. Qed.
Lemma D_3bbbc : decode_any W_3bbbc = Some (OpImm32 28 28 1361, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3bbc0 : bv 32 := 0x00078e93.
Lemma F_3bbc0 : fetch_word Ubsan.M.loaded_segments (0x3f318 : word) = Some W_3bbc0.
Proof. vm_refl. Qed.
Lemma D_3bbc0 : decode_any W_3bbc0 = Some (OpImm ALU_ADD 29 15 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3bbc4 : bv 32 := 0x0180006f.
Lemma F_3bbc4 : fetch_word Ubsan.M.loaded_segments (0x3f31c : word) = Some W_3bbc4.
Proof. vm_refl. Qed.
Lemma D_3bbc4 : decode_any W_3bbc4 = Some (Jal 0 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)
Definition W_3bbd0 : bv 32 := 0xfff68693.
Lemma F_3bbd0 : fetch_word Ubsan.M.loaded_segments (0x3f328 : word) = Some W_3bbd0.
Proof. vm_refl. Qed.
Lemma D_3bbd0 : decode_any W_3bbd0 = Some (OpImm ALU_ADD 13 13 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3bbd4 : bv 32 := 0x00ae8eb3.
Lemma F_3bbd4 : fetch_word Ubsan.M.loaded_segments (0x3f32c : word) = Some W_3bbd4.
Proof. vm_refl. Qed.
Lemma D_3bbd4 : decode_any W_3bbd4 = Some (Op ALU_ADD 29 29 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3bbd8 : bv 32 := 0x04068a63.
Lemma F_3bbd8 : fetch_word Ubsan.M.loaded_segments (0x3f330 : word) = Some W_3bbd8.
Proof. vm_refl. Qed.
Lemma D_3bbd8 : decode_any W_3bbd8 = Some (Branch BC_EQ 13 0 84, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3bbdc : bv 32 := 0x000ea403.
Lemma F_3bbdc : fetch_word Ubsan.M.loaded_segments (0x3f334 : word) = Some W_3bbdc.
Proof. vm_refl. Qed.
Lemma D_3bbdc : decode_any W_3bbdc = Some (Load SZ4 true 8 29 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3bbe0 : bv 32 := 0xff0404e3.
Lemma F_3bbe0 : fetch_word Ubsan.M.loaded_segments (0x3f338 : word) = Some W_3bbe0.
Proof. vm_refl. Qed.
Lemma D_3bbe0 : decode_any W_3bbe0 = Some (Branch BC_EQ 8 16 8168, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3bbe4 : bv 32 := 0x00028a63.
Lemma F_3bbe4 : fetch_word Ubsan.M.loaded_segments (0x3f33c : word) = Some W_3bbe4.
Proof. vm_refl. Qed.
Lemma D_3bbe4 : decode_any W_3bbe4 = Some (Branch BC_EQ 5 0 20, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3bbf8 : bv 32 := 0x000e8f93.
Lemma F_3bbf8 : fetch_word Ubsan.M.loaded_segments (0x3f350 : word) = Some W_3bbf8.
Proof. vm_refl. Qed.
Lemma D_3bbf8 : decode_any W_3bbf8 = Some (OpImm ALU_ADD 31 29 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3bbfc : bv 32 := 0x00740463.
Lemma F_3bbfc : fetch_word Ubsan.M.loaded_segments (0x3f354 : word) = Some W_3bbfc.
Proof. vm_refl. Qed.
Lemma D_3bbfc : decode_any W_3bbfc = Some (Branch BC_EQ 8 7 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3bc00 : bv 32 := 0x00088f93.
Lemma F_3bc00 : fetch_word Ubsan.M.loaded_segments (0x3f358 : word) = Some W_3bc00.
Proof. vm_refl. Qed.
Lemma D_3bc00 : decode_any W_3bc00 = Some (OpImm ALU_ADD 31 17 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3bc04 : bv 32 := 0x03c41063.
Lemma F_3bc04 : fetch_word Ubsan.M.loaded_segments (0x3f35c : word) = Some W_3bc04.
Proof. vm_refl. Qed.
Lemma D_3bc04 : decode_any W_3bc04 = Some (Branch BC_NE 8 28 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3bc08 : bv 32 := 0x028eb883.
Lemma F_3bc08 : fetch_word Ubsan.M.loaded_segments (0x3f360 : word) = Some W_3bc08.
Proof. vm_refl. Qed.
Lemma D_3bc08 : decode_any W_3bc08 = Some (Load SZ8 true 17 29 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3bc0c : bv 32 := 0x011f7c63.
Lemma F_3bc0c : fetch_word Ubsan.M.loaded_segments (0x3f364 : word) = Some W_3bc0c.
Proof. vm_refl. Qed.
Lemma D_3bc0c : decode_any W_3bc0c = Some (Branch BC_GEU 30 17 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3bc24 : bv 32 := 0x000f8893.
Lemma F_3bc24 : fetch_word Ubsan.M.loaded_segments (0x3f37c : word) = Some W_3bc24.
Proof. vm_refl. Qed.
Lemma D_3bc24 : decode_any W_3bc24 = Some (OpImm ALU_ADD 17 31 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3bc28 : bv 32 := 0xfa9ff06f.
Lemma F_3bc28 : fetch_word Ubsan.M.loaded_segments (0x3f380 : word) = Some W_3bc28.
Proof. vm_refl. Qed.
Lemma D_3bc28 : decode_any W_3bc28 = Some (Jal 0 2097064, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3bc2c : bv 32 := 0x02088c63.
Lemma F_3bc2c : fetch_word Ubsan.M.loaded_segments (0x3f384 : word) = Some W_3bc2c.
Proof. vm_refl. Qed.
Lemma D_3bc2c : decode_any W_3bc2c = Some (Branch BC_EQ 17 0 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)
Definition W_3bc74 : bv 32 := 0xfff50793.
Lemma F_3bc74 : fetch_word Ubsan.M.loaded_segments (0x3f3cc : word) = Some W_3bc74.
Proof. vm_refl. Qed.
Lemma D_3bc74 : decode_any W_3bc74 = Some (OpImm ALU_ADD 15 10 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3bc78 : bv 32 := 0x40e00733.
Lemma F_3bc78 : fetch_word Ubsan.M.loaded_segments (0x3f3d0 : word) = Some W_3bc78.
Proof. vm_refl. Qed.
Lemma D_3bc78 : decode_any W_3bc78 = Some (Op ALU_SUB 14 0 14, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)
Definition W_3bc80 : bv 32 := 0x00e7f733.
Lemma F_3bc80 : fetch_word Ubsan.M.loaded_segments (0x3f3d8 : word) = Some W_3bc80.
Proof. vm_refl. Qed.
Lemma D_3bc80 : decode_any W_3bc80 = Some (Op ALU_AND 14 15 14, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3bc84 : bv 32 := 0x00700793.
Lemma F_3bc84 : fetch_word Ubsan.M.loaded_segments (0x3f3dc : word) = Some W_3bc84.
Proof. vm_refl. Qed.
Lemma D_3bc84 : decode_any W_3bc84 = Some (OpImm ALU_ADD 15 0 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3bc88 : bv 32 := 0x00d706b3.
Lemma F_3bc88 : fetch_word Ubsan.M.loaded_segments (0x3f3e0 : word) = Some W_3bc88.
Proof. vm_refl. Qed.
Lemma D_3bc88 : decode_any W_3bc88 = Some (Op ALU_ADD 13 14 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)
Definition W_3bc94 : bv 32 := 0x00a7e663.
Lemma F_3bc94 : fetch_word Ubsan.M.loaded_segments (0x3f3ec : word) = Some W_3bc94.
Proof. vm_refl. Qed.
Lemma D_3bc94 : decode_any W_3bc94 = Some (Branch BC_LTU 15 10 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3bc98 : bv 32 := 0x00800513.
Lemma F_3bc98 : fetch_word Ubsan.M.loaded_segments (0x3f3f0 : word) = Some W_3bc98.
Proof. vm_refl. Qed.
Lemma D_3bc98 : decode_any W_3bc98 = Some (OpImm ALU_ADD 10 0 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)
Definition W_3bcb0 : bv 32 := 0xff85f593.
Lemma F_3bcb0 : fetch_word Ubsan.M.loaded_segments (0x3f40c : word) = Some W_3bcb0.
Proof. vm_refl. Qed.
Lemma D_3bcb0 : decode_any W_3bcb0 = Some (OpImm ALU_AND 11 11 4088, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3bcb4 : bv 32 := 0x00b4bc23.
Lemma F_3bcb4 : fetch_word Ubsan.M.loaded_segments (0x3f410 : word) = Some W_3bcb4.
Proof. vm_refl. Qed.
Lemma D_3bcb4 : decode_any W_3bcb4 = Some (Store SZ8 9 11 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3bcb8 : bv 32 := 0x02a4b023.
Lemma F_3bcb8 : fetch_word Ubsan.M.loaded_segments (0x3f414 : word) = Some W_3bcb8.
Proof. vm_refl. Qed.
Lemma D_3bcb8 : decode_any W_3bcb8 = Some (Store SZ8 9 10 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3bcbc : bv 32 := 0x02d5ea63.
Lemma F_3bcbc : fetch_word Ubsan.M.loaded_segments (0x3f418 : word) = Some W_3bcbc.
Proof. vm_refl. Qed.
Lemma D_3bcbc : decode_any W_3bcbc = Some (Branch BC_LTU 11 13 52, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)
Definition W_3bd08 : bv 32 := 0x0284b603.
Lemma F_3bd08 : fetch_word Ubsan.M.loaded_segments (0x3f454 : word) = Some W_3bd08.
Proof. vm_refl. Qed.
Lemma D_3bd08 : decode_any W_3bd08 = Some (Load SZ8 true 12 9 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)
Definition W_3bd34 : bv 32 := 0x0c890413.
Lemma F_3bd34 : fetch_word Ubsan.M.loaded_segments (0x3f480 : word) = Some W_3bd34.
Proof. vm_refl. Qed.
Lemma D_3bd34 : decode_any W_3bd34 = Some (OpImm ALU_ADD 8 18 200, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)
Definition W_3bd88 : bv 32 := 0x01293023.
Lemma F_3bd88 : fetch_word Ubsan.M.loaded_segments (0x3f4d4 : word) = Some W_3bd88.
Proof. vm_refl. Qed.
Lemma D_3bd88 : decode_any W_3bd88 = Some (Store SZ8 18 18 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3bd8c : bv 32 := 0x00040513.
Lemma F_3bd8c : fetch_word Ubsan.M.loaded_segments (0x3f4d8 : word) = Some W_3bd8c.
Proof. vm_refl. Qed.
Lemma D_3bd8c : decode_any W_3bd8c = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3bd90 : bv 32 := 0x5c9070ef.
Lemma F_3bd90 : fetch_word Ubsan.M.loaded_segments (0x3f4dc : word) = Some W_3bd90.
Proof. vm_refl. Qed.
Lemma D_3bd90 : decode_any W_3bd90 = Some (Jal 1 32200, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3bd94 : bv 32 := 0x04054a63.
Lemma F_3bd94 : fetch_word Ubsan.M.loaded_segments (0x3f4e0 : word) = Some W_3bd94.
Proof. vm_refl. Qed.
Lemma D_3bd94 : decode_any W_3bd94 = Some (Branch BC_LT 10 0 84, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3bd98 : bv 32 := 0x00051663.
Lemma F_3bd98 : fetch_word Ubsan.M.loaded_segments (0x3f4e4 : word) = Some W_3bd98.
Proof. vm_refl. Qed.
Lemma D_3bd98 : decode_any W_3bd98 = Some (Branch BC_NE 10 0 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3bd9c : bv 32 := 0x00100513.
Lemma F_3bd9c : fetch_word Ubsan.M.loaded_segments (0x3f4e8 : word) = Some W_3bd9c.
Proof. vm_refl. Qed.
Lemma D_3bd9c : decode_any W_3bd9c = Some (OpImm ALU_ADD 10 0 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3bda0 : bv 32 := 0x00a48023.
Lemma F_3bda0 : fetch_word Ubsan.M.loaded_segments (0x3f4ec : word) = Some W_3bda0.
Proof. vm_refl. Qed.
Lemma D_3bda0 : decode_any W_3bda0 = Some (Store SZ1 9 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3bda4 : bv 32 := 0x00200513.
Lemma F_3bda4 : fetch_word Ubsan.M.loaded_segments (0x3f4f0 : word) = Some W_3bda4.
Proof. vm_refl. Qed.
Lemma D_3bda4 : decode_any W_3bda4 = Some (OpImm ALU_ADD 10 0 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3bda8 : bv 32 := 0x0003e597.
Lemma F_3bda8 : fetch_word Ubsan.M.loaded_segments (0x3f4f4 : word) = Some W_3bda8.
Proof. vm_refl. Qed.
Lemma D_3bda8 : decode_any W_3bda8 = Some (Auipc 11 62, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3bdac : bv 32 := 0x02a92423.
Lemma F_3bdac : fetch_word Ubsan.M.loaded_segments (0x3f4f8 : word) = Some W_3bdac.
Proof. vm_refl. Qed.
Lemma D_3bdac : decode_any W_3bdac = Some (Store SZ4 18 10 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3bdb0 : bv 32 := 0x06000893.
Lemma F_3bdb0 : fetch_word Ubsan.M.loaded_segments (0x3f4fc : word) = Some W_3bdb0.
Proof. vm_refl. Qed.
Lemma D_3bdb0 : decode_any W_3bdb0 = Some (OpImm ALU_ADD 17 0 96, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3bdb4 : bv 32 := 0xbdc58513.
Lemma F_3bdb4 : fetch_word Ubsan.M.loaded_segments (0x3f500 : word) = Some W_3bdb4.
Proof. vm_refl. Qed.
Lemma D_3bdb4 : decode_any W_3bdb4 = Some (OpImm ALU_ADD 10 11 3036, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3bdb8 : bv 32 := 0x03848593.
Lemma F_3bdb8 : fetch_word Ubsan.M.loaded_segments (0x3f504 : word) = Some W_3bdb8.
Proof. vm_refl. Qed.
Lemma D_3bdb8 : decode_any W_3bdb8 = Some (OpImm ALU_ADD 11 9 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3bdbc : bv 32 := 0x00000073.
Lemma F_3bdbc : fetch_word Ubsan.M.loaded_segments (0x3f508 : word) = Some W_3bdbc.
Proof. vm_refl. Qed.
Lemma E_3bdbc : is_ecall W_3bdbc = true.
Proof. reflexivity. Qed.

(* [comment removed for export] *)
Definition W_3bdc0 : bv 32 := 0x07890613.
Lemma F_3bdc0 : fetch_word Ubsan.M.loaded_segments (0x3f50c : word) = Some W_3bdc0.
Proof. vm_refl. Qed.
Lemma D_3bdc0 : decode_any W_3bdc0 = Some (OpImm ALU_ADD 12 18 120, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3bdc4 : bv 32 := 0x02a92023.
Lemma F_3bdc4 : fetch_word Ubsan.M.loaded_segments (0x3f510 : word) = Some W_3bdc4.
Proof. vm_refl. Qed.
Lemma D_3bdc4 : decode_any W_3bdc4 = Some (Store SZ4 18 10 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3bdc8 : bv 32 := 0x08b93c23.
Lemma F_3bdc8 : fetch_word Ubsan.M.loaded_segments (0x3f514 : word) = Some W_3bdc8.
Proof. vm_refl. Qed.
Lemma D_3bdc8 : decode_any W_3bdc8 = Some (Store SZ8 18 11 152, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3bdcc : bv 32 := 0x06c93c23.
Lemma F_3bdcc : fetch_word Ubsan.M.loaded_segments (0x3f518 : word) = Some W_3bdcc.
Proof. vm_refl. Qed.
Lemma D_3bdcc : decode_any W_3bdcc = Some (Store SZ8 18 12 120, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3bdd0 : bv 32 := 0x0003e517.
Lemma F_3bdd0 : fetch_word Ubsan.M.loaded_segments (0x3f51c : word) = Some W_3bdd0.
Proof. vm_refl. Qed.
Lemma D_3bdd0 : decode_any W_3bdd0 = Some (Auipc 10 62, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3bdd4 : bv 32 := 0xe1c53503.
Lemma F_3bdd4 : fetch_word Ubsan.M.loaded_segments (0x3f520 : word) = Some W_3bdd4.
Proof. vm_refl. Qed.
Lemma D_3bdd4 : decode_any W_3bdd4 = Some (Load SZ8 true 10 10 3612, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3bdd8 : bv 32 := 0x01293423.
Lemma F_3bdd8 : fetch_word Ubsan.M.loaded_segments (0x3f524 : word) = Some W_3bdd8.
Proof. vm_refl. Qed.
Lemma D_3bdd8 : decode_any W_3bdd8 = Some (Store SZ8 18 18 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3bddc : bv 32 := 0x01293823.
Lemma F_3bddc : fetch_word Ubsan.M.loaded_segments (0x3f528 : word) = Some W_3bddc.
Proof. vm_refl. Qed.
Lemma D_3bddc : decode_any W_3bddc = Some (Store SZ8 18 18 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3bde0 : bv 32 := 0x00a93c23.
Lemma F_3bde0 : fetch_word Ubsan.M.loaded_segments (0x3f52c : word) = Some W_3bde0.
Proof. vm_refl. Qed.
Lemma D_3bde0 : decode_any W_3bde0 = Some (Store SZ8 18 10 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3bde4 : bv 32 := 0x0080006f.
Lemma F_3bde4 : fetch_word Ubsan.M.loaded_segments (0x3f530 : word) = Some W_3bde4.
Proof. vm_refl. Qed.
Lemma D_3bde4 : decode_any W_3bde4 = Some (Jal 0 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3bdec : bv 32 := 0x03813083.
Lemma F_3bdec : fetch_word Ubsan.M.loaded_segments (0x3f538 : word) = Some W_3bdec.
Proof. vm_refl. Qed.
Lemma D_3bdec : decode_any W_3bdec = Some (Load SZ8 true 1 2 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3bdf0 : bv 32 := 0x03013403.
Lemma F_3bdf0 : fetch_word Ubsan.M.loaded_segments (0x3f53c : word) = Some W_3bdf0.
Proof. vm_refl. Qed.
Lemma D_3bdf0 : decode_any W_3bdf0 = Some (Load SZ8 true 8 2 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3bdf4 : bv 32 := 0x02813483.
Lemma F_3bdf4 : fetch_word Ubsan.M.loaded_segments (0x3f540 : word) = Some W_3bdf4.
Proof. vm_refl. Qed.
Lemma D_3bdf4 : decode_any W_3bdf4 = Some (Load SZ8 true 9 2 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3bdf8 : bv 32 := 0x02013903.
Lemma F_3bdf8 : fetch_word Ubsan.M.loaded_segments (0x3f544 : word) = Some W_3bdf8.
Proof. vm_refl. Qed.
Lemma D_3bdf8 : decode_any W_3bdf8 = Some (Load SZ8 true 18 2 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3bdfc : bv 32 := 0x01813983.
Lemma F_3bdfc : fetch_word Ubsan.M.loaded_segments (0x3f548 : word) = Some W_3bdfc.
Proof. vm_refl. Qed.
Lemma D_3bdfc : decode_any W_3bdfc = Some (Load SZ8 true 19 2 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3be00 : bv 32 := 0x01013a03.
Lemma F_3be00 : fetch_word Ubsan.M.loaded_segments (0x3f54c : word) = Some W_3be00.
Proof. vm_refl. Qed.
Lemma D_3be00 : decode_any W_3be00 = Some (Load SZ8 true 20 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3be04 : bv 32 := 0x00813a83.
Lemma F_3be04 : fetch_word Ubsan.M.loaded_segments (0x3f550 : word) = Some W_3be04.
Proof. vm_refl. Qed.
Lemma D_3be04 : decode_any W_3be04 = Some (Load SZ8 true 21 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3be08 : bv 32 := 0x04010113.
Lemma F_3be08 : fetch_word Ubsan.M.loaded_segments (0x3f554 : word) = Some W_3be08.
Proof. vm_refl. Qed.
Lemma D_3be08 : decode_any W_3be08 = Some (OpImm ALU_ADD 2 2 64, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3be0c : bv 32 := 0x00008067.
Lemma F_3be0c : fetch_word Ubsan.M.loaded_segments (0x3f558 : word) = Some W_3be0c.
Proof. vm_refl. Qed.
Lemma D_3be0c : decode_any W_3be0c = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3be1c : bv 32 := 0xfd010113.
Lemma F_3be1c : fetch_word Ubsan.M.loaded_segments (0x3f568 : word) = Some W_3be1c.
Proof. vm_refl. Qed.
Lemma D_3be1c : decode_any W_3be1c = Some (OpImm ALU_ADD 2 2 4048, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3be20 : bv 32 := 0x02113423.
Lemma F_3be20 : fetch_word Ubsan.M.loaded_segments (0x3f56c : word) = Some W_3be20.
Proof. vm_refl. Qed.
Lemma D_3be20 : decode_any W_3be20 = Some (Store SZ8 2 1 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3be24 : bv 32 := 0x02813023.
Lemma F_3be24 : fetch_word Ubsan.M.loaded_segments (0x3f570 : word) = Some W_3be24.
Proof. vm_refl. Qed.
Lemma D_3be24 : decode_any W_3be24 = Some (Store SZ8 2 8 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3be28 : bv 32 := 0x00913c23.
Lemma F_3be28 : fetch_word Ubsan.M.loaded_segments (0x3f574 : word) = Some W_3be28.
Proof. vm_refl. Qed.
Lemma D_3be28 : decode_any W_3be28 = Some (Store SZ8 2 9 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3be2c : bv 32 := 0x01213823.
Lemma F_3be2c : fetch_word Ubsan.M.loaded_segments (0x3f578 : word) = Some W_3be2c.
Proof. vm_refl. Qed.
Lemma D_3be2c : decode_any W_3be2c = Some (Store SZ8 2 18 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3be30 : bv 32 := 0x01313423.
Lemma F_3be30 : fetch_word Ubsan.M.loaded_segments (0x3f57c : word) = Some W_3be30.
Proof. vm_refl. Qed.
Lemma D_3be30 : decode_any W_3be30 = Some (Store SZ8 2 19 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3be34 : bv 32 := 0x0003e517.
Lemma F_3be34 : fetch_word Ubsan.M.loaded_segments (0x3f580 : word) = Some W_3be34.
Proof. vm_refl. Qed.
Lemma D_3be34 : decode_any W_3be34 = Some (Auipc 10 62, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3be38 : bv 32 := 0xb8850913.
Lemma F_3be38 : fetch_word Ubsan.M.loaded_segments (0x3f584 : word) = Some W_3be38.
Proof. vm_refl. Qed.
Lemma D_3be38 : decode_any W_3be38 = Some (OpImm ALU_ADD 18 10 2952, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3be3c : bv 32 := 0x00490413.
Lemma F_3be3c : fetch_word Ubsan.M.loaded_segments (0x3f588 : word) = Some W_3be3c.
Proof. vm_refl. Qed.
Lemma D_3be3c : decode_any W_3be3c = Some (OpImm ALU_ADD 8 18 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3be40 : bv 32 := 0x00040513.
Lemma F_3be40 : fetch_word Ubsan.M.loaded_segments (0x3f58c : word) = Some W_3be40.
Proof. vm_refl. Qed.
Lemma D_3be40 : decode_any W_3be40 = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3be44 : bv 32 := 0x1f1070ef.
Lemma F_3be44 : fetch_word Ubsan.M.loaded_segments (0x3f590 : word) = Some W_3be44.
Proof. vm_refl. Qed.
Lemma D_3be44 : decode_any W_3be44 = Some (Jal 1 31216, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3be48 : bv 32 := 0x01093503.
Lemma F_3be48 : fetch_word Ubsan.M.loaded_segments (0x3f594 : word) = Some W_3be48.
Proof. vm_refl. Qed.
Lemma D_3be48 : decode_any W_3be48 = Some (Load SZ8 true 10 18 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3be4c : bv 32 := 0x06050863.
Lemma F_3be4c : fetch_word Ubsan.M.loaded_segments (0x3f598 : word) = Some W_3be4c.
Proof. vm_refl. Qed.
Lemma D_3be4c : decode_any W_3be4c = Some (Branch BC_EQ 10 0 112, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3be50 : bv 32 := 0x00892583.
Lemma F_3be50 : fetch_word Ubsan.M.loaded_segments (0x3f59c : word) = Some W_3be50.
Proof. vm_refl. Qed.
Lemma D_3be50 : decode_any W_3be50 = Some (Load SZ4 true 11 18 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3be54 : bv 32 := 0x0180006f.
Lemma F_3be54 : fetch_word Ubsan.M.loaded_segments (0x3f5a0 : word) = Some W_3be54.
Proof. vm_refl. Qed.
Lemma D_3be54 : decode_any W_3be54 = Some (Jal 0 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3be58 : bv 32 := 0x00053503.
Lemma F_3be58 : fetch_word Ubsan.M.loaded_segments (0x3f5a4 : word) = Some W_3be58.
Proof. vm_refl. Qed.
Lemma D_3be58 : decode_any W_3be58 = Some (Load SZ8 true 10 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3be5c : bv 32 := 0x02000593.
Lemma F_3be5c : fetch_word Ubsan.M.loaded_segments (0x3f5a8 : word) = Some W_3be5c.
Proof. vm_refl. Qed.
Lemma D_3be5c : decode_any W_3be5c = Some (OpImm ALU_ADD 11 0 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3be60 : bv 32 := 0x00b92423.
Lemma F_3be60 : fetch_word Ubsan.M.loaded_segments (0x3f5ac : word) = Some W_3be60.
Proof. vm_refl. Qed.
Lemma D_3be60 : decode_any W_3be60 = Some (Store SZ4 18 11 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3be64 : bv 32 := 0x00a93823.
Lemma F_3be64 : fetch_word Ubsan.M.loaded_segments (0x3f5b0 : word) = Some W_3be64.
Proof. vm_refl. Qed.
Lemma D_3be64 : decode_any W_3be64 = Some (Store SZ8 18 10 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3be68 : bv 32 := 0x04050a63.
Lemma F_3be68 : fetch_word Ubsan.M.loaded_segments (0x3f5b4 : word) = Some W_3be68.
Proof. vm_refl. Qed.
Lemma D_3be68 : decode_any W_3be68 = Some (Branch BC_EQ 10 0 84, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3be6c : bv 32 := 0xfff5861b.
Lemma F_3be6c : fetch_word Ubsan.M.loaded_segments (0x3f5b8 : word) = Some W_3be6c.
Proof. vm_refl. Qed.
Lemma D_3be6c : decode_any W_3be6c = Some (OpImm32 12 11 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3be70 : bv 32 := 0x00c92423.
Lemma F_3be70 : fetch_word Ubsan.M.loaded_segments (0x3f5bc : word) = Some W_3be70.
Proof. vm_refl. Qed.
Lemma D_3be70 : decode_any W_3be70 = Some (Store SZ4 18 12 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3be74 : bv 32 := 0xfeb052e3.
Lemma F_3be74 : fetch_word Ubsan.M.loaded_segments (0x3f5c0 : word) = Some W_3be74.
Proof. vm_refl. Qed.
Lemma D_3be74 : decode_any W_3be74 = Some (Branch BC_GE 0 11 8164, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3be78 : bv 32 := 0x01093503.
Lemma F_3be78 : fetch_word Ubsan.M.loaded_segments (0x3f5c4 : word) = Some W_3be78.
Proof. vm_refl. Qed.
Lemma D_3be78 : decode_any W_3be78 = Some (Load SZ8 true 10 18 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3be7c : bv 32 := 0x00361613.
Lemma F_3be7c : fetch_word Ubsan.M.loaded_segments (0x3f5c8 : word) = Some W_3be7c.
Proof. vm_refl. Qed.
Lemma D_3be7c : decode_any W_3be7c = Some (ShiftImm ALU_SLL 12 12 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3be80 : bv 32 := 0x00c50533.
Lemma F_3be80 : fetch_word Ubsan.M.loaded_segments (0x3f5cc : word) = Some W_3be80.
Proof. vm_refl. Qed.
Lemma D_3be80 : decode_any W_3be80 = Some (Op ALU_ADD 10 10 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3be84 : bv 32 := 0x00853983.
Lemma F_3be84 : fetch_word Ubsan.M.loaded_segments (0x3f5d0 : word) = Some W_3be84.
Proof. vm_refl. Qed.
Lemma D_3be84 : decode_any W_3be84 = Some (Load SZ8 true 19 10 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3be88 : bv 32 := 0x10853483.
Lemma F_3be88 : fetch_word Ubsan.M.loaded_segments (0x3f5d4 : word) = Some W_3be88.
Proof. vm_refl. Qed.
Lemma D_3be88 : decode_any W_3be88 = Some (Load SZ8 true 9 10 264, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3be8c : bv 32 := 0x00040513.
Lemma F_3be8c : fetch_word Ubsan.M.loaded_segments (0x3f5d8 : word) = Some W_3be8c.
Proof. vm_refl. Qed.
Lemma D_3be8c : decode_any W_3be8c = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3be90 : bv 32 := 0x42d070ef.
Lemma F_3be90 : fetch_word Ubsan.M.loaded_segments (0x3f5dc : word) = Some W_3be90.
Proof. vm_refl. Qed.
Lemma D_3be90 : decode_any W_3be90 = Some (Jal 1 31788, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3be94 : bv 32 := 0x00048513.
Lemma F_3be94 : fetch_word Ubsan.M.loaded_segments (0x3f5e0 : word) = Some W_3be94.
Proof. vm_refl. Qed.
Lemma D_3be94 : decode_any W_3be94 = Some (OpImm ALU_ADD 10 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3be98 : bv 32 := 0x000980e7.
Lemma F_3be98 : fetch_word Ubsan.M.loaded_segments (0x3f5e4 : word) = Some W_3be98.
Proof. vm_refl. Qed.
Lemma D_3be98 : decode_any W_3be98 = Some (Jalr 1 19 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3be9c : bv 32 := 0x00040513.
Lemma F_3be9c : fetch_word Ubsan.M.loaded_segments (0x3f5e8 : word) = Some W_3be9c.
Proof. vm_refl. Qed.
Lemma D_3be9c : decode_any W_3be9c = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3bea0 : bv 32 := 0x195070ef.
Lemma F_3bea0 : fetch_word Ubsan.M.loaded_segments (0x3f5ec : word) = Some W_3bea0.
Proof. vm_refl. Qed.
Lemma D_3bea0 : decode_any W_3bea0 = Some (Jal 1 31124, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3bea4 : bv 32 := 0x00892503.
Lemma F_3bea4 : fetch_word Ubsan.M.loaded_segments (0x3f5f0 : word) = Some W_3bea4.
Proof. vm_refl. Qed.
Lemma D_3bea4 : decode_any W_3bea4 = Some (Load SZ4 true 10 18 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3bea8 : bv 32 := 0xfff5061b.
Lemma F_3bea8 : fetch_word Ubsan.M.loaded_segments (0x3f5f4 : word) = Some W_3bea8.
Proof. vm_refl. Qed.
Lemma D_3bea8 : decode_any W_3bea8 = Some (OpImm32 12 10 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3beac : bv 32 := 0x00c92423.
Lemma F_3beac : fetch_word Ubsan.M.loaded_segments (0x3f5f8 : word) = Some W_3beac.
Proof. vm_refl. Qed.
Lemma D_3beac : decode_any W_3beac = Some (Store SZ4 18 12 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3beb0 : bv 32 := 0xfca044e3.
Lemma F_3beb0 : fetch_word Ubsan.M.loaded_segments (0x3f5fc : word) = Some W_3beb0.
Proof. vm_refl. Qed.
Lemma D_3beb0 : decode_any W_3beb0 = Some (Branch BC_LT 0 10 8136, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3beb4 : bv 32 := 0x01093503.
Lemma F_3beb4 : fetch_word Ubsan.M.loaded_segments (0x3f600 : word) = Some W_3beb4.
Proof. vm_refl. Qed.
Lemma D_3beb4 : decode_any W_3beb4 = Some (Load SZ8 true 10 18 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3beb8 : bv 32 := 0xfa1ff06f.
Lemma F_3beb8 : fetch_word Ubsan.M.loaded_segments (0x3f604 : word) = Some W_3beb8.
Proof. vm_refl. Qed.
Lemma D_3beb8 : decode_any W_3beb8 = Some (Jal 0 2097056, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3bebc : bv 32 := 0x00100513.
Lemma F_3bebc : fetch_word Ubsan.M.loaded_segments (0x3f608 : word) = Some W_3bebc.
Proof. vm_refl. Qed.
Lemma D_3bebc : decode_any W_3bebc = Some (OpImm ALU_ADD 10 0 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3bec0 : bv 32 := 0x00a90023.
Lemma F_3bec0 : fetch_word Ubsan.M.loaded_segments (0x3f60c : word) = Some W_3bec0.
Proof. vm_refl. Qed.
Lemma D_3bec0 : decode_any W_3bec0 = Some (Store SZ1 18 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3bec4 : bv 32 := 0x00040513.
Lemma F_3bec4 : fetch_word Ubsan.M.loaded_segments (0x3f610 : word) = Some W_3bec4.
Proof. vm_refl. Qed.
Lemma D_3bec4 : decode_any W_3bec4 = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3bec8 : bv 32 := 0x02813083.
Lemma F_3bec8 : fetch_word Ubsan.M.loaded_segments (0x3f614 : word) = Some W_3bec8.
Proof. vm_refl. Qed.
Lemma D_3bec8 : decode_any W_3bec8 = Some (Load SZ8 true 1 2 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3becc : bv 32 := 0x02013403.
Lemma F_3becc : fetch_word Ubsan.M.loaded_segments (0x3f618 : word) = Some W_3becc.
Proof. vm_refl. Qed.
Lemma D_3becc : decode_any W_3becc = Some (Load SZ8 true 8 2 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3bed0 : bv 32 := 0x01813483.
Lemma F_3bed0 : fetch_word Ubsan.M.loaded_segments (0x3f61c : word) = Some W_3bed0.
Proof. vm_refl. Qed.
Lemma D_3bed0 : decode_any W_3bed0 = Some (Load SZ8 true 9 2 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3bed4 : bv 32 := 0x01013903.
Lemma F_3bed4 : fetch_word Ubsan.M.loaded_segments (0x3f620 : word) = Some W_3bed4.
Proof. vm_refl. Qed.
Lemma D_3bed4 : decode_any W_3bed4 = Some (Load SZ8 true 18 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3bed8 : bv 32 := 0x00813983.
Lemma F_3bed8 : fetch_word Ubsan.M.loaded_segments (0x3f624 : word) = Some W_3bed8.
Proof. vm_refl. Qed.
Lemma D_3bed8 : decode_any W_3bed8 = Some (Load SZ8 true 19 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3bedc : bv 32 := 0x03010113.
Lemma F_3bedc : fetch_word Ubsan.M.loaded_segments (0x3f628 : word) = Some W_3bedc.
Proof. vm_refl. Qed.
Lemma D_3bedc : decode_any W_3bedc = Some (OpImm ALU_ADD 2 2 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3bee0 : bv 32 := 0x3dd0706f.
Lemma F_3bee0 : fetch_word Ubsan.M.loaded_segments (0x3f62c : word) = Some W_3bee0.
Proof. vm_refl. Qed.
Lemma D_3bee0 : decode_any W_3bee0 = Some (Jal 0 31708, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3bee4 : bv 32 := 0x00008067.
Lemma F_3bee4 : fetch_word Ubsan.M.loaded_segments (0x3f630 : word) = Some W_3bee4.
Proof. vm_refl. Qed.
Lemma D_3bee4 : decode_any W_3bee4 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3bfac : bv 32 := 0x00050067.
Lemma F_3bfac : fetch_word Ubsan.M.loaded_segments (0x3f6f8 : word) = Some W_3bfac.
Proof. vm_refl. Qed.
Lemma D_3bfac : decode_any W_3bfac = Some (Jalr 0 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3bfb0 : bv 32 := 0x00008067.
Lemma F_3bfb0 : fetch_word Ubsan.M.loaded_segments (0x3f6fc : word) = Some W_3bfb0.
Proof. vm_refl. Qed.
Lemma D_3bfb0 : decode_any W_3bfb0 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3bfb4 : bv 32 := 0xfe010113.
Lemma F_3bfb4 : fetch_word Ubsan.M.loaded_segments (0x3f700 : word) = Some W_3bfb4.
Proof. vm_refl. Qed.
Lemma D_3bfb4 : decode_any W_3bfb4 = Some (OpImm ALU_ADD 2 2 4064, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3bfb8 : bv 32 := 0x00113c23.
Lemma F_3bfb8 : fetch_word Ubsan.M.loaded_segments (0x3f704 : word) = Some W_3bfb8.
Proof. vm_refl. Qed.
Lemma D_3bfb8 : decode_any W_3bfb8 = Some (Store SZ8 2 1 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3bfbc : bv 32 := 0x00813823.
Lemma F_3bfbc : fetch_word Ubsan.M.loaded_segments (0x3f708 : word) = Some W_3bfbc.
Proof. vm_refl. Qed.
Lemma D_3bfbc : decode_any W_3bfbc = Some (Store SZ8 2 8 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3bfc0 : bv 32 := 0x00913423.
Lemma F_3bfc0 : fetch_word Ubsan.M.loaded_segments (0x3f70c : word) = Some W_3bfc0.
Proof. vm_refl. Qed.
Lemma D_3bfc0 : decode_any W_3bfc0 = Some (Store SZ8 2 9 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3bfc4 : bv 32 := 0x0000c517.
Lemma F_3bfc4 : fetch_word Ubsan.M.loaded_segments (0x3f710 : word) = Some W_3bfc4.
Proof. vm_refl. Qed.
Lemma D_3bfc4 : decode_any W_3bfc4 = Some (Auipc 10 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3bfc8 : bv 32 := 0x0000c597.
Lemma F_3bfc8 : fetch_word Ubsan.M.loaded_segments (0x3f714 : word) = Some W_3bfc8.
Proof. vm_refl. Qed.
Lemma D_3bfc8 : decode_any W_3bfc8 = Some (Auipc 11 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3bfcc : bv 32 := 0x5d053503.
Lemma F_3bfcc : fetch_word Ubsan.M.loaded_segments (0x3f718 : word) = Some W_3bfcc.
Proof. vm_refl. Qed.
Lemma D_3bfcc : decode_any W_3bfcc = Some (Load SZ8 true 10 10 1488, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3bfd0 : bv 32 := 0x5d45b403.
Lemma F_3bfd0 : fetch_word Ubsan.M.loaded_segments (0x3f71c : word) = Some W_3bfd0.
Proof. vm_refl. Qed.
Lemma D_3bfd0 : decode_any W_3bfd0 = Some (Load SZ8 true 8 11 1492, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3bfd4 : bv 32 := 0x00a47c63.
Lemma F_3bfd4 : fetch_word Ubsan.M.loaded_segments (0x3f720 : word) = Some W_3bfd4.
Proof. vm_refl. Qed.
Lemma D_3bfd4 : decode_any W_3bfd4 = Some (Branch BC_GEU 8 10 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3bfd8 : bv 32 := 0xff853583.
Lemma F_3bfd8 : fetch_word Ubsan.M.loaded_segments (0x3f724 : word) = Some W_3bfd8.
Proof. vm_refl. Qed.
Lemma D_3bfd8 : decode_any W_3bfd8 = Some (Load SZ8 true 11 10 4088, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3bfdc : bv 32 := 0xff850493.
Lemma F_3bfdc : fetch_word Ubsan.M.loaded_segments (0x3f728 : word) = Some W_3bfdc.
Proof. vm_refl. Qed.
Lemma D_3bfdc : decode_any W_3bfdc = Some (OpImm ALU_ADD 9 10 4088, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3bfe0 : bv 32 := 0x000580e7.
Lemma F_3bfe0 : fetch_word Ubsan.M.loaded_segments (0x3f72c : word) = Some W_3bfe0.
Proof. vm_refl. Qed.
Lemma D_3bfe0 : decode_any W_3bfe0 = Some (Jalr 1 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3bfe4 : bv 32 := 0x00048513.
Lemma F_3bfe4 : fetch_word Ubsan.M.loaded_segments (0x3f730 : word) = Some W_3bfe4.
Proof. vm_refl. Qed.
Lemma D_3bfe4 : decode_any W_3bfe4 = Some (OpImm ALU_ADD 10 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3bfe8 : bv 32 := 0xfe9468e3.
Lemma F_3bfe8 : fetch_word Ubsan.M.loaded_segments (0x3f734 : word) = Some W_3bfe8.
Proof. vm_refl. Qed.
Lemma D_3bfe8 : decode_any W_3bfe8 = Some (Branch BC_LTU 8 9 8176, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3bfec : bv 32 := 0x01813083.
Lemma F_3bfec : fetch_word Ubsan.M.loaded_segments (0x3f738 : word) = Some W_3bfec.
Proof. vm_refl. Qed.
Lemma D_3bfec : decode_any W_3bfec = Some (Load SZ8 true 1 2 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3bff0 : bv 32 := 0x01013403.
Lemma F_3bff0 : fetch_word Ubsan.M.loaded_segments (0x3f73c : word) = Some W_3bff0.
Proof. vm_refl. Qed.
Lemma D_3bff0 : decode_any W_3bff0 = Some (Load SZ8 true 8 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3bff4 : bv 32 := 0x00813483.
Lemma F_3bff4 : fetch_word Ubsan.M.loaded_segments (0x3f740 : word) = Some W_3bff4.
Proof. vm_refl. Qed.
Lemma D_3bff4 : decode_any W_3bff4 = Some (Load SZ8 true 9 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3bff8 : bv 32 := 0x02010113.
Lemma F_3bff8 : fetch_word Ubsan.M.loaded_segments (0x3f744 : word) = Some W_3bff8.
Proof. vm_refl. Qed.
Lemma D_3bff8 : decode_any W_3bff8 = Some (OpImm ALU_ADD 2 2 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3bffc : bv 32 := 0xfb5ff06f.
Lemma F_3bffc : fetch_word Ubsan.M.loaded_segments (0x3f748 : word) = Some W_3bffc.
Proof. vm_refl. Qed.
Lemma D_3bffc : decode_any W_3bffc = Some (Jal 0 2097076, 4%Z).
Proof. vm_refl. Qed.
