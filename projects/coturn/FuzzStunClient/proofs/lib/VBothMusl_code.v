(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.coturn.FuzzStunClient.images Require Import AsanUbsan.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.

(* [comment removed for export] *)
Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

(* [comment removed for export] *)
Definition W_9850c : bv 32 := 0xfbf5059b.
Lemma F_9850c : fetch_word AsanUbsan.M.loaded_segments (0x9850c : word) = Some W_9850c.
Proof. vm_refl. Qed.
Lemma D_9850c : decode_any W_9850c = Some (OpImm32 11 10 4031, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_98510 : bv 32 := 0x01a5b593.
Lemma F_98510 : fetch_word AsanUbsan.M.loaded_segments (0x98510 : word) = Some W_98510.
Proof. vm_refl. Qed.
Lemma D_98510 : decode_any W_98510 = Some (OpImm ALU_SLTU 11 11 26, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_98514 : bv 32 := 0x00559593.
Lemma F_98514 : fetch_word AsanUbsan.M.loaded_segments (0x98514 : word) = Some W_98514.
Proof. vm_refl. Qed.
Lemma D_98514 : decode_any W_98514 = Some (ShiftImm ALU_SLL 11 11 5, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_98518 : bv 32 := 0x00b56533.
Lemma F_98518 : fetch_word AsanUbsan.M.loaded_segments (0x98518 : word) = Some W_98518.
Proof. vm_refl. Qed.
Lemma D_98518 : decode_any W_98518 = Some (Op ALU_OR 10 10 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9851c : bv 32 := 0x00008067.
Lemma F_9851c : fetch_word AsanUbsan.M.loaded_segments (0x9851c : word) = Some W_9851c.
Proof. vm_refl. Qed.
Lemma D_9851c : decode_any W_9851c = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.
(* [comment removed for export] *)
Definition W_a27b8 : bv 32 := 0x02060063.
Lemma F_a27b8 : fetch_word AsanUbsan.M.loaded_segments (0xa27b8 : word) = Some W_a27b8.
Proof. vm_refl. Qed.
Lemma D_a27b8 : decode_any W_a27b8 = Some (Branch BC_EQ 12 0 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a27bc : bv 32 := 0x00054683.
Lemma F_a27bc : fetch_word AsanUbsan.M.loaded_segments (0xa27bc : word) = Some W_a27bc.
Proof. vm_refl. Qed.
Lemma D_a27bc : decode_any W_a27bc = Some (Load SZ1 false 13 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a27c0 : bv 32 := 0x0005c703.
Lemma F_a27c0 : fetch_word AsanUbsan.M.loaded_segments (0xa27c0 : word) = Some W_a27c0.
Proof. vm_refl. Qed.
Lemma D_a27c0 : decode_any W_a27c0 = Some (Load SZ1 false 14 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a27c4 : bv 32 := 0x00e69e63.
Lemma F_a27c4 : fetch_word AsanUbsan.M.loaded_segments (0xa27c4 : word) = Some W_a27c4.
Proof. vm_refl. Qed.
Lemma D_a27c4 : decode_any W_a27c4 = Some (Branch BC_NE 13 14 28, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a27c8 : bv 32 := 0xfff60613.
Lemma F_a27c8 : fetch_word AsanUbsan.M.loaded_segments (0xa27c8 : word) = Some W_a27c8.
Proof. vm_refl. Qed.
Lemma D_a27c8 : decode_any W_a27c8 = Some (OpImm ALU_ADD 12 12 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a27cc : bv 32 := 0x00150513.
Lemma F_a27cc : fetch_word AsanUbsan.M.loaded_segments (0xa27cc : word) = Some W_a27cc.
Proof. vm_refl. Qed.
Lemma D_a27cc : decode_any W_a27cc = Some (OpImm ALU_ADD 10 10 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a27d0 : bv 32 := 0x00158593.
Lemma F_a27d0 : fetch_word AsanUbsan.M.loaded_segments (0xa27d0 : word) = Some W_a27d0.
Proof. vm_refl. Qed.
Lemma D_a27d0 : decode_any W_a27d0 = Some (OpImm ALU_ADD 11 11 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a27d4 : bv 32 := 0xfe0614e3.
Lemma F_a27d4 : fetch_word AsanUbsan.M.loaded_segments (0xa27d4 : word) = Some W_a27d4.
Proof. vm_refl. Qed.
Lemma D_a27d4 : decode_any W_a27d4 = Some (Branch BC_NE 12 0 8168, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a27d8 : bv 32 := 0x00000513.
Lemma F_a27d8 : fetch_word AsanUbsan.M.loaded_segments (0xa27d8 : word) = Some W_a27d8.
Proof. vm_refl. Qed.
Lemma D_a27d8 : decode_any W_a27d8 = Some (OpImm ALU_ADD 10 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a27dc : bv 32 := 0x00008067.
Lemma F_a27dc : fetch_word AsanUbsan.M.loaded_segments (0xa27dc : word) = Some W_a27dc.
Proof. vm_refl. Qed.
Lemma D_a27dc : decode_any W_a27dc = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a27e0 : bv 32 := 0x40e68533.
Lemma F_a27e0 : fetch_word AsanUbsan.M.loaded_segments (0xa27e0 : word) = Some W_a27e0.
Proof. vm_refl. Qed.
Lemma D_a27e0 : decode_any W_a27e0 = Some (Op ALU_SUB 10 13 14, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a27e4 : bv 32 := 0x00008067.
Lemma F_a27e4 : fetch_word AsanUbsan.M.loaded_segments (0xa27e4 : word) = Some W_a27e4.
Proof. vm_refl. Qed.
Lemma D_a27e4 : decode_any W_a27e4 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.
(* [comment removed for export] *)
Definition W_a2e38 : bv 32 := 0x00757593.
Lemma F_a2e38 : fetch_word AsanUbsan.M.loaded_segments (0xa2e38 : word) = Some W_a2e38.
Proof. vm_refl. Qed.
Lemma D_a2e38 : decode_any W_a2e38 = Some (OpImm ALU_AND 11 10 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a2e3c : bv 32 := 0x00050613.
Lemma F_a2e3c : fetch_word AsanUbsan.M.loaded_segments (0xa2e3c : word) = Some W_a2e3c.
Proof. vm_refl. Qed.
Lemma D_a2e3c : decode_any W_a2e3c = Some (OpImm ALU_ADD 12 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a2e40 : bv 32 := 0x02058a63.
Lemma F_a2e40 : fetch_word AsanUbsan.M.loaded_segments (0xa2e40 : word) = Some W_a2e40.
Proof. vm_refl. Qed.
Lemma D_a2e40 : decode_any W_a2e40 = Some (Branch BC_EQ 11 0 52, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a2e44 : bv 32 := 0x00054583.
Lemma F_a2e44 : fetch_word AsanUbsan.M.loaded_segments (0xa2e44 : word) = Some W_a2e44.
Proof. vm_refl. Qed.
Lemma D_a2e44 : decode_any W_a2e44 = Some (Load SZ1 false 11 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a2e48 : bv 32 := 0x06058c63.
Lemma F_a2e48 : fetch_word AsanUbsan.M.loaded_segments (0xa2e48 : word) = Some W_a2e48.
Proof. vm_refl. Qed.
Lemma D_a2e48 : decode_any W_a2e48 = Some (Branch BC_EQ 11 0 120, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a2e4c : bv 32 := 0x00150613.
Lemma F_a2e4c : fetch_word AsanUbsan.M.loaded_segments (0xa2e4c : word) = Some W_a2e4c.
Proof. vm_refl. Qed.
Lemma D_a2e4c : decode_any W_a2e4c = Some (OpImm ALU_ADD 12 10 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a2e50 : bv 32 := 0x00050593.
Lemma F_a2e50 : fetch_word AsanUbsan.M.loaded_segments (0xa2e50 : word) = Some W_a2e50.
Proof. vm_refl. Qed.
Lemma D_a2e50 : decode_any W_a2e50 = Some (OpImm ALU_ADD 11 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a2e54 : bv 32 := 0x00158693.
Lemma F_a2e54 : fetch_word AsanUbsan.M.loaded_segments (0xa2e54 : word) = Some W_a2e54.
Proof. vm_refl. Qed.
Lemma D_a2e54 : decode_any W_a2e54 = Some (OpImm ALU_ADD 13 11 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a2e58 : bv 32 := 0x0076f693.
Lemma F_a2e58 : fetch_word AsanUbsan.M.loaded_segments (0xa2e58 : word) = Some W_a2e58.
Proof. vm_refl. Qed.
Lemma D_a2e58 : decode_any W_a2e58 = Some (OpImm ALU_AND 13 13 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a2e5c : bv 32 := 0x00068c63.
Lemma F_a2e5c : fetch_word AsanUbsan.M.loaded_segments (0xa2e5c : word) = Some W_a2e5c.
Proof. vm_refl. Qed.
Lemma D_a2e5c : decode_any W_a2e5c = Some (Branch BC_EQ 13 0 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a2e60 : bv 32 := 0x00064683.
Lemma F_a2e60 : fetch_word AsanUbsan.M.loaded_segments (0xa2e60 : word) = Some W_a2e60.
Proof. vm_refl. Qed.
Lemma D_a2e60 : decode_any W_a2e60 = Some (Load SZ1 false 13 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a2e64 : bv 32 := 0x00160613.
Lemma F_a2e64 : fetch_word AsanUbsan.M.loaded_segments (0xa2e64 : word) = Some W_a2e64.
Proof. vm_refl. Qed.
Lemma D_a2e64 : decode_any W_a2e64 = Some (OpImm ALU_ADD 12 12 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a2e68 : bv 32 := 0x00158593.
Lemma F_a2e68 : fetch_word AsanUbsan.M.loaded_segments (0xa2e68 : word) = Some W_a2e68.
Proof. vm_refl. Qed.
Lemma D_a2e68 : decode_any W_a2e68 = Some (OpImm ALU_ADD 11 11 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a2e6c : bv 32 := 0xfe0694e3.
Lemma F_a2e6c : fetch_word AsanUbsan.M.loaded_segments (0xa2e6c : word) = Some W_a2e6c.
Proof. vm_refl. Qed.
Lemma D_a2e6c : decode_any W_a2e6c = Some (Branch BC_NE 13 0 8168, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a2e70 : bv 32 := 0x0480006f.
Lemma F_a2e70 : fetch_word AsanUbsan.M.loaded_segments (0xa2e70 : word) = Some W_a2e70.
Proof. vm_refl. Qed.
Lemma D_a2e70 : decode_any W_a2e70 = Some (Jal 0 72, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a2e74 : bv 32 := 0xfff6d597.
Lemma F_a2e74 : fetch_word AsanUbsan.M.loaded_segments (0xa2e74 : word) = Some W_a2e74.
Proof. vm_refl. Qed.
Lemma D_a2e74 : decode_any W_a2e74 = Some (Auipc 11 1048429, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a2e78 : bv 32 := 0xfff6d717.
Lemma F_a2e78 : fetch_word AsanUbsan.M.loaded_segments (0xa2e78 : word) = Some W_a2e78.
Proof. vm_refl. Qed.
Lemma D_a2e78 : decode_any W_a2e78 = Some (Auipc 14 1048429, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a2e7c : bv 32 := 0x50c5b683.
Lemma F_a2e7c : fetch_word AsanUbsan.M.loaded_segments (0xa2e7c : word) = Some W_a2e7c.
Proof. vm_refl. Qed.
Lemma D_a2e7c : decode_any W_a2e7c = Some (Load SZ8 true 13 11 1292, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a2e80 : bv 32 := 0x4e873703.
Lemma F_a2e80 : fetch_word AsanUbsan.M.loaded_segments (0xa2e80 : word) = Some W_a2e80.
Proof. vm_refl. Qed.
Lemma D_a2e80 : decode_any W_a2e80 = Some (Load SZ8 true 14 14 1256, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a2e84 : bv 32 := 0xff760593.
Lemma F_a2e84 : fetch_word AsanUbsan.M.loaded_segments (0xa2e84 : word) = Some W_a2e84.
Proof. vm_refl. Qed.
Lemma D_a2e84 : decode_any W_a2e84 = Some (OpImm ALU_ADD 11 12 4087, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a2e88 : bv 32 := 0xff860613.
Lemma F_a2e88 : fetch_word AsanUbsan.M.loaded_segments (0xa2e88 : word) = Some W_a2e88.
Proof. vm_refl. Qed.
Lemma D_a2e88 : decode_any W_a2e88 = Some (OpImm ALU_ADD 12 12 4088, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a2e8c : bv 32 := 0x00863783.
Lemma F_a2e8c : fetch_word AsanUbsan.M.loaded_segments (0xa2e8c : word) = Some W_a2e8c.
Proof. vm_refl. Qed.
Lemma D_a2e8c : decode_any W_a2e8c = Some (Load SZ8 true 15 12 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a2e90 : bv 32 := 0x00860613.
Lemma F_a2e90 : fetch_word AsanUbsan.M.loaded_segments (0xa2e90 : word) = Some W_a2e90.
Proof. vm_refl. Qed.
Lemma D_a2e90 : decode_any W_a2e90 = Some (OpImm ALU_ADD 12 12 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a2e94 : bv 32 := 0x40f68833.
Lemma F_a2e94 : fetch_word AsanUbsan.M.loaded_segments (0xa2e94 : word) = Some W_a2e94.
Proof. vm_refl. Qed.
Lemma D_a2e94 : decode_any W_a2e94 = Some (Op ALU_SUB 16 13 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a2e98 : bv 32 := 0x00f867b3.
Lemma F_a2e98 : fetch_word AsanUbsan.M.loaded_segments (0xa2e98 : word) = Some W_a2e98.
Proof. vm_refl. Qed.
Lemma D_a2e98 : decode_any W_a2e98 = Some (Op ALU_OR 15 16 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a2e9c : bv 32 := 0x00e7f7b3.
Lemma F_a2e9c : fetch_word AsanUbsan.M.loaded_segments (0xa2e9c : word) = Some W_a2e9c.
Proof. vm_refl. Qed.
Lemma D_a2e9c : decode_any W_a2e9c = Some (Op ALU_AND 15 15 14, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a2ea0 : bv 32 := 0x00858593.
Lemma F_a2ea0 : fetch_word AsanUbsan.M.loaded_segments (0xa2ea0 : word) = Some W_a2ea0.
Proof. vm_refl. Qed.
Lemma D_a2ea0 : decode_any W_a2ea0 = Some (OpImm ALU_ADD 11 11 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a2ea4 : bv 32 := 0xfee784e3.
Lemma F_a2ea4 : fetch_word AsanUbsan.M.loaded_segments (0xa2ea4 : word) = Some W_a2ea4.
Proof. vm_refl. Qed.
Lemma D_a2ea4 : decode_any W_a2ea4 = Some (Branch BC_EQ 15 14 8168, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a2ea8 : bv 32 := 0x00064683.
Lemma F_a2ea8 : fetch_word AsanUbsan.M.loaded_segments (0xa2ea8 : word) = Some W_a2ea8.
Proof. vm_refl. Qed.
Lemma D_a2ea8 : decode_any W_a2ea8 = Some (Load SZ1 false 13 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a2eac : bv 32 := 0x00160613.
Lemma F_a2eac : fetch_word AsanUbsan.M.loaded_segments (0xa2eac : word) = Some W_a2eac.
Proof. vm_refl. Qed.
Lemma D_a2eac : decode_any W_a2eac = Some (OpImm ALU_ADD 12 12 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a2eb0 : bv 32 := 0x00158593.
Lemma F_a2eb0 : fetch_word AsanUbsan.M.loaded_segments (0xa2eb0 : word) = Some W_a2eb0.
Proof. vm_refl. Qed.
Lemma D_a2eb0 : decode_any W_a2eb0 = Some (OpImm ALU_ADD 11 11 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a2eb4 : bv 32 := 0xfe069ae3.
Lemma F_a2eb4 : fetch_word AsanUbsan.M.loaded_segments (0xa2eb4 : word) = Some W_a2eb4.
Proof. vm_refl. Qed.
Lemma D_a2eb4 : decode_any W_a2eb4 = Some (Branch BC_NE 13 0 8180, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a2eb8 : bv 32 := 0x40a58533.
Lemma F_a2eb8 : fetch_word AsanUbsan.M.loaded_segments (0xa2eb8 : word) = Some W_a2eb8.
Proof. vm_refl. Qed.
Lemma D_a2eb8 : decode_any W_a2eb8 = Some (Op ALU_SUB 10 11 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a2ebc : bv 32 := 0x00008067.
Lemma F_a2ebc : fetch_word AsanUbsan.M.loaded_segments (0xa2ebc : word) = Some W_a2ebc.
Proof. vm_refl. Qed.
Lemma D_a2ebc : decode_any W_a2ebc = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a2ec0 : bv 32 := 0x40a50533.
Lemma F_a2ec0 : fetch_word AsanUbsan.M.loaded_segments (0xa2ec0 : word) = Some W_a2ec0.
Proof. vm_refl. Qed.
Lemma D_a2ec0 : decode_any W_a2ec0 = Some (Op ALU_SUB 10 10 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a2ec4 : bv 32 := 0x00008067.
Lemma F_a2ec4 : fetch_word AsanUbsan.M.loaded_segments (0xa2ec4 : word) = Some W_a2ec4.
Proof. vm_refl. Qed.
Lemma D_a2ec4 : decode_any W_a2ec4 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.
(* [comment removed for export] *)
Definition W_a2f3c : bv 32 := 0xff010113.
Lemma F_a2f3c : fetch_word AsanUbsan.M.loaded_segments (0xa2f3c : word) = Some W_a2f3c.
Proof. vm_refl. Qed.
Lemma D_a2f3c : decode_any W_a2f3c = Some (OpImm ALU_ADD 2 2 4080, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a2f40 : bv 32 := 0x00113423.
Lemma F_a2f40 : fetch_word AsanUbsan.M.loaded_segments (0xa2f40 : word) = Some W_a2f40.
Proof. vm_refl. Qed.
Lemma D_a2f40 : decode_any W_a2f40 = Some (Store SZ8 2 1 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a2f44 : bv 32 := 0x00813023.
Lemma F_a2f44 : fetch_word AsanUbsan.M.loaded_segments (0xa2f44 : word) = Some W_a2f44.
Proof. vm_refl. Qed.
Lemma D_a2f44 : decode_any W_a2f44 = Some (Store SZ8 2 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a2f48 : bv 32 := 0x00050413.
Lemma F_a2f48 : fetch_word AsanUbsan.M.loaded_segments (0xa2f48 : word) = Some W_a2f48.
Proof. vm_refl. Qed.
Lemma D_a2f48 : decode_any W_a2f48 = Some (OpImm ALU_ADD 8 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a2f4c : bv 32 := 0x018000ef.
Lemma F_a2f4c : fetch_word AsanUbsan.M.loaded_segments (0xa2f4c : word) = Some W_a2f4c.
Proof. vm_refl. Qed.
Lemma D_a2f4c : decode_any W_a2f4c = Some (Jal 1 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a2f50 : bv 32 := 0x00040513.
Lemma F_a2f50 : fetch_word AsanUbsan.M.loaded_segments (0xa2f50 : word) = Some W_a2f50.
Proof. vm_refl. Qed.
Lemma D_a2f50 : decode_any W_a2f50 = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a2f54 : bv 32 := 0x00813083.
Lemma F_a2f54 : fetch_word AsanUbsan.M.loaded_segments (0xa2f54 : word) = Some W_a2f54.
Proof. vm_refl. Qed.
Lemma D_a2f54 : decode_any W_a2f54 = Some (Load SZ8 true 1 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a2f58 : bv 32 := 0x00013403.
Lemma F_a2f58 : fetch_word AsanUbsan.M.loaded_segments (0xa2f58 : word) = Some W_a2f58.
Proof. vm_refl. Qed.
Lemma D_a2f58 : decode_any W_a2f58 = Some (Load SZ8 true 8 2 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a2f5c : bv 32 := 0x01010113.
Lemma F_a2f5c : fetch_word AsanUbsan.M.loaded_segments (0xa2f5c : word) = Some W_a2f5c.
Proof. vm_refl. Qed.
Lemma D_a2f5c : decode_any W_a2f5c = Some (OpImm ALU_ADD 2 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a2f60 : bv 32 := 0x00008067.
Lemma F_a2f60 : fetch_word AsanUbsan.M.loaded_segments (0xa2f60 : word) = Some W_a2f60.
Proof. vm_refl. Qed.
Lemma D_a2f60 : decode_any W_a2f60 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a2f64 : bv 32 := 0xff010113.
Lemma F_a2f64 : fetch_word AsanUbsan.M.loaded_segments (0xa2f64 : word) = Some W_a2f64.
Proof. vm_refl. Qed.
Lemma D_a2f64 : decode_any W_a2f64 = Some (OpImm ALU_ADD 2 2 4080, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a2f68 : bv 32 := 0x00113423.
Lemma F_a2f68 : fetch_word AsanUbsan.M.loaded_segments (0xa2f68 : word) = Some W_a2f68.
Proof. vm_refl. Qed.
Lemma D_a2f68 : decode_any W_a2f68 = Some (Store SZ8 2 1 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a2f6c : bv 32 := 0x00813023.
Lemma F_a2f6c : fetch_word AsanUbsan.M.loaded_segments (0xa2f6c : word) = Some W_a2f6c.
Proof. vm_refl. Qed.
Lemma D_a2f6c : decode_any W_a2f6c = Some (Store SZ8 2 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a2f70 : bv 32 := 0x00050413.
Lemma F_a2f70 : fetch_word AsanUbsan.M.loaded_segments (0xa2f70 : word) = Some W_a2f70.
Proof. vm_refl. Qed.
Lemma D_a2f70 : decode_any W_a2f70 = Some (OpImm ALU_ADD 8 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a2f74 : bv 32 := 0x00a5c6b3.
Lemma F_a2f74 : fetch_word AsanUbsan.M.loaded_segments (0xa2f74 : word) = Some W_a2f74.
Proof. vm_refl. Qed.
Lemma D_a2f74 : decode_any W_a2f74 = Some (Op ALU_XOR 13 11 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a2f78 : bv 32 := 0x0076f693.
Lemma F_a2f78 : fetch_word AsanUbsan.M.loaded_segments (0xa2f78 : word) = Some W_a2f78.
Proof. vm_refl. Qed.
Lemma D_a2f78 : decode_any W_a2f78 = Some (OpImm ALU_AND 13 13 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a2f7c : bv 32 := 0x02068663.
Lemma F_a2f7c : fetch_word AsanUbsan.M.loaded_segments (0xa2f7c : word) = Some W_a2f7c.
Proof. vm_refl. Qed.
Lemma D_a2f7c : decode_any W_a2f7c = Some (Branch BC_EQ 13 0 44, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a2f80 : bv 32 := 0x0c060263.
Lemma F_a2f80 : fetch_word AsanUbsan.M.loaded_segments (0xa2f80 : word) = Some W_a2f80.
Proof. vm_refl. Qed.
Lemma D_a2f80 : decode_any W_a2f80 = Some (Branch BC_EQ 12 0 196, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a2f84 : bv 32 := 0x00060693.
Lemma F_a2f84 : fetch_word AsanUbsan.M.loaded_segments (0xa2f84 : word) = Some W_a2f84.
Proof. vm_refl. Qed.
Lemma D_a2f84 : decode_any W_a2f84 = Some (OpImm ALU_ADD 13 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a2f88 : bv 32 := 0x0005c603.
Lemma F_a2f88 : fetch_word AsanUbsan.M.loaded_segments (0xa2f88 : word) = Some W_a2f88.
Proof. vm_refl. Qed.
Lemma D_a2f88 : decode_any W_a2f88 = Some (Load SZ1 false 12 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a2f8c : bv 32 := 0x00c40023.
Lemma F_a2f8c : fetch_word AsanUbsan.M.loaded_segments (0xa2f8c : word) = Some W_a2f8c.
Proof. vm_refl. Qed.
Lemma D_a2f8c : decode_any W_a2f8c = Some (Store SZ1 8 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a2f90 : bv 32 := 0x0a060c63.
Lemma F_a2f90 : fetch_word AsanUbsan.M.loaded_segments (0xa2f90 : word) = Some W_a2f90.
Proof. vm_refl. Qed.
Lemma D_a2f90 : decode_any W_a2f90 = Some (Branch BC_EQ 12 0 184, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a2f94 : bv 32 := 0xfff68693.
Lemma F_a2f94 : fetch_word AsanUbsan.M.loaded_segments (0xa2f94 : word) = Some W_a2f94.
Proof. vm_refl. Qed.
Lemma D_a2f94 : decode_any W_a2f94 = Some (OpImm ALU_ADD 13 13 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a2f98 : bv 32 := 0x00158593.
Lemma F_a2f98 : fetch_word AsanUbsan.M.loaded_segments (0xa2f98 : word) = Some W_a2f98.
Proof. vm_refl. Qed.
Lemma D_a2f98 : decode_any W_a2f98 = Some (OpImm ALU_ADD 11 11 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a2f9c : bv 32 := 0x00140413.
Lemma F_a2f9c : fetch_word AsanUbsan.M.loaded_segments (0xa2f9c : word) = Some W_a2f9c.
Proof. vm_refl. Qed.
Lemma D_a2f9c : decode_any W_a2f9c = Some (OpImm ALU_ADD 8 8 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a2fa0 : bv 32 := 0xfe0694e3.
Lemma F_a2fa0 : fetch_word AsanUbsan.M.loaded_segments (0xa2fa0 : word) = Some W_a2fa0.
Proof. vm_refl. Qed.
Lemma D_a2fa0 : decode_any W_a2fa0 = Some (Branch BC_NE 13 0 8168, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a2fa4 : bv 32 := 0x0a40006f.
Lemma F_a2fa4 : fetch_word AsanUbsan.M.loaded_segments (0xa2fa4 : word) = Some W_a2fa4.
Proof. vm_refl. Qed.
Lemma D_a2fa4 : decode_any W_a2fa4 = Some (Jal 0 164, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a2fa8 : bv 32 := 0x0075f693.
Lemma F_a2fa8 : fetch_word AsanUbsan.M.loaded_segments (0xa2fa8 : word) = Some W_a2fa8.
Proof. vm_refl. Qed.
Lemma D_a2fa8 : decode_any W_a2fa8 = Some (OpImm ALU_AND 13 11 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a2fac : bv 32 := 0x00c03733.
Lemma F_a2fac : fetch_word AsanUbsan.M.loaded_segments (0xa2fac : word) = Some W_a2fac.
Proof. vm_refl. Qed.
Lemma D_a2fac : decode_any W_a2fac = Some (Op ALU_SLTU 14 0 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a2fb0 : bv 32 := 0x04068063.
Lemma F_a2fb0 : fetch_word AsanUbsan.M.loaded_segments (0xa2fb0 : word) = Some W_a2fb0.
Proof. vm_refl. Qed.
Lemma D_a2fb0 : decode_any W_a2fb0 = Some (Branch BC_EQ 13 0 64, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a2fb4 : bv 32 := 0x02060e63.
Lemma F_a2fb4 : fetch_word AsanUbsan.M.loaded_segments (0xa2fb4 : word) = Some W_a2fb4.
Proof. vm_refl. Qed.
Lemma D_a2fb4 : decode_any W_a2fb4 = Some (Branch BC_EQ 12 0 60, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a2fb8 : bv 32 := 0x00158793.
Lemma F_a2fb8 : fetch_word AsanUbsan.M.loaded_segments (0xa2fb8 : word) = Some W_a2fb8.
Proof. vm_refl. Qed.
Lemma D_a2fb8 : decode_any W_a2fb8 = Some (OpImm ALU_ADD 15 11 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a2fbc : bv 32 := 0x00100813.
Lemma F_a2fbc : fetch_word AsanUbsan.M.loaded_segments (0xa2fbc : word) = Some W_a2fbc.
Proof. vm_refl. Qed.
Lemma D_a2fbc : decode_any W_a2fbc = Some (OpImm ALU_ADD 16 0 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a2fc0 : bv 32 := 0x0005c703.
Lemma F_a2fc0 : fetch_word AsanUbsan.M.loaded_segments (0xa2fc0 : word) = Some W_a2fc0.
Proof. vm_refl. Qed.
Lemma D_a2fc0 : decode_any W_a2fc0 = Some (Load SZ1 false 14 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a2fc4 : bv 32 := 0x00060693.
Lemma F_a2fc4 : fetch_word AsanUbsan.M.loaded_segments (0xa2fc4 : word) = Some W_a2fc4.
Proof. vm_refl. Qed.
Lemma D_a2fc4 : decode_any W_a2fc4 = Some (OpImm ALU_ADD 13 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a2fc8 : bv 32 := 0x00e40023.
Lemma F_a2fc8 : fetch_word AsanUbsan.M.loaded_segments (0xa2fc8 : word) = Some W_a2fc8.
Proof. vm_refl. Qed.
Lemma D_a2fc8 : decode_any W_a2fc8 = Some (Store SZ1 8 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a2fcc : bv 32 := 0x06070e63.
Lemma F_a2fcc : fetch_word AsanUbsan.M.loaded_segments (0xa2fcc : word) = Some W_a2fcc.
Proof. vm_refl. Qed.
Lemma D_a2fcc : decode_any W_a2fcc = Some (Branch BC_EQ 14 0 124, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a2fd0 : bv 32 := 0xfff68613.
Lemma F_a2fd0 : fetch_word AsanUbsan.M.loaded_segments (0xa2fd0 : word) = Some W_a2fd0.
Proof. vm_refl. Qed.
Lemma D_a2fd0 : decode_any W_a2fd0 = Some (OpImm ALU_ADD 12 13 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a2fd4 : bv 32 := 0x00158593.
Lemma F_a2fd4 : fetch_word AsanUbsan.M.loaded_segments (0xa2fd4 : word) = Some W_a2fd4.
Proof. vm_refl. Qed.
Lemma D_a2fd4 : decode_any W_a2fd4 = Some (OpImm ALU_ADD 11 11 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a2fd8 : bv 32 := 0x00140413.
Lemma F_a2fd8 : fetch_word AsanUbsan.M.loaded_segments (0xa2fd8 : word) = Some W_a2fd8.
Proof. vm_refl. Qed.
Lemma D_a2fd8 : decode_any W_a2fd8 = Some (OpImm ALU_ADD 8 8 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a2fdc : bv 32 := 0x0077f893.
Lemma F_a2fdc : fetch_word AsanUbsan.M.loaded_segments (0xa2fdc : word) = Some W_a2fdc.
Proof. vm_refl. Qed.
Lemma D_a2fdc : decode_any W_a2fdc = Some (OpImm ALU_AND 17 15 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a2fe0 : bv 32 := 0x00c03733.
Lemma F_a2fe0 : fetch_word AsanUbsan.M.loaded_segments (0xa2fe0 : word) = Some W_a2fe0.
Proof. vm_refl. Qed.
Lemma D_a2fe0 : decode_any W_a2fe0 = Some (Op ALU_SLTU 14 0 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a2fe4 : bv 32 := 0x00088663.
Lemma F_a2fe4 : fetch_word AsanUbsan.M.loaded_segments (0xa2fe4 : word) = Some W_a2fe4.
Proof. vm_refl. Qed.
Lemma D_a2fe4 : decode_any W_a2fe4 = Some (Branch BC_EQ 17 0 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a2fe8 : bv 32 := 0x00178793.
Lemma F_a2fe8 : fetch_word AsanUbsan.M.loaded_segments (0xa2fe8 : word) = Some W_a2fe8.
Proof. vm_refl. Qed.
Lemma D_a2fe8 : decode_any W_a2fe8 = Some (OpImm ALU_ADD 15 15 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a2fec : bv 32 := 0xfd069ae3.
Lemma F_a2fec : fetch_word AsanUbsan.M.loaded_segments (0xa2fec : word) = Some W_a2fec.
Proof. vm_refl. Qed.
Lemma D_a2fec : decode_any W_a2fec = Some (Branch BC_NE 13 16 8148, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a2ff0 : bv 32 := 0x04070a63.
Lemma F_a2ff0 : fetch_word AsanUbsan.M.loaded_segments (0xa2ff0 : word) = Some W_a2ff0.
Proof. vm_refl. Qed.
Lemma D_a2ff0 : decode_any W_a2ff0 = Some (Branch BC_EQ 14 0 84, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a2ff4 : bv 32 := 0x0005c683.
Lemma F_a2ff4 : fetch_word AsanUbsan.M.loaded_segments (0xa2ff4 : word) = Some W_a2ff4.
Proof. vm_refl. Qed.
Lemma D_a2ff4 : decode_any W_a2ff4 = Some (Load SZ1 false 13 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a2ff8 : bv 32 := 0x06068a63.
Lemma F_a2ff8 : fetch_word AsanUbsan.M.loaded_segments (0xa2ff8 : word) = Some W_a2ff8.
Proof. vm_refl. Qed.
Lemma D_a2ff8 : decode_any W_a2ff8 = Some (Branch BC_EQ 13 0 116, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a2ffc : bv 32 := 0x00800693.
Lemma F_a2ffc : fetch_word AsanUbsan.M.loaded_segments (0xa2ffc : word) = Some W_a2ffc.
Proof. vm_refl. Qed.
Lemma D_a2ffc : decode_any W_a2ffc = Some (OpImm ALU_ADD 13 0 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a3000 : bv 32 := 0xf8d660e3.
Lemma F_a3000 : fetch_word AsanUbsan.M.loaded_segments (0xa3000 : word) = Some W_a3000.
Proof. vm_refl. Qed.
Lemma D_a3000 : decode_any W_a3000 = Some (Branch BC_LTU 12 13 8064, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a3004 : bv 32 := 0xfff6d697.
Lemma F_a3004 : fetch_word AsanUbsan.M.loaded_segments (0xa3004 : word) = Some W_a3004.
Proof. vm_refl. Qed.
Lemma D_a3004 : decode_any W_a3004 = Some (Auipc 13 1048429, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a3008 : bv 32 := 0xfff6d717.
Lemma F_a3008 : fetch_word AsanUbsan.M.loaded_segments (0xa3008 : word) = Some W_a3008.
Proof. vm_refl. Qed.
Lemma D_a3008 : decode_any W_a3008 = Some (Auipc 14 1048429, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a300c : bv 32 := 0x37c6b683.
Lemma F_a300c : fetch_word AsanUbsan.M.loaded_segments (0xa300c : word) = Some W_a300c.
Proof. vm_refl. Qed.
Lemma D_a300c : decode_any W_a300c = Some (Load SZ8 true 13 13 892, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a3010 : bv 32 := 0x35873703.
Lemma F_a3010 : fetch_word AsanUbsan.M.loaded_segments (0xa3010 : word) = Some W_a3010.
Proof. vm_refl. Qed.
Lemma D_a3010 : decode_any W_a3010 = Some (Load SZ8 true 14 14 856, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a3014 : bv 32 := 0x00700793.
Lemma F_a3014 : fetch_word AsanUbsan.M.loaded_segments (0xa3014 : word) = Some W_a3014.
Proof. vm_refl. Qed.
Lemma D_a3014 : decode_any W_a3014 = Some (OpImm ALU_ADD 15 0 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a3018 : bv 32 := 0x0005b803.
Lemma F_a3018 : fetch_word AsanUbsan.M.loaded_segments (0xa3018 : word) = Some W_a3018.
Proof. vm_refl. Qed.
Lemma D_a3018 : decode_any W_a3018 = Some (Load SZ8 true 16 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a301c : bv 32 := 0x410688b3.
Lemma F_a301c : fetch_word AsanUbsan.M.loaded_segments (0xa301c : word) = Some W_a301c.
Proof. vm_refl. Qed.
Lemma D_a301c : decode_any W_a301c = Some (Op ALU_SUB 17 13 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a3020 : bv 32 := 0x0108e8b3.
Lemma F_a3020 : fetch_word AsanUbsan.M.loaded_segments (0xa3020 : word) = Some W_a3020.
Proof. vm_refl. Qed.
Lemma D_a3020 : decode_any W_a3020 = Some (Op ALU_OR 17 17 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a3024 : bv 32 := 0x00e8f8b3.
Lemma F_a3024 : fetch_word AsanUbsan.M.loaded_segments (0xa3024 : word) = Some W_a3024.
Proof. vm_refl. Qed.
Lemma D_a3024 : decode_any W_a3024 = Some (Op ALU_AND 17 17 14, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a3028 : bv 32 := 0xf4e89ee3.
Lemma F_a3028 : fetch_word AsanUbsan.M.loaded_segments (0xa3028 : word) = Some W_a3028.
Proof. vm_refl. Qed.
Lemma D_a3028 : decode_any W_a3028 = Some (Branch BC_NE 17 14 8028, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a302c : bv 32 := 0x01043023.
Lemma F_a302c : fetch_word AsanUbsan.M.loaded_segments (0xa302c : word) = Some W_a302c.
Proof. vm_refl. Qed.
Lemma D_a302c : decode_any W_a302c = Some (Store SZ8 8 16 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a3030 : bv 32 := 0xff860613.
Lemma F_a3030 : fetch_word AsanUbsan.M.loaded_segments (0xa3030 : word) = Some W_a3030.
Proof. vm_refl. Qed.
Lemma D_a3030 : decode_any W_a3030 = Some (OpImm ALU_ADD 12 12 4088, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a3034 : bv 32 := 0x00858593.
Lemma F_a3034 : fetch_word AsanUbsan.M.loaded_segments (0xa3034 : word) = Some W_a3034.
Proof. vm_refl. Qed.
Lemma D_a3034 : decode_any W_a3034 = Some (OpImm ALU_ADD 11 11 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a3038 : bv 32 := 0x00840413.
Lemma F_a3038 : fetch_word AsanUbsan.M.loaded_segments (0xa3038 : word) = Some W_a3038.
Proof. vm_refl. Qed.
Lemma D_a3038 : decode_any W_a3038 = Some (OpImm ALU_ADD 8 8 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a303c : bv 32 := 0xfcc7eee3.
Lemma F_a303c : fetch_word AsanUbsan.M.loaded_segments (0xa303c : word) = Some W_a303c.
Proof. vm_refl. Qed.
Lemma D_a303c : decode_any W_a303c = Some (Branch BC_LTU 15 12 8156, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a3040 : bv 32 := 0xf41ff06f.
Lemma F_a3040 : fetch_word AsanUbsan.M.loaded_segments (0xa3040 : word) = Some W_a3040.
Proof. vm_refl. Qed.
Lemma D_a3040 : decode_any W_a3040 = Some (Jal 0 2096960, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a3044 : bv 32 := 0x00000693.
Lemma F_a3044 : fetch_word AsanUbsan.M.loaded_segments (0xa3044 : word) = Some W_a3044.
Proof. vm_refl. Qed.
Lemma D_a3044 : decode_any W_a3044 = Some (OpImm ALU_ADD 13 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a3048 : bv 32 := 0x00040513.
Lemma F_a3048 : fetch_word AsanUbsan.M.loaded_segments (0xa3048 : word) = Some W_a3048.
Proof. vm_refl. Qed.
Lemma D_a3048 : decode_any W_a3048 = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a304c : bv 32 := 0x00000593.
Lemma F_a304c : fetch_word AsanUbsan.M.loaded_segments (0xa304c : word) = Some W_a304c.
Proof. vm_refl. Qed.
Lemma D_a304c : decode_any W_a304c = Some (OpImm ALU_ADD 11 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a3050 : bv 32 := 0x00068613.
Lemma F_a3050 : fetch_word AsanUbsan.M.loaded_segments (0xa3050 : word) = Some W_a3050.
Proof. vm_refl. Qed.
Lemma D_a3050 : decode_any W_a3050 = Some (OpImm ALU_ADD 12 13 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a3054 : bv 32 := 0xdc5b00ef.
Lemma F_a3054 : fetch_word AsanUbsan.M.loaded_segments (0xa3054 : word) = Some W_a3054.
Proof. vm_refl. Qed.
Lemma D_a3054 : decode_any W_a3054 = Some (Jal 1 1772996, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a3058 : bv 32 := 0x00040513.
Lemma F_a3058 : fetch_word AsanUbsan.M.loaded_segments (0xa3058 : word) = Some W_a3058.
Proof. vm_refl. Qed.
Lemma D_a3058 : decode_any W_a3058 = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a305c : bv 32 := 0x00813083.
Lemma F_a305c : fetch_word AsanUbsan.M.loaded_segments (0xa305c : word) = Some W_a305c.
Proof. vm_refl. Qed.
Lemma D_a305c : decode_any W_a305c = Some (Load SZ8 true 1 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a3060 : bv 32 := 0x00013403.
Lemma F_a3060 : fetch_word AsanUbsan.M.loaded_segments (0xa3060 : word) = Some W_a3060.
Proof. vm_refl. Qed.
Lemma D_a3060 : decode_any W_a3060 = Some (Load SZ8 true 8 2 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a3064 : bv 32 := 0x01010113.
Lemma F_a3064 : fetch_word AsanUbsan.M.loaded_segments (0xa3064 : word) = Some W_a3064.
Proof. vm_refl. Qed.
Lemma D_a3064 : decode_any W_a3064 = Some (OpImm ALU_ADD 2 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a3068 : bv 32 := 0x00008067.
Lemma F_a3068 : fetch_word AsanUbsan.M.loaded_segments (0xa3068 : word) = Some W_a3068.
Proof. vm_refl. Qed.
Lemma D_a3068 : decode_any W_a3068 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a306c : bv 32 := 0x00060693.
Lemma F_a306c : fetch_word AsanUbsan.M.loaded_segments (0xa306c : word) = Some W_a306c.
Proof. vm_refl. Qed.
Lemma D_a306c : decode_any W_a306c = Some (OpImm ALU_ADD 13 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a3070 : bv 32 := 0xfd9ff06f.
Lemma F_a3070 : fetch_word AsanUbsan.M.loaded_segments (0xa3070 : word) = Some W_a3070.
Proof. vm_refl. Qed.
Lemma D_a3070 : decode_any W_a3070 = Some (Jal 0 2097112, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a3074 : bv 32 := 0xfe010113.
Lemma F_a3074 : fetch_word AsanUbsan.M.loaded_segments (0xa3074 : word) = Some W_a3074.
Proof. vm_refl. Qed.
Lemma D_a3074 : decode_any W_a3074 = Some (OpImm ALU_ADD 2 2 4064, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a3078 : bv 32 := 0x00113c23.
Lemma F_a3078 : fetch_word AsanUbsan.M.loaded_segments (0xa3078 : word) = Some W_a3078.
Proof. vm_refl. Qed.
Lemma D_a3078 : decode_any W_a3078 = Some (Store SZ8 2 1 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a307c : bv 32 := 0x00813823.
Lemma F_a307c : fetch_word AsanUbsan.M.loaded_segments (0xa307c : word) = Some W_a307c.
Proof. vm_refl. Qed.
Lemma D_a307c : decode_any W_a307c = Some (Store SZ8 2 8 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a3080 : bv 32 := 0x00913423.
Lemma F_a3080 : fetch_word AsanUbsan.M.loaded_segments (0xa3080 : word) = Some W_a3080.
Proof. vm_refl. Qed.
Lemma D_a3080 : decode_any W_a3080 = Some (Store SZ8 2 9 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a3084 : bv 32 := 0x00058413.
Lemma F_a3084 : fetch_word AsanUbsan.M.loaded_segments (0xa3084 : word) = Some W_a3084.
Proof. vm_refl. Qed.
Lemma D_a3084 : decode_any W_a3084 = Some (OpImm ALU_ADD 8 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a3088 : bv 32 := 0x00050493.
Lemma F_a3088 : fetch_word AsanUbsan.M.loaded_segments (0xa3088 : word) = Some W_a3088.
Proof. vm_refl. Qed.
Lemma D_a3088 : decode_any W_a3088 = Some (OpImm ALU_ADD 9 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a308c : bv 32 := 0x00000593.
Lemma F_a308c : fetch_word AsanUbsan.M.loaded_segments (0xa308c : word) = Some W_a308c.
Proof. vm_refl. Qed.
Lemma D_a308c : decode_any W_a308c = Some (OpImm ALU_ADD 11 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a3090 : bv 32 := 0x00040613.
Lemma F_a3090 : fetch_word AsanUbsan.M.loaded_segments (0xa3090 : word) = Some W_a3090.
Proof. vm_refl. Qed.
Lemma D_a3090 : decode_any W_a3090 = Some (OpImm ALU_ADD 12 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a3094 : bv 32 := 0x9a4a10ef.
Lemma F_a3094 : fetch_word AsanUbsan.M.loaded_segments (0xa3094 : word) = Some W_a3094.
Proof. vm_refl. Qed.
Lemma D_a3094 : decode_any W_a3094 = Some (Jal 1 1708452, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a3098 : bv 32 := 0x00050463.
Lemma F_a3098 : fetch_word AsanUbsan.M.loaded_segments (0xa3098 : word) = Some W_a3098.
Proof. vm_refl. Qed.
Lemma D_a3098 : decode_any W_a3098 = Some (Branch BC_EQ 10 0 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a309c : bv 32 := 0x40950433.
Lemma F_a309c : fetch_word AsanUbsan.M.loaded_segments (0xa309c : word) = Some W_a309c.
Proof. vm_refl. Qed.
Lemma D_a309c : decode_any W_a309c = Some (Op ALU_SUB 8 10 9, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a30a0 : bv 32 := 0x00040513.
Lemma F_a30a0 : fetch_word AsanUbsan.M.loaded_segments (0xa30a0 : word) = Some W_a30a0.
Proof. vm_refl. Qed.
Lemma D_a30a0 : decode_any W_a30a0 = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a30a4 : bv 32 := 0x01813083.
Lemma F_a30a4 : fetch_word AsanUbsan.M.loaded_segments (0xa30a4 : word) = Some W_a30a4.
Proof. vm_refl. Qed.
Lemma D_a30a4 : decode_any W_a30a4 = Some (Load SZ8 true 1 2 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a30a8 : bv 32 := 0x01013403.
Lemma F_a30a8 : fetch_word AsanUbsan.M.loaded_segments (0xa30a8 : word) = Some W_a30a8.
Proof. vm_refl. Qed.
Lemma D_a30a8 : decode_any W_a30a8 = Some (Load SZ8 true 8 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a30ac : bv 32 := 0x00813483.
Lemma F_a30ac : fetch_word AsanUbsan.M.loaded_segments (0xa30ac : word) = Some W_a30ac.
Proof. vm_refl. Qed.
Lemma D_a30ac : decode_any W_a30ac = Some (Load SZ8 true 9 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a30b0 : bv 32 := 0x02010113.
Lemma F_a30b0 : fetch_word AsanUbsan.M.loaded_segments (0xa30b0 : word) = Some W_a30b0.
Proof. vm_refl. Qed.
Lemma D_a30b0 : decode_any W_a30b0 = Some (OpImm ALU_ADD 2 2 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a30b4 : bv 32 := 0x00008067.
Lemma F_a30b4 : fetch_word AsanUbsan.M.loaded_segments (0xa30b4 : word) = Some W_a30b4.
Proof. vm_refl. Qed.
Lemma D_a30b4 : decode_any W_a30b4 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.
