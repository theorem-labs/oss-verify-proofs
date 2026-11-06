(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib Require Import ImgB.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Abbreviation BSEGS_I := ImgB.M.loaded_segments.
Open Scope bv_scope.

(* [comment removed for export] *)
Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

(* [comment removed for export] *)
Definition W_75b70 : bv 32 := 0x000b5697.
Lemma F_75b70 : fetch_word BSEGS_I (0x75b70 : word) = Some W_75b70.
Proof. vm_refl. Qed.
Lemma D_75b70 : decode_any W_75b70 = Some (Auipc 13 181, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_75b74 : bv 32 := 0x8106b683.
Lemma F_75b74 : fetch_word BSEGS_I (0x75b74 : word) = Some W_75b74.
Proof. vm_refl. Qed.
Lemma D_75b74 : decode_any W_75b74 = Some (Load SZ8 true 13 13 2064, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_75b78 : bv 32 := 0x0006b703.
Lemma F_75b78 : fetch_word BSEGS_I (0x75b78 : word) = Some W_75b78.
Proof. vm_refl. Qed.
Lemma D_75b78 : decode_any W_75b78 = Some (Load SZ8 true 14 13 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_75b7c : bv 32 := 0xfff98993.
Lemma F_75b7c : fetch_word BSEGS_I (0x75b7c : word) = Some W_75b7c.
Proof. vm_refl. Qed.
Lemma D_75b7c : decode_any W_75b7c = Some (OpImm ALU_ADD 19 19 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_75b80 : bv 32 := 0x0035d693.
Lemma F_75b80 : fetch_word BSEGS_I (0x75b80 : word) = Some W_75b80.
Proof. vm_refl. Qed.
Lemma D_75b80 : decode_any W_75b80 = Some (ShiftImm ALU_SRL 13 11 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_75b84 : bv 32 := 0x0039d793.
Lemma F_75b84 : fetch_word BSEGS_I (0x75b84 : word) = Some W_75b84.
Proof. vm_refl. Qed.
Lemma D_75b84 : decode_any W_75b84 = Some (ShiftImm ALU_SRL 15 19 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_75b88 : bv 32 := 0x00d706b3.
Lemma F_75b88 : fetch_word BSEGS_I (0x75b88 : word) = Some W_75b88.
Proof. vm_refl. Qed.
Lemma D_75b88 : decode_any W_75b88 = Some (Op ALU_ADD 13 14 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_75b8c : bv 32 := 0x00f70733.
Lemma F_75b8c : fetch_word BSEGS_I (0x75b8c : word) = Some W_75b8c.
Proof. vm_refl. Qed.
Lemma D_75b8c : decode_any W_75b8c = Some (Op ALU_ADD 14 14 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_75b90 : bv 32 := 0xff86f793.
Lemma F_75b90 : fetch_word BSEGS_I (0x75b90 : word) = Some W_75b90.
Proof. vm_refl. Qed.
Lemma D_75b90 : decode_any W_75b90 = Some (OpImm ALU_AND 15 13 4088, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_75b94 : bv 32 := 0xff877813.
Lemma F_75b94 : fetch_word BSEGS_I (0x75b94 : word) = Some W_75b94.
Proof. vm_refl. Qed.
Lemma D_75b94 : decode_any W_75b94 = Some (OpImm ALU_AND 16 14 4088, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_75b98 : bv 32 := 0x0007b783.
Lemma F_75b98 : fetch_word BSEGS_I (0x75b98 : word) = Some W_75b98.
Proof. vm_refl. Qed.
Lemma D_75b98 : decode_any W_75b98 = Some (Load SZ8 true 15 15 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_75b9c : bv 32 := 0x00083803.
Lemma F_75b9c : fetch_word BSEGS_I (0x75b9c : word) = Some W_75b9c.
Proof. vm_refl. Qed.
Lemma D_75b9c : decode_any W_75b9c = Some (Load SZ8 true 16 16 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_75ba0 : bv 32 := 0x00f867b3.
Lemma F_75ba0 : fetch_word BSEGS_I (0x75ba0 : word) = Some W_75ba0.
Proof. vm_refl. Qed.
Lemma D_75ba0 : decode_any W_75ba0 = Some (Op ALU_OR 15 16 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_75ba4 : bv 32 := 0x2a079e63.
Lemma F_75ba4 : fetch_word BSEGS_I (0x75ba4 : word) = Some W_75ba4.
Proof. vm_refl. Qed.
Lemma D_75ba4 : decode_any W_75ba4 = Some (Branch BC_NE 15 0 700, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_75ba8 : bv 32 := 0xfff54693.
Lemma F_75ba8 : fetch_word BSEGS_I (0x75ba8 : word) = Some W_75ba8.
Proof. vm_refl. Qed.
Lemma D_75ba8 : decode_any W_75ba8 = Some (OpImm ALU_XOR 13 10 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_75bb8 : bv 32 := 0x000b4697.
Lemma F_75bb8 : fetch_word BSEGS_I (0x75bb8 : word) = Some W_75bb8.
Proof. vm_refl. Qed.
Lemma D_75bb8 : decode_any W_75bb8 = Some (Auipc 13 180, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_75bbc : bv 32 := 0x7c86b683.
Lemma F_75bbc : fetch_word BSEGS_I (0x75bbc : word) = Some W_75bbc.
Proof. vm_refl. Qed.
Lemma D_75bbc : decode_any W_75bbc = Some (Load SZ8 true 13 13 1992, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_75bc0 : bv 32 := 0x0006b703.
Lemma F_75bc0 : fetch_word BSEGS_I (0x75bc0 : word) = Some W_75bc0.
Proof. vm_refl. Qed.
Lemma D_75bc0 : decode_any W_75bc0 = Some (Load SZ8 true 14 13 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_75bc4 : bv 32 := 0xfffa0a13.
Lemma F_75bc4 : fetch_word BSEGS_I (0x75bc4 : word) = Some W_75bc4.
Proof. vm_refl. Qed.
Lemma D_75bc4 : decode_any W_75bc4 = Some (OpImm ALU_ADD 20 20 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_75bc8 : bv 32 := 0x00355693.
Lemma F_75bc8 : fetch_word BSEGS_I (0x75bc8 : word) = Some W_75bc8.
Proof. vm_refl. Qed.
Lemma D_75bc8 : decode_any W_75bc8 = Some (ShiftImm ALU_SRL 13 10 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_75bcc : bv 32 := 0x003a5793.
Lemma F_75bcc : fetch_word BSEGS_I (0x75bcc : word) = Some W_75bcc.
Proof. vm_refl. Qed.
Lemma D_75bcc : decode_any W_75bcc = Some (ShiftImm ALU_SRL 15 20 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_75bd0 : bv 32 := 0x00d706b3.
Lemma F_75bd0 : fetch_word BSEGS_I (0x75bd0 : word) = Some W_75bd0.
Proof. vm_refl. Qed.
Lemma D_75bd0 : decode_any W_75bd0 = Some (Op ALU_ADD 13 14 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_75bd4 : bv 32 := 0x00f70733.
Lemma F_75bd4 : fetch_word BSEGS_I (0x75bd4 : word) = Some W_75bd4.
Proof. vm_refl. Qed.
Lemma D_75bd4 : decode_any W_75bd4 = Some (Op ALU_ADD 14 14 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_75bd8 : bv 32 := 0xff86f793.
Lemma F_75bd8 : fetch_word BSEGS_I (0x75bd8 : word) = Some W_75bd8.
Proof. vm_refl. Qed.
Lemma D_75bd8 : decode_any W_75bd8 = Some (OpImm ALU_AND 15 13 4088, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_75bdc : bv 32 := 0xff877813.
Lemma F_75bdc : fetch_word BSEGS_I (0x75bdc : word) = Some W_75bdc.
Proof. vm_refl. Qed.
Lemma D_75bdc : decode_any W_75bdc = Some (OpImm ALU_AND 16 14 4088, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_75be0 : bv 32 := 0x0007b783.
Lemma F_75be0 : fetch_word BSEGS_I (0x75be0 : word) = Some W_75be0.
Proof. vm_refl. Qed.
Lemma D_75be0 : decode_any W_75be0 = Some (Load SZ8 true 15 15 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_75be4 : bv 32 := 0x00083803.
Lemma F_75be4 : fetch_word BSEGS_I (0x75be4 : word) = Some W_75be4.
Proof. vm_refl. Qed.
Lemma D_75be4 : decode_any W_75be4 = Some (Load SZ8 true 16 16 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_75be8 : bv 32 := 0x00f867b3.
Lemma F_75be8 : fetch_word BSEGS_I (0x75be8 : word) = Some W_75be8.
Proof. vm_refl. Qed.
Lemma D_75be8 : decode_any W_75be8 = Some (Op ALU_OR 15 16 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_75bec : bv 32 := 0x36079a63.
Lemma F_75bec : fetch_word BSEGS_I (0x75bec : word) = Some W_75bec.
Proof. vm_refl. Qed.
Lemma D_75bec : decode_any W_75bec = Some (Branch BC_NE 15 0 884, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_75bf0 : bv 32 := 0x000b6697.
Lemma F_75bf0 : fetch_word BSEGS_I (0x75bf0 : word) = Some W_75bf0.
Proof. vm_refl. Qed.
Lemma D_75bf0 : decode_any W_75bf0 = Some (Auipc 13 182, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_75e60 : bv 32 := 0x00070783.
Lemma F_75e60 : fetch_word BSEGS_I (0x75e60 : word) = Some W_75e60.
Proof. vm_refl. Qed.
Lemma D_75e60 : decode_any W_75e60 = Some (Load SZ1 true 15 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_75e64 : bv 32 := 0x0079f813.
Lemma F_75e64 : fetch_word BSEGS_I (0x75e64 : word) = Some W_75e64.
Proof. vm_refl. Qed.
Lemma D_75e64 : decode_any W_75e64 = Some (OpImm ALU_AND 16 19 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_75e68 : bv 32 := 0x00f038b3.
Lemma F_75e68 : fetch_word BSEGS_I (0x75e68 : word) = Some W_75e68.
Proof. vm_refl. Qed.
Lemma D_75e68 : decode_any W_75e68 = Some (Op ALU_SLTU 17 0 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_75e6c : bv 32 := 0x00f827b3.
Lemma F_75e6c : fetch_word BSEGS_I (0x75e6c : word) = Some W_75e6c.
Proof. vm_refl. Qed.
Lemma D_75e6c : decode_any W_75e6c = Some (Op ALU_SLT 15 16 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_75e70 : bv 32 := 0x0017c793.
Lemma F_75e70 : fetch_word BSEGS_I (0x75e70 : word) = Some W_75e70.
Proof. vm_refl. Qed.
Lemma D_75e70 : decode_any W_75e70 = Some (OpImm ALU_XOR 15 15 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_75e74 : bv 32 := 0x00f8f7b3.
Lemma F_75e74 : fetch_word BSEGS_I (0x75e74 : word) = Some W_75e74.
Proof. vm_refl. Qed.
Lemma D_75e74 : decode_any W_75e74 = Some (Op ALU_AND 15 17 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_75e78 : bv 32 := 0x00e6fa63.
Lemma F_75e78 : fetch_word BSEGS_I (0x75e78 : word) = Some W_75e78.
Proof. vm_refl. Qed.
Lemma D_75e78 : decode_any W_75e78 = Some (Branch BC_GEU 13 14 20, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_75e7c : bv 32 := 0x0006c803.
Lemma F_75e7c : fetch_word BSEGS_I (0x75e7c : word) = Some W_75e7c.
Proof. vm_refl. Qed.
Lemma D_75e7c : decode_any W_75e7c = Some (Load SZ1 false 16 13 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_75e80 : bv 32 := 0x00168693.
Lemma F_75e80 : fetch_word BSEGS_I (0x75e80 : word) = Some W_75e80.
Proof. vm_refl. Qed.
Lemma D_75e80 : decode_any W_75e80 = Some (OpImm ALU_ADD 13 13 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_75e84 : bv 32 := 0x00f867b3.
Lemma F_75e84 : fetch_word BSEGS_I (0x75e84 : word) = Some W_75e84.
Proof. vm_refl. Qed.
Lemma D_75e84 : decode_any W_75e84 = Some (Op ALU_OR 15 16 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_75e88 : bv 32 := 0xfee69ae3.
Lemma F_75e88 : fetch_word BSEGS_I (0x75e88 : word) = Some W_75e88.
Proof. vm_refl. Qed.
Lemma D_75e88 : decode_any W_75e88 = Some (Branch BC_NE 13 14 8180, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_75e8c : bv 32 := 0x0ff7f693.
Lemma F_75e8c : fetch_word BSEGS_I (0x75e8c : word) = Some W_75e8c.
Proof. vm_refl. Qed.
Lemma D_75e8c : decode_any W_75e8c = Some (OpImm ALU_AND 13 15 255, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_75e90 : bv 32 := 0xd0068ce3.
Lemma F_75e90 : fetch_word BSEGS_I (0x75e90 : word) = Some W_75e90.
Proof. vm_refl. Qed.
Lemma D_75e90 : decode_any W_75e90 = Some (Branch BC_EQ 13 0 7448, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_75f60 : bv 32 := 0x00070783.
Lemma F_75f60 : fetch_word BSEGS_I (0x75f60 : word) = Some W_75f60.
Proof. vm_refl. Qed.
Lemma D_75f60 : decode_any W_75f60 = Some (Load SZ1 true 15 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_75f64 : bv 32 := 0x007a7813.
Lemma F_75f64 : fetch_word BSEGS_I (0x75f64 : word) = Some W_75f64.
Proof. vm_refl. Qed.
Lemma D_75f64 : decode_any W_75f64 = Some (OpImm ALU_AND 16 20 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_75f68 : bv 32 := 0x00f038b3.
Lemma F_75f68 : fetch_word BSEGS_I (0x75f68 : word) = Some W_75f68.
Proof. vm_refl. Qed.
Lemma D_75f68 : decode_any W_75f68 = Some (Op ALU_SLTU 17 0 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_75f6c : bv 32 := 0x00f827b3.
Lemma F_75f6c : fetch_word BSEGS_I (0x75f6c : word) = Some W_75f6c.
Proof. vm_refl. Qed.
Lemma D_75f6c : decode_any W_75f6c = Some (Op ALU_SLT 15 16 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_75f70 : bv 32 := 0x0017c793.
Lemma F_75f70 : fetch_word BSEGS_I (0x75f70 : word) = Some W_75f70.
Proof. vm_refl. Qed.
Lemma D_75f70 : decode_any W_75f70 = Some (OpImm ALU_XOR 15 15 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_75f74 : bv 32 := 0x00f8f7b3.
Lemma F_75f74 : fetch_word BSEGS_I (0x75f74 : word) = Some W_75f74.
Proof. vm_refl. Qed.
Lemma D_75f74 : decode_any W_75f74 = Some (Op ALU_AND 15 17 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_75f78 : bv 32 := 0x00e6fa63.
Lemma F_75f78 : fetch_word BSEGS_I (0x75f78 : word) = Some W_75f78.
Proof. vm_refl. Qed.
Lemma D_75f78 : decode_any W_75f78 = Some (Branch BC_GEU 13 14 20, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_75f7c : bv 32 := 0x0006c803.
Lemma F_75f7c : fetch_word BSEGS_I (0x75f7c : word) = Some W_75f7c.
Proof. vm_refl. Qed.
Lemma D_75f7c : decode_any W_75f7c = Some (Load SZ1 false 16 13 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_75f80 : bv 32 := 0x00168693.
Lemma F_75f80 : fetch_word BSEGS_I (0x75f80 : word) = Some W_75f80.
Proof. vm_refl. Qed.
Lemma D_75f80 : decode_any W_75f80 = Some (OpImm ALU_ADD 13 13 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_75f84 : bv 32 := 0x00f867b3.
Lemma F_75f84 : fetch_word BSEGS_I (0x75f84 : word) = Some W_75f84.
Proof. vm_refl. Qed.
Lemma D_75f84 : decode_any W_75f84 = Some (Op ALU_OR 15 16 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_75f88 : bv 32 := 0xfee69ae3.
Lemma F_75f88 : fetch_word BSEGS_I (0x75f88 : word) = Some W_75f88.
Proof. vm_refl. Qed.
Lemma D_75f88 : decode_any W_75f88 = Some (Branch BC_NE 13 14 8180, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_75f8c : bv 32 := 0x0ff7f693.
Lemma F_75f8c : fetch_word BSEGS_I (0x75f8c : word) = Some W_75f8c.
Proof. vm_refl. Qed.
Lemma D_75f8c : decode_any W_75f8c = Some (OpImm ALU_AND 13 15 255, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_75f90 : bv 32 := 0xc60680e3.
Lemma F_75f90 : fetch_word BSEGS_I (0x75f90 : word) = Some W_75f90.
Proof. vm_refl. Qed.
Lemma D_75f90 : decode_any W_75f90 = Some (Branch BC_EQ 13 0 7264, 4%Z).
Proof. vm_refl. Qed.
