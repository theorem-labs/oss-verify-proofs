(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.skcms.iccprofile_info.images Require Import AsanUbsan.
Unset Lia Cache. Unset Nia Cache.  (* [comment removed for export] *)
Open Scope bv_scope.

(* [comment removed for export] *)
Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

(* [comment removed for export] *)
Definition W_51aa0 : bv 32 := 0x0004e697.
Lemma F_51aa0 : fetch_word AsanUbsan.M.loaded_segments (0x51aa0 : word) = Some W_51aa0.
Proof. vm_refl. Qed.
Lemma D_51aa0 : decode_any W_51aa0 = Some (Auipc 13 78, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_51aa4 : bv 32 := 0xe806b683.
Lemma F_51aa4 : fetch_word AsanUbsan.M.loaded_segments (0x51aa4 : word) = Some W_51aa4.
Proof. vm_refl. Qed.
Lemma D_51aa4 : decode_any W_51aa4 = Some (Load SZ8 true 13 13 3712, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_51aa8 : bv 32 := 0x0006b703.
Lemma F_51aa8 : fetch_word AsanUbsan.M.loaded_segments (0x51aa8 : word) = Some W_51aa8.
Proof. vm_refl. Qed.
Lemma D_51aa8 : decode_any W_51aa8 = Some (Load SZ8 true 14 13 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_51aac : bv 32 := 0xfff98993.
Lemma F_51aac : fetch_word AsanUbsan.M.loaded_segments (0x51aac : word) = Some W_51aac.
Proof. vm_refl. Qed.
Lemma D_51aac : decode_any W_51aac = Some (OpImm ALU_ADD 19 19 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_51ab0 : bv 32 := 0x0035d693.
Lemma F_51ab0 : fetch_word AsanUbsan.M.loaded_segments (0x51ab0 : word) = Some W_51ab0.
Proof. vm_refl. Qed.
Lemma D_51ab0 : decode_any W_51ab0 = Some (ShiftImm ALU_SRL 13 11 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_51ab4 : bv 32 := 0x0039d793.
Lemma F_51ab4 : fetch_word AsanUbsan.M.loaded_segments (0x51ab4 : word) = Some W_51ab4.
Proof. vm_refl. Qed.
Lemma D_51ab4 : decode_any W_51ab4 = Some (ShiftImm ALU_SRL 15 19 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_51ab8 : bv 32 := 0x00d706b3.
Lemma F_51ab8 : fetch_word AsanUbsan.M.loaded_segments (0x51ab8 : word) = Some W_51ab8.
Proof. vm_refl. Qed.
Lemma D_51ab8 : decode_any W_51ab8 = Some (Op ALU_ADD 13 14 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_51abc : bv 32 := 0x00f70733.
Lemma F_51abc : fetch_word AsanUbsan.M.loaded_segments (0x51abc : word) = Some W_51abc.
Proof. vm_refl. Qed.
Lemma D_51abc : decode_any W_51abc = Some (Op ALU_ADD 14 14 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_51ac0 : bv 32 := 0xff86f793.
Lemma F_51ac0 : fetch_word AsanUbsan.M.loaded_segments (0x51ac0 : word) = Some W_51ac0.
Proof. vm_refl. Qed.
Lemma D_51ac0 : decode_any W_51ac0 = Some (OpImm ALU_AND 15 13 4088, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_51ac4 : bv 32 := 0xff877813.
Lemma F_51ac4 : fetch_word AsanUbsan.M.loaded_segments (0x51ac4 : word) = Some W_51ac4.
Proof. vm_refl. Qed.
Lemma D_51ac4 : decode_any W_51ac4 = Some (OpImm ALU_AND 16 14 4088, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_51ac8 : bv 32 := 0x0007b783.
Lemma F_51ac8 : fetch_word AsanUbsan.M.loaded_segments (0x51ac8 : word) = Some W_51ac8.
Proof. vm_refl. Qed.
Lemma D_51ac8 : decode_any W_51ac8 = Some (Load SZ8 true 15 15 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_51acc : bv 32 := 0x00083803.
Lemma F_51acc : fetch_word AsanUbsan.M.loaded_segments (0x51acc : word) = Some W_51acc.
Proof. vm_refl. Qed.
Lemma D_51acc : decode_any W_51acc = Some (Load SZ8 true 16 16 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_51ad0 : bv 32 := 0x00f867b3.
Lemma F_51ad0 : fetch_word AsanUbsan.M.loaded_segments (0x51ad0 : word) = Some W_51ad0.
Proof. vm_refl. Qed.
Lemma D_51ad0 : decode_any W_51ad0 = Some (Op ALU_OR 15 16 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_51ad4 : bv 32 := 0x2a079e63.
Lemma F_51ad4 : fetch_word AsanUbsan.M.loaded_segments (0x51ad4 : word) = Some W_51ad4.
Proof. vm_refl. Qed.
Lemma D_51ad4 : decode_any W_51ad4 = Some (Branch BC_NE 15 0 700, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_51ad8 : bv 32 := 0xfff54693.
Lemma F_51ad8 : fetch_word AsanUbsan.M.loaded_segments (0x51ad8 : word) = Some W_51ad8.
Proof. vm_refl. Qed.
Lemma D_51ad8 : decode_any W_51ad8 = Some (OpImm ALU_XOR 13 10 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_51adc : bv 32 := 0x0cc6ee63.
Lemma F_51adc : fetch_word AsanUbsan.M.loaded_segments (0x51adc : word) = Some W_51adc.
Proof. vm_refl. Qed.
Lemma D_51adc : decode_any W_51adc = Some (Branch BC_LTU 13 12 220, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_51ae0 : bv 32 := 0xfbf00693.
Lemma F_51ae0 : fetch_word AsanUbsan.M.loaded_segments (0x51ae0 : word) = Some W_51ae0.
Proof. vm_refl. Qed.
Lemma D_51ae0 : decode_any W_51ae0 = Some (OpImm ALU_ADD 13 0 4031, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_51ae4 : bv 32 := 0x1566fc63.
Lemma F_51ae4 : fetch_word AsanUbsan.M.loaded_segments (0x51ae4 : word) = Some W_51ae4.
Proof. vm_refl. Qed.
Lemma D_51ae4 : decode_any W_51ae4 = Some (Branch BC_GEU 13 22 344, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_51ae8 : bv 32 := 0x0004e697.
Lemma F_51ae8 : fetch_word AsanUbsan.M.loaded_segments (0x51ae8 : word) = Some W_51ae8.
Proof. vm_refl. Qed.
Lemma D_51ae8 : decode_any W_51ae8 = Some (Auipc 13 78, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_51aec : bv 32 := 0xe386b683.
Lemma F_51aec : fetch_word AsanUbsan.M.loaded_segments (0x51aec : word) = Some W_51aec.
Proof. vm_refl. Qed.
Lemma D_51aec : decode_any W_51aec = Some (Load SZ8 true 13 13 3640, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_51af0 : bv 32 := 0x0006b703.
Lemma F_51af0 : fetch_word AsanUbsan.M.loaded_segments (0x51af0 : word) = Some W_51af0.
Proof. vm_refl. Qed.
Lemma D_51af0 : decode_any W_51af0 = Some (Load SZ8 true 14 13 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_51af4 : bv 32 := 0xfffa0a13.
Lemma F_51af4 : fetch_word AsanUbsan.M.loaded_segments (0x51af4 : word) = Some W_51af4.
Proof. vm_refl. Qed.
Lemma D_51af4 : decode_any W_51af4 = Some (OpImm ALU_ADD 20 20 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_51af8 : bv 32 := 0x00355693.
Lemma F_51af8 : fetch_word AsanUbsan.M.loaded_segments (0x51af8 : word) = Some W_51af8.
Proof. vm_refl. Qed.
Lemma D_51af8 : decode_any W_51af8 = Some (ShiftImm ALU_SRL 13 10 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_51afc : bv 32 := 0x003a5793.
Lemma F_51afc : fetch_word AsanUbsan.M.loaded_segments (0x51afc : word) = Some W_51afc.
Proof. vm_refl. Qed.
Lemma D_51afc : decode_any W_51afc = Some (ShiftImm ALU_SRL 15 20 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_51b00 : bv 32 := 0x00d706b3.
Lemma F_51b00 : fetch_word AsanUbsan.M.loaded_segments (0x51b00 : word) = Some W_51b00.
Proof. vm_refl. Qed.
Lemma D_51b00 : decode_any W_51b00 = Some (Op ALU_ADD 13 14 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_51b04 : bv 32 := 0x00f70733.
Lemma F_51b04 : fetch_word AsanUbsan.M.loaded_segments (0x51b04 : word) = Some W_51b04.
Proof. vm_refl. Qed.
Lemma D_51b04 : decode_any W_51b04 = Some (Op ALU_ADD 14 14 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_51b08 : bv 32 := 0xff86f793.
Lemma F_51b08 : fetch_word AsanUbsan.M.loaded_segments (0x51b08 : word) = Some W_51b08.
Proof. vm_refl. Qed.
Lemma D_51b08 : decode_any W_51b08 = Some (OpImm ALU_AND 15 13 4088, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_51b0c : bv 32 := 0xff877813.
Lemma F_51b0c : fetch_word AsanUbsan.M.loaded_segments (0x51b0c : word) = Some W_51b0c.
Proof. vm_refl. Qed.
Lemma D_51b0c : decode_any W_51b0c = Some (OpImm ALU_AND 16 14 4088, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_51b10 : bv 32 := 0x0007b783.
Lemma F_51b10 : fetch_word AsanUbsan.M.loaded_segments (0x51b10 : word) = Some W_51b10.
Proof. vm_refl. Qed.
Lemma D_51b10 : decode_any W_51b10 = Some (Load SZ8 true 15 15 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_51b14 : bv 32 := 0x00083803.
Lemma F_51b14 : fetch_word AsanUbsan.M.loaded_segments (0x51b14 : word) = Some W_51b14.
Proof. vm_refl. Qed.
Lemma D_51b14 : decode_any W_51b14 = Some (Load SZ8 true 16 16 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_51b18 : bv 32 := 0x00f867b3.
Lemma F_51b18 : fetch_word AsanUbsan.M.loaded_segments (0x51b18 : word) = Some W_51b18.
Proof. vm_refl. Qed.
Lemma D_51b18 : decode_any W_51b18 = Some (Op ALU_OR 15 16 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_51b1c : bv 32 := 0x36079a63.
Lemma F_51b1c : fetch_word AsanUbsan.M.loaded_segments (0x51b1c : word) = Some W_51b1c.
Proof. vm_refl. Qed.
Lemma D_51b1c : decode_any W_51b1c = Some (Branch BC_NE 15 0 884, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_51b20 : bv 32 := 0x00050697.
Lemma F_51b20 : fetch_word AsanUbsan.M.loaded_segments (0x51b20 : word) = Some W_51b20.
Proof. vm_refl. Qed.
Lemma D_51b20 : decode_any W_51b20 = Some (Auipc 13 80, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_51b24 : bv 32 := 0xc586b683.
Lemma F_51b24 : fetch_word AsanUbsan.M.loaded_segments (0x51b24 : word) = Some W_51b24.
Proof. vm_refl. Qed.
Lemma D_51b24 : decode_any W_51b24 = Some (Load SZ8 true 13 13 3160, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_51b28 : bv 32 := 0x000680e7.
Lemma F_51b28 : fetch_word AsanUbsan.M.loaded_segments (0x51b28 : word) = Some W_51b28.
Proof. vm_refl. Qed.
Lemma D_51b28 : decode_any W_51b28 = Some (Jalr 1 13 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_51b2c : bv 32 := 0x08010113.
Lemma F_51b2c : fetch_word AsanUbsan.M.loaded_segments (0x51b2c : word) = Some W_51b2c.
Proof. vm_refl. Qed.
Lemma D_51b2c : decode_any W_51b2c = Some (OpImm ALU_ADD 2 2 128, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_51b30 : bv 32 := 0x7e813083.
Lemma F_51b30 : fetch_word AsanUbsan.M.loaded_segments (0x51b30 : word) = Some W_51b30.
Proof. vm_refl. Qed.
Lemma D_51b30 : decode_any W_51b30 = Some (Load SZ8 true 1 2 2024, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_51b34 : bv 32 := 0x7e013403.
Lemma F_51b34 : fetch_word AsanUbsan.M.loaded_segments (0x51b34 : word) = Some W_51b34.
Proof. vm_refl. Qed.
Lemma D_51b34 : decode_any W_51b34 = Some (Load SZ8 true 8 2 2016, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_51b38 : bv 32 := 0x7d813483.
Lemma F_51b38 : fetch_word AsanUbsan.M.loaded_segments (0x51b38 : word) = Some W_51b38.
Proof. vm_refl. Qed.
Lemma D_51b38 : decode_any W_51b38 = Some (Load SZ8 true 9 2 2008, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_51b3c : bv 32 := 0x7d013903.
Lemma F_51b3c : fetch_word AsanUbsan.M.loaded_segments (0x51b3c : word) = Some W_51b3c.
Proof. vm_refl. Qed.
Lemma D_51b3c : decode_any W_51b3c = Some (Load SZ8 true 18 2 2000, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_51b40 : bv 32 := 0x7c813983.
Lemma F_51b40 : fetch_word AsanUbsan.M.loaded_segments (0x51b40 : word) = Some W_51b40.
Proof. vm_refl. Qed.
Lemma D_51b40 : decode_any W_51b40 = Some (Load SZ8 true 19 2 1992, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_51b44 : bv 32 := 0x7c013a03.
Lemma F_51b44 : fetch_word AsanUbsan.M.loaded_segments (0x51b44 : word) = Some W_51b44.
Proof. vm_refl. Qed.
Lemma D_51b44 : decode_any W_51b44 = Some (Load SZ8 true 20 2 1984, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_51b48 : bv 32 := 0x7b813a83.
Lemma F_51b48 : fetch_word AsanUbsan.M.loaded_segments (0x51b48 : word) = Some W_51b48.
Proof. vm_refl. Qed.
Lemma D_51b48 : decode_any W_51b48 = Some (Load SZ8 true 21 2 1976, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_51b4c : bv 32 := 0x7b013b03.
Lemma F_51b4c : fetch_word AsanUbsan.M.loaded_segments (0x51b4c : word) = Some W_51b4c.
Proof. vm_refl. Qed.
Lemma D_51b4c : decode_any W_51b4c = Some (Load SZ8 true 22 2 1968, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_51b50 : bv 32 := 0x7a813b83.
Lemma F_51b50 : fetch_word AsanUbsan.M.loaded_segments (0x51b50 : word) = Some W_51b50.
Proof. vm_refl. Qed.
Lemma D_51b50 : decode_any W_51b50 = Some (Load SZ8 true 23 2 1960, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_51b54 : bv 32 := 0x7a013c03.
Lemma F_51b54 : fetch_word AsanUbsan.M.loaded_segments (0x51b54 : word) = Some W_51b54.
Proof. vm_refl. Qed.
Lemma D_51b54 : decode_any W_51b54 = Some (Load SZ8 true 24 2 1952, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_51b58 : bv 32 := 0x7f010113.
Lemma F_51b58 : fetch_word AsanUbsan.M.loaded_segments (0x51b58 : word) = Some W_51b58.
Proof. vm_refl. Qed.
Lemma D_51b58 : decode_any W_51b58 = Some (OpImm ALU_ADD 2 2 2032, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_51b5c : bv 32 := 0x00008067.
Lemma F_51b5c : fetch_word AsanUbsan.M.loaded_segments (0x51b5c : word) = Some W_51b5c.
Proof. vm_refl. Qed.
Lemma D_51b5c : decode_any W_51b5c = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_51b60 : bv 32 := 0x00060913.
Lemma F_51b60 : fetch_word AsanUbsan.M.loaded_segments (0x51b60 : word) = Some W_51b60.
Proof. vm_refl. Qed.
Lemma D_51b60 : decode_any W_51b60 = Some (OpImm ALU_ADD 18 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_51b64 : bv 32 := 0x00058993.
Lemma F_51b64 : fetch_word AsanUbsan.M.loaded_segments (0x51b64 : word) = Some W_51b64.
Proof. vm_refl. Qed.
Lemma D_51b64 : decode_any W_51b64 = Some (OpImm ALU_ADD 19 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_51b68 : bv 32 := 0x00050493.
Lemma F_51b68 : fetch_word AsanUbsan.M.loaded_segments (0x51b68 : word) = Some W_51b68.
Proof. vm_refl. Qed.
Lemma D_51b68 : decode_any W_51b68 = Some (OpImm ALU_ADD 9 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_51b6c : bv 32 := 0x5f4060ef.
Lemma F_51b6c : fetch_word AsanUbsan.M.loaded_segments (0x51b6c : word) = Some W_51b6c.
Proof. vm_refl. Qed.
Lemma D_51b6c : decode_any W_51b6c = Some (Jal 1 26100, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_51b70 : bv 32 := 0x00098593.
Lemma F_51b70 : fetch_word AsanUbsan.M.loaded_segments (0x51b70 : word) = Some W_51b70.
Proof. vm_refl. Qed.
Lemma D_51b70 : decode_any W_51b70 = Some (OpImm ALU_ADD 11 19 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_51b74 : bv 32 := 0x00090613.
Lemma F_51b74 : fetch_word AsanUbsan.M.loaded_segments (0x51b74 : word) = Some W_51b74.
Proof. vm_refl. Qed.
Lemma D_51b74 : decode_any W_51b74 = Some (OpImm ALU_ADD 12 18 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_51b78 : bv 32 := 0x00050693.
Lemma F_51b78 : fetch_word AsanUbsan.M.loaded_segments (0x51b78 : word) = Some W_51b78.
Proof. vm_refl. Qed.
Lemma D_51b78 : decode_any W_51b78 = Some (OpImm ALU_ADD 13 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_51b7c : bv 32 := 0x00048513.
Lemma F_51b7c : fetch_word AsanUbsan.M.loaded_segments (0x51b7c : word) = Some W_51b7c.
Proof. vm_refl. Qed.
Lemma D_51b7c : decode_any W_51b7c = Some (OpImm ALU_ADD 10 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_51b80 : bv 32 := 0xfa0690e3.
Lemma F_51b80 : fetch_word AsanUbsan.M.loaded_segments (0x51b80 : word) = Some W_51b80.
Proof. vm_refl. Qed.
Lemma D_51b80 : decode_any W_51b80 = Some (Branch BC_NE 13 0 8096, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_51b84 : bv 32 := 0x08010113.
Lemma F_51b84 : fetch_word AsanUbsan.M.loaded_segments (0x51b84 : word) = Some W_51b84.
Proof. vm_refl. Qed.
Lemma D_51b84 : decode_any W_51b84 = Some (OpImm ALU_ADD 2 2 128, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_51b88 : bv 32 := 0x7e813083.
Lemma F_51b88 : fetch_word AsanUbsan.M.loaded_segments (0x51b88 : word) = Some W_51b88.
Proof. vm_refl. Qed.
Lemma D_51b88 : decode_any W_51b88 = Some (Load SZ8 true 1 2 2024, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_51b8c : bv 32 := 0x7e013403.
Lemma F_51b8c : fetch_word AsanUbsan.M.loaded_segments (0x51b8c : word) = Some W_51b8c.
Proof. vm_refl. Qed.
Lemma D_51b8c : decode_any W_51b8c = Some (Load SZ8 true 8 2 2016, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_51b90 : bv 32 := 0x7d813483.
Lemma F_51b90 : fetch_word AsanUbsan.M.loaded_segments (0x51b90 : word) = Some W_51b90.
Proof. vm_refl. Qed.
Lemma D_51b90 : decode_any W_51b90 = Some (Load SZ8 true 9 2 2008, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_51b94 : bv 32 := 0x7d013903.
Lemma F_51b94 : fetch_word AsanUbsan.M.loaded_segments (0x51b94 : word) = Some W_51b94.
Proof. vm_refl. Qed.
Lemma D_51b94 : decode_any W_51b94 = Some (Load SZ8 true 18 2 2000, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_51b98 : bv 32 := 0x7c813983.
Lemma F_51b98 : fetch_word AsanUbsan.M.loaded_segments (0x51b98 : word) = Some W_51b98.
Proof. vm_refl. Qed.
Lemma D_51b98 : decode_any W_51b98 = Some (Load SZ8 true 19 2 1992, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_51b9c : bv 32 := 0x7c013a03.
Lemma F_51b9c : fetch_word AsanUbsan.M.loaded_segments (0x51b9c : word) = Some W_51b9c.
Proof. vm_refl. Qed.
Lemma D_51b9c : decode_any W_51b9c = Some (Load SZ8 true 20 2 1984, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_51ba0 : bv 32 := 0x7b813a83.
Lemma F_51ba0 : fetch_word AsanUbsan.M.loaded_segments (0x51ba0 : word) = Some W_51ba0.
Proof. vm_refl. Qed.
Lemma D_51ba0 : decode_any W_51ba0 = Some (Load SZ8 true 21 2 1976, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_51ba4 : bv 32 := 0x7b013b03.
Lemma F_51ba4 : fetch_word AsanUbsan.M.loaded_segments (0x51ba4 : word) = Some W_51ba4.
Proof. vm_refl. Qed.
Lemma D_51ba4 : decode_any W_51ba4 = Some (Load SZ8 true 22 2 1968, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_51ba8 : bv 32 := 0x7a813b83.
Lemma F_51ba8 : fetch_word AsanUbsan.M.loaded_segments (0x51ba8 : word) = Some W_51ba8.
Proof. vm_refl. Qed.
Lemma D_51ba8 : decode_any W_51ba8 = Some (Load SZ8 true 23 2 1960, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_51bac : bv 32 := 0x7a013c03.
Lemma F_51bac : fetch_word AsanUbsan.M.loaded_segments (0x51bac : word) = Some W_51bac.
Proof. vm_refl. Qed.
Lemma D_51bac : decode_any W_51bac = Some (Load SZ8 true 24 2 1952, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_51bb0 : bv 32 := 0x7f010113.
Lemma F_51bb0 : fetch_word AsanUbsan.M.loaded_segments (0x51bb0 : word) = Some W_51bb0.
Proof. vm_refl. Qed.
Lemma D_51bb0 : decode_any W_51bb0 = Some (OpImm ALU_ADD 2 2 2032, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_51bb4 : bv 32 := 0x7bc1106f.
Lemma F_51bb4 : fetch_word AsanUbsan.M.loaded_segments (0x51bb4 : word) = Some W_51bb4.
Proof. vm_refl. Qed.
Lemma D_51bb4 : decode_any W_51bb4 = Some (Jal 0 71612, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_51bb8 : bv 32 := 0x80040693.
Lemma F_51bb8 : fetch_word AsanUbsan.M.loaded_segments (0x51bb8 : word) = Some W_51bb8.
Proof. vm_refl. Qed.
Lemma D_51bb8 : decode_any W_51bb8 = Some (OpImm ALU_ADD 13 8 2048, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_51bbc : bv 32 := 0xfa868693.
Lemma F_51bbc : fetch_word AsanUbsan.M.loaded_segments (0x51bbc : word) = Some W_51bbc.
Proof. vm_refl. Qed.
Lemma D_51bbc : decode_any W_51bbc = Some (OpImm ALU_ADD 13 13 4008, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_51bc0 : bv 32 := 0x80040713.
Lemma F_51bc0 : fetch_word AsanUbsan.M.loaded_segments (0x51bc0 : word) = Some W_51bc0.
Proof. vm_refl. Qed.
Lemma D_51bc0 : decode_any W_51bc0 = Some (OpImm ALU_ADD 14 8 2048, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_51bc4 : bv 32 := 0xf9870713.
Lemma F_51bc4 : fetch_word AsanUbsan.M.loaded_segments (0x51bc4 : word) = Some W_51bc4.
Proof. vm_refl. Qed.
Lemma D_51bc4 : decode_any W_51bc4 = Some (OpImm ALU_ADD 14 14 3992, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_51bc8 : bv 32 := 0x7ff70b93.
Lemma F_51bc8 : fetch_word AsanUbsan.M.loaded_segments (0x51bc8 : word) = Some W_51bc8.
Proof. vm_refl. Qed.
Lemma D_51bc8 : decode_any W_51bc8 = Some (OpImm ALU_ADD 23 14 2047, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_51bcc : bv 32 := 0x000bb4a3.
Lemma F_51bcc : fetch_word AsanUbsan.M.loaded_segments (0x51bcc : word) = Some W_51bcc.
Proof. vm_refl. Qed.
Lemma D_51bcc : decode_any W_51bcc = Some (Store SZ8 23 0 9, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_51bd0 : bv 32 := 0x00dab023.
Lemma F_51bd0 : fetch_word AsanUbsan.M.loaded_segments (0x51bd0 : word) = Some W_51bd0.
Proof. vm_refl. Qed.
Lemma D_51bd0 : decode_any W_51bd0 = Some (Store SZ8 21 13 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_51bd4 : bv 32 := 0x000ab423.
Lemma F_51bd4 : fetch_word AsanUbsan.M.loaded_segments (0x51bd4 : word) = Some W_51bd4.
Proof. vm_refl. Qed.
Lemma D_51bd4 : decode_any W_51bd4 = Some (Store SZ8 21 0 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_51bd8 : bv 32 := 0x00060493.
Lemma F_51bd8 : fetch_word AsanUbsan.M.loaded_segments (0x51bd8 : word) = Some W_51bd8.
Proof. vm_refl. Qed.
Lemma D_51bd8 : decode_any W_51bd8 = Some (OpImm ALU_ADD 9 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_51bdc : bv 32 := 0x00058993.
Lemma F_51bdc : fetch_word AsanUbsan.M.loaded_segments (0x51bdc : word) = Some W_51bdc.
Proof. vm_refl. Qed.
Lemma D_51bdc : decode_any W_51bdc = Some (OpImm ALU_ADD 19 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_51be0 : bv 32 := 0x00050913.
Lemma F_51be0 : fetch_word AsanUbsan.M.loaded_segments (0x51be0 : word) = Some W_51be0.
Proof. vm_refl. Qed.
Lemma D_51be0 : decode_any W_51be0 = Some (OpImm ALU_ADD 18 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_51be4 : bv 32 := 0x4d5200ef.
Lemma F_51be4 : fetch_word AsanUbsan.M.loaded_segments (0x51be4 : word) = Some W_51be4.
Proof. vm_refl. Qed.
Lemma D_51be4 : decode_any W_51be4 = Some (Jal 1 134356, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_51be8 : bv 32 := 0x00050593.
Lemma F_51be8 : fetch_word AsanUbsan.M.loaded_segments (0x51be8 : word) = Some W_51be8.
Proof. vm_refl. Qed.
Lemma D_51be8 : decode_any W_51be8 = Some (OpImm ALU_ADD 11 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_51bec : bv 32 := 0x0004e517.
Lemma F_51bec : fetch_word AsanUbsan.M.loaded_segments (0x51bec : word) = Some W_51bec.
Proof. vm_refl. Qed.
Lemma D_51bec : decode_any W_51bec = Some (Auipc 10 78, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_51bf0 : bv 32 := 0xd2453503.
Lemma F_51bf0 : fetch_word AsanUbsan.M.loaded_segments (0x51bf0 : word) = Some W_51bf0.
Proof. vm_refl. Qed.
Lemma D_51bf0 : decode_any W_51bf0 = Some (Load SZ8 true 10 10 3364, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_51bf4 : bv 32 := 0x02154703.
Lemma F_51bf4 : fetch_word AsanUbsan.M.loaded_segments (0x51bf4 : word) = Some W_51bf4.
Proof. vm_refl. Qed.
Lemma D_51bf4 : decode_any W_51bf4 = Some (Load SZ1 false 14 10 33, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_51bf8 : bv 32 := 0x008bb4a3.
Lemma F_51bf8 : fetch_word AsanUbsan.M.loaded_segments (0x51bf8 : word) = Some W_51bf8.
Proof. vm_refl. Qed.
Lemma D_51bf8 : decode_any W_51bf8 = Some (Store SZ8 23 8 9, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_51bfc : bv 32 := 0x80040513.
Lemma F_51bfc : fetch_word AsanUbsan.M.loaded_segments (0x51bfc : word) = Some W_51bfc.
Proof. vm_refl. Qed.
Lemma D_51bfc : decode_any W_51bfc = Some (OpImm ALU_ADD 10 8 2048, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_51c00 : bv 32 := 0xf9850513.
Lemma F_51c00 : fetch_word AsanUbsan.M.loaded_segments (0x51c00 : word) = Some W_51c00.
Proof. vm_refl. Qed.
Lemma D_51c00 : decode_any W_51c00 = Some (OpImm ALU_ADD 10 10 3992, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_51c04 : bv 32 := 0x0ff00793.
Lemma F_51c04 : fetch_word AsanUbsan.M.loaded_segments (0x51c04 : word) = Some W_51c04.
Proof. vm_refl. Qed.
Lemma D_51c04 : decode_any W_51c04 = Some (OpImm ALU_ADD 15 0 255, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_51c08 : bv 32 := 0x00040613.
Lemma F_51c08 : fetch_word AsanUbsan.M.loaded_segments (0x51c08 : word) = Some W_51c08.
Proof. vm_refl. Qed.
Lemma D_51c08 : decode_any W_51c08 = Some (OpImm ALU_ADD 12 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_51c0c : bv 32 := 0x00000693.
Lemma F_51c0c : fetch_word AsanUbsan.M.loaded_segments (0x51c0c : word) = Some W_51c0c.
Proof. vm_refl. Qed.
Lemma D_51c0c : decode_any W_51c0c = Some (OpImm ALU_ADD 13 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_51c10 : bv 32 := 0x1f8080ef.
Lemma F_51c10 : fetch_word AsanUbsan.M.loaded_segments (0x51c10 : word) = Some W_51c10.
Proof. vm_refl. Qed.
Lemma D_51c10 : decode_any W_51c10 = Some (Jal 1 33272, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_51c14 : bv 32 := 0x80040613.
Lemma F_51c14 : fetch_word AsanUbsan.M.loaded_segments (0x51c14 : word) = Some W_51c14.
Proof. vm_refl. Qed.
Lemma D_51c14 : decode_any W_51c14 = Some (OpImm ALU_ADD 12 8 2048, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_51c18 : bv 32 := 0xf9860613.
Lemma F_51c18 : fetch_word AsanUbsan.M.loaded_segments (0x51c18 : word) = Some W_51c18.
Proof. vm_refl. Qed.
Lemma D_51c18 : decode_any W_51c18 = Some (OpImm ALU_ADD 12 12 3992, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_51c1c : bv 32 := 0x00090513.
Lemma F_51c1c : fetch_word AsanUbsan.M.loaded_segments (0x51c1c : word) = Some W_51c1c.
Proof. vm_refl. Qed.
Lemma D_51c1c : decode_any W_51c1c = Some (OpImm ALU_ADD 10 18 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_51c20 : bv 32 := 0x00048593.
Lemma F_51c20 : fetch_word AsanUbsan.M.loaded_segments (0x51c20 : word) = Some W_51c20.
Proof. vm_refl. Qed.
Lemma D_51c20 : decode_any W_51c20 = Some (OpImm ALU_ADD 11 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_51c24 : bv 32 := 0x79d040ef.
Lemma F_51c24 : fetch_word AsanUbsan.M.loaded_segments (0x51c24 : word) = Some W_51c24.
Proof. vm_refl. Qed.
Lemma D_51c24 : decode_any W_51c24 = Some (Jal 1 20380, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_51c28 : bv 32 := 0x00090513.
Lemma F_51c28 : fetch_word AsanUbsan.M.loaded_segments (0x51c28 : word) = Some W_51c28.
Proof. vm_refl. Qed.
Lemma D_51c28 : decode_any W_51c28 = Some (OpImm ALU_ADD 10 18 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_51c2c : bv 32 := 0x00098593.
Lemma F_51c2c : fetch_word AsanUbsan.M.loaded_segments (0x51c2c : word) = Some W_51c2c.
Proof. vm_refl. Qed.
Lemma D_51c2c : decode_any W_51c2c = Some (OpImm ALU_ADD 11 19 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_51c30 : bv 32 := 0x00048613.
Lemma F_51c30 : fetch_word AsanUbsan.M.loaded_segments (0x51c30 : word) = Some W_51c30.
Proof. vm_refl. Qed.
Lemma D_51c30 : decode_any W_51c30 = Some (OpImm ALU_ADD 12 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_51c34 : bv 32 := 0xfbf00693.
Lemma F_51c34 : fetch_word AsanUbsan.M.loaded_segments (0x51c34 : word) = Some W_51c34.
Proof. vm_refl. Qed.
Lemma D_51c34 : decode_any W_51c34 = Some (OpImm ALU_ADD 13 0 4031, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_51c38 : bv 32 := 0xeb66e8e3.
Lemma F_51c38 : fetch_word AsanUbsan.M.loaded_segments (0x51c38 : word) = Some W_51c38.
Proof. vm_refl. Qed.
Lemma D_51c38 : decode_any W_51c38 = Some (Branch BC_LTU 13 22 7856, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_51c3c : bv 32 := 0x28061463.
Lemma F_51c3c : fetch_word AsanUbsan.M.loaded_segments (0x51c3c : word) = Some W_51c3c.
Proof. vm_refl. Qed.
Lemma D_51c3c : decode_any W_51c3c = Some (Branch BC_NE 12 0 648, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_51c40 : bv 32 := 0xee1ff06f.
Lemma F_51c40 : fetch_word AsanUbsan.M.loaded_segments (0x51c40 : word) = Some W_51c40.
Proof. vm_refl. Qed.
Lemma D_51c40 : decode_any W_51c40 = Some (Jal 0 2096864, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_51c44 : bv 32 := 0x00050493.
Lemma F_51c44 : fetch_word AsanUbsan.M.loaded_segments (0x51c44 : word) = Some W_51c44.
Proof. vm_refl. Qed.
Lemma D_51c44 : decode_any W_51c44 = Some (OpImm ALU_ADD 9 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_51c48 : bv 32 := 0x00058913.
Lemma F_51c48 : fetch_word AsanUbsan.M.loaded_segments (0x51c48 : word) = Some W_51c48.
Proof. vm_refl. Qed.
Lemma D_51c48 : decode_any W_51c48 = Some (OpImm ALU_ADD 18 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_51c4c : bv 32 := 0x00060b13.
Lemma F_51c4c : fetch_word AsanUbsan.M.loaded_segments (0x51c4c : word) = Some W_51c4c.
Proof. vm_refl. Qed.
Lemma D_51c4c : decode_any W_51c4c = Some (OpImm ALU_ADD 22 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_51c50 : bv 32 := 0x80040513.
Lemma F_51c50 : fetch_word AsanUbsan.M.loaded_segments (0x51c50 : word) = Some W_51c50.
Proof. vm_refl. Qed.
Lemma D_51c50 : decode_any W_51c50 = Some (OpImm ALU_ADD 10 8 2048, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_51c54 : bv 32 := 0xfa850513.
Lemma F_51c54 : fetch_word AsanUbsan.M.loaded_segments (0x51c54 : word) = Some W_51c54.
Proof. vm_refl. Qed.
Lemma D_51c54 : decode_any W_51c54 = Some (OpImm ALU_ADD 10 10 4008, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_51c58 : bv 32 := 0x80040593.
Lemma F_51c58 : fetch_word AsanUbsan.M.loaded_segments (0x51c58 : word) = Some W_51c58.
Proof. vm_refl. Qed.
Lemma D_51c58 : decode_any W_51c58 = Some (OpImm ALU_ADD 11 8 2048, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_51c5c : bv 32 := 0xf9858593.
Lemma F_51c5c : fetch_word AsanUbsan.M.loaded_segments (0x51c5c : word) = Some W_51c5c.
Proof. vm_refl. Qed.
Lemma D_51c5c : decode_any W_51c5c = Some (OpImm ALU_ADD 11 11 3992, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_51c60 : bv 32 := 0x7ff58b93.
Lemma F_51c60 : fetch_word AsanUbsan.M.loaded_segments (0x51c60 : word) = Some W_51c60.
Proof. vm_refl. Qed.
Lemma D_51c60 : decode_any W_51c60 = Some (OpImm ALU_ADD 23 11 2047, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_51c64 : bv 32 := 0x000bb4a3.
Lemma F_51c64 : fetch_word AsanUbsan.M.loaded_segments (0x51c64 : word) = Some W_51c64.
Proof. vm_refl. Qed.
Lemma D_51c64 : decode_any W_51c64 = Some (Store SZ8 23 0 9, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_51c68 : bv 32 := 0x00aab023.
Lemma F_51c68 : fetch_word AsanUbsan.M.loaded_segments (0x51c68 : word) = Some W_51c68.
Proof. vm_refl. Qed.
Lemma D_51c68 : decode_any W_51c68 = Some (Store SZ8 21 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_51c6c : bv 32 := 0x000ab423.
Lemma F_51c6c : fetch_word AsanUbsan.M.loaded_segments (0x51c6c : word) = Some W_51c6c.
Proof. vm_refl. Qed.
Lemma D_51c6c : decode_any W_51c6c = Some (Store SZ8 21 0 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_51c70 : bv 32 := 0x449200ef.
Lemma F_51c70 : fetch_word AsanUbsan.M.loaded_segments (0x51c70 : word) = Some W_51c70.
Proof. vm_refl. Qed.
Lemma D_51c70 : decode_any W_51c70 = Some (Jal 1 134216, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_51c74 : bv 32 := 0x00050593.
Lemma F_51c74 : fetch_word AsanUbsan.M.loaded_segments (0x51c74 : word) = Some W_51c74.
Proof. vm_refl. Qed.
Lemma D_51c74 : decode_any W_51c74 = Some (OpImm ALU_ADD 11 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_51c78 : bv 32 := 0x0004e517.
Lemma F_51c78 : fetch_word AsanUbsan.M.loaded_segments (0x51c78 : word) = Some W_51c78.
Proof. vm_refl. Qed.
Lemma D_51c78 : decode_any W_51c78 = Some (Auipc 10 78, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_51c7c : bv 32 := 0xc9853503.
Lemma F_51c7c : fetch_word AsanUbsan.M.loaded_segments (0x51c7c : word) = Some W_51c7c.
Proof. vm_refl. Qed.
Lemma D_51c7c : decode_any W_51c7c = Some (Load SZ8 true 10 10 3224, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_51c80 : bv 32 := 0x02154703.
Lemma F_51c80 : fetch_word AsanUbsan.M.loaded_segments (0x51c80 : word) = Some W_51c80.
Proof. vm_refl. Qed.
Lemma D_51c80 : decode_any W_51c80 = Some (Load SZ1 false 14 10 33, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_51c84 : bv 32 := 0x008bb4a3.
Lemma F_51c84 : fetch_word AsanUbsan.M.loaded_segments (0x51c84 : word) = Some W_51c84.
Proof. vm_refl. Qed.
Lemma D_51c84 : decode_any W_51c84 = Some (Store SZ8 23 8 9, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_51c88 : bv 32 := 0x80040513.
Lemma F_51c88 : fetch_word AsanUbsan.M.loaded_segments (0x51c88 : word) = Some W_51c88.
Proof. vm_refl. Qed.
Lemma D_51c88 : decode_any W_51c88 = Some (OpImm ALU_ADD 10 8 2048, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_51c8c : bv 32 := 0xf9850513.
Lemma F_51c8c : fetch_word AsanUbsan.M.loaded_segments (0x51c8c : word) = Some W_51c8c.
Proof. vm_refl. Qed.
Lemma D_51c8c : decode_any W_51c8c = Some (OpImm ALU_ADD 10 10 3992, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_51c90 : bv 32 := 0x0ff00793.
Lemma F_51c90 : fetch_word AsanUbsan.M.loaded_segments (0x51c90 : word) = Some W_51c90.
Proof. vm_refl. Qed.
Lemma D_51c90 : decode_any W_51c90 = Some (OpImm ALU_ADD 15 0 255, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_51c94 : bv 32 := 0x00040613.
Lemma F_51c94 : fetch_word AsanUbsan.M.loaded_segments (0x51c94 : word) = Some W_51c94.
Proof. vm_refl. Qed.
Lemma D_51c94 : decode_any W_51c94 = Some (OpImm ALU_ADD 12 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_51c98 : bv 32 := 0x00000693.
Lemma F_51c98 : fetch_word AsanUbsan.M.loaded_segments (0x51c98 : word) = Some W_51c98.
Proof. vm_refl. Qed.
Lemma D_51c98 : decode_any W_51c98 = Some (OpImm ALU_ADD 13 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_51c9c : bv 32 := 0x16c080ef.
Lemma F_51c9c : fetch_word AsanUbsan.M.loaded_segments (0x51c9c : word) = Some W_51c9c.
Proof. vm_refl. Qed.
Lemma D_51c9c : decode_any W_51c9c = Some (Jal 1 33132, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_51ca0 : bv 32 := 0xfffc3517.
Lemma F_51ca0 : fetch_word AsanUbsan.M.loaded_segments (0x51ca0 : word) = Some W_51ca0.
Proof. vm_refl. Qed.
Lemma D_51ca0 : decode_any W_51ca0 = Some (Auipc 10 1048515, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_51ca4 : bv 32 := 0xde650513.
Lemma F_51ca4 : fetch_word AsanUbsan.M.loaded_segments (0x51ca4 : word) = Some W_51ca4.
Proof. vm_refl. Qed.
Lemma D_51ca4 : decode_any W_51ca4 = Some (OpImm ALU_ADD 10 10 3558, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_51ca8 : bv 32 := 0x10c090ef.
Lemma F_51ca8 : fetch_word AsanUbsan.M.loaded_segments (0x51ca8 : word) = Some W_51ca8.
Proof. vm_refl. Qed.
Lemma D_51ca8 : decode_any W_51ca8 = Some (Jal 1 37132, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_51cac : bv 32 := 0x04051063.
Lemma F_51cac : fetch_word AsanUbsan.M.loaded_segments (0x51cac : word) = Some W_51cac.
Proof. vm_refl. Qed.
Lemma D_51cac : decode_any W_51cac = Some (Branch BC_NE 10 0 64, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_51cb0 : bv 32 := 0x16c090ef.
Lemma F_51cb0 : fetch_word AsanUbsan.M.loaded_segments (0x51cb0 : word) = Some W_51cb0.
Proof. vm_refl. Qed.
Lemma D_51cb0 : decode_any W_51cb0 = Some (Jal 1 37228, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_51cb4 : bv 32 := 0x00050a63.
Lemma F_51cb4 : fetch_word AsanUbsan.M.loaded_segments (0x51cb4 : word) = Some W_51cb4.
Proof. vm_refl. Qed.
Lemma D_51cb4 : decode_any W_51cb4 = Some (Branch BC_EQ 10 0 20, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_51cb8 : bv 32 := 0x80040513.
Lemma F_51cb8 : fetch_word AsanUbsan.M.loaded_segments (0x51cb8 : word) = Some W_51cb8.
Proof. vm_refl. Qed.
Lemma D_51cb8 : decode_any W_51cb8 = Some (OpImm ALU_ADD 10 8 2048, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_51cbc : bv 32 := 0xf9850513.
Lemma F_51cbc : fetch_word AsanUbsan.M.loaded_segments (0x51cbc : word) = Some W_51cbc.
Proof. vm_refl. Qed.
Lemma D_51cbc : decode_any W_51cbc = Some (OpImm ALU_ADD 10 10 3992, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_51cc0 : bv 32 := 0x464090ef.
Lemma F_51cc0 : fetch_word AsanUbsan.M.loaded_segments (0x51cc0 : word) = Some W_51cc0.
Proof. vm_refl. Qed.
Lemma D_51cc0 : decode_any W_51cc0 = Some (Jal 1 37988, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_51cc4 : bv 32 := 0x02051463.
Lemma F_51cc4 : fetch_word AsanUbsan.M.loaded_segments (0x51cc4 : word) = Some W_51cc4.
Proof. vm_refl. Qed.
Lemma D_51cc4 : decode_any W_51cc4 = Some (Branch BC_NE 10 0 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_51cc8 : bv 32 := 0xfffc3517.
Lemma F_51cc8 : fetch_word AsanUbsan.M.loaded_segments (0x51cc8 : word) = Some W_51cc8.
Proof. vm_refl. Qed.
Lemma D_51cc8 : decode_any W_51cc8 = Some (Auipc 10 1048515, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_51ccc : bv 32 := 0xdbe50513.
Lemma F_51ccc : fetch_word AsanUbsan.M.loaded_segments (0x51ccc : word) = Some W_51ccc.
Proof. vm_refl. Qed.
Lemma D_51ccc : decode_any W_51ccc = Some (OpImm ALU_ADD 10 10 3518, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_51cd0 : bv 32 := 0x80040793.
Lemma F_51cd0 : fetch_word AsanUbsan.M.loaded_segments (0x51cd0 : word) = Some W_51cd0.
Proof. vm_refl. Qed.
Lemma D_51cd0 : decode_any W_51cd0 = Some (OpImm ALU_ADD 15 8 2048, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_51cd4 : bv 32 := 0xf9878793.
Lemma F_51cd4 : fetch_word AsanUbsan.M.loaded_segments (0x51cd4 : word) = Some W_51cd4.
Proof. vm_refl. Qed.
Lemma D_51cd4 : decode_any W_51cd4 = Some (OpImm ALU_ADD 15 15 3992, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_51cd8 : bv 32 := 0x00048593.
Lemma F_51cd8 : fetch_word AsanUbsan.M.loaded_segments (0x51cd8 : word) = Some W_51cd8.
Proof. vm_refl. Qed.
Lemma D_51cd8 : decode_any W_51cd8 = Some (OpImm ALU_ADD 11 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_51cdc : bv 32 := 0x000b0613.
Lemma F_51cdc : fetch_word AsanUbsan.M.loaded_segments (0x51cdc : word) = Some W_51cdc.
Proof. vm_refl. Qed.
Lemma D_51cdc : decode_any W_51cdc = Some (OpImm ALU_ADD 12 22 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_51ce0 : bv 32 := 0x00090693.
Lemma F_51ce0 : fetch_word AsanUbsan.M.loaded_segments (0x51ce0 : word) = Some W_51ce0.
Proof. vm_refl. Qed.
Lemma D_51ce0 : decode_any W_51ce0 = Some (OpImm ALU_ADD 13 18 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_51ce4 : bv 32 := 0x000b0713.
Lemma F_51ce4 : fetch_word AsanUbsan.M.loaded_segments (0x51ce4 : word) = Some W_51ce4.
Proof. vm_refl. Qed.
Lemma D_51ce4 : decode_any W_51ce4 = Some (OpImm ALU_ADD 14 22 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_51ce8 : bv 32 := 0x405040ef.
Lemma F_51ce8 : fetch_word AsanUbsan.M.loaded_segments (0x51ce8 : word) = Some W_51ce8.
Proof. vm_refl. Qed.
Lemma D_51ce8 : decode_any W_51ce8 = Some (Jal 1 19460, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_51cec : bv 32 := 0x000b0613.
Lemma F_51cec : fetch_word AsanUbsan.M.loaded_segments (0x51cec : word) = Some W_51cec.
Proof. vm_refl. Qed.
Lemma D_51cec : decode_any W_51cec = Some (OpImm ALU_ADD 12 22 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_51cf0 : bv 32 := 0x00090593.
Lemma F_51cf0 : fetch_word AsanUbsan.M.loaded_segments (0x51cf0 : word) = Some W_51cf0.
Proof. vm_refl. Qed.
Lemma D_51cf0 : decode_any W_51cf0 = Some (OpImm ALU_ADD 11 18 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_51cf4 : bv 32 := 0x00048513.
Lemma F_51cf4 : fetch_word AsanUbsan.M.loaded_segments (0x51cf4 : word) = Some W_51cf4.
Proof. vm_refl. Qed.
Lemma D_51cf4 : decode_any W_51cf4 = Some (OpImm ALU_ADD 10 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_51cf8 : bv 32 := 0xfff94693.
Lemma F_51cf8 : fetch_word AsanUbsan.M.loaded_segments (0x51cf8 : word) = Some W_51cf8.
Proof. vm_refl. Qed.
Lemma D_51cf8 : decode_any W_51cf8 = Some (OpImm ALU_XOR 13 18 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_51cfc : bv 32 := 0xd966fce3.
Lemma F_51cfc : fetch_word AsanUbsan.M.loaded_segments (0x51cfc : word) = Some W_51cfc.
Proof. vm_refl. Qed.
Lemma D_51cfc : decode_any W_51cfc = Some (Branch BC_GEU 13 22 7576, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_51d00 : bv 32 := 0x80040693.
Lemma F_51d00 : fetch_word AsanUbsan.M.loaded_segments (0x51d00 : word) = Some W_51d00.
Proof. vm_refl. Qed.
Lemma D_51d00 : decode_any W_51d00 = Some (OpImm ALU_ADD 13 8 2048, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_51d04 : bv 32 := 0xfa868693.
Lemma F_51d04 : fetch_word AsanUbsan.M.loaded_segments (0x51d04 : word) = Some W_51d04.
Proof. vm_refl. Qed.
Lemma D_51d04 : decode_any W_51d04 = Some (OpImm ALU_ADD 13 13 4008, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_51d08 : bv 32 := 0x80040713.
Lemma F_51d08 : fetch_word AsanUbsan.M.loaded_segments (0x51d08 : word) = Some W_51d08.
Proof. vm_refl. Qed.
Lemma D_51d08 : decode_any W_51d08 = Some (OpImm ALU_ADD 14 8 2048, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_51d0c : bv 32 := 0xf9870713.
Lemma F_51d0c : fetch_word AsanUbsan.M.loaded_segments (0x51d0c : word) = Some W_51d0c.
Proof. vm_refl. Qed.
Lemma D_51d0c : decode_any W_51d0c = Some (OpImm ALU_ADD 14 14 3992, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_51d10 : bv 32 := 0x7ff70b93.
Lemma F_51d10 : fetch_word AsanUbsan.M.loaded_segments (0x51d10 : word) = Some W_51d10.
Proof. vm_refl. Qed.
Lemma D_51d10 : decode_any W_51d10 = Some (OpImm ALU_ADD 23 14 2047, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_51d14 : bv 32 := 0x000bb4a3.
Lemma F_51d14 : fetch_word AsanUbsan.M.loaded_segments (0x51d14 : word) = Some W_51d14.
Proof. vm_refl. Qed.
Lemma D_51d14 : decode_any W_51d14 = Some (Store SZ8 23 0 9, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_51d18 : bv 32 := 0x00dab023.
Lemma F_51d18 : fetch_word AsanUbsan.M.loaded_segments (0x51d18 : word) = Some W_51d18.
Proof. vm_refl. Qed.
Lemma D_51d18 : decode_any W_51d18 = Some (Store SZ8 21 13 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_51d1c : bv 32 := 0x000ab423.
Lemma F_51d1c : fetch_word AsanUbsan.M.loaded_segments (0x51d1c : word) = Some W_51d1c.
Proof. vm_refl. Qed.
Lemma D_51d1c : decode_any W_51d1c = Some (Store SZ8 21 0 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_51d20 : bv 32 := 0x00060493.
Lemma F_51d20 : fetch_word AsanUbsan.M.loaded_segments (0x51d20 : word) = Some W_51d20.
Proof. vm_refl. Qed.
Lemma D_51d20 : decode_any W_51d20 = Some (OpImm ALU_ADD 9 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_51d24 : bv 32 := 0x00058913.
Lemma F_51d24 : fetch_word AsanUbsan.M.loaded_segments (0x51d24 : word) = Some W_51d24.
Proof. vm_refl. Qed.
Lemma D_51d24 : decode_any W_51d24 = Some (OpImm ALU_ADD 18 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_51d28 : bv 32 := 0x00050b13.
Lemma F_51d28 : fetch_word AsanUbsan.M.loaded_segments (0x51d28 : word) = Some W_51d28.
Proof. vm_refl. Qed.
Lemma D_51d28 : decode_any W_51d28 = Some (OpImm ALU_ADD 22 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_51d2c : bv 32 := 0x38d200ef.
Lemma F_51d2c : fetch_word AsanUbsan.M.loaded_segments (0x51d2c : word) = Some W_51d2c.
Proof. vm_refl. Qed.
Lemma D_51d2c : decode_any W_51d2c = Some (Jal 1 134028, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_51d30 : bv 32 := 0x00050593.
Lemma F_51d30 : fetch_word AsanUbsan.M.loaded_segments (0x51d30 : word) = Some W_51d30.
Proof. vm_refl. Qed.
Lemma D_51d30 : decode_any W_51d30 = Some (OpImm ALU_ADD 11 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_51d34 : bv 32 := 0x0004e517.
Lemma F_51d34 : fetch_word AsanUbsan.M.loaded_segments (0x51d34 : word) = Some W_51d34.
Proof. vm_refl. Qed.
Lemma D_51d34 : decode_any W_51d34 = Some (Auipc 10 78, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_51d38 : bv 32 := 0xbdc53503.
Lemma F_51d38 : fetch_word AsanUbsan.M.loaded_segments (0x51d38 : word) = Some W_51d38.
Proof. vm_refl. Qed.
Lemma D_51d38 : decode_any W_51d38 = Some (Load SZ8 true 10 10 3036, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_51d3c : bv 32 := 0x02154703.
Lemma F_51d3c : fetch_word AsanUbsan.M.loaded_segments (0x51d3c : word) = Some W_51d3c.
Proof. vm_refl. Qed.
Lemma D_51d3c : decode_any W_51d3c = Some (Load SZ1 false 14 10 33, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_51d40 : bv 32 := 0x008bb4a3.
Lemma F_51d40 : fetch_word AsanUbsan.M.loaded_segments (0x51d40 : word) = Some W_51d40.
Proof. vm_refl. Qed.
Lemma D_51d40 : decode_any W_51d40 = Some (Store SZ8 23 8 9, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_51d44 : bv 32 := 0x80040513.
Lemma F_51d44 : fetch_word AsanUbsan.M.loaded_segments (0x51d44 : word) = Some W_51d44.
Proof. vm_refl. Qed.
Lemma D_51d44 : decode_any W_51d44 = Some (OpImm ALU_ADD 10 8 2048, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_51d48 : bv 32 := 0xf9850513.
Lemma F_51d48 : fetch_word AsanUbsan.M.loaded_segments (0x51d48 : word) = Some W_51d48.
Proof. vm_refl. Qed.
Lemma D_51d48 : decode_any W_51d48 = Some (OpImm ALU_ADD 10 10 3992, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_51d4c : bv 32 := 0x0ff00793.
Lemma F_51d4c : fetch_word AsanUbsan.M.loaded_segments (0x51d4c : word) = Some W_51d4c.
Proof. vm_refl. Qed.
Lemma D_51d4c : decode_any W_51d4c = Some (OpImm ALU_ADD 15 0 255, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_51d50 : bv 32 := 0x00040613.
Lemma F_51d50 : fetch_word AsanUbsan.M.loaded_segments (0x51d50 : word) = Some W_51d50.
Proof. vm_refl. Qed.
Lemma D_51d50 : decode_any W_51d50 = Some (OpImm ALU_ADD 12 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_51d54 : bv 32 := 0x00000693.
Lemma F_51d54 : fetch_word AsanUbsan.M.loaded_segments (0x51d54 : word) = Some W_51d54.
Proof. vm_refl. Qed.
Lemma D_51d54 : decode_any W_51d54 = Some (OpImm ALU_ADD 13 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_51d58 : bv 32 := 0x0b0080ef.
Lemma F_51d58 : fetch_word AsanUbsan.M.loaded_segments (0x51d58 : word) = Some W_51d58.
Proof. vm_refl. Qed.
Lemma D_51d58 : decode_any W_51d58 = Some (Jal 1 32944, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_51d5c : bv 32 := 0x80040613.
Lemma F_51d5c : fetch_word AsanUbsan.M.loaded_segments (0x51d5c : word) = Some W_51d5c.
Proof. vm_refl. Qed.
Lemma D_51d5c : decode_any W_51d5c = Some (OpImm ALU_ADD 12 8 2048, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_51d60 : bv 32 := 0xf9860613.
Lemma F_51d60 : fetch_word AsanUbsan.M.loaded_segments (0x51d60 : word) = Some W_51d60.
Proof. vm_refl. Qed.
Lemma D_51d60 : decode_any W_51d60 = Some (OpImm ALU_ADD 12 12 3992, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_51d64 : bv 32 := 0x00090513.
Lemma F_51d64 : fetch_word AsanUbsan.M.loaded_segments (0x51d64 : word) = Some W_51d64.
Proof. vm_refl. Qed.
Lemma D_51d64 : decode_any W_51d64 = Some (OpImm ALU_ADD 10 18 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_51d68 : bv 32 := 0x00048593.
Lemma F_51d68 : fetch_word AsanUbsan.M.loaded_segments (0x51d68 : word) = Some W_51d68.
Proof. vm_refl. Qed.
Lemma D_51d68 : decode_any W_51d68 = Some (OpImm ALU_ADD 11 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_51d6c : bv 32 := 0x655040ef.
Lemma F_51d6c : fetch_word AsanUbsan.M.loaded_segments (0x51d6c : word) = Some W_51d6c.
Proof. vm_refl. Qed.
Lemma D_51d6c : decode_any W_51d6c = Some (Jal 1 20052, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_51d70 : bv 32 := 0x000b0513.
Lemma F_51d70 : fetch_word AsanUbsan.M.loaded_segments (0x51d70 : word) = Some W_51d70.
Proof. vm_refl. Qed.
Lemma D_51d70 : decode_any W_51d70 = Some (OpImm ALU_ADD 10 22 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_51d74 : bv 32 := 0x00090593.
Lemma F_51d74 : fetch_word AsanUbsan.M.loaded_segments (0x51d74 : word) = Some W_51d74.
Proof. vm_refl. Qed.
Lemma D_51d74 : decode_any W_51d74 = Some (OpImm ALU_ADD 11 18 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_51d78 : bv 32 := 0x00048613.
Lemma F_51d78 : fetch_word AsanUbsan.M.loaded_segments (0x51d78 : word) = Some W_51d78.
Proof. vm_refl. Qed.
Lemma D_51d78 : decode_any W_51d78 = Some (OpImm ALU_ADD 12 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_51d7c : bv 32 := 0xfbf48b13.
Lemma F_51d7c : fetch_word AsanUbsan.M.loaded_segments (0x51d7c : word) = Some W_51d7c.
Proof. vm_refl. Qed.
Lemma D_51d7c : decode_any W_51d7c = Some (OpImm ALU_ADD 22 9 4031, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_51d80 : bv 32 := 0xfbf00693.
Lemma F_51d80 : fetch_word AsanUbsan.M.loaded_segments (0x51d80 : word) = Some W_51d80.
Proof. vm_refl. Qed.
Lemma D_51d80 : decode_any W_51d80 = Some (OpImm ALU_ADD 13 0 4031, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_51d84 : bv 32 := 0xd166eee3.
Lemma F_51d84 : fetch_word AsanUbsan.M.loaded_segments (0x51d84 : word) = Some W_51d84.
Proof. vm_refl. Qed.
Lemma D_51d84 : decode_any W_51d84 = Some (Branch BC_LTU 13 22 7452, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_51d88 : bv 32 := 0x02061e63.
Lemma F_51d88 : fetch_word AsanUbsan.M.loaded_segments (0x51d88 : word) = Some W_51d88.
Proof. vm_refl. Qed.
Lemma D_51d88 : decode_any W_51d88 = Some (Branch BC_NE 12 0 60, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_51d8c : bv 32 := 0xd4dff06f.
Lemma F_51d8c : fetch_word AsanUbsan.M.loaded_segments (0x51d8c : word) = Some W_51d8c.
Proof. vm_refl. Qed.
Lemma D_51d8c : decode_any W_51d8c = Some (Jal 0 2096460, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_51d90 : bv 32 := 0x00070783.
Lemma F_51d90 : fetch_word AsanUbsan.M.loaded_segments (0x51d90 : word) = Some W_51d90.
Proof. vm_refl. Qed.
Lemma D_51d90 : decode_any W_51d90 = Some (Load SZ1 true 15 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_51d94 : bv 32 := 0x0079f813.
Lemma F_51d94 : fetch_word AsanUbsan.M.loaded_segments (0x51d94 : word) = Some W_51d94.
Proof. vm_refl. Qed.
Lemma D_51d94 : decode_any W_51d94 = Some (OpImm ALU_AND 16 19 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_51d98 : bv 32 := 0x00f038b3.
Lemma F_51d98 : fetch_word AsanUbsan.M.loaded_segments (0x51d98 : word) = Some W_51d98.
Proof. vm_refl. Qed.
Lemma D_51d98 : decode_any W_51d98 = Some (Op ALU_SLTU 17 0 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_51d9c : bv 32 := 0x00f827b3.
Lemma F_51d9c : fetch_word AsanUbsan.M.loaded_segments (0x51d9c : word) = Some W_51d9c.
Proof. vm_refl. Qed.
Lemma D_51d9c : decode_any W_51d9c = Some (Op ALU_SLT 15 16 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_51da0 : bv 32 := 0x0017c793.
Lemma F_51da0 : fetch_word AsanUbsan.M.loaded_segments (0x51da0 : word) = Some W_51da0.
Proof. vm_refl. Qed.
Lemma D_51da0 : decode_any W_51da0 = Some (OpImm ALU_XOR 15 15 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_51da4 : bv 32 := 0x00f8f7b3.
Lemma F_51da4 : fetch_word AsanUbsan.M.loaded_segments (0x51da4 : word) = Some W_51da4.
Proof. vm_refl. Qed.
Lemma D_51da4 : decode_any W_51da4 = Some (Op ALU_AND 15 17 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_51da8 : bv 32 := 0x00e6fa63.
Lemma F_51da8 : fetch_word AsanUbsan.M.loaded_segments (0x51da8 : word) = Some W_51da8.
Proof. vm_refl. Qed.
Lemma D_51da8 : decode_any W_51da8 = Some (Branch BC_GEU 13 14 20, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_51dac : bv 32 := 0x0006c803.
Lemma F_51dac : fetch_word AsanUbsan.M.loaded_segments (0x51dac : word) = Some W_51dac.
Proof. vm_refl. Qed.
Lemma D_51dac : decode_any W_51dac = Some (Load SZ1 false 16 13 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_51db0 : bv 32 := 0x00168693.
Lemma F_51db0 : fetch_word AsanUbsan.M.loaded_segments (0x51db0 : word) = Some W_51db0.
Proof. vm_refl. Qed.
Lemma D_51db0 : decode_any W_51db0 = Some (OpImm ALU_ADD 13 13 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_51db4 : bv 32 := 0x00f867b3.
Lemma F_51db4 : fetch_word AsanUbsan.M.loaded_segments (0x51db4 : word) = Some W_51db4.
Proof. vm_refl. Qed.
Lemma D_51db4 : decode_any W_51db4 = Some (Op ALU_OR 15 16 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_51db8 : bv 32 := 0xfee69ae3.
Lemma F_51db8 : fetch_word AsanUbsan.M.loaded_segments (0x51db8 : word) = Some W_51db8.
Proof. vm_refl. Qed.
Lemma D_51db8 : decode_any W_51db8 = Some (Branch BC_NE 13 14 8180, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_51dbc : bv 32 := 0x0ff7f693.
Lemma F_51dbc : fetch_word AsanUbsan.M.loaded_segments (0x51dbc : word) = Some W_51dbc.
Proof. vm_refl. Qed.
Lemma D_51dbc : decode_any W_51dbc = Some (OpImm ALU_AND 13 15 255, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_51dc0 : bv 32 := 0xd0068ce3.
Lemma F_51dc0 : fetch_word AsanUbsan.M.loaded_segments (0x51dc0 : word) = Some W_51dc0.
Proof. vm_refl. Qed.
Lemma D_51dc0 : decode_any W_51dc0 = Some (Branch BC_EQ 13 0 7448, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_51dc4 : bv 32 := 0x00050b93.
Lemma F_51dc4 : fetch_word AsanUbsan.M.loaded_segments (0x51dc4 : word) = Some W_51dc4.
Proof. vm_refl. Qed.
Lemma D_51dc4 : decode_any W_51dc4 = Some (OpImm ALU_ADD 23 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_51dc8 : bv 32 := 0x00058513.
Lemma F_51dc8 : fetch_word AsanUbsan.M.loaded_segments (0x51dc8 : word) = Some W_51dc8.
Proof. vm_refl. Qed.
Lemma D_51dc8 : decode_any W_51dc8 = Some (OpImm ALU_ADD 10 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_51dcc : bv 32 := 0x00058c13.
Lemma F_51dcc : fetch_word AsanUbsan.M.loaded_segments (0x51dcc : word) = Some W_51dcc.
Proof. vm_refl. Qed.
Lemma D_51dcc : decode_any W_51dcc = Some (OpImm ALU_ADD 24 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_51dd0 : bv 32 := 0x00060593.
Lemma F_51dd0 : fetch_word AsanUbsan.M.loaded_segments (0x51dd0 : word) = Some W_51dd0.
Proof. vm_refl. Qed.
Lemma D_51dd0 : decode_any W_51dd0 = Some (OpImm ALU_ADD 11 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_51dd4 : bv 32 := 0x00060493.
Lemma F_51dd4 : fetch_word AsanUbsan.M.loaded_segments (0x51dd4 : word) = Some W_51dd4.
Proof. vm_refl. Qed.
Lemma D_51dd4 : decode_any W_51dd4 = Some (OpImm ALU_ADD 9 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_51dd8 : bv 32 := 0x605010ef.
Lemma F_51dd8 : fetch_word AsanUbsan.M.loaded_segments (0x51dd8 : word) = Some W_51dd8.
Proof. vm_refl. Qed.
Lemma D_51dd8 : decode_any W_51dd8 = Some (Jal 1 7684, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_51ddc : bv 32 := 0x000c0593.
Lemma F_51ddc : fetch_word AsanUbsan.M.loaded_segments (0x51ddc : word) = Some W_51ddc.
Proof. vm_refl. Qed.
Lemma D_51ddc : decode_any W_51ddc = Some (OpImm ALU_ADD 11 24 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_51de0 : bv 32 := 0x00048613.
Lemma F_51de0 : fetch_word AsanUbsan.M.loaded_segments (0x51de0 : word) = Some W_51de0.
Proof. vm_refl. Qed.
Lemma D_51de0 : decode_any W_51de0 = Some (OpImm ALU_ADD 12 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_51de4 : bv 32 := 0x00050913.
Lemma F_51de4 : fetch_word AsanUbsan.M.loaded_segments (0x51de4 : word) = Some W_51de4.
Proof. vm_refl. Qed.
Lemma D_51de4 : decode_any W_51de4 = Some (OpImm ALU_ADD 18 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_51de8 : bv 32 := 0x000b8513.
Lemma F_51de8 : fetch_word AsanUbsan.M.loaded_segments (0x51de8 : word) = Some W_51de8.
Proof. vm_refl. Qed.
Lemma D_51de8 : decode_any W_51de8 = Some (OpImm ALU_ADD 10 23 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_51dec : bv 32 := 0xce0906e3.
Lemma F_51dec : fetch_word AsanUbsan.M.loaded_segments (0x51dec : word) = Some W_51dec.
Proof. vm_refl. Qed.
Lemma D_51dec : decode_any W_51dec = Some (Branch BC_EQ 18 0 7404, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_51df0 : bv 32 := 0xfffc3517.
Lemma F_51df0 : fetch_word AsanUbsan.M.loaded_segments (0x51df0 : word) = Some W_51df0.
Proof. vm_refl. Qed.
Lemma D_51df0 : decode_any W_51df0 = Some (Auipc 10 1048515, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_51df4 : bv 32 := 0xc9650513.
Lemma F_51df4 : fetch_word AsanUbsan.M.loaded_segments (0x51df4 : word) = Some W_51df4.
Proof. vm_refl. Qed.
Lemma D_51df4 : decode_any W_51df4 = Some (OpImm ALU_ADD 10 10 3222, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_51df8 : bv 32 := 0x7bd080ef.
Lemma F_51df8 : fetch_word AsanUbsan.M.loaded_segments (0x51df8 : word) = Some W_51df8.
Proof. vm_refl. Qed.
Lemma D_51df8 : decode_any W_51df8 = Some (Jal 1 36796, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_51dfc : bv 32 := 0x000c0593.
Lemma F_51dfc : fetch_word AsanUbsan.M.loaded_segments (0x51dfc : word) = Some W_51dfc.
Proof. vm_refl. Qed.
Lemma D_51dfc : decode_any W_51dfc = Some (OpImm ALU_ADD 11 24 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_51e00 : bv 32 := 0x00048613.
Lemma F_51e00 : fetch_word AsanUbsan.M.loaded_segments (0x51e00 : word) = Some W_51e00.
Proof. vm_refl. Qed.
Lemma D_51e00 : decode_any W_51e00 = Some (OpImm ALU_ADD 12 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_51e04 : bv 32 := 0x00050693.
Lemma F_51e04 : fetch_word AsanUbsan.M.loaded_segments (0x51e04 : word) = Some W_51e04.
Proof. vm_refl. Qed.
Lemma D_51e04 : decode_any W_51e04 = Some (OpImm ALU_ADD 13 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_51e08 : bv 32 := 0x000b8513.
Lemma F_51e08 : fetch_word AsanUbsan.M.loaded_segments (0x51e08 : word) = Some W_51e08.
Proof. vm_refl. Qed.
Lemma D_51e08 : decode_any W_51e08 = Some (OpImm ALU_ADD 10 23 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_51e0c : bv 32 := 0xcc0696e3.
Lemma F_51e0c : fetch_word AsanUbsan.M.loaded_segments (0x51e0c : word) = Some W_51e0c.
Proof. vm_refl. Qed.
Lemma D_51e0c : decode_any W_51e0c = Some (Branch BC_NE 13 0 7372, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_51e10 : bv 32 := 0x00c090ef.
Lemma F_51e10 : fetch_word AsanUbsan.M.loaded_segments (0x51e10 : word) = Some W_51e10.
Proof. vm_refl. Qed.
Lemma D_51e10 : decode_any W_51e10 = Some (Jal 1 36876, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_51e14 : bv 32 := 0x16050c63.
Lemma F_51e14 : fetch_word AsanUbsan.M.loaded_segments (0x51e14 : word) = Some W_51e14.
Proof. vm_refl. Qed.
Lemma D_51e14 : decode_any W_51e14 = Some (Branch BC_EQ 10 0 376, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_51e18 : bv 32 := 0x80040513.
Lemma F_51e18 : fetch_word AsanUbsan.M.loaded_segments (0x51e18 : word) = Some W_51e18.
Proof. vm_refl. Qed.
Lemma D_51e18 : decode_any W_51e18 = Some (OpImm ALU_ADD 10 8 2048, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_51e1c : bv 32 := 0xfa850513.
Lemma F_51e1c : fetch_word AsanUbsan.M.loaded_segments (0x51e1c : word) = Some W_51e1c.
Proof. vm_refl. Qed.
Lemma D_51e1c : decode_any W_51e1c = Some (OpImm ALU_ADD 10 10 4008, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_51e20 : bv 32 := 0x80040593.
Lemma F_51e20 : fetch_word AsanUbsan.M.loaded_segments (0x51e20 : word) = Some W_51e20.
Proof. vm_refl. Qed.
Lemma D_51e20 : decode_any W_51e20 = Some (OpImm ALU_ADD 11 8 2048, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_51e24 : bv 32 := 0xf9858593.
Lemma F_51e24 : fetch_word AsanUbsan.M.loaded_segments (0x51e24 : word) = Some W_51e24.
Proof. vm_refl. Qed.
Lemma D_51e24 : decode_any W_51e24 = Some (OpImm ALU_ADD 11 11 3992, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_51e28 : bv 32 := 0x7ff58993.
Lemma F_51e28 : fetch_word AsanUbsan.M.loaded_segments (0x51e28 : word) = Some W_51e28.
Proof. vm_refl. Qed.
Lemma D_51e28 : decode_any W_51e28 = Some (OpImm ALU_ADD 19 11 2047, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_51e2c : bv 32 := 0x0009b4a3.
Lemma F_51e2c : fetch_word AsanUbsan.M.loaded_segments (0x51e2c : word) = Some W_51e2c.
Proof. vm_refl. Qed.
Lemma D_51e2c : decode_any W_51e2c = Some (Store SZ8 19 0 9, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_51e30 : bv 32 := 0x00aab023.
Lemma F_51e30 : fetch_word AsanUbsan.M.loaded_segments (0x51e30 : word) = Some W_51e30.
Proof. vm_refl. Qed.
Lemma D_51e30 : decode_any W_51e30 = Some (Store SZ8 21 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_51e34 : bv 32 := 0x000ab423.
Lemma F_51e34 : fetch_word AsanUbsan.M.loaded_segments (0x51e34 : word) = Some W_51e34.
Proof. vm_refl. Qed.
Lemma D_51e34 : decode_any W_51e34 = Some (Store SZ8 21 0 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_51e38 : bv 32 := 0x281200ef.
Lemma F_51e38 : fetch_word AsanUbsan.M.loaded_segments (0x51e38 : word) = Some W_51e38.
Proof. vm_refl. Qed.
Lemma D_51e38 : decode_any W_51e38 = Some (Jal 1 133760, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_51e3c : bv 32 := 0x00050593.
Lemma F_51e3c : fetch_word AsanUbsan.M.loaded_segments (0x51e3c : word) = Some W_51e3c.
Proof. vm_refl. Qed.
Lemma D_51e3c : decode_any W_51e3c = Some (OpImm ALU_ADD 11 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_51e40 : bv 32 := 0x0004e517.
Lemma F_51e40 : fetch_word AsanUbsan.M.loaded_segments (0x51e40 : word) = Some W_51e40.
Proof. vm_refl. Qed.
Lemma D_51e40 : decode_any W_51e40 = Some (Auipc 10 78, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_51e44 : bv 32 := 0xad053503.
Lemma F_51e44 : fetch_word AsanUbsan.M.loaded_segments (0x51e44 : word) = Some W_51e44.
Proof. vm_refl. Qed.
Lemma D_51e44 : decode_any W_51e44 = Some (Load SZ8 true 10 10 2768, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_51e48 : bv 32 := 0x02154703.
Lemma F_51e48 : fetch_word AsanUbsan.M.loaded_segments (0x51e48 : word) = Some W_51e48.
Proof. vm_refl. Qed.
Lemma D_51e48 : decode_any W_51e48 = Some (Load SZ1 false 14 10 33, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_51e4c : bv 32 := 0x0089b4a3.
Lemma F_51e4c : fetch_word AsanUbsan.M.loaded_segments (0x51e4c : word) = Some W_51e4c.
Proof. vm_refl. Qed.
Lemma D_51e4c : decode_any W_51e4c = Some (Store SZ8 19 8 9, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_51e50 : bv 32 := 0x80040513.
Lemma F_51e50 : fetch_word AsanUbsan.M.loaded_segments (0x51e50 : word) = Some W_51e50.
Proof. vm_refl. Qed.
Lemma D_51e50 : decode_any W_51e50 = Some (OpImm ALU_ADD 10 8 2048, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_51e54 : bv 32 := 0xf9850513.
Lemma F_51e54 : fetch_word AsanUbsan.M.loaded_segments (0x51e54 : word) = Some W_51e54.
Proof. vm_refl. Qed.
Lemma D_51e54 : decode_any W_51e54 = Some (OpImm ALU_ADD 10 10 3992, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_51e58 : bv 32 := 0x0ff00793.
Lemma F_51e58 : fetch_word AsanUbsan.M.loaded_segments (0x51e58 : word) = Some W_51e58.
Proof. vm_refl. Qed.
Lemma D_51e58 : decode_any W_51e58 = Some (OpImm ALU_ADD 15 0 255, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_51e5c : bv 32 := 0x00040613.
Lemma F_51e5c : fetch_word AsanUbsan.M.loaded_segments (0x51e5c : word) = Some W_51e5c.
Proof. vm_refl. Qed.
Lemma D_51e5c : decode_any W_51e5c = Some (OpImm ALU_ADD 12 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_51e60 : bv 32 := 0x00000693.
Lemma F_51e60 : fetch_word AsanUbsan.M.loaded_segments (0x51e60 : word) = Some W_51e60.
Proof. vm_refl. Qed.
Lemma D_51e60 : decode_any W_51e60 = Some (OpImm ALU_ADD 13 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_51e64 : bv 32 := 0x7a5070ef.
Lemma F_51e64 : fetch_word AsanUbsan.M.loaded_segments (0x51e64 : word) = Some W_51e64.
Proof. vm_refl. Qed.
Lemma D_51e64 : decode_any W_51e64 = Some (Jal 1 32676, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_51e68 : bv 32 := 0x80040513.
Lemma F_51e68 : fetch_word AsanUbsan.M.loaded_segments (0x51e68 : word) = Some W_51e68.
Proof. vm_refl. Qed.
Lemma D_51e68 : decode_any W_51e68 = Some (OpImm ALU_ADD 10 8 2048, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_51e6c : bv 32 := 0xf9850513.
Lemma F_51e6c : fetch_word AsanUbsan.M.loaded_segments (0x51e6c : word) = Some W_51e6c.
Proof. vm_refl. Qed.
Lemma D_51e6c : decode_any W_51e6c = Some (OpImm ALU_ADD 10 10 3992, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_51e70 : bv 32 := 0x2b4090ef.
Lemma F_51e70 : fetch_word AsanUbsan.M.loaded_segments (0x51e70 : word) = Some W_51e70.
Proof. vm_refl. Qed.
Lemma D_51e70 : decode_any W_51e70 = Some (Jal 1 37556, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_51e74 : bv 32 := 0x00050693.
Lemma F_51e74 : fetch_word AsanUbsan.M.loaded_segments (0x51e74 : word) = Some W_51e74.
Proof. vm_refl. Qed.
Lemma D_51e74 : decode_any W_51e74 = Some (OpImm ALU_ADD 13 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_51e78 : bv 32 := 0x00040993.
Lemma F_51e78 : fetch_word AsanUbsan.M.loaded_segments (0x51e78 : word) = Some W_51e78.
Proof. vm_refl. Qed.
Lemma D_51e78 : decode_any W_51e78 = Some (OpImm ALU_ADD 19 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_51e7c : bv 32 := 0x00048613.
Lemma F_51e7c : fetch_word AsanUbsan.M.loaded_segments (0x51e7c : word) = Some W_51e7c.
Proof. vm_refl. Qed.
Lemma D_51e7c : decode_any W_51e7c = Some (OpImm ALU_ADD 12 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_51e80 : bv 32 := 0x000c0593.
Lemma F_51e80 : fetch_word AsanUbsan.M.loaded_segments (0x51e80 : word) = Some W_51e80.
Proof. vm_refl. Qed.
Lemma D_51e80 : decode_any W_51e80 = Some (OpImm ALU_ADD 11 24 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_51e84 : bv 32 := 0x000b8513.
Lemma F_51e84 : fetch_word AsanUbsan.M.loaded_segments (0x51e84 : word) = Some W_51e84.
Proof. vm_refl. Qed.
Lemma D_51e84 : decode_any W_51e84 = Some (OpImm ALU_ADD 10 23 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_51e88 : bv 32 := 0xc40698e3.
Lemma F_51e88 : fetch_word AsanUbsan.M.loaded_segments (0x51e88 : word) = Some W_51e88.
Proof. vm_refl. Qed.
Lemma D_51e88 : decode_any W_51e88 = Some (Branch BC_NE 13 0 7248, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_51e8c : bv 32 := 0x1040006f.
Lemma F_51e8c : fetch_word AsanUbsan.M.loaded_segments (0x51e8c : word) = Some W_51e8c.
Proof. vm_refl. Qed.
Lemma D_51e8c : decode_any W_51e8c = Some (Jal 0 260, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_51e90 : bv 32 := 0x00070783.
Lemma F_51e90 : fetch_word AsanUbsan.M.loaded_segments (0x51e90 : word) = Some W_51e90.
Proof. vm_refl. Qed.
Lemma D_51e90 : decode_any W_51e90 = Some (Load SZ1 true 15 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_51e94 : bv 32 := 0x007a7813.
Lemma F_51e94 : fetch_word AsanUbsan.M.loaded_segments (0x51e94 : word) = Some W_51e94.
Proof. vm_refl. Qed.
Lemma D_51e94 : decode_any W_51e94 = Some (OpImm ALU_AND 16 20 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_51e98 : bv 32 := 0x00f038b3.
Lemma F_51e98 : fetch_word AsanUbsan.M.loaded_segments (0x51e98 : word) = Some W_51e98.
Proof. vm_refl. Qed.
Lemma D_51e98 : decode_any W_51e98 = Some (Op ALU_SLTU 17 0 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_51e9c : bv 32 := 0x00f827b3.
Lemma F_51e9c : fetch_word AsanUbsan.M.loaded_segments (0x51e9c : word) = Some W_51e9c.
Proof. vm_refl. Qed.
Lemma D_51e9c : decode_any W_51e9c = Some (Op ALU_SLT 15 16 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_51ea0 : bv 32 := 0x0017c793.
Lemma F_51ea0 : fetch_word AsanUbsan.M.loaded_segments (0x51ea0 : word) = Some W_51ea0.
Proof. vm_refl. Qed.
Lemma D_51ea0 : decode_any W_51ea0 = Some (OpImm ALU_XOR 15 15 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_51ea4 : bv 32 := 0x00f8f7b3.
Lemma F_51ea4 : fetch_word AsanUbsan.M.loaded_segments (0x51ea4 : word) = Some W_51ea4.
Proof. vm_refl. Qed.
Lemma D_51ea4 : decode_any W_51ea4 = Some (Op ALU_AND 15 17 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_51ea8 : bv 32 := 0x00e6fa63.
Lemma F_51ea8 : fetch_word AsanUbsan.M.loaded_segments (0x51ea8 : word) = Some W_51ea8.
Proof. vm_refl. Qed.
Lemma D_51ea8 : decode_any W_51ea8 = Some (Branch BC_GEU 13 14 20, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_51eac : bv 32 := 0x0006c803.
Lemma F_51eac : fetch_word AsanUbsan.M.loaded_segments (0x51eac : word) = Some W_51eac.
Proof. vm_refl. Qed.
Lemma D_51eac : decode_any W_51eac = Some (Load SZ1 false 16 13 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_51eb0 : bv 32 := 0x00168693.
Lemma F_51eb0 : fetch_word AsanUbsan.M.loaded_segments (0x51eb0 : word) = Some W_51eb0.
Proof. vm_refl. Qed.
Lemma D_51eb0 : decode_any W_51eb0 = Some (OpImm ALU_ADD 13 13 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_51eb4 : bv 32 := 0x00f867b3.
Lemma F_51eb4 : fetch_word AsanUbsan.M.loaded_segments (0x51eb4 : word) = Some W_51eb4.
Proof. vm_refl. Qed.
Lemma D_51eb4 : decode_any W_51eb4 = Some (Op ALU_OR 15 16 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_51eb8 : bv 32 := 0xfee69ae3.
Lemma F_51eb8 : fetch_word AsanUbsan.M.loaded_segments (0x51eb8 : word) = Some W_51eb8.
Proof. vm_refl. Qed.
Lemma D_51eb8 : decode_any W_51eb8 = Some (Branch BC_NE 13 14 8180, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_51ebc : bv 32 := 0x0ff7f693.
Lemma F_51ebc : fetch_word AsanUbsan.M.loaded_segments (0x51ebc : word) = Some W_51ebc.
Proof. vm_refl. Qed.
Lemma D_51ebc : decode_any W_51ebc = Some (OpImm ALU_AND 13 15 255, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_51ec0 : bv 32 := 0xc60680e3.
Lemma F_51ec0 : fetch_word AsanUbsan.M.loaded_segments (0x51ec0 : word) = Some W_51ec0.
Proof. vm_refl. Qed.
Lemma D_51ec0 : decode_any W_51ec0 = Some (Branch BC_EQ 13 0 7264, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_51ec4 : bv 32 := 0x00050493.
Lemma F_51ec4 : fetch_word AsanUbsan.M.loaded_segments (0x51ec4 : word) = Some W_51ec4.
Proof. vm_refl. Qed.
Lemma D_51ec4 : decode_any W_51ec4 = Some (OpImm ALU_ADD 9 10 0, 4%Z).
Proof. vm_refl. Qed.
