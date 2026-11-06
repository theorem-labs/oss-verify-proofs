(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.boost_beast.http_request.images Require Import Plain.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.

(* [comment removed for export] *)
Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

(* [comment removed for export] *)
Definition W_67aec : bv 32 := 0xfa010113.
Lemma F_67aec : fetch_word Plain.M.loaded_segments (0x67aec : word) = Some W_67aec.
Proof. vm_refl. Qed.
Lemma D_67aec : decode_any W_67aec = Some (OpImm ALU_ADD 2 2 4000, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_67af0 : bv 32 := 0x02113423.
Lemma F_67af0 : fetch_word Plain.M.loaded_segments (0x67af0 : word) = Some W_67af0.
Proof. vm_refl. Qed.
Lemma D_67af0 : decode_any W_67af0 = Some (Store SZ8 2 1 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_67af4 : bv 32 := 0x02813023.
Lemma F_67af4 : fetch_word Plain.M.loaded_segments (0x67af4 : word) = Some W_67af4.
Proof. vm_refl. Qed.
Lemma D_67af4 : decode_any W_67af4 = Some (Store SZ8 2 8 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_67af8 : bv 32 := 0x00913c23.
Lemma F_67af8 : fetch_word Plain.M.loaded_segments (0x67af8 : word) = Some W_67af8.
Proof. vm_refl. Qed.
Lemma D_67af8 : decode_any W_67af8 = Some (Store SZ8 2 9 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_67afc : bv 32 := 0x00058413.
Lemma F_67afc : fetch_word Plain.M.loaded_segments (0x67afc : word) = Some W_67afc.
Proof. vm_refl. Qed.
Lemma D_67afc : decode_any W_67afc = Some (OpImm ALU_ADD 8 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_67b00 : bv 32 := 0x00050293.
Lemma F_67b00 : fetch_word Plain.M.loaded_segments (0x67b00 : word) = Some W_67b00.
Proof. vm_refl. Qed.
Lemma D_67b00 : decode_any W_67b00 = Some (OpImm ALU_ADD 5 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_67b04 : bv 32 := 0x05013823.
Lemma F_67b04 : fetch_word Plain.M.loaded_segments (0x67b04 : word) = Some W_67b04.
Proof. vm_refl. Qed.
Lemma D_67b04 : decode_any W_67b04 = Some (Store SZ8 2 16 80, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_67b08 : bv 32 := 0x05113c23.
Lemma F_67b08 : fetch_word Plain.M.loaded_segments (0x67b08 : word) = Some W_67b08.
Proof. vm_refl. Qed.
Lemma D_67b08 : decode_any W_67b08 = Some (Store SZ8 2 17 88, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_67b0c : bv 32 := 0x00018517.
Lemma F_67b0c : fetch_word Plain.M.loaded_segments (0x67b0c : word) = Some W_67b0c.
Proof. vm_refl. Qed.
Lemma D_67b0c : decode_any W_67b0c = Some (Auipc 10 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_67b10 : bv 32 := 0xcfc53483.
Lemma F_67b10 : fetch_word Plain.M.loaded_segments (0x67b10 : word) = Some W_67b10.
Proof. vm_refl. Qed.
Lemma D_67b10 : decode_any W_67b10 = Some (Load SZ8 true 9 10 3324, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_67b14 : bv 32 := 0x02c13823.
Lemma F_67b14 : fetch_word Plain.M.loaded_segments (0x67b14 : word) = Some W_67b14.
Proof. vm_refl. Qed.
Lemma D_67b14 : decode_any W_67b14 = Some (Store SZ8 2 12 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_67b18 : bv 32 := 0x02d13c23.
Lemma F_67b18 : fetch_word Plain.M.loaded_segments (0x67b18 : word) = Some W_67b18.
Proof. vm_refl. Qed.
Lemma D_67b18 : decode_any W_67b18 = Some (Store SZ8 2 13 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_67b1c : bv 32 := 0x04e13023.
Lemma F_67b1c : fetch_word Plain.M.loaded_segments (0x67b1c : word) = Some W_67b1c.
Proof. vm_refl. Qed.
Lemma D_67b1c : decode_any W_67b1c = Some (Store SZ8 2 14 64, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_67b20 : bv 32 := 0x04f13423.
Lemma F_67b20 : fetch_word Plain.M.loaded_segments (0x67b20 : word) = Some W_67b20.
Proof. vm_refl. Qed.
Lemma D_67b20 : decode_any W_67b20 = Some (Store SZ8 2 15 72, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_67b24 : bv 32 := 0x0004b503.
Lemma F_67b24 : fetch_word Plain.M.loaded_segments (0x67b24 : word) = Some W_67b24.
Proof. vm_refl. Qed.
Lemma D_67b24 : decode_any W_67b24 = Some (Load SZ8 true 10 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_67b28 : bv 32 := 0x0405f593.
Lemma F_67b28 : fetch_word Plain.M.loaded_segments (0x67b28 : word) = Some W_67b28.
Proof. vm_refl. Qed.
Lemma D_67b28 : decode_any W_67b28 = Some (OpImm ALU_AND 11 11 64, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_67b2c : bv 32 := 0x00a13823.
Lemma F_67b2c : fetch_word Plain.M.loaded_segments (0x67b2c : word) = Some W_67b2c.
Proof. vm_refl. Qed.
Lemma D_67b2c : decode_any W_67b2c = Some (Store SZ8 2 10 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_67b30 : bv 32 := 0x00059c63.
Lemma F_67b30 : fetch_word Plain.M.loaded_segments (0x67b30 : word) = Some W_67b30.
Proof. vm_refl. Qed.
Lemma D_67b30 : decode_any W_67b30 = Some (Branch BC_NE 11 0 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_67b34 : bv 32 := 0x00410537.
Lemma F_67b34 : fetch_word Plain.M.loaded_segments (0x67b34 : word) = Some W_67b34.
Proof. vm_refl. Qed.
Lemma D_67b34 : decode_any W_67b34 = Some (Lui 10 1040, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_67b38 : bv 32 := 0x00a475b3.
Lemma F_67b38 : fetch_word Plain.M.loaded_segments (0x67b38 : word) = Some W_67b38.
Proof. vm_refl. Qed.
Lemma D_67b38 : decode_any W_67b38 = Some (Op ALU_AND 11 8 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_67b3c : bv 32 := 0x00a58663.
Lemma F_67b3c : fetch_word Plain.M.loaded_segments (0x67b3c : word) = Some W_67b3c.
Proof. vm_refl. Qed.
Lemma D_67b3c : decode_any W_67b3c = Some (Branch BC_EQ 11 10 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_67b40 : bv 32 := 0x00000713.
Lemma F_67b40 : fetch_word Plain.M.loaded_segments (0x67b40 : word) = Some W_67b40.
Proof. vm_refl. Qed.
Lemma D_67b40 : decode_any W_67b40 = Some (OpImm ALU_ADD 14 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_67b44 : bv 32 := 0x0080006f.
Lemma F_67b44 : fetch_word Plain.M.loaded_segments (0x67b44 : word) = Some W_67b44.
Proof. vm_refl. Qed.
Lemma D_67b44 : decode_any W_67b44 = Some (Jal 0 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_67b48 : bv 32 := 0x03016703.
Lemma F_67b48 : fetch_word Plain.M.loaded_segments (0x67b48 : word) = Some W_67b48.
Proof. vm_refl. Qed.
Lemma D_67b48 : decode_any W_67b48 = Some (Load SZ4 false 14 2 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_67b4c : bv 32 := 0x000086b7.
Lemma F_67b4c : fetch_word Plain.M.loaded_segments (0x67b4c : word) = Some W_67b4c.
Proof. vm_refl. Qed.
Lemma D_67b4c : decode_any W_67b4c = Some (Lui 13 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_67b50 : bv 32 := 0x00d466b3.
Lemma F_67b50 : fetch_word Plain.M.loaded_segments (0x67b50 : word) = Some W_67b50.
Proof. vm_refl. Qed.
Lemma D_67b50 : decode_any W_67b50 = Some (Op ALU_OR 13 8 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_67b54 : bv 32 := 0x03800513.
Lemma F_67b54 : fetch_word Plain.M.loaded_segments (0x67b54 : word) = Some W_67b54.
Proof. vm_refl. Qed.
Lemma D_67b54 : decode_any W_67b54 = Some (OpImm ALU_ADD 10 0 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_67b58 : bv 32 := 0xf9c00593.
Lemma F_67b58 : fetch_word Plain.M.loaded_segments (0x67b58 : word) = Some W_67b58.
Proof. vm_refl. Qed.
Lemma D_67b58 : decode_any W_67b58 = Some (OpImm ALU_ADD 11 0 3996, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_67b5c : bv 32 := 0x00028613.
Lemma F_67b5c : fetch_word Plain.M.loaded_segments (0x67b5c : word) = Some W_67b5c.
Proof. vm_refl. Qed.
Lemma D_67b5c : decode_any W_67b5c = Some (OpImm ALU_ADD 12 5 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_67b60 : bv 32 := 0x00000793.
Lemma F_67b60 : fetch_word Plain.M.loaded_segments (0x67b60 : word) = Some W_67b60.
Proof. vm_refl. Qed.
Lemma D_67b60 : decode_any W_67b60 = Some (OpImm ALU_ADD 15 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_67b64 : bv 32 := 0x00000813.
Lemma F_67b64 : fetch_word Plain.M.loaded_segments (0x67b64 : word) = Some W_67b64.
Proof. vm_refl. Qed.
Lemma D_67b64 : decode_any W_67b64 = Some (OpImm ALU_ADD 16 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_67b68 : bv 32 := 0x4180e0ef.
Lemma F_67b68 : fetch_word Plain.M.loaded_segments (0x67b68 : word) = Some W_67b68.
Proof. vm_refl. Qed.
Lemma D_67b68 : decode_any W_67b68 = Some (Jal 1 58392, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_67b6c : bv 32 := 0x02c41413.
Lemma F_67b6c : fetch_word Plain.M.loaded_segments (0x67b6c : word) = Some W_67b6c.
Proof. vm_refl. Qed.
Lemma D_67b6c : decode_any W_67b6c = Some (ShiftImm ALU_SLL 8 8 44, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_67b70 : bv 32 := 0x00050693.
Lemma F_67b70 : fetch_word Plain.M.loaded_segments (0x67b70 : word) = Some W_67b70.
Proof. vm_refl. Qed.
Lemma D_67b70 : decode_any W_67b70 = Some (OpImm ALU_ADD 13 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_67b74 : bv 32 := 0x02045663.
Lemma F_67b74 : fetch_word Plain.M.loaded_segments (0x67b74 : word) = Some W_67b74.
Proof. vm_refl. Qed.
Lemma D_67b74 : decode_any W_67b74 = Some (Branch BC_GE 8 0 44, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_67b78 : bv 32 := 0x80000537.
Lemma F_67b78 : fetch_word Plain.M.loaded_segments (0x67b78 : word) = Some W_67b78.
Proof. vm_refl. Qed.
Lemma D_67b78 : decode_any W_67b78 = Some (Lui 10 524288, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_67b7c : bv 32 := 0xfff5051b.
Lemma F_67b7c : fetch_word Plain.M.loaded_segments (0x67b7c : word) = Some W_67b7c.
Proof. vm_refl. Qed.
Lemma D_67b7c : decode_any W_67b7c = Some (OpImm32 10 10 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_67b80 : bv 32 := 0x00150593.
Lemma F_67b80 : fetch_word Plain.M.loaded_segments (0x67b80 : word) = Some W_67b80.
Proof. vm_refl. Qed.
Lemma D_67b80 : decode_any W_67b80 = Some (OpImm ALU_ADD 11 10 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_67b84 : bv 32 := 0x00b6f5b3.
Lemma F_67b84 : fetch_word Plain.M.loaded_segments (0x67b84 : word) = Some W_67b84.
Proof. vm_refl. Qed.
Lemma D_67b84 : decode_any W_67b84 = Some (Op ALU_AND 11 13 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_67b88 : bv 32 := 0x00059c63.
Lemma F_67b88 : fetch_word Plain.M.loaded_segments (0x67b88 : word) = Some W_67b88.
Proof. vm_refl. Qed.
Lemma D_67b88 : decode_any W_67b88 = Some (Branch BC_NE 11 0 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_67b8c : bv 32 := 0x00a6f533.
Lemma F_67b8c : fetch_word Plain.M.loaded_segments (0x67b8c : word) = Some W_67b8c.
Proof. vm_refl. Qed.
Lemma D_67b8c : decode_any W_67b8c = Some (Op ALU_AND 10 13 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_67b90 : bv 32 := 0x01900893.
Lemma F_67b90 : fetch_word Plain.M.loaded_segments (0x67b90 : word) = Some W_67b90.
Proof. vm_refl. Qed.
Lemma D_67b90 : decode_any W_67b90 = Some (OpImm ALU_ADD 17 0 25, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_67b94 : bv 32 := 0x00200593.
Lemma F_67b94 : fetch_word Plain.M.loaded_segments (0x67b94 : word) = Some W_67b94.
Proof. vm_refl. Qed.
Lemma D_67b94 : decode_any W_67b94 = Some (OpImm ALU_ADD 11 0 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_67b98 : bv 32 := 0x00100613.
Lemma F_67b98 : fetch_word Plain.M.loaded_segments (0x67b98 : word) = Some W_67b98.
Proof. vm_refl. Qed.
Lemma D_67b98 : decode_any W_67b98 = Some (OpImm ALU_ADD 12 0 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_67b9c : bv 32 := 0x00000073.
Lemma F_67b9c : fetch_word Plain.M.loaded_segments (0x67b9c : word) = Some W_67b9c.
Proof. vm_refl. Qed.
Lemma D_67b9c : decode_any W_67b9c = Some (Ecall, 4%Z).
Proof. vm_refl. Qed.
Lemma E_67b9c : is_ecall W_67b9c = true.
Proof. reflexivity. Qed.

(* [comment removed for export] *)
Definition W_67ba0 : bv 32 := 0x0006851b.
Lemma F_67ba0 : fetch_word Plain.M.loaded_segments (0x67ba0 : word) = Some W_67ba0.
Proof. vm_refl. Qed.
Lemma D_67ba0 : decode_any W_67ba0 = Some (OpImm32 10 13 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_67ba4 : bv 32 := 0x02c000ef.
Lemma F_67ba4 : fetch_word Plain.M.loaded_segments (0x67ba4 : word) = Some W_67ba4.
Proof. vm_refl. Qed.
Lemma D_67ba4 : decode_any W_67ba4 = Some (Jal 1 44, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_67ba8 : bv 32 := 0x0004b583.
Lemma F_67ba8 : fetch_word Plain.M.loaded_segments (0x67ba8 : word) = Some W_67ba8.
Proof. vm_refl. Qed.
Lemma D_67ba8 : decode_any W_67ba8 = Some (Load SZ8 true 11 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_67bac : bv 32 := 0x01013603.
Lemma F_67bac : fetch_word Plain.M.loaded_segments (0x67bac : word) = Some W_67bac.
Proof. vm_refl. Qed.
Lemma D_67bac : decode_any W_67bac = Some (Load SZ8 true 12 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_67bb0 : bv 32 := 0x00c59e63.
Lemma F_67bb0 : fetch_word Plain.M.loaded_segments (0x67bb0 : word) = Some W_67bb0.
Proof. vm_refl. Qed.
Lemma D_67bb0 : decode_any W_67bb0 = Some (Branch BC_NE 11 12 28, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_67bb4 : bv 32 := 0x0005051b.
Lemma F_67bb4 : fetch_word Plain.M.loaded_segments (0x67bb4 : word) = Some W_67bb4.
Proof. vm_refl. Qed.
Lemma D_67bb4 : decode_any W_67bb4 = Some (OpImm32 10 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_67bb8 : bv 32 := 0x02813083.
Lemma F_67bb8 : fetch_word Plain.M.loaded_segments (0x67bb8 : word) = Some W_67bb8.
Proof. vm_refl. Qed.
Lemma D_67bb8 : decode_any W_67bb8 = Some (Load SZ8 true 1 2 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_67bbc : bv 32 := 0x02013403.
Lemma F_67bbc : fetch_word Plain.M.loaded_segments (0x67bbc : word) = Some W_67bbc.
Proof. vm_refl. Qed.
Lemma D_67bbc : decode_any W_67bbc = Some (Load SZ8 true 8 2 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_67bc0 : bv 32 := 0x01813483.
Lemma F_67bc0 : fetch_word Plain.M.loaded_segments (0x67bc0 : word) = Some W_67bc0.
Proof. vm_refl. Qed.
Lemma D_67bc0 : decode_any W_67bc0 = Some (Load SZ8 true 9 2 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_67bc4 : bv 32 := 0x06010113.
Lemma F_67bc4 : fetch_word Plain.M.loaded_segments (0x67bc4 : word) = Some W_67bc4.
Proof. vm_refl. Qed.
Lemma D_67bc4 : decode_any W_67bc4 = Some (OpImm ALU_ADD 2 2 96, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_67bc8 : bv 32 := 0x00008067.
Lemma F_67bc8 : fetch_word Plain.M.loaded_segments (0x67bc8 : word) = Some W_67bc8.
Proof. vm_refl. Qed.
Lemma D_67bc8 : decode_any W_67bc8 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_67bcc : bv 32 := 0x999ff0ef.
Lemma F_67bcc : fetch_word Plain.M.loaded_segments (0x67bcc : word) = Some W_67bcc.
Proof. vm_refl. Qed.
Lemma D_67bcc : decode_any W_67bcc = Some (Jal 1 2095512, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_67bd0 : bv 32 := 0xfffff5b7.
Lemma F_67bd0 : fetch_word Plain.M.loaded_segments (0x67bd0 : word) = Some W_67bd0.
Proof. vm_refl. Qed.
Lemma D_67bd0 : decode_any W_67bd0 = Some (Lui 11 1048575, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_67bd4 : bv 32 := 0x0015859b.
Lemma F_67bd4 : fetch_word Plain.M.loaded_segments (0x67bd4 : word) = Some W_67bd4.
Proof. vm_refl. Qed.
Lemma D_67bd4 : decode_any W_67bd4 = Some (OpImm32 11 11 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_67bd8 : bv 32 := 0x02b56663.
Lemma F_67bd8 : fetch_word Plain.M.loaded_segments (0x67bd8 : word) = Some W_67bd8.
Proof. vm_refl. Qed.
Lemma D_67bd8 : decode_any W_67bd8 = Some (Branch BC_LTU 10 11 44, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_67bdc : bv 32 := 0xff010113.
Lemma F_67bdc : fetch_word Plain.M.loaded_segments (0x67bdc : word) = Some W_67bdc.
Proof. vm_refl. Qed.
Lemma D_67bdc : decode_any W_67bdc = Some (OpImm ALU_ADD 2 2 4080, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_67be0 : bv 32 := 0x00113423.
Lemma F_67be0 : fetch_word Plain.M.loaded_segments (0x67be0 : word) = Some W_67be0.
Proof. vm_refl. Qed.
Lemma D_67be0 : decode_any W_67be0 = Some (Store SZ8 2 1 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_67be4 : bv 32 := 0x00813023.
Lemma F_67be4 : fetch_word Plain.M.loaded_segments (0x67be4 : word) = Some W_67be4.
Proof. vm_refl. Qed.
Lemma D_67be4 : decode_any W_67be4 = Some (Store SZ8 2 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_67be8 : bv 32 := 0x40a0043b.
Lemma F_67be8 : fetch_word Plain.M.loaded_segments (0x67be8 : word) = Some W_67be8.
Proof. vm_refl. Qed.
Lemma D_67be8 : decode_any W_67be8 = Some (Op32 ALU_SUB 8 0 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_67bec : bv 32 := 0x981ff0ef.
Lemma F_67bec : fetch_word Plain.M.loaded_segments (0x67bec : word) = Some W_67bec.
Proof. vm_refl. Qed.
Lemma D_67bec : decode_any W_67bec = Some (Jal 1 2095488, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_67bf0 : bv 32 := 0x00852023.
Lemma F_67bf0 : fetch_word Plain.M.loaded_segments (0x67bf0 : word) = Some W_67bf0.
Proof. vm_refl. Qed.
Lemma D_67bf0 : decode_any W_67bf0 = Some (Store SZ4 10 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_67bf4 : bv 32 := 0xfff00513.
Lemma F_67bf4 : fetch_word Plain.M.loaded_segments (0x67bf4 : word) = Some W_67bf4.
Proof. vm_refl. Qed.
Lemma D_67bf4 : decode_any W_67bf4 = Some (OpImm ALU_ADD 10 0 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_67bf8 : bv 32 := 0x00813083.
Lemma F_67bf8 : fetch_word Plain.M.loaded_segments (0x67bf8 : word) = Some W_67bf8.
Proof. vm_refl. Qed.
Lemma D_67bf8 : decode_any W_67bf8 = Some (Load SZ8 true 1 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_67bfc : bv 32 := 0x00013403.
Lemma F_67bfc : fetch_word Plain.M.loaded_segments (0x67bfc : word) = Some W_67bfc.
Proof. vm_refl. Qed.
Lemma D_67bfc : decode_any W_67bfc = Some (Load SZ8 true 8 2 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_67c00 : bv 32 := 0x01010113.
Lemma F_67c00 : fetch_word Plain.M.loaded_segments (0x67c00 : word) = Some W_67c00.
Proof. vm_refl. Qed.
Lemma D_67c00 : decode_any W_67c00 = Some (OpImm ALU_ADD 2 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_67c04 : bv 32 := 0x00008067.
Lemma F_67c04 : fetch_word Plain.M.loaded_segments (0x67c04 : word) = Some W_67c04.
Proof. vm_refl. Qed.
Lemma D_67c04 : decode_any W_67c04 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.
