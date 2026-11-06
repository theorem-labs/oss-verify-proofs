(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.boost_beast.http_request.images Require Import Ubsan.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.

(* [comment removed for export] *)
Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

(* [comment removed for export] *)
Definition W_6be18 : bv 32 := 0xfa010113.
Lemma F_6be18 : fetch_word Ubsan.M.loaded_segments (0x6be18 : word) = Some W_6be18.
Proof. vm_refl. Qed.
Lemma D_6be18 : decode_any W_6be18 = Some (OpImm ALU_ADD 2 2 4000, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6be1c : bv 32 := 0x02113423.
Lemma F_6be1c : fetch_word Ubsan.M.loaded_segments (0x6be1c : word) = Some W_6be1c.
Proof. vm_refl. Qed.
Lemma D_6be1c : decode_any W_6be1c = Some (Store SZ8 2 1 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6be20 : bv 32 := 0x02813023.
Lemma F_6be20 : fetch_word Ubsan.M.loaded_segments (0x6be20 : word) = Some W_6be20.
Proof. vm_refl. Qed.
Lemma D_6be20 : decode_any W_6be20 = Some (Store SZ8 2 8 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6be24 : bv 32 := 0x00913c23.
Lemma F_6be24 : fetch_word Ubsan.M.loaded_segments (0x6be24 : word) = Some W_6be24.
Proof. vm_refl. Qed.
Lemma D_6be24 : decode_any W_6be24 = Some (Store SZ8 2 9 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6be28 : bv 32 := 0x00058413.
Lemma F_6be28 : fetch_word Ubsan.M.loaded_segments (0x6be28 : word) = Some W_6be28.
Proof. vm_refl. Qed.
Lemma D_6be28 : decode_any W_6be28 = Some (OpImm ALU_ADD 8 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6be2c : bv 32 := 0x00050293.
Lemma F_6be2c : fetch_word Ubsan.M.loaded_segments (0x6be2c : word) = Some W_6be2c.
Proof. vm_refl. Qed.
Lemma D_6be2c : decode_any W_6be2c = Some (OpImm ALU_ADD 5 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6be30 : bv 32 := 0x05013823.
Lemma F_6be30 : fetch_word Ubsan.M.loaded_segments (0x6be30 : word) = Some W_6be30.
Proof. vm_refl. Qed.
Lemma D_6be30 : decode_any W_6be30 = Some (Store SZ8 2 16 80, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6be34 : bv 32 := 0x05113c23.
Lemma F_6be34 : fetch_word Ubsan.M.loaded_segments (0x6be34 : word) = Some W_6be34.
Proof. vm_refl. Qed.
Lemma D_6be34 : decode_any W_6be34 = Some (Store SZ8 2 17 88, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6be38 : bv 32 := 0x00018517.
Lemma F_6be38 : fetch_word Ubsan.M.loaded_segments (0x6be38 : word) = Some W_6be38.
Proof. vm_refl. Qed.
Lemma D_6be38 : decode_any W_6be38 = Some (Auipc 10 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6be3c : bv 32 := 0xcf853483.
Lemma F_6be3c : fetch_word Ubsan.M.loaded_segments (0x6be3c : word) = Some W_6be3c.
Proof. vm_refl. Qed.
Lemma D_6be3c : decode_any W_6be3c = Some (Load SZ8 true 9 10 3320, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6be40 : bv 32 := 0x02c13823.
Lemma F_6be40 : fetch_word Ubsan.M.loaded_segments (0x6be40 : word) = Some W_6be40.
Proof. vm_refl. Qed.
Lemma D_6be40 : decode_any W_6be40 = Some (Store SZ8 2 12 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6be44 : bv 32 := 0x02d13c23.
Lemma F_6be44 : fetch_word Ubsan.M.loaded_segments (0x6be44 : word) = Some W_6be44.
Proof. vm_refl. Qed.
Lemma D_6be44 : decode_any W_6be44 = Some (Store SZ8 2 13 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6be48 : bv 32 := 0x04e13023.
Lemma F_6be48 : fetch_word Ubsan.M.loaded_segments (0x6be48 : word) = Some W_6be48.
Proof. vm_refl. Qed.
Lemma D_6be48 : decode_any W_6be48 = Some (Store SZ8 2 14 64, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6be4c : bv 32 := 0x04f13423.
Lemma F_6be4c : fetch_word Ubsan.M.loaded_segments (0x6be4c : word) = Some W_6be4c.
Proof. vm_refl. Qed.
Lemma D_6be4c : decode_any W_6be4c = Some (Store SZ8 2 15 72, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6be50 : bv 32 := 0x0004b503.
Lemma F_6be50 : fetch_word Ubsan.M.loaded_segments (0x6be50 : word) = Some W_6be50.
Proof. vm_refl. Qed.
Lemma D_6be50 : decode_any W_6be50 = Some (Load SZ8 true 10 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6be54 : bv 32 := 0x0405f593.
Lemma F_6be54 : fetch_word Ubsan.M.loaded_segments (0x6be54 : word) = Some W_6be54.
Proof. vm_refl. Qed.
Lemma D_6be54 : decode_any W_6be54 = Some (OpImm ALU_AND 11 11 64, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6be58 : bv 32 := 0x00a13823.
Lemma F_6be58 : fetch_word Ubsan.M.loaded_segments (0x6be58 : word) = Some W_6be58.
Proof. vm_refl. Qed.
Lemma D_6be58 : decode_any W_6be58 = Some (Store SZ8 2 10 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6be5c : bv 32 := 0x00059c63.
Lemma F_6be5c : fetch_word Ubsan.M.loaded_segments (0x6be5c : word) = Some W_6be5c.
Proof. vm_refl. Qed.
Lemma D_6be5c : decode_any W_6be5c = Some (Branch BC_NE 11 0 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6be60 : bv 32 := 0x00410537.
Lemma F_6be60 : fetch_word Ubsan.M.loaded_segments (0x6be60 : word) = Some W_6be60.
Proof. vm_refl. Qed.
Lemma D_6be60 : decode_any W_6be60 = Some (Lui 10 1040, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6be64 : bv 32 := 0x00a475b3.
Lemma F_6be64 : fetch_word Ubsan.M.loaded_segments (0x6be64 : word) = Some W_6be64.
Proof. vm_refl. Qed.
Lemma D_6be64 : decode_any W_6be64 = Some (Op ALU_AND 11 8 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6be68 : bv 32 := 0x00a58663.
Lemma F_6be68 : fetch_word Ubsan.M.loaded_segments (0x6be68 : word) = Some W_6be68.
Proof. vm_refl. Qed.
Lemma D_6be68 : decode_any W_6be68 = Some (Branch BC_EQ 11 10 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6be6c : bv 32 := 0x00000713.
Lemma F_6be6c : fetch_word Ubsan.M.loaded_segments (0x6be6c : word) = Some W_6be6c.
Proof. vm_refl. Qed.
Lemma D_6be6c : decode_any W_6be6c = Some (OpImm ALU_ADD 14 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6be70 : bv 32 := 0x0080006f.
Lemma F_6be70 : fetch_word Ubsan.M.loaded_segments (0x6be70 : word) = Some W_6be70.
Proof. vm_refl. Qed.
Lemma D_6be70 : decode_any W_6be70 = Some (Jal 0 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6be74 : bv 32 := 0x03016703.
Lemma F_6be74 : fetch_word Ubsan.M.loaded_segments (0x6be74 : word) = Some W_6be74.
Proof. vm_refl. Qed.
Lemma D_6be74 : decode_any W_6be74 = Some (Load SZ4 false 14 2 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6be78 : bv 32 := 0x000086b7.
Lemma F_6be78 : fetch_word Ubsan.M.loaded_segments (0x6be78 : word) = Some W_6be78.
Proof. vm_refl. Qed.
Lemma D_6be78 : decode_any W_6be78 = Some (Lui 13 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6be7c : bv 32 := 0x00d466b3.
Lemma F_6be7c : fetch_word Ubsan.M.loaded_segments (0x6be7c : word) = Some W_6be7c.
Proof. vm_refl. Qed.
Lemma D_6be7c : decode_any W_6be7c = Some (Op ALU_OR 13 8 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6be80 : bv 32 := 0x03800513.
Lemma F_6be80 : fetch_word Ubsan.M.loaded_segments (0x6be80 : word) = Some W_6be80.
Proof. vm_refl. Qed.
Lemma D_6be80 : decode_any W_6be80 = Some (OpImm ALU_ADD 10 0 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6be84 : bv 32 := 0xf9c00593.
Lemma F_6be84 : fetch_word Ubsan.M.loaded_segments (0x6be84 : word) = Some W_6be84.
Proof. vm_refl. Qed.
Lemma D_6be84 : decode_any W_6be84 = Some (OpImm ALU_ADD 11 0 3996, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6be88 : bv 32 := 0x00028613.
Lemma F_6be88 : fetch_word Ubsan.M.loaded_segments (0x6be88 : word) = Some W_6be88.
Proof. vm_refl. Qed.
Lemma D_6be88 : decode_any W_6be88 = Some (OpImm ALU_ADD 12 5 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6be8c : bv 32 := 0x00000793.
Lemma F_6be8c : fetch_word Ubsan.M.loaded_segments (0x6be8c : word) = Some W_6be8c.
Proof. vm_refl. Qed.
Lemma D_6be8c : decode_any W_6be8c = Some (OpImm ALU_ADD 15 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6be90 : bv 32 := 0x00000813.
Lemma F_6be90 : fetch_word Ubsan.M.loaded_segments (0x6be90 : word) = Some W_6be90.
Proof. vm_refl. Qed.
Lemma D_6be90 : decode_any W_6be90 = Some (OpImm ALU_ADD 16 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6be94 : bv 32 := 0x4180e0ef.
Lemma F_6be94 : fetch_word Ubsan.M.loaded_segments (0x6be94 : word) = Some W_6be94.
Proof. vm_refl. Qed.
Lemma D_6be94 : decode_any W_6be94 = Some (Jal 1 58392, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6be98 : bv 32 := 0x02c41413.
Lemma F_6be98 : fetch_word Ubsan.M.loaded_segments (0x6be98 : word) = Some W_6be98.
Proof. vm_refl. Qed.
Lemma D_6be98 : decode_any W_6be98 = Some (ShiftImm ALU_SLL 8 8 44, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6be9c : bv 32 := 0x00050693.
Lemma F_6be9c : fetch_word Ubsan.M.loaded_segments (0x6be9c : word) = Some W_6be9c.
Proof. vm_refl. Qed.
Lemma D_6be9c : decode_any W_6be9c = Some (OpImm ALU_ADD 13 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6bea0 : bv 32 := 0x02045663.
Lemma F_6bea0 : fetch_word Ubsan.M.loaded_segments (0x6bea0 : word) = Some W_6bea0.
Proof. vm_refl. Qed.
Lemma D_6bea0 : decode_any W_6bea0 = Some (Branch BC_GE 8 0 44, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6bea4 : bv 32 := 0x80000537.
Lemma F_6bea4 : fetch_word Ubsan.M.loaded_segments (0x6bea4 : word) = Some W_6bea4.
Proof. vm_refl. Qed.
Lemma D_6bea4 : decode_any W_6bea4 = Some (Lui 10 524288, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6bea8 : bv 32 := 0xfff5051b.
Lemma F_6bea8 : fetch_word Ubsan.M.loaded_segments (0x6bea8 : word) = Some W_6bea8.
Proof. vm_refl. Qed.
Lemma D_6bea8 : decode_any W_6bea8 = Some (OpImm32 10 10 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6beac : bv 32 := 0x00150593.
Lemma F_6beac : fetch_word Ubsan.M.loaded_segments (0x6beac : word) = Some W_6beac.
Proof. vm_refl. Qed.
Lemma D_6beac : decode_any W_6beac = Some (OpImm ALU_ADD 11 10 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6beb0 : bv 32 := 0x00b6f5b3.
Lemma F_6beb0 : fetch_word Ubsan.M.loaded_segments (0x6beb0 : word) = Some W_6beb0.
Proof. vm_refl. Qed.
Lemma D_6beb0 : decode_any W_6beb0 = Some (Op ALU_AND 11 13 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6beb4 : bv 32 := 0x00059c63.
Lemma F_6beb4 : fetch_word Ubsan.M.loaded_segments (0x6beb4 : word) = Some W_6beb4.
Proof. vm_refl. Qed.
Lemma D_6beb4 : decode_any W_6beb4 = Some (Branch BC_NE 11 0 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6beb8 : bv 32 := 0x00a6f533.
Lemma F_6beb8 : fetch_word Ubsan.M.loaded_segments (0x6beb8 : word) = Some W_6beb8.
Proof. vm_refl. Qed.
Lemma D_6beb8 : decode_any W_6beb8 = Some (Op ALU_AND 10 13 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6bebc : bv 32 := 0x01900893.
Lemma F_6bebc : fetch_word Ubsan.M.loaded_segments (0x6bebc : word) = Some W_6bebc.
Proof. vm_refl. Qed.
Lemma D_6bebc : decode_any W_6bebc = Some (OpImm ALU_ADD 17 0 25, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6bec0 : bv 32 := 0x00200593.
Lemma F_6bec0 : fetch_word Ubsan.M.loaded_segments (0x6bec0 : word) = Some W_6bec0.
Proof. vm_refl. Qed.
Lemma D_6bec0 : decode_any W_6bec0 = Some (OpImm ALU_ADD 11 0 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6bec4 : bv 32 := 0x00100613.
Lemma F_6bec4 : fetch_word Ubsan.M.loaded_segments (0x6bec4 : word) = Some W_6bec4.
Proof. vm_refl. Qed.
Lemma D_6bec4 : decode_any W_6bec4 = Some (OpImm ALU_ADD 12 0 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6bec8 : bv 32 := 0x00000073.
Lemma F_6bec8 : fetch_word Ubsan.M.loaded_segments (0x6bec8 : word) = Some W_6bec8.
Proof. vm_refl. Qed.
Lemma D_6bec8 : decode_any W_6bec8 = Some (Ecall, 4%Z).
Proof. vm_refl. Qed.
Lemma E_6bec8 : is_ecall W_6bec8 = true.
Proof. reflexivity. Qed.

(* [comment removed for export] *)
Definition W_6becc : bv 32 := 0x0006851b.
Lemma F_6becc : fetch_word Ubsan.M.loaded_segments (0x6becc : word) = Some W_6becc.
Proof. vm_refl. Qed.
Lemma D_6becc : decode_any W_6becc = Some (OpImm32 10 13 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6bed0 : bv 32 := 0x02c000ef.
Lemma F_6bed0 : fetch_word Ubsan.M.loaded_segments (0x6bed0 : word) = Some W_6bed0.
Proof. vm_refl. Qed.
Lemma D_6bed0 : decode_any W_6bed0 = Some (Jal 1 44, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6bed4 : bv 32 := 0x0004b583.
Lemma F_6bed4 : fetch_word Ubsan.M.loaded_segments (0x6bed4 : word) = Some W_6bed4.
Proof. vm_refl. Qed.
Lemma D_6bed4 : decode_any W_6bed4 = Some (Load SZ8 true 11 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6bed8 : bv 32 := 0x01013603.
Lemma F_6bed8 : fetch_word Ubsan.M.loaded_segments (0x6bed8 : word) = Some W_6bed8.
Proof. vm_refl. Qed.
Lemma D_6bed8 : decode_any W_6bed8 = Some (Load SZ8 true 12 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6bedc : bv 32 := 0x00c59e63.
Lemma F_6bedc : fetch_word Ubsan.M.loaded_segments (0x6bedc : word) = Some W_6bedc.
Proof. vm_refl. Qed.
Lemma D_6bedc : decode_any W_6bedc = Some (Branch BC_NE 11 12 28, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6bee0 : bv 32 := 0x0005051b.
Lemma F_6bee0 : fetch_word Ubsan.M.loaded_segments (0x6bee0 : word) = Some W_6bee0.
Proof. vm_refl. Qed.
Lemma D_6bee0 : decode_any W_6bee0 = Some (OpImm32 10 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6bee4 : bv 32 := 0x02813083.
Lemma F_6bee4 : fetch_word Ubsan.M.loaded_segments (0x6bee4 : word) = Some W_6bee4.
Proof. vm_refl. Qed.
Lemma D_6bee4 : decode_any W_6bee4 = Some (Load SZ8 true 1 2 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6bee8 : bv 32 := 0x02013403.
Lemma F_6bee8 : fetch_word Ubsan.M.loaded_segments (0x6bee8 : word) = Some W_6bee8.
Proof. vm_refl. Qed.
Lemma D_6bee8 : decode_any W_6bee8 = Some (Load SZ8 true 8 2 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6beec : bv 32 := 0x01813483.
Lemma F_6beec : fetch_word Ubsan.M.loaded_segments (0x6beec : word) = Some W_6beec.
Proof. vm_refl. Qed.
Lemma D_6beec : decode_any W_6beec = Some (Load SZ8 true 9 2 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6bef0 : bv 32 := 0x06010113.
Lemma F_6bef0 : fetch_word Ubsan.M.loaded_segments (0x6bef0 : word) = Some W_6bef0.
Proof. vm_refl. Qed.
Lemma D_6bef0 : decode_any W_6bef0 = Some (OpImm ALU_ADD 2 2 96, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6bef4 : bv 32 := 0x00008067.
Lemma F_6bef4 : fetch_word Ubsan.M.loaded_segments (0x6bef4 : word) = Some W_6bef4.
Proof. vm_refl. Qed.
Lemma D_6bef4 : decode_any W_6bef4 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6bef8 : bv 32 := 0x999ff0ef.
Lemma F_6bef8 : fetch_word Ubsan.M.loaded_segments (0x6bef8 : word) = Some W_6bef8.
Proof. vm_refl. Qed.
Lemma D_6bef8 : decode_any W_6bef8 = Some (Jal 1 2095512, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6befc : bv 32 := 0xfffff5b7.
Lemma F_6befc : fetch_word Ubsan.M.loaded_segments (0x6befc : word) = Some W_6befc.
Proof. vm_refl. Qed.
Lemma D_6befc : decode_any W_6befc = Some (Lui 11 1048575, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6bf00 : bv 32 := 0x0015859b.
Lemma F_6bf00 : fetch_word Ubsan.M.loaded_segments (0x6bf00 : word) = Some W_6bf00.
Proof. vm_refl. Qed.
Lemma D_6bf00 : decode_any W_6bf00 = Some (OpImm32 11 11 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6bf04 : bv 32 := 0x02b56663.
Lemma F_6bf04 : fetch_word Ubsan.M.loaded_segments (0x6bf04 : word) = Some W_6bf04.
Proof. vm_refl. Qed.
Lemma D_6bf04 : decode_any W_6bf04 = Some (Branch BC_LTU 10 11 44, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6bf08 : bv 32 := 0xff010113.
Lemma F_6bf08 : fetch_word Ubsan.M.loaded_segments (0x6bf08 : word) = Some W_6bf08.
Proof. vm_refl. Qed.
Lemma D_6bf08 : decode_any W_6bf08 = Some (OpImm ALU_ADD 2 2 4080, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6bf0c : bv 32 := 0x00113423.
Lemma F_6bf0c : fetch_word Ubsan.M.loaded_segments (0x6bf0c : word) = Some W_6bf0c.
Proof. vm_refl. Qed.
Lemma D_6bf0c : decode_any W_6bf0c = Some (Store SZ8 2 1 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6bf10 : bv 32 := 0x00813023.
Lemma F_6bf10 : fetch_word Ubsan.M.loaded_segments (0x6bf10 : word) = Some W_6bf10.
Proof. vm_refl. Qed.
Lemma D_6bf10 : decode_any W_6bf10 = Some (Store SZ8 2 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6bf14 : bv 32 := 0x40a0043b.
Lemma F_6bf14 : fetch_word Ubsan.M.loaded_segments (0x6bf14 : word) = Some W_6bf14.
Proof. vm_refl. Qed.
Lemma D_6bf14 : decode_any W_6bf14 = Some (Op32 ALU_SUB 8 0 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6bf18 : bv 32 := 0x981ff0ef.
Lemma F_6bf18 : fetch_word Ubsan.M.loaded_segments (0x6bf18 : word) = Some W_6bf18.
Proof. vm_refl. Qed.
Lemma D_6bf18 : decode_any W_6bf18 = Some (Jal 1 2095488, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6bf1c : bv 32 := 0x00852023.
Lemma F_6bf1c : fetch_word Ubsan.M.loaded_segments (0x6bf1c : word) = Some W_6bf1c.
Proof. vm_refl. Qed.
Lemma D_6bf1c : decode_any W_6bf1c = Some (Store SZ4 10 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6bf20 : bv 32 := 0xfff00513.
Lemma F_6bf20 : fetch_word Ubsan.M.loaded_segments (0x6bf20 : word) = Some W_6bf20.
Proof. vm_refl. Qed.
Lemma D_6bf20 : decode_any W_6bf20 = Some (OpImm ALU_ADD 10 0 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6bf24 : bv 32 := 0x00813083.
Lemma F_6bf24 : fetch_word Ubsan.M.loaded_segments (0x6bf24 : word) = Some W_6bf24.
Proof. vm_refl. Qed.
Lemma D_6bf24 : decode_any W_6bf24 = Some (Load SZ8 true 1 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6bf28 : bv 32 := 0x00013403.
Lemma F_6bf28 : fetch_word Ubsan.M.loaded_segments (0x6bf28 : word) = Some W_6bf28.
Proof. vm_refl. Qed.
Lemma D_6bf28 : decode_any W_6bf28 = Some (Load SZ8 true 8 2 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6bf2c : bv 32 := 0x01010113.
Lemma F_6bf2c : fetch_word Ubsan.M.loaded_segments (0x6bf2c : word) = Some W_6bf2c.
Proof. vm_refl. Qed.
Lemma D_6bf2c : decode_any W_6bf2c = Some (OpImm ALU_ADD 2 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6bf30 : bv 32 := 0x00008067.
Lemma F_6bf30 : fetch_word Ubsan.M.loaded_segments (0x6bf30 : word) = Some W_6bf30.
Proof. vm_refl. Qed.
Lemma D_6bf30 : decode_any W_6bf30 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.
