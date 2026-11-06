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
Definition W_6f2f4 : bv 32 := 0xf9010113.
Lemma F_6f2f4 : fetch_word Ubsan.M.loaded_segments (0x6f2f4 : word) = Some W_6f2f4.
Proof. vm_refl. Qed.
Lemma D_6f2f4 : decode_any W_6f2f4 = Some (OpImm ALU_ADD 2 2 3984, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6f2f8 : bv 32 := 0x06113423.
Lemma F_6f2f8 : fetch_word Ubsan.M.loaded_segments (0x6f2f8 : word) = Some W_6f2f8.
Proof. vm_refl. Qed.
Lemma D_6f2f8 : decode_any W_6f2f8 = Some (Store SZ8 2 1 104, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6f2fc : bv 32 := 0x06813023.
Lemma F_6f2fc : fetch_word Ubsan.M.loaded_segments (0x6f2fc : word) = Some W_6f2fc.
Proof. vm_refl. Qed.
Lemma D_6f2fc : decode_any W_6f2fc = Some (Store SZ8 2 8 96, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6f300 : bv 32 := 0x04913c23.
Lemma F_6f300 : fetch_word Ubsan.M.loaded_segments (0x6f300 : word) = Some W_6f300.
Proof. vm_refl. Qed.
Lemma D_6f300 : decode_any W_6f300 = Some (Store SZ8 2 9 88, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6f304 : bv 32 := 0x05213823.
Lemma F_6f304 : fetch_word Ubsan.M.loaded_segments (0x6f304 : word) = Some W_6f304.
Proof. vm_refl. Qed.
Lemma D_6f304 : decode_any W_6f304 = Some (Store SZ8 2 18 80, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6f308 : bv 32 := 0x05313423.
Lemma F_6f308 : fetch_word Ubsan.M.loaded_segments (0x6f308 : word) = Some W_6f308.
Proof. vm_refl. Qed.
Lemma D_6f308 : decode_any W_6f308 = Some (Store SZ8 2 19 72, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6f30c : bv 32 := 0x05413023.
Lemma F_6f30c : fetch_word Ubsan.M.loaded_segments (0x6f30c : word) = Some W_6f30c.
Proof. vm_refl. Qed.
Lemma D_6f30c : decode_any W_6f30c = Some (Store SZ8 2 20 64, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6f310 : bv 32 := 0x03513c23.
Lemma F_6f310 : fetch_word Ubsan.M.loaded_segments (0x6f310 : word) = Some W_6f310.
Proof. vm_refl. Qed.
Lemma D_6f310 : decode_any W_6f310 = Some (Store SZ8 2 21 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6f314 : bv 32 := 0x03613823.
Lemma F_6f314 : fetch_word Ubsan.M.loaded_segments (0x6f314 : word) = Some W_6f314.
Proof. vm_refl. Qed.
Lemma D_6f314 : decode_any W_6f314 = Some (Store SZ8 2 22 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6f318 : bv 32 := 0x00060413.
Lemma F_6f318 : fetch_word Ubsan.M.loaded_segments (0x6f318 : word) = Some W_6f318.
Proof. vm_refl. Qed.
Lemma D_6f318 : decode_any W_6f318 = Some (OpImm ALU_ADD 8 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6f31c : bv 32 := 0x00050493.
Lemma F_6f31c : fetch_word Ubsan.M.loaded_segments (0x6f31c : word) = Some W_6f31c.
Proof. vm_refl. Qed.
Lemma D_6f31c : decode_any W_6f31c = Some (OpImm ALU_ADD 9 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6f320 : bv 32 := 0x00015517.
Lemma F_6f320 : fetch_word Ubsan.M.loaded_segments (0x6f320 : word) = Some W_6f320.
Proof. vm_refl. Qed.
Lemma D_6f320 : decode_any W_6f320 = Some (Auipc 10 21, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6f324 : bv 32 := 0x81053a83.
Lemma F_6f324 : fetch_word Ubsan.M.loaded_segments (0x6f324 : word) = Some W_6f324.
Proof. vm_refl. Qed.
Lemma D_6f324 : decode_any W_6f324 = Some (Load SZ8 true 21 10 2064, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6f328 : bv 32 := 0x000ab503.
Lemma F_6f328 : fetch_word Ubsan.M.loaded_segments (0x6f328 : word) = Some W_6f328.
Proof. vm_refl. Qed.
Lemma D_6f328 : decode_any W_6f328 = Some (Load SZ8 true 10 21 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6f32c : bv 32 := 0x02a13423.
Lemma F_6f32c : fetch_word Ubsan.M.loaded_segments (0x6f32c : word) = Some W_6f32c.
Proof. vm_refl. Qed.
Lemma D_6f32c : decode_any W_6f32c = Some (Store SZ8 2 10 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6f330 : bv 32 := 0x0284b503.
Lemma F_6f330 : fetch_word Ubsan.M.loaded_segments (0x6f330 : word) = Some W_6f330.
Proof. vm_refl. Qed.
Lemma D_6f330 : decode_any W_6f330 = Some (Load SZ8 true 10 9 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6f334 : bv 32 := 0x0384b603.
Lemma F_6f334 : fetch_word Ubsan.M.loaded_segments (0x6f334 : word) = Some W_6f334.
Proof. vm_refl. Qed.
Lemma D_6f334 : decode_any W_6f334 = Some (Load SZ8 true 12 9 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6f338 : bv 32 := 0x40c50b33.
Lemma F_6f338 : fetch_word Ubsan.M.loaded_segments (0x6f338 : word) = Some W_6f338.
Proof. vm_refl. Qed.
Lemma D_6f338 : decode_any W_6f338 = Some (Op ALU_SUB 22 10 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6f33c : bv 32 := 0x00c546b3.
Lemma F_6f33c : fetch_word Ubsan.M.loaded_segments (0x6f33c : word) = Some W_6f33c.
Proof. vm_refl. Qed.
Lemma D_6f33c : decode_any W_6f33c = Some (Op ALU_XOR 13 10 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6f340 : bv 32 := 0x00c13423.
Lemma F_6f340 : fetch_word Ubsan.M.loaded_segments (0x6f340 : word) = Some W_6f340.
Proof. vm_refl. Qed.
Lemma D_6f340 : decode_any W_6f340 = Some (Store SZ8 2 12 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6f344 : bv 32 := 0x01613823.
Lemma F_6f344 : fetch_word Ubsan.M.loaded_segments (0x6f344 : word) = Some W_6f344.
Proof. vm_refl. Qed.
Lemma D_6f344 : decode_any W_6f344 = Some (Store SZ8 2 22 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6f348 : bv 32 := 0x00b13c23.
Lemma F_6f348 : fetch_word Ubsan.M.loaded_segments (0x6f348 : word) = Some W_6f348.
Proof. vm_refl. Qed.
Lemma D_6f348 : decode_any W_6f348 = Some (Store SZ8 2 11 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6f34c : bv 32 := 0x02813023.
Lemma F_6f34c : fetch_word Ubsan.M.loaded_segments (0x6f34c : word) = Some W_6f34c.
Proof. vm_refl. Qed.
Lemma D_6f34c : decode_any W_6f34c = Some (Store SZ8 2 8 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6f350 : bv 32 := 0x008b0b33.
Lemma F_6f350 : fetch_word Ubsan.M.loaded_segments (0x6f350 : word) = Some W_6f350.
Proof. vm_refl. Qed.
Lemma D_6f350 : decode_any W_6f350 = Some (Op ALU_ADD 22 22 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6f354 : bv 32 := 0x00d03933.
Lemma F_6f354 : fetch_word Ubsan.M.loaded_segments (0x6f354 : word) = Some W_6f354.
Proof. vm_refl. Qed.
Lemma D_6f354 : decode_any W_6f354 = Some (Op ALU_SLTU 18 0 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6f358 : bv 32 := 0x00c50663.
Lemma F_6f358 : fetch_word Ubsan.M.loaded_segments (0x6f358 : word) = Some W_6f358.
Proof. vm_refl. Qed.
Lemma D_6f358 : decode_any W_6f358 = Some (Branch BC_EQ 10 12 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6f35c : bv 32 := 0x00810993.
Lemma F_6f35c : fetch_word Ubsan.M.loaded_segments (0x6f35c : word) = Some W_6f35c.
Proof. vm_refl. Qed.
Lemma D_6f35c : decode_any W_6f35c = Some (OpImm ALU_ADD 19 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6f360 : bv 32 := 0x0080006f.
Lemma F_6f360 : fetch_word Ubsan.M.loaded_segments (0x6f360 : word) = Some W_6f360.
Proof. vm_refl. Qed.
Lemma D_6f360 : decode_any W_6f360 = Some (Jal 0 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6f364 : bv 32 := 0x01810993.
Lemma F_6f364 : fetch_word Ubsan.M.loaded_segments (0x6f364 : word) = Some W_6f364.
Proof. vm_refl. Qed.
Lemma D_6f364 : decode_any W_6f364 = Some (OpImm ALU_ADD 19 2 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6f368 : bv 32 := 0x0784a503.
Lemma F_6f368 : fetch_word Ubsan.M.loaded_segments (0x6f368 : word) = Some W_6f368.
Proof. vm_refl. Qed.
Lemma D_6f368 : decode_any W_6f368 = Some (Load SZ4 true 10 9 120, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6f36c : bv 32 := 0x00190913.
Lemma F_6f36c : fetch_word Ubsan.M.loaded_segments (0x6f36c : word) = Some W_6f36c.
Proof. vm_refl. Qed.
Lemma D_6f36c : decode_any W_6f36c = Some (OpImm ALU_ADD 18 18 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6f370 : bv 32 := 0x04200893.
Lemma F_6f370 : fetch_word Ubsan.M.loaded_segments (0x6f370 : word) = Some W_6f370.
Proof. vm_refl. Qed.
Lemma D_6f370 : decode_any W_6f370 = Some (OpImm ALU_ADD 17 0 66, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6f374 : bv 32 := 0x00098593.
Lemma F_6f374 : fetch_word Ubsan.M.loaded_segments (0x6f374 : word) = Some W_6f374.
Proof. vm_refl. Qed.
Lemma D_6f374 : decode_any W_6f374 = Some (OpImm ALU_ADD 11 19 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6f378 : bv 32 := 0x00090613.
Lemma F_6f378 : fetch_word Ubsan.M.loaded_segments (0x6f378 : word) = Some W_6f378.
Proof. vm_refl. Qed.
Lemma D_6f378 : decode_any W_6f378 = Some (OpImm ALU_ADD 12 18 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6f37c : bv 32 := 0x00000073.
Lemma F_6f37c : fetch_word Ubsan.M.loaded_segments (0x6f37c : word) = Some W_6f37c.
Proof. vm_refl. Qed.
Lemma D_6f37c : decode_any W_6f37c = Some (Ecall, 4%Z).
Proof. vm_refl. Qed.
Lemma E_6f37c : is_ecall W_6f37c = true.
Proof. reflexivity. Qed.

(* [comment removed for export] *)
Definition W_6f380 : bv 32 := 0xb7dfc0ef.
Lemma F_6f380 : fetch_word Ubsan.M.loaded_segments (0x6f380 : word) = Some W_6f380.
Proof. vm_refl. Qed.
Lemma D_6f380 : decode_any W_6f380 = Some (Jal 1 2083708, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6f384 : bv 32 := 0x09651863.
Lemma F_6f384 : fetch_word Ubsan.M.loaded_segments (0x6f384 : word) = Some W_6f384.
Proof. vm_refl. Qed.
Lemma D_6f384 : decode_any W_6f384 = Some (Branch BC_NE 10 22 144, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6f388 : bv 32 := 0x0584b503.
Lemma F_6f388 : fetch_word Ubsan.M.loaded_segments (0x6f388 : word) = Some W_6f388.
Proof. vm_refl. Qed.
Lemma D_6f388 : decode_any W_6f388 = Some (Load SZ8 true 10 9 88, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6f38c : bv 32 := 0x0604b583.
Lemma F_6f38c : fetch_word Ubsan.M.loaded_segments (0x6f38c : word) = Some W_6f38c.
Proof. vm_refl. Qed.
Lemma D_6f38c : decode_any W_6f38c = Some (Load SZ8 true 11 9 96, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6f390 : bv 32 := 0x00b505b3.
Lemma F_6f390 : fetch_word Ubsan.M.loaded_segments (0x6f390 : word) = Some W_6f390.
Proof. vm_refl. Qed.
Lemma D_6f390 : decode_any W_6f390 = Some (Op ALU_ADD 11 10 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6f394 : bv 32 := 0x02b4b023.
Lemma F_6f394 : fetch_word Ubsan.M.loaded_segments (0x6f394 : word) = Some W_6f394.
Proof. vm_refl. Qed.
Lemma D_6f394 : decode_any W_6f394 = Some (Store SZ8 9 11 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6f398 : bv 32 := 0x02a4b423.
Lemma F_6f398 : fetch_word Ubsan.M.loaded_segments (0x6f398 : word) = Some W_6f398.
Proof. vm_refl. Qed.
Lemma D_6f398 : decode_any W_6f398 = Some (Store SZ8 9 10 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6f39c : bv 32 := 0x02a4bc23.
Lemma F_6f39c : fetch_word Ubsan.M.loaded_segments (0x6f39c : word) = Some W_6f39c.
Proof. vm_refl. Qed.
Lemma D_6f39c : decode_any W_6f39c = Some (Store SZ8 9 10 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6f3a0 : bv 32 := 0x00040513.
Lemma F_6f3a0 : fetch_word Ubsan.M.loaded_segments (0x6f3a0 : word) = Some W_6f3a0.
Proof. vm_refl. Qed.
Lemma D_6f3a0 : decode_any W_6f3a0 = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6f3a4 : bv 32 := 0x000ab583.
Lemma F_6f3a4 : fetch_word Ubsan.M.loaded_segments (0x6f3a4 : word) = Some W_6f3a4.
Proof. vm_refl. Qed.
Lemma D_6f3a4 : decode_any W_6f3a4 = Some (Load SZ8 true 11 21 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6f3a8 : bv 32 := 0x02813603.
Lemma F_6f3a8 : fetch_word Ubsan.M.loaded_segments (0x6f3a8 : word) = Some W_6f3a8.
Proof. vm_refl. Qed.
Lemma D_6f3a8 : decode_any W_6f3a8 = Some (Load SZ8 true 12 2 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6f3ac : bv 32 := 0x0cc59a63.
Lemma F_6f3ac : fetch_word Ubsan.M.loaded_segments (0x6f3ac : word) = Some W_6f3ac.
Proof. vm_refl. Qed.
Lemma D_6f3ac : decode_any W_6f3ac = Some (Branch BC_NE 11 12 212, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6f3b0 : bv 32 := 0x06813083.
Lemma F_6f3b0 : fetch_word Ubsan.M.loaded_segments (0x6f3b0 : word) = Some W_6f3b0.
Proof. vm_refl. Qed.
Lemma D_6f3b0 : decode_any W_6f3b0 = Some (Load SZ8 true 1 2 104, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6f3b4 : bv 32 := 0x06013403.
Lemma F_6f3b4 : fetch_word Ubsan.M.loaded_segments (0x6f3b4 : word) = Some W_6f3b4.
Proof. vm_refl. Qed.
Lemma D_6f3b4 : decode_any W_6f3b4 = Some (Load SZ8 true 8 2 96, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6f3b8 : bv 32 := 0x05813483.
Lemma F_6f3b8 : fetch_word Ubsan.M.loaded_segments (0x6f3b8 : word) = Some W_6f3b8.
Proof. vm_refl. Qed.
Lemma D_6f3b8 : decode_any W_6f3b8 = Some (Load SZ8 true 9 2 88, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6f3bc : bv 32 := 0x05013903.
Lemma F_6f3bc : fetch_word Ubsan.M.loaded_segments (0x6f3bc : word) = Some W_6f3bc.
Proof. vm_refl. Qed.
Lemma D_6f3bc : decode_any W_6f3bc = Some (Load SZ8 true 18 2 80, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6f3c0 : bv 32 := 0x04813983.
Lemma F_6f3c0 : fetch_word Ubsan.M.loaded_segments (0x6f3c0 : word) = Some W_6f3c0.
Proof. vm_refl. Qed.
Lemma D_6f3c0 : decode_any W_6f3c0 = Some (Load SZ8 true 19 2 72, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6f3c4 : bv 32 := 0x04013a03.
Lemma F_6f3c4 : fetch_word Ubsan.M.loaded_segments (0x6f3c4 : word) = Some W_6f3c4.
Proof. vm_refl. Qed.
Lemma D_6f3c4 : decode_any W_6f3c4 = Some (Load SZ8 true 20 2 64, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6f3c8 : bv 32 := 0x03813a83.
Lemma F_6f3c8 : fetch_word Ubsan.M.loaded_segments (0x6f3c8 : word) = Some W_6f3c8.
Proof. vm_refl. Qed.
Lemma D_6f3c8 : decode_any W_6f3c8 = Some (Load SZ8 true 21 2 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6f3cc : bv 32 := 0x03013b03.
Lemma F_6f3cc : fetch_word Ubsan.M.loaded_segments (0x6f3cc : word) = Some W_6f3cc.
Proof. vm_refl. Qed.
Lemma D_6f3cc : decode_any W_6f3cc = Some (Load SZ8 true 22 2 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6f3d0 : bv 32 := 0x07010113.
Lemma F_6f3d0 : fetch_word Ubsan.M.loaded_segments (0x6f3d0 : word) = Some W_6f3d0.
Proof. vm_refl. Qed.
Lemma D_6f3d0 : decode_any W_6f3d0 = Some (OpImm ALU_ADD 2 2 112, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6f3d4 : bv 32 := 0x00008067.
Lemma F_6f3d4 : fetch_word Ubsan.M.loaded_segments (0x6f3d4 : word) = Some W_6f3d4.
Proof. vm_refl. Qed.
Lemma D_6f3d4 : decode_any W_6f3d4 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6f3d8 : bv 32 := 0x00800713.
Lemma F_6f3d8 : fetch_word Ubsan.M.loaded_segments (0x6f3d8 : word) = Some W_6f3d8.
Proof. vm_refl. Qed.
Lemma D_6f3d8 : decode_any W_6f3d8 = Some (OpImm ALU_ADD 14 0 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6f3dc : bv 32 := 0x000a0593.
Lemma F_6f3dc : fetch_word Ubsan.M.loaded_segments (0x6f3dc : word) = Some W_6f3dc.
Proof. vm_refl. Qed.
Lemma D_6f3dc : decode_any W_6f3dc = Some (OpImm ALU_ADD 11 20 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6f3e0 : bv 32 := 0x00e98733.
Lemma F_6f3e0 : fetch_word Ubsan.M.loaded_segments (0x6f3e0 : word) = Some W_6f3e0.
Proof. vm_refl. Qed.
Lemma D_6f3e0 : decode_any W_6f3e0 = Some (Op ALU_ADD 14 19 14, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6f3e4 : bv 32 := 0x00073783.
Lemma F_6f3e4 : fetch_word Ubsan.M.loaded_segments (0x6f3e4 : word) = Some W_6f3e4.
Proof. vm_refl. Qed.
Lemma D_6f3e4 : decode_any W_6f3e4 = Some (Load SZ8 true 15 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6f3e8 : bv 32 := 0x40ab0b33.
Lemma F_6f3e8 : fetch_word Ubsan.M.loaded_segments (0x6f3e8 : word) = Some W_6f3e8.
Proof. vm_refl. Qed.
Lemma D_6f3e8 : decode_any W_6f3e8 = Some (Op ALU_SUB 22 22 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6f3ec : bv 32 := 0x0784a503.
Lemma F_6f3ec : fetch_word Ubsan.M.loaded_segments (0x6f3ec : word) = Some W_6f3ec.
Proof. vm_refl. Qed.
Lemma D_6f3ec : decode_any W_6f3ec = Some (Load SZ4 true 10 9 120, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6f3f0 : bv 32 := 0x40c9093b.
Lemma F_6f3f0 : fetch_word Ubsan.M.loaded_segments (0x6f3f0 : word) = Some W_6f3f0.
Proof. vm_refl. Qed.
Lemma D_6f3f0 : decode_any W_6f3f0 = Some (Op32 ALU_SUB 18 18 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6f3f4 : bv 32 := 0x40d787b3.
Lemma F_6f3f4 : fetch_word Ubsan.M.loaded_segments (0x6f3f4 : word) = Some W_6f3f4.
Proof. vm_refl. Qed.
Lemma D_6f3f4 : decode_any W_6f3f4 = Some (Op ALU_SUB 15 15 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6f3f8 : bv 32 := 0x00f73023.
Lemma F_6f3f8 : fetch_word Ubsan.M.loaded_segments (0x6f3f8 : word) = Some W_6f3f8.
Proof. vm_refl. Qed.
Lemma D_6f3f8 : decode_any W_6f3f8 = Some (Store SZ8 14 15 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6f3fc : bv 32 := 0x04200893.
Lemma F_6f3fc : fetch_word Ubsan.M.loaded_segments (0x6f3fc : word) = Some W_6f3fc.
Proof. vm_refl. Qed.
Lemma D_6f3fc : decode_any W_6f3fc = Some (OpImm ALU_ADD 17 0 66, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6f400 : bv 32 := 0x00090613.
Lemma F_6f400 : fetch_word Ubsan.M.loaded_segments (0x6f400 : word) = Some W_6f400.
Proof. vm_refl. Qed.
Lemma D_6f400 : decode_any W_6f400 = Some (OpImm ALU_ADD 12 18 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6f404 : bv 32 := 0x00000073.
Lemma F_6f404 : fetch_word Ubsan.M.loaded_segments (0x6f404 : word) = Some W_6f404.
Proof. vm_refl. Qed.
Lemma D_6f404 : decode_any W_6f404 = Some (Ecall, 4%Z).
Proof. vm_refl. Qed.
Lemma E_6f404 : is_ecall W_6f404 = true.
Proof. reflexivity. Qed.

(* [comment removed for export] *)
Definition W_6f408 : bv 32 := 0xaf5fc0ef.
Lemma F_6f408 : fetch_word Ubsan.M.loaded_segments (0x6f408 : word) = Some W_6f408.
Proof. vm_refl. Qed.
Lemma D_6f408 : decode_any W_6f408 = Some (Jal 1 2083572, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6f40c : bv 32 := 0x000a0993.
Lemma F_6f40c : fetch_word Ubsan.M.loaded_segments (0x6f40c : word) = Some W_6f40c.
Proof. vm_refl. Qed.
Lemma D_6f40c : decode_any W_6f40c = Some (OpImm ALU_ADD 19 20 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6f410 : bv 32 := 0xf7650ce3.
Lemma F_6f410 : fetch_word Ubsan.M.loaded_segments (0x6f410 : word) = Some W_6f410.
Proof. vm_refl. Qed.
Lemma D_6f410 : decode_any W_6f410 = Some (Branch BC_EQ 10 22 8056, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6f414 : bv 32 := 0x02054c63.
Lemma F_6f414 : fetch_word Ubsan.M.loaded_segments (0x6f414 : word) = Some W_6f414.
Proof. vm_refl. Qed.
Lemma D_6f414 : decode_any W_6f414 = Some (Branch BC_LT 10 0 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6f418 : bv 32 := 0x0089b583.
Lemma F_6f418 : fetch_word Ubsan.M.loaded_segments (0x6f418 : word) = Some W_6f418.
Proof. vm_refl. Qed.
Lemma D_6f418 : decode_any W_6f418 = Some (Load SZ8 true 11 19 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6f41c : bv 32 := 0x00a5b633.
Lemma F_6f41c : fetch_word Ubsan.M.loaded_segments (0x6f41c : word) = Some W_6f41c.
Proof. vm_refl. Qed.
Lemma D_6f41c : decode_any W_6f41c = Some (Op ALU_SLTU 12 11 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6f420 : bv 32 := 0x00461a13.
Lemma F_6f420 : fetch_word Ubsan.M.loaded_segments (0x6f420 : word) = Some W_6f420.
Proof. vm_refl. Qed.
Lemma D_6f420 : decode_any W_6f420 = Some (ShiftImm ALU_SLL 20 12 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6f424 : bv 32 := 0x01498a33.
Lemma F_6f424 : fetch_word Ubsan.M.loaded_segments (0x6f424 : word) = Some W_6f424.
Proof. vm_refl. Qed.
Lemma D_6f424 : decode_any W_6f424 = Some (Op ALU_ADD 20 19 20, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6f428 : bv 32 := 0x000a3703.
Lemma F_6f428 : fetch_word Ubsan.M.loaded_segments (0x6f428 : word) = Some W_6f428.
Proof. vm_refl. Qed.
Lemma D_6f428 : decode_any W_6f428 = Some (Load SZ8 true 14 20 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6f42c : bv 32 := 0x40c006b3.
Lemma F_6f42c : fetch_word Ubsan.M.loaded_segments (0x6f42c : word) = Some W_6f42c.
Proof. vm_refl. Qed.
Lemma D_6f42c : decode_any W_6f42c = Some (Op ALU_SUB 13 0 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6f430 : bv 32 := 0x00b6f6b3.
Lemma F_6f430 : fetch_word Ubsan.M.loaded_segments (0x6f430 : word) = Some W_6f430.
Proof. vm_refl. Qed.
Lemma D_6f430 : decode_any W_6f430 = Some (Op ALU_AND 13 13 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6f434 : bv 32 := 0x40d506b3.
Lemma F_6f434 : fetch_word Ubsan.M.loaded_segments (0x6f434 : word) = Some W_6f434.
Proof. vm_refl. Qed.
Lemma D_6f434 : decode_any W_6f434 = Some (Op ALU_SUB 13 10 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6f438 : bv 32 := 0x00d70733.
Lemma F_6f438 : fetch_word Ubsan.M.loaded_segments (0x6f438 : word) = Some W_6f438.
Proof. vm_refl. Qed.
Lemma D_6f438 : decode_any W_6f438 = Some (Op ALU_ADD 14 14 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6f43c : bv 32 := 0x00ea3023.
Lemma F_6f43c : fetch_word Ubsan.M.loaded_segments (0x6f43c : word) = Some W_6f43c.
Proof. vm_refl. Qed.
Lemma D_6f43c : decode_any W_6f43c = Some (Store SZ8 20 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6f440 : bv 32 := 0xf8a5fce3.
Lemma F_6f440 : fetch_word Ubsan.M.loaded_segments (0x6f440 : word) = Some W_6f440.
Proof. vm_refl. Qed.
Lemma D_6f440 : decode_any W_6f440 = Some (Branch BC_GEU 11 10 8088, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6f444 : bv 32 := 0x01800713.
Lemma F_6f444 : fetch_word Ubsan.M.loaded_segments (0x6f444 : word) = Some W_6f444.
Proof. vm_refl. Qed.
Lemma D_6f444 : decode_any W_6f444 = Some (OpImm ALU_ADD 14 0 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6f448 : bv 32 := 0xf95ff06f.
Lemma F_6f448 : fetch_word Ubsan.M.loaded_segments (0x6f448 : word) = Some W_6f448.
Proof. vm_refl. Qed.
Lemma D_6f448 : decode_any W_6f448 = Some (Jal 0 2097044, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6f44c : bv 32 := 0x00000513.
Lemma F_6f44c : fetch_word Ubsan.M.loaded_segments (0x6f44c : word) = Some W_6f44c.
Proof. vm_refl. Qed.
Lemma D_6f44c : decode_any W_6f44c = Some (OpImm ALU_ADD 10 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6f450 : bv 32 := 0x0004a583.
Lemma F_6f450 : fetch_word Ubsan.M.loaded_segments (0x6f450 : word) = Some W_6f450.
Proof. vm_refl. Qed.
Lemma D_6f450 : decode_any W_6f450 = Some (Load SZ4 true 11 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6f454 : bv 32 := 0x0009091b.
Lemma F_6f454 : fetch_word Ubsan.M.loaded_segments (0x6f454 : word) = Some W_6f454.
Proof. vm_refl. Qed.
Lemma D_6f454 : decode_any W_6f454 = Some (OpImm32 18 18 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6f458 : bv 32 := 0x00200613.
Lemma F_6f458 : fetch_word Ubsan.M.loaded_segments (0x6f458 : word) = Some W_6f458.
Proof. vm_refl. Qed.
Lemma D_6f458 : decode_any W_6f458 = Some (OpImm ALU_ADD 12 0 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6f45c : bv 32 := 0x0205e593.
Lemma F_6f45c : fetch_word Ubsan.M.loaded_segments (0x6f45c : word) = Some W_6f45c.
Proof. vm_refl. Qed.
Lemma D_6f45c : decode_any W_6f45c = Some (OpImm ALU_OR 11 11 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6f460 : bv 32 := 0x00b4a023.
Lemma F_6f460 : fetch_word Ubsan.M.loaded_segments (0x6f460 : word) = Some W_6f460.
Proof. vm_refl. Qed.
Lemma D_6f460 : decode_any W_6f460 = Some (Store SZ4 9 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6f464 : bv 32 := 0x0204b023.
Lemma F_6f464 : fetch_word Ubsan.M.loaded_segments (0x6f464 : word) = Some W_6f464.
Proof. vm_refl. Qed.
Lemma D_6f464 : decode_any W_6f464 = Some (Store SZ8 9 0 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6f468 : bv 32 := 0x0204b423.
Lemma F_6f468 : fetch_word Ubsan.M.loaded_segments (0x6f468 : word) = Some W_6f468.
Proof. vm_refl. Qed.
Lemma D_6f468 : decode_any W_6f468 = Some (Store SZ8 9 0 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6f46c : bv 32 := 0x0204bc23.
Lemma F_6f46c : fetch_word Ubsan.M.loaded_segments (0x6f46c : word) = Some W_6f46c.
Proof. vm_refl. Qed.
Lemma D_6f46c : decode_any W_6f46c = Some (Store SZ8 9 0 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6f470 : bv 32 := 0xf2c90ae3.
Lemma F_6f470 : fetch_word Ubsan.M.loaded_segments (0x6f470 : word) = Some W_6f470.
Proof. vm_refl. Qed.
Lemma D_6f470 : decode_any W_6f470 = Some (Branch BC_EQ 18 12 7988, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6f474 : bv 32 := 0x0089b503.
Lemma F_6f474 : fetch_word Ubsan.M.loaded_segments (0x6f474 : word) = Some W_6f474.
Proof. vm_refl. Qed.
Lemma D_6f474 : decode_any W_6f474 = Some (Load SZ8 true 10 19 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6f478 : bv 32 := 0x40a40533.
Lemma F_6f478 : fetch_word Ubsan.M.loaded_segments (0x6f478 : word) = Some W_6f478.
Proof. vm_refl. Qed.
Lemma D_6f478 : decode_any W_6f478 = Some (Op ALU_SUB 10 8 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6f47c : bv 32 := 0xf29ff06f.
Lemma F_6f47c : fetch_word Ubsan.M.loaded_segments (0x6f47c : word) = Some W_6f47c.
Proof. vm_refl. Qed.
Lemma D_6f47c : decode_any W_6f47c = Some (Jal 0 2096936, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6f480 : bv 32 := 0xc10fc0ef.
Lemma F_6f480 : fetch_word Ubsan.M.loaded_segments (0x6f480 : word) = Some W_6f480.
Proof. vm_refl. Qed.
Lemma D_6f480 : decode_any W_6f480 = Some (Jal 1 2081808, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6f484 : bv 32 := 0x07852503.
Lemma F_6f484 : fetch_word Ubsan.M.loaded_segments (0x6f484 : word) = Some W_6f484.
Proof. vm_refl. Qed.
Lemma D_6f484 : decode_any W_6f484 = Some (Load SZ4 true 10 10 120, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6f488 : bv 32 := 0x5c50d06f.
Lemma F_6f488 : fetch_word Ubsan.M.loaded_segments (0x6f488 : word) = Some W_6f488.
Proof. vm_refl. Qed.
Lemma D_6f488 : decode_any W_6f488 = Some (Jal 0 56772, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6f48c : bv 32 := 0xfe010113.
Lemma F_6f48c : fetch_word Ubsan.M.loaded_segments (0x6f48c : word) = Some W_6f48c.
Proof. vm_refl. Qed.
Lemma D_6f48c : decode_any W_6f48c = Some (OpImm ALU_ADD 2 2 4064, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6f490 : bv 32 := 0x00113c23.
Lemma F_6f490 : fetch_word Ubsan.M.loaded_segments (0x6f490 : word) = Some W_6f490.
Proof. vm_refl. Qed.
Lemma D_6f490 : decode_any W_6f490 = Some (Store SZ8 2 1 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6f494 : bv 32 := 0x00813823.
Lemma F_6f494 : fetch_word Ubsan.M.loaded_segments (0x6f494 : word) = Some W_6f494.
Proof. vm_refl. Qed.
Lemma D_6f494 : decode_any W_6f494 = Some (Store SZ8 2 8 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6f498 : bv 32 := 0x00014697.
Lemma F_6f498 : fetch_word Ubsan.M.loaded_segments (0x6f498 : word) = Some W_6f498.
Proof. vm_refl. Qed.
Lemma D_6f498 : decode_any W_6f498 = Some (Auipc 13 20, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6f49c : bv 32 := 0x6986b403.
Lemma F_6f49c : fetch_word Ubsan.M.loaded_segments (0x6f49c : word) = Some W_6f49c.
Proof. vm_refl. Qed.
Lemma D_6f49c : decode_any W_6f49c = Some (Load SZ8 true 8 13 1688, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6f4a0 : bv 32 := 0x00043683.
Lemma F_6f4a0 : fetch_word Ubsan.M.loaded_segments (0x6f4a0 : word) = Some W_6f4a0.
Proof. vm_refl. Qed.
Lemma D_6f4a0 : decode_any W_6f4a0 = Some (Load SZ8 true 13 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6f4a4 : bv 32 := 0x00d13423.
Lemma F_6f4a4 : fetch_word Ubsan.M.loaded_segments (0x6f4a4 : word) = Some W_6f4a4.
Proof. vm_refl. Qed.
Lemma D_6f4a4 : decode_any W_6f4a4 = Some (Store SZ8 2 13 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6f4a8 : bv 32 := 0x00054683.
Lemma F_6f4a8 : fetch_word Ubsan.M.loaded_segments (0x6f4a8 : word) = Some W_6f4a8.
Proof. vm_refl. Qed.
Lemma D_6f4a8 : decode_any W_6f4a8 = Some (Load SZ1 false 13 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6f4ac : bv 32 := 0x00000717.
Lemma F_6f4ac : fetch_word Ubsan.M.loaded_segments (0x6f4ac : word) = Some W_6f4ac.
Proof. vm_refl. Qed.
Lemma D_6f4ac : decode_any W_6f4ac = Some (Auipc 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6f4b0 : bv 32 := 0xe4870713.
Lemma F_6f4b0 : fetch_word Ubsan.M.loaded_segments (0x6f4b0 : word) = Some W_6f4b0.
Proof. vm_refl. Qed.
Lemma D_6f4b0 : decode_any W_6f4b0 = Some (OpImm ALU_ADD 14 14 3656, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6f4b4 : bv 32 := 0x0406f693.
Lemma F_6f4b4 : fetch_word Ubsan.M.loaded_segments (0x6f4b4 : word) = Some W_6f4b4.
Proof. vm_refl. Qed.
Lemma D_6f4b4 : decode_any W_6f4b4 = Some (OpImm ALU_AND 13 13 64, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6f4b8 : bv 32 := 0x04e53423.
Lemma F_6f4b8 : fetch_word Ubsan.M.loaded_segments (0x6f4b8 : word) = Some W_6f4b8.
Proof. vm_refl. Qed.
Lemma D_6f4b8 : decode_any W_6f4b8 = Some (Store SZ8 10 14 72, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6f4bc : bv 32 := 0x04069663.
Lemma F_6f4bc : fetch_word Ubsan.M.loaded_segments (0x6f4bc : word) = Some W_6f4bc.
Proof. vm_refl. Qed.
Lemma D_6f4bc : decode_any W_6f4bc = Some (Branch BC_NE 13 0 76, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6f4c0 : bv 32 := 0x07852683.
Lemma F_6f4c0 : fetch_word Ubsan.M.loaded_segments (0x6f4c0 : word) = Some W_6f4c0.
Proof. vm_refl. Qed.
Lemma D_6f4c0 : decode_any W_6f4c0 = Some (Load SZ4 true 13 10 120, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6f4c4 : bv 32 := 0x00005737.
Lemma F_6f4c4 : fetch_word Ubsan.M.loaded_segments (0x6f4c4 : word) = Some W_6f4c4.
Proof. vm_refl. Qed.
Lemma D_6f4c4 : decode_any W_6f4c4 = Some (Lui 14 5, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6f4c8 : bv 32 := 0x4137071b.
Lemma F_6f4c8 : fetch_word Ubsan.M.loaded_segments (0x6f4c8 : word) = Some W_6f4c8.
Proof. vm_refl. Qed.
Lemma D_6f4c8 : decode_any W_6f4c8 = Some (OpImm32 14 14 1043, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6f4cc : bv 32 := 0x01d00893.
Lemma F_6f4cc : fetch_word Ubsan.M.loaded_segments (0x6f4cc : word) = Some W_6f4cc.
Proof. vm_refl. Qed.
Lemma D_6f4cc : decode_any W_6f4cc = Some (OpImm ALU_ADD 17 0 29, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6f4d0 : bv 32 := 0x00060793.
Lemma F_6f4d0 : fetch_word Ubsan.M.loaded_segments (0x6f4d0 : word) = Some W_6f4d0.
Proof. vm_refl. Qed.
Lemma D_6f4d0 : decode_any W_6f4d0 = Some (OpImm ALU_ADD 15 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6f4d4 : bv 32 := 0x00010613.
Lemma F_6f4d4 : fetch_word Ubsan.M.loaded_segments (0x6f4d4 : word) = Some W_6f4d4.
Proof. vm_refl. Qed.
Lemma D_6f4d4 : decode_any W_6f4d4 = Some (OpImm ALU_ADD 12 2 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6f4d8 : bv 32 := 0x00050813.
Lemma F_6f4d8 : fetch_word Ubsan.M.loaded_segments (0x6f4d8 : word) = Some W_6f4d8.
Proof. vm_refl. Qed.
Lemma D_6f4d8 : decode_any W_6f4d8 = Some (OpImm ALU_ADD 16 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6f4dc : bv 32 := 0x00068513.
Lemma F_6f4dc : fetch_word Ubsan.M.loaded_segments (0x6f4dc : word) = Some W_6f4dc.
Proof. vm_refl. Qed.
Lemma D_6f4dc : decode_any W_6f4dc = Some (OpImm ALU_ADD 10 13 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6f4e0 : bv 32 := 0x00058693.
Lemma F_6f4e0 : fetch_word Ubsan.M.loaded_segments (0x6f4e0 : word) = Some W_6f4e0.
Proof. vm_refl. Qed.
Lemma D_6f4e0 : decode_any W_6f4e0 = Some (OpImm ALU_ADD 13 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6f4e4 : bv 32 := 0x00070593.
Lemma F_6f4e4 : fetch_word Ubsan.M.loaded_segments (0x6f4e4 : word) = Some W_6f4e4.
Proof. vm_refl. Qed.
Lemma D_6f4e4 : decode_any W_6f4e4 = Some (OpImm ALU_ADD 11 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6f4e8 : bv 32 := 0x00000073.
Lemma F_6f4e8 : fetch_word Ubsan.M.loaded_segments (0x6f4e8 : word) = Some W_6f4e8.
Proof. vm_refl. Qed.
Lemma D_6f4e8 : decode_any W_6f4e8 = Some (Ecall, 4%Z).
Proof. vm_refl. Qed.
Lemma E_6f4e8 : is_ecall W_6f4e8 = true.
Proof. reflexivity. Qed.

(* [comment removed for export] *)
Definition W_6f4ec : bv 32 := 0x00068593.
Lemma F_6f4ec : fetch_word Ubsan.M.loaded_segments (0x6f4ec : word) = Some W_6f4ec.
Proof. vm_refl. Qed.
Lemma D_6f4ec : decode_any W_6f4ec = Some (OpImm ALU_ADD 11 13 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6f4f0 : bv 32 := 0x00078613.
Lemma F_6f4f0 : fetch_word Ubsan.M.loaded_segments (0x6f4f0 : word) = Some W_6f4f0.
Proof. vm_refl. Qed.
Lemma D_6f4f0 : decode_any W_6f4f0 = Some (OpImm ALU_ADD 12 15 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6f4f4 : bv 32 := 0x00050693.
Lemma F_6f4f4 : fetch_word Ubsan.M.loaded_segments (0x6f4f4 : word) = Some W_6f4f4.
Proof. vm_refl. Qed.
Lemma D_6f4f4 : decode_any W_6f4f4 = Some (OpImm ALU_ADD 13 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6f4f8 : bv 32 := 0x00080513.
Lemma F_6f4f8 : fetch_word Ubsan.M.loaded_segments (0x6f4f8 : word) = Some W_6f4f8.
Proof. vm_refl. Qed.
Lemma D_6f4f8 : decode_any W_6f4f8 = Some (OpImm ALU_ADD 10 16 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6f4fc : bv 32 := 0x00068663.
Lemma F_6f4fc : fetch_word Ubsan.M.loaded_segments (0x6f4fc : word) = Some W_6f4fc.
Proof. vm_refl. Qed.
Lemma D_6f4fc : decode_any W_6f4fc = Some (Branch BC_EQ 13 0 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6f500 : bv 32 := 0xfff00693.
Lemma F_6f500 : fetch_word Ubsan.M.loaded_segments (0x6f500 : word) = Some W_6f500.
Proof. vm_refl. Qed.
Lemma D_6f500 : decode_any W_6f500 = Some (OpImm ALU_ADD 13 0 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6f504 : bv 32 := 0x08d52823.
Lemma F_6f504 : fetch_word Ubsan.M.loaded_segments (0x6f504 : word) = Some W_6f504.
Proof. vm_refl. Qed.
Lemma D_6f504 : decode_any W_6f504 = Some (Store SZ4 10 13 144, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6f508 : bv 32 := 0xdedff0ef.
Lemma F_6f508 : fetch_word Ubsan.M.loaded_segments (0x6f508 : word) = Some W_6f508.
Proof. vm_refl. Qed.
Lemma D_6f508 : decode_any W_6f508 = Some (Jal 1 2096620, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6f50c : bv 32 := 0x00043583.
Lemma F_6f50c : fetch_word Ubsan.M.loaded_segments (0x6f50c : word) = Some W_6f50c.
Proof. vm_refl. Qed.
Lemma D_6f50c : decode_any W_6f50c = Some (Load SZ8 true 11 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6f510 : bv 32 := 0x00813603.
Lemma F_6f510 : fetch_word Ubsan.M.loaded_segments (0x6f510 : word) = Some W_6f510.
Proof. vm_refl. Qed.
Lemma D_6f510 : decode_any W_6f510 = Some (Load SZ8 true 12 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6f514 : bv 32 := 0x00c59a63.
Lemma F_6f514 : fetch_word Ubsan.M.loaded_segments (0x6f514 : word) = Some W_6f514.
Proof. vm_refl. Qed.
Lemma D_6f514 : decode_any W_6f514 = Some (Branch BC_NE 11 12 20, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6f518 : bv 32 := 0x01813083.
Lemma F_6f518 : fetch_word Ubsan.M.loaded_segments (0x6f518 : word) = Some W_6f518.
Proof. vm_refl. Qed.
Lemma D_6f518 : decode_any W_6f518 = Some (Load SZ8 true 1 2 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6f51c : bv 32 := 0x01013403.
Lemma F_6f51c : fetch_word Ubsan.M.loaded_segments (0x6f51c : word) = Some W_6f51c.
Proof. vm_refl. Qed.
Lemma D_6f51c : decode_any W_6f51c = Some (Load SZ8 true 8 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6f520 : bv 32 := 0x02010113.
Lemma F_6f520 : fetch_word Ubsan.M.loaded_segments (0x6f520 : word) = Some W_6f520.
Proof. vm_refl. Qed.
Lemma D_6f520 : decode_any W_6f520 = Some (OpImm ALU_ADD 2 2 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6f524 : bv 32 := 0x00008067.
Lemma F_6f524 : fetch_word Ubsan.M.loaded_segments (0x6f524 : word) = Some W_6f524.
Proof. vm_refl. Qed.
Lemma D_6f524 : decode_any W_6f524 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6f528 : bv 32 := 0xb68fc0ef.
Lemma F_6f528 : fetch_word Ubsan.M.loaded_segments (0x6f528 : word) = Some W_6f528.
Proof. vm_refl. Qed.
Lemma D_6f528 : decode_any W_6f528 = Some (Jal 1 2081640, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6f52c : bv 32 := 0xfb010113.
Lemma F_6f52c : fetch_word Ubsan.M.loaded_segments (0x6f52c : word) = Some W_6f52c.
Proof. vm_refl. Qed.
Lemma D_6f52c : decode_any W_6f52c = Some (OpImm ALU_ADD 2 2 4016, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6f530 : bv 32 := 0x00113c23.
Lemma F_6f530 : fetch_word Ubsan.M.loaded_segments (0x6f530 : word) = Some W_6f530.
Proof. vm_refl. Qed.
Lemma D_6f530 : decode_any W_6f530 = Some (Store SZ8 2 1 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6f534 : bv 32 := 0x00813823.
Lemma F_6f534 : fetch_word Ubsan.M.loaded_segments (0x6f534 : word) = Some W_6f534.
Proof. vm_refl. Qed.
Lemma D_6f534 : decode_any W_6f534 = Some (Store SZ8 2 8 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6f538 : bv 32 := 0x05113423.
Lemma F_6f538 : fetch_word Ubsan.M.loaded_segments (0x6f538 : word) = Some W_6f538.
Proof. vm_refl. Qed.
Lemma D_6f538 : decode_any W_6f538 = Some (Store SZ8 2 17 72, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6f53c : bv 32 := 0x00014897.
Lemma F_6f53c : fetch_word Ubsan.M.loaded_segments (0x6f53c : word) = Some W_6f53c.
Proof. vm_refl. Qed.
Lemma D_6f53c : decode_any W_6f53c = Some (Auipc 17 20, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6f540 : bv 32 := 0x5f48b403.
Lemma F_6f540 : fetch_word Ubsan.M.loaded_segments (0x6f540 : word) = Some W_6f540.
Proof. vm_refl. Qed.
Lemma D_6f540 : decode_any W_6f540 = Some (Load SZ8 true 8 17 1524, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6f544 : bv 32 := 0x02d13423.
Lemma F_6f544 : fetch_word Ubsan.M.loaded_segments (0x6f544 : word) = Some W_6f544.
Proof. vm_refl. Qed.
Lemma D_6f544 : decode_any W_6f544 = Some (Store SZ8 2 13 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6f548 : bv 32 := 0x02e13823.
Lemma F_6f548 : fetch_word Ubsan.M.loaded_segments (0x6f548 : word) = Some W_6f548.
Proof. vm_refl. Qed.
Lemma D_6f548 : decode_any W_6f548 = Some (Store SZ8 2 14 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6f54c : bv 32 := 0x02f13c23.
Lemma F_6f54c : fetch_word Ubsan.M.loaded_segments (0x6f54c : word) = Some W_6f54c.
Proof. vm_refl. Qed.
Lemma D_6f54c : decode_any W_6f54c = Some (Store SZ8 2 15 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6f550 : bv 32 := 0x05013023.
Lemma F_6f550 : fetch_word Ubsan.M.loaded_segments (0x6f550 : word) = Some W_6f550.
Proof. vm_refl. Qed.
Lemma D_6f550 : decode_any W_6f550 = Some (Store SZ8 2 16 64, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6f554 : bv 32 := 0x00043683.
Lemma F_6f554 : fetch_word Ubsan.M.loaded_segments (0x6f554 : word) = Some W_6f554.
Proof. vm_refl. Qed.
Lemma D_6f554 : decode_any W_6f554 = Some (Load SZ8 true 13 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6f558 : bv 32 := 0x02810713.
Lemma F_6f558 : fetch_word Ubsan.M.loaded_segments (0x6f558 : word) = Some W_6f558.
Proof. vm_refl. Qed.
Lemma D_6f558 : decode_any W_6f558 = Some (OpImm ALU_ADD 14 2 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6f55c : bv 32 := 0x00d13423.
Lemma F_6f55c : fetch_word Ubsan.M.loaded_segments (0x6f55c : word) = Some W_6f55c.
Proof. vm_refl. Qed.
Lemma D_6f55c : decode_any W_6f55c = Some (Store SZ8 2 13 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6f560 : bv 32 := 0x00e13023.
Lemma F_6f560 : fetch_word Ubsan.M.loaded_segments (0x6f560 : word) = Some W_6f560.
Proof. vm_refl. Qed.
Lemma D_6f560 : decode_any W_6f560 = Some (Store SZ8 2 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6f564 : bv 32 := 0x02810693.
Lemma F_6f564 : fetch_word Ubsan.M.loaded_segments (0x6f564 : word) = Some W_6f564.
Proof. vm_refl. Qed.
Lemma D_6f564 : decode_any W_6f564 = Some (OpImm ALU_ADD 13 2 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6f568 : bv 32 := 0x405040ef.
Lemma F_6f568 : fetch_word Ubsan.M.loaded_segments (0x6f568 : word) = Some W_6f568.
Proof. vm_refl. Qed.
Lemma D_6f568 : decode_any W_6f568 = Some (Jal 1 19460, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6f56c : bv 32 := 0x00043583.
Lemma F_6f56c : fetch_word Ubsan.M.loaded_segments (0x6f56c : word) = Some W_6f56c.
Proof. vm_refl. Qed.
Lemma D_6f56c : decode_any W_6f56c = Some (Load SZ8 true 11 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6f570 : bv 32 := 0x00813603.
Lemma F_6f570 : fetch_word Ubsan.M.loaded_segments (0x6f570 : word) = Some W_6f570.
Proof. vm_refl. Qed.
Lemma D_6f570 : decode_any W_6f570 = Some (Load SZ8 true 12 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6f574 : bv 32 := 0x00c59a63.
Lemma F_6f574 : fetch_word Ubsan.M.loaded_segments (0x6f574 : word) = Some W_6f574.
Proof. vm_refl. Qed.
Lemma D_6f574 : decode_any W_6f574 = Some (Branch BC_NE 11 12 20, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6f578 : bv 32 := 0x01813083.
Lemma F_6f578 : fetch_word Ubsan.M.loaded_segments (0x6f578 : word) = Some W_6f578.
Proof. vm_refl. Qed.
Lemma D_6f578 : decode_any W_6f578 = Some (Load SZ8 true 1 2 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6f57c : bv 32 := 0x01013403.
Lemma F_6f57c : fetch_word Ubsan.M.loaded_segments (0x6f57c : word) = Some W_6f57c.
Proof. vm_refl. Qed.
Lemma D_6f57c : decode_any W_6f57c = Some (Load SZ8 true 8 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6f580 : bv 32 := 0x05010113.
Lemma F_6f580 : fetch_word Ubsan.M.loaded_segments (0x6f580 : word) = Some W_6f580.
Proof. vm_refl. Qed.
Lemma D_6f580 : decode_any W_6f580 = Some (OpImm ALU_ADD 2 2 80, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6f584 : bv 32 := 0x00008067.
Lemma F_6f584 : fetch_word Ubsan.M.loaded_segments (0x6f584 : word) = Some W_6f584.
Proof. vm_refl. Qed.
Lemma D_6f584 : decode_any W_6f584 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6f588 : bv 32 := 0xb08fc0ef.
Lemma F_6f588 : fetch_word Ubsan.M.loaded_segments (0x6f588 : word) = Some W_6f588.
Proof. vm_refl. Qed.
Lemma D_6f588 : decode_any W_6f588 = Some (Jal 1 2081544, 4%Z).
Proof. vm_refl. Qed.
