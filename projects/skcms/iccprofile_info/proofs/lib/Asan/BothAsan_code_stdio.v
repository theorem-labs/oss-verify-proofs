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
Definition W_8f790 : bv 32 := 0xfffff5b7.
Lemma F_8f790 : fetch_word AsanUbsan.M.loaded_segments (0x8f790 : word) = Some W_8f790.
Proof. vm_refl. Qed.
Lemma D_8f790 : decode_any W_8f790 = Some (Lui 11 1048575, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8f794 : bv 32 := 0x0015859b.
Lemma F_8f794 : fetch_word AsanUbsan.M.loaded_segments (0x8f794 : word) = Some W_8f794.
Proof. vm_refl. Qed.
Lemma D_8f794 : decode_any W_8f794 = Some (OpImm32 11 11 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8f798 : bv 32 := 0x02b56663.
Lemma F_8f798 : fetch_word AsanUbsan.M.loaded_segments (0x8f798 : word) = Some W_8f798.
Proof. vm_refl. Qed.
Lemma D_8f798 : decode_any W_8f798 = Some (Branch BC_LTU 10 11 44, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8f79c : bv 32 := 0xff010113.
Lemma F_8f79c : fetch_word AsanUbsan.M.loaded_segments (0x8f79c : word) = Some W_8f79c.
Proof. vm_refl. Qed.
Lemma D_8f79c : decode_any W_8f79c = Some (OpImm ALU_ADD 2 2 4080, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8f7a0 : bv 32 := 0x00113423.
Lemma F_8f7a0 : fetch_word AsanUbsan.M.loaded_segments (0x8f7a0 : word) = Some W_8f7a0.
Proof. vm_refl. Qed.
Lemma D_8f7a0 : decode_any W_8f7a0 = Some (Store SZ8 2 1 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8f7a4 : bv 32 := 0x00813023.
Lemma F_8f7a4 : fetch_word AsanUbsan.M.loaded_segments (0x8f7a4 : word) = Some W_8f7a4.
Proof. vm_refl. Qed.
Lemma D_8f7a4 : decode_any W_8f7a4 = Some (Store SZ8 2 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8f7a8 : bv 32 := 0x40a0043b.
Lemma F_8f7a8 : fetch_word AsanUbsan.M.loaded_segments (0x8f7a8 : word) = Some W_8f7a8.
Proof. vm_refl. Qed.
Lemma D_8f7a8 : decode_any W_8f7a8 = Some (Op32 ALU_SUB 8 0 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8f7ac : bv 32 := 0x981ff0ef.
Lemma F_8f7ac : fetch_word AsanUbsan.M.loaded_segments (0x8f7ac : word) = Some W_8f7ac.
Proof. vm_refl. Qed.
Lemma D_8f7ac : decode_any W_8f7ac = Some (Jal 1 2095488, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8f7b0 : bv 32 := 0x00852023.
Lemma F_8f7b0 : fetch_word AsanUbsan.M.loaded_segments (0x8f7b0 : word) = Some W_8f7b0.
Proof. vm_refl. Qed.
Lemma D_8f7b0 : decode_any W_8f7b0 = Some (Store SZ4 10 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8f7b4 : bv 32 := 0xfff00513.
Lemma F_8f7b4 : fetch_word AsanUbsan.M.loaded_segments (0x8f7b4 : word) = Some W_8f7b4.
Proof. vm_refl. Qed.
Lemma D_8f7b4 : decode_any W_8f7b4 = Some (OpImm ALU_ADD 10 0 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8f7b8 : bv 32 := 0x00813083.
Lemma F_8f7b8 : fetch_word AsanUbsan.M.loaded_segments (0x8f7b8 : word) = Some W_8f7b8.
Proof. vm_refl. Qed.
Lemma D_8f7b8 : decode_any W_8f7b8 = Some (Load SZ8 true 1 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8f7bc : bv 32 := 0x00013403.
Lemma F_8f7bc : fetch_word AsanUbsan.M.loaded_segments (0x8f7bc : word) = Some W_8f7bc.
Proof. vm_refl. Qed.
Lemma D_8f7bc : decode_any W_8f7bc = Some (Load SZ8 true 8 2 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8f7c0 : bv 32 := 0x01010113.
Lemma F_8f7c0 : fetch_word AsanUbsan.M.loaded_segments (0x8f7c0 : word) = Some W_8f7c0.
Proof. vm_refl. Qed.
Lemma D_8f7c0 : decode_any W_8f7c0 = Some (OpImm ALU_ADD 2 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8f7c4 : bv 32 := 0x00008067.
Lemma F_8f7c4 : fetch_word AsanUbsan.M.loaded_segments (0x8f7c4 : word) = Some W_8f7c4.
Proof. vm_refl. Qed.
Lemma D_8f7c4 : decode_any W_8f7c4 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_94948 : bv 32 := 0xf9010113.
Lemma F_94948 : fetch_word AsanUbsan.M.loaded_segments (0x94948 : word) = Some W_94948.
Proof. vm_refl. Qed.
Lemma D_94948 : decode_any W_94948 = Some (OpImm ALU_ADD 2 2 3984, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9494c : bv 32 := 0x06113423.
Lemma F_9494c : fetch_word AsanUbsan.M.loaded_segments (0x9494c : word) = Some W_9494c.
Proof. vm_refl. Qed.
Lemma D_9494c : decode_any W_9494c = Some (Store SZ8 2 1 104, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_94950 : bv 32 := 0x06813023.
Lemma F_94950 : fetch_word AsanUbsan.M.loaded_segments (0x94950 : word) = Some W_94950.
Proof. vm_refl. Qed.
Lemma D_94950 : decode_any W_94950 = Some (Store SZ8 2 8 96, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_94954 : bv 32 := 0x04913c23.
Lemma F_94954 : fetch_word AsanUbsan.M.loaded_segments (0x94954 : word) = Some W_94954.
Proof. vm_refl. Qed.
Lemma D_94954 : decode_any W_94954 = Some (Store SZ8 2 9 88, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_94958 : bv 32 := 0x05213823.
Lemma F_94958 : fetch_word AsanUbsan.M.loaded_segments (0x94958 : word) = Some W_94958.
Proof. vm_refl. Qed.
Lemma D_94958 : decode_any W_94958 = Some (Store SZ8 2 18 80, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9495c : bv 32 := 0x05313423.
Lemma F_9495c : fetch_word AsanUbsan.M.loaded_segments (0x9495c : word) = Some W_9495c.
Proof. vm_refl. Qed.
Lemma D_9495c : decode_any W_9495c = Some (Store SZ8 2 19 72, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_94960 : bv 32 := 0x05413023.
Lemma F_94960 : fetch_word AsanUbsan.M.loaded_segments (0x94960 : word) = Some W_94960.
Proof. vm_refl. Qed.
Lemma D_94960 : decode_any W_94960 = Some (Store SZ8 2 20 64, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_94964 : bv 32 := 0x03513c23.
Lemma F_94964 : fetch_word AsanUbsan.M.loaded_segments (0x94964 : word) = Some W_94964.
Proof. vm_refl. Qed.
Lemma D_94964 : decode_any W_94964 = Some (Store SZ8 2 21 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_94968 : bv 32 := 0x03613823.
Lemma F_94968 : fetch_word AsanUbsan.M.loaded_segments (0x94968 : word) = Some W_94968.
Proof. vm_refl. Qed.
Lemma D_94968 : decode_any W_94968 = Some (Store SZ8 2 22 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9496c : bv 32 := 0x00060413.
Lemma F_9496c : fetch_word AsanUbsan.M.loaded_segments (0x9496c : word) = Some W_9496c.
Proof. vm_refl. Qed.
Lemma D_9496c : decode_any W_9496c = Some (OpImm ALU_ADD 8 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_94970 : bv 32 := 0x00050493.
Lemma F_94970 : fetch_word AsanUbsan.M.loaded_segments (0x94970 : word) = Some W_94970.
Proof. vm_refl. Qed.
Lemma D_94970 : decode_any W_94970 = Some (OpImm ALU_ADD 9 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_94974 : bv 32 := 0x0000c517.
Lemma F_94974 : fetch_word AsanUbsan.M.loaded_segments (0x94974 : word) = Some W_94974.
Proof. vm_refl. Qed.
Lemma D_94974 : decode_any W_94974 = Some (Auipc 10 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_94978 : bv 32 := 0xc3453a83.
Lemma F_94978 : fetch_word AsanUbsan.M.loaded_segments (0x94978 : word) = Some W_94978.
Proof. vm_refl. Qed.
Lemma D_94978 : decode_any W_94978 = Some (Load SZ8 true 21 10 3124, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9497c : bv 32 := 0x000ab503.
Lemma F_9497c : fetch_word AsanUbsan.M.loaded_segments (0x9497c : word) = Some W_9497c.
Proof. vm_refl. Qed.
Lemma D_9497c : decode_any W_9497c = Some (Load SZ8 true 10 21 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_94980 : bv 32 := 0x02a13423.
Lemma F_94980 : fetch_word AsanUbsan.M.loaded_segments (0x94980 : word) = Some W_94980.
Proof. vm_refl. Qed.
Lemma D_94980 : decode_any W_94980 = Some (Store SZ8 2 10 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_94984 : bv 32 := 0x0284b503.
Lemma F_94984 : fetch_word AsanUbsan.M.loaded_segments (0x94984 : word) = Some W_94984.
Proof. vm_refl. Qed.
Lemma D_94984 : decode_any W_94984 = Some (Load SZ8 true 10 9 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_94988 : bv 32 := 0x0384b603.
Lemma F_94988 : fetch_word AsanUbsan.M.loaded_segments (0x94988 : word) = Some W_94988.
Proof. vm_refl. Qed.
Lemma D_94988 : decode_any W_94988 = Some (Load SZ8 true 12 9 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9498c : bv 32 := 0x40c50b33.
Lemma F_9498c : fetch_word AsanUbsan.M.loaded_segments (0x9498c : word) = Some W_9498c.
Proof. vm_refl. Qed.
Lemma D_9498c : decode_any W_9498c = Some (Op ALU_SUB 22 10 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_94990 : bv 32 := 0x00c546b3.
Lemma F_94990 : fetch_word AsanUbsan.M.loaded_segments (0x94990 : word) = Some W_94990.
Proof. vm_refl. Qed.
Lemma D_94990 : decode_any W_94990 = Some (Op ALU_XOR 13 10 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_94994 : bv 32 := 0x00c13423.
Lemma F_94994 : fetch_word AsanUbsan.M.loaded_segments (0x94994 : word) = Some W_94994.
Proof. vm_refl. Qed.
Lemma D_94994 : decode_any W_94994 = Some (Store SZ8 2 12 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_94998 : bv 32 := 0x01613823.
Lemma F_94998 : fetch_word AsanUbsan.M.loaded_segments (0x94998 : word) = Some W_94998.
Proof. vm_refl. Qed.
Lemma D_94998 : decode_any W_94998 = Some (Store SZ8 2 22 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9499c : bv 32 := 0x00b13c23.
Lemma F_9499c : fetch_word AsanUbsan.M.loaded_segments (0x9499c : word) = Some W_9499c.
Proof. vm_refl. Qed.
Lemma D_9499c : decode_any W_9499c = Some (Store SZ8 2 11 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_949a0 : bv 32 := 0x02813023.
Lemma F_949a0 : fetch_word AsanUbsan.M.loaded_segments (0x949a0 : word) = Some W_949a0.
Proof. vm_refl. Qed.
Lemma D_949a0 : decode_any W_949a0 = Some (Store SZ8 2 8 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_949a4 : bv 32 := 0x008b0b33.
Lemma F_949a4 : fetch_word AsanUbsan.M.loaded_segments (0x949a4 : word) = Some W_949a4.
Proof. vm_refl. Qed.
Lemma D_949a4 : decode_any W_949a4 = Some (Op ALU_ADD 22 22 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_949a8 : bv 32 := 0x00d03933.
Lemma F_949a8 : fetch_word AsanUbsan.M.loaded_segments (0x949a8 : word) = Some W_949a8.
Proof. vm_refl. Qed.
Lemma D_949a8 : decode_any W_949a8 = Some (Op ALU_SLTU 18 0 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_949ac : bv 32 := 0x00c50663.
Lemma F_949ac : fetch_word AsanUbsan.M.loaded_segments (0x949ac : word) = Some W_949ac.
Proof. vm_refl. Qed.
Lemma D_949ac : decode_any W_949ac = Some (Branch BC_EQ 10 12 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_949b0 : bv 32 := 0x00810993.
Lemma F_949b0 : fetch_word AsanUbsan.M.loaded_segments (0x949b0 : word) = Some W_949b0.
Proof. vm_refl. Qed.
Lemma D_949b0 : decode_any W_949b0 = Some (OpImm ALU_ADD 19 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_949b4 : bv 32 := 0x0080006f.
Lemma F_949b4 : fetch_word AsanUbsan.M.loaded_segments (0x949b4 : word) = Some W_949b4.
Proof. vm_refl. Qed.
Lemma D_949b4 : decode_any W_949b4 = Some (Jal 0 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_949b8 : bv 32 := 0x01810993.
Lemma F_949b8 : fetch_word AsanUbsan.M.loaded_segments (0x949b8 : word) = Some W_949b8.
Proof. vm_refl. Qed.
Lemma D_949b8 : decode_any W_949b8 = Some (OpImm ALU_ADD 19 2 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_949bc : bv 32 := 0x0784a503.
Lemma F_949bc : fetch_word AsanUbsan.M.loaded_segments (0x949bc : word) = Some W_949bc.
Proof. vm_refl. Qed.
Lemma D_949bc : decode_any W_949bc = Some (Load SZ4 true 10 9 120, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_949c0 : bv 32 := 0x00190913.
Lemma F_949c0 : fetch_word AsanUbsan.M.loaded_segments (0x949c0 : word) = Some W_949c0.
Proof. vm_refl. Qed.
Lemma D_949c0 : decode_any W_949c0 = Some (OpImm ALU_ADD 18 18 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_949c4 : bv 32 := 0x04200893.
Lemma F_949c4 : fetch_word AsanUbsan.M.loaded_segments (0x949c4 : word) = Some W_949c4.
Proof. vm_refl. Qed.
Lemma D_949c4 : decode_any W_949c4 = Some (OpImm ALU_ADD 17 0 66, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_949c8 : bv 32 := 0x00098593.
Lemma F_949c8 : fetch_word AsanUbsan.M.loaded_segments (0x949c8 : word) = Some W_949c8.
Proof. vm_refl. Qed.
Lemma D_949c8 : decode_any W_949c8 = Some (OpImm ALU_ADD 11 19 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_949cc : bv 32 := 0x00090613.
Lemma F_949cc : fetch_word AsanUbsan.M.loaded_segments (0x949cc : word) = Some W_949cc.
Proof. vm_refl. Qed.
Lemma D_949cc : decode_any W_949cc = Some (OpImm ALU_ADD 12 18 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_949d0 : bv 32 := 0x00000073.
Lemma F_949d0 : fetch_word AsanUbsan.M.loaded_segments (0x949d0 : word) = Some W_949d0.
Proof. vm_refl. Qed.
Lemma D_949d0 : decode_any W_949d0 = Some (Ecall, 4%Z).
Proof. vm_refl. Qed.
Lemma E_949d0 : is_ecall W_949d0 = true.
Proof. reflexivity. Qed.

(* [comment removed for export] *)
Definition W_949d4 : bv 32 := 0xdbdfa0ef.
Lemma F_949d4 : fetch_word AsanUbsan.M.loaded_segments (0x949d4 : word) = Some W_949d4.
Proof. vm_refl. Qed.
Lemma D_949d4 : decode_any W_949d4 = Some (Jal 1 2076092, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_949d8 : bv 32 := 0x09651863.
Lemma F_949d8 : fetch_word AsanUbsan.M.loaded_segments (0x949d8 : word) = Some W_949d8.
Proof. vm_refl. Qed.
Lemma D_949d8 : decode_any W_949d8 = Some (Branch BC_NE 10 22 144, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_949dc : bv 32 := 0x0584b503.
Lemma F_949dc : fetch_word AsanUbsan.M.loaded_segments (0x949dc : word) = Some W_949dc.
Proof. vm_refl. Qed.
Lemma D_949dc : decode_any W_949dc = Some (Load SZ8 true 10 9 88, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_949e0 : bv 32 := 0x0604b583.
Lemma F_949e0 : fetch_word AsanUbsan.M.loaded_segments (0x949e0 : word) = Some W_949e0.
Proof. vm_refl. Qed.
Lemma D_949e0 : decode_any W_949e0 = Some (Load SZ8 true 11 9 96, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_949e4 : bv 32 := 0x00b505b3.
Lemma F_949e4 : fetch_word AsanUbsan.M.loaded_segments (0x949e4 : word) = Some W_949e4.
Proof. vm_refl. Qed.
Lemma D_949e4 : decode_any W_949e4 = Some (Op ALU_ADD 11 10 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_949e8 : bv 32 := 0x02b4b023.
Lemma F_949e8 : fetch_word AsanUbsan.M.loaded_segments (0x949e8 : word) = Some W_949e8.
Proof. vm_refl. Qed.
Lemma D_949e8 : decode_any W_949e8 = Some (Store SZ8 9 11 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_949ec : bv 32 := 0x02a4b423.
Lemma F_949ec : fetch_word AsanUbsan.M.loaded_segments (0x949ec : word) = Some W_949ec.
Proof. vm_refl. Qed.
Lemma D_949ec : decode_any W_949ec = Some (Store SZ8 9 10 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_949f0 : bv 32 := 0x02a4bc23.
Lemma F_949f0 : fetch_word AsanUbsan.M.loaded_segments (0x949f0 : word) = Some W_949f0.
Proof. vm_refl. Qed.
Lemma D_949f0 : decode_any W_949f0 = Some (Store SZ8 9 10 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_949f4 : bv 32 := 0x00040513.
Lemma F_949f4 : fetch_word AsanUbsan.M.loaded_segments (0x949f4 : word) = Some W_949f4.
Proof. vm_refl. Qed.
Lemma D_949f4 : decode_any W_949f4 = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_949f8 : bv 32 := 0x000ab583.
Lemma F_949f8 : fetch_word AsanUbsan.M.loaded_segments (0x949f8 : word) = Some W_949f8.
Proof. vm_refl. Qed.
Lemma D_949f8 : decode_any W_949f8 = Some (Load SZ8 true 11 21 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_949fc : bv 32 := 0x02813603.
Lemma F_949fc : fetch_word AsanUbsan.M.loaded_segments (0x949fc : word) = Some W_949fc.
Proof. vm_refl. Qed.
Lemma D_949fc : decode_any W_949fc = Some (Load SZ8 true 12 2 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_94a00 : bv 32 := 0x0cc59a63.
Lemma F_94a00 : fetch_word AsanUbsan.M.loaded_segments (0x94a00 : word) = Some W_94a00.
Proof. vm_refl. Qed.
Lemma D_94a00 : decode_any W_94a00 = Some (Branch BC_NE 11 12 212, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_94a04 : bv 32 := 0x06813083.
Lemma F_94a04 : fetch_word AsanUbsan.M.loaded_segments (0x94a04 : word) = Some W_94a04.
Proof. vm_refl. Qed.
Lemma D_94a04 : decode_any W_94a04 = Some (Load SZ8 true 1 2 104, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_94a08 : bv 32 := 0x06013403.
Lemma F_94a08 : fetch_word AsanUbsan.M.loaded_segments (0x94a08 : word) = Some W_94a08.
Proof. vm_refl. Qed.
Lemma D_94a08 : decode_any W_94a08 = Some (Load SZ8 true 8 2 96, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_94a0c : bv 32 := 0x05813483.
Lemma F_94a0c : fetch_word AsanUbsan.M.loaded_segments (0x94a0c : word) = Some W_94a0c.
Proof. vm_refl. Qed.
Lemma D_94a0c : decode_any W_94a0c = Some (Load SZ8 true 9 2 88, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_94a10 : bv 32 := 0x05013903.
Lemma F_94a10 : fetch_word AsanUbsan.M.loaded_segments (0x94a10 : word) = Some W_94a10.
Proof. vm_refl. Qed.
Lemma D_94a10 : decode_any W_94a10 = Some (Load SZ8 true 18 2 80, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_94a14 : bv 32 := 0x04813983.
Lemma F_94a14 : fetch_word AsanUbsan.M.loaded_segments (0x94a14 : word) = Some W_94a14.
Proof. vm_refl. Qed.
Lemma D_94a14 : decode_any W_94a14 = Some (Load SZ8 true 19 2 72, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_94a18 : bv 32 := 0x04013a03.
Lemma F_94a18 : fetch_word AsanUbsan.M.loaded_segments (0x94a18 : word) = Some W_94a18.
Proof. vm_refl. Qed.
Lemma D_94a18 : decode_any W_94a18 = Some (Load SZ8 true 20 2 64, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_94a1c : bv 32 := 0x03813a83.
Lemma F_94a1c : fetch_word AsanUbsan.M.loaded_segments (0x94a1c : word) = Some W_94a1c.
Proof. vm_refl. Qed.
Lemma D_94a1c : decode_any W_94a1c = Some (Load SZ8 true 21 2 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_94a20 : bv 32 := 0x03013b03.
Lemma F_94a20 : fetch_word AsanUbsan.M.loaded_segments (0x94a20 : word) = Some W_94a20.
Proof. vm_refl. Qed.
Lemma D_94a20 : decode_any W_94a20 = Some (Load SZ8 true 22 2 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_94a24 : bv 32 := 0x07010113.
Lemma F_94a24 : fetch_word AsanUbsan.M.loaded_segments (0x94a24 : word) = Some W_94a24.
Proof. vm_refl. Qed.
Lemma D_94a24 : decode_any W_94a24 = Some (OpImm ALU_ADD 2 2 112, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_94a28 : bv 32 := 0x00008067.
Lemma F_94a28 : fetch_word AsanUbsan.M.loaded_segments (0x94a28 : word) = Some W_94a28.
Proof. vm_refl. Qed.
Lemma D_94a28 : decode_any W_94a28 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_94a2c : bv 32 := 0x00800713.
Lemma F_94a2c : fetch_word AsanUbsan.M.loaded_segments (0x94a2c : word) = Some W_94a2c.
Proof. vm_refl. Qed.
Lemma D_94a2c : decode_any W_94a2c = Some (OpImm ALU_ADD 14 0 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_94a30 : bv 32 := 0x000a0593.
Lemma F_94a30 : fetch_word AsanUbsan.M.loaded_segments (0x94a30 : word) = Some W_94a30.
Proof. vm_refl. Qed.
Lemma D_94a30 : decode_any W_94a30 = Some (OpImm ALU_ADD 11 20 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_94a34 : bv 32 := 0x00e98733.
Lemma F_94a34 : fetch_word AsanUbsan.M.loaded_segments (0x94a34 : word) = Some W_94a34.
Proof. vm_refl. Qed.
Lemma D_94a34 : decode_any W_94a34 = Some (Op ALU_ADD 14 19 14, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_94a38 : bv 32 := 0x00073783.
Lemma F_94a38 : fetch_word AsanUbsan.M.loaded_segments (0x94a38 : word) = Some W_94a38.
Proof. vm_refl. Qed.
Lemma D_94a38 : decode_any W_94a38 = Some (Load SZ8 true 15 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_94a3c : bv 32 := 0x40ab0b33.
Lemma F_94a3c : fetch_word AsanUbsan.M.loaded_segments (0x94a3c : word) = Some W_94a3c.
Proof. vm_refl. Qed.
Lemma D_94a3c : decode_any W_94a3c = Some (Op ALU_SUB 22 22 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_94a40 : bv 32 := 0x0784a503.
Lemma F_94a40 : fetch_word AsanUbsan.M.loaded_segments (0x94a40 : word) = Some W_94a40.
Proof. vm_refl. Qed.
Lemma D_94a40 : decode_any W_94a40 = Some (Load SZ4 true 10 9 120, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_94a44 : bv 32 := 0x40c9093b.
Lemma F_94a44 : fetch_word AsanUbsan.M.loaded_segments (0x94a44 : word) = Some W_94a44.
Proof. vm_refl. Qed.
Lemma D_94a44 : decode_any W_94a44 = Some (Op32 ALU_SUB 18 18 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_94a48 : bv 32 := 0x40d787b3.
Lemma F_94a48 : fetch_word AsanUbsan.M.loaded_segments (0x94a48 : word) = Some W_94a48.
Proof. vm_refl. Qed.
Lemma D_94a48 : decode_any W_94a48 = Some (Op ALU_SUB 15 15 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_94a4c : bv 32 := 0x00f73023.
Lemma F_94a4c : fetch_word AsanUbsan.M.loaded_segments (0x94a4c : word) = Some W_94a4c.
Proof. vm_refl. Qed.
Lemma D_94a4c : decode_any W_94a4c = Some (Store SZ8 14 15 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_94a50 : bv 32 := 0x04200893.
Lemma F_94a50 : fetch_word AsanUbsan.M.loaded_segments (0x94a50 : word) = Some W_94a50.
Proof. vm_refl. Qed.
Lemma D_94a50 : decode_any W_94a50 = Some (OpImm ALU_ADD 17 0 66, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_94a54 : bv 32 := 0x00090613.
Lemma F_94a54 : fetch_word AsanUbsan.M.loaded_segments (0x94a54 : word) = Some W_94a54.
Proof. vm_refl. Qed.
Lemma D_94a54 : decode_any W_94a54 = Some (OpImm ALU_ADD 12 18 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_94a58 : bv 32 := 0x00000073.
Lemma F_94a58 : fetch_word AsanUbsan.M.loaded_segments (0x94a58 : word) = Some W_94a58.
Proof. vm_refl. Qed.
Lemma D_94a58 : decode_any W_94a58 = Some (Ecall, 4%Z).
Proof. vm_refl. Qed.
Lemma E_94a58 : is_ecall W_94a58 = true.
Proof. reflexivity. Qed.

(* [comment removed for export] *)
Definition W_94a5c : bv 32 := 0xd35fa0ef.
Lemma F_94a5c : fetch_word AsanUbsan.M.loaded_segments (0x94a5c : word) = Some W_94a5c.
Proof. vm_refl. Qed.
Lemma D_94a5c : decode_any W_94a5c = Some (Jal 1 2075956, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_94a60 : bv 32 := 0x000a0993.
Lemma F_94a60 : fetch_word AsanUbsan.M.loaded_segments (0x94a60 : word) = Some W_94a60.
Proof. vm_refl. Qed.
Lemma D_94a60 : decode_any W_94a60 = Some (OpImm ALU_ADD 19 20 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_94a64 : bv 32 := 0xf7650ce3.
Lemma F_94a64 : fetch_word AsanUbsan.M.loaded_segments (0x94a64 : word) = Some W_94a64.
Proof. vm_refl. Qed.
Lemma D_94a64 : decode_any W_94a64 = Some (Branch BC_EQ 10 22 8056, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_94a68 : bv 32 := 0x02054c63.
Lemma F_94a68 : fetch_word AsanUbsan.M.loaded_segments (0x94a68 : word) = Some W_94a68.
Proof. vm_refl. Qed.
Lemma D_94a68 : decode_any W_94a68 = Some (Branch BC_LT 10 0 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_94a6c : bv 32 := 0x0089b583.
Lemma F_94a6c : fetch_word AsanUbsan.M.loaded_segments (0x94a6c : word) = Some W_94a6c.
Proof. vm_refl. Qed.
Lemma D_94a6c : decode_any W_94a6c = Some (Load SZ8 true 11 19 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_94a70 : bv 32 := 0x00a5b633.
Lemma F_94a70 : fetch_word AsanUbsan.M.loaded_segments (0x94a70 : word) = Some W_94a70.
Proof. vm_refl. Qed.
Lemma D_94a70 : decode_any W_94a70 = Some (Op ALU_SLTU 12 11 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_94a74 : bv 32 := 0x00461a13.
Lemma F_94a74 : fetch_word AsanUbsan.M.loaded_segments (0x94a74 : word) = Some W_94a74.
Proof. vm_refl. Qed.
Lemma D_94a74 : decode_any W_94a74 = Some (ShiftImm ALU_SLL 20 12 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_94a78 : bv 32 := 0x01498a33.
Lemma F_94a78 : fetch_word AsanUbsan.M.loaded_segments (0x94a78 : word) = Some W_94a78.
Proof. vm_refl. Qed.
Lemma D_94a78 : decode_any W_94a78 = Some (Op ALU_ADD 20 19 20, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_94a7c : bv 32 := 0x000a3703.
Lemma F_94a7c : fetch_word AsanUbsan.M.loaded_segments (0x94a7c : word) = Some W_94a7c.
Proof. vm_refl. Qed.
Lemma D_94a7c : decode_any W_94a7c = Some (Load SZ8 true 14 20 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_94a80 : bv 32 := 0x40c006b3.
Lemma F_94a80 : fetch_word AsanUbsan.M.loaded_segments (0x94a80 : word) = Some W_94a80.
Proof. vm_refl. Qed.
Lemma D_94a80 : decode_any W_94a80 = Some (Op ALU_SUB 13 0 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_94a84 : bv 32 := 0x00b6f6b3.
Lemma F_94a84 : fetch_word AsanUbsan.M.loaded_segments (0x94a84 : word) = Some W_94a84.
Proof. vm_refl. Qed.
Lemma D_94a84 : decode_any W_94a84 = Some (Op ALU_AND 13 13 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_94a88 : bv 32 := 0x40d506b3.
Lemma F_94a88 : fetch_word AsanUbsan.M.loaded_segments (0x94a88 : word) = Some W_94a88.
Proof. vm_refl. Qed.
Lemma D_94a88 : decode_any W_94a88 = Some (Op ALU_SUB 13 10 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_94a8c : bv 32 := 0x00d70733.
Lemma F_94a8c : fetch_word AsanUbsan.M.loaded_segments (0x94a8c : word) = Some W_94a8c.
Proof. vm_refl. Qed.
Lemma D_94a8c : decode_any W_94a8c = Some (Op ALU_ADD 14 14 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_94a90 : bv 32 := 0x00ea3023.
Lemma F_94a90 : fetch_word AsanUbsan.M.loaded_segments (0x94a90 : word) = Some W_94a90.
Proof. vm_refl. Qed.
Lemma D_94a90 : decode_any W_94a90 = Some (Store SZ8 20 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_94a94 : bv 32 := 0xf8a5fce3.
Lemma F_94a94 : fetch_word AsanUbsan.M.loaded_segments (0x94a94 : word) = Some W_94a94.
Proof. vm_refl. Qed.
Lemma D_94a94 : decode_any W_94a94 = Some (Branch BC_GEU 11 10 8088, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_94a98 : bv 32 := 0x01800713.
Lemma F_94a98 : fetch_word AsanUbsan.M.loaded_segments (0x94a98 : word) = Some W_94a98.
Proof. vm_refl. Qed.
Lemma D_94a98 : decode_any W_94a98 = Some (OpImm ALU_ADD 14 0 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_94a9c : bv 32 := 0xf95ff06f.
Lemma F_94a9c : fetch_word AsanUbsan.M.loaded_segments (0x94a9c : word) = Some W_94a9c.
Proof. vm_refl. Qed.
Lemma D_94a9c : decode_any W_94a9c = Some (Jal 0 2097044, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_94aa0 : bv 32 := 0x00000513.
Lemma F_94aa0 : fetch_word AsanUbsan.M.loaded_segments (0x94aa0 : word) = Some W_94aa0.
Proof. vm_refl. Qed.
Lemma D_94aa0 : decode_any W_94aa0 = Some (OpImm ALU_ADD 10 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_94aa4 : bv 32 := 0x0004a583.
Lemma F_94aa4 : fetch_word AsanUbsan.M.loaded_segments (0x94aa4 : word) = Some W_94aa4.
Proof. vm_refl. Qed.
Lemma D_94aa4 : decode_any W_94aa4 = Some (Load SZ4 true 11 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_94aa8 : bv 32 := 0x0009091b.
Lemma F_94aa8 : fetch_word AsanUbsan.M.loaded_segments (0x94aa8 : word) = Some W_94aa8.
Proof. vm_refl. Qed.
Lemma D_94aa8 : decode_any W_94aa8 = Some (OpImm32 18 18 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_94aac : bv 32 := 0x00200613.
Lemma F_94aac : fetch_word AsanUbsan.M.loaded_segments (0x94aac : word) = Some W_94aac.
Proof. vm_refl. Qed.
Lemma D_94aac : decode_any W_94aac = Some (OpImm ALU_ADD 12 0 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_94ab0 : bv 32 := 0x0205e593.
Lemma F_94ab0 : fetch_word AsanUbsan.M.loaded_segments (0x94ab0 : word) = Some W_94ab0.
Proof. vm_refl. Qed.
Lemma D_94ab0 : decode_any W_94ab0 = Some (OpImm ALU_OR 11 11 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_94ab4 : bv 32 := 0x00b4a023.
Lemma F_94ab4 : fetch_word AsanUbsan.M.loaded_segments (0x94ab4 : word) = Some W_94ab4.
Proof. vm_refl. Qed.
Lemma D_94ab4 : decode_any W_94ab4 = Some (Store SZ4 9 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_94ab8 : bv 32 := 0x0204b023.
Lemma F_94ab8 : fetch_word AsanUbsan.M.loaded_segments (0x94ab8 : word) = Some W_94ab8.
Proof. vm_refl. Qed.
Lemma D_94ab8 : decode_any W_94ab8 = Some (Store SZ8 9 0 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_94abc : bv 32 := 0x0204b423.
Lemma F_94abc : fetch_word AsanUbsan.M.loaded_segments (0x94abc : word) = Some W_94abc.
Proof. vm_refl. Qed.
Lemma D_94abc : decode_any W_94abc = Some (Store SZ8 9 0 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_94ac0 : bv 32 := 0x0204bc23.
Lemma F_94ac0 : fetch_word AsanUbsan.M.loaded_segments (0x94ac0 : word) = Some W_94ac0.
Proof. vm_refl. Qed.
Lemma D_94ac0 : decode_any W_94ac0 = Some (Store SZ8 9 0 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_94ac4 : bv 32 := 0xf2c90ae3.
Lemma F_94ac4 : fetch_word AsanUbsan.M.loaded_segments (0x94ac4 : word) = Some W_94ac4.
Proof. vm_refl. Qed.
Lemma D_94ac4 : decode_any W_94ac4 = Some (Branch BC_EQ 18 12 7988, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_94ac8 : bv 32 := 0x0089b503.
Lemma F_94ac8 : fetch_word AsanUbsan.M.loaded_segments (0x94ac8 : word) = Some W_94ac8.
Proof. vm_refl. Qed.
Lemma D_94ac8 : decode_any W_94ac8 = Some (Load SZ8 true 10 19 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_94acc : bv 32 := 0x40a40533.
Lemma F_94acc : fetch_word AsanUbsan.M.loaded_segments (0x94acc : word) = Some W_94acc.
Proof. vm_refl. Qed.
Lemma D_94acc : decode_any W_94acc = Some (Op ALU_SUB 10 8 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_94ad0 : bv 32 := 0xf29ff06f.
Lemma F_94ad0 : fetch_word AsanUbsan.M.loaded_segments (0x94ad0 : word) = Some W_94ad0.
Proof. vm_refl. Qed.
Lemma D_94ad0 : decode_any W_94ad0 = Some (Jal 0 2096936, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_94ad4 : bv 32 := 0xe50fa0ef.
Lemma F_94ad4 : fetch_word AsanUbsan.M.loaded_segments (0x94ad4 : word) = Some W_94ad4.
Proof. vm_refl. Qed.
Lemma D_94ad4 : decode_any W_94ad4 = Some (Jal 1 2074192, 4%Z).
Proof. vm_refl. Qed.
