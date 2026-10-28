(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OssFuzzTheorems.openssl.hashtable.images Require Import AsanUbsan.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.

(* [comment removed for export] *)
Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

(* [comment removed for export] *)
Definition W_522930 : bv 32 := 0xf9010113.
Lemma F_522930 : fetch_word AsanUbsan.M.loaded_segments (0x55b4a8 : word) = Some W_522930.
Proof. vm_refl. Qed.
Lemma D_522930 : decode_any W_522930 = Some (OpImm ALU_ADD 2 2 3984, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_522934 : bv 32 := 0x06113423.
Lemma F_522934 : fetch_word AsanUbsan.M.loaded_segments (0x55b4ac : word) = Some W_522934.
Proof. vm_refl. Qed.
Lemma D_522934 : decode_any W_522934 = Some (Store SZ8 2 1 104, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_522938 : bv 32 := 0x06813023.
Lemma F_522938 : fetch_word AsanUbsan.M.loaded_segments (0x55b4b0 : word) = Some W_522938.
Proof. vm_refl. Qed.
Lemma D_522938 : decode_any W_522938 = Some (Store SZ8 2 8 96, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52293c : bv 32 := 0x04913c23.
Lemma F_52293c : fetch_word AsanUbsan.M.loaded_segments (0x55b4b4 : word) = Some W_52293c.
Proof. vm_refl. Qed.
Lemma D_52293c : decode_any W_52293c = Some (Store SZ8 2 9 88, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_522940 : bv 32 := 0x05213823.
Lemma F_522940 : fetch_word AsanUbsan.M.loaded_segments (0x55b4b8 : word) = Some W_522940.
Proof. vm_refl. Qed.
Lemma D_522940 : decode_any W_522940 = Some (Store SZ8 2 18 80, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_522944 : bv 32 := 0x05313423.
Lemma F_522944 : fetch_word AsanUbsan.M.loaded_segments (0x55b4bc : word) = Some W_522944.
Proof. vm_refl. Qed.
Lemma D_522944 : decode_any W_522944 = Some (Store SZ8 2 19 72, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_522948 : bv 32 := 0x05413023.
Lemma F_522948 : fetch_word AsanUbsan.M.loaded_segments (0x55b4c0 : word) = Some W_522948.
Proof. vm_refl. Qed.
Lemma D_522948 : decode_any W_522948 = Some (Store SZ8 2 20 64, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52294c : bv 32 := 0x03513c23.
Lemma F_52294c : fetch_word AsanUbsan.M.loaded_segments (0x55b4c4 : word) = Some W_52294c.
Proof. vm_refl. Qed.
Lemma D_52294c : decode_any W_52294c = Some (Store SZ8 2 21 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_522950 : bv 32 := 0x03613823.
Lemma F_522950 : fetch_word AsanUbsan.M.loaded_segments (0x55b4c8 : word) = Some W_522950.
Proof. vm_refl. Qed.
Lemma D_522950 : decode_any W_522950 = Some (Store SZ8 2 22 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_522954 : bv 32 := 0x00060413.
Lemma F_522954 : fetch_word AsanUbsan.M.loaded_segments (0x55b4cc : word) = Some W_522954.
Proof. vm_refl. Qed.
Lemma D_522954 : decode_any W_522954 = Some (OpImm ALU_ADD 8 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_522958 : bv 32 := 0x00050493.
Lemma F_522958 : fetch_word AsanUbsan.M.loaded_segments (0x55b4d0 : word) = Some W_522958.
Proof. vm_refl. Qed.
Lemma D_522958 : decode_any W_522958 = Some (OpImm ALU_ADD 9 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52295c : bv 32 := 0x00085517.
Lemma F_52295c : fetch_word AsanUbsan.M.loaded_segments (0x55b4d4 : word) = Some W_52295c.
Proof. vm_refl. Qed.
Lemma D_52295c : decode_any W_52295c = Some (Auipc 10 133, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_522960 : bv 32 := 0x57453a83.
Lemma F_522960 : fetch_word AsanUbsan.M.loaded_segments (0x55b4d8 : word) = Some W_522960.
Proof. vm_refl. Qed.
Lemma D_522960 : decode_any W_522960 = Some (Load SZ8 true 21 10 1396, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_522964 : bv 32 := 0x000ab503.
Lemma F_522964 : fetch_word AsanUbsan.M.loaded_segments (0x55b4dc : word) = Some W_522964.
Proof. vm_refl. Qed.
Lemma D_522964 : decode_any W_522964 = Some (Load SZ8 true 10 21 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_522968 : bv 32 := 0x02a13423.
Lemma F_522968 : fetch_word AsanUbsan.M.loaded_segments (0x55b4e0 : word) = Some W_522968.
Proof. vm_refl. Qed.
Lemma D_522968 : decode_any W_522968 = Some (Store SZ8 2 10 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52296c : bv 32 := 0x0284b503.
Lemma F_52296c : fetch_word AsanUbsan.M.loaded_segments (0x55b4e4 : word) = Some W_52296c.
Proof. vm_refl. Qed.
Lemma D_52296c : decode_any W_52296c = Some (Load SZ8 true 10 9 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_522970 : bv 32 := 0x0384b603.
Lemma F_522970 : fetch_word AsanUbsan.M.loaded_segments (0x55b4e8 : word) = Some W_522970.
Proof. vm_refl. Qed.
Lemma D_522970 : decode_any W_522970 = Some (Load SZ8 true 12 9 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_522974 : bv 32 := 0x40c50b33.
Lemma F_522974 : fetch_word AsanUbsan.M.loaded_segments (0x55b4ec : word) = Some W_522974.
Proof. vm_refl. Qed.
Lemma D_522974 : decode_any W_522974 = Some (Op ALU_SUB 22 10 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_522978 : bv 32 := 0x00c546b3.
Lemma F_522978 : fetch_word AsanUbsan.M.loaded_segments (0x55b4f0 : word) = Some W_522978.
Proof. vm_refl. Qed.
Lemma D_522978 : decode_any W_522978 = Some (Op ALU_XOR 13 10 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52297c : bv 32 := 0x00c13423.
Lemma F_52297c : fetch_word AsanUbsan.M.loaded_segments (0x55b4f4 : word) = Some W_52297c.
Proof. vm_refl. Qed.
Lemma D_52297c : decode_any W_52297c = Some (Store SZ8 2 12 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_522980 : bv 32 := 0x01613823.
Lemma F_522980 : fetch_word AsanUbsan.M.loaded_segments (0x55b4f8 : word) = Some W_522980.
Proof. vm_refl. Qed.
Lemma D_522980 : decode_any W_522980 = Some (Store SZ8 2 22 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_522984 : bv 32 := 0x00b13c23.
Lemma F_522984 : fetch_word AsanUbsan.M.loaded_segments (0x55b4fc : word) = Some W_522984.
Proof. vm_refl. Qed.
Lemma D_522984 : decode_any W_522984 = Some (Store SZ8 2 11 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_522988 : bv 32 := 0x02813023.
Lemma F_522988 : fetch_word AsanUbsan.M.loaded_segments (0x55b500 : word) = Some W_522988.
Proof. vm_refl. Qed.
Lemma D_522988 : decode_any W_522988 = Some (Store SZ8 2 8 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52298c : bv 32 := 0x008b0b33.
Lemma F_52298c : fetch_word AsanUbsan.M.loaded_segments (0x55b504 : word) = Some W_52298c.
Proof. vm_refl. Qed.
Lemma D_52298c : decode_any W_52298c = Some (Op ALU_ADD 22 22 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_522990 : bv 32 := 0x00d03933.
Lemma F_522990 : fetch_word AsanUbsan.M.loaded_segments (0x55b508 : word) = Some W_522990.
Proof. vm_refl. Qed.
Lemma D_522990 : decode_any W_522990 = Some (Op ALU_SLTU 18 0 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_522994 : bv 32 := 0x00c50663.
Lemma F_522994 : fetch_word AsanUbsan.M.loaded_segments (0x55b50c : word) = Some W_522994.
Proof. vm_refl. Qed.
Lemma D_522994 : decode_any W_522994 = Some (Branch BC_EQ 10 12 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_522998 : bv 32 := 0x00810993.
Lemma F_522998 : fetch_word AsanUbsan.M.loaded_segments (0x55b510 : word) = Some W_522998.
Proof. vm_refl. Qed.
Lemma D_522998 : decode_any W_522998 = Some (OpImm ALU_ADD 19 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_52299c : bv 32 := 0x0080006f.
Lemma F_52299c : fetch_word AsanUbsan.M.loaded_segments (0x55b514 : word) = Some W_52299c.
Proof. vm_refl. Qed.
Lemma D_52299c : decode_any W_52299c = Some (Jal 0 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5229a0 : bv 32 := 0x01810993.
Lemma F_5229a0 : fetch_word AsanUbsan.M.loaded_segments (0x55b518 : word) = Some W_5229a0.
Proof. vm_refl. Qed.
Lemma D_5229a0 : decode_any W_5229a0 = Some (OpImm ALU_ADD 19 2 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5229a4 : bv 32 := 0x0784a503.
Lemma F_5229a4 : fetch_word AsanUbsan.M.loaded_segments (0x55b51c : word) = Some W_5229a4.
Proof. vm_refl. Qed.
Lemma D_5229a4 : decode_any W_5229a4 = Some (Load SZ4 true 10 9 120, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5229a8 : bv 32 := 0x00190913.
Lemma F_5229a8 : fetch_word AsanUbsan.M.loaded_segments (0x55b520 : word) = Some W_5229a8.
Proof. vm_refl. Qed.
Lemma D_5229a8 : decode_any W_5229a8 = Some (OpImm ALU_ADD 18 18 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5229ac : bv 32 := 0x04200893.
Lemma F_5229ac : fetch_word AsanUbsan.M.loaded_segments (0x55b524 : word) = Some W_5229ac.
Proof. vm_refl. Qed.
Lemma D_5229ac : decode_any W_5229ac = Some (OpImm ALU_ADD 17 0 66, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5229b0 : bv 32 := 0x00098593.
Lemma F_5229b0 : fetch_word AsanUbsan.M.loaded_segments (0x55b528 : word) = Some W_5229b0.
Proof. vm_refl. Qed.
Lemma D_5229b0 : decode_any W_5229b0 = Some (OpImm ALU_ADD 11 19 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5229b4 : bv 32 := 0x00090613.
Lemma F_5229b4 : fetch_word AsanUbsan.M.loaded_segments (0x55b52c : word) = Some W_5229b4.
Proof. vm_refl. Qed.
Lemma D_5229b4 : decode_any W_5229b4 = Some (OpImm ALU_ADD 12 18 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5229b8 : bv 32 := 0x00000073.
Lemma F_5229b8 : fetch_word AsanUbsan.M.loaded_segments (0x55b530 : word) = Some W_5229b8.
Proof. vm_refl. Qed.
Lemma D_5229b8 : decode_any W_5229b8 = Some (Ecall, 4%Z).
Proof. vm_refl. Qed.
Lemma E_5229b8 : is_ecall W_5229b8 = true.
Proof. reflexivity. Qed.

(* [comment removed for export] *)
Definition W_5229bc : bv 32 := 0xfacfa0ef.
Lemma F_5229bc : fetch_word AsanUbsan.M.loaded_segments (0x55b534 : word) = Some W_5229bc.
Proof. vm_refl. Qed.
Lemma D_5229bc : decode_any W_5229bc = Some (Jal 1 2074540, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5229c0 : bv 32 := 0x09651863.
Lemma F_5229c0 : fetch_word AsanUbsan.M.loaded_segments (0x55b538 : word) = Some W_5229c0.
Proof. vm_refl. Qed.
Lemma D_5229c0 : decode_any W_5229c0 = Some (Branch BC_NE 10 22 144, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5229c4 : bv 32 := 0x0584b503.
Lemma F_5229c4 : fetch_word AsanUbsan.M.loaded_segments (0x55b53c : word) = Some W_5229c4.
Proof. vm_refl. Qed.
Lemma D_5229c4 : decode_any W_5229c4 = Some (Load SZ8 true 10 9 88, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5229c8 : bv 32 := 0x0604b583.
Lemma F_5229c8 : fetch_word AsanUbsan.M.loaded_segments (0x55b540 : word) = Some W_5229c8.
Proof. vm_refl. Qed.
Lemma D_5229c8 : decode_any W_5229c8 = Some (Load SZ8 true 11 9 96, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5229cc : bv 32 := 0x00b505b3.
Lemma F_5229cc : fetch_word AsanUbsan.M.loaded_segments (0x55b544 : word) = Some W_5229cc.
Proof. vm_refl. Qed.
Lemma D_5229cc : decode_any W_5229cc = Some (Op ALU_ADD 11 10 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5229d0 : bv 32 := 0x02b4b023.
Lemma F_5229d0 : fetch_word AsanUbsan.M.loaded_segments (0x55b548 : word) = Some W_5229d0.
Proof. vm_refl. Qed.
Lemma D_5229d0 : decode_any W_5229d0 = Some (Store SZ8 9 11 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5229d4 : bv 32 := 0x02a4b423.
Lemma F_5229d4 : fetch_word AsanUbsan.M.loaded_segments (0x55b54c : word) = Some W_5229d4.
Proof. vm_refl. Qed.
Lemma D_5229d4 : decode_any W_5229d4 = Some (Store SZ8 9 10 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5229d8 : bv 32 := 0x02a4bc23.
Lemma F_5229d8 : fetch_word AsanUbsan.M.loaded_segments (0x55b550 : word) = Some W_5229d8.
Proof. vm_refl. Qed.
Lemma D_5229d8 : decode_any W_5229d8 = Some (Store SZ8 9 10 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5229dc : bv 32 := 0x00040513.
Lemma F_5229dc : fetch_word AsanUbsan.M.loaded_segments (0x55b554 : word) = Some W_5229dc.
Proof. vm_refl. Qed.
Lemma D_5229dc : decode_any W_5229dc = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5229e0 : bv 32 := 0x000ab583.
Lemma F_5229e0 : fetch_word AsanUbsan.M.loaded_segments (0x55b558 : word) = Some W_5229e0.
Proof. vm_refl. Qed.
Lemma D_5229e0 : decode_any W_5229e0 = Some (Load SZ8 true 11 21 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5229e4 : bv 32 := 0x02813603.
Lemma F_5229e4 : fetch_word AsanUbsan.M.loaded_segments (0x55b55c : word) = Some W_5229e4.
Proof. vm_refl. Qed.
Lemma D_5229e4 : decode_any W_5229e4 = Some (Load SZ8 true 12 2 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5229e8 : bv 32 := 0x0cc59a63.
Lemma F_5229e8 : fetch_word AsanUbsan.M.loaded_segments (0x55b560 : word) = Some W_5229e8.
Proof. vm_refl. Qed.
Lemma D_5229e8 : decode_any W_5229e8 = Some (Branch BC_NE 11 12 212, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5229ec : bv 32 := 0x06813083.
Lemma F_5229ec : fetch_word AsanUbsan.M.loaded_segments (0x55b564 : word) = Some W_5229ec.
Proof. vm_refl. Qed.
Lemma D_5229ec : decode_any W_5229ec = Some (Load SZ8 true 1 2 104, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5229f0 : bv 32 := 0x06013403.
Lemma F_5229f0 : fetch_word AsanUbsan.M.loaded_segments (0x55b568 : word) = Some W_5229f0.
Proof. vm_refl. Qed.
Lemma D_5229f0 : decode_any W_5229f0 = Some (Load SZ8 true 8 2 96, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5229f4 : bv 32 := 0x05813483.
Lemma F_5229f4 : fetch_word AsanUbsan.M.loaded_segments (0x55b56c : word) = Some W_5229f4.
Proof. vm_refl. Qed.
Lemma D_5229f4 : decode_any W_5229f4 = Some (Load SZ8 true 9 2 88, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5229f8 : bv 32 := 0x05013903.
Lemma F_5229f8 : fetch_word AsanUbsan.M.loaded_segments (0x55b570 : word) = Some W_5229f8.
Proof. vm_refl. Qed.
Lemma D_5229f8 : decode_any W_5229f8 = Some (Load SZ8 true 18 2 80, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5229fc : bv 32 := 0x04813983.
Lemma F_5229fc : fetch_word AsanUbsan.M.loaded_segments (0x55b574 : word) = Some W_5229fc.
Proof. vm_refl. Qed.
Lemma D_5229fc : decode_any W_5229fc = Some (Load SZ8 true 19 2 72, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_522a00 : bv 32 := 0x04013a03.
Lemma F_522a00 : fetch_word AsanUbsan.M.loaded_segments (0x55b578 : word) = Some W_522a00.
Proof. vm_refl. Qed.
Lemma D_522a00 : decode_any W_522a00 = Some (Load SZ8 true 20 2 64, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_522a04 : bv 32 := 0x03813a83.
Lemma F_522a04 : fetch_word AsanUbsan.M.loaded_segments (0x55b57c : word) = Some W_522a04.
Proof. vm_refl. Qed.
Lemma D_522a04 : decode_any W_522a04 = Some (Load SZ8 true 21 2 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_522a08 : bv 32 := 0x03013b03.
Lemma F_522a08 : fetch_word AsanUbsan.M.loaded_segments (0x55b580 : word) = Some W_522a08.
Proof. vm_refl. Qed.
Lemma D_522a08 : decode_any W_522a08 = Some (Load SZ8 true 22 2 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_522a0c : bv 32 := 0x07010113.
Lemma F_522a0c : fetch_word AsanUbsan.M.loaded_segments (0x55b584 : word) = Some W_522a0c.
Proof. vm_refl. Qed.
Lemma D_522a0c : decode_any W_522a0c = Some (OpImm ALU_ADD 2 2 112, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_522a10 : bv 32 := 0x00008067.
Lemma F_522a10 : fetch_word AsanUbsan.M.loaded_segments (0x55b588 : word) = Some W_522a10.
Proof. vm_refl. Qed.
Lemma D_522a10 : decode_any W_522a10 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_522a14 : bv 32 := 0x00800713.
Lemma F_522a14 : fetch_word AsanUbsan.M.loaded_segments (0x55b58c : word) = Some W_522a14.
Proof. vm_refl. Qed.
Lemma D_522a14 : decode_any W_522a14 = Some (OpImm ALU_ADD 14 0 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_522a18 : bv 32 := 0x000a0593.
Lemma F_522a18 : fetch_word AsanUbsan.M.loaded_segments (0x55b590 : word) = Some W_522a18.
Proof. vm_refl. Qed.
Lemma D_522a18 : decode_any W_522a18 = Some (OpImm ALU_ADD 11 20 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_522a1c : bv 32 := 0x00e98733.
Lemma F_522a1c : fetch_word AsanUbsan.M.loaded_segments (0x55b594 : word) = Some W_522a1c.
Proof. vm_refl. Qed.
Lemma D_522a1c : decode_any W_522a1c = Some (Op ALU_ADD 14 19 14, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_522a20 : bv 32 := 0x00073783.
Lemma F_522a20 : fetch_word AsanUbsan.M.loaded_segments (0x55b598 : word) = Some W_522a20.
Proof. vm_refl. Qed.
Lemma D_522a20 : decode_any W_522a20 = Some (Load SZ8 true 15 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_522a24 : bv 32 := 0x40ab0b33.
Lemma F_522a24 : fetch_word AsanUbsan.M.loaded_segments (0x55b59c : word) = Some W_522a24.
Proof. vm_refl. Qed.
Lemma D_522a24 : decode_any W_522a24 = Some (Op ALU_SUB 22 22 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_522a28 : bv 32 := 0x0784a503.
Lemma F_522a28 : fetch_word AsanUbsan.M.loaded_segments (0x55b5a0 : word) = Some W_522a28.
Proof. vm_refl. Qed.
Lemma D_522a28 : decode_any W_522a28 = Some (Load SZ4 true 10 9 120, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_522a2c : bv 32 := 0x40c9093b.
Lemma F_522a2c : fetch_word AsanUbsan.M.loaded_segments (0x55b5a4 : word) = Some W_522a2c.
Proof. vm_refl. Qed.
Lemma D_522a2c : decode_any W_522a2c = Some (Op32 ALU_SUB 18 18 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_522a30 : bv 32 := 0x40d787b3.
Lemma F_522a30 : fetch_word AsanUbsan.M.loaded_segments (0x55b5a8 : word) = Some W_522a30.
Proof. vm_refl. Qed.
Lemma D_522a30 : decode_any W_522a30 = Some (Op ALU_SUB 15 15 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_522a34 : bv 32 := 0x00f73023.
Lemma F_522a34 : fetch_word AsanUbsan.M.loaded_segments (0x55b5ac : word) = Some W_522a34.
Proof. vm_refl. Qed.
Lemma D_522a34 : decode_any W_522a34 = Some (Store SZ8 14 15 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_522a38 : bv 32 := 0x04200893.
Lemma F_522a38 : fetch_word AsanUbsan.M.loaded_segments (0x55b5b0 : word) = Some W_522a38.
Proof. vm_refl. Qed.
Lemma D_522a38 : decode_any W_522a38 = Some (OpImm ALU_ADD 17 0 66, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_522a3c : bv 32 := 0x00090613.
Lemma F_522a3c : fetch_word AsanUbsan.M.loaded_segments (0x55b5b4 : word) = Some W_522a3c.
Proof. vm_refl. Qed.
Lemma D_522a3c : decode_any W_522a3c = Some (OpImm ALU_ADD 12 18 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_522a40 : bv 32 := 0x00000073.
Lemma F_522a40 : fetch_word AsanUbsan.M.loaded_segments (0x55b5b8 : word) = Some W_522a40.
Proof. vm_refl. Qed.
Lemma D_522a40 : decode_any W_522a40 = Some (Ecall, 4%Z).
Proof. vm_refl. Qed.
Lemma E_522a40 : is_ecall W_522a40 = true.
Proof. reflexivity. Qed.

(* [comment removed for export] *)
Definition W_522a44 : bv 32 := 0xf24fa0ef.
Lemma F_522a44 : fetch_word AsanUbsan.M.loaded_segments (0x55b5bc : word) = Some W_522a44.
Proof. vm_refl. Qed.
Lemma D_522a44 : decode_any W_522a44 = Some (Jal 1 2074404, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_522a48 : bv 32 := 0x000a0993.
Lemma F_522a48 : fetch_word AsanUbsan.M.loaded_segments (0x55b5c0 : word) = Some W_522a48.
Proof. vm_refl. Qed.
Lemma D_522a48 : decode_any W_522a48 = Some (OpImm ALU_ADD 19 20 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_522a4c : bv 32 := 0xf7650ce3.
Lemma F_522a4c : fetch_word AsanUbsan.M.loaded_segments (0x55b5c4 : word) = Some W_522a4c.
Proof. vm_refl. Qed.
Lemma D_522a4c : decode_any W_522a4c = Some (Branch BC_EQ 10 22 8056, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_522a50 : bv 32 := 0x02054c63.
Lemma F_522a50 : fetch_word AsanUbsan.M.loaded_segments (0x55b5c8 : word) = Some W_522a50.
Proof. vm_refl. Qed.
Lemma D_522a50 : decode_any W_522a50 = Some (Branch BC_LT 10 0 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_522a54 : bv 32 := 0x0089b583.
Lemma F_522a54 : fetch_word AsanUbsan.M.loaded_segments (0x55b5cc : word) = Some W_522a54.
Proof. vm_refl. Qed.
Lemma D_522a54 : decode_any W_522a54 = Some (Load SZ8 true 11 19 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_522a58 : bv 32 := 0x00a5b633.
Lemma F_522a58 : fetch_word AsanUbsan.M.loaded_segments (0x55b5d0 : word) = Some W_522a58.
Proof. vm_refl. Qed.
Lemma D_522a58 : decode_any W_522a58 = Some (Op ALU_SLTU 12 11 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_522a5c : bv 32 := 0x00461a13.
Lemma F_522a5c : fetch_word AsanUbsan.M.loaded_segments (0x55b5d4 : word) = Some W_522a5c.
Proof. vm_refl. Qed.
Lemma D_522a5c : decode_any W_522a5c = Some (ShiftImm ALU_SLL 20 12 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_522a60 : bv 32 := 0x01498a33.
Lemma F_522a60 : fetch_word AsanUbsan.M.loaded_segments (0x55b5d8 : word) = Some W_522a60.
Proof. vm_refl. Qed.
Lemma D_522a60 : decode_any W_522a60 = Some (Op ALU_ADD 20 19 20, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_522a64 : bv 32 := 0x000a3703.
Lemma F_522a64 : fetch_word AsanUbsan.M.loaded_segments (0x55b5dc : word) = Some W_522a64.
Proof. vm_refl. Qed.
Lemma D_522a64 : decode_any W_522a64 = Some (Load SZ8 true 14 20 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_522a68 : bv 32 := 0x40c006b3.
Lemma F_522a68 : fetch_word AsanUbsan.M.loaded_segments (0x55b5e0 : word) = Some W_522a68.
Proof. vm_refl. Qed.
Lemma D_522a68 : decode_any W_522a68 = Some (Op ALU_SUB 13 0 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_522a6c : bv 32 := 0x00b6f6b3.
Lemma F_522a6c : fetch_word AsanUbsan.M.loaded_segments (0x55b5e4 : word) = Some W_522a6c.
Proof. vm_refl. Qed.
Lemma D_522a6c : decode_any W_522a6c = Some (Op ALU_AND 13 13 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_522a70 : bv 32 := 0x40d506b3.
Lemma F_522a70 : fetch_word AsanUbsan.M.loaded_segments (0x55b5e8 : word) = Some W_522a70.
Proof. vm_refl. Qed.
Lemma D_522a70 : decode_any W_522a70 = Some (Op ALU_SUB 13 10 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_522a74 : bv 32 := 0x00d70733.
Lemma F_522a74 : fetch_word AsanUbsan.M.loaded_segments (0x55b5ec : word) = Some W_522a74.
Proof. vm_refl. Qed.
Lemma D_522a74 : decode_any W_522a74 = Some (Op ALU_ADD 14 14 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_522a78 : bv 32 := 0x00ea3023.
Lemma F_522a78 : fetch_word AsanUbsan.M.loaded_segments (0x55b5f0 : word) = Some W_522a78.
Proof. vm_refl. Qed.
Lemma D_522a78 : decode_any W_522a78 = Some (Store SZ8 20 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_522a7c : bv 32 := 0xf8a5fce3.
Lemma F_522a7c : fetch_word AsanUbsan.M.loaded_segments (0x55b5f4 : word) = Some W_522a7c.
Proof. vm_refl. Qed.
Lemma D_522a7c : decode_any W_522a7c = Some (Branch BC_GEU 11 10 8088, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_522a80 : bv 32 := 0x01800713.
Lemma F_522a80 : fetch_word AsanUbsan.M.loaded_segments (0x55b5f8 : word) = Some W_522a80.
Proof. vm_refl. Qed.
Lemma D_522a80 : decode_any W_522a80 = Some (OpImm ALU_ADD 14 0 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_522a84 : bv 32 := 0xf95ff06f.
Lemma F_522a84 : fetch_word AsanUbsan.M.loaded_segments (0x55b5fc : word) = Some W_522a84.
Proof. vm_refl. Qed.
Lemma D_522a84 : decode_any W_522a84 = Some (Jal 0 2097044, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_522a88 : bv 32 := 0x00000513.
Lemma F_522a88 : fetch_word AsanUbsan.M.loaded_segments (0x55b600 : word) = Some W_522a88.
Proof. vm_refl. Qed.
Lemma D_522a88 : decode_any W_522a88 = Some (OpImm ALU_ADD 10 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_522a8c : bv 32 := 0x0004a583.
Lemma F_522a8c : fetch_word AsanUbsan.M.loaded_segments (0x55b604 : word) = Some W_522a8c.
Proof. vm_refl. Qed.
Lemma D_522a8c : decode_any W_522a8c = Some (Load SZ4 true 11 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_522a90 : bv 32 := 0x0009091b.
Lemma F_522a90 : fetch_word AsanUbsan.M.loaded_segments (0x55b608 : word) = Some W_522a90.
Proof. vm_refl. Qed.
Lemma D_522a90 : decode_any W_522a90 = Some (OpImm32 18 18 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_522a94 : bv 32 := 0x00200613.
Lemma F_522a94 : fetch_word AsanUbsan.M.loaded_segments (0x55b60c : word) = Some W_522a94.
Proof. vm_refl. Qed.
Lemma D_522a94 : decode_any W_522a94 = Some (OpImm ALU_ADD 12 0 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_522a98 : bv 32 := 0x0205e593.
Lemma F_522a98 : fetch_word AsanUbsan.M.loaded_segments (0x55b610 : word) = Some W_522a98.
Proof. vm_refl. Qed.
Lemma D_522a98 : decode_any W_522a98 = Some (OpImm ALU_OR 11 11 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_522a9c : bv 32 := 0x00b4a023.
Lemma F_522a9c : fetch_word AsanUbsan.M.loaded_segments (0x55b614 : word) = Some W_522a9c.
Proof. vm_refl. Qed.
Lemma D_522a9c : decode_any W_522a9c = Some (Store SZ4 9 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_522aa0 : bv 32 := 0x0204b023.
Lemma F_522aa0 : fetch_word AsanUbsan.M.loaded_segments (0x55b618 : word) = Some W_522aa0.
Proof. vm_refl. Qed.
Lemma D_522aa0 : decode_any W_522aa0 = Some (Store SZ8 9 0 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_522aa4 : bv 32 := 0x0204b423.
Lemma F_522aa4 : fetch_word AsanUbsan.M.loaded_segments (0x55b61c : word) = Some W_522aa4.
Proof. vm_refl. Qed.
Lemma D_522aa4 : decode_any W_522aa4 = Some (Store SZ8 9 0 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_522aa8 : bv 32 := 0x0204bc23.
Lemma F_522aa8 : fetch_word AsanUbsan.M.loaded_segments (0x55b620 : word) = Some W_522aa8.
Proof. vm_refl. Qed.
Lemma D_522aa8 : decode_any W_522aa8 = Some (Store SZ8 9 0 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_522aac : bv 32 := 0xf2c90ae3.
Lemma F_522aac : fetch_word AsanUbsan.M.loaded_segments (0x55b624 : word) = Some W_522aac.
Proof. vm_refl. Qed.
Lemma D_522aac : decode_any W_522aac = Some (Branch BC_EQ 18 12 7988, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_522ab0 : bv 32 := 0x0089b503.
Lemma F_522ab0 : fetch_word AsanUbsan.M.loaded_segments (0x55b628 : word) = Some W_522ab0.
Proof. vm_refl. Qed.
Lemma D_522ab0 : decode_any W_522ab0 = Some (Load SZ8 true 10 19 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_522ab4 : bv 32 := 0x40a40533.
Lemma F_522ab4 : fetch_word AsanUbsan.M.loaded_segments (0x55b62c : word) = Some W_522ab4.
Proof. vm_refl. Qed.
Lemma D_522ab4 : decode_any W_522ab4 = Some (Op ALU_SUB 10 8 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_522ab8 : bv 32 := 0xf29ff06f.
Lemma F_522ab8 : fetch_word AsanUbsan.M.loaded_segments (0x55b630 : word) = Some W_522ab8.
Proof. vm_refl. Qed.
Lemma D_522ab8 : decode_any W_522ab8 = Some (Jal 0 2096936, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_522abc : bv 32 := 0x83cfa0ef.
Lemma F_522abc : fetch_word AsanUbsan.M.loaded_segments (0x55b634 : word) = Some W_522abc.
Proof. vm_refl. Qed.
Lemma D_522abc : decode_any W_522abc = Some (Jal 1 2072636, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_522ac0 : bv 32 := 0xfb010113.
Lemma F_522ac0 : fetch_word AsanUbsan.M.loaded_segments (0x55b638 : word) = Some W_522ac0.
Proof. vm_refl. Qed.
Lemma D_522ac0 : decode_any W_522ac0 = Some (OpImm ALU_ADD 2 2 4016, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_522ac4 : bv 32 := 0x00113c23.
Lemma F_522ac4 : fetch_word AsanUbsan.M.loaded_segments (0x55b63c : word) = Some W_522ac4.
Proof. vm_refl. Qed.
Lemma D_522ac4 : decode_any W_522ac4 = Some (Store SZ8 2 1 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_522ac8 : bv 32 := 0x00813823.
Lemma F_522ac8 : fetch_word AsanUbsan.M.loaded_segments (0x55b640 : word) = Some W_522ac8.
Proof. vm_refl. Qed.
Lemma D_522ac8 : decode_any W_522ac8 = Some (Store SZ8 2 8 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_522acc : bv 32 := 0x05013023.
Lemma F_522acc : fetch_word AsanUbsan.M.loaded_segments (0x55b644 : word) = Some W_522acc.
Proof. vm_refl. Qed.
Lemma D_522acc : decode_any W_522acc = Some (Store SZ8 2 16 64, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_522ad0 : bv 32 := 0x05113423.
Lemma F_522ad0 : fetch_word AsanUbsan.M.loaded_segments (0x55b648 : word) = Some W_522ad0.
Proof. vm_refl. Qed.
Lemma D_522ad0 : decode_any W_522ad0 = Some (Store SZ8 2 17 72, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_522ad4 : bv 32 := 0x00085817.
Lemma F_522ad4 : fetch_word AsanUbsan.M.loaded_segments (0x55b64c : word) = Some W_522ad4.
Proof. vm_refl. Qed.
Lemma D_522ad4 : decode_any W_522ad4 = Some (Auipc 16 133, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_522ad8 : bv 32 := 0x3fc83403.
Lemma F_522ad8 : fetch_word AsanUbsan.M.loaded_segments (0x55b650 : word) = Some W_522ad8.
Proof. vm_refl. Qed.
Lemma D_522ad8 : decode_any W_522ad8 = Some (Load SZ8 true 8 16 1020, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_522adc : bv 32 := 0x02c13023.
Lemma F_522adc : fetch_word AsanUbsan.M.loaded_segments (0x55b654 : word) = Some W_522adc.
Proof. vm_refl. Qed.
Lemma D_522adc : decode_any W_522adc = Some (Store SZ8 2 12 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_522ae0 : bv 32 := 0x02d13423.
Lemma F_522ae0 : fetch_word AsanUbsan.M.loaded_segments (0x55b658 : word) = Some W_522ae0.
Proof. vm_refl. Qed.
Lemma D_522ae0 : decode_any W_522ae0 = Some (Store SZ8 2 13 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_522ae4 : bv 32 := 0x02e13823.
Lemma F_522ae4 : fetch_word AsanUbsan.M.loaded_segments (0x55b65c : word) = Some W_522ae4.
Proof. vm_refl. Qed.
Lemma D_522ae4 : decode_any W_522ae4 = Some (Store SZ8 2 14 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_522ae8 : bv 32 := 0x02f13c23.
Lemma F_522ae8 : fetch_word AsanUbsan.M.loaded_segments (0x55b660 : word) = Some W_522ae8.
Proof. vm_refl. Qed.
Lemma D_522ae8 : decode_any W_522ae8 = Some (Store SZ8 2 15 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_522aec : bv 32 := 0x00043603.
Lemma F_522aec : fetch_word AsanUbsan.M.loaded_segments (0x55b664 : word) = Some W_522aec.
Proof. vm_refl. Qed.
Lemma D_522aec : decode_any W_522aec = Some (Load SZ8 true 12 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_522af0 : bv 32 := 0x02010693.
Lemma F_522af0 : fetch_word AsanUbsan.M.loaded_segments (0x55b668 : word) = Some W_522af0.
Proof. vm_refl. Qed.
Lemma D_522af0 : decode_any W_522af0 = Some (OpImm ALU_ADD 13 2 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_522af4 : bv 32 := 0x00c13423.
Lemma F_522af4 : fetch_word AsanUbsan.M.loaded_segments (0x55b66c : word) = Some W_522af4.
Proof. vm_refl. Qed.
Lemma D_522af4 : decode_any W_522af4 = Some (Store SZ8 2 12 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_522af8 : bv 32 := 0x00d13023.
Lemma F_522af8 : fetch_word AsanUbsan.M.loaded_segments (0x55b670 : word) = Some W_522af8.
Proof. vm_refl. Qed.
Lemma D_522af8 : decode_any W_522af8 = Some (Store SZ8 2 13 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_522afc : bv 32 := 0x02010613.
Lemma F_522afc : fetch_word AsanUbsan.M.loaded_segments (0x55b674 : word) = Some W_522afc.
Proof. vm_refl. Qed.
Lemma D_522afc : decode_any W_522afc = Some (OpImm ALU_ADD 12 2 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_522b00 : bv 32 := 0x428010ef.
Lemma F_522b00 : fetch_word AsanUbsan.M.loaded_segments (0x55b678 : word) = Some W_522b00.
Proof. vm_refl. Qed.
Lemma D_522b00 : decode_any W_522b00 = Some (Jal 1 5160, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_522b04 : bv 32 := 0x00043583.
Lemma F_522b04 : fetch_word AsanUbsan.M.loaded_segments (0x55b67c : word) = Some W_522b04.
Proof. vm_refl. Qed.
Lemma D_522b04 : decode_any W_522b04 = Some (Load SZ8 true 11 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_522b08 : bv 32 := 0x00813603.
Lemma F_522b08 : fetch_word AsanUbsan.M.loaded_segments (0x55b680 : word) = Some W_522b08.
Proof. vm_refl. Qed.
Lemma D_522b08 : decode_any W_522b08 = Some (Load SZ8 true 12 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_522b0c : bv 32 := 0x00c59a63.
Lemma F_522b0c : fetch_word AsanUbsan.M.loaded_segments (0x55b684 : word) = Some W_522b0c.
Proof. vm_refl. Qed.
Lemma D_522b0c : decode_any W_522b0c = Some (Branch BC_NE 11 12 20, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_522b10 : bv 32 := 0x01813083.
Lemma F_522b10 : fetch_word AsanUbsan.M.loaded_segments (0x55b688 : word) = Some W_522b10.
Proof. vm_refl. Qed.
Lemma D_522b10 : decode_any W_522b10 = Some (Load SZ8 true 1 2 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_522b14 : bv 32 := 0x01013403.
Lemma F_522b14 : fetch_word AsanUbsan.M.loaded_segments (0x55b68c : word) = Some W_522b14.
Proof. vm_refl. Qed.
Lemma D_522b14 : decode_any W_522b14 = Some (Load SZ8 true 8 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_522b18 : bv 32 := 0x05010113.
Lemma F_522b18 : fetch_word AsanUbsan.M.loaded_segments (0x55b690 : word) = Some W_522b18.
Proof. vm_refl. Qed.
Lemma D_522b18 : decode_any W_522b18 = Some (OpImm ALU_ADD 2 2 80, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_522b1c : bv 32 := 0x00008067.
Lemma F_522b1c : fetch_word AsanUbsan.M.loaded_segments (0x55b694 : word) = Some W_522b1c.
Proof. vm_refl. Qed.
Lemma D_522b1c : decode_any W_522b1c = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_522b20 : bv 32 := 0xfd9f90ef.
Lemma F_522b20 : fetch_word AsanUbsan.M.loaded_segments (0x55b698 : word) = Some W_522b20.
Proof. vm_refl. Qed.
Lemma D_522b20 : decode_any W_522b20 = Some (Jal 1 2072536, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_522b24 : bv 32 := 0x00008067.
Lemma F_522b24 : fetch_word AsanUbsan.M.loaded_segments (0x55b69c : word) = Some W_522b24.
Proof. vm_refl. Qed.
Lemma D_522b24 : decode_any W_522b24 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.
