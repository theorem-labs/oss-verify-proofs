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
Definition W_11394c : bv 32 := 0xf9010113.
Lemma F_11394c : fetch_word BSEGS_I (0x11394c : word) = Some W_11394c.
Proof. vm_refl. Qed.
Lemma D_11394c : decode_any W_11394c = Some (OpImm ALU_ADD 2 2 3984, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_113950 : bv 32 := 0x06113423.
Lemma F_113950 : fetch_word BSEGS_I (0x113950 : word) = Some W_113950.
Proof. vm_refl. Qed.
Lemma D_113950 : decode_any W_113950 = Some (Store SZ8 2 1 104, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_113954 : bv 32 := 0x06813023.
Lemma F_113954 : fetch_word BSEGS_I (0x113954 : word) = Some W_113954.
Proof. vm_refl. Qed.
Lemma D_113954 : decode_any W_113954 = Some (Store SZ8 2 8 96, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_113958 : bv 32 := 0x04913c23.
Lemma F_113958 : fetch_word BSEGS_I (0x113958 : word) = Some W_113958.
Proof. vm_refl. Qed.
Lemma D_113958 : decode_any W_113958 = Some (Store SZ8 2 9 88, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_11395c : bv 32 := 0x05213823.
Lemma F_11395c : fetch_word BSEGS_I (0x11395c : word) = Some W_11395c.
Proof. vm_refl. Qed.
Lemma D_11395c : decode_any W_11395c = Some (Store SZ8 2 18 80, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_113960 : bv 32 := 0x05313423.
Lemma F_113960 : fetch_word BSEGS_I (0x113960 : word) = Some W_113960.
Proof. vm_refl. Qed.
Lemma D_113960 : decode_any W_113960 = Some (Store SZ8 2 19 72, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_113964 : bv 32 := 0x05413023.
Lemma F_113964 : fetch_word BSEGS_I (0x113964 : word) = Some W_113964.
Proof. vm_refl. Qed.
Lemma D_113964 : decode_any W_113964 = Some (Store SZ8 2 20 64, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_113968 : bv 32 := 0x03513c23.
Lemma F_113968 : fetch_word BSEGS_I (0x113968 : word) = Some W_113968.
Proof. vm_refl. Qed.
Lemma D_113968 : decode_any W_113968 = Some (Store SZ8 2 21 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_11396c : bv 32 := 0x03613823.
Lemma F_11396c : fetch_word BSEGS_I (0x11396c : word) = Some W_11396c.
Proof. vm_refl. Qed.
Lemma D_11396c : decode_any W_11396c = Some (Store SZ8 2 22 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_113970 : bv 32 := 0x00060413.
Lemma F_113970 : fetch_word BSEGS_I (0x113970 : word) = Some W_113970.
Proof. vm_refl. Qed.
Lemma D_113970 : decode_any W_113970 = Some (OpImm ALU_ADD 8 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_113974 : bv 32 := 0x00050493.
Lemma F_113974 : fetch_word BSEGS_I (0x113974 : word) = Some W_113974.
Proof. vm_refl. Qed.
Lemma D_113974 : decode_any W_113974 = Some (OpImm ALU_ADD 9 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_113978 : bv 32 := 0x00017517.
Lemma F_113978 : fetch_word BSEGS_I (0x113978 : word) = Some W_113978.
Proof. vm_refl. Qed.
Lemma D_113978 : decode_any W_113978 = Some (Auipc 10 23, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_11397c : bv 32 := 0x78053a83.
Lemma F_11397c : fetch_word BSEGS_I (0x11397c : word) = Some W_11397c.
Proof. vm_refl. Qed.
Lemma D_11397c : decode_any W_11397c = Some (Load SZ8 true 21 10 1920, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_113980 : bv 32 := 0x000ab503.
Lemma F_113980 : fetch_word BSEGS_I (0x113980 : word) = Some W_113980.
Proof. vm_refl. Qed.
Lemma D_113980 : decode_any W_113980 = Some (Load SZ8 true 10 21 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_113984 : bv 32 := 0x02a13423.
Lemma F_113984 : fetch_word BSEGS_I (0x113984 : word) = Some W_113984.
Proof. vm_refl. Qed.
Lemma D_113984 : decode_any W_113984 = Some (Store SZ8 2 10 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_113988 : bv 32 := 0x0284b503.
Lemma F_113988 : fetch_word BSEGS_I (0x113988 : word) = Some W_113988.
Proof. vm_refl. Qed.
Lemma D_113988 : decode_any W_113988 = Some (Load SZ8 true 10 9 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_11398c : bv 32 := 0x0384b603.
Lemma F_11398c : fetch_word BSEGS_I (0x11398c : word) = Some W_11398c.
Proof. vm_refl. Qed.
Lemma D_11398c : decode_any W_11398c = Some (Load SZ8 true 12 9 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_113990 : bv 32 := 0x40c50b33.
Lemma F_113990 : fetch_word BSEGS_I (0x113990 : word) = Some W_113990.
Proof. vm_refl. Qed.
Lemma D_113990 : decode_any W_113990 = Some (Op ALU_SUB 22 10 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_113994 : bv 32 := 0x00c546b3.
Lemma F_113994 : fetch_word BSEGS_I (0x113994 : word) = Some W_113994.
Proof. vm_refl. Qed.
Lemma D_113994 : decode_any W_113994 = Some (Op ALU_XOR 13 10 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_113998 : bv 32 := 0x00c13423.
Lemma F_113998 : fetch_word BSEGS_I (0x113998 : word) = Some W_113998.
Proof. vm_refl. Qed.
Lemma D_113998 : decode_any W_113998 = Some (Store SZ8 2 12 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_11399c : bv 32 := 0x01613823.
Lemma F_11399c : fetch_word BSEGS_I (0x11399c : word) = Some W_11399c.
Proof. vm_refl. Qed.
Lemma D_11399c : decode_any W_11399c = Some (Store SZ8 2 22 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1139a0 : bv 32 := 0x00b13c23.
Lemma F_1139a0 : fetch_word BSEGS_I (0x1139a0 : word) = Some W_1139a0.
Proof. vm_refl. Qed.
Lemma D_1139a0 : decode_any W_1139a0 = Some (Store SZ8 2 11 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1139a4 : bv 32 := 0x02813023.
Lemma F_1139a4 : fetch_word BSEGS_I (0x1139a4 : word) = Some W_1139a4.
Proof. vm_refl. Qed.
Lemma D_1139a4 : decode_any W_1139a4 = Some (Store SZ8 2 8 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1139a8 : bv 32 := 0x008b0b33.
Lemma F_1139a8 : fetch_word BSEGS_I (0x1139a8 : word) = Some W_1139a8.
Proof. vm_refl. Qed.
Lemma D_1139a8 : decode_any W_1139a8 = Some (Op ALU_ADD 22 22 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1139ac : bv 32 := 0x00d03933.
Lemma F_1139ac : fetch_word BSEGS_I (0x1139ac : word) = Some W_1139ac.
Proof. vm_refl. Qed.
Lemma D_1139ac : decode_any W_1139ac = Some (Op ALU_SLTU 18 0 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1139b0 : bv 32 := 0x00c50663.
Lemma F_1139b0 : fetch_word BSEGS_I (0x1139b0 : word) = Some W_1139b0.
Proof. vm_refl. Qed.
Lemma D_1139b0 : decode_any W_1139b0 = Some (Branch BC_EQ 10 12 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1139b4 : bv 32 := 0x00810993.
Lemma F_1139b4 : fetch_word BSEGS_I (0x1139b4 : word) = Some W_1139b4.
Proof. vm_refl. Qed.
Lemma D_1139b4 : decode_any W_1139b4 = Some (OpImm ALU_ADD 19 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1139b8 : bv 32 := 0x0080006f.
Lemma F_1139b8 : fetch_word BSEGS_I (0x1139b8 : word) = Some W_1139b8.
Proof. vm_refl. Qed.
Lemma D_1139b8 : decode_any W_1139b8 = Some (Jal 0 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1139bc : bv 32 := 0x01810993.
Lemma F_1139bc : fetch_word BSEGS_I (0x1139bc : word) = Some W_1139bc.
Proof. vm_refl. Qed.
Lemma D_1139bc : decode_any W_1139bc = Some (OpImm ALU_ADD 19 2 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1139c0 : bv 32 := 0x0784a503.
Lemma F_1139c0 : fetch_word BSEGS_I (0x1139c0 : word) = Some W_1139c0.
Proof. vm_refl. Qed.
Lemma D_1139c0 : decode_any W_1139c0 = Some (Load SZ4 true 10 9 120, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1139c4 : bv 32 := 0x00190913.
Lemma F_1139c4 : fetch_word BSEGS_I (0x1139c4 : word) = Some W_1139c4.
Proof. vm_refl. Qed.
Lemma D_1139c4 : decode_any W_1139c4 = Some (OpImm ALU_ADD 18 18 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1139c8 : bv 32 := 0x04200893.
Lemma F_1139c8 : fetch_word BSEGS_I (0x1139c8 : word) = Some W_1139c8.
Proof. vm_refl. Qed.
Lemma D_1139c8 : decode_any W_1139c8 = Some (OpImm ALU_ADD 17 0 66, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1139cc : bv 32 := 0x00098593.
Lemma F_1139cc : fetch_word BSEGS_I (0x1139cc : word) = Some W_1139cc.
Proof. vm_refl. Qed.
Lemma D_1139cc : decode_any W_1139cc = Some (OpImm ALU_ADD 11 19 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1139d0 : bv 32 := 0x00090613.
Lemma F_1139d0 : fetch_word BSEGS_I (0x1139d0 : word) = Some W_1139d0.
Proof. vm_refl. Qed.
Lemma D_1139d0 : decode_any W_1139d0 = Some (OpImm ALU_ADD 12 18 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1139d4 : bv 32 := 0x00000073.
Lemma F_1139d4 : fetch_word BSEGS_I (0x1139d4 : word) = Some W_1139d4.
Proof. vm_refl. Qed.
Lemma D_1139d4 : decode_any W_1139d4 = Some (Ecall, 4%Z).
Proof. vm_refl. Qed.
Lemma E_1139d4 : is_ecall W_1139d4 = true.
Proof. reflexivity. Qed.

(* [comment removed for export] *)
Definition W_1139d8 : bv 32 := 0x971f80ef.
Lemma F_1139d8 : fetch_word BSEGS_I (0x1139d8 : word) = Some W_1139d8.
Proof. vm_refl. Qed.
Lemma D_1139d8 : decode_any W_1139d8 = Some (Jal 1 2066800, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1139dc : bv 32 := 0x09651863.
Lemma F_1139dc : fetch_word BSEGS_I (0x1139dc : word) = Some W_1139dc.
Proof. vm_refl. Qed.
Lemma D_1139dc : decode_any W_1139dc = Some (Branch BC_NE 10 22 144, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1139e0 : bv 32 := 0x0584b503.
Lemma F_1139e0 : fetch_word BSEGS_I (0x1139e0 : word) = Some W_1139e0.
Proof. vm_refl. Qed.
Lemma D_1139e0 : decode_any W_1139e0 = Some (Load SZ8 true 10 9 88, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1139e4 : bv 32 := 0x0604b583.
Lemma F_1139e4 : fetch_word BSEGS_I (0x1139e4 : word) = Some W_1139e4.
Proof. vm_refl. Qed.
Lemma D_1139e4 : decode_any W_1139e4 = Some (Load SZ8 true 11 9 96, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1139e8 : bv 32 := 0x00b505b3.
Lemma F_1139e8 : fetch_word BSEGS_I (0x1139e8 : word) = Some W_1139e8.
Proof. vm_refl. Qed.
Lemma D_1139e8 : decode_any W_1139e8 = Some (Op ALU_ADD 11 10 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1139ec : bv 32 := 0x02b4b023.
Lemma F_1139ec : fetch_word BSEGS_I (0x1139ec : word) = Some W_1139ec.
Proof. vm_refl. Qed.
Lemma D_1139ec : decode_any W_1139ec = Some (Store SZ8 9 11 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1139f0 : bv 32 := 0x02a4b423.
Lemma F_1139f0 : fetch_word BSEGS_I (0x1139f0 : word) = Some W_1139f0.
Proof. vm_refl. Qed.
Lemma D_1139f0 : decode_any W_1139f0 = Some (Store SZ8 9 10 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1139f4 : bv 32 := 0x02a4bc23.
Lemma F_1139f4 : fetch_word BSEGS_I (0x1139f4 : word) = Some W_1139f4.
Proof. vm_refl. Qed.
Lemma D_1139f4 : decode_any W_1139f4 = Some (Store SZ8 9 10 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1139f8 : bv 32 := 0x00040513.
Lemma F_1139f8 : fetch_word BSEGS_I (0x1139f8 : word) = Some W_1139f8.
Proof. vm_refl. Qed.
Lemma D_1139f8 : decode_any W_1139f8 = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1139fc : bv 32 := 0x000ab583.
Lemma F_1139fc : fetch_word BSEGS_I (0x1139fc : word) = Some W_1139fc.
Proof. vm_refl. Qed.
Lemma D_1139fc : decode_any W_1139fc = Some (Load SZ8 true 11 21 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_113a00 : bv 32 := 0x02813603.
Lemma F_113a00 : fetch_word BSEGS_I (0x113a00 : word) = Some W_113a00.
Proof. vm_refl. Qed.
Lemma D_113a00 : decode_any W_113a00 = Some (Load SZ8 true 12 2 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_113a04 : bv 32 := 0x0cc59a63.
Lemma F_113a04 : fetch_word BSEGS_I (0x113a04 : word) = Some W_113a04.
Proof. vm_refl. Qed.
Lemma D_113a04 : decode_any W_113a04 = Some (Branch BC_NE 11 12 212, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_113a08 : bv 32 := 0x06813083.
Lemma F_113a08 : fetch_word BSEGS_I (0x113a08 : word) = Some W_113a08.
Proof. vm_refl. Qed.
Lemma D_113a08 : decode_any W_113a08 = Some (Load SZ8 true 1 2 104, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_113a0c : bv 32 := 0x06013403.
Lemma F_113a0c : fetch_word BSEGS_I (0x113a0c : word) = Some W_113a0c.
Proof. vm_refl. Qed.
Lemma D_113a0c : decode_any W_113a0c = Some (Load SZ8 true 8 2 96, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_113a10 : bv 32 := 0x05813483.
Lemma F_113a10 : fetch_word BSEGS_I (0x113a10 : word) = Some W_113a10.
Proof. vm_refl. Qed.
Lemma D_113a10 : decode_any W_113a10 = Some (Load SZ8 true 9 2 88, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_113a14 : bv 32 := 0x05013903.
Lemma F_113a14 : fetch_word BSEGS_I (0x113a14 : word) = Some W_113a14.
Proof. vm_refl. Qed.
Lemma D_113a14 : decode_any W_113a14 = Some (Load SZ8 true 18 2 80, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_113a18 : bv 32 := 0x04813983.
Lemma F_113a18 : fetch_word BSEGS_I (0x113a18 : word) = Some W_113a18.
Proof. vm_refl. Qed.
Lemma D_113a18 : decode_any W_113a18 = Some (Load SZ8 true 19 2 72, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_113a1c : bv 32 := 0x04013a03.
Lemma F_113a1c : fetch_word BSEGS_I (0x113a1c : word) = Some W_113a1c.
Proof. vm_refl. Qed.
Lemma D_113a1c : decode_any W_113a1c = Some (Load SZ8 true 20 2 64, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_113a20 : bv 32 := 0x03813a83.
Lemma F_113a20 : fetch_word BSEGS_I (0x113a20 : word) = Some W_113a20.
Proof. vm_refl. Qed.
Lemma D_113a20 : decode_any W_113a20 = Some (Load SZ8 true 21 2 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_113a24 : bv 32 := 0x03013b03.
Lemma F_113a24 : fetch_word BSEGS_I (0x113a24 : word) = Some W_113a24.
Proof. vm_refl. Qed.
Lemma D_113a24 : decode_any W_113a24 = Some (Load SZ8 true 22 2 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_113a28 : bv 32 := 0x07010113.
Lemma F_113a28 : fetch_word BSEGS_I (0x113a28 : word) = Some W_113a28.
Proof. vm_refl. Qed.
Lemma D_113a28 : decode_any W_113a28 = Some (OpImm ALU_ADD 2 2 112, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_113a2c : bv 32 := 0x00008067.
Lemma F_113a2c : fetch_word BSEGS_I (0x113a2c : word) = Some W_113a2c.
Proof. vm_refl. Qed.
Lemma D_113a2c : decode_any W_113a2c = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_113a30 : bv 32 := 0x00800713.
Lemma F_113a30 : fetch_word BSEGS_I (0x113a30 : word) = Some W_113a30.
Proof. vm_refl. Qed.
Lemma D_113a30 : decode_any W_113a30 = Some (OpImm ALU_ADD 14 0 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_113a34 : bv 32 := 0x000a0593.
Lemma F_113a34 : fetch_word BSEGS_I (0x113a34 : word) = Some W_113a34.
Proof. vm_refl. Qed.
Lemma D_113a34 : decode_any W_113a34 = Some (OpImm ALU_ADD 11 20 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_113a38 : bv 32 := 0x00e98733.
Lemma F_113a38 : fetch_word BSEGS_I (0x113a38 : word) = Some W_113a38.
Proof. vm_refl. Qed.
Lemma D_113a38 : decode_any W_113a38 = Some (Op ALU_ADD 14 19 14, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_113a3c : bv 32 := 0x00073783.
Lemma F_113a3c : fetch_word BSEGS_I (0x113a3c : word) = Some W_113a3c.
Proof. vm_refl. Qed.
Lemma D_113a3c : decode_any W_113a3c = Some (Load SZ8 true 15 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_113a40 : bv 32 := 0x40ab0b33.
Lemma F_113a40 : fetch_word BSEGS_I (0x113a40 : word) = Some W_113a40.
Proof. vm_refl. Qed.
Lemma D_113a40 : decode_any W_113a40 = Some (Op ALU_SUB 22 22 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_113a44 : bv 32 := 0x0784a503.
Lemma F_113a44 : fetch_word BSEGS_I (0x113a44 : word) = Some W_113a44.
Proof. vm_refl. Qed.
Lemma D_113a44 : decode_any W_113a44 = Some (Load SZ4 true 10 9 120, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_113a48 : bv 32 := 0x40c9093b.
Lemma F_113a48 : fetch_word BSEGS_I (0x113a48 : word) = Some W_113a48.
Proof. vm_refl. Qed.
Lemma D_113a48 : decode_any W_113a48 = Some (Op32 ALU_SUB 18 18 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_113a4c : bv 32 := 0x40d787b3.
Lemma F_113a4c : fetch_word BSEGS_I (0x113a4c : word) = Some W_113a4c.
Proof. vm_refl. Qed.
Lemma D_113a4c : decode_any W_113a4c = Some (Op ALU_SUB 15 15 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_113a50 : bv 32 := 0x00f73023.
Lemma F_113a50 : fetch_word BSEGS_I (0x113a50 : word) = Some W_113a50.
Proof. vm_refl. Qed.
Lemma D_113a50 : decode_any W_113a50 = Some (Store SZ8 14 15 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_113a54 : bv 32 := 0x04200893.
Lemma F_113a54 : fetch_word BSEGS_I (0x113a54 : word) = Some W_113a54.
Proof. vm_refl. Qed.
Lemma D_113a54 : decode_any W_113a54 = Some (OpImm ALU_ADD 17 0 66, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_113a58 : bv 32 := 0x00090613.
Lemma F_113a58 : fetch_word BSEGS_I (0x113a58 : word) = Some W_113a58.
Proof. vm_refl. Qed.
Lemma D_113a58 : decode_any W_113a58 = Some (OpImm ALU_ADD 12 18 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_113a5c : bv 32 := 0x00000073.
Lemma F_113a5c : fetch_word BSEGS_I (0x113a5c : word) = Some W_113a5c.
Proof. vm_refl. Qed.
Lemma D_113a5c : decode_any W_113a5c = Some (Ecall, 4%Z).
Proof. vm_refl. Qed.
Lemma E_113a5c : is_ecall W_113a5c = true.
Proof. reflexivity. Qed.

(* [comment removed for export] *)
Definition W_113a60 : bv 32 := 0x8e9f80ef.
Lemma F_113a60 : fetch_word BSEGS_I (0x113a60 : word) = Some W_113a60.
Proof. vm_refl. Qed.
Lemma D_113a60 : decode_any W_113a60 = Some (Jal 1 2066664, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_113a64 : bv 32 := 0x000a0993.
Lemma F_113a64 : fetch_word BSEGS_I (0x113a64 : word) = Some W_113a64.
Proof. vm_refl. Qed.
Lemma D_113a64 : decode_any W_113a64 = Some (OpImm ALU_ADD 19 20 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_113a68 : bv 32 := 0xf7650ce3.
Lemma F_113a68 : fetch_word BSEGS_I (0x113a68 : word) = Some W_113a68.
Proof. vm_refl. Qed.
Lemma D_113a68 : decode_any W_113a68 = Some (Branch BC_EQ 10 22 8056, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_113a6c : bv 32 := 0x02054c63.
Lemma F_113a6c : fetch_word BSEGS_I (0x113a6c : word) = Some W_113a6c.
Proof. vm_refl. Qed.
Lemma D_113a6c : decode_any W_113a6c = Some (Branch BC_LT 10 0 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_113a70 : bv 32 := 0x0089b583.
Lemma F_113a70 : fetch_word BSEGS_I (0x113a70 : word) = Some W_113a70.
Proof. vm_refl. Qed.
Lemma D_113a70 : decode_any W_113a70 = Some (Load SZ8 true 11 19 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_113a74 : bv 32 := 0x00a5b633.
Lemma F_113a74 : fetch_word BSEGS_I (0x113a74 : word) = Some W_113a74.
Proof. vm_refl. Qed.
Lemma D_113a74 : decode_any W_113a74 = Some (Op ALU_SLTU 12 11 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_113a78 : bv 32 := 0x00461a13.
Lemma F_113a78 : fetch_word BSEGS_I (0x113a78 : word) = Some W_113a78.
Proof. vm_refl. Qed.
Lemma D_113a78 : decode_any W_113a78 = Some (ShiftImm ALU_SLL 20 12 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_113a7c : bv 32 := 0x01498a33.
Lemma F_113a7c : fetch_word BSEGS_I (0x113a7c : word) = Some W_113a7c.
Proof. vm_refl. Qed.
Lemma D_113a7c : decode_any W_113a7c = Some (Op ALU_ADD 20 19 20, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_113a80 : bv 32 := 0x000a3703.
Lemma F_113a80 : fetch_word BSEGS_I (0x113a80 : word) = Some W_113a80.
Proof. vm_refl. Qed.
Lemma D_113a80 : decode_any W_113a80 = Some (Load SZ8 true 14 20 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_113a84 : bv 32 := 0x40c006b3.
Lemma F_113a84 : fetch_word BSEGS_I (0x113a84 : word) = Some W_113a84.
Proof. vm_refl. Qed.
Lemma D_113a84 : decode_any W_113a84 = Some (Op ALU_SUB 13 0 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_113a88 : bv 32 := 0x00b6f6b3.
Lemma F_113a88 : fetch_word BSEGS_I (0x113a88 : word) = Some W_113a88.
Proof. vm_refl. Qed.
Lemma D_113a88 : decode_any W_113a88 = Some (Op ALU_AND 13 13 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_113a8c : bv 32 := 0x40d506b3.
Lemma F_113a8c : fetch_word BSEGS_I (0x113a8c : word) = Some W_113a8c.
Proof. vm_refl. Qed.
Lemma D_113a8c : decode_any W_113a8c = Some (Op ALU_SUB 13 10 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_113a90 : bv 32 := 0x00d70733.
Lemma F_113a90 : fetch_word BSEGS_I (0x113a90 : word) = Some W_113a90.
Proof. vm_refl. Qed.
Lemma D_113a90 : decode_any W_113a90 = Some (Op ALU_ADD 14 14 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_113a94 : bv 32 := 0x00ea3023.
Lemma F_113a94 : fetch_word BSEGS_I (0x113a94 : word) = Some W_113a94.
Proof. vm_refl. Qed.
Lemma D_113a94 : decode_any W_113a94 = Some (Store SZ8 20 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_113a98 : bv 32 := 0xf8a5fce3.
Lemma F_113a98 : fetch_word BSEGS_I (0x113a98 : word) = Some W_113a98.
Proof. vm_refl. Qed.
Lemma D_113a98 : decode_any W_113a98 = Some (Branch BC_GEU 11 10 8088, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_113a9c : bv 32 := 0x01800713.
Lemma F_113a9c : fetch_word BSEGS_I (0x113a9c : word) = Some W_113a9c.
Proof. vm_refl. Qed.
Lemma D_113a9c : decode_any W_113a9c = Some (OpImm ALU_ADD 14 0 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_113aa0 : bv 32 := 0xf95ff06f.
Lemma F_113aa0 : fetch_word BSEGS_I (0x113aa0 : word) = Some W_113aa0.
Proof. vm_refl. Qed.
Lemma D_113aa0 : decode_any W_113aa0 = Some (Jal 0 2097044, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_113aa4 : bv 32 := 0x00000513.
Lemma F_113aa4 : fetch_word BSEGS_I (0x113aa4 : word) = Some W_113aa4.
Proof. vm_refl. Qed.
Lemma D_113aa4 : decode_any W_113aa4 = Some (OpImm ALU_ADD 10 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_113aa8 : bv 32 := 0x0004a583.
Lemma F_113aa8 : fetch_word BSEGS_I (0x113aa8 : word) = Some W_113aa8.
Proof. vm_refl. Qed.
Lemma D_113aa8 : decode_any W_113aa8 = Some (Load SZ4 true 11 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_113aac : bv 32 := 0x0009091b.
Lemma F_113aac : fetch_word BSEGS_I (0x113aac : word) = Some W_113aac.
Proof. vm_refl. Qed.
Lemma D_113aac : decode_any W_113aac = Some (OpImm32 18 18 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_113ab0 : bv 32 := 0x00200613.
Lemma F_113ab0 : fetch_word BSEGS_I (0x113ab0 : word) = Some W_113ab0.
Proof. vm_refl. Qed.
Lemma D_113ab0 : decode_any W_113ab0 = Some (OpImm ALU_ADD 12 0 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_113ab4 : bv 32 := 0x0205e593.
Lemma F_113ab4 : fetch_word BSEGS_I (0x113ab4 : word) = Some W_113ab4.
Proof. vm_refl. Qed.
Lemma D_113ab4 : decode_any W_113ab4 = Some (OpImm ALU_OR 11 11 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_113ab8 : bv 32 := 0x00b4a023.
Lemma F_113ab8 : fetch_word BSEGS_I (0x113ab8 : word) = Some W_113ab8.
Proof. vm_refl. Qed.
Lemma D_113ab8 : decode_any W_113ab8 = Some (Store SZ4 9 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_113abc : bv 32 := 0x0204b023.
Lemma F_113abc : fetch_word BSEGS_I (0x113abc : word) = Some W_113abc.
Proof. vm_refl. Qed.
Lemma D_113abc : decode_any W_113abc = Some (Store SZ8 9 0 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_113ac0 : bv 32 := 0x0204b423.
Lemma F_113ac0 : fetch_word BSEGS_I (0x113ac0 : word) = Some W_113ac0.
Proof. vm_refl. Qed.
Lemma D_113ac0 : decode_any W_113ac0 = Some (Store SZ8 9 0 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_113ac4 : bv 32 := 0x0204bc23.
Lemma F_113ac4 : fetch_word BSEGS_I (0x113ac4 : word) = Some W_113ac4.
Proof. vm_refl. Qed.
Lemma D_113ac4 : decode_any W_113ac4 = Some (Store SZ8 9 0 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_113ac8 : bv 32 := 0xf2c90ae3.
Lemma F_113ac8 : fetch_word BSEGS_I (0x113ac8 : word) = Some W_113ac8.
Proof. vm_refl. Qed.
Lemma D_113ac8 : decode_any W_113ac8 = Some (Branch BC_EQ 18 12 7988, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_113acc : bv 32 := 0x0089b503.
Lemma F_113acc : fetch_word BSEGS_I (0x113acc : word) = Some W_113acc.
Proof. vm_refl. Qed.
Lemma D_113acc : decode_any W_113acc = Some (Load SZ8 true 10 19 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_113ad0 : bv 32 := 0x40a40533.
Lemma F_113ad0 : fetch_word BSEGS_I (0x113ad0 : word) = Some W_113ad0.
Proof. vm_refl. Qed.
Lemma D_113ad0 : decode_any W_113ad0 = Some (Op ALU_SUB 10 8 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_113ad4 : bv 32 := 0xf29ff06f.
Lemma F_113ad4 : fetch_word BSEGS_I (0x113ad4 : word) = Some W_113ad4.
Proof. vm_refl. Qed.
Lemma D_113ad4 : decode_any W_113ad4 = Some (Jal 0 2096936, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_113ad8 : bv 32 := 0x93cf80ef.
Lemma F_113ad8 : fetch_word BSEGS_I (0x113ad8 : word) = Some W_113ad8.
Proof. vm_refl. Qed.
Lemma D_113ad8 : decode_any W_113ad8 = Some (Jal 1 2064700, 4%Z).
Proof. vm_refl. Qed.
