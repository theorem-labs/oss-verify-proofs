(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
(* [comment removed for export] *)

From OssFuzzTheorems.Proofs.leptonica.bilateral_fuzzer.lib.H Require GcFlushS2.   (* [comment removed for export] *)
From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OssFuzzTheorems.leptonica.bilateral_fuzzer.images Require Import Ubsan.
Open Scope bv_scope.

(* [comment removed for export] *)
Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

Definition W_1b95c : bv 32 := 0xf9010113.
Lemma F_1b95c : fetch_word Ubsan.M.loaded_segments (0x1b95c : word) = Some W_1b95c.
Proof. vm_refl. Qed.
Lemma D_1b95c : decode_any W_1b95c = Some (OpImm ALU_ADD 2 2 3984, 4%Z).
Proof. vm_refl. Qed.

Definition W_1b960 : bv 32 := 0x06113423.
Lemma F_1b960 : fetch_word Ubsan.M.loaded_segments (0x1b960 : word) = Some W_1b960.
Proof. vm_refl. Qed.
Lemma D_1b960 : decode_any W_1b960 = Some (Store SZ8 2 1 104, 4%Z).
Proof. vm_refl. Qed.

Definition W_1b964 : bv 32 := 0x06813023.
Lemma F_1b964 : fetch_word Ubsan.M.loaded_segments (0x1b964 : word) = Some W_1b964.
Proof. vm_refl. Qed.
Lemma D_1b964 : decode_any W_1b964 = Some (Store SZ8 2 8 96, 4%Z).
Proof. vm_refl. Qed.

Definition W_1b968 : bv 32 := 0x04913c23.
Lemma F_1b968 : fetch_word Ubsan.M.loaded_segments (0x1b968 : word) = Some W_1b968.
Proof. vm_refl. Qed.
Lemma D_1b968 : decode_any W_1b968 = Some (Store SZ8 2 9 88, 4%Z).
Proof. vm_refl. Qed.

Definition W_1b96c : bv 32 := 0x05213823.
Lemma F_1b96c : fetch_word Ubsan.M.loaded_segments (0x1b96c : word) = Some W_1b96c.
Proof. vm_refl. Qed.
Lemma D_1b96c : decode_any W_1b96c = Some (Store SZ8 2 18 80, 4%Z).
Proof. vm_refl. Qed.

Definition W_1b970 : bv 32 := 0x05313423.
Lemma F_1b970 : fetch_word Ubsan.M.loaded_segments (0x1b970 : word) = Some W_1b970.
Proof. vm_refl. Qed.
Lemma D_1b970 : decode_any W_1b970 = Some (Store SZ8 2 19 72, 4%Z).
Proof. vm_refl. Qed.

Definition W_1b974 : bv 32 := 0x05413023.
Lemma F_1b974 : fetch_word Ubsan.M.loaded_segments (0x1b974 : word) = Some W_1b974.
Proof. vm_refl. Qed.
Lemma D_1b974 : decode_any W_1b974 = Some (Store SZ8 2 20 64, 4%Z).
Proof. vm_refl. Qed.

Definition W_1b978 : bv 32 := 0x03513c23.
Lemma F_1b978 : fetch_word Ubsan.M.loaded_segments (0x1b978 : word) = Some W_1b978.
Proof. vm_refl. Qed.
Lemma D_1b978 : decode_any W_1b978 = Some (Store SZ8 2 21 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_1b97c : bv 32 := 0x03613823.
Lemma F_1b97c : fetch_word Ubsan.M.loaded_segments (0x1b97c : word) = Some W_1b97c.
Proof. vm_refl. Qed.
Lemma D_1b97c : decode_any W_1b97c = Some (Store SZ8 2 22 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_1b980 : bv 32 := 0x03713423.
Lemma F_1b980 : fetch_word Ubsan.M.loaded_segments (0x1b980 : word) = Some W_1b980.
Proof. vm_refl. Qed.
Lemma D_1b980 : decode_any W_1b980 = Some (Store SZ8 2 23 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_1b984 : bv 32 := 0x03813023.
Lemma F_1b984 : fetch_word Ubsan.M.loaded_segments (0x1b984 : word) = Some W_1b984.
Proof. vm_refl. Qed.
Lemma D_1b984 : decode_any W_1b984 = Some (Store SZ8 2 24 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_1b988 : bv 32 := 0x01913c23.
Lemma F_1b988 : fetch_word Ubsan.M.loaded_segments (0x1b988 : word) = Some W_1b988.
Proof. vm_refl. Qed.
Lemma D_1b988 : decode_any W_1b988 = Some (Store SZ8 2 25 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_1b98c : bv 32 := 0x04050c63.
Lemma F_1b98c : fetch_word Ubsan.M.loaded_segments (0x1b98c : word) = Some W_1b98c.
Proof. vm_refl. Qed.
Lemma D_1b98c : decode_any W_1b98c = Some (Branch BC_EQ 10 0 88, 4%Z).
Proof. vm_refl. Qed.

Definition W_1b990 : bv 32 := 0x00058913.
Lemma F_1b990 : fetch_word Ubsan.M.loaded_segments (0x1b990 : word) = Some W_1b990.
Proof. vm_refl. Qed.
Lemma D_1b990 : decode_any W_1b990 = Some (OpImm ALU_ADD 18 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_1b994 : bv 32 := 0x06058863.
Lemma F_1b994 : fetch_word Ubsan.M.loaded_segments (0x1b994 : word) = Some W_1b994.
Proof. vm_refl. Qed.
Lemma D_1b994 : decode_any W_1b994 = Some (Branch BC_EQ 11 0 112, 4%Z).
Proof. vm_refl. Qed.

Definition W_1b998 : bv 32 := 0x00060b13.
Lemma F_1b998 : fetch_word Ubsan.M.loaded_segments (0x1b998 : word) = Some W_1b998.
Proof. vm_refl. Qed.
Lemma D_1b998 : decode_any W_1b998 = Some (OpImm ALU_ADD 22 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_1b99c : bv 32 := 0x00050993.
Lemma F_1b99c : fetch_word Ubsan.M.loaded_segments (0x1b99c : word) = Some W_1b99c.
Proof. vm_refl. Qed.
Lemma D_1b99c : decode_any W_1b99c = Some (OpImm ALU_ADD 19 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_1b9a0 : bv 32 := 0xf2dfe0ef.
Lemma F_1b9a0 : fetch_word Ubsan.M.loaded_segments (0x1b9a0 : word) = Some W_1b9a0.
Proof. vm_refl. Qed.
Lemma D_1b9a0 : decode_any W_1b9a0 = Some (Jal 1 2092844, 4%Z).
Proof. vm_refl. Qed.

Definition W_1b9a4 : bv 32 := 0x02000593.
Lemma F_1b9a4 : fetch_word Ubsan.M.loaded_segments (0x1b9a4 : word) = Some W_1b9a4.
Proof. vm_refl. Qed.
Lemma D_1b9a4 : decode_any W_1b9a4 = Some (OpImm ALU_ADD 11 0 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_1b9a8 : bv 32 := 0x06b51e63.
Lemma F_1b9a8 : fetch_word Ubsan.M.loaded_segments (0x1b9a8 : word) = Some W_1b9a8.
Proof. vm_refl. Qed.
Lemma D_1b9a8 : decode_any W_1b9a8 = Some (Branch BC_NE 10 11 124, 4%Z).
Proof. vm_refl. Qed.

Definition W_1b9ac : bv 32 := 0x00090513.
Lemma F_1b9ac : fetch_word Ubsan.M.loaded_segments (0x1b9ac : word) = Some W_1b9ac.
Proof. vm_refl. Qed.
Lemma D_1b9ac : decode_any W_1b9ac = Some (OpImm ALU_ADD 10 18 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_1b9b0 : bv 32 := 0xf1dfe0ef.
Lemma F_1b9b0 : fetch_word Ubsan.M.loaded_segments (0x1b9b0 : word) = Some W_1b9b0.
Proof. vm_refl. Qed.
Lemma D_1b9b0 : decode_any W_1b9b0 = Some (Jal 1 2092828, 4%Z).
Proof. vm_refl. Qed.

Definition W_1b9b4 : bv 32 := 0x00800593.
Lemma F_1b9b4 : fetch_word Ubsan.M.loaded_segments (0x1b9b4 : word) = Some W_1b9b4.
Proof. vm_refl. Qed.
Lemma D_1b9b4 : decode_any W_1b9b4 = Some (OpImm ALU_ADD 11 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_1b9b8 : bv 32 := 0x08b51663.
Lemma F_1b9b8 : fetch_word Ubsan.M.loaded_segments (0x1b9b8 : word) = Some W_1b9b8.
Proof. vm_refl. Qed.
Lemma D_1b9b8 : decode_any W_1b9b8 = Some (Branch BC_NE 10 11 140, 4%Z).
Proof. vm_refl. Qed.

Definition W_1b9bc : bv 32 := 0x00400513.
Lemma F_1b9bc : fetch_word Ubsan.M.loaded_segments (0x1b9bc : word) = Some W_1b9bc.
Proof. vm_refl. Qed.
Lemma D_1b9bc : decode_any W_1b9bc = Some (OpImm ALU_ADD 10 0 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_1b9c0 : bv 32 := 0x10ab6c63.
Lemma F_1b9c0 : fetch_word Ubsan.M.loaded_segments (0x1b9c0 : word) = Some W_1b9c0.
Proof. vm_refl. Qed.
Lemma D_1b9c0 : decode_any W_1b9c0 = Some (Branch BC_LTU 22 10 280, 4%Z).
Proof. vm_refl. Qed.

Definition W_1b9c4 : bv 32 := 0x00029517.
Lemma F_1b9c4 : fetch_word Ubsan.M.loaded_segments (0x1b9c4 : word) = Some W_1b9c4.
Proof. vm_refl. Qed.
Lemma D_1b9c4 : decode_any W_1b9c4 = Some (Auipc 10 41, 4%Z).
Proof. vm_refl. Qed.

Definition W_1b9c8 : bv 32 := 0x4d453503.
Lemma F_1b9c8 : fetch_word Ubsan.M.loaded_segments (0x1b9c8 : word) = Some W_1b9c8.
Proof. vm_refl. Qed.
Lemma D_1b9c8 : decode_any W_1b9c8 = Some (Load SZ8 true 10 10 1236, 4%Z).
Proof. vm_refl. Qed.

Definition W_1b9cc : bv 32 := 0x00052503.
Lemma F_1b9cc : fetch_word Ubsan.M.loaded_segments (0x1b9cc : word) = Some W_1b9cc.
Proof. vm_refl. Qed.
Lemma D_1b9cc : decode_any W_1b9cc = Some (Load SZ4 true 10 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_1b9d0 : bv 32 := 0x00600593.
Lemma F_1b9d0 : fetch_word Ubsan.M.loaded_segments (0x1b9d0 : word) = Some W_1b9d0.
Proof. vm_refl. Qed.
Lemma D_1b9d0 : decode_any W_1b9d0 = Some (OpImm ALU_ADD 11 0 6, 4%Z).
Proof. vm_refl. Qed.

Definition W_1b9d4 : bv 32 := 0x0cb55663.
Lemma F_1b9d4 : fetch_word Ubsan.M.loaded_segments (0x1b9d4 : word) = Some W_1b9d4.
Proof. vm_refl. Qed.
Lemma D_1b9d4 : decode_any W_1b9d4 = Some (Branch BC_GE 10 11 204, 4%Z).
Proof. vm_refl. Qed.

Definition W_1b9d8 : bv 32 := 0xffff5517.
Lemma F_1b9d8 : fetch_word Ubsan.M.loaded_segments (0x1b9d8 : word) = Some W_1b9d8.
Proof. vm_refl. Qed.
Lemma D_1b9d8 : decode_any W_1b9d8 = Some (Auipc 10 1048565, 4%Z).
Proof. vm_refl. Qed.

Definition W_1b9dc : bv 32 := 0x09e50513.
Lemma F_1b9dc : fetch_word Ubsan.M.loaded_segments (0x1b9dc : word) = Some W_1b9dc.
Proof. vm_refl. Qed.
Lemma D_1b9dc : decode_any W_1b9dc = Some (OpImm ALU_ADD 10 10 158, 4%Z).
Proof. vm_refl. Qed.

Definition W_1b9e0 : bv 32 := 0x0800006f.
Lemma F_1b9e0 : fetch_word Ubsan.M.loaded_segments (0x1b9e0 : word) = Some W_1b9e0.
Proof. vm_refl. Qed.
Lemma D_1b9e0 : decode_any W_1b9e0 = Some (Jal 0 128, 4%Z).
Proof. vm_refl. Qed.

Definition W_1b9e4 : bv 32 := 0x00029517.
Lemma F_1b9e4 : fetch_word Ubsan.M.loaded_segments (0x1b9e4 : word) = Some W_1b9e4.
Proof. vm_refl. Qed.
Lemma D_1b9e4 : decode_any W_1b9e4 = Some (Auipc 10 41, 4%Z).
Proof. vm_refl. Qed.

Definition W_1b9e8 : bv 32 := 0x4b453503.
Lemma F_1b9e8 : fetch_word Ubsan.M.loaded_segments (0x1b9e8 : word) = Some W_1b9e8.
Proof. vm_refl. Qed.
Lemma D_1b9e8 : decode_any W_1b9e8 = Some (Load SZ8 true 10 10 1204, 4%Z).
Proof. vm_refl. Qed.

Definition W_1b9ec : bv 32 := 0x00052503.
Lemma F_1b9ec : fetch_word Ubsan.M.loaded_segments (0x1b9ec : word) = Some W_1b9ec.
Proof. vm_refl. Qed.
Lemma D_1b9ec : decode_any W_1b9ec = Some (Load SZ4 true 10 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_1b9f0 : bv 32 := 0x00600593.
Lemma F_1b9f0 : fetch_word Ubsan.M.loaded_segments (0x1b9f0 : word) = Some W_1b9f0.
Proof. vm_refl. Qed.
Lemma D_1b9f0 : decode_any W_1b9f0 = Some (OpImm ALU_ADD 11 0 6, 4%Z).
Proof. vm_refl. Qed.

Definition W_1b9f4 : bv 32 := 0x0ab55663.
Lemma F_1b9f4 : fetch_word Ubsan.M.loaded_segments (0x1b9f4 : word) = Some W_1b9f4.
Proof. vm_refl. Qed.
Lemma D_1b9f4 : decode_any W_1b9f4 = Some (Branch BC_GE 10 11 172, 4%Z).
Proof. vm_refl. Qed.

Definition W_1b9f8 : bv 32 := 0xffff6517.
Lemma F_1b9f8 : fetch_word Ubsan.M.loaded_segments (0x1b9f8 : word) = Some W_1b9f8.
Proof. vm_refl. Qed.
Lemma D_1b9f8 : decode_any W_1b9f8 = Some (Auipc 10 1048566, 4%Z).
Proof. vm_refl. Qed.

Definition W_1b9fc : bv 32 := 0xf3850513.
Lemma F_1b9fc : fetch_word Ubsan.M.loaded_segments (0x1b9fc : word) = Some W_1b9fc.
Proof. vm_refl. Qed.
Lemma D_1b9fc : decode_any W_1b9fc = Some (OpImm ALU_ADD 10 10 3896, 4%Z).
Proof. vm_refl. Qed.

Definition W_1ba00 : bv 32 := 0x0600006f.
Lemma F_1ba00 : fetch_word Ubsan.M.loaded_segments (0x1ba00 : word) = Some W_1ba00.
Proof. vm_refl. Qed.
Lemma D_1ba00 : decode_any W_1ba00 = Some (Jal 0 96, 4%Z).
Proof. vm_refl. Qed.

Definition W_1ba04 : bv 32 := 0x00029517.
Lemma F_1ba04 : fetch_word Ubsan.M.loaded_segments (0x1ba04 : word) = Some W_1ba04.
Proof. vm_refl. Qed.
Lemma D_1ba04 : decode_any W_1ba04 = Some (Auipc 10 41, 4%Z).
Proof. vm_refl. Qed.

Definition W_1ba08 : bv 32 := 0x49453503.
Lemma F_1ba08 : fetch_word Ubsan.M.loaded_segments (0x1ba08 : word) = Some W_1ba08.
Proof. vm_refl. Qed.
Lemma D_1ba08 : decode_any W_1ba08 = Some (Load SZ8 true 10 10 1172, 4%Z).
Proof. vm_refl. Qed.

Definition W_1ba0c : bv 32 := 0x00052503.
Lemma F_1ba0c : fetch_word Ubsan.M.loaded_segments (0x1ba0c : word) = Some W_1ba0c.
Proof. vm_refl. Qed.
Lemma D_1ba0c : decode_any W_1ba0c = Some (Load SZ4 true 10 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_1ba10 : bv 32 := 0x00600593.
Lemma F_1ba10 : fetch_word Ubsan.M.loaded_segments (0x1ba10 : word) = Some W_1ba10.
Proof. vm_refl. Qed.
Lemma D_1ba10 : decode_any W_1ba10 = Some (OpImm ALU_ADD 11 0 6, 4%Z).
Proof. vm_refl. Qed.

Definition W_1ba14 : bv 32 := 0x08b55663.
Lemma F_1ba14 : fetch_word Ubsan.M.loaded_segments (0x1ba14 : word) = Some W_1ba14.
Proof. vm_refl. Qed.
Lemma D_1ba14 : decode_any W_1ba14 = Some (Branch BC_GE 10 11 140, 4%Z).
Proof. vm_refl. Qed.

Definition W_1ba18 : bv 32 := 0xffff5517.
Lemma F_1ba18 : fetch_word Ubsan.M.loaded_segments (0x1ba18 : word) = Some W_1ba18.
Proof. vm_refl. Qed.
Lemma D_1ba18 : decode_any W_1ba18 = Some (Auipc 10 1048565, 4%Z).
Proof. vm_refl. Qed.

Definition W_1ba1c : bv 32 := 0x89c50513.
Lemma F_1ba1c : fetch_word Ubsan.M.loaded_segments (0x1ba1c : word) = Some W_1ba1c.
Proof. vm_refl. Qed.
Lemma D_1ba1c : decode_any W_1ba1c = Some (OpImm ALU_ADD 10 10 2204, 4%Z).
Proof. vm_refl. Qed.

Definition W_1ba20 : bv 32 := 0x0400006f.
Lemma F_1ba20 : fetch_word Ubsan.M.loaded_segments (0x1ba20 : word) = Some W_1ba20.
Proof. vm_refl. Qed.
Lemma D_1ba20 : decode_any W_1ba20 = Some (Jal 0 64, 4%Z).
Proof. vm_refl. Qed.

Definition W_1ba24 : bv 32 := 0x00029517.
Lemma F_1ba24 : fetch_word Ubsan.M.loaded_segments (0x1ba24 : word) = Some W_1ba24.
Proof. vm_refl. Qed.
Lemma D_1ba24 : decode_any W_1ba24 = Some (Auipc 10 41, 4%Z).
Proof. vm_refl. Qed.

Definition W_1ba28 : bv 32 := 0x47453503.
Lemma F_1ba28 : fetch_word Ubsan.M.loaded_segments (0x1ba28 : word) = Some W_1ba28.
Proof. vm_refl. Qed.
Lemma D_1ba28 : decode_any W_1ba28 = Some (Load SZ8 true 10 10 1140, 4%Z).
Proof. vm_refl. Qed.

Definition W_1ba2c : bv 32 := 0x00052503.
Lemma F_1ba2c : fetch_word Ubsan.M.loaded_segments (0x1ba2c : word) = Some W_1ba2c.
Proof. vm_refl. Qed.
Lemma D_1ba2c : decode_any W_1ba2c = Some (Load SZ4 true 10 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_1ba30 : bv 32 := 0x00600593.
Lemma F_1ba30 : fetch_word Ubsan.M.loaded_segments (0x1ba30 : word) = Some W_1ba30.
Proof. vm_refl. Qed.
Lemma D_1ba30 : decode_any W_1ba30 = Some (OpImm ALU_ADD 11 0 6, 4%Z).
Proof. vm_refl. Qed.

Definition W_1ba34 : bv 32 := 0x06b55663.
Lemma F_1ba34 : fetch_word Ubsan.M.loaded_segments (0x1ba34 : word) = Some W_1ba34.
Proof. vm_refl. Qed.
Lemma D_1ba34 : decode_any W_1ba34 = Some (Branch BC_GE 10 11 108, 4%Z).
Proof. vm_refl. Qed.

Definition W_1ba38 : bv 32 := 0xffff5517.
Lemma F_1ba38 : fetch_word Ubsan.M.loaded_segments (0x1ba38 : word) = Some W_1ba38.
Proof. vm_refl. Qed.
Lemma D_1ba38 : decode_any W_1ba38 = Some (Auipc 10 1048565, 4%Z).
Proof. vm_refl. Qed.

Definition W_1ba3c : bv 32 := 0x8b750513.
Lemma F_1ba3c : fetch_word Ubsan.M.loaded_segments (0x1ba3c : word) = Some W_1ba3c.
Proof. vm_refl. Qed.
Lemma D_1ba3c : decode_any W_1ba3c = Some (OpImm ALU_ADD 10 10 2231, 4%Z).
Proof. vm_refl. Qed.

Definition W_1ba40 : bv 32 := 0x0200006f.
Lemma F_1ba40 : fetch_word Ubsan.M.loaded_segments (0x1ba40 : word) = Some W_1ba40.
Proof. vm_refl. Qed.
Lemma D_1ba40 : decode_any W_1ba40 = Some (Jal 0 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_1ba44 : bv 32 := 0x00029517.
Lemma F_1ba44 : fetch_word Ubsan.M.loaded_segments (0x1ba44 : word) = Some W_1ba44.
Proof. vm_refl. Qed.
Lemma D_1ba44 : decode_any W_1ba44 = Some (Auipc 10 41, 4%Z).
Proof. vm_refl. Qed.

Definition W_1ba48 : bv 32 := 0x45453503.
Lemma F_1ba48 : fetch_word Ubsan.M.loaded_segments (0x1ba48 : word) = Some W_1ba48.
Proof. vm_refl. Qed.
Lemma D_1ba48 : decode_any W_1ba48 = Some (Load SZ8 true 10 10 1108, 4%Z).
Proof. vm_refl. Qed.

Definition W_1ba4c : bv 32 := 0x00052503.
Lemma F_1ba4c : fetch_word Ubsan.M.loaded_segments (0x1ba4c : word) = Some W_1ba4c.
Proof. vm_refl. Qed.
Lemma D_1ba4c : decode_any W_1ba4c = Some (Load SZ4 true 10 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_1ba50 : bv 32 := 0x00600593.
Lemma F_1ba50 : fetch_word Ubsan.M.loaded_segments (0x1ba50 : word) = Some W_1ba50.
Proof. vm_refl. Qed.
Lemma D_1ba50 : decode_any W_1ba50 = Some (OpImm ALU_ADD 11 0 6, 4%Z).
Proof. vm_refl. Qed.

Definition W_1ba54 : bv 32 := 0x04b55663.
Lemma F_1ba54 : fetch_word Ubsan.M.loaded_segments (0x1ba54 : word) = Some W_1ba54.
Proof. vm_refl. Qed.
Lemma D_1ba54 : decode_any W_1ba54 = Some (Branch BC_GE 10 11 76, 4%Z).
Proof. vm_refl. Qed.

Definition W_1ba58 : bv 32 := 0xffff6517.
Lemma F_1ba58 : fetch_word Ubsan.M.loaded_segments (0x1ba58 : word) = Some W_1ba58.
Proof. vm_refl. Qed.
Lemma D_1ba58 : decode_any W_1ba58 = Some (Auipc 10 1048566, 4%Z).
Proof. vm_refl. Qed.

Definition W_1ba5c : bv 32 := 0xbf850513.
Lemma F_1ba5c : fetch_word Ubsan.M.loaded_segments (0x1ba5c : word) = Some W_1ba5c.
Proof. vm_refl. Qed.
Lemma D_1ba5c : decode_any W_1ba5c = Some (OpImm ALU_ADD 10 10 3064, 4%Z).
Proof. vm_refl. Qed.

Definition W_1ba60 : bv 32 := 0xffff5597.
Lemma F_1ba60 : fetch_word Ubsan.M.loaded_segments (0x1ba60 : word) = Some W_1ba60.
Proof. vm_refl. Qed.
Lemma D_1ba60 : decode_any W_1ba60 = Some (Auipc 11 1048565, 4%Z).
Proof. vm_refl. Qed.

Definition W_1ba64 : bv 32 := 0xae758593.
Lemma F_1ba64 : fetch_word Ubsan.M.loaded_segments (0x1ba64 : word) = Some W_1ba64.
Proof. vm_refl. Qed.
Lemma D_1ba64 : decode_any W_1ba64 = Some (OpImm ALU_ADD 11 11 2791, 4%Z).
Proof. vm_refl. Qed.

Definition W_1ba68 : bv 32 := 0x00100613.
Lemma F_1ba68 : fetch_word Ubsan.M.loaded_segments (0x1ba68 : word) = Some W_1ba68.
Proof. vm_refl. Qed.
Lemma D_1ba68 : decode_any W_1ba68 = Some (OpImm ALU_ADD 12 0 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_1ba6c : bv 32 := 0x06813083.
Lemma F_1ba6c : fetch_word Ubsan.M.loaded_segments (0x1ba6c : word) = Some W_1ba6c.
Proof. vm_refl. Qed.
Lemma D_1ba6c : decode_any W_1ba6c = Some (Load SZ8 true 1 2 104, 4%Z).
Proof. vm_refl. Qed.

Definition W_1ba70 : bv 32 := 0x06013403.
Lemma F_1ba70 : fetch_word Ubsan.M.loaded_segments (0x1ba70 : word) = Some W_1ba70.
Proof. vm_refl. Qed.
Lemma D_1ba70 : decode_any W_1ba70 = Some (Load SZ8 true 8 2 96, 4%Z).
Proof. vm_refl. Qed.

Definition W_1ba74 : bv 32 := 0x05813483.
Lemma F_1ba74 : fetch_word Ubsan.M.loaded_segments (0x1ba74 : word) = Some W_1ba74.
Proof. vm_refl. Qed.
Lemma D_1ba74 : decode_any W_1ba74 = Some (Load SZ8 true 9 2 88, 4%Z).
Proof. vm_refl. Qed.

Definition W_1ba78 : bv 32 := 0x05013903.
Lemma F_1ba78 : fetch_word Ubsan.M.loaded_segments (0x1ba78 : word) = Some W_1ba78.
Proof. vm_refl. Qed.
Lemma D_1ba78 : decode_any W_1ba78 = Some (Load SZ8 true 18 2 80, 4%Z).
Proof. vm_refl. Qed.

Definition W_1ba7c : bv 32 := 0x04813983.
Lemma F_1ba7c : fetch_word Ubsan.M.loaded_segments (0x1ba7c : word) = Some W_1ba7c.
Proof. vm_refl. Qed.
Lemma D_1ba7c : decode_any W_1ba7c = Some (Load SZ8 true 19 2 72, 4%Z).
Proof. vm_refl. Qed.

Definition W_1ba80 : bv 32 := 0x04013a03.
Lemma F_1ba80 : fetch_word Ubsan.M.loaded_segments (0x1ba80 : word) = Some W_1ba80.
Proof. vm_refl. Qed.
Lemma D_1ba80 : decode_any W_1ba80 = Some (Load SZ8 true 20 2 64, 4%Z).
Proof. vm_refl. Qed.

Definition W_1ba84 : bv 32 := 0x03813a83.
Lemma F_1ba84 : fetch_word Ubsan.M.loaded_segments (0x1ba84 : word) = Some W_1ba84.
Proof. vm_refl. Qed.
Lemma D_1ba84 : decode_any W_1ba84 = Some (Load SZ8 true 21 2 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_1ba88 : bv 32 := 0x03013b03.
Lemma F_1ba88 : fetch_word Ubsan.M.loaded_segments (0x1ba88 : word) = Some W_1ba88.
Proof. vm_refl. Qed.
Lemma D_1ba88 : decode_any W_1ba88 = Some (Load SZ8 true 22 2 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_1ba8c : bv 32 := 0x02813b83.
Lemma F_1ba8c : fetch_word Ubsan.M.loaded_segments (0x1ba8c : word) = Some W_1ba8c.
Proof. vm_refl. Qed.
Lemma D_1ba8c : decode_any W_1ba8c = Some (Load SZ8 true 23 2 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_1ba90 : bv 32 := 0x02013c03.
Lemma F_1ba90 : fetch_word Ubsan.M.loaded_segments (0x1ba90 : word) = Some W_1ba90.
Proof. vm_refl. Qed.
Lemma D_1ba90 : decode_any W_1ba90 = Some (Load SZ8 true 24 2 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_1ba94 : bv 32 := 0x01813c83.
Lemma F_1ba94 : fetch_word Ubsan.M.loaded_segments (0x1ba94 : word) = Some W_1ba94.
Proof. vm_refl. Qed.
Lemma D_1ba94 : decode_any W_1ba94 = Some (Load SZ8 true 25 2 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_1ba98 : bv 32 := 0x07010113.
Lemma F_1ba98 : fetch_word Ubsan.M.loaded_segments (0x1ba98 : word) = Some W_1ba98.
Proof. vm_refl. Qed.
Lemma D_1ba98 : decode_any W_1ba98 = Some (OpImm ALU_ADD 2 2 112, 4%Z).
Proof. vm_refl. Qed.

Definition W_1ba9c : bv 32 := 0xb58fc06f.
Lemma F_1ba9c : fetch_word Ubsan.M.loaded_segments (0x1ba9c : word) = Some W_1ba9c.
Proof. vm_refl. Qed.
Lemma D_1ba9c : decode_any W_1ba9c = Some (Jal 0 2081624, 4%Z).
Proof. vm_refl. Qed.

Definition W_1baa0 : bv 32 := 0x00100513.
Lemma F_1baa0 : fetch_word Ubsan.M.loaded_segments (0x1baa0 : word) = Some W_1baa0.
Proof. vm_refl. Qed.
Lemma D_1baa0 : decode_any W_1baa0 = Some (OpImm ALU_ADD 10 0 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_1baa4 : bv 32 := 0x06813083.
Lemma F_1baa4 : fetch_word Ubsan.M.loaded_segments (0x1baa4 : word) = Some W_1baa4.
Proof. vm_refl. Qed.
Lemma D_1baa4 : decode_any W_1baa4 = Some (Load SZ8 true 1 2 104, 4%Z).
Proof. vm_refl. Qed.

Definition W_1baa8 : bv 32 := 0x06013403.
Lemma F_1baa8 : fetch_word Ubsan.M.loaded_segments (0x1baa8 : word) = Some W_1baa8.
Proof. vm_refl. Qed.
Lemma D_1baa8 : decode_any W_1baa8 = Some (Load SZ8 true 8 2 96, 4%Z).
Proof. vm_refl. Qed.

Definition W_1baac : bv 32 := 0x05813483.
Lemma F_1baac : fetch_word Ubsan.M.loaded_segments (0x1baac : word) = Some W_1baac.
Proof. vm_refl. Qed.
Lemma D_1baac : decode_any W_1baac = Some (Load SZ8 true 9 2 88, 4%Z).
Proof. vm_refl. Qed.

Definition W_1bab0 : bv 32 := 0x05013903.
Lemma F_1bab0 : fetch_word Ubsan.M.loaded_segments (0x1bab0 : word) = Some W_1bab0.
Proof. vm_refl. Qed.
Lemma D_1bab0 : decode_any W_1bab0 = Some (Load SZ8 true 18 2 80, 4%Z).
Proof. vm_refl. Qed.

Definition W_1bab4 : bv 32 := 0x04813983.
Lemma F_1bab4 : fetch_word Ubsan.M.loaded_segments (0x1bab4 : word) = Some W_1bab4.
Proof. vm_refl. Qed.
Lemma D_1bab4 : decode_any W_1bab4 = Some (Load SZ8 true 19 2 72, 4%Z).
Proof. vm_refl. Qed.

Definition W_1bab8 : bv 32 := 0x04013a03.
Lemma F_1bab8 : fetch_word Ubsan.M.loaded_segments (0x1bab8 : word) = Some W_1bab8.
Proof. vm_refl. Qed.
Lemma D_1bab8 : decode_any W_1bab8 = Some (Load SZ8 true 20 2 64, 4%Z).
Proof. vm_refl. Qed.

Definition W_1babc : bv 32 := 0x03813a83.
Lemma F_1babc : fetch_word Ubsan.M.loaded_segments (0x1babc : word) = Some W_1babc.
Proof. vm_refl. Qed.
Lemma D_1babc : decode_any W_1babc = Some (Load SZ8 true 21 2 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_1bac0 : bv 32 := 0x03013b03.
Lemma F_1bac0 : fetch_word Ubsan.M.loaded_segments (0x1bac0 : word) = Some W_1bac0.
Proof. vm_refl. Qed.
Lemma D_1bac0 : decode_any W_1bac0 = Some (Load SZ8 true 22 2 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_1bac4 : bv 32 := 0x02813b83.
Lemma F_1bac4 : fetch_word Ubsan.M.loaded_segments (0x1bac4 : word) = Some W_1bac4.
Proof. vm_refl. Qed.
Lemma D_1bac4 : decode_any W_1bac4 = Some (Load SZ8 true 23 2 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_1bac8 : bv 32 := 0x02013c03.
Lemma F_1bac8 : fetch_word Ubsan.M.loaded_segments (0x1bac8 : word) = Some W_1bac8.
Proof. vm_refl. Qed.
Lemma D_1bac8 : decode_any W_1bac8 = Some (Load SZ8 true 24 2 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_1bacc : bv 32 := 0x01813c83.
Lemma F_1bacc : fetch_word Ubsan.M.loaded_segments (0x1bacc : word) = Some W_1bacc.
Proof. vm_refl. Qed.
Lemma D_1bacc : decode_any W_1bacc = Some (Load SZ8 true 25 2 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_1bad0 : bv 32 := 0x07010113.
Lemma F_1bad0 : fetch_word Ubsan.M.loaded_segments (0x1bad0 : word) = Some W_1bad0.
Proof. vm_refl. Qed.
Lemma D_1bad0 : decode_any W_1bad0 = Some (OpImm ALU_ADD 2 2 112, 4%Z).
Proof. vm_refl. Qed.

Definition W_1bad4 : bv 32 := 0x00008067.
Lemma F_1bad4 : fetch_word Ubsan.M.loaded_segments (0x1bad4 : word) = Some W_1bad4.
Proof. vm_refl. Qed.
Lemma D_1bad4 : decode_any W_1bad4 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_1bad8 : bv 32 := 0x01410593.
Lemma F_1bad8 : fetch_word Ubsan.M.loaded_segments (0x1bad8 : word) = Some W_1bad8.
Proof. vm_refl. Qed.
Lemma D_1bad8 : decode_any W_1bad8 = Some (OpImm ALU_ADD 11 2 20, 4%Z).
Proof. vm_refl. Qed.

Definition W_1badc : bv 32 := 0x01010613.
Lemma F_1badc : fetch_word Ubsan.M.loaded_segments (0x1badc : word) = Some W_1badc.
Proof. vm_refl. Qed.
Lemma D_1badc : decode_any W_1badc = Some (OpImm ALU_ADD 12 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_1bae0 : bv 32 := 0x00090513.
Lemma F_1bae0 : fetch_word Ubsan.M.loaded_segments (0x1bae0 : word) = Some W_1bae0.
Proof. vm_refl. Qed.
Lemma D_1bae0 : decode_any W_1bae0 = Some (OpImm ALU_ADD 10 18 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_1bae4 : bv 32 := 0x00000693.
Lemma F_1bae4 : fetch_word Ubsan.M.loaded_segments (0x1bae4 : word) = Some W_1bae4.
Proof. vm_refl. Qed.
Lemma D_1bae4 : decode_any W_1bae4 = Some (OpImm ALU_ADD 13 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_1bae8 : bv 32 := 0x850fe0ef.
Lemma F_1bae8 : fetch_word Ubsan.M.loaded_segments (0x1bae8 : word) = Some W_1bae8.
Proof. vm_refl. Qed.
Lemma D_1bae8 : decode_any W_1bae8 = Some (Jal 1 2089040, 4%Z).
Proof. vm_refl. Qed.

Definition W_1baec : bv 32 := 0x00c10593.
Lemma F_1baec : fetch_word Ubsan.M.loaded_segments (0x1baec : word) = Some W_1baec.
Proof. vm_refl. Qed.
Lemma D_1baec : decode_any W_1baec = Some (OpImm ALU_ADD 11 2 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_1baf0 : bv 32 := 0x00810613.
Lemma F_1baf0 : fetch_word Ubsan.M.loaded_segments (0x1baf0 : word) = Some W_1baf0.
Proof. vm_refl. Qed.
Lemma D_1baf0 : decode_any W_1baf0 = Some (OpImm ALU_ADD 12 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_1baf4 : bv 32 := 0x00098513.
Lemma F_1baf4 : fetch_word Ubsan.M.loaded_segments (0x1baf4 : word) = Some W_1baf4.
Proof. vm_refl. Qed.
Lemma D_1baf4 : decode_any W_1baf4 = Some (OpImm ALU_ADD 10 19 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_1baf8 : bv 32 := 0x00000693.
Lemma F_1baf8 : fetch_word Ubsan.M.loaded_segments (0x1baf8 : word) = Some W_1baf8.
Proof. vm_refl. Qed.
Lemma D_1baf8 : decode_any W_1baf8 = Some (OpImm ALU_ADD 13 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_1bafc : bv 32 := 0x83cfe0ef.
Lemma F_1bafc : fetch_word Ubsan.M.loaded_segments (0x1bafc : word) = Some W_1bafc.
Proof. vm_refl. Qed.
Lemma D_1bafc : decode_any W_1bafc = Some (Jal 1 2089020, 4%Z).
Proof. vm_refl. Qed.

Definition W_1bb00 : bv 32 := 0x01412a03.
Lemma F_1bb00 : fetch_word Ubsan.M.loaded_segments (0x1bb00 : word) = Some W_1bb00.
Proof. vm_refl. Qed.
Lemma D_1bb00 : decode_any W_1bb00 = Some (Load SZ4 true 20 2 20, 4%Z).
Proof. vm_refl. Qed.

Definition W_1bb04 : bv 32 := 0x00c12503.
Lemma F_1bb04 : fetch_word Ubsan.M.loaded_segments (0x1bb04 : word) = Some W_1bb04.
Proof. vm_refl. Qed.
Lemma D_1bb04 : decode_any W_1bb04 = Some (Load SZ4 true 10 2 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_1bb08 : bv 32 := 0x02aa1663.
Lemma F_1bb08 : fetch_word Ubsan.M.loaded_segments (0x1bb08 : word) = Some W_1bb08.
Proof. vm_refl. Qed.
Lemma D_1bb08 : decode_any W_1bb08 = Some (Branch BC_NE 20 10 44, 4%Z).
Proof. vm_refl. Qed.

Definition W_1bb0c : bv 32 := 0x01012503.
Lemma F_1bb0c : fetch_word Ubsan.M.loaded_segments (0x1bb0c : word) = Some W_1bb0c.
Proof. vm_refl. Qed.
Lemma D_1bb0c : decode_any W_1bb0c = Some (Load SZ4 true 10 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_1bb10 : bv 32 := 0x00812583.
Lemma F_1bb10 : fetch_word Ubsan.M.loaded_segments (0x1bb10 : word) = Some W_1bb10.
Proof. vm_refl. Qed.
Lemma D_1bb10 : decode_any W_1bb10 = Some (Load SZ4 true 11 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_1bb14 : bv 32 := 0x1eb50663.
Lemma F_1bb14 : fetch_word Ubsan.M.loaded_segments (0x1bb14 : word) = Some W_1bb14.
Proof. vm_refl. Qed.
Lemma D_1bb14 : decode_any W_1bb14 = Some (Branch BC_EQ 10 11 492, 4%Z).
Proof. vm_refl. Qed.

Definition W_1bb18 : bv 32 := 0x00029517.
Lemma F_1bb18 : fetch_word Ubsan.M.loaded_segments (0x1bb18 : word) = Some W_1bb18.
Proof. vm_refl. Qed.
Lemma D_1bb18 : decode_any W_1bb18 = Some (Auipc 10 41, 4%Z).
Proof. vm_refl. Qed.

Definition W_1bb1c : bv 32 := 0x38053503.
Lemma F_1bb1c : fetch_word Ubsan.M.loaded_segments (0x1bb1c : word) = Some W_1bb1c.
Proof. vm_refl. Qed.
Lemma D_1bb1c : decode_any W_1bb1c = Some (Load SZ8 true 10 10 896, 4%Z).
Proof. vm_refl. Qed.

Definition W_1bb20 : bv 32 := 0x00052583.
Lemma F_1bb20 : fetch_word Ubsan.M.loaded_segments (0x1bb20 : word) = Some W_1bb20.
Proof. vm_refl. Qed.
Lemma D_1bb20 : decode_any W_1bb20 = Some (Load SZ4 true 11 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_1bb24 : bv 32 := 0x00500613.
Lemma F_1bb24 : fetch_word Ubsan.M.loaded_segments (0x1bb24 : word) = Some W_1bb24.
Proof. vm_refl. Qed.
Lemma D_1bb24 : decode_any W_1bb24 = Some (OpImm ALU_ADD 12 0 5, 4%Z).
Proof. vm_refl. Qed.

Definition W_1bb28 : bv 32 := 0x000a0513.
Lemma F_1bb28 : fetch_word Ubsan.M.loaded_segments (0x1bb28 : word) = Some W_1bb28.
Proof. vm_refl. Qed.
Lemma D_1bb28 : decode_any W_1bb28 = Some (OpImm ALU_ADD 10 20 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_1bb2c : bv 32 := 0x00c5ce63.
Lemma F_1bb2c : fetch_word Ubsan.M.loaded_segments (0x1bb2c : word) = Some W_1bb2c.
Proof. vm_refl. Qed.
Lemma D_1bb2c : decode_any W_1bb2c = Some (Branch BC_LT 11 12 28, 4%Z).
Proof. vm_refl. Qed.

Definition W_1bb30 : bv 32 := 0x0340006f.
Lemma F_1bb30 : fetch_word Ubsan.M.loaded_segments (0x1bb30 : word) = Some W_1bb30.
Proof. vm_refl. Qed.
Lemma D_1bb30 : decode_any W_1bb30 = Some (Jal 0 52, 4%Z).
Proof. vm_refl. Qed.

Definition W_1bb34 : bv 32 := 0x00029597.
Lemma F_1bb34 : fetch_word Ubsan.M.loaded_segments (0x1bb34 : word) = Some W_1bb34.
Proof. vm_refl. Qed.
Lemma D_1bb34 : decode_any W_1bb34 = Some (Auipc 11 41, 4%Z).
Proof. vm_refl. Qed.

Definition W_1bb38 : bv 32 := 0x3645b583.
Lemma F_1bb38 : fetch_word Ubsan.M.loaded_segments (0x1bb38 : word) = Some W_1bb38.
Proof. vm_refl. Qed.
Lemma D_1bb38 : decode_any W_1bb38 = Some (Load SZ8 true 11 11 868, 4%Z).
Proof. vm_refl. Qed.

Definition W_1bb3c : bv 32 := 0x0005a583.
Lemma F_1bb3c : fetch_word Ubsan.M.loaded_segments (0x1bb3c : word) = Some W_1bb3c.
Proof. vm_refl. Qed.
Lemma D_1bb3c : decode_any W_1bb3c = Some (Load SZ4 true 11 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_1bb40 : bv 32 := 0x00400613.
Lemma F_1bb40 : fetch_word Ubsan.M.loaded_segments (0x1bb40 : word) = Some W_1bb40.
Proof. vm_refl. Qed.
Lemma D_1bb40 : decode_any W_1bb40 = Some (OpImm ALU_ADD 12 0 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_1bb44 : bv 32 := 0x02b64063.
Lemma F_1bb44 : fetch_word Ubsan.M.loaded_segments (0x1bb44 : word) = Some W_1bb44.
Proof. vm_refl. Qed.
Lemma D_1bb44 : decode_any W_1bb44 = Some (Branch BC_LT 12 11 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_1bb48 : bv 32 := 0xffff6517.
Lemma F_1bb48 : fetch_word Ubsan.M.loaded_segments (0x1bb48 : word) = Some W_1bb48.
Proof. vm_refl. Qed.
Lemma D_1bb48 : decode_any W_1bb48 = Some (Auipc 10 1048566, 4%Z).
Proof. vm_refl. Qed.

Definition W_1bb4c : bv 32 := 0xffff5597.
Lemma F_1bb4c : fetch_word Ubsan.M.loaded_segments (0x1bb4c : word) = Some W_1bb4c.
Proof. vm_refl. Qed.
Lemma D_1bb4c : decode_any W_1bb4c = Some (Auipc 11 1048565, 4%Z).
Proof. vm_refl. Qed.

Definition W_1bb50 : bv 32 := 0xec850513.
Lemma F_1bb50 : fetch_word Ubsan.M.loaded_segments (0x1bb50 : word) = Some W_1bb50.
Proof. vm_refl. Qed.
Lemma D_1bb50 : decode_any W_1bb50 = Some (OpImm ALU_ADD 10 10 3784, 4%Z).
Proof. vm_refl. Qed.

Definition W_1bb54 : bv 32 := 0x9fb58593.
Lemma F_1bb54 : fetch_word Ubsan.M.loaded_segments (0x1bb54 : word) = Some W_1bb54.
Proof. vm_refl. Qed.
Lemma D_1bb54 : decode_any W_1bb54 = Some (OpImm ALU_ADD 11 11 2555, 4%Z).
Proof. vm_refl. Qed.

Definition W_1bb58 : bv 32 := 0xad0fc0ef.
Lemma F_1bb58 : fetch_word Ubsan.M.loaded_segments (0x1bb58 : word) = Some W_1bb58.
Proof. vm_refl. Qed.
Lemma D_1bb58 : decode_any W_1bb58 = Some (Jal 1 2081488, 4%Z).
Proof. vm_refl. Qed.

Definition W_1bb5c : bv 32 := 0x01412a03.
Lemma F_1bb5c : fetch_word Ubsan.M.loaded_segments (0x1bb5c : word) = Some W_1bb5c.
Proof. vm_refl. Qed.
Lemma D_1bb5c : decode_any W_1bb5c = Some (Load SZ4 true 20 2 20, 4%Z).
Proof. vm_refl. Qed.

Definition W_1bb60 : bv 32 := 0x00c12503.
Lemma F_1bb60 : fetch_word Ubsan.M.loaded_segments (0x1bb60 : word) = Some W_1bb60.
Proof. vm_refl. Qed.
Lemma D_1bb60 : decode_any W_1bb60 = Some (Load SZ4 true 10 2 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_1bb64 : bv 32 := 0x000b0593.
Lemma F_1bb64 : fetch_word Ubsan.M.loaded_segments (0x1bb64 : word) = Some W_1bb64.
Proof. vm_refl. Qed.
Lemma D_1bb64 : decode_any W_1bb64 = Some (OpImm ALU_ADD 11 22 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_1bb68 : bv 32 := 0x00aa4463.
Lemma F_1bb68 : fetch_word Ubsan.M.loaded_segments (0x1bb68 : word) = Some W_1bb68.
Proof. vm_refl. Qed.
Lemma D_1bb68 : decode_any W_1bb68 = Some (Branch BC_LT 20 10 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_1bb6c : bv 32 := 0x00050a13.
Lemma F_1bb6c : fetch_word Ubsan.M.loaded_segments (0x1bb6c : word) = Some W_1bb6c.
Proof. vm_refl. Qed.
Lemma D_1bb6c : decode_any W_1bb6c = Some (OpImm ALU_ADD 20 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_1bb70 : bv 32 := 0x01012a83.
Lemma F_1bb70 : fetch_word Ubsan.M.loaded_segments (0x1bb70 : word) = Some W_1bb70.
Proof. vm_refl. Qed.
Lemma D_1bb70 : decode_any W_1bb70 = Some (Load SZ4 true 21 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_1bb74 : bv 32 := 0x00812503.
Lemma F_1bb74 : fetch_word Ubsan.M.loaded_segments (0x1bb74 : word) = Some W_1bb74.
Proof. vm_refl. Qed.
Lemma D_1bb74 : decode_any W_1bb74 = Some (Load SZ4 true 10 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_1bb78 : bv 32 := 0x00aac463.
Lemma F_1bb78 : fetch_word Ubsan.M.loaded_segments (0x1bb78 : word) = Some W_1bb78.
Proof. vm_refl. Qed.
Lemma D_1bb78 : decode_any W_1bb78 = Some (Branch BC_LT 21 10 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_1bb7c : bv 32 := 0x00050a93.
Lemma F_1bb7c : fetch_word Ubsan.M.loaded_segments (0x1bb7c : word) = Some W_1bb7c.
Proof. vm_refl. Qed.
Lemma D_1bb7c : decode_any W_1bb7c = Some (OpImm ALU_ADD 21 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_1bb80 : bv 32 := 0x00300513.
Lemma F_1bb80 : fetch_word Ubsan.M.loaded_segments (0x1bb80 : word) = Some W_1bb80.
Proof. vm_refl. Qed.
Lemma D_1bb80 : decode_any W_1bb80 = Some (OpImm ALU_ADD 10 0 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_1bb84 : bv 32 := 0x00a59863.
Lemma F_1bb84 : fetch_word Ubsan.M.loaded_segments (0x1bb84 : word) = Some W_1bb84.
Proof. vm_refl. Qed.
Lemma D_1bb84 : decode_any W_1bb84 = Some (Branch BC_NE 11 10 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_1bb88 : bv 32 := 0x00400593.
Lemma F_1bb88 : fetch_word Ubsan.M.loaded_segments (0x1bb88 : word) = Some W_1bb88.
Proof. vm_refl. Qed.
Lemma D_1bb88 : decode_any W_1bb88 = Some (OpImm ALU_ADD 11 0 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_1bb8c : bv 32 := 0x00098513.
Lemma F_1bb8c : fetch_word Ubsan.M.loaded_segments (0x1bb8c : word) = Some W_1bb8c.
Proof. vm_refl. Qed.
Lemma D_1bb8c : decode_any W_1bb8c = Some (OpImm ALU_ADD 10 19 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_1bb90 : bv 32 := 0xeb0fe0ef.
Lemma F_1bb90 : fetch_word Ubsan.M.loaded_segments (0x1bb90 : word) = Some W_1bb90.
Proof. vm_refl. Qed.
Lemma D_1bb90 : decode_any W_1bb90 = Some (Jal 1 2090672, 4%Z).
Proof. vm_refl. Qed.

Definition W_1bb94 : bv 32 := 0x00090513.
Lemma F_1bb94 : fetch_word Ubsan.M.loaded_segments (0x1bb94 : word) = Some W_1bb94.
Proof. vm_refl. Qed.
Lemma D_1bb94 : decode_any W_1bb94 = Some (OpImm ALU_ADD 10 18 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_1bb98 : bv 32 := 0xe0dfe0ef.
Lemma F_1bb98 : fetch_word Ubsan.M.loaded_segments (0x1bb98 : word) = Some W_1bb98.
Proof. vm_refl. Qed.
Lemma D_1bb98 : decode_any W_1bb98 = Some (Jal 1 2092556, 4%Z).
Proof. vm_refl. Qed.

Definition W_1bb9c : bv 32 := 0x00050413.
Lemma F_1bb9c : fetch_word Ubsan.M.loaded_segments (0x1bb9c : word) = Some W_1bb9c.
Proof. vm_refl. Qed.
Lemma D_1bb9c : decode_any W_1bb9c = Some (OpImm ALU_ADD 8 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_1bba0 : bv 32 := 0x00098513.
Lemma F_1bba0 : fetch_word Ubsan.M.loaded_segments (0x1bba0 : word) = Some W_1bba0.
Proof. vm_refl. Qed.
Lemma D_1bba0 : decode_any W_1bba0 = Some (OpImm ALU_ADD 10 19 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_1bba4 : bv 32 := 0xe01fe0ef.
Lemma F_1bba4 : fetch_word Ubsan.M.loaded_segments (0x1bba4 : word) = Some W_1bba4.
Proof. vm_refl. Qed.
Lemma D_1bba4 : decode_any W_1bba4 = Some (Jal 1 2092544, 4%Z).
Proof. vm_refl. Qed.

Definition W_1bba8 : bv 32 := 0x00050493.
Lemma F_1bba8 : fetch_word Ubsan.M.loaded_segments (0x1bba8 : word) = Some W_1bba8.
Proof. vm_refl. Qed.
Lemma D_1bba8 : decode_any W_1bba8 = Some (OpImm ALU_ADD 9 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_1bbac : bv 32 := 0x00090513.
Lemma F_1bbac : fetch_word Ubsan.M.loaded_segments (0x1bbac : word) = Some W_1bbac.
Proof. vm_refl. Qed.
Lemma D_1bbac : decode_any W_1bbac = Some (OpImm ALU_ADD 10 18 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_1bbb0 : bv 32 := 0xc31fd0ef.
Lemma F_1bbb0 : fetch_word Ubsan.M.loaded_segments (0x1bbb0 : word) = Some W_1bbb0.
Proof. vm_refl. Qed.
Lemma D_1bbb0 : decode_any W_1bbb0 = Some (Jal 1 2087984, 4%Z).
Proof. vm_refl. Qed.

Definition W_1bbb4 : bv 32 := 0x00050913.
Lemma F_1bbb4 : fetch_word Ubsan.M.loaded_segments (0x1bbb4 : word) = Some W_1bbb4.
Proof. vm_refl. Qed.
Lemma D_1bbb4 : decode_any W_1bbb4 = Some (OpImm ALU_ADD 18 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_1bbb8 : bv 32 := 0x00098513.
Lemma F_1bbb8 : fetch_word Ubsan.M.loaded_segments (0x1bbb8 : word) = Some W_1bbb8.
Proof. vm_refl. Qed.
Lemma D_1bbb8 : decode_any W_1bbb8 = Some (OpImm ALU_ADD 10 19 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_1bbbc : bv 32 := 0xc25fd0ef.
Lemma F_1bbbc : fetch_word Ubsan.M.loaded_segments (0x1bbbc : word) = Some W_1bbbc.
Proof. vm_refl. Qed.
Lemma D_1bbbc : decode_any W_1bbbc = Some (Jal 1 2087972, 4%Z).
Proof. vm_refl. Qed.

Definition W_1bbc0 : bv 32 := 0x13505c63.
Lemma F_1bbc0 : fetch_word Ubsan.M.loaded_segments (0x1bbc0 : word) = Some W_1bbc0.
Proof. vm_refl. Qed.
Lemma D_1bbc0 : decode_any W_1bbc0 = Some (Branch BC_GE 0 21 312, 4%Z).
Proof. vm_refl. Qed.

Definition W_1bbc4 : bv 32 := 0x00000593.
Lemma F_1bbc4 : fetch_word Ubsan.M.loaded_segments (0x1bbc4 : word) = Some W_1bbc4.
Proof. vm_refl. Qed.
Lemma D_1bbc4 : decode_any W_1bbc4 = Some (OpImm ALU_ADD 11 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_1bbc8 : bv 32 := 0x00000613.
Lemma F_1bbc8 : fetch_word Ubsan.M.loaded_segments (0x1bbc8 : word) = Some W_1bbc8.
Proof. vm_refl. Qed.
Lemma D_1bbc8 : decode_any W_1bbc8 = Some (OpImm ALU_ADD 12 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_1bbcc : bv 32 := 0x00000693.
Lemma F_1bbcc : fetch_word Ubsan.M.loaded_segments (0x1bbcc : word) = Some W_1bbcc.
Proof. vm_refl. Qed.
Lemma D_1bbcc : decode_any W_1bbcc = Some (OpImm ALU_ADD 13 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_1bbd0 : bv 32 := 0x020b1b13.
Lemma F_1bbd0 : fetch_word Ubsan.M.loaded_segments (0x1bbd0 : word) = Some W_1bbd0.
Proof. vm_refl. Qed.
Lemma D_1bbd0 : decode_any W_1bbd0 = Some (ShiftImm ALU_SLL 22 22 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_1bbd4 : bv 32 := 0x020a1893.
Lemma F_1bbd4 : fetch_word Ubsan.M.loaded_segments (0x1bbd4 : word) = Some W_1bbd4.
Proof. vm_refl. Qed.
Lemma D_1bbd4 : decode_any W_1bbd4 = Some (ShiftImm ALU_SLL 17 20 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_1bbd8 : bv 32 := 0x00803733.
Lemma F_1bbd8 : fetch_word Ubsan.M.loaded_segments (0x1bbd8 : word) = Some W_1bbd8.
Proof. vm_refl. Qed.
Lemma D_1bbd8 : decode_any W_1bbd8 = Some (Op ALU_SLTU 14 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_1bbdc : bv 32 := 0x009037b3.
Lemma F_1bbdc : fetch_word Ubsan.M.loaded_segments (0x1bbdc : word) = Some W_1bbdc.
Proof. vm_refl. Qed.
Lemma D_1bbdc : decode_any W_1bbdc = Some (Op ALU_SLTU 15 0 9, 4%Z).
Proof. vm_refl. Qed.

Definition W_1bbe0 : bv 32 := 0x020b5813.
Lemma F_1bbe0 : fetch_word Ubsan.M.loaded_segments (0x1bbe0 : word) = Some W_1bbe0.
Proof. vm_refl. Qed.
Lemma D_1bbe0 : decode_any W_1bbe0 = Some (ShiftImm ALU_SRL 16 22 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_1bbe4 : bv 32 := 0x01e8d893.
Lemma F_1bbe4 : fetch_word Ubsan.M.loaded_segments (0x1bbe4 : word) = Some W_1bbe4.
Proof. vm_refl. Qed.
Lemma D_1bbe4 : decode_any W_1bbe4 = Some (ShiftImm ALU_SRL 17 17 30, 4%Z).
Proof. vm_refl. Qed.

Definition W_1bbe8 : bv 32 := 0x010482b3.
Lemma F_1bbe8 : fetch_word Ubsan.M.loaded_segments (0x1bbe8 : word) = Some W_1bbe8.
Proof. vm_refl. Qed.
Lemma D_1bbe8 : decode_any W_1bbe8 = Some (Op ALU_ADD 5 9 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_1bbec : bv 32 := 0x00300313.
Lemma F_1bbec : fetch_word Ubsan.M.loaded_segments (0x1bbec : word) = Some W_1bbec.
Proof. vm_refl. Qed.
Lemma D_1bbec : decode_any W_1bbec = Some (OpImm ALU_ADD 6 0 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_1bbf0 : bv 32 := 0x0140006f.
Lemma F_1bbf0 : fetch_word Ubsan.M.loaded_segments (0x1bbf0 : word) = Some W_1bbf0.
Proof. vm_refl. Qed.
Lemma D_1bbf0 : decode_any W_1bbf0 = Some (Jal 0 20, 4%Z).
Proof. vm_refl. Qed.

Definition W_1bbf4 : bv 32 := 0x0016869b.
Lemma F_1bbf4 : fetch_word Ubsan.M.loaded_segments (0x1bbf4 : word) = Some W_1bbf4.
Proof. vm_refl. Qed.
Lemma D_1bbf4 : decode_any W_1bbf4 = Some (OpImm32 13 13 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_1bbf8 : bv 32 := 0x00a6063b.
Lemma F_1bbf8 : fetch_word Ubsan.M.loaded_segments (0x1bbf8 : word) = Some W_1bbf8.
Proof. vm_refl. Qed.
Lemma D_1bbf8 : decode_any W_1bbf8 = Some (Op32 ALU_ADD 12 12 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_1bbfc : bv 32 := 0x012585bb.
Lemma F_1bbfc : fetch_word Ubsan.M.loaded_segments (0x1bbfc : word) = Some W_1bbfc.
Proof. vm_refl. Qed.
Lemma D_1bbfc : decode_any W_1bbfc = Some (Op32 ALU_ADD 11 11 18, 4%Z).
Proof. vm_refl. Qed.

Definition W_1bc00 : bv 32 := 0x0f568c63.
Lemma F_1bc00 : fetch_word Ubsan.M.loaded_segments (0x1bc00 : word) = Some W_1bc00.
Proof. vm_refl. Qed.
Lemma D_1bc00 : decode_any W_1bc00 = Some (Branch BC_EQ 13 21 248, 4%Z).
Proof. vm_refl. Qed.

Definition W_1bc04 : bv 32 := 0x03268e33.
Lemma F_1bc04 : fetch_word Ubsan.M.loaded_segments (0x1bc04 : word) = Some W_1bc04.
Proof. vm_refl. Qed.
Lemma D_1bc04 : decode_any W_1bc04 = Some (Mul M_MUL 28 13 18, 4%Z).
Proof. vm_refl. Qed.

Definition W_1bc08 : bv 32 := 0x032683bb.
Lemma F_1bc08 : fetch_word Ubsan.M.loaded_segments (0x1bc08 : word) = Some W_1bc08.
Proof. vm_refl. Qed.
Lemma D_1bc08 : decode_any W_1bc08 = Some (Mul32 M_MUL 7 13 18, 4%Z).
Proof. vm_refl. Qed.

Definition W_1bc0c : bv 32 := 0x11c39263.
Lemma F_1bc0c : fetch_word Ubsan.M.loaded_segments (0x1bc0c : word) = Some W_1bc0c.
Proof. vm_refl. Qed.
Lemma D_1bc0c : decode_any W_1bc0c = Some (Branch BC_NE 7 28 260, 4%Z).
Proof. vm_refl. Qed.

Definition W_1bc10 : bv 32 := 0x000e0e1b.
Lemma F_1bc10 : fetch_word Ubsan.M.loaded_segments (0x1bc10 : word) = Some W_1bc10.
Proof. vm_refl. Qed.
Lemma D_1bc10 : decode_any W_1bc10 = Some (OpImm32 28 28 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_1bc14 : bv 32 := 0x002e1393.
Lemma F_1bc14 : fetch_word Ubsan.M.loaded_segments (0x1bc14 : word) = Some W_1bc14.
Proof. vm_refl. Qed.
Lemma D_1bc14 : decode_any W_1bc14 = Some (ShiftImm ALU_SLL 7 28 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_1bc18 : bv 32 := 0x007403b3.
Lemma F_1bc18 : fetch_word Ubsan.M.loaded_segments (0x1bc18 : word) = Some W_1bc18.
Proof. vm_refl. Qed.
Lemma D_1bc18 : decode_any W_1bc18 = Some (Op ALU_ADD 7 8 7, 4%Z).
Proof. vm_refl. Qed.

Definition W_1bc1c : bv 32 := 0x0013be93.
Lemma F_1bc1c : fetch_word Ubsan.M.loaded_segments (0x1bc1c : word) = Some W_1bc1c.
Proof. vm_refl. Qed.
Lemma D_1bc1c : decode_any W_1bc1c = Some (OpImm ALU_SLTU 29 7 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_1bc20 : bv 32 := 0x0fd70863.
Lemma F_1bc20 : fetch_word Ubsan.M.loaded_segments (0x1bc20 : word) = Some W_1bc20.
Proof. vm_refl. Qed.
Lemma D_1bc20 : decode_any W_1bc20 = Some (Branch BC_EQ 14 29 240, 4%Z).
Proof. vm_refl. Qed.

Definition W_1bc24 : bv 32 := 0x0083beb3.
Lemma F_1bc24 : fetch_word Ubsan.M.loaded_segments (0x1bc24 : word) = Some W_1bc24.
Proof. vm_refl. Qed.
Lemma D_1bc24 : decode_any W_1bc24 = Some (Op ALU_SLTU 29 7 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_1bc28 : bv 32 := 0x000e2e13.
Lemma F_1bc28 : fetch_word Ubsan.M.loaded_segments (0x1bc28 : word) = Some W_1bc28.
Proof. vm_refl. Qed.
Lemma D_1bc28 : decode_any W_1bc28 = Some (OpImm ALU_SLT 28 28 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_1bc2c : bv 32 := 0x01cece33.
Lemma F_1bc2c : fetch_word Ubsan.M.loaded_segments (0x1bc2c : word) = Some W_1bc2c.
Proof. vm_refl. Qed.
Lemma D_1bc2c : decode_any W_1bc2c = Some (Op ALU_XOR 28 29 28, 4%Z).
Proof. vm_refl. Qed.

Definition W_1bc30 : bv 32 := 0x001e4e13.
Lemma F_1bc30 : fetch_word Ubsan.M.loaded_segments (0x1bc30 : word) = Some W_1bc30.
Proof. vm_refl. Qed.
Lemma D_1bc30 : decode_any W_1bc30 = Some (OpImm ALU_XOR 28 28 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_1bc34 : bv 32 := 0x0c0e0e63.
Lemma F_1bc34 : fetch_word Ubsan.M.loaded_segments (0x1bc34 : word) = Some W_1bc34.
Proof. vm_refl. Qed.
Lemma D_1bc34 : decode_any W_1bc34 = Some (Branch BC_EQ 28 0 220, 4%Z).
Proof. vm_refl. Qed.

Definition W_1bc38 : bv 32 := 0x02a68eb3.
Lemma F_1bc38 : fetch_word Ubsan.M.loaded_segments (0x1bc38 : word) = Some W_1bc38.
Proof. vm_refl. Qed.
Lemma D_1bc38 : decode_any W_1bc38 = Some (Mul M_MUL 29 13 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_1bc3c : bv 32 := 0x02a68e3b.
Lemma F_1bc3c : fetch_word Ubsan.M.loaded_segments (0x1bc3c : word) = Some W_1bc3c.
Proof. vm_refl. Qed.
Lemma D_1bc3c : decode_any W_1bc3c = Some (Mul32 M_MUL 28 13 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_1bc40 : bv 32 := 0x0dde1863.
Lemma F_1bc40 : fetch_word Ubsan.M.loaded_segments (0x1bc40 : word) = Some W_1bc40.
Proof. vm_refl. Qed.
Lemma D_1bc40 : decode_any W_1bc40 = Some (Branch BC_NE 28 29 208, 4%Z).
Proof. vm_refl. Qed.

Definition W_1bc44 : bv 32 := 0x000e8e9b.
Lemma F_1bc44 : fetch_word Ubsan.M.loaded_segments (0x1bc44 : word) = Some W_1bc44.
Proof. vm_refl. Qed.
Lemma D_1bc44 : decode_any W_1bc44 = Some (OpImm32 29 29 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_1bc48 : bv 32 := 0x002e9e13.
Lemma F_1bc48 : fetch_word Ubsan.M.loaded_segments (0x1bc48 : word) = Some W_1bc48.
Proof. vm_refl. Qed.
Lemma D_1bc48 : decode_any W_1bc48 = Some (ShiftImm ALU_SLL 28 29 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_1bc4c : bv 32 := 0x01c48e33.
Lemma F_1bc4c : fetch_word Ubsan.M.loaded_segments (0x1bc4c : word) = Some W_1bc4c.
Proof. vm_refl. Qed.
Lemma D_1bc4c : decode_any W_1bc4c = Some (Op ALU_ADD 28 9 28, 4%Z).
Proof. vm_refl. Qed.

Definition W_1bc50 : bv 32 := 0x001e3f13.
Lemma F_1bc50 : fetch_word Ubsan.M.loaded_segments (0x1bc50 : word) = Some W_1bc50.
Proof. vm_refl. Qed.
Lemma D_1bc50 : decode_any W_1bc50 = Some (OpImm ALU_SLTU 30 28 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_1bc54 : bv 32 := 0x0be78e63.
Lemma F_1bc54 : fetch_word Ubsan.M.loaded_segments (0x1bc54 : word) = Some W_1bc54.
Proof. vm_refl. Qed.
Lemma D_1bc54 : decode_any W_1bc54 = Some (Branch BC_EQ 15 30 188, 4%Z).
Proof. vm_refl. Qed.

Definition W_1bc58 : bv 32 := 0x009e3f33.
Lemma F_1bc58 : fetch_word Ubsan.M.loaded_segments (0x1bc58 : word) = Some W_1bc58.
Proof. vm_refl. Qed.
Lemma D_1bc58 : decode_any W_1bc58 = Some (Op ALU_SLTU 30 28 9, 4%Z).
Proof. vm_refl. Qed.

Definition W_1bc5c : bv 32 := 0x000eae93.
Lemma F_1bc5c : fetch_word Ubsan.M.loaded_segments (0x1bc5c : word) = Some W_1bc5c.
Proof. vm_refl. Qed.
Lemma D_1bc5c : decode_any W_1bc5c = Some (OpImm ALU_SLT 29 29 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_1bc60 : bv 32 := 0x01df4eb3.
Lemma F_1bc60 : fetch_word Ubsan.M.loaded_segments (0x1bc60 : word) = Some W_1bc60.
Proof. vm_refl. Qed.
Lemma D_1bc60 : decode_any W_1bc60 = Some (Op ALU_XOR 29 30 29, 4%Z).
Proof. vm_refl. Qed.

Definition W_1bc64 : bv 32 := 0x001ece93.
Lemma F_1bc64 : fetch_word Ubsan.M.loaded_segments (0x1bc64 : word) = Some W_1bc64.
Proof. vm_refl. Qed.
Lemma D_1bc64 : decode_any W_1bc64 = Some (OpImm ALU_XOR 29 29 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_1bc68 : bv 32 := 0x0a0e8463.
Lemma F_1bc68 : fetch_word Ubsan.M.loaded_segments (0x1bc68 : word) = Some W_1bc68.
Proof. vm_refl. Qed.
Lemma D_1bc68 : decode_any W_1bc68 = Some (Branch BC_EQ 29 0 168, 4%Z).
Proof. vm_refl. Qed.

Definition W_1bc6c : bv 32 := 0xf94054e3.
Lemma F_1bc6c : fetch_word Ubsan.M.loaded_segments (0x1bc6c : word) = Some W_1bc6c.
Proof. vm_refl. Qed.
Lemma D_1bc6c : decode_any W_1bc6c = Some (Branch BC_GE 0 20 8072, 4%Z).
Proof. vm_refl. Qed.

Definition W_1bc70 : bv 32 := 0x00000e93.
Lemma F_1bc70 : fetch_word Ubsan.M.loaded_segments (0x1bc70 : word) = Some W_1bc70.
Proof. vm_refl. Qed.
Lemma D_1bc70 : decode_any W_1bc70 = Some (OpImm ALU_ADD 29 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_1bc74 : bv 32 := 0x00261993.
Lemma F_1bc74 : fetch_word Ubsan.M.loaded_segments (0x1bc74 : word) = Some W_1bc74.
Proof. vm_refl. Qed.
Lemma D_1bc74 : decode_any W_1bc74 = Some (ShiftImm ALU_SLL 19 12 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_1bc78 : bv 32 := 0x00259f93.
Lemma F_1bc78 : fetch_word Ubsan.M.loaded_segments (0x1bc78 : word) = Some W_1bc78.
Proof. vm_refl. Qed.
Lemma D_1bc78 : decode_any W_1bc78 = Some (ShiftImm ALU_SLL 31 11 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_1bc7c : bv 32 := 0x01348f33.
Lemma F_1bc7c : fetch_word Ubsan.M.loaded_segments (0x1bc7c : word) = Some W_1bc7c.
Proof. vm_refl. Qed.
Lemma D_1bc7c : decode_any W_1bc7c = Some (Op ALU_ADD 30 9 19, 4%Z).
Proof. vm_refl. Qed.

Definition W_1bc80 : bv 32 := 0x01f40fb3.
Lemma F_1bc80 : fetch_word Ubsan.M.loaded_segments (0x1bc80 : word) = Some W_1bc80.
Proof. vm_refl. Qed.
Lemma D_1bc80 : decode_any W_1bc80 = Some (Op ALU_ADD 31 8 31, 4%Z).
Proof. vm_refl. Qed.

Definition W_1bc84 : bv 32 := 0x013289b3.
Lemma F_1bc84 : fetch_word Ubsan.M.loaded_segments (0x1bc84 : word) = Some W_1bc84.
Proof. vm_refl. Qed.
Lemma D_1bc84 : decode_any W_1bc84 = Some (Op ALU_ADD 19 5 19, 4%Z).
Proof. vm_refl. Qed.

Definition W_1bc88 : bv 32 := 0x01e80b33.
Lemma F_1bc88 : fetch_word Ubsan.M.loaded_segments (0x1bc88 : word) = Some W_1bc88.
Proof. vm_refl. Qed.
Lemma D_1bc88 : decode_any W_1bc88 = Some (Op ALU_ADD 22 16 30, 4%Z).
Proof. vm_refl. Qed.

Definition W_1bc8c : bv 32 := 0x000f8b93.
Lemma F_1bc8c : fetch_word Ubsan.M.loaded_segments (0x1bc8c : word) = Some W_1bc8c.
Proof. vm_refl. Qed.
Lemma D_1bc8c : decode_any W_1bc8c = Some (OpImm ALU_ADD 23 31 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_1bc90 : bv 32 := 0x087be063.
Lemma F_1bc90 : fetch_word Ubsan.M.loaded_segments (0x1bc90 : word) = Some W_1bc90.
Proof. vm_refl. Qed.
Lemma D_1bc90 : decode_any W_1bc90 = Some (Branch BC_LTU 23 7 128, 4%Z).
Proof. vm_refl. Qed.

Definition W_1bc94 : bv 32 := 0x001bbc13.
Lemma F_1bc94 : fetch_word Ubsan.M.loaded_segments (0x1bc94 : word) = Some W_1bc94.
Proof. vm_refl. Qed.
Lemma D_1bc94 : decode_any W_1bc94 = Some (OpImm ALU_SLTU 24 23 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_1bc98 : bv 32 := 0x01874c33.
Lemma F_1bc98 : fetch_word Ubsan.M.loaded_segments (0x1bc98 : word) = Some W_1bc98.
Proof. vm_refl. Qed.
Lemma D_1bc98 : decode_any W_1bc98 = Some (Op ALU_XOR 24 14 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_1bc9c : bv 32 := 0x060c0a63.
Lemma F_1bc9c : fetch_word Ubsan.M.loaded_segments (0x1bc9c : word) = Some W_1bc9c.
Proof. vm_refl. Qed.
Lemma D_1bc9c : decode_any W_1bc9c = Some (Branch BC_EQ 24 0 116, 4%Z).
Proof. vm_refl. Qed.

Definition W_1bca0 : bv 32 := 0x066f8863.
Lemma F_1bca0 : fetch_word Ubsan.M.loaded_segments (0x1bca0 : word) = Some W_1bca0.
Proof. vm_refl. Qed.
Lemma D_1bca0 : decode_any W_1bca0 = Some (Branch BC_EQ 31 6 112, 4%Z).
Proof. vm_refl. Qed.

Definition W_1bca4 : bv 32 := 0x01df0cb3.
Lemma F_1bca4 : fetch_word Ubsan.M.loaded_segments (0x1bca4 : word) = Some W_1bca4.
Proof. vm_refl. Qed.
Lemma D_1bca4 : decode_any W_1bca4 = Some (Op ALU_ADD 25 30 29, 4%Z).
Proof. vm_refl. Qed.

Definition W_1bca8 : bv 32 := 0x07cce463.
Lemma F_1bca8 : fetch_word Ubsan.M.loaded_segments (0x1bca8 : word) = Some W_1bca8.
Proof. vm_refl. Qed.
Lemma D_1bca8 : decode_any W_1bca8 = Some (Branch BC_LTU 25 28 104, 4%Z).
Proof. vm_refl. Qed.

Definition W_1bcac : bv 32 := 0x001cbc13.
Lemma F_1bcac : fetch_word Ubsan.M.loaded_segments (0x1bcac : word) = Some W_1bcac.
Proof. vm_refl. Qed.
Lemma D_1bcac : decode_any W_1bcac = Some (OpImm ALU_SLTU 24 25 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_1bcb0 : bv 32 := 0x0187cc33.
Lemma F_1bcb0 : fetch_word Ubsan.M.loaded_segments (0x1bcb0 : word) = Some W_1bcb0.
Proof. vm_refl. Qed.
Lemma D_1bcb0 : decode_any W_1bcb0 = Some (Op ALU_XOR 24 15 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_1bcb4 : bv 32 := 0x040c0e63.
Lemma F_1bcb4 : fetch_word Ubsan.M.loaded_segments (0x1bcb4 : word) = Some W_1bcb4.
Proof. vm_refl. Qed.
Lemma D_1bcb4 : decode_any W_1bcb4 = Some (Branch BC_EQ 24 0 92, 4%Z).
Proof. vm_refl. Qed.

Definition W_1bcb8 : bv 32 := 0x01d98c33.
Lemma F_1bcb8 : fetch_word Ubsan.M.loaded_segments (0x1bcb8 : word) = Some W_1bcb8.
Proof. vm_refl. Qed.
Lemma D_1bcb8 : decode_any W_1bcb8 = Some (Op ALU_ADD 24 19 29, 4%Z).
Proof. vm_refl. Qed.

Definition W_1bcbc : bv 32 := 0x059c6a63.
Lemma F_1bcbc : fetch_word Ubsan.M.loaded_segments (0x1bcbc : word) = Some W_1bcbc.
Proof. vm_refl. Qed.
Lemma D_1bcbc : decode_any W_1bcbc = Some (Branch BC_LTU 24 25 84, 4%Z).
Proof. vm_refl. Qed.

Definition W_1bcc0 : bv 32 := 0x01db0cb3.
Lemma F_1bcc0 : fetch_word Ubsan.M.loaded_segments (0x1bcc0 : word) = Some W_1bcc0.
Proof. vm_refl. Qed.
Lemma D_1bcc0 : decode_any W_1bcc0 = Some (Op ALU_ADD 25 22 29, 4%Z).
Proof. vm_refl. Qed.

Definition W_1bcc4 : bv 32 := 0x001cbc93.
Lemma F_1bcc4 : fetch_word Ubsan.M.loaded_segments (0x1bcc4 : word) = Some W_1bcc4.
Proof. vm_refl. Qed.
Lemma D_1bcc4 : decode_any W_1bcc4 = Some (OpImm ALU_SLTU 25 25 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_1bcc8 : bv 32 := 0x0197ccb3.
Lemma F_1bcc8 : fetch_word Ubsan.M.loaded_segments (0x1bcc8 : word) = Some W_1bcc8.
Proof. vm_refl. Qed.
Lemma D_1bcc8 : decode_any W_1bcc8 = Some (Op ALU_XOR 25 15 25, 4%Z).
Proof. vm_refl. Qed.

Definition W_1bccc : bv 32 := 0x040c8263.
Lemma F_1bccc : fetch_word Ubsan.M.loaded_segments (0x1bccc : word) = Some W_1bccc.
Proof. vm_refl. Qed.
Lemma D_1bccc : decode_any W_1bccc = Some (Branch BC_EQ 25 0 68, 4%Z).
Proof. vm_refl. Qed.

Definition W_1bcd0 : bv 32 := 0x046c0063.
Lemma F_1bcd0 : fetch_word Ubsan.M.loaded_segments (0x1bcd0 : word) = Some W_1bcd0.
Proof. vm_refl. Qed.
Lemma D_1bcd0 : decode_any W_1bcd0 = Some (Branch BC_EQ 24 6 64, 4%Z).
Proof. vm_refl. Qed.

Definition W_1bcd4 : bv 32 := 0x003bcc93.
Lemma F_1bcd4 : fetch_word Ubsan.M.loaded_segments (0x1bcd4 : word) = Some W_1bcd4.
Proof. vm_refl. Qed.
Lemma D_1bcd4 : decode_any W_1bcd4 = Some (OpImm ALU_XOR 25 23 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_1bcd8 : bv 32 := 0x000ccc83.
Lemma F_1bcd8 : fetch_word Ubsan.M.loaded_segments (0x1bcd8 : word) = Some W_1bcd8.
Proof. vm_refl. Qed.
Lemma D_1bcd8 : decode_any W_1bcd8 = Some (Load SZ1 false 25 25 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_1bcdc : bv 32 := 0x003c4c13.
Lemma F_1bcdc : fetch_word Ubsan.M.loaded_segments (0x1bcdc : word) = Some W_1bcdc.
Proof. vm_refl. Qed.
Lemma D_1bcdc : decode_any W_1bcdc = Some (OpImm ALU_XOR 24 24 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_1bce0 : bv 32 := 0x004e8e93.
Lemma F_1bce0 : fetch_word Ubsan.M.loaded_segments (0x1bce0 : word) = Some W_1bce0.
Proof. vm_refl. Qed.
Lemma D_1bce0 : decode_any W_1bce0 = Some (OpImm ALU_ADD 29 29 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_1bce4 : bv 32 := 0x001b8b93.
Lemma F_1bce4 : fetch_word Ubsan.M.loaded_segments (0x1bce4 : word) = Some W_1bce4.
Proof. vm_refl. Qed.
Lemma D_1bce4 : decode_any W_1bce4 = Some (OpImm ALU_ADD 23 23 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_1bce8 : bv 32 := 0x019c0023.
Lemma F_1bce8 : fetch_word Ubsan.M.loaded_segments (0x1bce8 : word) = Some W_1bce8.
Proof. vm_refl. Qed.
Lemma D_1bce8 : decode_any W_1bce8 = Some (Store SZ1 24 25 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_1bcec : bv 32 := 0x001f8f93.
Lemma F_1bcec : fetch_word Ubsan.M.loaded_segments (0x1bcec : word) = Some W_1bcec.
Proof. vm_refl. Qed.
Lemma D_1bcec : decode_any W_1bcec = Some (OpImm ALU_ADD 31 31 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_1bcf0 : bv 32 := 0xfbd890e3.
Lemma F_1bcf0 : fetch_word Ubsan.M.loaded_segments (0x1bcf0 : word) = Some W_1bcf0.
Proof. vm_refl. Qed.
Lemma D_1bcf0 : decode_any W_1bcf0 = Some (Branch BC_NE 17 29 8096, 4%Z).
Proof. vm_refl. Qed.

Definition W_1bcf4 : bv 32 := 0xf01ff06f.
Lemma F_1bcf4 : fetch_word Ubsan.M.loaded_segments (0x1bcf4 : word) = Some W_1bcf4.
Proof. vm_refl. Qed.
Lemma D_1bcf4 : decode_any W_1bcf4 = Some (Jal 0 2096896, 4%Z).
Proof. vm_refl. Qed.

Definition W_1bcf8 : bv 32 := 0x00000513.
Lemma F_1bcf8 : fetch_word Ubsan.M.loaded_segments (0x1bcf8 : word) = Some W_1bcf8.
Proof. vm_refl. Qed.
Lemma D_1bcf8 : decode_any W_1bcf8 = Some (OpImm ALU_ADD 10 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_1bcfc : bv 32 := 0xda9ff06f.
Lemma F_1bcfc : fetch_word Ubsan.M.loaded_segments (0x1bcfc : word) = Some W_1bcfc.
Proof. vm_refl. Qed.
Lemma D_1bcfc : decode_any W_1bcfc = Some (Jal 0 2096552, 4%Z).
Proof. vm_refl. Qed.

Definition W_1bd00 : bv 32 := 0x000a0513.
Lemma F_1bd00 : fetch_word Ubsan.M.loaded_segments (0x1bd00 : word) = Some W_1bd00.
Proof. vm_refl. Qed.
Lemma D_1bd00 : decode_any W_1bd00 = Some (OpImm ALU_ADD 10 20 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_1bd04 : bv 32 := 0x000b0593.
Lemma F_1bd04 : fetch_word Ubsan.M.loaded_segments (0x1bd04 : word) = Some W_1bd04.
Proof. vm_refl. Qed.
Lemma D_1bd04 : decode_any W_1bd04 = Some (OpImm ALU_ADD 11 22 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_1bd08 : bv 32 := 0xe74a52e3.
Lemma F_1bd08 : fetch_word Ubsan.M.loaded_segments (0x1bd08 : word) = Some W_1bd08.
Proof. vm_refl. Qed.
Lemma D_1bd08 : decode_any W_1bd08 = Some (Branch BC_GE 20 20 7780, 4%Z).
Proof. vm_refl. Qed.

Definition W_1bd0c : bv 32 := 0xe65ff06f.
Lemma F_1bd0c : fetch_word Ubsan.M.loaded_segments (0x1bd0c : word) = Some W_1bd0c.
Proof. vm_refl. Qed.
Lemma D_1bd0c : decode_any W_1bd0c = Some (Jal 0 2096740, 4%Z).
Proof. vm_refl. Qed.

Definition W_1bd10 : bv 32 := 0xc0001073.
Lemma F_1bd10 : fetch_word Ubsan.M.loaded_segments (0x1bd10 : word) = Some W_1bd10.
Proof. vm_refl. Qed.
Lemma D_1bd10 : decode_any W_1bd10 = Some (Csr CSR_RW 0 0 3072, 4%Z).
Proof. vm_refl. Qed.
