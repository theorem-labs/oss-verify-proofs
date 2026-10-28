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

Definition W_38e54 : bv 32 := 0xfc010113.
Lemma F_38e54 : fetch_word Ubsan.M.loaded_segments (0x38e54 : word) = Some W_38e54.
Proof. vm_refl. Qed.
Lemma D_38e54 : decode_any W_38e54 = Some (OpImm ALU_ADD 2 2 4032, 4%Z).
Proof. vm_refl. Qed.

Definition W_38e58 : bv 32 := 0x02113c23.
Lemma F_38e58 : fetch_word Ubsan.M.loaded_segments (0x38e58 : word) = Some W_38e58.
Proof. vm_refl. Qed.
Lemma D_38e58 : decode_any W_38e58 = Some (Store SZ8 2 1 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_38e5c : bv 32 := 0x02813823.
Lemma F_38e5c : fetch_word Ubsan.M.loaded_segments (0x38e5c : word) = Some W_38e5c.
Proof. vm_refl. Qed.
Lemma D_38e5c : decode_any W_38e5c = Some (Store SZ8 2 8 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_38e60 : bv 32 := 0x02913423.
Lemma F_38e60 : fetch_word Ubsan.M.loaded_segments (0x38e60 : word) = Some W_38e60.
Proof. vm_refl. Qed.
Lemma D_38e60 : decode_any W_38e60 = Some (Store SZ8 2 9 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_38e64 : bv 32 := 0x03213023.
Lemma F_38e64 : fetch_word Ubsan.M.loaded_segments (0x38e64 : word) = Some W_38e64.
Proof. vm_refl. Qed.
Lemma D_38e64 : decode_any W_38e64 = Some (Store SZ8 2 18 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_38e68 : bv 32 := 0x01313c23.
Lemma F_38e68 : fetch_word Ubsan.M.loaded_segments (0x38e68 : word) = Some W_38e68.
Proof. vm_refl. Qed.
Lemma D_38e68 : decode_any W_38e68 = Some (Store SZ8 2 19 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_38e6c : bv 32 := 0x01413823.
Lemma F_38e6c : fetch_word Ubsan.M.loaded_segments (0x38e6c : word) = Some W_38e6c.
Proof. vm_refl. Qed.
Lemma D_38e6c : decode_any W_38e6c = Some (Store SZ8 2 20 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_38e70 : bv 32 := 0x01513423.
Lemma F_38e70 : fetch_word Ubsan.M.loaded_segments (0x38e70 : word) = Some W_38e70.
Proof. vm_refl. Qed.
Lemma D_38e70 : decode_any W_38e70 = Some (Store SZ8 2 21 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_38e74 : bv 32 := 0x1a050063.
Lemma F_38e74 : fetch_word Ubsan.M.loaded_segments (0x38e74 : word) = Some W_38e74.
Proof. vm_refl. Qed.
Lemma D_38e74 : decode_any W_38e74 = Some (Branch BC_EQ 10 0 416, 4%Z).
Proof. vm_refl. Qed.

Definition W_38e78 : bv 32 := 0x00050413.
Lemma F_38e78 : fetch_word Ubsan.M.loaded_segments (0x38e78 : word) = Some W_38e78.
Proof. vm_refl. Qed.
Lemma D_38e78 : decode_any W_38e78 = Some (OpImm ALU_ADD 8 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_38e7c : bv 32 := 0x00757513.
Lemma F_38e7c : fetch_word Ubsan.M.loaded_segments (0x38e7c : word) = Some W_38e7c.
Proof. vm_refl. Qed.
Lemma D_38e7c : decode_any W_38e7c = Some (OpImm ALU_AND 10 10 7, 4%Z).
Proof. vm_refl. Qed.

Definition W_38e80 : bv 32 := 0x22051463.
Lemma F_38e80 : fetch_word Ubsan.M.loaded_segments (0x38e80 : word) = Some W_38e80.
Proof. vm_refl. Qed.
Lemma D_38e80 : decode_any W_38e80 = Some (Branch BC_NE 10 0 552, 4%Z).
Proof. vm_refl. Qed.

Definition W_38e84 : bv 32 := 0x00042903.
Lemma F_38e84 : fetch_word Ubsan.M.loaded_segments (0x38e84 : word) = Some W_38e84.
Proof. vm_refl. Qed.
Lemma D_38e84 : decode_any W_38e84 = Some (Load SZ4 true 18 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_38e88 : bv 32 := 0x00446983.
Lemma F_38e88 : fetch_word Ubsan.M.loaded_segments (0x38e88 : word) = Some W_38e88.
Proof. vm_refl. Qed.
Lemma D_38e88 : decode_any W_38e88 = Some (Load SZ4 false 19 8 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_38e8c : bv 32 := 0x00842a83.
Lemma F_38e8c : fetch_word Ubsan.M.loaded_segments (0x38e8c : word) = Some W_38e8c.
Proof. vm_refl. Qed.
Lemma D_38e8c : decode_any W_38e8c = Some (Load SZ4 true 21 8 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_38e90 : bv 32 := 0x00c42a03.
Lemma F_38e90 : fetch_word Ubsan.M.loaded_segments (0x38e90 : word) = Some W_38e90.
Proof. vm_refl. Qed.
Lemma D_38e90 : decode_any W_38e90 = Some (Load SZ4 true 20 8 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_38e94 : bv 32 := 0x0009849b.
Lemma F_38e94 : fetch_word Ubsan.M.loaded_segments (0x38e94 : word) = Some W_38e94.
Proof. vm_refl. Qed.
Lemma D_38e94 : decode_any W_38e94 = Some (OpImm32 9 19 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_38e98 : bv 32 := 0x00090513.
Lemma F_38e98 : fetch_word Ubsan.M.loaded_segments (0x38e98 : word) = Some W_38e98.
Proof. vm_refl. Qed.
Lemma D_38e98 : decode_any W_38e98 = Some (OpImm ALU_ADD 10 18 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_38e9c : bv 32 := 0x00048593.
Lemma F_38e9c : fetch_word Ubsan.M.loaded_segments (0x38e9c : word) = Some W_38e9c.
Proof. vm_refl. Qed.
Lemma D_38e9c : decode_any W_38e9c = Some (OpImm ALU_ADD 11 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_38ea0 : bv 32 := 0xc30ff0ef.
Lemma F_38ea0 : fetch_word Ubsan.M.loaded_segments (0x38ea0 : word) = Some W_38ea0.
Proof. vm_refl. Qed.
Lemma D_38ea0 : decode_any W_38ea0 = Some (Jal 1 2094128, 4%Z).
Proof. vm_refl. Qed.

Definition W_38ea4 : bv 32 := 0x18050863.
Lemma F_38ea4 : fetch_word Ubsan.M.loaded_segments (0x38ea4 : word) = Some W_38ea4.
Proof. vm_refl. Qed.
Lemma D_38ea4 : decode_any W_38ea4 = Some (Branch BC_EQ 10 0 400, 4%Z).
Proof. vm_refl. Qed.

Definition W_38ea8 : bv 32 := 0xfff9059b.
Lemma F_38ea8 : fetch_word Ubsan.M.loaded_segments (0x38ea8 : word) = Some W_38ea8.
Proof. vm_refl. Qed.
Lemma D_38ea8 : decode_any W_38ea8 = Some (OpImm32 11 18 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_38eac : bv 32 := 0x1f25de63.
Lemma F_38eac : fetch_word Ubsan.M.loaded_segments (0x38eac : word) = Some W_38eac.
Proof. vm_refl. Qed.
Lemma D_38eac : decode_any W_38eac = Some (Branch BC_GE 11 18 508, 4%Z).
Proof. vm_refl. Qed.

Definition W_38eb0 : bv 32 := 0x415586b3.
Lemma F_38eb0 : fetch_word Ubsan.M.loaded_segments (0x38eb0 : word) = Some W_38eb0.
Proof. vm_refl. Qed.
Lemma D_38eb0 : decode_any W_38eb0 = Some (Op ALU_SUB 13 11 21, 4%Z).
Proof. vm_refl. Qed.

Definition W_38eb4 : bv 32 := 0x4155863b.
Lemma F_38eb4 : fetch_word Ubsan.M.loaded_segments (0x38eb4 : word) = Some W_38eb4.
Proof. vm_refl. Qed.
Lemma D_38eb4 : decode_any W_38eb4 = Some (Op32 ALU_SUB 12 11 21, 4%Z).
Proof. vm_refl. Qed.

Definition W_38eb8 : bv 32 := 0x1ed61863.
Lemma F_38eb8 : fetch_word Ubsan.M.loaded_segments (0x38eb8 : word) = Some W_38eb8.
Proof. vm_refl. Qed.
Lemma D_38eb8 : decode_any W_38eb8 = Some (Branch BC_NE 12 13 496, 4%Z).
Proof. vm_refl. Qed.

Definition W_38ebc : bv 32 := 0x00757613.
Lemma F_38ebc : fetch_word Ubsan.M.loaded_segments (0x38ebc : word) = Some W_38ebc.
Proof. vm_refl. Qed.
Lemma D_38ebc : decode_any W_38ebc = Some (OpImm ALU_AND 12 10 7, 4%Z).
Proof. vm_refl. Qed.

Definition W_38ec0 : bv 32 := 0x1e061463.
Lemma F_38ec0 : fetch_word Ubsan.M.loaded_segments (0x38ec0 : word) = Some W_38ec0.
Proof. vm_refl. Qed.
Lemma D_38ec0 : decode_any W_38ec0 = Some (Branch BC_NE 12 0 488, 4%Z).
Proof. vm_refl. Qed.

Definition W_38ec4 : bv 32 := 0xfff4861b.
Lemma F_38ec4 : fetch_word Ubsan.M.loaded_segments (0x38ec4 : word) = Some W_38ec4.
Proof. vm_refl. Qed.
Lemma D_38ec4 : decode_any W_38ec4 = Some (OpImm32 12 9 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_38ec8 : bv 32 := 0x00d52423.
Lemma F_38ec8 : fetch_word Ubsan.M.loaded_segments (0x38ec8 : word) = Some W_38ec8.
Proof. vm_refl. Qed.
Lemma D_38ec8 : decode_any W_38ec8 = Some (Store SZ4 10 13 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_38ecc : bv 32 := 0x1c965e63.
Lemma F_38ecc : fetch_word Ubsan.M.loaded_segments (0x38ecc : word) = Some W_38ecc.
Proof. vm_refl. Qed.
Lemma D_38ecc : decode_any W_38ecc = Some (Branch BC_GE 12 9 476, 4%Z).
Proof. vm_refl. Qed.

Definition W_38ed0 : bv 32 := 0x414606b3.
Lemma F_38ed0 : fetch_word Ubsan.M.loaded_segments (0x38ed0 : word) = Some W_38ed0.
Proof. vm_refl. Qed.
Lemma D_38ed0 : decode_any W_38ed0 = Some (Op ALU_SUB 13 12 20, 4%Z).
Proof. vm_refl. Qed.

Definition W_38ed4 : bv 32 := 0x4146073b.
Lemma F_38ed4 : fetch_word Ubsan.M.loaded_segments (0x38ed4 : word) = Some W_38ed4.
Proof. vm_refl. Qed.
Lemma D_38ed4 : decode_any W_38ed4 = Some (Op32 ALU_SUB 14 12 20, 4%Z).
Proof. vm_refl. Qed.

Definition W_38ed8 : bv 32 := 0x1cd71863.
Lemma F_38ed8 : fetch_word Ubsan.M.loaded_segments (0x38ed8 : word) = Some W_38ed8.
Proof. vm_refl. Qed.
Lemma D_38ed8 : decode_any W_38ed8 = Some (Branch BC_NE 14 13 464, 4%Z).
Proof. vm_refl. Qed.

Definition W_38edc : bv 32 := 0x00d52623.
Lemma F_38edc : fetch_word Ubsan.M.loaded_segments (0x38edc : word) = Some W_38edc.
Proof. vm_refl. Qed.
Lemma D_38edc : decode_any W_38edc = Some (Store SZ4 10 13 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_38ee0 : bv 32 := 0x1b205263.
Lemma F_38ee0 : fetch_word Ubsan.M.loaded_segments (0x38ee0 : word) = Some W_38ee0.
Proof. vm_refl. Qed.
Lemma D_38ee0 : decode_any W_38ee0 = Some (Branch BC_GE 0 18 420, 4%Z).
Proof. vm_refl. Qed.

Definition W_38ee4 : bv 32 := 0x00000693.
Lemma F_38ee4 : fetch_word Ubsan.M.loaded_segments (0x38ee4 : word) = Some W_38ee4.
Proof. vm_refl. Qed.
Lemma D_38ee4 : decode_any W_38ee4 = Some (OpImm ALU_ADD 13 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_38ee8 : bv 32 := 0x012027b3.
Lemma F_38ee8 : fetch_word Ubsan.M.loaded_segments (0x38ee8 : word) = Some W_38ee8.
Proof. vm_refl. Qed.
Lemma D_38ee8 : decode_any W_38ee8 = Some (Op ALU_SLT 15 0 18, 4%Z).
Proof. vm_refl. Qed.

Definition W_38eec : bv 32 := 0x00299713.
Lemma F_38eec : fetch_word Ubsan.M.loaded_segments (0x38eec : word) = Some W_38eec.
Proof. vm_refl. Qed.
Lemma D_38eec : decode_any W_38eec = Some (ShiftImm ALU_SLL 14 19 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_38ef0 : bv 32 := 0x40f007b3.
Lemma F_38ef0 : fetch_word Ubsan.M.loaded_segments (0x38ef0 : word) = Some W_38ef0.
Proof. vm_refl. Qed.
Lemma D_38ef0 : decode_any W_38ef0 = Some (Op ALU_SUB 15 0 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_38ef4 : bv 32 := 0x0127f7b3.
Lemma F_38ef4 : fetch_word Ubsan.M.loaded_segments (0x38ef4 : word) = Some W_38ef4.
Proof. vm_refl. Qed.
Lemma D_38ef4 : decode_any W_38ef4 = Some (Op ALU_AND 15 15 18, 4%Z).
Proof. vm_refl. Qed.

Definition W_38ef8 : bv 32 := 0x80000837.
Lemma F_38ef8 : fetch_word Ubsan.M.loaded_segments (0x38ef8 : word) = Some W_38ef8.
Proof. vm_refl. Qed.
Lemma D_38ef8 : decode_any W_38ef8 = Some (Lui 16 524288, 4%Z).
Proof. vm_refl. Qed.

Definition W_38efc : bv 32 := 0xfff8081b.
Lemma F_38efc : fetch_word Ubsan.M.loaded_segments (0x38efc : word) = Some W_38efc.
Proof. vm_refl. Qed.
Lemma D_38efc : decode_any W_38efc = Some (OpImm32 16 16 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_38f00 : bv 32 := 0x10905263.
Lemma F_38f00 : fetch_word Ubsan.M.loaded_segments (0x38f00 : word) = Some W_38f00.
Proof. vm_refl. Qed.
Lemma D_38f00 : decode_any W_38f00 = Some (Branch BC_GE 0 9 260, 4%Z).
Proof. vm_refl. Qed.

Definition W_38f04 : bv 32 := 0x0006829b.
Lemma F_38f04 : fetch_word Ubsan.M.loaded_segments (0x38f04 : word) = Some W_38f04.
Proof. vm_refl. Qed.
Lemma D_38f04 : decode_any W_38f04 = Some (OpImm32 5 13 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_38f08 : bv 32 := 0x405588b3.
Lemma F_38f08 : fetch_word Ubsan.M.loaded_segments (0x38f08 : word) = Some W_38f08.
Proof. vm_refl. Qed.
Lemma D_38f08 : decode_any W_38f08 = Some (Op ALU_SUB 17 11 5, 4%Z).
Proof. vm_refl. Qed.

Definition W_38f0c : bv 32 := 0x405582bb.
Lemma F_38f0c : fetch_word Ubsan.M.loaded_segments (0x38f0c : word) = Some W_38f0c.
Proof. vm_refl. Qed.
Lemma D_38f0c : decode_any W_38f0c = Some (Op32 ALU_SUB 5 11 5, 4%Z).
Proof. vm_refl. Qed.

Definition W_38f10 : bv 32 := 0x19129c63.
Lemma F_38f10 : fetch_word Ubsan.M.loaded_segments (0x38f10 : word) = Some W_38f10.
Proof. vm_refl. Qed.
Lemma D_38f10 : decode_any W_38f10 = Some (Branch BC_NE 5 17 408, 4%Z).
Proof. vm_refl. Qed.

Definition W_38f14 : bv 32 := 0x01043283.
Lemma F_38f14 : fetch_word Ubsan.M.loaded_segments (0x38f14 : word) = Some W_38f14.
Proof. vm_refl. Qed.
Lemma D_38f14 : decode_any W_38f14 = Some (Load SZ8 true 5 8 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_38f18 : bv 32 := 0x0008831b.
Lemma F_38f18 : fetch_word Ubsan.M.loaded_segments (0x38f18 : word) = Some W_38f18.
Proof. vm_refl. Qed.
Lemma D_38f18 : decode_any W_38f18 = Some (OpImm32 6 17 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_38f1c : bv 32 := 0x00331893.
Lemma F_38f1c : fetch_word Ubsan.M.loaded_segments (0x38f1c : word) = Some W_38f1c.
Proof. vm_refl. Qed.
Lemma D_38f1c : decode_any W_38f1c = Some (ShiftImm ALU_SLL 17 6 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_38f20 : bv 32 := 0x011288b3.
Lemma F_38f20 : fetch_word Ubsan.M.loaded_segments (0x38f20 : word) = Some W_38f20.
Proof. vm_refl. Qed.
Lemma D_38f20 : decode_any W_38f20 = Some (Op ALU_ADD 17 5 17, 4%Z).
Proof. vm_refl. Qed.

Definition W_38f24 : bv 32 := 0x005033b3.
Lemma F_38f24 : fetch_word Ubsan.M.loaded_segments (0x38f24 : word) = Some W_38f24.
Proof. vm_refl. Qed.
Lemma D_38f24 : decode_any W_38f24 = Some (Op ALU_SLTU 7 0 5, 4%Z).
Proof. vm_refl. Qed.

Definition W_38f28 : bv 32 := 0x0018be13.
Lemma F_38f28 : fetch_word Ubsan.M.loaded_segments (0x38f28 : word) = Some W_38f28.
Proof. vm_refl. Qed.
Lemma D_38f28 : decode_any W_38f28 = Some (OpImm ALU_SLTU 28 17 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_38f2c : bv 32 := 0x17c38e63.
Lemma F_38f2c : fetch_word Ubsan.M.loaded_segments (0x38f2c : word) = Some W_38f2c.
Proof. vm_refl. Qed.
Lemma D_38f2c : decode_any W_38f2c = Some (Branch BC_EQ 7 28 380, 4%Z).
Proof. vm_refl. Qed.

Definition W_38f30 : bv 32 := 0x00032313.
Lemma F_38f30 : fetch_word Ubsan.M.loaded_segments (0x38f30 : word) = Some W_38f30.
Proof. vm_refl. Qed.
Lemma D_38f30 : decode_any W_38f30 = Some (OpImm ALU_SLT 6 6 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_38f34 : bv 32 := 0x0058b3b3.
Lemma F_38f34 : fetch_word Ubsan.M.loaded_segments (0x38f34 : word) = Some W_38f34.
Proof. vm_refl. Qed.
Lemma D_38f34 : decode_any W_38f34 = Some (Op ALU_SLTU 7 17 5, 4%Z).
Proof. vm_refl. Qed.

Definition W_38f38 : bv 32 := 0x0063c333.
Lemma F_38f38 : fetch_word Ubsan.M.loaded_segments (0x38f38 : word) = Some W_38f38.
Proof. vm_refl. Qed.
Lemma D_38f38 : decode_any W_38f38 = Some (Op ALU_XOR 6 7 6, 4%Z).
Proof. vm_refl. Qed.

Definition W_38f3c : bv 32 := 0x00134313.
Lemma F_38f3c : fetch_word Ubsan.M.loaded_segments (0x38f3c : word) = Some W_38f3c.
Proof. vm_refl. Qed.
Lemma D_38f3c : decode_any W_38f3c = Some (OpImm ALU_XOR 6 6 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_38f40 : bv 32 := 0x16030463.
Lemma F_38f40 : fetch_word Ubsan.M.loaded_segments (0x38f40 : word) = Some W_38f40.
Proof. vm_refl. Qed.
Lemma D_38f40 : decode_any W_38f40 = Some (Branch BC_EQ 6 0 360, 4%Z).
Proof. vm_refl. Qed.

Definition W_38f44 : bv 32 := 0x16028263.
Lemma F_38f44 : fetch_word Ubsan.M.loaded_segments (0x38f44 : word) = Some W_38f44.
Proof. vm_refl. Qed.
Lemma D_38f44 : decode_any W_38f44 = Some (Branch BC_EQ 5 0 356, 4%Z).
Proof. vm_refl. Qed.

Definition W_38f48 : bv 32 := 0x0078f293.
Lemma F_38f48 : fetch_word Ubsan.M.loaded_segments (0x38f48 : word) = Some W_38f48.
Proof. vm_refl. Qed.
Lemma D_38f48 : decode_any W_38f48 = Some (OpImm ALU_AND 5 17 7, 4%Z).
Proof. vm_refl. Qed.

Definition W_38f4c : bv 32 := 0x14029e63.
Lemma F_38f4c : fetch_word Ubsan.M.loaded_segments (0x38f4c : word) = Some W_38f4c.
Proof. vm_refl. Qed.
Lemma D_38f4c : decode_any W_38f4c = Some (Branch BC_NE 5 0 348, 4%Z).
Proof. vm_refl. Qed.

Definition W_38f50 : bv 32 := 0x00000313.
Lemma F_38f50 : fetch_word Ubsan.M.loaded_segments (0x38f50 : word) = Some W_38f50.
Proof. vm_refl. Qed.
Lemma D_38f50 : decode_any W_38f50 = Some (OpImm ALU_ADD 6 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_38f54 : bv 32 := 0x00369393.
Lemma F_38f54 : fetch_word Ubsan.M.loaded_segments (0x38f54 : word) = Some W_38f54.
Proof. vm_refl. Qed.
Lemma D_38f54 : decode_any W_38f54 = Some (ShiftImm ALU_SLL 7 13 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_38f58 : bv 32 := 0x40660f33.
Lemma F_38f58 : fetch_word Ubsan.M.loaded_segments (0x38f58 : word) = Some W_38f58.
Proof. vm_refl. Qed.
Lemma D_38f58 : decode_any W_38f58 = Some (Op ALU_SUB 30 12 6, 4%Z).
Proof. vm_refl. Qed.

Definition W_38f5c : bv 32 := 0x40660e3b.
Lemma F_38f5c : fetch_word Ubsan.M.loaded_segments (0x38f5c : word) = Some W_38f5c.
Proof. vm_refl. Qed.
Lemma D_38f5c : decode_any W_38f5c = Some (Op32 ALU_SUB 28 12 6, 4%Z).
Proof. vm_refl. Qed.

Definition W_38f60 : bv 32 := 0x15ee1463.
Lemma F_38f60 : fetch_word Ubsan.M.loaded_segments (0x38f60 : word) = Some W_38f60.
Proof. vm_refl. Qed.
Lemma D_38f60 : decode_any W_38f60 = Some (Branch BC_NE 28 30 328, 4%Z).
Proof. vm_refl. Qed.

Definition W_38f64 : bv 32 := 0x0008be83.
Lemma F_38f64 : fetch_word Ubsan.M.loaded_segments (0x38f64 : word) = Some W_38f64.
Proof. vm_refl. Qed.
Lemma D_38f64 : decode_any W_38f64 = Some (Load SZ8 true 29 17 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_38f68 : bv 32 := 0x000f0f1b.
Lemma F_38f68 : fetch_word Ubsan.M.loaded_segments (0x38f68 : word) = Some W_38f68.
Proof. vm_refl. Qed.
Lemma D_38f68 : decode_any W_38f68 = Some (OpImm32 30 30 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_38f6c : bv 32 := 0x002f1e13.
Lemma F_38f6c : fetch_word Ubsan.M.loaded_segments (0x38f6c : word) = Some W_38f6c.
Proof. vm_refl. Qed.
Lemma D_38f6c : decode_any W_38f6c = Some (ShiftImm ALU_SLL 28 30 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_38f70 : bv 32 := 0x01ce8e33.
Lemma F_38f70 : fetch_word Ubsan.M.loaded_segments (0x38f70 : word) = Some W_38f70.
Proof. vm_refl. Qed.
Lemma D_38f70 : decode_any W_38f70 = Some (Op ALU_ADD 28 29 28, 4%Z).
Proof. vm_refl. Qed.

Definition W_38f74 : bv 32 := 0x01d03fb3.
Lemma F_38f74 : fetch_word Ubsan.M.loaded_segments (0x38f74 : word) = Some W_38f74.
Proof. vm_refl. Qed.
Lemma D_38f74 : decode_any W_38f74 = Some (Op ALU_SLTU 31 0 29, 4%Z).
Proof. vm_refl. Qed.

Definition W_38f78 : bv 32 := 0x001e3913.
Lemma F_38f78 : fetch_word Ubsan.M.loaded_segments (0x38f78 : word) = Some W_38f78.
Proof. vm_refl. Qed.
Lemma D_38f78 : decode_any W_38f78 = Some (OpImm ALU_SLTU 18 28 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_38f7c : bv 32 := 0x132f8663.
Lemma F_38f7c : fetch_word Ubsan.M.loaded_segments (0x38f7c : word) = Some W_38f7c.
Proof. vm_refl. Qed.
Lemma D_38f7c : decode_any W_38f7c = Some (Branch BC_EQ 31 18 300, 4%Z).
Proof. vm_refl. Qed.

Definition W_38f80 : bv 32 := 0x01de3fb3.
Lemma F_38f80 : fetch_word Ubsan.M.loaded_segments (0x38f80 : word) = Some W_38f80.
Proof. vm_refl. Qed.
Lemma D_38f80 : decode_any W_38f80 = Some (Op ALU_SLTU 31 28 29, 4%Z).
Proof. vm_refl. Qed.

Definition W_38f84 : bv 32 := 0x000f2f13.
Lemma F_38f84 : fetch_word Ubsan.M.loaded_segments (0x38f84 : word) = Some W_38f84.
Proof. vm_refl. Qed.
Lemma D_38f84 : decode_any W_38f84 = Some (OpImm ALU_SLT 30 30 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_38f88 : bv 32 := 0x01efcf33.
Lemma F_38f88 : fetch_word Ubsan.M.loaded_segments (0x38f88 : word) = Some W_38f88.
Proof. vm_refl. Qed.
Lemma D_38f88 : decode_any W_38f88 = Some (Op ALU_XOR 30 31 30, 4%Z).
Proof. vm_refl. Qed.

Definition W_38f8c : bv 32 := 0x001f4f13.
Lemma F_38f8c : fetch_word Ubsan.M.loaded_segments (0x38f8c : word) = Some W_38f8c.
Proof. vm_refl. Qed.
Lemma D_38f8c : decode_any W_38f8c = Some (OpImm ALU_XOR 30 30 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_38f90 : bv 32 := 0x100f0c63.
Lemma F_38f90 : fetch_word Ubsan.M.loaded_segments (0x38f90 : word) = Some W_38f90.
Proof. vm_refl. Qed.
Lemma D_38f90 : decode_any W_38f90 = Some (Branch BC_EQ 30 0 280, 4%Z).
Proof. vm_refl. Qed.

Definition W_38f94 : bv 32 := 0x100e8a63.
Lemma F_38f94 : fetch_word Ubsan.M.loaded_segments (0x38f94 : word) = Some W_38f94.
Proof. vm_refl. Qed.
Lemma D_38f94 : decode_any W_38f94 = Some (Branch BC_EQ 29 0 276, 4%Z).
Proof. vm_refl. Qed.

Definition W_38f98 : bv 32 := 0x003e7e93.
Lemma F_38f98 : fetch_word Ubsan.M.loaded_segments (0x38f98 : word) = Some W_38f98.
Proof. vm_refl. Qed.
Lemma D_38f98 : decode_any W_38f98 = Some (OpImm ALU_AND 29 28 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_38f9c : bv 32 := 0x100e9663.
Lemma F_38f9c : fetch_word Ubsan.M.loaded_segments (0x38f9c : word) = Some W_38f9c.
Proof. vm_refl. Qed.
Lemma D_38f9c : decode_any W_38f9c = Some (Branch BC_NE 29 0 268, 4%Z).
Proof. vm_refl. Qed.

Definition W_38fa0 : bv 32 := 0x01053f03.
Lemma F_38fa0 : fetch_word Ubsan.M.loaded_segments (0x38fa0 : word) = Some W_38fa0.
Proof. vm_refl. Qed.
Lemma D_38fa0 : decode_any W_38fa0 = Some (Load SZ8 true 30 10 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_38fa4 : bv 32 := 0x007f0eb3.
Lemma F_38fa4 : fetch_word Ubsan.M.loaded_segments (0x38fa4 : word) = Some W_38fa4.
Proof. vm_refl. Qed.
Lemma D_38fa4 : decode_any W_38fa4 = Some (Op ALU_ADD 29 30 7, 4%Z).
Proof. vm_refl. Qed.

Definition W_38fa8 : bv 32 := 0x01e03fb3.
Lemma F_38fa8 : fetch_word Ubsan.M.loaded_segments (0x38fa8 : word) = Some W_38fa8.
Proof. vm_refl. Qed.
Lemma D_38fa8 : decode_any W_38fa8 = Some (Op ALU_SLTU 31 0 30, 4%Z).
Proof. vm_refl. Qed.

Definition W_38fac : bv 32 := 0x001eb913.
Lemma F_38fac : fetch_word Ubsan.M.loaded_segments (0x38fac : word) = Some W_38fac.
Proof. vm_refl. Qed.
Lemma D_38fac : decode_any W_38fac = Some (OpImm ALU_SLTU 18 29 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_38fb0 : bv 32 := 0x0f2f8c63.
Lemma F_38fb0 : fetch_word Ubsan.M.loaded_segments (0x38fb0 : word) = Some W_38fb0.
Proof. vm_refl. Qed.
Lemma D_38fb0 : decode_any W_38fb0 = Some (Branch BC_EQ 31 18 248, 4%Z).
Proof. vm_refl. Qed.

Definition W_38fb4 : bv 32 := 0x0feeea63.
Lemma F_38fb4 : fetch_word Ubsan.M.loaded_segments (0x38fb4 : word) = Some W_38fb4.
Proof. vm_refl. Qed.
Lemma D_38fb4 : decode_any W_38fb4 = Some (Branch BC_LTU 29 30 244, 4%Z).
Proof. vm_refl. Qed.

Definition W_38fb8 : bv 32 := 0x0e0f0863.
Lemma F_38fb8 : fetch_word Ubsan.M.loaded_segments (0x38fb8 : word) = Some W_38fb8.
Proof. vm_refl. Qed.
Lemma D_38fb8 : decode_any W_38fb8 = Some (Branch BC_EQ 30 0 240, 4%Z).
Proof. vm_refl. Qed.

Definition W_38fbc : bv 32 := 0x007eff13.
Lemma F_38fbc : fetch_word Ubsan.M.loaded_segments (0x38fbc : word) = Some W_38fbc.
Proof. vm_refl. Qed.
Lemma D_38fbc : decode_any W_38fbc = Some (OpImm ALU_AND 30 29 7, 4%Z).
Proof. vm_refl. Qed.

Definition W_38fc0 : bv 32 := 0x0e0f1463.
Lemma F_38fc0 : fetch_word Ubsan.M.loaded_segments (0x38fc0 : word) = Some W_38fc0.
Proof. vm_refl. Qed.
Lemma D_38fc0 : decode_any W_38fc0 = Some (Branch BC_NE 30 0 232, 4%Z).
Proof. vm_refl. Qed.

Definition W_38fc4 : bv 32 := 0x000ebf03.
Lemma F_38fc4 : fetch_word Ubsan.M.loaded_segments (0x38fc4 : word) = Some W_38fc4.
Proof. vm_refl. Qed.
Lemma D_38fc4 : decode_any W_38fc4 = Some (Load SZ8 true 30 29 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_38fc8 : bv 32 := 0x005f0eb3.
Lemma F_38fc8 : fetch_word Ubsan.M.loaded_segments (0x38fc8 : word) = Some W_38fc8.
Proof. vm_refl. Qed.
Lemma D_38fc8 : decode_any W_38fc8 = Some (Op ALU_ADD 29 30 5, 4%Z).
Proof. vm_refl. Qed.

Definition W_38fcc : bv 32 := 0x0deeee63.
Lemma F_38fcc : fetch_word Ubsan.M.loaded_segments (0x38fcc : word) = Some W_38fcc.
Proof. vm_refl. Qed.
Lemma D_38fcc : decode_any W_38fcc = Some (Branch BC_LTU 29 30 220, 4%Z).
Proof. vm_refl. Qed.

Definition W_38fd0 : bv 32 := 0x01e03fb3.
Lemma F_38fd0 : fetch_word Ubsan.M.loaded_segments (0x38fd0 : word) = Some W_38fd0.
Proof. vm_refl. Qed.
Lemma D_38fd0 : decode_any W_38fd0 = Some (Op ALU_SLTU 31 0 30, 4%Z).
Proof. vm_refl. Qed.

Definition W_38fd4 : bv 32 := 0x001eb913.
Lemma F_38fd4 : fetch_word Ubsan.M.loaded_segments (0x38fd4 : word) = Some W_38fd4.
Proof. vm_refl. Qed.
Lemma D_38fd4 : decode_any W_38fd4 = Some (OpImm ALU_SLTU 18 29 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_38fd8 : bv 32 := 0x012fcfb3.
Lemma F_38fd8 : fetch_word Ubsan.M.loaded_segments (0x38fd8 : word) = Some W_38fd8.
Proof. vm_refl. Qed.
Lemma D_38fd8 : decode_any W_38fd8 = Some (Op ALU_XOR 31 31 18, 4%Z).
Proof. vm_refl. Qed.

Definition W_38fdc : bv 32 := 0x0c0f8663.
Lemma F_38fdc : fetch_word Ubsan.M.loaded_segments (0x38fdc : word) = Some W_38fdc.
Proof. vm_refl. Qed.
Lemma D_38fdc : decode_any W_38fdc = Some (Branch BC_EQ 31 0 204, 4%Z).
Proof. vm_refl. Qed.

Definition W_38fe0 : bv 32 := 0x0c0f0463.
Lemma F_38fe0 : fetch_word Ubsan.M.loaded_segments (0x38fe0 : word) = Some W_38fe0.
Proof. vm_refl. Qed.
Lemma D_38fe0 : decode_any W_38fe0 = Some (Branch BC_EQ 30 0 200, 4%Z).
Proof. vm_refl. Qed.

Definition W_38fe4 : bv 32 := 0x01e28f33.
Lemma F_38fe4 : fetch_word Ubsan.M.loaded_segments (0x38fe4 : word) = Some W_38fe4.
Proof. vm_refl. Qed.
Lemma D_38fe4 : decode_any W_38fe4 = Some (Op ALU_ADD 30 5 30, 4%Z).
Proof. vm_refl. Qed.

Definition W_38fe8 : bv 32 := 0x003f7f13.
Lemma F_38fe8 : fetch_word Ubsan.M.loaded_segments (0x38fe8 : word) = Some W_38fe8.
Proof. vm_refl. Qed.
Lemma D_38fe8 : decode_any W_38fe8 = Some (OpImm ALU_AND 30 30 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_38fec : bv 32 := 0x0a0f1e63.
Lemma F_38fec : fetch_word Ubsan.M.loaded_segments (0x38fec : word) = Some W_38fec.
Proof. vm_refl. Qed.
Lemma D_38fec : decode_any W_38fec = Some (Branch BC_NE 30 0 188, 4%Z).
Proof. vm_refl. Qed.

Definition W_38ff0 : bv 32 := 0x000e2787.
Lemma F_38ff0 : fetch_word Ubsan.M.loaded_segments (0x38ff0 : word) = Some W_38ff0.
Proof. vm_refl. Qed.
Lemma D_38ff0 : decode_any W_38ff0 = Some (FLoad FMT_S 15 28 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_38ff4 : bv 32 := 0x00428293.
Lemma F_38ff4 : fetch_word Ubsan.M.loaded_segments (0x38ff4 : word) = Some W_38ff4.
Proof. vm_refl. Qed.
Lemma D_38ff4 : decode_any W_38ff4 = Some (OpImm ALU_ADD 5 5 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_38ff8 : bv 32 := 0x00fea027.
Lemma F_38ff8 : fetch_word Ubsan.M.loaded_segments (0x38ff8 : word) = Some W_38ff8.
Proof. vm_refl. Qed.
Lemma D_38ff8 : decode_any W_38ff8 = Some (FStore FMT_S 29 15 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_38ffc : bv 32 := 0x0013031b.
Lemma F_38ffc : fetch_word Ubsan.M.loaded_segments (0x38ffc : word) = Some W_38ffc.
Proof. vm_refl. Qed.
Lemma D_38ffc : decode_any W_38ffc = Some (OpImm32 6 6 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_39000 : bv 32 := 0xf4571ce3.
Lemma F_39000 : fetch_word Ubsan.M.loaded_segments (0x39000 : word) = Some W_39000.
Proof. vm_refl. Qed.
Lemma D_39000 : decode_any W_39000 = Some (Branch BC_NE 14 5 8024, 4%Z).
Proof. vm_refl. Qed.

Definition W_39004 : bv 32 := 0x0b068263.
Lemma F_39004 : fetch_word Ubsan.M.loaded_segments (0x39004 : word) = Some W_39004.
Proof. vm_refl. Qed.
Lemma D_39004 : decode_any W_39004 = Some (Branch BC_EQ 13 16 164, 4%Z).
Proof. vm_refl. Qed.

Definition W_39008 : bv 32 := 0x00168693.
Lemma F_39008 : fetch_word Ubsan.M.loaded_segments (0x39008 : word) = Some W_39008.
Proof. vm_refl. Qed.
Lemma D_39008 : decode_any W_39008 = Some (OpImm ALU_ADD 13 13 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_3900c : bv 32 := 0xeef69ae3.
Lemma F_3900c : fetch_word Ubsan.M.loaded_segments (0x3900c : word) = Some W_3900c.
Proof. vm_refl. Qed.
Lemma D_3900c : decode_any W_3900c = Some (Branch BC_NE 13 15 7924, 4%Z).
Proof. vm_refl. Qed.

Definition W_39010 : bv 32 := 0x0740006f.
Lemma F_39010 : fetch_word Ubsan.M.loaded_segments (0x39010 : word) = Some W_39010.
Proof. vm_refl. Qed.
Lemma D_39010 : decode_any W_39010 = Some (Jal 0 116, 4%Z).
Proof. vm_refl. Qed.

Definition W_39014 : bv 32 := 0x0000c517.
Lemma F_39014 : fetch_word Ubsan.M.loaded_segments (0x39014 : word) = Some W_39014.
Proof. vm_refl. Qed.
Lemma D_39014 : decode_any W_39014 = Some (Auipc 10 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_39018 : bv 32 := 0xe8453503.
Lemma F_39018 : fetch_word Ubsan.M.loaded_segments (0x39018 : word) = Some W_39018.
Proof. vm_refl. Qed.
Lemma D_39018 : decode_any W_39018 = Some (Load SZ8 true 10 10 3716, 4%Z).
Proof. vm_refl. Qed.

Definition W_3901c : bv 32 := 0x00052503.
Lemma F_3901c : fetch_word Ubsan.M.loaded_segments (0x3901c : word) = Some W_3901c.
Proof. vm_refl. Qed.
Lemma D_3901c : decode_any W_3901c = Some (Load SZ4 true 10 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_39020 : bv 32 := 0x00600593.
Lemma F_39020 : fetch_word Ubsan.M.loaded_segments (0x39020 : word) = Some W_39020.
Proof. vm_refl. Qed.
Lemma D_39020 : decode_any W_39020 = Some (OpImm ALU_ADD 11 0 6, 4%Z).
Proof. vm_refl. Qed.

Definition W_39024 : bv 32 := 0x04b55e63.
Lemma F_39024 : fetch_word Ubsan.M.loaded_segments (0x39024 : word) = Some W_39024.
Proof. vm_refl. Qed.
Lemma D_39024 : decode_any W_39024 = Some (Branch BC_GE 10 11 92, 4%Z).
Proof. vm_refl. Qed.

Definition W_39028 : bv 32 := 0xfffd8517.
Lemma F_39028 : fetch_word Ubsan.M.loaded_segments (0x39028 : word) = Some W_39028.
Proof. vm_refl. Qed.
Lemma D_39028 : decode_any W_39028 = Some (Auipc 10 1048536, 4%Z).
Proof. vm_refl. Qed.

Definition W_3902c : bv 32 := 0x43b50513.
Lemma F_3902c : fetch_word Ubsan.M.loaded_segments (0x3902c : word) = Some W_3902c.
Proof. vm_refl. Qed.
Lemma D_3902c : decode_any W_3902c = Some (OpImm ALU_ADD 10 10 1083, 4%Z).
Proof. vm_refl. Qed.

Definition W_39030 : bv 32 := 0x0200006f.
Lemma F_39030 : fetch_word Ubsan.M.loaded_segments (0x39030 : word) = Some W_39030.
Proof. vm_refl. Qed.
Lemma D_39030 : decode_any W_39030 = Some (Jal 0 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_39034 : bv 32 := 0x0000c517.
Lemma F_39034 : fetch_word Ubsan.M.loaded_segments (0x39034 : word) = Some W_39034.
Proof. vm_refl. Qed.
Lemma D_39034 : decode_any W_39034 = Some (Auipc 10 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_39038 : bv 32 := 0xe6453503.
Lemma F_39038 : fetch_word Ubsan.M.loaded_segments (0x39038 : word) = Some W_39038.
Proof. vm_refl. Qed.
Lemma D_39038 : decode_any W_39038 = Some (Load SZ8 true 10 10 3684, 4%Z).
Proof. vm_refl. Qed.

Definition W_3903c : bv 32 := 0x00052503.
Lemma F_3903c : fetch_word Ubsan.M.loaded_segments (0x3903c : word) = Some W_3903c.
Proof. vm_refl. Qed.
Lemma D_3903c : decode_any W_3903c = Some (Load SZ4 true 10 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_39040 : bv 32 := 0x00600593.
Lemma F_39040 : fetch_word Ubsan.M.loaded_segments (0x39040 : word) = Some W_39040.
Proof. vm_refl. Qed.
Lemma D_39040 : decode_any W_39040 = Some (OpImm ALU_ADD 11 0 6, 4%Z).
Proof. vm_refl. Qed.

Definition W_39044 : bv 32 := 0x02b55e63.
Lemma F_39044 : fetch_word Ubsan.M.loaded_segments (0x39044 : word) = Some W_39044.
Proof. vm_refl. Qed.
Lemma D_39044 : decode_any W_39044 = Some (Branch BC_GE 10 11 60, 4%Z).
Proof. vm_refl. Qed.

Definition W_39048 : bv 32 := 0xfffd8517.
Lemma F_39048 : fetch_word Ubsan.M.loaded_segments (0x39048 : word) = Some W_39048.
Proof. vm_refl. Qed.
Lemma D_39048 : decode_any W_39048 = Some (Auipc 10 1048536, 4%Z).
Proof. vm_refl. Qed.

Definition W_3904c : bv 32 := 0x42c50513.
Lemma F_3904c : fetch_word Ubsan.M.loaded_segments (0x3904c : word) = Some W_3904c.
Proof. vm_refl. Qed.
Lemma D_3904c : decode_any W_3904c = Some (OpImm ALU_ADD 10 10 1068, 4%Z).
Proof. vm_refl. Qed.

Definition W_39050 : bv 32 := 0xfffd7597.
Lemma F_39050 : fetch_word Ubsan.M.loaded_segments (0x39050 : word) = Some W_39050.
Proof. vm_refl. Qed.
Lemma D_39050 : decode_any W_39050 = Some (Auipc 11 1048535, 4%Z).
Proof. vm_refl. Qed.

Definition W_39054 : bv 32 := 0x4c558593.
Lemma F_39054 : fetch_word Ubsan.M.loaded_segments (0x39054 : word) = Some W_39054.
Proof. vm_refl. Qed.
Lemma D_39054 : decode_any W_39054 = Some (OpImm ALU_ADD 11 11 1221, 4%Z).
Proof. vm_refl. Qed.

Definition W_39058 : bv 32 := 0x00000613.
Lemma F_39058 : fetch_word Ubsan.M.loaded_segments (0x39058 : word) = Some W_39058.
Proof. vm_refl. Qed.
Lemma D_39058 : decode_any W_39058 = Some (OpImm ALU_ADD 12 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_3905c : bv 32 := 0x03813083.
Lemma F_3905c : fetch_word Ubsan.M.loaded_segments (0x3905c : word) = Some W_3905c.
Proof. vm_refl. Qed.
Lemma D_3905c : decode_any W_3905c = Some (Load SZ8 true 1 2 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_39060 : bv 32 := 0x03013403.
Lemma F_39060 : fetch_word Ubsan.M.loaded_segments (0x39060 : word) = Some W_39060.
Proof. vm_refl. Qed.
Lemma D_39060 : decode_any W_39060 = Some (Load SZ8 true 8 2 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_39064 : bv 32 := 0x02813483.
Lemma F_39064 : fetch_word Ubsan.M.loaded_segments (0x39064 : word) = Some W_39064.
Proof. vm_refl. Qed.
Lemma D_39064 : decode_any W_39064 = Some (Load SZ8 true 9 2 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_39068 : bv 32 := 0x02013903.
Lemma F_39068 : fetch_word Ubsan.M.loaded_segments (0x39068 : word) = Some W_39068.
Proof. vm_refl. Qed.
Lemma D_39068 : decode_any W_39068 = Some (Load SZ8 true 18 2 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_3906c : bv 32 := 0x01813983.
Lemma F_3906c : fetch_word Ubsan.M.loaded_segments (0x3906c : word) = Some W_3906c.
Proof. vm_refl. Qed.
Lemma D_3906c : decode_any W_3906c = Some (Load SZ8 true 19 2 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_39070 : bv 32 := 0x01013a03.
Lemma F_39070 : fetch_word Ubsan.M.loaded_segments (0x39070 : word) = Some W_39070.
Proof. vm_refl. Qed.
Lemma D_39070 : decode_any W_39070 = Some (Load SZ8 true 20 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_39074 : bv 32 := 0x00813a83.
Lemma F_39074 : fetch_word Ubsan.M.loaded_segments (0x39074 : word) = Some W_39074.
Proof. vm_refl. Qed.
Lemma D_39074 : decode_any W_39074 = Some (Load SZ8 true 21 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_39078 : bv 32 := 0x04010113.
Lemma F_39078 : fetch_word Ubsan.M.loaded_segments (0x39078 : word) = Some W_39078.
Proof. vm_refl. Qed.
Lemma D_39078 : decode_any W_39078 = Some (OpImm ALU_ADD 2 2 64, 4%Z).
Proof. vm_refl. Qed.

Definition W_3907c : bv 32 := 0xe49de06f.
Lemma F_3907c : fetch_word Ubsan.M.loaded_segments (0x3907c : word) = Some W_3907c.
Proof. vm_refl. Qed.
Lemma D_3907c : decode_any W_3907c = Some (Jal 0 1961544, 4%Z).
Proof. vm_refl. Qed.

Definition W_39080 : bv 32 := 0x00000513.
Lemma F_39080 : fetch_word Ubsan.M.loaded_segments (0x39080 : word) = Some W_39080.
Proof. vm_refl. Qed.
Lemma D_39080 : decode_any W_39080 = Some (OpImm ALU_ADD 10 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_39084 : bv 32 := 0x03813083.
Lemma F_39084 : fetch_word Ubsan.M.loaded_segments (0x39084 : word) = Some W_39084.
Proof. vm_refl. Qed.
Lemma D_39084 : decode_any W_39084 = Some (Load SZ8 true 1 2 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_39088 : bv 32 := 0x03013403.
Lemma F_39088 : fetch_word Ubsan.M.loaded_segments (0x39088 : word) = Some W_39088.
Proof. vm_refl. Qed.
Lemma D_39088 : decode_any W_39088 = Some (Load SZ8 true 8 2 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_3908c : bv 32 := 0x02813483.
Lemma F_3908c : fetch_word Ubsan.M.loaded_segments (0x3908c : word) = Some W_3908c.
Proof. vm_refl. Qed.
Lemma D_3908c : decode_any W_3908c = Some (Load SZ8 true 9 2 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_39090 : bv 32 := 0x02013903.
Lemma F_39090 : fetch_word Ubsan.M.loaded_segments (0x39090 : word) = Some W_39090.
Proof. vm_refl. Qed.
Lemma D_39090 : decode_any W_39090 = Some (Load SZ8 true 18 2 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_39094 : bv 32 := 0x01813983.
Lemma F_39094 : fetch_word Ubsan.M.loaded_segments (0x39094 : word) = Some W_39094.
Proof. vm_refl. Qed.
Lemma D_39094 : decode_any W_39094 = Some (Load SZ8 true 19 2 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_39098 : bv 32 := 0x01013a03.
Lemma F_39098 : fetch_word Ubsan.M.loaded_segments (0x39098 : word) = Some W_39098.
Proof. vm_refl. Qed.
Lemma D_39098 : decode_any W_39098 = Some (Load SZ8 true 20 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_3909c : bv 32 := 0x00813a83.
Lemma F_3909c : fetch_word Ubsan.M.loaded_segments (0x3909c : word) = Some W_3909c.
Proof. vm_refl. Qed.
Lemma D_3909c : decode_any W_3909c = Some (Load SZ8 true 21 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_390a0 : bv 32 := 0x04010113.
Lemma F_390a0 : fetch_word Ubsan.M.loaded_segments (0x390a0 : word) = Some W_390a0.
Proof. vm_refl. Qed.
Lemma D_390a0 : decode_any W_390a0 = Some (OpImm ALU_ADD 2 2 64, 4%Z).
Proof. vm_refl. Qed.

Definition W_390a4 : bv 32 := 0x00008067.
Lemma F_390a4 : fetch_word Ubsan.M.loaded_segments (0x390a4 : word) = Some W_390a4.
Proof. vm_refl. Qed.
Lemma D_390a4 : decode_any W_390a4 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_390a8 : bv 32 := 0xc0001073.
Lemma F_390a8 : fetch_word Ubsan.M.loaded_segments (0x390a8 : word) = Some W_390a8.
Proof. vm_refl. Qed.
Lemma D_390a8 : decode_any W_390a8 = Some (Csr CSR_RW 0 0 3072, 4%Z).
Proof. vm_refl. Qed.
