(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require BvWfKernel.
(* [comment removed for export] *)
From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OssFuzzTheorems.jsoncons.fuzz_bson_parser_max.images Require Import Ubsan.
Open Scope bv_scope.

Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

(* [comment removed for export] *)
Definition W_9eb6c : bv 32 := 0x02d61863.
Lemma F_9eb6c : fetch_word Ubsan.M.loaded_segments (0xa01a0 : word) = Some W_9eb6c.
Proof. vm_refl. Qed.
Lemma D_9eb6c : decode_any W_9eb6c = Some (Branch BC_NE 12 13 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9eb8c : bv 32 := 0x02e5b423.
Lemma F_9eb8c : fetch_word Ubsan.M.loaded_segments (0xa01c0 : word) = Some W_9eb8c.
Proof. vm_refl. Qed.
Lemma D_9eb8c : decode_any W_9eb8c = Some (Store SZ8 11 14 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9eb9c : bv 32 := 0x0100006f.
Lemma F_9eb9c : fetch_word Ubsan.M.loaded_segments (0xa01d0 : word) = Some W_9eb9c.
Proof. vm_refl. Qed.
Lemma D_9eb9c : decode_any W_9eb9c = Some (Jal 0 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9eba0 : bv 32 := 0x00058513.
Lemma F_9eba0 : fetch_word Ubsan.M.loaded_segments (0xa01d4 : word) = Some W_9eba0.
Proof. vm_refl. Qed.
Lemma D_9eba0 : decode_any W_9eba0 = Some (OpImm ALU_ADD 10 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9ebc8 : bv 32 := 0x08c48413.
Lemma F_9ebc8 : fetch_word Ubsan.M.loaded_segments (0xa01fc : word) = Some W_9ebc8.
Proof. vm_refl. Qed.
Lemma D_9ebc8 : decode_any W_9ebc8 = Some (OpImm ALU_ADD 8 9 140, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9ec04 : bv 32 := 0x0204b583.
Lemma F_9ec04 : fetch_word Ubsan.M.loaded_segments (0xa0238 : word) = Some W_9ec04.
Proof. vm_refl. Qed.
Lemma D_9ec04 : decode_any W_9ec04 = Some (Load SZ8 true 11 9 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9ec10 : bv 32 := 0x00150593.
Lemma F_9ec10 : fetch_word Ubsan.M.loaded_segments (0xa0244 : word) = Some W_9ec10.
Proof. vm_refl. Qed.
Lemma D_9ec10 : decode_any W_9ec10 = Some (OpImm ALU_ADD 11 10 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9ec14 : bv 32 := 0x02b4b423.
Lemma F_9ec14 : fetch_word Ubsan.M.loaded_segments (0xa0248 : word) = Some W_9ec14.
Proof. vm_refl. Qed.
Lemma D_9ec14 : decode_any W_9ec14 = Some (Store SZ8 9 11 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9ec18 : bv 32 := 0x01250023.
Lemma F_9ec18 : fetch_word Ubsan.M.loaded_segments (0xa024c : word) = Some W_9ec18.
Proof. vm_refl. Qed.
Lemma D_9ec18 : decode_any W_9ec18 = Some (Store SZ1 10 18 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9ec1c : bv 32 := 0x0140006f.
Lemma F_9ec1c : fetch_word Ubsan.M.loaded_segments (0xa0250 : word) = Some W_9ec1c.
Proof. vm_refl. Qed.
Lemma D_9ec1c : decode_any W_9ec1c = Some (Jal 0 20, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9ec20 : bv 32 := 0x00048513.
Lemma F_9ec20 : fetch_word Ubsan.M.loaded_segments (0xa0254 : word) = Some W_9ec20.
Proof. vm_refl. Qed.
Lemma D_9ec20 : decode_any W_9ec20 = Some (OpImm ALU_ADD 10 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9ec24 : bv 32 := 0x00068593.
Lemma F_9ec24 : fetch_word Ubsan.M.loaded_segments (0xa0258 : word) = Some W_9ec24.
Proof. vm_refl. Qed.
Lemma D_9ec24 : decode_any W_9ec24 = Some (OpImm ALU_ADD 11 13 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9ec28 : bv 32 := 0x07c000ef.
Lemma F_9ec28 : fetch_word Ubsan.M.loaded_segments (0xa025c : word) = Some W_9ec28.
Proof. vm_refl. Qed.
Lemma D_9ec28 : decode_any W_9ec28 = Some (Jal 1 124, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9ec2c : bv 32 := 0x00050693.
Lemma F_9ec2c : fetch_word Ubsan.M.loaded_segments (0xa0260 : word) = Some W_9ec2c.
Proof. vm_refl. Qed.
Lemma D_9ec2c : decode_any W_9ec2c = Some (OpImm ALU_ADD 13 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9ec30 : bv 32 := 0x00000513.
Lemma F_9ec30 : fetch_word Ubsan.M.loaded_segments (0xa0264 : word) = Some W_9ec30.
Proof. vm_refl. Qed.
Lemma D_9ec30 : decode_any W_9ec30 = Some (OpImm ALU_ADD 10 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9ec34 : bv 32 := 0x00042583.
Lemma F_9ec34 : fetch_word Ubsan.M.loaded_segments (0xa0268 : word) = Some W_9ec34.
Proof. vm_refl. Qed.
Lemma D_9ec34 : decode_any W_9ec34 = Some (Load SZ4 true 11 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9ec38 : bv 32 := 0x1604262f.
Lemma F_9ec38 : fetch_word Ubsan.M.loaded_segments (0xa026c : word) = Some W_9ec38.
Proof. vm_refl. Qed.
Lemma D_9ec38 : decode_any W_9ec38 = Some (Lr AW true true 12 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9ec3c : bv 32 := 0x00b61663.
Lemma F_9ec3c : fetch_word Ubsan.M.loaded_segments (0xa0270 : word) = Some W_9ec3c.
Proof. vm_refl. Qed.
Lemma D_9ec3c : decode_any W_9ec3c = Some (Branch BC_NE 12 11 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9ec40 : bv 32 := 0x1ea4272f.
Lemma F_9ec40 : fetch_word Ubsan.M.loaded_segments (0xa0274 : word) = Some W_9ec40.
Proof. vm_refl. Qed.
Lemma D_9ec40 : decode_any W_9ec40 = Some (Sc AW true true 14 8 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9ec44 : bv 32 := 0xfe071ae3.
Lemma F_9ec44 : fetch_word Ubsan.M.loaded_segments (0xa0278 : word) = Some W_9ec44.
Proof. vm_refl. Qed.
Lemma D_9ec44 : decode_any W_9ec44 = Some (Branch BC_NE 14 0 8180, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9ec48 : bv 32 := 0x0006061b.
Lemma F_9ec48 : fetch_word Ubsan.M.loaded_segments (0xa027c : word) = Some W_9ec48.
Proof. vm_refl. Qed.
Lemma D_9ec48 : decode_any W_9ec48 = Some (OpImm32 12 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9ec4c : bv 32 := 0xfeb614e3.
Lemma F_9ec4c : fetch_word Ubsan.M.loaded_segments (0xa0280 : word) = Some W_9ec4c.
Proof. vm_refl. Qed.
Lemma D_9ec4c : decode_any W_9ec4c = Some (Branch BC_NE 12 11 8168, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9ec50 : bv 32 := 0x02159593.
Lemma F_9ec50 : fetch_word Ubsan.M.loaded_segments (0xa0284 : word) = Some W_9ec50.
Proof. vm_refl. Qed.
Lemma D_9ec50 : decode_any W_9ec50 = Some (ShiftImm ALU_SLL 11 11 33, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9ec54 : bv 32 := 0x0205da63.
Lemma F_9ec54 : fetch_word Ubsan.M.loaded_segments (0xa0288 : word) = Some W_9ec54.
Proof. vm_refl. Qed.
Lemma D_9ec54 : decode_any W_9ec54 = Some (Branch BC_GE 11 0 52, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9ec58 : bv 32 := 0x06200893.
Lemma F_9ec58 : fetch_word Ubsan.M.loaded_segments (0xa028c : word) = Some W_9ec58.
Proof. vm_refl. Qed.
Lemma D_9ec58 : decode_any W_9ec58 = Some (OpImm ALU_ADD 17 0 98, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9ec5c : bv 32 := 0x08100593.
Lemma F_9ec5c : fetch_word Ubsan.M.loaded_segments (0xa0290 : word) = Some W_9ec5c.
Proof. vm_refl. Qed.
Lemma D_9ec5c : decode_any W_9ec5c = Some (OpImm ALU_ADD 11 0 129, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9ec60 : bv 32 := 0x00100613.
Lemma F_9ec60 : fetch_word Ubsan.M.loaded_segments (0xa0294 : word) = Some W_9ec60.
Proof. vm_refl. Qed.
Lemma D_9ec60 : decode_any W_9ec60 = Some (OpImm ALU_ADD 12 0 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9ec64 : bv 32 := 0xfda00713.
Lemma F_9ec64 : fetch_word Ubsan.M.loaded_segments (0xa0298 : word) = Some W_9ec64.
Proof. vm_refl. Qed.
Lemma D_9ec64 : decode_any W_9ec64 = Some (OpImm ALU_ADD 14 0 4058, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9ec68 : bv 32 := 0x00040513.
Lemma F_9ec68 : fetch_word Ubsan.M.loaded_segments (0xa029c : word) = Some W_9ec68.
Proof. vm_refl. Qed.
Lemma D_9ec68 : decode_any W_9ec68 = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9ec6c : bv 32 := 0x00000073.
Lemma F_9ec6c : fetch_word Ubsan.M.loaded_segments (0xa02a0 : word) = Some W_9ec6c.
Proof. vm_refl. Qed.
Lemma D_9ec6c : decode_any W_9ec6c = Some (Ecall, 4%Z).
Proof. vm_refl. Qed.
Lemma E_9ec6c : is_ecall W_9ec6c = true.
Proof. reflexivity. Qed.

(* [comment removed for export] *)
Definition W_9ec70 : bv 32 := 0x00e51c63.
Lemma F_9ec70 : fetch_word Ubsan.M.loaded_segments (0xa02a4 : word) = Some W_9ec70.
Proof. vm_refl. Qed.
Lemma D_9ec70 : decode_any W_9ec70 = Some (Branch BC_NE 10 14 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9ec74 : bv 32 := 0x06200893.
Lemma F_9ec74 : fetch_word Ubsan.M.loaded_segments (0xa02a8 : word) = Some W_9ec74.
Proof. vm_refl. Qed.
Lemma D_9ec74 : decode_any W_9ec74 = Some (OpImm ALU_ADD 17 0 98, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9ec78 : bv 32 := 0x00100593.
Lemma F_9ec78 : fetch_word Ubsan.M.loaded_segments (0xa02ac : word) = Some W_9ec78.
Proof. vm_refl. Qed.
Lemma D_9ec78 : decode_any W_9ec78 = Some (OpImm ALU_ADD 11 0 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9ec7c : bv 32 := 0x00100613.
Lemma F_9ec7c : fetch_word Ubsan.M.loaded_segments (0xa02b0 : word) = Some W_9ec7c.
Proof. vm_refl. Qed.
Lemma D_9ec7c : decode_any W_9ec7c = Some (OpImm ALU_ADD 12 0 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9ec80 : bv 32 := 0x00040513.
Lemma F_9ec80 : fetch_word Ubsan.M.loaded_segments (0xa02b4 : word) = Some W_9ec80.
Proof. vm_refl. Qed.
Lemma D_9ec80 : decode_any W_9ec80 = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9ec84 : bv 32 := 0x00000073.
Lemma F_9ec84 : fetch_word Ubsan.M.loaded_segments (0xa02b8 : word) = Some W_9ec84.
Proof. vm_refl. Qed.
Lemma D_9ec84 : decode_any W_9ec84 = Some (Ecall, 4%Z).
Proof. vm_refl. Qed.
Lemma E_9ec84 : is_ecall W_9ec84 = true.
Proof. reflexivity. Qed.

(* [comment removed for export] *)
Definition W_9ec88 : bv 32 := 0x00068513.
Lemma F_9ec88 : fetch_word Ubsan.M.loaded_segments (0xa02bc : word) = Some W_9ec88.
Proof. vm_refl. Qed.
Lemma D_9ec88 : decode_any W_9ec88 = Some (OpImm ALU_ADD 10 13 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9ec8c : bv 32 := 0x01813083.
Lemma F_9ec8c : fetch_word Ubsan.M.loaded_segments (0xa02c0 : word) = Some W_9ec8c.
Proof. vm_refl. Qed.
Lemma D_9ec8c : decode_any W_9ec8c = Some (Load SZ8 true 1 2 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9ec90 : bv 32 := 0x01013403.
Lemma F_9ec90 : fetch_word Ubsan.M.loaded_segments (0xa02c4 : word) = Some W_9ec90.
Proof. vm_refl. Qed.
Lemma D_9ec90 : decode_any W_9ec90 = Some (Load SZ8 true 8 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9ec94 : bv 32 := 0x00813483.
Lemma F_9ec94 : fetch_word Ubsan.M.loaded_segments (0xa02c8 : word) = Some W_9ec94.
Proof. vm_refl. Qed.
Lemma D_9ec94 : decode_any W_9ec94 = Some (Load SZ8 true 9 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9ec98 : bv 32 := 0x00013903.
Lemma F_9ec98 : fetch_word Ubsan.M.loaded_segments (0xa02cc : word) = Some W_9ec98.
Proof. vm_refl. Qed.
Lemma D_9ec98 : decode_any W_9ec98 = Some (Load SZ8 true 18 2 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9ec9c : bv 32 := 0x02010113.
Lemma F_9ec9c : fetch_word Ubsan.M.loaded_segments (0xa02d0 : word) = Some W_9ec9c.
Proof. vm_refl. Qed.
Lemma D_9ec9c : decode_any W_9ec9c = Some (OpImm ALU_ADD 2 2 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9eca0 : bv 32 := 0x00008067.
Lemma F_9eca0 : fetch_word Ubsan.M.loaded_segments (0xa02d4 : word) = Some W_9eca0.
Proof. vm_refl. Qed.
Lemma D_9eca0 : decode_any W_9eca0 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9eca4 : bv 32 := 0xfd010113.
Lemma F_9eca4 : fetch_word Ubsan.M.loaded_segments (0xa02d8 : word) = Some W_9eca4.
Proof. vm_refl. Qed.
Lemma D_9eca4 : decode_any W_9eca4 = Some (OpImm ALU_ADD 2 2 4048, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9eca8 : bv 32 := 0x02113423.
Lemma F_9eca8 : fetch_word Ubsan.M.loaded_segments (0xa02dc : word) = Some W_9eca8.
Proof. vm_refl. Qed.
Lemma D_9eca8 : decode_any W_9eca8 = Some (Store SZ8 2 1 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9ecac : bv 32 := 0x02813023.
Lemma F_9ecac : fetch_word Ubsan.M.loaded_segments (0xa02e0 : word) = Some W_9ecac.
Proof. vm_refl. Qed.
Lemma D_9ecac : decode_any W_9ecac = Some (Store SZ8 2 8 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9ecb0 : bv 32 := 0x00913c23.
Lemma F_9ecb0 : fetch_word Ubsan.M.loaded_segments (0xa02e4 : word) = Some W_9ecb0.
Proof. vm_refl. Qed.
Lemma D_9ecb0 : decode_any W_9ecb0 = Some (Store SZ8 2 9 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9ecb4 : bv 32 := 0x01213823.
Lemma F_9ecb4 : fetch_word Ubsan.M.loaded_segments (0xa02e8 : word) = Some W_9ecb4.
Proof. vm_refl. Qed.
Lemma D_9ecb4 : decode_any W_9ecb4 = Some (Store SZ8 2 18 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9ecb8 : bv 32 := 0x00017617.
Lemma F_9ecb8 : fetch_word Ubsan.M.loaded_segments (0xa02ec : word) = Some W_9ecb8.
Proof. vm_refl. Qed.
Lemma D_9ecb8 : decode_any W_9ecb8 = Some (Auipc 12 23, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9ecbc : bv 32 := 0xefc63403.
Lemma F_9ecbc : fetch_word Ubsan.M.loaded_segments (0xa02f0 : word) = Some W_9ecbc.
Proof. vm_refl. Qed.
Lemma D_9ecbc : decode_any W_9ecbc = Some (Load SZ8 true 8 12 3836, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9ecc0 : bv 32 := 0x00043603.
Lemma F_9ecc0 : fetch_word Ubsan.M.loaded_segments (0xa02f4 : word) = Some W_9ecc0.
Proof. vm_refl. Qed.
Lemma D_9ecc0 : decode_any W_9ecc0 = Some (Load SZ8 true 12 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9ecc4 : bv 32 := 0x00c13423.
Lemma F_9ecc4 : fetch_word Ubsan.M.loaded_segments (0xa02f8 : word) = Some W_9ecc4.
Proof. vm_refl. Qed.
Lemma D_9ecc4 : decode_any W_9ecc4 = Some (Store SZ8 2 12 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9ecc8 : bv 32 := 0x02053683.
Lemma F_9ecc8 : fetch_word Ubsan.M.loaded_segments (0xa02fc : word) = Some W_9ecc8.
Proof. vm_refl. Qed.
Lemma D_9ecc8 : decode_any W_9ecc8 = Some (Load SZ8 true 13 10 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9eccc : bv 32 := 0x00b103a3.
Lemma F_9eccc : fetch_word Ubsan.M.loaded_segments (0xa0300 : word) = Some W_9eccc.
Proof. vm_refl. Qed.
Lemma D_9eccc : decode_any W_9eccc = Some (Store SZ1 2 11 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9ecd0 : bv 32 := 0x02068c63.
Lemma F_9ecd0 : fetch_word Ubsan.M.loaded_segments (0xa0304 : word) = Some W_9ecd0.
Proof. vm_refl. Qed.
Lemma D_9ecd0 : decode_any W_9ecd0 = Some (Branch BC_EQ 13 0 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9ecd4 : bv 32 := 0x02853603.
Lemma F_9ecd4 : fetch_word Ubsan.M.loaded_segments (0xa0308 : word) = Some W_9ecd4.
Proof. vm_refl. Qed.
Lemma D_9ecd4 : decode_any W_9ecd4 = Some (Load SZ8 true 12 10 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9ecd8 : bv 32 := 0x00d60863.
Lemma F_9ecd8 : fetch_word Ubsan.M.loaded_segments (0xa030c : word) = Some W_9ecd8.
Proof. vm_refl. Qed.
Lemma D_9ecd8 : decode_any W_9ecd8 = Some (Branch BC_EQ 12 13 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9ecdc : bv 32 := 0x09052703.
Lemma F_9ecdc : fetch_word Ubsan.M.loaded_segments (0xa0310 : word) = Some W_9ecdc.
Proof. vm_refl. Qed.
Lemma D_9ecdc : decode_any W_9ecdc = Some (Load SZ4 true 14 10 144, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9ece0 : bv 32 := 0x0ff5f793.
Lemma F_9ece0 : fetch_word Ubsan.M.loaded_segments (0xa0314 : word) = Some W_9ece0.
Proof. vm_refl. Qed.
Lemma D_9ece0 : decode_any W_9ece0 = Some (OpImm ALU_AND 15 11 255, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9ece4 : bv 32 := 0x02f71e63.
Lemma F_9ece4 : fetch_word Ubsan.M.loaded_segments (0xa0318 : word) = Some W_9ece4.
Proof. vm_refl. Qed.
Lemma D_9ece4 : decode_any W_9ece4 = Some (Branch BC_NE 14 15 60, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9ece8 : bv 32 := 0x04853683.
Lemma F_9ece8 : fetch_word Ubsan.M.loaded_segments (0xa031c : word) = Some W_9ece8.
Proof. vm_refl. Qed.
Lemma D_9ece8 : decode_any W_9ece8 = Some (Load SZ8 true 13 10 72, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9ecec : bv 32 := 0x00710593.
Lemma F_9ecec : fetch_word Ubsan.M.loaded_segments (0xa0320 : word) = Some W_9ecec.
Proof. vm_refl. Qed.
Lemma D_9ecec : decode_any W_9ecec = Some (OpImm ALU_ADD 11 2 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9ecf0 : bv 32 := 0x00100613.
Lemma F_9ecf0 : fetch_word Ubsan.M.loaded_segments (0xa0324 : word) = Some W_9ecf0.
Proof. vm_refl. Qed.
Lemma D_9ecf0 : decode_any W_9ecf0 = Some (OpImm ALU_ADD 12 0 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9ed90 : bv 32 := 0x06053683.
Lemma F_9ed90 : fetch_word Ubsan.M.loaded_segments (0xa03c4 : word) = Some W_9ed90.
Proof. vm_refl. Qed.
Lemma D_9ed90 : decode_any W_9ed90 = Some (Load SZ8 true 13 10 96, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9ed94 : bv 32 := 0x02c53c23.
Lemma F_9ed94 : fetch_word Ubsan.M.loaded_segments (0xa03c8 : word) = Some W_9ed94.
Proof. vm_refl. Qed.
Lemma D_9ed94 : decode_any W_9ed94 = Some (Store SZ8 10 12 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9eda0 : bv 32 := 0x00053823.
Lemma F_9eda0 : fetch_word Ubsan.M.loaded_segments (0xa03d4 : word) = Some W_9eda0.
Proof. vm_refl. Qed.
Lemma D_9eda0 : decode_any W_9eda0 = Some (Store SZ8 10 0 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9eda4 : bv 32 := 0x02d53023.
Lemma F_9eda4 : fetch_word Ubsan.M.loaded_segments (0xa03d8 : word) = Some W_9eda4.
Proof. vm_refl. Qed.
Lemma D_9eda4 : decode_any W_9eda4 = Some (Store SZ8 10 13 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9eda8 : bv 32 := 0x02c53423.
Lemma F_9eda8 : fetch_word Ubsan.M.loaded_segments (0xa03dc : word) = Some W_9eda8.
Proof. vm_refl. Qed.
Lemma D_9eda8 : decode_any W_9eda8 = Some (Store SZ8 10 12 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9edac : bv 32 := 0x00000513.
Lemma F_9edac : fetch_word Ubsan.M.loaded_segments (0xa03e0 : word) = Some W_9edac.
Proof. vm_refl. Qed.
Lemma D_9edac : decode_any W_9edac = Some (OpImm ALU_ADD 10 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9edb0 : bv 32 := 0x00008067.
Lemma F_9edb0 : fetch_word Ubsan.M.loaded_segments (0xa03e4 : word) = Some W_9edb0.
Proof. vm_refl. Qed.
Lemma D_9edb0 : decode_any W_9edb0 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9edb4 : bv 32 := 0x0205e593.
Lemma F_9edb4 : fetch_word Ubsan.M.loaded_segments (0xa03e8 : word) = Some W_9edb4.
Proof. vm_refl. Qed.
Lemma D_9edb4 : decode_any W_9edb4 = Some (OpImm ALU_OR 11 11 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9edb8 : bv 32 := 0x00b52023.
Lemma F_9edb8 : fetch_word Ubsan.M.loaded_segments (0xa03ec : word) = Some W_9edb8.
Proof. vm_refl. Qed.
Lemma D_9edb8 : decode_any W_9edb8 = Some (Store SZ4 10 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9edbc : bv 32 := 0xfff00513.
Lemma F_9edbc : fetch_word Ubsan.M.loaded_segments (0xa03f0 : word) = Some W_9edbc.
Proof. vm_refl. Qed.
Lemma D_9edbc : decode_any W_9edbc = Some (OpImm ALU_ADD 10 0 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9edc0 : bv 32 := 0x00008067.
Lemma F_9edc0 : fetch_word Ubsan.M.loaded_segments (0xa03f4 : word) = Some W_9edc0.
Proof. vm_refl. Qed.
Lemma D_9edc0 : decode_any W_9edc0 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9edc4 : bv 32 := 0xff010113.
Lemma F_9edc4 : fetch_word Ubsan.M.loaded_segments (0xa03f8 : word) = Some W_9edc4.
Proof. vm_refl. Qed.
Lemma D_9edc4 : decode_any W_9edc4 = Some (OpImm ALU_ADD 2 2 4080, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9edc8 : bv 32 := 0x00113423.
Lemma F_9edc8 : fetch_word Ubsan.M.loaded_segments (0xa03fc : word) = Some W_9edc8.
Proof. vm_refl. Qed.
Lemma D_9edc8 : decode_any W_9edc8 = Some (Store SZ8 2 1 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9edcc : bv 32 := 0x00813023.
Lemma F_9edcc : fetch_word Ubsan.M.loaded_segments (0xa0400 : word) = Some W_9edcc.
Proof. vm_refl. Qed.
Lemma D_9edcc : decode_any W_9edcc = Some (Store SZ8 2 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9edd0 : bv 32 := 0x41c000ef.
Lemma F_9edd0 : fetch_word Ubsan.M.loaded_segments (0xa0404 : word) = Some W_9edd0.
Proof. vm_refl. Qed.
Lemma D_9edd0 : decode_any W_9edd0 = Some (Jal 1 1052, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9edd4 : bv 32 := 0x00053403.
Lemma F_9edd4 : fetch_word Ubsan.M.loaded_segments (0xa0408 : word) = Some W_9edd4.
Proof. vm_refl. Qed.
Lemma D_9edd4 : decode_any W_9edd4 = Some (Load SZ8 true 8 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9edd8 : bv 32 := 0x12041663.
Lemma F_9edd8 : fetch_word Ubsan.M.loaded_segments (0xa040c : word) = Some W_9edd8.
Proof. vm_refl. Qed.
Lemma D_9edd8 : decode_any W_9edd8 = Some (Branch BC_NE 8 0 300, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9eddc : bv 32 := 0x0004a517.
Lemma F_9eddc : fetch_word Ubsan.M.loaded_segments (0xa0410 : word) = Some W_9eddc.
Proof. vm_refl. Qed.
Lemma D_9eddc : decode_any W_9eddc = Some (Auipc 10 74, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9ede0 : bv 32 := 0x37853403.
Lemma F_9ede0 : fetch_word Ubsan.M.loaded_segments (0xa0414 : word) = Some W_9ede0.
Proof. vm_refl. Qed.
Lemma D_9ede0 : decode_any W_9ede0 = Some (Load SZ8 true 8 10 888, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9ede4 : bv 32 := 0x04040a63.
Lemma F_9ede4 : fetch_word Ubsan.M.loaded_segments (0xa0418 : word) = Some W_9ede4.
Proof. vm_refl. Qed.
Lemma D_9ede4 : decode_any W_9ede4 = Some (Branch BC_EQ 8 0 84, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9ee38 : bv 32 := 0x00018517.
Lemma F_9ee38 : fetch_word Ubsan.M.loaded_segments (0xa046c : word) = Some W_9ee38.
Proof. vm_refl. Qed.
Lemma D_9ee38 : decode_any W_9ee38 = Some (Auipc 10 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9ee3c : bv 32 := 0x06c53403.
Lemma F_9ee3c : fetch_word Ubsan.M.loaded_segments (0xa0470 : word) = Some W_9ee3c.
Proof. vm_refl. Qed.
Lemma D_9ee3c : decode_any W_9ee3c = Some (Load SZ8 true 8 10 108, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9ee40 : bv 32 := 0x04040a63.
Lemma F_9ee40 : fetch_word Ubsan.M.loaded_segments (0xa0474 : word) = Some W_9ee40.
Proof. vm_refl. Qed.
Lemma D_9ee40 : decode_any W_9ee40 = Some (Branch BC_EQ 8 0 84, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9ee44 : bv 32 := 0x08c42503.
Lemma F_9ee44 : fetch_word Ubsan.M.loaded_segments (0xa0478 : word) = Some W_9ee44.
Proof. vm_refl. Qed.
Lemma D_9ee44 : decode_any W_9ee44 = Some (Load SZ4 true 10 8 140, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9ee48 : bv 32 := 0x00054663.
Lemma F_9ee48 : fetch_word Ubsan.M.loaded_segments (0xa047c : word) = Some W_9ee48.
Proof. vm_refl. Qed.
Lemma D_9ee48 : decode_any W_9ee48 = Some (Branch BC_LT 10 0 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9ee54 : bv 32 := 0x02843503.
Lemma F_9ee54 : fetch_word Ubsan.M.loaded_segments (0xa0488 : word) = Some W_9ee54.
Proof. vm_refl. Qed.
Lemma D_9ee54 : decode_any W_9ee54 = Some (Load SZ8 true 10 8 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9ee58 : bv 32 := 0x03843583.
Lemma F_9ee58 : fetch_word Ubsan.M.loaded_segments (0xa048c : word) = Some W_9ee58.
Proof. vm_refl. Qed.
Lemma D_9ee58 : decode_any W_9ee58 = Some (Load SZ8 true 11 8 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9ee5c : bv 32 := 0x00b50c63.
Lemma F_9ee5c : fetch_word Ubsan.M.loaded_segments (0xa0490 : word) = Some W_9ee5c.
Proof. vm_refl. Qed.
Lemma D_9ee5c : decode_any W_9ee5c = Some (Branch BC_EQ 10 11 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9ee60 : bv 32 := 0x04843683.
Lemma F_9ee60 : fetch_word Ubsan.M.loaded_segments (0xa0494 : word) = Some W_9ee60.
Proof. vm_refl. Qed.
Lemma D_9ee60 : decode_any W_9ee60 = Some (Load SZ8 true 13 8 72, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9ee64 : bv 32 := 0x00040513.
Lemma F_9ee64 : fetch_word Ubsan.M.loaded_segments (0xa0498 : word) = Some W_9ee64.
Proof. vm_refl. Qed.
Lemma D_9ee64 : decode_any W_9ee64 = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9ee68 : bv 32 := 0x00000593.
Lemma F_9ee68 : fetch_word Ubsan.M.loaded_segments (0xa049c : word) = Some W_9ee68.
Proof. vm_refl. Qed.
Lemma D_9ee68 : decode_any W_9ee68 = Some (OpImm ALU_ADD 11 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9ee6c : bv 32 := 0x00000613.
Lemma F_9ee6c : fetch_word Ubsan.M.loaded_segments (0xa04a0 : word) = Some W_9ee6c.
Proof. vm_refl. Qed.
Lemma D_9ee6c : decode_any W_9ee6c = Some (OpImm ALU_ADD 12 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9ee70 : bv 32 := 0x000680e7.
Lemma F_9ee70 : fetch_word Ubsan.M.loaded_segments (0xa04a4 : word) = Some W_9ee70.
Proof. vm_refl. Qed.
Lemma D_9ee70 : decode_any W_9ee70 = Some (Jalr 1 13 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9ee74 : bv 32 := 0x00843503.
Lemma F_9ee74 : fetch_word Ubsan.M.loaded_segments (0xa04a8 : word) = Some W_9ee74.
Proof. vm_refl. Qed.
Lemma D_9ee74 : decode_any W_9ee74 = Some (Load SZ8 true 10 8 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9ee78 : bv 32 := 0x01043583.
Lemma F_9ee78 : fetch_word Ubsan.M.loaded_segments (0xa04ac : word) = Some W_9ee78.
Proof. vm_refl. Qed.
Lemma D_9ee78 : decode_any W_9ee78 = Some (Load SZ8 true 11 8 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9ee7c : bv 32 := 0x00b50c63.
Lemma F_9ee7c : fetch_word Ubsan.M.loaded_segments (0xa04b0 : word) = Some W_9ee7c.
Proof. vm_refl. Qed.
Lemma D_9ee7c : decode_any W_9ee7c = Some (Branch BC_EQ 10 11 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9ee94 : bv 32 := 0x00018517.
Lemma F_9ee94 : fetch_word Ubsan.M.loaded_segments (0xa04c8 : word) = Some W_9ee94.
Proof. vm_refl. Qed.
Lemma D_9ee94 : decode_any W_9ee94 = Some (Auipc 10 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9ee98 : bv 32 := 0xf2053403.
Lemma F_9ee98 : fetch_word Ubsan.M.loaded_segments (0xa04cc : word) = Some W_9ee98.
Proof. vm_refl. Qed.
Lemma D_9ee98 : decode_any W_9ee98 = Some (Load SZ8 true 8 10 3872, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9ee9c : bv 32 := 0x0a040e63.
Lemma F_9ee9c : fetch_word Ubsan.M.loaded_segments (0xa04d0 : word) = Some W_9ee9c.
Proof. vm_refl. Qed.
Lemma D_9ee9c : decode_any W_9ee9c = Some (Branch BC_EQ 8 0 188, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9eea0 : bv 32 := 0x08c42503.
Lemma F_9eea0 : fetch_word Ubsan.M.loaded_segments (0xa04d4 : word) = Some W_9eea0.
Proof. vm_refl. Qed.
Lemma D_9eea0 : decode_any W_9eea0 = Some (Load SZ4 true 10 8 140, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9eea4 : bv 32 := 0x00054663.
Lemma F_9eea4 : fetch_word Ubsan.M.loaded_segments (0xa04d8 : word) = Some W_9eea4.
Proof. vm_refl. Qed.
Lemma D_9eea4 : decode_any W_9eea4 = Some (Branch BC_LT 10 0 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9eeb0 : bv 32 := 0x02843503.
Lemma F_9eeb0 : fetch_word Ubsan.M.loaded_segments (0xa04e4 : word) = Some W_9eeb0.
Proof. vm_refl. Qed.
Lemma D_9eeb0 : decode_any W_9eeb0 = Some (Load SZ8 true 10 8 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9eeb4 : bv 32 := 0x03843583.
Lemma F_9eeb4 : fetch_word Ubsan.M.loaded_segments (0xa04e8 : word) = Some W_9eeb4.
Proof. vm_refl. Qed.
Lemma D_9eeb4 : decode_any W_9eeb4 = Some (Load SZ8 true 11 8 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9eeb8 : bv 32 := 0x00b50c63.
Lemma F_9eeb8 : fetch_word Ubsan.M.loaded_segments (0xa04ec : word) = Some W_9eeb8.
Proof. vm_refl. Qed.
Lemma D_9eeb8 : decode_any W_9eeb8 = Some (Branch BC_EQ 10 11 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9eed0 : bv 32 := 0x00843503.
Lemma F_9eed0 : fetch_word Ubsan.M.loaded_segments (0xa0504 : word) = Some W_9eed0.
Proof. vm_refl. Qed.
Lemma D_9eed0 : decode_any W_9eed0 = Some (Load SZ8 true 10 8 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9eed4 : bv 32 := 0x01043583.
Lemma F_9eed4 : fetch_word Ubsan.M.loaded_segments (0xa0508 : word) = Some W_9eed4.
Proof. vm_refl. Qed.
Lemma D_9eed4 : decode_any W_9eed4 = Some (Load SZ8 true 11 8 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9eed8 : bv 32 := 0x08b50063.
Lemma F_9eed8 : fetch_word Ubsan.M.loaded_segments (0xa050c : word) = Some W_9eed8.
Proof. vm_refl. Qed.
Lemma D_9eed8 : decode_any W_9eed8 = Some (Branch BC_EQ 10 11 128, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9ef58 : bv 32 := 0x00813083.
Lemma F_9ef58 : fetch_word Ubsan.M.loaded_segments (0xa058c : word) = Some W_9ef58.
Proof. vm_refl. Qed.
Lemma D_9ef58 : decode_any W_9ef58 = Some (Load SZ8 true 1 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9ef5c : bv 32 := 0x00013403.
Lemma F_9ef5c : fetch_word Ubsan.M.loaded_segments (0xa0590 : word) = Some W_9ef5c.
Proof. vm_refl. Qed.
Lemma D_9ef5c : decode_any W_9ef5c = Some (Load SZ8 true 8 2 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9ef60 : bv 32 := 0x01010113.
Lemma F_9ef60 : fetch_word Ubsan.M.loaded_segments (0xa0594 : word) = Some W_9ef60.
Proof. vm_refl. Qed.
Lemma D_9ef60 : decode_any W_9ef60 = Some (OpImm ALU_ADD 2 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9ef64 : bv 32 := 0x00008067.
Lemma F_9ef64 : fetch_word Ubsan.M.loaded_segments (0xa0598 : word) = Some W_9ef64.
Proof. vm_refl. Qed.
Lemma D_9ef64 : decode_any W_9ef64 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.
