(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require BvWfKernel.
(* [comment removed for export] *)
From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.jsoncons.fuzz_ubjson_encoder.images Require Import AsanUbsan.
Open Scope bv_scope.

Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

(* [comment removed for export] *)
Definition W_7bcdc : bv 32 := 0xfff48693.
Lemma F_7bcdc : fetch_word AsanUbsan.M.loaded_segments (0x7bd2c : word) = Some W_7bcdc.
Proof. vm_refl. Qed.
Lemma D_7bcdc : decode_any W_7bcdc = Some (OpImm ALU_ADD 13 9 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7bce0 : bv 32 := 0x00d4b733.
Lemma F_7bce0 : fetch_word AsanUbsan.M.loaded_segments (0x7bd30 : word) = Some W_7bce0.
Proof. vm_refl. Qed.
Lemma D_7bce0 : decode_any W_7bce0 = Some (Op ALU_SLTU 14 9 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7bce4 : bv 32 := 0xfff70713.
Lemma F_7bce4 : fetch_word AsanUbsan.M.loaded_segments (0x7bd34 : word) = Some W_7bce4.
Proof. vm_refl. Qed.
Lemma D_7bce4 : decode_any W_7bce4 = Some (OpImm ALU_ADD 14 14 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7bce8 : bv 32 := 0x00d77733.
Lemma F_7bce8 : fetch_word AsanUbsan.M.loaded_segments (0x7bd38 : word) = Some W_7bce8.
Proof. vm_refl. Qed.
Lemma D_7bce8 : decode_any W_7bce8 = Some (Op ALU_AND 14 14 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7bcec : bv 32 := 0x1ca77c63.
Lemma F_7bcec : fetch_word AsanUbsan.M.loaded_segments (0x7bd3c : word) = Some W_7bcec.
Proof. vm_refl. Qed.
Lemma D_7bcec : decode_any W_7bcec = Some (Branch BC_GEU 14 10 472, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7bcf0 : bv 32 := 0x000c2797.
Lemma F_7bcf0 : fetch_word AsanUbsan.M.loaded_segments (0x7bd40 : word) = Some W_7bcf0.
Proof. vm_refl. Qed.
Lemma D_7bcf0 : decode_any W_7bcf0 = Some (Auipc 15 194, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7bcf4 : bv 32 := 0xb907b783.
Lemma F_7bcf4 : fetch_word AsanUbsan.M.loaded_segments (0x7bd44 : word) = Some W_7bcf4.
Proof. vm_refl. Qed.
Lemma D_7bcf4 : decode_any W_7bcf4 = Some (Load SZ8 true 15 15 2960, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7bcf8 : bv 32 := 0x000c2817.
Lemma F_7bcf8 : fetch_word AsanUbsan.M.loaded_segments (0x7bd48 : word) = Some W_7bcf8.
Proof. vm_refl. Qed.
Lemma D_7bcf8 : decode_any W_7bcf8 = Some (Auipc 16 194, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7bcfc : bv 32 := 0xb9083803.
Lemma F_7bcfc : fetch_word AsanUbsan.M.loaded_segments (0x7bd4c : word) = Some W_7bcfc.
Proof. vm_refl. Qed.
Lemma D_7bcfc : decode_any W_7bcfc = Some (Load SZ8 true 16 16 2960, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7bd00 : bv 32 := 0x0007b883.
Lemma F_7bd00 : fetch_word AsanUbsan.M.loaded_segments (0x7bd50 : word) = Some W_7bd00.
Proof. vm_refl. Qed.
Lemma D_7bd00 : decode_any W_7bd00 = Some (Load SZ8 true 17 15 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7bd04 : bv 32 := 0x00083783.
Lemma F_7bd04 : fetch_word AsanUbsan.M.loaded_segments (0x7bd54 : word) = Some W_7bd04.
Proof. vm_refl. Qed.
Lemma D_7bd04 : decode_any W_7bd04 = Some (Load SZ8 true 15 16 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7bd08 : bv 32 := 0xfff88813.
Lemma F_7bd08 : fetch_word AsanUbsan.M.loaded_segments (0x7bd58 : word) = Some W_7bd08.
Proof. vm_refl. Qed.
Lemma D_7bd08 : decode_any W_7bd08 = Some (OpImm ALU_ADD 16 17 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7bd0c : bv 32 := 0x00a87463.
Lemma F_7bd0c : fetch_word AsanUbsan.M.loaded_segments (0x7bd5c : word) = Some W_7bd0c.
Proof. vm_refl. Qed.
Lemma D_7bd0c : decode_any W_7bd0c = Some (Branch BC_GEU 16 10 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7bd10 : bv 32 := 0x1aa7fa63.
Lemma F_7bd10 : fetch_word AsanUbsan.M.loaded_segments (0x7bd60 : word) = Some W_7bd10.
Proof. vm_refl. Qed.
Lemma D_7bd10 : decode_any W_7bd10 = Some (Branch BC_GEU 15 10 436, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7bd14 : bv 32 := 0x000c2297.
Lemma F_7bd14 : fetch_word AsanUbsan.M.loaded_segments (0x7bd64 : word) = Some W_7bd14.
Proof. vm_refl. Qed.
Lemma D_7bd14 : decode_any W_7bd14 = Some (Auipc 5 194, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7bd18 : bv 32 := 0xb7c2b283.
Lemma F_7bd18 : fetch_word AsanUbsan.M.loaded_segments (0x7bd68 : word) = Some W_7bd18.
Proof. vm_refl. Qed.
Lemma D_7bd18 : decode_any W_7bd18 = Some (Load SZ8 true 5 5 2940, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7bd1c : bv 32 := 0x0002be03.
Lemma F_7bd1c : fetch_word AsanUbsan.M.loaded_segments (0x7bd6c : word) = Some W_7bd1c.
Proof. vm_refl. Qed.
Lemma D_7bd1c : decode_any W_7bd1c = Some (Load SZ8 true 28 5 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7bd20 : bv 32 := 0x003e5313.
Lemma F_7bd20 : fetch_word AsanUbsan.M.loaded_segments (0x7bd70 : word) = Some W_7bd20.
Proof. vm_refl. Qed.
Lemma D_7bd20 : decode_any W_7bd20 = Some (ShiftImm ALU_SRL 6 28 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7bd24 : bv 32 := 0x009303b3.
Lemma F_7bd24 : fetch_word AsanUbsan.M.loaded_segments (0x7bd74 : word) = Some W_7bd24.
Proof. vm_refl. Qed.
Lemma D_7bd24 : decode_any W_7bd24 = Some (Op ALU_ADD 7 6 9, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7bd28 : bv 32 := 0x00ae6463.
Lemma F_7bd28 : fetch_word AsanUbsan.M.loaded_segments (0x7bd78 : word) = Some W_7bd28.
Proof. vm_refl. Qed.
Lemma D_7bd28 : decode_any W_7bd28 = Some (Branch BC_LTU 28 10 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7bd2c : bv 32 := 0x0ca3e463.
Lemma F_7bd2c : fetch_word AsanUbsan.M.loaded_segments (0x7bd7c : word) = Some W_7bd2c.
Proof. vm_refl. Qed.
Lemma D_7bd2c : decode_any W_7bd2c = Some (Branch BC_LTU 7 10 200, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7bd30 : bv 32 := 0x000c2e17.
Lemma F_7bd30 : fetch_word AsanUbsan.M.loaded_segments (0x7bd80 : word) = Some W_7bd30.
Proof. vm_refl. Qed.
Lemma D_7bd30 : decode_any W_7bd30 = Some (Auipc 28 194, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7bd34 : bv 32 := 0xb40e3e03.
Lemma F_7bd34 : fetch_word AsanUbsan.M.loaded_segments (0x7bd84 : word) = Some W_7bd34.
Proof. vm_refl. Qed.
Lemma D_7bd34 : decode_any W_7bd34 = Some (Load SZ8 true 28 28 2880, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7bd38 : bv 32 := 0x04ee4e03.
Lemma F_7bd38 : fetch_word AsanUbsan.M.loaded_segments (0x7bd88 : word) = Some W_7bd38.
Proof. vm_refl. Qed.
Lemma D_7bd38 : decode_any W_7bd38 = Some (Load SZ1 false 28 28 78, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7bd3c : bv 32 := 0x3e0e1063.
Lemma F_7bd3c : fetch_word AsanUbsan.M.loaded_segments (0x7bd8c : word) = Some W_7bd3c.
Proof. vm_refl. Qed.
Lemma D_7bd3c : decode_any W_7bd3c = Some (Branch BC_NE 28 0 992, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7bd40 : bv 32 := 0x04088e63.
Lemma F_7bd40 : fetch_word AsanUbsan.M.loaded_segments (0x7bd90 : word) = Some W_7bd40.
Proof. vm_refl. Qed.
Lemma D_7bd40 : decode_any W_7bd40 = Some (Branch BC_EQ 17 0 92, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7bd44 : bv 32 := 0x0038d393.
Lemma F_7bd44 : fetch_word AsanUbsan.M.loaded_segments (0x7bd94 : word) = Some W_7bd44.
Proof. vm_refl. Qed.
Lemma D_7bd44 : decode_any W_7bd44 = Some (ShiftImm ALU_SRL 7 17 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7bd48 : bv 32 := 0x00d383b3.
Lemma F_7bd48 : fetch_word AsanUbsan.M.loaded_segments (0x7bd98 : word) = Some W_7bd48.
Proof. vm_refl. Qed.
Lemma D_7bd48 : decode_any W_7bd48 = Some (Op ALU_ADD 7 7 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7bd4c : bv 32 := 0x06a3fe63.
Lemma F_7bd4c : fetch_word AsanUbsan.M.loaded_segments (0x7bd9c : word) = Some W_7bd4c.
Proof. vm_refl. Qed.
Lemma D_7bd4c : decode_any W_7bd4c = Some (Branch BC_GEU 7 10 124, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7bd50 : bv 32 := 0x00148393.
Lemma F_7bd50 : fetch_word AsanUbsan.M.loaded_segments (0x7bda0 : word) = Some W_7bd50.
Proof. vm_refl. Qed.
Lemma D_7bd50 : decode_any W_7bd50 = Some (OpImm ALU_ADD 7 9 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7bd54 : bv 32 := 0x00a86863.
Lemma F_7bd54 : fetch_word AsanUbsan.M.loaded_segments (0x7bda4 : word) = Some W_7bd54.
Proof. vm_refl. Qed.
Lemma D_7bd54 : decode_any W_7bd54 = Some (Branch BC_LTU 16 10 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7bd58 : bv 32 := 0x0037de13.
Lemma F_7bd58 : fetch_word AsanUbsan.M.loaded_segments (0x7bda8 : word) = Some W_7bd58.
Proof. vm_refl. Qed.
Lemma D_7bd58 : decode_any W_7bd58 = Some (ShiftImm ALU_SRL 28 15 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7bd5c : bv 32 := 0x007e0e33.
Lemma F_7bd5c : fetch_word AsanUbsan.M.loaded_segments (0x7bdac : word) = Some W_7bd5c.
Proof. vm_refl. Qed.
Lemma D_7bd5c : decode_any W_7bd5c = Some (Op ALU_ADD 28 28 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7bd60 : bv 32 := 0x09c57a63.
Lemma F_7bd60 : fetch_word AsanUbsan.M.loaded_segments (0x7bdb0 : word) = Some W_7bd60.
Proof. vm_refl. Qed.
Lemma D_7bd60 : decode_any W_7bd60 = Some (Branch BC_GEU 10 28 148, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7bd64 : bv 32 := 0x00178e13.
Lemma F_7bd64 : fetch_word AsanUbsan.M.loaded_segments (0x7bdb4 : word) = Some W_7bd64.
Proof. vm_refl. Qed.
Lemma D_7bd64 : decode_any W_7bd64 = Some (OpImm ALU_ADD 28 15 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7bd68 : bv 32 := 0x3bc56a63.
Lemma F_7bd68 : fetch_word AsanUbsan.M.loaded_segments (0x7bdb8 : word) = Some W_7bd68.
Proof. vm_refl. Qed.
Lemma D_7bd68 : decode_any W_7bd68 = Some (Branch BC_LTU 10 28 948, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7bd6c : bv 32 := 0x00730333.
Lemma F_7bd6c : fetch_word AsanUbsan.M.loaded_segments (0x7bdbc : word) = Some W_7bd6c.
Proof. vm_refl. Qed.
Lemma D_7bd6c : decode_any W_7bd6c = Some (Op ALU_ADD 6 6 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7bd70 : bv 32 := 0x00335313.
Lemma F_7bd70 : fetch_word AsanUbsan.M.loaded_segments (0x7bdc0 : word) = Some W_7bd70.
Proof. vm_refl. Qed.
Lemma D_7bd70 : decode_any W_7bd70 = Some (ShiftImm ALU_SRL 6 6 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7bd74 : bv 32 := 0x0480006f.
Lemma F_7bd74 : fetch_word AsanUbsan.M.loaded_segments (0x7bdc4 : word) = Some W_7bd74.
Proof. vm_refl. Qed.
Lemma D_7bd74 : decode_any W_7bd74 = Some (Jal 0 72, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7bd78 : bv 32 := 0x03813083.
Lemma F_7bd78 : fetch_word AsanUbsan.M.loaded_segments (0x7bdc8 : word) = Some W_7bd78.
Proof. vm_refl. Qed.
Lemma D_7bd78 : decode_any W_7bd78 = Some (Load SZ8 true 1 2 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7bd7c : bv 32 := 0x03013403.
Lemma F_7bd7c : fetch_word AsanUbsan.M.loaded_segments (0x7bdcc : word) = Some W_7bd7c.
Proof. vm_refl. Qed.
Lemma D_7bd7c : decode_any W_7bd7c = Some (Load SZ8 true 8 2 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7bd80 : bv 32 := 0x02813483.
Lemma F_7bd80 : fetch_word AsanUbsan.M.loaded_segments (0x7bdd0 : word) = Some W_7bd80.
Proof. vm_refl. Qed.
Lemma D_7bd80 : decode_any W_7bd80 = Some (Load SZ8 true 9 2 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7bd84 : bv 32 := 0x02013903.
Lemma F_7bd84 : fetch_word AsanUbsan.M.loaded_segments (0x7bdd4 : word) = Some W_7bd84.
Proof. vm_refl. Qed.
Lemma D_7bd84 : decode_any W_7bd84 = Some (Load SZ8 true 18 2 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7bd88 : bv 32 := 0x01813983.
Lemma F_7bd88 : fetch_word AsanUbsan.M.loaded_segments (0x7bdd8 : word) = Some W_7bd88.
Proof. vm_refl. Qed.
Lemma D_7bd88 : decode_any W_7bd88 = Some (Load SZ8 true 19 2 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7bd8c : bv 32 := 0x01013a03.
Lemma F_7bd8c : fetch_word AsanUbsan.M.loaded_segments (0x7bddc : word) = Some W_7bd8c.
Proof. vm_refl. Qed.
Lemma D_7bd8c : decode_any W_7bd8c = Some (Load SZ8 true 20 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7bd90 : bv 32 := 0x00813a83.
Lemma F_7bd90 : fetch_word AsanUbsan.M.loaded_segments (0x7bde0 : word) = Some W_7bd90.
Proof. vm_refl. Qed.
Lemma D_7bd90 : decode_any W_7bd90 = Some (Load SZ8 true 21 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7bd94 : bv 32 := 0x04010113.
Lemma F_7bd94 : fetch_word AsanUbsan.M.loaded_segments (0x7bde4 : word) = Some W_7bd94.
Proof. vm_refl. Qed.
Lemma D_7bd94 : decode_any W_7bd94 = Some (OpImm ALU_ADD 2 2 64, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7bd98 : bv 32 := 0x00008067.
Lemma F_7bd98 : fetch_word AsanUbsan.M.loaded_segments (0x7bde8 : word) = Some W_7bd98.
Proof. vm_refl. Qed.
Lemma D_7bd98 : decode_any W_7bd98 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7bd9c : bv 32 := 0x04048463.
Lemma F_7bd9c : fetch_word AsanUbsan.M.loaded_segments (0x7bdec : word) = Some W_7bd9c.
Proof. vm_refl. Qed.
Lemma D_7bd9c : decode_any W_7bd9c = Some (Branch BC_EQ 9 0 72, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7bda0 : bv 32 := 0x0036d313.
Lemma F_7bda0 : fetch_word AsanUbsan.M.loaded_segments (0x7bdf0 : word) = Some W_7bda0.
Proof. vm_refl. Qed.
Lemma D_7bda0 : decode_any W_7bda0 = Some (ShiftImm ALU_SRL 6 13 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7bda4 : bv 32 := 0x00930333.
Lemma F_7bda4 : fetch_word AsanUbsan.M.loaded_segments (0x7bdf4 : word) = Some W_7bda4.
Proof. vm_refl. Qed.
Lemma D_7bda4 : decode_any W_7bda4 = Some (Op ALU_ADD 6 6 9, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7bda8 : bv 32 := 0x00030663.
Lemma F_7bda8 : fetch_word AsanUbsan.M.loaded_segments (0x7bdf8 : word) = Some W_7bda8.
Proof. vm_refl. Qed.
Lemma D_7bda8 : decode_any W_7bda8 = Some (Branch BC_EQ 6 0 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7bdac : bv 32 := 0x00130313.
Lemma F_7bdac : fetch_word AsanUbsan.M.loaded_segments (0x7bdfc : word) = Some W_7bdac.
Proof. vm_refl. Qed.
Lemma D_7bdac : decode_any W_7bdac = Some (OpImm ALU_ADD 6 6 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7bdb0 : bv 32 := 0x36656663.
Lemma F_7bdb0 : fetch_word AsanUbsan.M.loaded_segments (0x7be00 : word) = Some W_7bdb0.
Proof. vm_refl. Qed.
Lemma D_7bdb0 : decode_any W_7bdb0 = Some (Branch BC_LTU 10 6 876, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7bdb4 : bv 32 := 0x00138393.
Lemma F_7bdb4 : fetch_word AsanUbsan.M.loaded_segments (0x7be04 : word) = Some W_7bdb4.
Proof. vm_refl. Qed.
Lemma D_7bdb4 : decode_any W_7bdb4 = Some (OpImm ALU_ADD 7 7 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7bdb8 : bv 32 := 0x0033d313.
Lemma F_7bdb8 : fetch_word AsanUbsan.M.loaded_segments (0x7be08 : word) = Some W_7bdb8.
Proof. vm_refl. Qed.
Lemma D_7bdb8 : decode_any W_7bdb8 = Some (ShiftImm ALU_SRL 6 7 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7bdbc : bv 32 := 0x00d30333.
Lemma F_7bdbc : fetch_word AsanUbsan.M.loaded_segments (0x7be0c : word) = Some W_7bdbc.
Proof. vm_refl. Qed.
Lemma D_7bdbc : decode_any W_7bdbc = Some (Op ALU_ADD 6 6 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7bdc0 : bv 32 := 0x02a37a63.
Lemma F_7bdc0 : fetch_word AsanUbsan.M.loaded_segments (0x7be10 : word) = Some W_7bdc0.
Proof. vm_refl. Qed.
Lemma D_7bdc0 : decode_any W_7bdc0 = Some (Branch BC_GEU 6 10 52, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7bdc4 : bv 32 := 0x3580006f.
Lemma F_7bdc4 : fetch_word AsanUbsan.M.loaded_segments (0x7be14 : word) = Some W_7bdc4.
Proof. vm_refl. Qed.
Lemma D_7bdc4 : decode_any W_7bdc4 = Some (Jal 0 856, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7bdc8 : bv 32 := 0x02048663.
Lemma F_7bdc8 : fetch_word AsanUbsan.M.loaded_segments (0x7be18 : word) = Some W_7bdc8.
Proof. vm_refl. Qed.
Lemma D_7bdc8 : decode_any W_7bdc8 = Some (Branch BC_EQ 9 0 44, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7bdcc : bv 32 := 0x0036d313.
Lemma F_7bdcc : fetch_word AsanUbsan.M.loaded_segments (0x7be1c : word) = Some W_7bdcc.
Proof. vm_refl. Qed.
Lemma D_7bdcc : decode_any W_7bdcc = Some (ShiftImm ALU_SRL 6 13 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7bdd0 : bv 32 := 0x00930333.
Lemma F_7bdd0 : fetch_word AsanUbsan.M.loaded_segments (0x7be20 : word) = Some W_7bdd0.
Proof. vm_refl. Qed.
Lemma D_7bdd0 : decode_any W_7bdd0 = Some (Op ALU_ADD 6 6 9, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7bdd4 : bv 32 := 0x02030063.
Lemma F_7bdd4 : fetch_word AsanUbsan.M.loaded_segments (0x7be24 : word) = Some W_7bdd4.
Proof. vm_refl. Qed.
Lemma D_7bdd4 : decode_any W_7bdd4 = Some (Branch BC_EQ 6 0 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7bdd8 : bv 32 := 0x00130313.
Lemma F_7bdd8 : fetch_word AsanUbsan.M.loaded_segments (0x7be28 : word) = Some W_7bdd8.
Proof. vm_refl. Qed.
Lemma D_7bdd8 : decode_any W_7bdd8 = Some (OpImm ALU_ADD 6 6 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7bddc : bv 32 := 0x00657c63.
Lemma F_7bddc : fetch_word AsanUbsan.M.loaded_segments (0x7be2c : word) = Some W_7bddc.
Proof. vm_refl. Qed.
Lemma D_7bddc : decode_any W_7bddc = Some (Branch BC_GEU 10 6 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7bde0 : bv 32 := 0x33c0006f.
Lemma F_7bde0 : fetch_word AsanUbsan.M.loaded_segments (0x7be30 : word) = Some W_7bde0.
Proof. vm_refl. Qed.
Lemma D_7bde0 : decode_any W_7bde0 = Some (Jal 0 828, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7bde4 : bv 32 := 0x00130313.
Lemma F_7bde4 : fetch_word AsanUbsan.M.loaded_segments (0x7be34 : word) = Some W_7bde4.
Proof. vm_refl. Qed.
Lemma D_7bde4 : decode_any W_7bde4 = Some (OpImm ALU_ADD 6 6 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7bde8 : bv 32 := 0x00335313.
Lemma F_7bde8 : fetch_word AsanUbsan.M.loaded_segments (0x7be38 : word) = Some W_7bde8.
Proof. vm_refl. Qed.
Lemma D_7bde8 : decode_any W_7bde8 = Some (ShiftImm ALU_SRL 6 6 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7bdec : bv 32 := 0xfff30313.
Lemma F_7bdec : fetch_word AsanUbsan.M.loaded_segments (0x7be3c : word) = Some W_7bdec.
Proof. vm_refl. Qed.
Lemma D_7bdec : decode_any W_7bdec = Some (OpImm ALU_ADD 6 6 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7bdf0 : bv 32 := 0x32a36663.
Lemma F_7bdf0 : fetch_word AsanUbsan.M.loaded_segments (0x7be40 : word) = Some W_7bdf0.
Proof. vm_refl. Qed.
Lemma D_7bdf0 : decode_any W_7bdf0 = Some (Branch BC_LTU 6 10 812, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7bdf4 : bv 32 := 0x0002b383.
Lemma F_7bdf4 : fetch_word AsanUbsan.M.loaded_segments (0x7be44 : word) = Some W_7bdf4.
Proof. vm_refl. Qed.
Lemma D_7bdf4 : decode_any W_7bdf4 = Some (Load SZ8 true 7 5 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7bdf8 : bv 32 := 0x0033d293.
Lemma F_7bdf8 : fetch_word AsanUbsan.M.loaded_segments (0x7be48 : word) = Some W_7bdf8.
Proof. vm_refl. Qed.
Lemma D_7bdf8 : decode_any W_7bdf8 = Some (ShiftImm ALU_SRL 5 7 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7bdfc : bv 32 := 0x00928333.
Lemma F_7bdfc : fetch_word AsanUbsan.M.loaded_segments (0x7be4c : word) = Some W_7bdfc.
Proof. vm_refl. Qed.
Lemma D_7bdfc : decode_any W_7bdfc = Some (Op ALU_ADD 6 5 9, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7be00 : bv 32 := 0x00a3e463.
Lemma F_7be00 : fetch_word AsanUbsan.M.loaded_segments (0x7be50 : word) = Some W_7be00.
Proof. vm_refl. Qed.
Lemma D_7be00 : decode_any W_7be00 = Some (Branch BC_LTU 7 10 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7be04 : bv 32 := 0x0ca36063.
Lemma F_7be04 : fetch_word AsanUbsan.M.loaded_segments (0x7be54 : word) = Some W_7be04.
Proof. vm_refl. Qed.
Lemma D_7be04 : decode_any W_7be04 = Some (Branch BC_LTU 6 10 192, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7be08 : bv 32 := 0x000c2397.
Lemma F_7be08 : fetch_word AsanUbsan.M.loaded_segments (0x7be58 : word) = Some W_7be08.
Proof. vm_refl. Qed.
Lemma D_7be08 : decode_any W_7be08 = Some (Auipc 7 194, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7be0c : bv 32 := 0xa683b383.
Lemma F_7be0c : fetch_word AsanUbsan.M.loaded_segments (0x7be5c : word) = Some W_7be0c.
Proof. vm_refl. Qed.
Lemma D_7be0c : decode_any W_7be0c = Some (Load SZ8 true 7 7 2664, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7be10 : bv 32 := 0x04e3c383.
Lemma F_7be10 : fetch_word AsanUbsan.M.loaded_segments (0x7be60 : word) = Some W_7be10.
Proof. vm_refl. Qed.
Lemma D_7be10 : decode_any W_7be10 = Some (Load SZ1 false 7 7 78, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7be14 : bv 32 := 0x08039063.
Lemma F_7be14 : fetch_word AsanUbsan.M.loaded_segments (0x7be64 : word) = Some W_7be14.
Proof. vm_refl. Qed.
Lemma D_7be14 : decode_any W_7be14 = Some (Branch BC_NE 7 0 128, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7be18 : bv 32 := 0x02088c63.
Lemma F_7be18 : fetch_word AsanUbsan.M.loaded_segments (0x7be68 : word) = Some W_7be18.
Proof. vm_refl. Qed.
Lemma D_7be18 : decode_any W_7be18 = Some (Branch BC_EQ 17 0 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7be1c : bv 32 := 0x0038d893.
Lemma F_7be1c : fetch_word AsanUbsan.M.loaded_segments (0x7be6c : word) = Some W_7be1c.
Proof. vm_refl. Qed.
Lemma D_7be1c : decode_any W_7be1c = Some (ShiftImm ALU_SRL 17 17 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7be20 : bv 32 := 0x00d888b3.
Lemma F_7be20 : fetch_word AsanUbsan.M.loaded_segments (0x7be70 : word) = Some W_7be20.
Proof. vm_refl. Qed.
Lemma D_7be20 : decode_any W_7be20 = Some (Op ALU_ADD 17 17 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7be24 : bv 32 := 0x04a8fc63.
Lemma F_7be24 : fetch_word AsanUbsan.M.loaded_segments (0x7be74 : word) = Some W_7be24.
Proof. vm_refl. Qed.
Lemma D_7be24 : decode_any W_7be24 = Some (Branch BC_GEU 17 10 88, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7be28 : bv 32 := 0x00148893.
Lemma F_7be28 : fetch_word AsanUbsan.M.loaded_segments (0x7be78 : word) = Some W_7be28.
Proof. vm_refl. Qed.
Lemma D_7be28 : decode_any W_7be28 = Some (OpImm ALU_ADD 17 9 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7be2c : bv 32 := 0x00a86863.
Lemma F_7be2c : fetch_word AsanUbsan.M.loaded_segments (0x7be7c : word) = Some W_7be2c.
Proof. vm_refl. Qed.
Lemma D_7be2c : decode_any W_7be2c = Some (Branch BC_LTU 16 10 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7be30 : bv 32 := 0x0037d813.
Lemma F_7be30 : fetch_word AsanUbsan.M.loaded_segments (0x7be80 : word) = Some W_7be30.
Proof. vm_refl. Qed.
Lemma D_7be30 : decode_any W_7be30 = Some (ShiftImm ALU_SRL 16 15 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7be34 : bv 32 := 0x01180833.
Lemma F_7be34 : fetch_word AsanUbsan.M.loaded_segments (0x7be84 : word) = Some W_7be34.
Proof. vm_refl. Qed.
Lemma D_7be34 : decode_any W_7be34 = Some (Op ALU_ADD 16 16 17, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7be38 : bv 32 := 0x09057663.
Lemma F_7be38 : fetch_word AsanUbsan.M.loaded_segments (0x7be88 : word) = Some W_7be38.
Proof. vm_refl. Qed.
Lemma D_7be38 : decode_any W_7be38 = Some (Branch BC_GEU 10 16 140, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7be3c : bv 32 := 0x00178793.
Lemma F_7be3c : fetch_word AsanUbsan.M.loaded_segments (0x7be8c : word) = Some W_7be3c.
Proof. vm_refl. Qed.
Lemma D_7be3c : decode_any W_7be3c = Some (OpImm ALU_ADD 15 15 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7be40 : bv 32 := 0x04f56a63.
Lemma F_7be40 : fetch_word AsanUbsan.M.loaded_segments (0x7be90 : word) = Some W_7be40.
Proof. vm_refl. Qed.
Lemma D_7be40 : decode_any W_7be40 = Some (Branch BC_LTU 10 15 84, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7be44 : bv 32 := 0x011288b3.
Lemma F_7be44 : fetch_word AsanUbsan.M.loaded_segments (0x7be94 : word) = Some W_7be44.
Proof. vm_refl. Qed.
Lemma D_7be44 : decode_any W_7be44 = Some (Op ALU_ADD 17 5 17, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7be48 : bv 32 := 0x0038d793.
Lemma F_7be48 : fetch_word AsanUbsan.M.loaded_segments (0x7be98 : word) = Some W_7be48.
Proof. vm_refl. Qed.
Lemma D_7be48 : decode_any W_7be48 = Some (ShiftImm ALU_SRL 15 17 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7be4c : bv 32 := 0x0240006f.
Lemma F_7be4c : fetch_word AsanUbsan.M.loaded_segments (0x7be9c : word) = Some W_7be4c.
Proof. vm_refl. Qed.
Lemma D_7be4c : decode_any W_7be4c = Some (Jal 0 36, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7be50 : bv 32 := 0x06048263.
Lemma F_7be50 : fetch_word AsanUbsan.M.loaded_segments (0x7bea0 : word) = Some W_7be50.
Proof. vm_refl. Qed.
Lemma D_7be50 : decode_any W_7be50 = Some (Branch BC_EQ 9 0 100, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7be54 : bv 32 := 0x0036d793.
Lemma F_7be54 : fetch_word AsanUbsan.M.loaded_segments (0x7bea4 : word) = Some W_7be54.
Proof. vm_refl. Qed.
Lemma D_7be54 : decode_any W_7be54 = Some (ShiftImm ALU_SRL 15 13 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7be58 : bv 32 := 0x009787b3.
Lemma F_7be58 : fetch_word AsanUbsan.M.loaded_segments (0x7bea8 : word) = Some W_7be58.
Proof. vm_refl. Qed.
Lemma D_7be58 : decode_any W_7be58 = Some (Op ALU_ADD 15 15 9, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7be5c : bv 32 := 0x00078663.
Lemma F_7be5c : fetch_word AsanUbsan.M.loaded_segments (0x7beac : word) = Some W_7be5c.
Proof. vm_refl. Qed.
Lemma D_7be5c : decode_any W_7be5c = Some (Branch BC_EQ 15 0 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7be60 : bv 32 := 0x00178793.
Lemma F_7be60 : fetch_word AsanUbsan.M.loaded_segments (0x7beb0 : word) = Some W_7be60.
Proof. vm_refl. Qed.
Lemma D_7be60 : decode_any W_7be60 = Some (OpImm ALU_ADD 15 15 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7be64 : bv 32 := 0x02f56863.
Lemma F_7be64 : fetch_word AsanUbsan.M.loaded_segments (0x7beb4 : word) = Some W_7be64.
Proof. vm_refl. Qed.
Lemma D_7be64 : decode_any W_7be64 = Some (Branch BC_LTU 10 15 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7be68 : bv 32 := 0x00130313.
Lemma F_7be68 : fetch_word AsanUbsan.M.loaded_segments (0x7beb8 : word) = Some W_7be68.
Proof. vm_refl. Qed.
Lemma D_7be68 : decode_any W_7be68 = Some (OpImm ALU_ADD 6 6 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7be6c : bv 32 := 0x00335793.
Lemma F_7be6c : fetch_word AsanUbsan.M.loaded_segments (0x7bebc : word) = Some W_7be6c.
Proof. vm_refl. Qed.
Lemma D_7be6c : decode_any W_7be6c = Some (ShiftImm ALU_SRL 15 6 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7be70 : bv 32 := 0x00d787b3.
Lemma F_7be70 : fetch_word AsanUbsan.M.loaded_segments (0x7bec0 : word) = Some W_7be70.
Proof. vm_refl. Qed.
Lemma D_7be70 : decode_any W_7be70 = Some (Op ALU_ADD 15 15 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7be74 : bv 32 := 0x04a7f863.
Lemma F_7be74 : fetch_word AsanUbsan.M.loaded_segments (0x7bec4 : word) = Some W_7be74.
Proof. vm_refl. Qed.
Lemma D_7be74 : decode_any W_7be74 = Some (Branch BC_GEU 15 10 80, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7be78 : bv 32 := 0x01c0006f.
Lemma F_7be78 : fetch_word AsanUbsan.M.loaded_segments (0x7bec8 : word) = Some W_7be78.
Proof. vm_refl. Qed.
Lemma D_7be78 : decode_any W_7be78 = Some (Jal 0 28, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7be7c : bv 32 := 0x04048463.
Lemma F_7be7c : fetch_word AsanUbsan.M.loaded_segments (0x7becc : word) = Some W_7be7c.
Proof. vm_refl. Qed.
Lemma D_7be7c : decode_any W_7be7c = Some (Branch BC_EQ 9 0 72, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7be80 : bv 32 := 0x0036d793.
Lemma F_7be80 : fetch_word AsanUbsan.M.loaded_segments (0x7bed0 : word) = Some W_7be80.
Proof. vm_refl. Qed.
Lemma D_7be80 : decode_any W_7be80 = Some (ShiftImm ALU_SRL 15 13 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7be84 : bv 32 := 0x009787b3.
Lemma F_7be84 : fetch_word AsanUbsan.M.loaded_segments (0x7bed4 : word) = Some W_7be84.
Proof. vm_refl. Qed.
Lemma D_7be84 : decode_any W_7be84 = Some (Op ALU_ADD 15 15 9, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7be88 : bv 32 := 0x02078e63.
Lemma F_7be88 : fetch_word AsanUbsan.M.loaded_segments (0x7bed8 : word) = Some W_7be88.
Proof. vm_refl. Qed.
Lemma D_7be88 : decode_any W_7be88 = Some (Branch BC_EQ 15 0 60, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7be8c : bv 32 := 0x00178793.
Lemma F_7be8c : fetch_word AsanUbsan.M.loaded_segments (0x7bedc : word) = Some W_7be8c.
Proof. vm_refl. Qed.
Lemma D_7be8c : decode_any W_7be8c = Some (OpImm ALU_ADD 15 15 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7be90 : bv 32 := 0x02f57a63.
Lemma F_7be90 : fetch_word AsanUbsan.M.loaded_segments (0x7bee0 : word) = Some W_7be90.
Proof. vm_refl. Qed.
Lemma D_7be90 : decode_any W_7be90 = Some (Branch BC_GEU 10 15 52, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7be94 : bv 32 := 0xfffa5517.
Lemma F_7be94 : fetch_word AsanUbsan.M.loaded_segments (0x7bee4 : word) = Some W_7be94.
Proof. vm_refl. Qed.
Lemma D_7be94 : decode_any W_7be94 = Some (Auipc 10 1048485, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7be98 : bv 32 := 0xfff9d597.
Lemma F_7be98 : fetch_word AsanUbsan.M.loaded_segments (0x7bee8 : word) = Some W_7be98.
Proof. vm_refl. Qed.
Lemma D_7be98 : decode_any W_7be98 = Some (Auipc 11 1048477, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7be9c : bv 32 := 0x51150513.
Lemma F_7be9c : fetch_word AsanUbsan.M.loaded_segments (0x7beec : word) = Some W_7be9c.
Proof. vm_refl. Qed.
Lemma D_7be9c : decode_any W_7be9c = Some (OpImm ALU_ADD 10 10 1297, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7bea0 : bv 32 := 0xb7c58613.
Lemma F_7bea0 : fetch_word AsanUbsan.M.loaded_segments (0x7bef0 : word) = Some W_7bea0.
Proof. vm_refl. Qed.
Lemma D_7bea0 : decode_any W_7bea0 = Some (OpImm ALU_ADD 12 11 2940, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7bea4 : bv 32 := 0x02f00593.
Lemma F_7bea4 : fetch_word AsanUbsan.M.loaded_segments (0x7bef4 : word) = Some W_7bea4.
Proof. vm_refl. Qed.
Lemma D_7bea4 : decode_any W_7bea4 = Some (OpImm ALU_ADD 11 0 47, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7bea8 : bv 32 := 0x00000693.
Lemma F_7bea8 : fetch_word AsanUbsan.M.loaded_segments (0x7bef8 : word) = Some W_7bea8.
Proof. vm_refl. Qed.
Lemma D_7bea8 : decode_any W_7bea8 = Some (OpImm ALU_ADD 13 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7beac : bv 32 := 0x00000713.
Lemma F_7beac : fetch_word AsanUbsan.M.loaded_segments (0x7befc : word) = Some W_7beac.
Proof. vm_refl. Qed.
Lemma D_7beac : decode_any W_7beac = Some (OpImm ALU_ADD 14 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7beb0 : bv 32 := 0x430180ef.
Lemma F_7beb0 : fetch_word AsanUbsan.M.loaded_segments (0x7bf00 : word) = Some W_7beb0.
Proof. vm_refl. Qed.
Lemma D_7beb0 : decode_any W_7beb0 = Some (Jal 1 99376, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7beb4 : bv 32 := 0x00128293.
Lemma F_7beb4 : fetch_word AsanUbsan.M.loaded_segments (0x7bf04 : word) = Some W_7beb4.
Proof. vm_refl. Qed.
Lemma D_7beb4 : decode_any W_7beb4 = Some (OpImm ALU_ADD 5 5 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7beb8 : bv 32 := 0x0032d793.
Lemma F_7beb8 : fetch_word AsanUbsan.M.loaded_segments (0x7bf08 : word) = Some W_7beb8.
Proof. vm_refl. Qed.
Lemma D_7beb8 : decode_any W_7beb8 = Some (ShiftImm ALU_SRL 15 5 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7bebc : bv 32 := 0xfff78793.
Lemma F_7bebc : fetch_word AsanUbsan.M.loaded_segments (0x7bf0c : word) = Some W_7bebc.
Proof. vm_refl. Qed.
Lemma D_7bebc : decode_any W_7bebc = Some (OpImm ALU_ADD 15 15 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7bec0 : bv 32 := 0xfca7eae3.
Lemma F_7bec0 : fetch_word AsanUbsan.M.loaded_segments (0x7bf10 : word) = Some W_7bec0.
Proof. vm_refl. Qed.
Lemma D_7bec0 : decode_any W_7bec0 = Some (Branch BC_LTU 15 10 8148, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7bec4 : bv 32 := 0x0075f793.
Lemma F_7bec4 : fetch_word AsanUbsan.M.loaded_segments (0x7bf14 : word) = Some W_7bec4.
Proof. vm_refl. Qed.
Lemma D_7bec4 : decode_any W_7bec4 = Some (OpImm ALU_AND 15 11 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7bec8 : bv 32 := 0x26079a63.
Lemma F_7bec8 : fetch_word AsanUbsan.M.loaded_segments (0x7bf18 : word) = Some W_7bec8.
Proof. vm_refl. Qed.
Lemma D_7bec8 : decode_any W_7bec8 = Some (Branch BC_NE 15 0 628, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7becc : bv 32 := 0x00b505b3.
Lemma F_7becc : fetch_word AsanUbsan.M.loaded_segments (0x7bf1c : word) = Some W_7becc.
Proof. vm_refl. Qed.
Lemma D_7becc : decode_any W_7becc = Some (Op ALU_ADD 11 10 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7bed0 : bv 32 := 0xff858593.
Lemma F_7bed0 : fetch_word AsanUbsan.M.loaded_segments (0x7bf20 : word) = Some W_7bed0.
Proof. vm_refl. Qed.
Lemma D_7bed0 : decode_any W_7bed0 = Some (OpImm ALU_ADD 11 11 4088, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7bed4 : bv 32 := 0x04b77263.
Lemma F_7bed4 : fetch_word AsanUbsan.M.loaded_segments (0x7bf24 : word) = Some W_7bed4.
Proof. vm_refl. Qed.
Lemma D_7bed4 : decode_any W_7bed4 = Some (Branch BC_GEU 14 11 68, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7bed8 : bv 32 := 0x000c2717.
Lemma F_7bed8 : fetch_word AsanUbsan.M.loaded_segments (0x7bf28 : word) = Some W_7bed8.
Proof. vm_refl. Qed.
Lemma D_7bed8 : decode_any W_7bed8 = Some (Auipc 14 194, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7bedc : bv 32 := 0x9a873703.
Lemma F_7bedc : fetch_word AsanUbsan.M.loaded_segments (0x7bf2c : word) = Some W_7bedc.
Proof. vm_refl. Qed.
Lemma D_7bedc : decode_any W_7bedc = Some (Load SZ8 true 14 14 2472, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7bee0 : bv 32 := 0x000c2797.
Lemma F_7bee0 : fetch_word AsanUbsan.M.loaded_segments (0x7bf30 : word) = Some W_7bee0.
Proof. vm_refl. Qed.
Lemma D_7bee0 : decode_any W_7bee0 = Some (Auipc 15 194, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7bee4 : bv 32 := 0x9a87b783.
Lemma F_7bee4 : fetch_word AsanUbsan.M.loaded_segments (0x7bf34 : word) = Some W_7bee4.
Proof. vm_refl. Qed.
Lemma D_7bee4 : decode_any W_7bee4 = Some (Load SZ8 true 15 15 2472, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7bee8 : bv 32 := 0x00073883.
Lemma F_7bee8 : fetch_word AsanUbsan.M.loaded_segments (0x7bf38 : word) = Some W_7bee8.
Proof. vm_refl. Qed.
Lemma D_7bee8 : decode_any W_7bee8 = Some (Load SZ8 true 17 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7beec : bv 32 := 0x0007b703.
Lemma F_7beec : fetch_word AsanUbsan.M.loaded_segments (0x7bf3c : word) = Some W_7beec.
Proof. vm_refl. Qed.
Lemma D_7beec : decode_any W_7beec = Some (Load SZ8 true 14 15 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7bef0 : bv 32 := 0xfff88813.
Lemma F_7bef0 : fetch_word AsanUbsan.M.loaded_segments (0x7bf40 : word) = Some W_7bef0.
Proof. vm_refl. Qed.
Lemma D_7bef0 : decode_any W_7bef0 = Some (OpImm ALU_ADD 16 17 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7bef4 : bv 32 := 0x00b87463.
Lemma F_7bef4 : fetch_word AsanUbsan.M.loaded_segments (0x7bf44 : word) = Some W_7bef4.
Proof. vm_refl. Qed.
Lemma D_7bef4 : decode_any W_7bef4 = Some (Branch BC_GEU 16 11 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7bef8 : bv 32 := 0x02b77063.
Lemma F_7bef8 : fetch_word AsanUbsan.M.loaded_segments (0x7bf48 : word) = Some W_7bef8.
Proof. vm_refl. Qed.
Lemma D_7bef8 : decode_any W_7bef8 = Some (Branch BC_GEU 14 11 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7befc : bv 32 := 0x000c2797.
Lemma F_7befc : fetch_word AsanUbsan.M.loaded_segments (0x7bf4c : word) = Some W_7befc.
Proof. vm_refl. Qed.
Lemma D_7befc : decode_any W_7befc = Some (Auipc 15 194, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7bf00 : bv 32 := 0x9947b783.
Lemma F_7bf00 : fetch_word AsanUbsan.M.loaded_segments (0x7bf50 : word) = Some W_7bf00.
Proof. vm_refl. Qed.
Lemma D_7bf00 : decode_any W_7bf00 = Some (Load SZ8 true 15 15 2452, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7bf04 : bv 32 := 0x0007b303.
Lemma F_7bf04 : fetch_word AsanUbsan.M.loaded_segments (0x7bf54 : word) = Some W_7bf04.
Proof. vm_refl. Qed.
Lemma D_7bf04 : decode_any W_7bf04 = Some (Load SZ8 true 6 15 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7bf08 : bv 32 := 0x00335793.
Lemma F_7bf08 : fetch_word AsanUbsan.M.loaded_segments (0x7bf58 : word) = Some W_7bf08.
Proof. vm_refl. Qed.
Lemma D_7bf08 : decode_any W_7bf08 = Some (ShiftImm ALU_SRL 15 6 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7bf0c : bv 32 := 0x009782b3.
Lemma F_7bf0c : fetch_word AsanUbsan.M.loaded_segments (0x7bf5c : word) = Some W_7bf0c.
Proof. vm_refl. Qed.
Lemma D_7bf0c : decode_any W_7bf0c = Some (Op ALU_ADD 5 15 9, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7bf10 : bv 32 := 0x12b36263.
Lemma F_7bf10 : fetch_word AsanUbsan.M.loaded_segments (0x7bf60 : word) = Some W_7bf10.
Proof. vm_refl. Qed.
Lemma D_7bf10 : decode_any W_7bf10 = Some (Branch BC_LTU 6 11 292, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7bf14 : bv 32 := 0x12b2f063.
Lemma F_7bf14 : fetch_word AsanUbsan.M.loaded_segments (0x7bf64 : word) = Some W_7bf14.
Proof. vm_refl. Qed.
Lemma D_7bf14 : decode_any W_7bf14 = Some (Branch BC_GEU 5 11 288, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_7bf18 : bv 32 := 0x000c2697.
Lemma F_7bf18 : fetch_word AsanUbsan.M.loaded_segments (0x7bf68 : word) = Some W_7bf18.
Proof. vm_refl. Qed.
Lemma D_7bf18 : decode_any W_7bf18 = Some (Auipc 13 194, 4%Z).
Proof. vm_refl. Qed.
