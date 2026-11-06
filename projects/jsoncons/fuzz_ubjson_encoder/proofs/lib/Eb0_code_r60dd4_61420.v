(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
(* [comment removed for export] *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require BvWfKernel.

From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.jsoncons.fuzz_ubjson_encoder.images Require Import AsanUbsan.
Open Scope bv_scope.

Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

Definition W_7bc80 : bv 32 := 0x000ca517.
Lemma F_7bc80 : fetch_word AsanUbsan.M.loaded_segments (0x7bcd0 : word) = Some W_7bc80.
Proof. vm_refl. Qed.
Lemma D_7bc80 : decode_any W_7bc80 = Some (Auipc 10 202, 4%Z).
Proof. vm_refl. Qed.

Definition W_7bc84 : bv 32 := 0xc8c50503.
Lemma F_7bc84 : fetch_word AsanUbsan.M.loaded_segments (0x7bcd4 : word) = Some W_7bc84.
Proof. vm_refl. Qed.
Lemma D_7bc84 : decode_any W_7bc84 = Some (Load SZ1 true 10 10 3212, 4%Z).
Proof. vm_refl. Qed.

Definition W_7bc88 : bv 32 := 0x0230000f.
Lemma F_7bc88 : fetch_word AsanUbsan.M.loaded_segments (0x7bcd8 : word) = Some W_7bc88.
Proof. vm_refl. Qed.
Lemma D_7bc88 : decode_any W_7bc88 = Some (Fence 0 2 3 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7bc8c : bv 32 := 0x00a03533.
Lemma F_7bc8c : fetch_word AsanUbsan.M.loaded_segments (0x7bcdc : word) = Some W_7bc8c.
Proof. vm_refl. Qed.
Lemma D_7bc8c : decode_any W_7bc8c = Some (Op ALU_SLTU 10 0 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_7bc90 : bv 32 := 0x00008067.
Lemma F_7bc90 : fetch_word AsanUbsan.M.loaded_segments (0x7bce0 : word) = Some W_7bc90.
Proof. vm_refl. Qed.
Lemma D_7bc90 : decode_any W_7bc90 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7bc94 : bv 32 := 0xfc010113.
Lemma F_7bc94 : fetch_word AsanUbsan.M.loaded_segments (0x7bce4 : word) = Some W_7bc94.
Proof. vm_refl. Qed.
Lemma D_7bc94 : decode_any W_7bc94 = Some (OpImm ALU_ADD 2 2 4032, 4%Z).
Proof. vm_refl. Qed.

Definition W_7bc98 : bv 32 := 0x02113c23.
Lemma F_7bc98 : fetch_word AsanUbsan.M.loaded_segments (0x7bce8 : word) = Some W_7bc98.
Proof. vm_refl. Qed.
Lemma D_7bc98 : decode_any W_7bc98 = Some (Store SZ8 2 1 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_7bc9c : bv 32 := 0x02813823.
Lemma F_7bc9c : fetch_word AsanUbsan.M.loaded_segments (0x7bcec : word) = Some W_7bc9c.
Proof. vm_refl. Qed.
Lemma D_7bc9c : decode_any W_7bc9c = Some (Store SZ8 2 8 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_7bca0 : bv 32 := 0x02913423.
Lemma F_7bca0 : fetch_word AsanUbsan.M.loaded_segments (0x7bcf0 : word) = Some W_7bca0.
Proof. vm_refl. Qed.
Lemma D_7bca0 : decode_any W_7bca0 = Some (Store SZ8 2 9 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_7bca4 : bv 32 := 0x03213023.
Lemma F_7bca4 : fetch_word AsanUbsan.M.loaded_segments (0x7bcf4 : word) = Some W_7bca4.
Proof. vm_refl. Qed.
Lemma D_7bca4 : decode_any W_7bca4 = Some (Store SZ8 2 18 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_7bca8 : bv 32 := 0x01313c23.
Lemma F_7bca8 : fetch_word AsanUbsan.M.loaded_segments (0x7bcf8 : word) = Some W_7bca8.
Proof. vm_refl. Qed.
Lemma D_7bca8 : decode_any W_7bca8 = Some (Store SZ8 2 19 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_7bcac : bv 32 := 0x01413823.
Lemma F_7bcac : fetch_word AsanUbsan.M.loaded_segments (0x7bcfc : word) = Some W_7bcac.
Proof. vm_refl. Qed.
Lemma D_7bcac : decode_any W_7bcac = Some (Store SZ8 2 20 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_7bcb0 : bv 32 := 0x01513423.
Lemma F_7bcb0 : fetch_word AsanUbsan.M.loaded_segments (0x7bd00 : word) = Some W_7bcb0.
Proof. vm_refl. Qed.
Lemma D_7bcb0 : decode_any W_7bcb0 = Some (Store SZ8 2 21 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_7bcb4 : bv 32 := 0x00060a63.
Lemma F_7bcb4 : fetch_word AsanUbsan.M.loaded_segments (0x7bd04 : word) = Some W_7bcb4.
Proof. vm_refl. Qed.
Lemma D_7bcb4 : decode_any W_7bcb4 = Some (Branch BC_EQ 12 0 20, 4%Z).
Proof. vm_refl. Qed.

Definition W_7bcb8 : bv 32 := 0x000ca697.
Lemma F_7bcb8 : fetch_word AsanUbsan.M.loaded_segments (0x7bd08 : word) = Some W_7bcb8.
Proof. vm_refl. Qed.
Lemma D_7bcb8 : decode_any W_7bcb8 = Some (Auipc 13 202, 4%Z).
Proof. vm_refl. Qed.

Definition W_7bcbc : bv 32 := 0xc5468683.
Lemma F_7bcbc : fetch_word AsanUbsan.M.loaded_segments (0x7bd0c : word) = Some W_7bcbc.
Proof. vm_refl. Qed.
Lemma D_7bcbc : decode_any W_7bcbc = Some (Load SZ1 true 13 13 3156, 4%Z).
Proof. vm_refl. Qed.

Definition W_7bcc0 : bv 32 := 0x0230000f.
Lemma F_7bcc0 : fetch_word AsanUbsan.M.loaded_segments (0x7bd10 : word) = Some W_7bcc0.
Proof. vm_refl. Qed.
Lemma D_7bcc0 : decode_any W_7bcc0 = Some (Fence 0 2 3 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7bcc4 : bv 32 := 0x0a068a63.
Lemma F_7bcc4 : fetch_word AsanUbsan.M.loaded_segments (0x7bd14 : word) = Some W_7bcc4.
Proof. vm_refl. Qed.
Lemma D_7bcc4 : decode_any W_7bcc4 = Some (Branch BC_EQ 13 0 180, 4%Z).
Proof. vm_refl. Qed.

Definition W_7bcc8 : bv 32 := 0x00757693.
Lemma F_7bcc8 : fetch_word AsanUbsan.M.loaded_segments (0x7bd18 : word) = Some W_7bcc8.
Proof. vm_refl. Qed.
Lemma D_7bcc8 : decode_any W_7bcc8 = Some (OpImm ALU_AND 13 10 7, 4%Z).
Proof. vm_refl. Qed.

Definition W_7bccc : bv 32 := 0x42069863.
Lemma F_7bccc : fetch_word AsanUbsan.M.loaded_segments (0x7bd1c : word) = Some W_7bccc.
Proof. vm_refl. Qed.
Lemma D_7bccc : decode_any W_7bccc = Some (Branch BC_NE 13 0 1072, 4%Z).
Proof. vm_refl. Qed.

Definition W_7bcd0 : bv 32 := 0x000c2697.
Lemma F_7bcd0 : fetch_word AsanUbsan.M.loaded_segments (0x7bd20 : word) = Some W_7bcd0.
Proof. vm_refl. Qed.
Lemma D_7bcd0 : decode_any W_7bcd0 = Some (Auipc 13 194, 4%Z).
Proof. vm_refl. Qed.

Definition W_7bcd4 : bv 32 := 0xba86b683.
Lemma F_7bcd4 : fetch_word AsanUbsan.M.loaded_segments (0x7bd24 : word) = Some W_7bcd4.
Proof. vm_refl. Qed.
Lemma D_7bcd4 : decode_any W_7bcd4 = Some (Load SZ8 true 13 13 2984, 4%Z).
Proof. vm_refl. Qed.

Definition W_7bcd8 : bv 32 := 0x0006b483.
Lemma F_7bcd8 : fetch_word AsanUbsan.M.loaded_segments (0x7bd28 : word) = Some W_7bcd8.
Proof. vm_refl. Qed.
Lemma D_7bcd8 : decode_any W_7bcd8 = Some (Load SZ8 true 9 13 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7bcdc : bv 32 := 0xfff48693.
Lemma F_7bcdc : fetch_word AsanUbsan.M.loaded_segments (0x7bd2c : word) = Some W_7bcdc.
Proof. vm_refl. Qed.
Lemma D_7bcdc : decode_any W_7bcdc = Some (OpImm ALU_ADD 13 9 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_7bce0 : bv 32 := 0x00d4b733.
Lemma F_7bce0 : fetch_word AsanUbsan.M.loaded_segments (0x7bd30 : word) = Some W_7bce0.
Proof. vm_refl. Qed.
Lemma D_7bce0 : decode_any W_7bce0 = Some (Op ALU_SLTU 14 9 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_7bce4 : bv 32 := 0xfff70713.
Lemma F_7bce4 : fetch_word AsanUbsan.M.loaded_segments (0x7bd34 : word) = Some W_7bce4.
Proof. vm_refl. Qed.
Lemma D_7bce4 : decode_any W_7bce4 = Some (OpImm ALU_ADD 14 14 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_7bce8 : bv 32 := 0x00d77733.
Lemma F_7bce8 : fetch_word AsanUbsan.M.loaded_segments (0x7bd38 : word) = Some W_7bce8.
Proof. vm_refl. Qed.
Lemma D_7bce8 : decode_any W_7bce8 = Some (Op ALU_AND 14 14 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_7bcec : bv 32 := 0x1ca77c63.
Lemma F_7bcec : fetch_word AsanUbsan.M.loaded_segments (0x7bd3c : word) = Some W_7bcec.
Proof. vm_refl. Qed.
Lemma D_7bcec : decode_any W_7bcec = Some (Branch BC_GEU 14 10 472, 4%Z).
Proof. vm_refl. Qed.

Definition W_7bcf0 : bv 32 := 0x000c2797.
Lemma F_7bcf0 : fetch_word AsanUbsan.M.loaded_segments (0x7bd40 : word) = Some W_7bcf0.
Proof. vm_refl. Qed.
Lemma D_7bcf0 : decode_any W_7bcf0 = Some (Auipc 15 194, 4%Z).
Proof. vm_refl. Qed.

Definition W_7bcf4 : bv 32 := 0xb907b783.
Lemma F_7bcf4 : fetch_word AsanUbsan.M.loaded_segments (0x7bd44 : word) = Some W_7bcf4.
Proof. vm_refl. Qed.
Lemma D_7bcf4 : decode_any W_7bcf4 = Some (Load SZ8 true 15 15 2960, 4%Z).
Proof. vm_refl. Qed.

Definition W_7bcf8 : bv 32 := 0x000c2817.
Lemma F_7bcf8 : fetch_word AsanUbsan.M.loaded_segments (0x7bd48 : word) = Some W_7bcf8.
Proof. vm_refl. Qed.
Lemma D_7bcf8 : decode_any W_7bcf8 = Some (Auipc 16 194, 4%Z).
Proof. vm_refl. Qed.

Definition W_7bcfc : bv 32 := 0xb9083803.
Lemma F_7bcfc : fetch_word AsanUbsan.M.loaded_segments (0x7bd4c : word) = Some W_7bcfc.
Proof. vm_refl. Qed.
Lemma D_7bcfc : decode_any W_7bcfc = Some (Load SZ8 true 16 16 2960, 4%Z).
Proof. vm_refl. Qed.

Definition W_7bd00 : bv 32 := 0x0007b883.
Lemma F_7bd00 : fetch_word AsanUbsan.M.loaded_segments (0x7bd50 : word) = Some W_7bd00.
Proof. vm_refl. Qed.
Lemma D_7bd00 : decode_any W_7bd00 = Some (Load SZ8 true 17 15 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7bd04 : bv 32 := 0x00083783.
Lemma F_7bd04 : fetch_word AsanUbsan.M.loaded_segments (0x7bd54 : word) = Some W_7bd04.
Proof. vm_refl. Qed.
Lemma D_7bd04 : decode_any W_7bd04 = Some (Load SZ8 true 15 16 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7bd08 : bv 32 := 0xfff88813.
Lemma F_7bd08 : fetch_word AsanUbsan.M.loaded_segments (0x7bd58 : word) = Some W_7bd08.
Proof. vm_refl. Qed.
Lemma D_7bd08 : decode_any W_7bd08 = Some (OpImm ALU_ADD 16 17 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_7bd0c : bv 32 := 0x00a87463.
Lemma F_7bd0c : fetch_word AsanUbsan.M.loaded_segments (0x7bd5c : word) = Some W_7bd0c.
Proof. vm_refl. Qed.
Lemma D_7bd0c : decode_any W_7bd0c = Some (Branch BC_GEU 16 10 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_7bd10 : bv 32 := 0x1aa7fa63.
Lemma F_7bd10 : fetch_word AsanUbsan.M.loaded_segments (0x7bd60 : word) = Some W_7bd10.
Proof. vm_refl. Qed.
Lemma D_7bd10 : decode_any W_7bd10 = Some (Branch BC_GEU 15 10 436, 4%Z).
Proof. vm_refl. Qed.

Definition W_7bd14 : bv 32 := 0x000c2297.
Lemma F_7bd14 : fetch_word AsanUbsan.M.loaded_segments (0x7bd64 : word) = Some W_7bd14.
Proof. vm_refl. Qed.
Lemma D_7bd14 : decode_any W_7bd14 = Some (Auipc 5 194, 4%Z).
Proof. vm_refl. Qed.

Definition W_7bd18 : bv 32 := 0xb7c2b283.
Lemma F_7bd18 : fetch_word AsanUbsan.M.loaded_segments (0x7bd68 : word) = Some W_7bd18.
Proof. vm_refl. Qed.
Lemma D_7bd18 : decode_any W_7bd18 = Some (Load SZ8 true 5 5 2940, 4%Z).
Proof. vm_refl. Qed.

Definition W_7bd1c : bv 32 := 0x0002be03.
Lemma F_7bd1c : fetch_word AsanUbsan.M.loaded_segments (0x7bd6c : word) = Some W_7bd1c.
Proof. vm_refl. Qed.
Lemma D_7bd1c : decode_any W_7bd1c = Some (Load SZ8 true 28 5 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7bd20 : bv 32 := 0x003e5313.
Lemma F_7bd20 : fetch_word AsanUbsan.M.loaded_segments (0x7bd70 : word) = Some W_7bd20.
Proof. vm_refl. Qed.
Lemma D_7bd20 : decode_any W_7bd20 = Some (ShiftImm ALU_SRL 6 28 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_7bd24 : bv 32 := 0x009303b3.
Lemma F_7bd24 : fetch_word AsanUbsan.M.loaded_segments (0x7bd74 : word) = Some W_7bd24.
Proof. vm_refl. Qed.
Lemma D_7bd24 : decode_any W_7bd24 = Some (Op ALU_ADD 7 6 9, 4%Z).
Proof. vm_refl. Qed.

Definition W_7bd28 : bv 32 := 0x00ae6463.
Lemma F_7bd28 : fetch_word AsanUbsan.M.loaded_segments (0x7bd78 : word) = Some W_7bd28.
Proof. vm_refl. Qed.
Lemma D_7bd28 : decode_any W_7bd28 = Some (Branch BC_LTU 28 10 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_7bd2c : bv 32 := 0x0ca3e463.
Lemma F_7bd2c : fetch_word AsanUbsan.M.loaded_segments (0x7bd7c : word) = Some W_7bd2c.
Proof. vm_refl. Qed.
Lemma D_7bd2c : decode_any W_7bd2c = Some (Branch BC_LTU 7 10 200, 4%Z).
Proof. vm_refl. Qed.

Definition W_7bd30 : bv 32 := 0x000c2e17.
Lemma F_7bd30 : fetch_word AsanUbsan.M.loaded_segments (0x7bd80 : word) = Some W_7bd30.
Proof. vm_refl. Qed.
Lemma D_7bd30 : decode_any W_7bd30 = Some (Auipc 28 194, 4%Z).
Proof. vm_refl. Qed.

Definition W_7bd34 : bv 32 := 0xb40e3e03.
Lemma F_7bd34 : fetch_word AsanUbsan.M.loaded_segments (0x7bd84 : word) = Some W_7bd34.
Proof. vm_refl. Qed.
Lemma D_7bd34 : decode_any W_7bd34 = Some (Load SZ8 true 28 28 2880, 4%Z).
Proof. vm_refl. Qed.

Definition W_7bd38 : bv 32 := 0x04ee4e03.
Lemma F_7bd38 : fetch_word AsanUbsan.M.loaded_segments (0x7bd88 : word) = Some W_7bd38.
Proof. vm_refl. Qed.
Lemma D_7bd38 : decode_any W_7bd38 = Some (Load SZ1 false 28 28 78, 4%Z).
Proof. vm_refl. Qed.

Definition W_7bd3c : bv 32 := 0x3e0e1063.
Lemma F_7bd3c : fetch_word AsanUbsan.M.loaded_segments (0x7bd8c : word) = Some W_7bd3c.
Proof. vm_refl. Qed.
Lemma D_7bd3c : decode_any W_7bd3c = Some (Branch BC_NE 28 0 992, 4%Z).
Proof. vm_refl. Qed.

Definition W_7bd40 : bv 32 := 0x04088e63.
Lemma F_7bd40 : fetch_word AsanUbsan.M.loaded_segments (0x7bd90 : word) = Some W_7bd40.
Proof. vm_refl. Qed.
Lemma D_7bd40 : decode_any W_7bd40 = Some (Branch BC_EQ 17 0 92, 4%Z).
Proof. vm_refl. Qed.

Definition W_7bd44 : bv 32 := 0x0038d393.
Lemma F_7bd44 : fetch_word AsanUbsan.M.loaded_segments (0x7bd94 : word) = Some W_7bd44.
Proof. vm_refl. Qed.
Lemma D_7bd44 : decode_any W_7bd44 = Some (ShiftImm ALU_SRL 7 17 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_7bd48 : bv 32 := 0x00d383b3.
Lemma F_7bd48 : fetch_word AsanUbsan.M.loaded_segments (0x7bd98 : word) = Some W_7bd48.
Proof. vm_refl. Qed.
Lemma D_7bd48 : decode_any W_7bd48 = Some (Op ALU_ADD 7 7 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_7bd4c : bv 32 := 0x06a3fe63.
Lemma F_7bd4c : fetch_word AsanUbsan.M.loaded_segments (0x7bd9c : word) = Some W_7bd4c.
Proof. vm_refl. Qed.
Lemma D_7bd4c : decode_any W_7bd4c = Some (Branch BC_GEU 7 10 124, 4%Z).
Proof. vm_refl. Qed.

Definition W_7bd50 : bv 32 := 0x00148393.
Lemma F_7bd50 : fetch_word AsanUbsan.M.loaded_segments (0x7bda0 : word) = Some W_7bd50.
Proof. vm_refl. Qed.
Lemma D_7bd50 : decode_any W_7bd50 = Some (OpImm ALU_ADD 7 9 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_7bd54 : bv 32 := 0x00a86863.
Lemma F_7bd54 : fetch_word AsanUbsan.M.loaded_segments (0x7bda4 : word) = Some W_7bd54.
Proof. vm_refl. Qed.
Lemma D_7bd54 : decode_any W_7bd54 = Some (Branch BC_LTU 16 10 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_7bd58 : bv 32 := 0x0037de13.
Lemma F_7bd58 : fetch_word AsanUbsan.M.loaded_segments (0x7bda8 : word) = Some W_7bd58.
Proof. vm_refl. Qed.
Lemma D_7bd58 : decode_any W_7bd58 = Some (ShiftImm ALU_SRL 28 15 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_7bd5c : bv 32 := 0x007e0e33.
Lemma F_7bd5c : fetch_word AsanUbsan.M.loaded_segments (0x7bdac : word) = Some W_7bd5c.
Proof. vm_refl. Qed.
Lemma D_7bd5c : decode_any W_7bd5c = Some (Op ALU_ADD 28 28 7, 4%Z).
Proof. vm_refl. Qed.

Definition W_7bd60 : bv 32 := 0x09c57a63.
Lemma F_7bd60 : fetch_word AsanUbsan.M.loaded_segments (0x7bdb0 : word) = Some W_7bd60.
Proof. vm_refl. Qed.
Lemma D_7bd60 : decode_any W_7bd60 = Some (Branch BC_GEU 10 28 148, 4%Z).
Proof. vm_refl. Qed.

Definition W_7bd64 : bv 32 := 0x00178e13.
Lemma F_7bd64 : fetch_word AsanUbsan.M.loaded_segments (0x7bdb4 : word) = Some W_7bd64.
Proof. vm_refl. Qed.
Lemma D_7bd64 : decode_any W_7bd64 = Some (OpImm ALU_ADD 28 15 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_7bd68 : bv 32 := 0x3bc56a63.
Lemma F_7bd68 : fetch_word AsanUbsan.M.loaded_segments (0x7bdb8 : word) = Some W_7bd68.
Proof. vm_refl. Qed.
Lemma D_7bd68 : decode_any W_7bd68 = Some (Branch BC_LTU 10 28 948, 4%Z).
Proof. vm_refl. Qed.

Definition W_7bd6c : bv 32 := 0x00730333.
Lemma F_7bd6c : fetch_word AsanUbsan.M.loaded_segments (0x7bdbc : word) = Some W_7bd6c.
Proof. vm_refl. Qed.
Lemma D_7bd6c : decode_any W_7bd6c = Some (Op ALU_ADD 6 6 7, 4%Z).
Proof. vm_refl. Qed.

Definition W_7bd70 : bv 32 := 0x00335313.
Lemma F_7bd70 : fetch_word AsanUbsan.M.loaded_segments (0x7bdc0 : word) = Some W_7bd70.
Proof. vm_refl. Qed.
Lemma D_7bd70 : decode_any W_7bd70 = Some (ShiftImm ALU_SRL 6 6 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_7bd74 : bv 32 := 0x0480006f.
Lemma F_7bd74 : fetch_word AsanUbsan.M.loaded_segments (0x7bdc4 : word) = Some W_7bd74.
Proof. vm_refl. Qed.
Lemma D_7bd74 : decode_any W_7bd74 = Some (Jal 0 72, 4%Z).
Proof. vm_refl. Qed.

Definition W_7bd78 : bv 32 := 0x03813083.
Lemma F_7bd78 : fetch_word AsanUbsan.M.loaded_segments (0x7bdc8 : word) = Some W_7bd78.
Proof. vm_refl. Qed.
Lemma D_7bd78 : decode_any W_7bd78 = Some (Load SZ8 true 1 2 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_7bd7c : bv 32 := 0x03013403.
Lemma F_7bd7c : fetch_word AsanUbsan.M.loaded_segments (0x7bdcc : word) = Some W_7bd7c.
Proof. vm_refl. Qed.
Lemma D_7bd7c : decode_any W_7bd7c = Some (Load SZ8 true 8 2 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_7bd80 : bv 32 := 0x02813483.
Lemma F_7bd80 : fetch_word AsanUbsan.M.loaded_segments (0x7bdd0 : word) = Some W_7bd80.
Proof. vm_refl. Qed.
Lemma D_7bd80 : decode_any W_7bd80 = Some (Load SZ8 true 9 2 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_7bd84 : bv 32 := 0x02013903.
Lemma F_7bd84 : fetch_word AsanUbsan.M.loaded_segments (0x7bdd4 : word) = Some W_7bd84.
Proof. vm_refl. Qed.
Lemma D_7bd84 : decode_any W_7bd84 = Some (Load SZ8 true 18 2 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_7bd88 : bv 32 := 0x01813983.
Lemma F_7bd88 : fetch_word AsanUbsan.M.loaded_segments (0x7bdd8 : word) = Some W_7bd88.
Proof. vm_refl. Qed.
Lemma D_7bd88 : decode_any W_7bd88 = Some (Load SZ8 true 19 2 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_7bd8c : bv 32 := 0x01013a03.
Lemma F_7bd8c : fetch_word AsanUbsan.M.loaded_segments (0x7bddc : word) = Some W_7bd8c.
Proof. vm_refl. Qed.
Lemma D_7bd8c : decode_any W_7bd8c = Some (Load SZ8 true 20 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_7bd90 : bv 32 := 0x00813a83.
Lemma F_7bd90 : fetch_word AsanUbsan.M.loaded_segments (0x7bde0 : word) = Some W_7bd90.
Proof. vm_refl. Qed.
Lemma D_7bd90 : decode_any W_7bd90 = Some (Load SZ8 true 21 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_7bd94 : bv 32 := 0x04010113.
Lemma F_7bd94 : fetch_word AsanUbsan.M.loaded_segments (0x7bde4 : word) = Some W_7bd94.
Proof. vm_refl. Qed.
Lemma D_7bd94 : decode_any W_7bd94 = Some (OpImm ALU_ADD 2 2 64, 4%Z).
Proof. vm_refl. Qed.

Definition W_7bd98 : bv 32 := 0x00008067.
Lemma F_7bd98 : fetch_word AsanUbsan.M.loaded_segments (0x7bde8 : word) = Some W_7bd98.
Proof. vm_refl. Qed.
Lemma D_7bd98 : decode_any W_7bd98 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7bd9c : bv 32 := 0x04048463.
Lemma F_7bd9c : fetch_word AsanUbsan.M.loaded_segments (0x7bdec : word) = Some W_7bd9c.
Proof. vm_refl. Qed.
Lemma D_7bd9c : decode_any W_7bd9c = Some (Branch BC_EQ 9 0 72, 4%Z).
Proof. vm_refl. Qed.

Definition W_7bda0 : bv 32 := 0x0036d313.
Lemma F_7bda0 : fetch_word AsanUbsan.M.loaded_segments (0x7bdf0 : word) = Some W_7bda0.
Proof. vm_refl. Qed.
Lemma D_7bda0 : decode_any W_7bda0 = Some (ShiftImm ALU_SRL 6 13 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_7bda4 : bv 32 := 0x00930333.
Lemma F_7bda4 : fetch_word AsanUbsan.M.loaded_segments (0x7bdf4 : word) = Some W_7bda4.
Proof. vm_refl. Qed.
Lemma D_7bda4 : decode_any W_7bda4 = Some (Op ALU_ADD 6 6 9, 4%Z).
Proof. vm_refl. Qed.

Definition W_7bda8 : bv 32 := 0x00030663.
Lemma F_7bda8 : fetch_word AsanUbsan.M.loaded_segments (0x7bdf8 : word) = Some W_7bda8.
Proof. vm_refl. Qed.
Lemma D_7bda8 : decode_any W_7bda8 = Some (Branch BC_EQ 6 0 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_7bdac : bv 32 := 0x00130313.
Lemma F_7bdac : fetch_word AsanUbsan.M.loaded_segments (0x7bdfc : word) = Some W_7bdac.
Proof. vm_refl. Qed.
Lemma D_7bdac : decode_any W_7bdac = Some (OpImm ALU_ADD 6 6 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_7bdb0 : bv 32 := 0x36656663.
Lemma F_7bdb0 : fetch_word AsanUbsan.M.loaded_segments (0x7be00 : word) = Some W_7bdb0.
Proof. vm_refl. Qed.
Lemma D_7bdb0 : decode_any W_7bdb0 = Some (Branch BC_LTU 10 6 876, 4%Z).
Proof. vm_refl. Qed.

Definition W_7bdb4 : bv 32 := 0x00138393.
Lemma F_7bdb4 : fetch_word AsanUbsan.M.loaded_segments (0x7be04 : word) = Some W_7bdb4.
Proof. vm_refl. Qed.
Lemma D_7bdb4 : decode_any W_7bdb4 = Some (OpImm ALU_ADD 7 7 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_7bdb8 : bv 32 := 0x0033d313.
Lemma F_7bdb8 : fetch_word AsanUbsan.M.loaded_segments (0x7be08 : word) = Some W_7bdb8.
Proof. vm_refl. Qed.
Lemma D_7bdb8 : decode_any W_7bdb8 = Some (ShiftImm ALU_SRL 6 7 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_7bdbc : bv 32 := 0x00d30333.
Lemma F_7bdbc : fetch_word AsanUbsan.M.loaded_segments (0x7be0c : word) = Some W_7bdbc.
Proof. vm_refl. Qed.
Lemma D_7bdbc : decode_any W_7bdbc = Some (Op ALU_ADD 6 6 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_7bdc0 : bv 32 := 0x02a37a63.
Lemma F_7bdc0 : fetch_word AsanUbsan.M.loaded_segments (0x7be10 : word) = Some W_7bdc0.
Proof. vm_refl. Qed.
Lemma D_7bdc0 : decode_any W_7bdc0 = Some (Branch BC_GEU 6 10 52, 4%Z).
Proof. vm_refl. Qed.

Definition W_7bdc4 : bv 32 := 0x3580006f.
Lemma F_7bdc4 : fetch_word AsanUbsan.M.loaded_segments (0x7be14 : word) = Some W_7bdc4.
Proof. vm_refl. Qed.
Lemma D_7bdc4 : decode_any W_7bdc4 = Some (Jal 0 856, 4%Z).
Proof. vm_refl. Qed.

Definition W_7bdc8 : bv 32 := 0x02048663.
Lemma F_7bdc8 : fetch_word AsanUbsan.M.loaded_segments (0x7be18 : word) = Some W_7bdc8.
Proof. vm_refl. Qed.
Lemma D_7bdc8 : decode_any W_7bdc8 = Some (Branch BC_EQ 9 0 44, 4%Z).
Proof. vm_refl. Qed.

Definition W_7bdcc : bv 32 := 0x0036d313.
Lemma F_7bdcc : fetch_word AsanUbsan.M.loaded_segments (0x7be1c : word) = Some W_7bdcc.
Proof. vm_refl. Qed.
Lemma D_7bdcc : decode_any W_7bdcc = Some (ShiftImm ALU_SRL 6 13 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_7bdd0 : bv 32 := 0x00930333.
Lemma F_7bdd0 : fetch_word AsanUbsan.M.loaded_segments (0x7be20 : word) = Some W_7bdd0.
Proof. vm_refl. Qed.
Lemma D_7bdd0 : decode_any W_7bdd0 = Some (Op ALU_ADD 6 6 9, 4%Z).
Proof. vm_refl. Qed.

Definition W_7bdd4 : bv 32 := 0x02030063.
Lemma F_7bdd4 : fetch_word AsanUbsan.M.loaded_segments (0x7be24 : word) = Some W_7bdd4.
Proof. vm_refl. Qed.
Lemma D_7bdd4 : decode_any W_7bdd4 = Some (Branch BC_EQ 6 0 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_7bdd8 : bv 32 := 0x00130313.
Lemma F_7bdd8 : fetch_word AsanUbsan.M.loaded_segments (0x7be28 : word) = Some W_7bdd8.
Proof. vm_refl. Qed.
Lemma D_7bdd8 : decode_any W_7bdd8 = Some (OpImm ALU_ADD 6 6 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_7bddc : bv 32 := 0x00657c63.
Lemma F_7bddc : fetch_word AsanUbsan.M.loaded_segments (0x7be2c : word) = Some W_7bddc.
Proof. vm_refl. Qed.
Lemma D_7bddc : decode_any W_7bddc = Some (Branch BC_GEU 10 6 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_7bde0 : bv 32 := 0x33c0006f.
Lemma F_7bde0 : fetch_word AsanUbsan.M.loaded_segments (0x7be30 : word) = Some W_7bde0.
Proof. vm_refl. Qed.
Lemma D_7bde0 : decode_any W_7bde0 = Some (Jal 0 828, 4%Z).
Proof. vm_refl. Qed.

Definition W_7bde4 : bv 32 := 0x00130313.
Lemma F_7bde4 : fetch_word AsanUbsan.M.loaded_segments (0x7be34 : word) = Some W_7bde4.
Proof. vm_refl. Qed.
Lemma D_7bde4 : decode_any W_7bde4 = Some (OpImm ALU_ADD 6 6 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_7bde8 : bv 32 := 0x00335313.
Lemma F_7bde8 : fetch_word AsanUbsan.M.loaded_segments (0x7be38 : word) = Some W_7bde8.
Proof. vm_refl. Qed.
Lemma D_7bde8 : decode_any W_7bde8 = Some (ShiftImm ALU_SRL 6 6 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_7bdec : bv 32 := 0xfff30313.
Lemma F_7bdec : fetch_word AsanUbsan.M.loaded_segments (0x7be3c : word) = Some W_7bdec.
Proof. vm_refl. Qed.
Lemma D_7bdec : decode_any W_7bdec = Some (OpImm ALU_ADD 6 6 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_7bdf0 : bv 32 := 0x32a36663.
Lemma F_7bdf0 : fetch_word AsanUbsan.M.loaded_segments (0x7be40 : word) = Some W_7bdf0.
Proof. vm_refl. Qed.
Lemma D_7bdf0 : decode_any W_7bdf0 = Some (Branch BC_LTU 6 10 812, 4%Z).
Proof. vm_refl. Qed.

Definition W_7bdf4 : bv 32 := 0x0002b383.
Lemma F_7bdf4 : fetch_word AsanUbsan.M.loaded_segments (0x7be44 : word) = Some W_7bdf4.
Proof. vm_refl. Qed.
Lemma D_7bdf4 : decode_any W_7bdf4 = Some (Load SZ8 true 7 5 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7bdf8 : bv 32 := 0x0033d293.
Lemma F_7bdf8 : fetch_word AsanUbsan.M.loaded_segments (0x7be48 : word) = Some W_7bdf8.
Proof. vm_refl. Qed.
Lemma D_7bdf8 : decode_any W_7bdf8 = Some (ShiftImm ALU_SRL 5 7 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_7bdfc : bv 32 := 0x00928333.
Lemma F_7bdfc : fetch_word AsanUbsan.M.loaded_segments (0x7be4c : word) = Some W_7bdfc.
Proof. vm_refl. Qed.
Lemma D_7bdfc : decode_any W_7bdfc = Some (Op ALU_ADD 6 5 9, 4%Z).
Proof. vm_refl. Qed.

Definition W_7be00 : bv 32 := 0x00a3e463.
Lemma F_7be00 : fetch_word AsanUbsan.M.loaded_segments (0x7be50 : word) = Some W_7be00.
Proof. vm_refl. Qed.
Lemma D_7be00 : decode_any W_7be00 = Some (Branch BC_LTU 7 10 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_7be04 : bv 32 := 0x0ca36063.
Lemma F_7be04 : fetch_word AsanUbsan.M.loaded_segments (0x7be54 : word) = Some W_7be04.
Proof. vm_refl. Qed.
Lemma D_7be04 : decode_any W_7be04 = Some (Branch BC_LTU 6 10 192, 4%Z).
Proof. vm_refl. Qed.

Definition W_7be08 : bv 32 := 0x000c2397.
Lemma F_7be08 : fetch_word AsanUbsan.M.loaded_segments (0x7be58 : word) = Some W_7be08.
Proof. vm_refl. Qed.
Lemma D_7be08 : decode_any W_7be08 = Some (Auipc 7 194, 4%Z).
Proof. vm_refl. Qed.

Definition W_7be0c : bv 32 := 0xa683b383.
Lemma F_7be0c : fetch_word AsanUbsan.M.loaded_segments (0x7be5c : word) = Some W_7be0c.
Proof. vm_refl. Qed.
Lemma D_7be0c : decode_any W_7be0c = Some (Load SZ8 true 7 7 2664, 4%Z).
Proof. vm_refl. Qed.

Definition W_7be10 : bv 32 := 0x04e3c383.
Lemma F_7be10 : fetch_word AsanUbsan.M.loaded_segments (0x7be60 : word) = Some W_7be10.
Proof. vm_refl. Qed.
Lemma D_7be10 : decode_any W_7be10 = Some (Load SZ1 false 7 7 78, 4%Z).
Proof. vm_refl. Qed.

Definition W_7be14 : bv 32 := 0x08039063.
Lemma F_7be14 : fetch_word AsanUbsan.M.loaded_segments (0x7be64 : word) = Some W_7be14.
Proof. vm_refl. Qed.
Lemma D_7be14 : decode_any W_7be14 = Some (Branch BC_NE 7 0 128, 4%Z).
Proof. vm_refl. Qed.

Definition W_7be18 : bv 32 := 0x02088c63.
Lemma F_7be18 : fetch_word AsanUbsan.M.loaded_segments (0x7be68 : word) = Some W_7be18.
Proof. vm_refl. Qed.
Lemma D_7be18 : decode_any W_7be18 = Some (Branch BC_EQ 17 0 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_7be1c : bv 32 := 0x0038d893.
Lemma F_7be1c : fetch_word AsanUbsan.M.loaded_segments (0x7be6c : word) = Some W_7be1c.
Proof. vm_refl. Qed.
Lemma D_7be1c : decode_any W_7be1c = Some (ShiftImm ALU_SRL 17 17 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_7be20 : bv 32 := 0x00d888b3.
Lemma F_7be20 : fetch_word AsanUbsan.M.loaded_segments (0x7be70 : word) = Some W_7be20.
Proof. vm_refl. Qed.
Lemma D_7be20 : decode_any W_7be20 = Some (Op ALU_ADD 17 17 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_7be24 : bv 32 := 0x04a8fc63.
Lemma F_7be24 : fetch_word AsanUbsan.M.loaded_segments (0x7be74 : word) = Some W_7be24.
Proof. vm_refl. Qed.
Lemma D_7be24 : decode_any W_7be24 = Some (Branch BC_GEU 17 10 88, 4%Z).
Proof. vm_refl. Qed.

Definition W_7be28 : bv 32 := 0x00148893.
Lemma F_7be28 : fetch_word AsanUbsan.M.loaded_segments (0x7be78 : word) = Some W_7be28.
Proof. vm_refl. Qed.
Lemma D_7be28 : decode_any W_7be28 = Some (OpImm ALU_ADD 17 9 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_7be2c : bv 32 := 0x00a86863.
Lemma F_7be2c : fetch_word AsanUbsan.M.loaded_segments (0x7be7c : word) = Some W_7be2c.
Proof. vm_refl. Qed.
Lemma D_7be2c : decode_any W_7be2c = Some (Branch BC_LTU 16 10 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_7be30 : bv 32 := 0x0037d813.
Lemma F_7be30 : fetch_word AsanUbsan.M.loaded_segments (0x7be80 : word) = Some W_7be30.
Proof. vm_refl. Qed.
Lemma D_7be30 : decode_any W_7be30 = Some (ShiftImm ALU_SRL 16 15 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_7be34 : bv 32 := 0x01180833.
Lemma F_7be34 : fetch_word AsanUbsan.M.loaded_segments (0x7be84 : word) = Some W_7be34.
Proof. vm_refl. Qed.
Lemma D_7be34 : decode_any W_7be34 = Some (Op ALU_ADD 16 16 17, 4%Z).
Proof. vm_refl. Qed.

Definition W_7be38 : bv 32 := 0x09057663.
Lemma F_7be38 : fetch_word AsanUbsan.M.loaded_segments (0x7be88 : word) = Some W_7be38.
Proof. vm_refl. Qed.
Lemma D_7be38 : decode_any W_7be38 = Some (Branch BC_GEU 10 16 140, 4%Z).
Proof. vm_refl. Qed.

Definition W_7be3c : bv 32 := 0x00178793.
Lemma F_7be3c : fetch_word AsanUbsan.M.loaded_segments (0x7be8c : word) = Some W_7be3c.
Proof. vm_refl. Qed.
Lemma D_7be3c : decode_any W_7be3c = Some (OpImm ALU_ADD 15 15 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_7be40 : bv 32 := 0x04f56a63.
Lemma F_7be40 : fetch_word AsanUbsan.M.loaded_segments (0x7be90 : word) = Some W_7be40.
Proof. vm_refl. Qed.
Lemma D_7be40 : decode_any W_7be40 = Some (Branch BC_LTU 10 15 84, 4%Z).
Proof. vm_refl. Qed.

Definition W_7be44 : bv 32 := 0x011288b3.
Lemma F_7be44 : fetch_word AsanUbsan.M.loaded_segments (0x7be94 : word) = Some W_7be44.
Proof. vm_refl. Qed.
Lemma D_7be44 : decode_any W_7be44 = Some (Op ALU_ADD 17 5 17, 4%Z).
Proof. vm_refl. Qed.

Definition W_7be48 : bv 32 := 0x0038d793.
Lemma F_7be48 : fetch_word AsanUbsan.M.loaded_segments (0x7be98 : word) = Some W_7be48.
Proof. vm_refl. Qed.
Lemma D_7be48 : decode_any W_7be48 = Some (ShiftImm ALU_SRL 15 17 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_7be4c : bv 32 := 0x0240006f.
Lemma F_7be4c : fetch_word AsanUbsan.M.loaded_segments (0x7be9c : word) = Some W_7be4c.
Proof. vm_refl. Qed.
Lemma D_7be4c : decode_any W_7be4c = Some (Jal 0 36, 4%Z).
Proof. vm_refl. Qed.

Definition W_7be50 : bv 32 := 0x06048263.
Lemma F_7be50 : fetch_word AsanUbsan.M.loaded_segments (0x7bea0 : word) = Some W_7be50.
Proof. vm_refl. Qed.
Lemma D_7be50 : decode_any W_7be50 = Some (Branch BC_EQ 9 0 100, 4%Z).
Proof. vm_refl. Qed.

Definition W_7be54 : bv 32 := 0x0036d793.
Lemma F_7be54 : fetch_word AsanUbsan.M.loaded_segments (0x7bea4 : word) = Some W_7be54.
Proof. vm_refl. Qed.
Lemma D_7be54 : decode_any W_7be54 = Some (ShiftImm ALU_SRL 15 13 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_7be58 : bv 32 := 0x009787b3.
Lemma F_7be58 : fetch_word AsanUbsan.M.loaded_segments (0x7bea8 : word) = Some W_7be58.
Proof. vm_refl. Qed.
Lemma D_7be58 : decode_any W_7be58 = Some (Op ALU_ADD 15 15 9, 4%Z).
Proof. vm_refl. Qed.

Definition W_7be5c : bv 32 := 0x00078663.
Lemma F_7be5c : fetch_word AsanUbsan.M.loaded_segments (0x7beac : word) = Some W_7be5c.
Proof. vm_refl. Qed.
Lemma D_7be5c : decode_any W_7be5c = Some (Branch BC_EQ 15 0 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_7be60 : bv 32 := 0x00178793.
Lemma F_7be60 : fetch_word AsanUbsan.M.loaded_segments (0x7beb0 : word) = Some W_7be60.
Proof. vm_refl. Qed.
Lemma D_7be60 : decode_any W_7be60 = Some (OpImm ALU_ADD 15 15 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_7be64 : bv 32 := 0x02f56863.
Lemma F_7be64 : fetch_word AsanUbsan.M.loaded_segments (0x7beb4 : word) = Some W_7be64.
Proof. vm_refl. Qed.
Lemma D_7be64 : decode_any W_7be64 = Some (Branch BC_LTU 10 15 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_7be68 : bv 32 := 0x00130313.
Lemma F_7be68 : fetch_word AsanUbsan.M.loaded_segments (0x7beb8 : word) = Some W_7be68.
Proof. vm_refl. Qed.
Lemma D_7be68 : decode_any W_7be68 = Some (OpImm ALU_ADD 6 6 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_7be6c : bv 32 := 0x00335793.
Lemma F_7be6c : fetch_word AsanUbsan.M.loaded_segments (0x7bebc : word) = Some W_7be6c.
Proof. vm_refl. Qed.
Lemma D_7be6c : decode_any W_7be6c = Some (ShiftImm ALU_SRL 15 6 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_7be70 : bv 32 := 0x00d787b3.
Lemma F_7be70 : fetch_word AsanUbsan.M.loaded_segments (0x7bec0 : word) = Some W_7be70.
Proof. vm_refl. Qed.
Lemma D_7be70 : decode_any W_7be70 = Some (Op ALU_ADD 15 15 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_7be74 : bv 32 := 0x04a7f863.
Lemma F_7be74 : fetch_word AsanUbsan.M.loaded_segments (0x7bec4 : word) = Some W_7be74.
Proof. vm_refl. Qed.
Lemma D_7be74 : decode_any W_7be74 = Some (Branch BC_GEU 15 10 80, 4%Z).
Proof. vm_refl. Qed.

Definition W_7be78 : bv 32 := 0x01c0006f.
Lemma F_7be78 : fetch_word AsanUbsan.M.loaded_segments (0x7bec8 : word) = Some W_7be78.
Proof. vm_refl. Qed.
Lemma D_7be78 : decode_any W_7be78 = Some (Jal 0 28, 4%Z).
Proof. vm_refl. Qed.

Definition W_7be7c : bv 32 := 0x04048463.
Lemma F_7be7c : fetch_word AsanUbsan.M.loaded_segments (0x7becc : word) = Some W_7be7c.
Proof. vm_refl. Qed.
Lemma D_7be7c : decode_any W_7be7c = Some (Branch BC_EQ 9 0 72, 4%Z).
Proof. vm_refl. Qed.

Definition W_7be80 : bv 32 := 0x0036d793.
Lemma F_7be80 : fetch_word AsanUbsan.M.loaded_segments (0x7bed0 : word) = Some W_7be80.
Proof. vm_refl. Qed.
Lemma D_7be80 : decode_any W_7be80 = Some (ShiftImm ALU_SRL 15 13 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_7be84 : bv 32 := 0x009787b3.
Lemma F_7be84 : fetch_word AsanUbsan.M.loaded_segments (0x7bed4 : word) = Some W_7be84.
Proof. vm_refl. Qed.
Lemma D_7be84 : decode_any W_7be84 = Some (Op ALU_ADD 15 15 9, 4%Z).
Proof. vm_refl. Qed.

Definition W_7be88 : bv 32 := 0x02078e63.
Lemma F_7be88 : fetch_word AsanUbsan.M.loaded_segments (0x7bed8 : word) = Some W_7be88.
Proof. vm_refl. Qed.
Lemma D_7be88 : decode_any W_7be88 = Some (Branch BC_EQ 15 0 60, 4%Z).
Proof. vm_refl. Qed.

Definition W_7be8c : bv 32 := 0x00178793.
Lemma F_7be8c : fetch_word AsanUbsan.M.loaded_segments (0x7bedc : word) = Some W_7be8c.
Proof. vm_refl. Qed.
Lemma D_7be8c : decode_any W_7be8c = Some (OpImm ALU_ADD 15 15 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_7be90 : bv 32 := 0x02f57a63.
Lemma F_7be90 : fetch_word AsanUbsan.M.loaded_segments (0x7bee0 : word) = Some W_7be90.
Proof. vm_refl. Qed.
Lemma D_7be90 : decode_any W_7be90 = Some (Branch BC_GEU 10 15 52, 4%Z).
Proof. vm_refl. Qed.

Definition W_7be94 : bv 32 := 0xfffa5517.
Lemma F_7be94 : fetch_word AsanUbsan.M.loaded_segments (0x7bee4 : word) = Some W_7be94.
Proof. vm_refl. Qed.
Lemma D_7be94 : decode_any W_7be94 = Some (Auipc 10 1048485, 4%Z).
Proof. vm_refl. Qed.

Definition W_7be98 : bv 32 := 0xfff9d597.
Lemma F_7be98 : fetch_word AsanUbsan.M.loaded_segments (0x7bee8 : word) = Some W_7be98.
Proof. vm_refl. Qed.
Lemma D_7be98 : decode_any W_7be98 = Some (Auipc 11 1048477, 4%Z).
Proof. vm_refl. Qed.

Definition W_7be9c : bv 32 := 0x51150513.
Lemma F_7be9c : fetch_word AsanUbsan.M.loaded_segments (0x7beec : word) = Some W_7be9c.
Proof. vm_refl. Qed.
Lemma D_7be9c : decode_any W_7be9c = Some (OpImm ALU_ADD 10 10 1297, 4%Z).
Proof. vm_refl. Qed.

Definition W_7bea0 : bv 32 := 0xb7c58613.
Lemma F_7bea0 : fetch_word AsanUbsan.M.loaded_segments (0x7bef0 : word) = Some W_7bea0.
Proof. vm_refl. Qed.
Lemma D_7bea0 : decode_any W_7bea0 = Some (OpImm ALU_ADD 12 11 2940, 4%Z).
Proof. vm_refl. Qed.

Definition W_7bea4 : bv 32 := 0x02f00593.
Lemma F_7bea4 : fetch_word AsanUbsan.M.loaded_segments (0x7bef4 : word) = Some W_7bea4.
Proof. vm_refl. Qed.
Lemma D_7bea4 : decode_any W_7bea4 = Some (OpImm ALU_ADD 11 0 47, 4%Z).
Proof. vm_refl. Qed.

Definition W_7bea8 : bv 32 := 0x00000693.
Lemma F_7bea8 : fetch_word AsanUbsan.M.loaded_segments (0x7bef8 : word) = Some W_7bea8.
Proof. vm_refl. Qed.
Lemma D_7bea8 : decode_any W_7bea8 = Some (OpImm ALU_ADD 13 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7beac : bv 32 := 0x00000713.
Lemma F_7beac : fetch_word AsanUbsan.M.loaded_segments (0x7befc : word) = Some W_7beac.
Proof. vm_refl. Qed.
Lemma D_7beac : decode_any W_7beac = Some (OpImm ALU_ADD 14 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7beb0 : bv 32 := 0x430180ef.
Lemma F_7beb0 : fetch_word AsanUbsan.M.loaded_segments (0x7bf00 : word) = Some W_7beb0.
Proof. vm_refl. Qed.
Lemma D_7beb0 : decode_any W_7beb0 = Some (Jal 1 99376, 4%Z).
Proof. vm_refl. Qed.

Definition W_7beb4 : bv 32 := 0x00128293.
Lemma F_7beb4 : fetch_word AsanUbsan.M.loaded_segments (0x7bf04 : word) = Some W_7beb4.
Proof. vm_refl. Qed.
Lemma D_7beb4 : decode_any W_7beb4 = Some (OpImm ALU_ADD 5 5 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_7beb8 : bv 32 := 0x0032d793.
Lemma F_7beb8 : fetch_word AsanUbsan.M.loaded_segments (0x7bf08 : word) = Some W_7beb8.
Proof. vm_refl. Qed.
Lemma D_7beb8 : decode_any W_7beb8 = Some (ShiftImm ALU_SRL 15 5 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_7bebc : bv 32 := 0xfff78793.
Lemma F_7bebc : fetch_word AsanUbsan.M.loaded_segments (0x7bf0c : word) = Some W_7bebc.
Proof. vm_refl. Qed.
Lemma D_7bebc : decode_any W_7bebc = Some (OpImm ALU_ADD 15 15 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_7bec0 : bv 32 := 0xfca7eae3.
Lemma F_7bec0 : fetch_word AsanUbsan.M.loaded_segments (0x7bf10 : word) = Some W_7bec0.
Proof. vm_refl. Qed.
Lemma D_7bec0 : decode_any W_7bec0 = Some (Branch BC_LTU 15 10 8148, 4%Z).
Proof. vm_refl. Qed.

Definition W_7bec4 : bv 32 := 0x0075f793.
Lemma F_7bec4 : fetch_word AsanUbsan.M.loaded_segments (0x7bf14 : word) = Some W_7bec4.
Proof. vm_refl. Qed.
Lemma D_7bec4 : decode_any W_7bec4 = Some (OpImm ALU_AND 15 11 7, 4%Z).
Proof. vm_refl. Qed.

Definition W_7bec8 : bv 32 := 0x26079a63.
Lemma F_7bec8 : fetch_word AsanUbsan.M.loaded_segments (0x7bf18 : word) = Some W_7bec8.
Proof. vm_refl. Qed.
Lemma D_7bec8 : decode_any W_7bec8 = Some (Branch BC_NE 15 0 628, 4%Z).
Proof. vm_refl. Qed.

Definition W_7becc : bv 32 := 0x00b505b3.
Lemma F_7becc : fetch_word AsanUbsan.M.loaded_segments (0x7bf1c : word) = Some W_7becc.
Proof. vm_refl. Qed.
Lemma D_7becc : decode_any W_7becc = Some (Op ALU_ADD 11 10 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_7bed0 : bv 32 := 0xff858593.
Lemma F_7bed0 : fetch_word AsanUbsan.M.loaded_segments (0x7bf20 : word) = Some W_7bed0.
Proof. vm_refl. Qed.
Lemma D_7bed0 : decode_any W_7bed0 = Some (OpImm ALU_ADD 11 11 4088, 4%Z).
Proof. vm_refl. Qed.

Definition W_7bed4 : bv 32 := 0x04b77263.
Lemma F_7bed4 : fetch_word AsanUbsan.M.loaded_segments (0x7bf24 : word) = Some W_7bed4.
Proof. vm_refl. Qed.
Lemma D_7bed4 : decode_any W_7bed4 = Some (Branch BC_GEU 14 11 68, 4%Z).
Proof. vm_refl. Qed.

Definition W_7bed8 : bv 32 := 0x000c2717.
Lemma F_7bed8 : fetch_word AsanUbsan.M.loaded_segments (0x7bf28 : word) = Some W_7bed8.
Proof. vm_refl. Qed.
Lemma D_7bed8 : decode_any W_7bed8 = Some (Auipc 14 194, 4%Z).
Proof. vm_refl. Qed.

Definition W_7bedc : bv 32 := 0x9a873703.
Lemma F_7bedc : fetch_word AsanUbsan.M.loaded_segments (0x7bf2c : word) = Some W_7bedc.
Proof. vm_refl. Qed.
Lemma D_7bedc : decode_any W_7bedc = Some (Load SZ8 true 14 14 2472, 4%Z).
Proof. vm_refl. Qed.

Definition W_7bee0 : bv 32 := 0x000c2797.
Lemma F_7bee0 : fetch_word AsanUbsan.M.loaded_segments (0x7bf30 : word) = Some W_7bee0.
Proof. vm_refl. Qed.
Lemma D_7bee0 : decode_any W_7bee0 = Some (Auipc 15 194, 4%Z).
Proof. vm_refl. Qed.

Definition W_7bee4 : bv 32 := 0x9a87b783.
Lemma F_7bee4 : fetch_word AsanUbsan.M.loaded_segments (0x7bf34 : word) = Some W_7bee4.
Proof. vm_refl. Qed.
Lemma D_7bee4 : decode_any W_7bee4 = Some (Load SZ8 true 15 15 2472, 4%Z).
Proof. vm_refl. Qed.

Definition W_7bee8 : bv 32 := 0x00073883.
Lemma F_7bee8 : fetch_word AsanUbsan.M.loaded_segments (0x7bf38 : word) = Some W_7bee8.
Proof. vm_refl. Qed.
Lemma D_7bee8 : decode_any W_7bee8 = Some (Load SZ8 true 17 14 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7beec : bv 32 := 0x0007b703.
Lemma F_7beec : fetch_word AsanUbsan.M.loaded_segments (0x7bf3c : word) = Some W_7beec.
Proof. vm_refl. Qed.
Lemma D_7beec : decode_any W_7beec = Some (Load SZ8 true 14 15 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7bef0 : bv 32 := 0xfff88813.
Lemma F_7bef0 : fetch_word AsanUbsan.M.loaded_segments (0x7bf40 : word) = Some W_7bef0.
Proof. vm_refl. Qed.
Lemma D_7bef0 : decode_any W_7bef0 = Some (OpImm ALU_ADD 16 17 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_7bef4 : bv 32 := 0x00b87463.
Lemma F_7bef4 : fetch_word AsanUbsan.M.loaded_segments (0x7bf44 : word) = Some W_7bef4.
Proof. vm_refl. Qed.
Lemma D_7bef4 : decode_any W_7bef4 = Some (Branch BC_GEU 16 11 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_7bef8 : bv 32 := 0x02b77063.
Lemma F_7bef8 : fetch_word AsanUbsan.M.loaded_segments (0x7bf48 : word) = Some W_7bef8.
Proof. vm_refl. Qed.
Lemma D_7bef8 : decode_any W_7bef8 = Some (Branch BC_GEU 14 11 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_7befc : bv 32 := 0x000c2797.
Lemma F_7befc : fetch_word AsanUbsan.M.loaded_segments (0x7bf4c : word) = Some W_7befc.
Proof. vm_refl. Qed.
Lemma D_7befc : decode_any W_7befc = Some (Auipc 15 194, 4%Z).
Proof. vm_refl. Qed.

Definition W_7bf00 : bv 32 := 0x9947b783.
Lemma F_7bf00 : fetch_word AsanUbsan.M.loaded_segments (0x7bf50 : word) = Some W_7bf00.
Proof. vm_refl. Qed.
Lemma D_7bf00 : decode_any W_7bf00 = Some (Load SZ8 true 15 15 2452, 4%Z).
Proof. vm_refl. Qed.

Definition W_7bf04 : bv 32 := 0x0007b303.
Lemma F_7bf04 : fetch_word AsanUbsan.M.loaded_segments (0x7bf54 : word) = Some W_7bf04.
Proof. vm_refl. Qed.
Lemma D_7bf04 : decode_any W_7bf04 = Some (Load SZ8 true 6 15 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7bf08 : bv 32 := 0x00335793.
Lemma F_7bf08 : fetch_word AsanUbsan.M.loaded_segments (0x7bf58 : word) = Some W_7bf08.
Proof. vm_refl. Qed.
Lemma D_7bf08 : decode_any W_7bf08 = Some (ShiftImm ALU_SRL 15 6 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_7bf0c : bv 32 := 0x009782b3.
Lemma F_7bf0c : fetch_word AsanUbsan.M.loaded_segments (0x7bf5c : word) = Some W_7bf0c.
Proof. vm_refl. Qed.
Lemma D_7bf0c : decode_any W_7bf0c = Some (Op ALU_ADD 5 15 9, 4%Z).
Proof. vm_refl. Qed.

Definition W_7bf10 : bv 32 := 0x12b36263.
Lemma F_7bf10 : fetch_word AsanUbsan.M.loaded_segments (0x7bf60 : word) = Some W_7bf10.
Proof. vm_refl. Qed.
Lemma D_7bf10 : decode_any W_7bf10 = Some (Branch BC_LTU 6 11 292, 4%Z).
Proof. vm_refl. Qed.

Definition W_7bf14 : bv 32 := 0x12b2f063.
Lemma F_7bf14 : fetch_word AsanUbsan.M.loaded_segments (0x7bf64 : word) = Some W_7bf14.
Proof. vm_refl. Qed.
Lemma D_7bf14 : decode_any W_7bf14 = Some (Branch BC_GEU 5 11 288, 4%Z).
Proof. vm_refl. Qed.

Definition W_7bf18 : bv 32 := 0x000c2697.
Lemma F_7bf18 : fetch_word AsanUbsan.M.loaded_segments (0x7bf68 : word) = Some W_7bf18.
Proof. vm_refl. Qed.
Lemma D_7bf18 : decode_any W_7bf18 = Some (Auipc 13 194, 4%Z).
Proof. vm_refl. Qed.

Definition W_7bf1c : bv 32 := 0x9806b983.
Lemma F_7bf1c : fetch_word AsanUbsan.M.loaded_segments (0x7bf6c : word) = Some W_7bf1c.
Proof. vm_refl. Qed.
Lemma D_7bf1c : decode_any W_7bf1c = Some (Load SZ8 true 19 13 2432, 4%Z).
Proof. vm_refl. Qed.

Definition W_7bf20 : bv 32 := 0x0009b303.
Lemma F_7bf20 : fetch_word AsanUbsan.M.loaded_segments (0x7bf70 : word) = Some W_7bf20.
Proof. vm_refl. Qed.
Lemma D_7bf20 : decode_any W_7bf20 = Some (Load SZ8 true 6 19 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7bf24 : bv 32 := 0x22030c63.
Lemma F_7bf24 : fetch_word AsanUbsan.M.loaded_segments (0x7bf74 : word) = Some W_7bf24.
Proof. vm_refl. Qed.
Lemma D_7bf24 : decode_any W_7bf24 = Some (Branch BC_EQ 6 0 568, 4%Z).
Proof. vm_refl. Qed.

Definition W_7bf28 : bv 32 := 0x00355693.
Lemma F_7bf28 : fetch_word AsanUbsan.M.loaded_segments (0x7bf78 : word) = Some W_7bf28.
Proof. vm_refl. Qed.
Lemma D_7bf28 : decode_any W_7bf28 = Some (ShiftImm ALU_SRL 13 10 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_7bf2c : bv 32 := 0x0035d593.
Lemma F_7bf2c : fetch_word AsanUbsan.M.loaded_segments (0x7bf7c : word) = Some W_7bf2c.
Proof. vm_refl. Qed.
Lemma D_7bf2c : decode_any W_7bf2c = Some (ShiftImm ALU_SRL 11 11 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_7bf30 : bv 32 := 0x00d48533.
Lemma F_7bf30 : fetch_word AsanUbsan.M.loaded_segments (0x7bf80 : word) = Some W_7bf30.
Proof. vm_refl. Qed.
Lemma D_7bf30 : decode_any W_7bf30 = Some (Op ALU_ADD 10 9 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_7bf34 : bv 32 := 0x00158913.
Lemma F_7bf34 : fetch_word AsanUbsan.M.loaded_segments (0x7bf84 : word) = Some W_7bf34.
Proof. vm_refl. Qed.
Lemma D_7bf34 : decode_any W_7bf34 = Some (OpImm ALU_ADD 18 11 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_7bf38 : bv 32 := 0x40d90433.
Lemma F_7bf38 : fetch_word AsanUbsan.M.loaded_segments (0x7bf88 : word) = Some W_7bf38.
Proof. vm_refl. Qed.
Lemma D_7bf38 : decode_any W_7bf38 = Some (Op ALU_SUB 8 18 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_7bf3c : bv 32 := 0x0c061063.
Lemma F_7bf3c : fetch_word AsanUbsan.M.loaded_segments (0x7bf8c : word) = Some W_7bf3c.
Proof. vm_refl. Qed.
Lemma D_7bf3c : decode_any W_7bf3c = Some (Branch BC_NE 12 0 192, 4%Z).
Proof. vm_refl. Qed.

Definition W_7bf40 : bv 32 := 0x000c2597.
Lemma F_7bf40 : fetch_word AsanUbsan.M.loaded_segments (0x7bf90 : word) = Some W_7bf40.
Proof. vm_refl. Qed.
Lemma D_7bf40 : decode_any W_7bf40 = Some (Auipc 11 194, 4%Z).
Proof. vm_refl. Qed.

Definition W_7bf44 : bv 32 := 0x9285b583.
Lemma F_7bf44 : fetch_word AsanUbsan.M.loaded_segments (0x7bf94 : word) = Some W_7bf44.
Proof. vm_refl. Qed.
Lemma D_7bf44 : decode_any W_7bf44 = Some (Load SZ8 true 11 11 2344, 4%Z).
Proof. vm_refl. Qed.

Definition W_7bf48 : bv 32 := 0x0785b583.
Lemma F_7bf48 : fetch_word AsanUbsan.M.loaded_segments (0x7bf98 : word) = Some W_7bf48.
Proof. vm_refl. Qed.
Lemma D_7bf48 : decode_any W_7bf48 = Some (Load SZ8 true 11 11 120, 4%Z).
Proof. vm_refl. Qed.

Definition W_7bf4c : bv 32 := 0x0ab46863.
Lemma F_7bf4c : fetch_word AsanUbsan.M.loaded_segments (0x7bf9c : word) = Some W_7bf4c.
Proof. vm_refl. Qed.
Lemma D_7bf4c : decode_any W_7bf4c = Some (Branch BC_LTU 8 11 176, 4%Z).
Proof. vm_refl. Qed.

Definition W_7bf5c : bv 32 := 0x00059c63.
Lemma F_7bf5c : fetch_word AsanUbsan.M.loaded_segments (0x7bfac : word) = Some W_7bf5c.
Proof. vm_refl. Qed.
Lemma D_7bf5c : decode_any W_7bf5c = Some (Branch BC_NE 11 0 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_7bf60 : bv 32 := 0x00050a93.
Lemma F_7bf60 : fetch_word AsanUbsan.M.loaded_segments (0x7bfb0 : word) = Some W_7bf60.
Proof. vm_refl. Qed.
Lemma D_7bf60 : decode_any W_7bf60 = Some (OpImm ALU_ADD 21 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7bf64 : bv 32 := 0x5a1110ef.
Lemma F_7bf64 : fetch_word AsanUbsan.M.loaded_segments (0x7bfb4 : word) = Some W_7bf64.
Proof. vm_refl. Qed.
Lemma D_7bf64 : decode_any W_7bf64 = Some (Jal 1 73120, 4%Z).
Proof. vm_refl. Qed.

Definition W_7bf68 : bv 32 := 0x00050593.
Lemma F_7bf68 : fetch_word AsanUbsan.M.loaded_segments (0x7bfb8 : word) = Some W_7bf68.
Proof. vm_refl. Qed.
Lemma D_7bf68 : decode_any W_7bf68 = Some (OpImm ALU_ADD 11 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7bf6c : bv 32 := 0x000a8513.
Lemma F_7bf6c : fetch_word AsanUbsan.M.loaded_segments (0x7bfbc : word) = Some W_7bf6c.
Proof. vm_refl. Qed.
Lemma D_7bf6c : decode_any W_7bf6c = Some (OpImm ALU_ADD 10 21 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7bf70 : bv 32 := 0x00ba3023.
Lemma F_7bf70 : fetch_word AsanUbsan.M.loaded_segments (0x7bfc0 : word) = Some W_7bf70.
Proof. vm_refl. Qed.
Lemma D_7bf70 : decode_any W_7bf70 = Some (Store SZ8 20 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7bf74 : bv 32 := 0xfff58613.
Lemma F_7bf74 : fetch_word AsanUbsan.M.loaded_segments (0x7bfc4 : word) = Some W_7bf74.
Proof. vm_refl. Qed.
Lemma D_7bf74 : decode_any W_7bf74 = Some (OpImm ALU_ADD 12 11 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_7bf78 : bv 32 := 0x00c5f633.
Lemma F_7bf78 : fetch_word AsanUbsan.M.loaded_segments (0x7bfc8 : word) = Some W_7bf78.
Proof. vm_refl. Qed.
Lemma D_7bf78 : decode_any W_7bf78 = Some (Op ALU_AND 12 11 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_7bf7c : bv 32 := 0x20061063.
Lemma F_7bf7c : fetch_word AsanUbsan.M.loaded_segments (0x7bfcc : word) = Some W_7bf7c.
Proof. vm_refl. Qed.
Lemma D_7bf7c : decode_any W_7bf7c = Some (Branch BC_NE 12 0 512, 4%Z).
Proof. vm_refl. Qed.

Definition W_7bf80 : bv 32 := 0x00990a33.
Lemma F_7bf80 : fetch_word AsanUbsan.M.loaded_segments (0x7bfd0 : word) = Some W_7bf80.
Proof. vm_refl. Qed.
Lemma D_7bf80 : decode_any W_7bf80 = Some (Op ALU_ADD 20 18 9, 4%Z).
Proof. vm_refl. Qed.

Definition W_7bf84 : bv 32 := 0x00b50633.
Lemma F_7bf84 : fetch_word AsanUbsan.M.loaded_segments (0x7bfd4 : word) = Some W_7bf84.
Proof. vm_refl. Qed.
Lemma D_7bf84 : decode_any W_7bf84 = Some (Op ALU_ADD 12 10 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_7bf88 : bv 32 := 0x40b005b3.
Lemma F_7bf88 : fetch_word AsanUbsan.M.loaded_segments (0x7bfd8 : word) = Some W_7bf88.
Proof. vm_refl. Qed.
Lemma D_7bf88 : decode_any W_7bf88 = Some (Op ALU_SUB 11 0 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_7bf8c : bv 32 := 0xfff60613.
Lemma F_7bf8c : fetch_word AsanUbsan.M.loaded_segments (0x7bfdc : word) = Some W_7bf8c.
Proof. vm_refl. Qed.
Lemma D_7bf8c : decode_any W_7bf8c = Some (OpImm ALU_ADD 12 12 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_7bf90 : bv 32 := 0x00b674b3.
Lemma F_7bf90 : fetch_word AsanUbsan.M.loaded_segments (0x7bfe0 : word) = Some W_7bf90.
Proof. vm_refl. Qed.
Lemma D_7bf90 : decode_any W_7bf90 = Some (Op ALU_AND 9 12 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_7bf94 : bv 32 := 0x00ba7933.
Lemma F_7bf94 : fetch_word AsanUbsan.M.loaded_segments (0x7bfe4 : word) = Some W_7bf94.
Proof. vm_refl. Qed.
Lemma D_7bf94 : decode_any W_7bf94 = Some (Op ALU_AND 18 20 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_7bf98 : bv 32 := 0x0724f663.
Lemma F_7bf98 : fetch_word AsanUbsan.M.loaded_segments (0x7bfe8 : word) = Some W_7bf98.
Proof. vm_refl. Qed.
Lemma D_7bf98 : decode_any W_7bf98 = Some (Branch BC_GEU 9 18 108, 4%Z).
Proof. vm_refl. Qed.

Definition W_7bf9c : bv 32 := 0x00a48a63.
Lemma F_7bf9c : fetch_word AsanUbsan.M.loaded_segments (0x7bfec : word) = Some W_7bf9c.
Proof. vm_refl. Qed.
Lemma D_7bf9c : decode_any W_7bf9c = Some (Branch BC_EQ 9 10 20, 4%Z).
Proof. vm_refl. Qed.

Definition W_7bfa0 : bv 32 := 0x0009b683.
Lemma F_7bfa0 : fetch_word AsanUbsan.M.loaded_segments (0x7bff0 : word) = Some W_7bfa0.
Proof. vm_refl. Qed.
Lemma D_7bfa0 : decode_any W_7bfa0 = Some (Load SZ8 true 13 19 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7bfa4 : bv 32 := 0x40a48633.
Lemma F_7bfa4 : fetch_word AsanUbsan.M.loaded_segments (0x7bff4 : word) = Some W_7bfa4.
Proof. vm_refl. Qed.
Lemma D_7bfa4 : decode_any W_7bfa4 = Some (Op ALU_SUB 12 9 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_7bfa8 : bv 32 := 0x00000593.
Lemma F_7bfa8 : fetch_word AsanUbsan.M.loaded_segments (0x7bff8 : word) = Some W_7bfa8.
Proof. vm_refl. Qed.
Lemma D_7bfa8 : decode_any W_7bfa8 = Some (OpImm ALU_ADD 11 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7bfac : bv 32 := 0x000680e7.
Lemma F_7bfac : fetch_word AsanUbsan.M.loaded_segments (0x7bffc : word) = Some W_7bfac.
Proof. vm_refl. Qed.
Lemma D_7bfac : decode_any W_7bfac = Some (Jalr 1 13 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7bfb0 : bv 32 := 0x012a0c63.
Lemma F_7bfb0 : fetch_word AsanUbsan.M.loaded_segments (0x7c000 : word) = Some W_7bfb0.
Proof. vm_refl. Qed.
Lemma D_7bfb0 : decode_any W_7bfb0 = Some (Branch BC_EQ 20 18 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_7bfb4 : bv 32 := 0x0009b683.
Lemma F_7bfb4 : fetch_word AsanUbsan.M.loaded_segments (0x7c004 : word) = Some W_7bfb4.
Proof. vm_refl. Qed.
Lemma D_7bfb4 : decode_any W_7bfb4 = Some (Load SZ8 true 13 19 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7bfb8 : bv 32 := 0x412a0633.
Lemma F_7bfb8 : fetch_word AsanUbsan.M.loaded_segments (0x7c008 : word) = Some W_7bfb8.
Proof. vm_refl. Qed.
Lemma D_7bfb8 : decode_any W_7bfb8 = Some (Op ALU_SUB 12 20 18, 4%Z).
Proof. vm_refl. Qed.

Definition W_7bfbc : bv 32 := 0x00090513.
Lemma F_7bfbc : fetch_word AsanUbsan.M.loaded_segments (0x7c00c : word) = Some W_7bfbc.
Proof. vm_refl. Qed.
Lemma D_7bfbc : decode_any W_7bfbc = Some (OpImm ALU_ADD 10 18 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7bfc0 : bv 32 := 0x00000593.
Lemma F_7bfc0 : fetch_word AsanUbsan.M.loaded_segments (0x7c010 : word) = Some W_7bfc0.
Proof. vm_refl. Qed.
Lemma D_7bfc0 : decode_any W_7bfc0 = Some (OpImm ALU_ADD 11 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7bfc4 : bv 32 := 0x000680e7.
Lemma F_7bfc4 : fetch_word AsanUbsan.M.loaded_segments (0x7c014 : word) = Some W_7bfc4.
Proof. vm_refl. Qed.
Lemma D_7bfc4 : decode_any W_7bfc4 = Some (Jalr 1 13 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7bfc8 : bv 32 := 0xfff90593.
Lemma F_7bfc8 : fetch_word AsanUbsan.M.loaded_segments (0x7c018 : word) = Some W_7bfc8.
Proof. vm_refl. Qed.
Lemma D_7bfc8 : decode_any W_7bfc8 = Some (OpImm ALU_ADD 11 18 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_7bfcc : bv 32 := 0x00100693.
Lemma F_7bfcc : fetch_word AsanUbsan.M.loaded_segments (0x7c01c : word) = Some W_7bfcc.
Proof. vm_refl. Qed.
Lemma D_7bfcc : decode_any W_7bfcc = Some (OpImm ALU_ADD 13 0 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_7bfd0 : bv 32 := 0x00048513.
Lemma F_7bfd0 : fetch_word AsanUbsan.M.loaded_segments (0x7c020 : word) = Some W_7bfd0.
Proof. vm_refl. Qed.
Lemma D_7bfd0 : decode_any W_7bfd0 = Some (OpImm ALU_ADD 10 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7bfd4 : bv 32 := 0x00000613.
Lemma F_7bfd4 : fetch_word AsanUbsan.M.loaded_segments (0x7c024 : word) = Some W_7bfd4.
Proof. vm_refl. Qed.
Lemma D_7bfd4 : decode_any W_7bfd4 = Some (OpImm ALU_ADD 12 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7bfd8 : bv 32 := 0x03813083.
Lemma F_7bfd8 : fetch_word AsanUbsan.M.loaded_segments (0x7c028 : word) = Some W_7bfd8.
Proof. vm_refl. Qed.
Lemma D_7bfd8 : decode_any W_7bfd8 = Some (Load SZ8 true 1 2 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_7bfdc : bv 32 := 0x03013403.
Lemma F_7bfdc : fetch_word AsanUbsan.M.loaded_segments (0x7c02c : word) = Some W_7bfdc.
Proof. vm_refl. Qed.
Lemma D_7bfdc : decode_any W_7bfdc = Some (Load SZ8 true 8 2 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_7bfe0 : bv 32 := 0x02813483.
Lemma F_7bfe0 : fetch_word AsanUbsan.M.loaded_segments (0x7c030 : word) = Some W_7bfe0.
Proof. vm_refl. Qed.
Lemma D_7bfe0 : decode_any W_7bfe0 = Some (Load SZ8 true 9 2 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_7bfe4 : bv 32 := 0x02013903.
Lemma F_7bfe4 : fetch_word AsanUbsan.M.loaded_segments (0x7c034 : word) = Some W_7bfe4.
Proof. vm_refl. Qed.
Lemma D_7bfe4 : decode_any W_7bfe4 = Some (Load SZ8 true 18 2 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_7bfe8 : bv 32 := 0x01813983.
Lemma F_7bfe8 : fetch_word AsanUbsan.M.loaded_segments (0x7c038 : word) = Some W_7bfe8.
Proof. vm_refl. Qed.
Lemma D_7bfe8 : decode_any W_7bfe8 = Some (Load SZ8 true 19 2 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_7bfec : bv 32 := 0x01013a03.
Lemma F_7bfec : fetch_word AsanUbsan.M.loaded_segments (0x7c03c : word) = Some W_7bfec.
Proof. vm_refl. Qed.
Lemma D_7bfec : decode_any W_7bfec = Some (Load SZ8 true 20 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_7bff0 : bv 32 := 0x00813a83.
Lemma F_7bff0 : fetch_word AsanUbsan.M.loaded_segments (0x7c040 : word) = Some W_7bff0.
Proof. vm_refl. Qed.
Lemma D_7bff0 : decode_any W_7bff0 = Some (Load SZ8 true 21 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_7bff4 : bv 32 := 0x04010113.
Lemma F_7bff4 : fetch_word AsanUbsan.M.loaded_segments (0x7c044 : word) = Some W_7bff4.
Proof. vm_refl. Qed.
Lemma D_7bff4 : decode_any W_7bff4 = Some (OpImm ALU_ADD 2 2 64, 4%Z).
Proof. vm_refl. Qed.

Definition W_7bff8 : bv 32 := 0x2f11806f.
Lemma F_7bff8 : fetch_word AsanUbsan.M.loaded_segments (0x7c048 : word) = Some W_7bff8.
Proof. vm_refl. Qed.
Lemma D_7bff8 : decode_any W_7bff8 = Some (Jal 0 101104, 4%Z).
Proof. vm_refl. Qed.

Definition W_7bffc : bv 32 := 0x00060593.
Lemma F_7bffc : fetch_word AsanUbsan.M.loaded_segments (0x7c04c : word) = Some W_7bffc.
Proof. vm_refl. Qed.
Lemma D_7bffc : decode_any W_7bffc = Some (OpImm ALU_ADD 11 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7c000 : bv 32 := 0x00c0006f.
Lemma F_7c000 : fetch_word AsanUbsan.M.loaded_segments (0x7c050 : word) = Some W_7c000.
Proof. vm_refl. Qed.
Lemma D_7c000 : decode_any W_7c000 = Some (Jal 0 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_7c004 : bv 32 := 0x0009b303.
Lemma F_7c004 : fetch_word AsanUbsan.M.loaded_segments (0x7c054 : word) = Some W_7c004.
Proof. vm_refl. Qed.
Lemma D_7c004 : decode_any W_7c004 = Some (Load SZ8 true 6 19 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7c008 : bv 32 := 0x00000593.
Lemma F_7c008 : fetch_word AsanUbsan.M.loaded_segments (0x7c058 : word) = Some W_7c008.
Proof. vm_refl. Qed.
Lemma D_7c008 : decode_any W_7c008 = Some (OpImm ALU_ADD 11 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7c00c : bv 32 := 0x00040613.
Lemma F_7c00c : fetch_word AsanUbsan.M.loaded_segments (0x7c05c : word) = Some W_7c00c.
Proof. vm_refl. Qed.
Lemma D_7c00c : decode_any W_7c00c = Some (OpImm ALU_ADD 12 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7c010 : bv 32 := 0x03813083.
Lemma F_7c010 : fetch_word AsanUbsan.M.loaded_segments (0x7c060 : word) = Some W_7c010.
Proof. vm_refl. Qed.
Lemma D_7c010 : decode_any W_7c010 = Some (Load SZ8 true 1 2 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_7c014 : bv 32 := 0x03013403.
Lemma F_7c014 : fetch_word AsanUbsan.M.loaded_segments (0x7c064 : word) = Some W_7c014.
Proof. vm_refl. Qed.
Lemma D_7c014 : decode_any W_7c014 = Some (Load SZ8 true 8 2 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_7c018 : bv 32 := 0x02813483.
Lemma F_7c018 : fetch_word AsanUbsan.M.loaded_segments (0x7c068 : word) = Some W_7c018.
Proof. vm_refl. Qed.
Lemma D_7c018 : decode_any W_7c018 = Some (Load SZ8 true 9 2 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_7c01c : bv 32 := 0x02013903.
Lemma F_7c01c : fetch_word AsanUbsan.M.loaded_segments (0x7c06c : word) = Some W_7c01c.
Proof. vm_refl. Qed.
Lemma D_7c01c : decode_any W_7c01c = Some (Load SZ8 true 18 2 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_7c020 : bv 32 := 0x01813983.
Lemma F_7c020 : fetch_word AsanUbsan.M.loaded_segments (0x7c070 : word) = Some W_7c020.
Proof. vm_refl. Qed.
Lemma D_7c020 : decode_any W_7c020 = Some (Load SZ8 true 19 2 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_7c024 : bv 32 := 0x01013a03.
Lemma F_7c024 : fetch_word AsanUbsan.M.loaded_segments (0x7c074 : word) = Some W_7c024.
Proof. vm_refl. Qed.
Lemma D_7c024 : decode_any W_7c024 = Some (Load SZ8 true 20 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_7c028 : bv 32 := 0x00813a83.
Lemma F_7c028 : fetch_word AsanUbsan.M.loaded_segments (0x7c078 : word) = Some W_7c028.
Proof. vm_refl. Qed.
Lemma D_7c028 : decode_any W_7c028 = Some (Load SZ8 true 21 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_7c02c : bv 32 := 0x04010113.
Lemma F_7c02c : fetch_word AsanUbsan.M.loaded_segments (0x7c07c : word) = Some W_7c02c.
Proof. vm_refl. Qed.
Lemma D_7c02c : decode_any W_7c02c = Some (OpImm ALU_ADD 2 2 64, 4%Z).
Proof. vm_refl. Qed.

Definition W_7c030 : bv 32 := 0x00030067.
Lemma F_7c030 : fetch_word AsanUbsan.M.loaded_segments (0x7c080 : word) = Some W_7c030.
Proof. vm_refl. Qed.
Lemma D_7c030 : decode_any W_7c030 = Some (Jalr 0 6 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7c034 : bv 32 := 0x000c2317.
Lemma F_7c034 : fetch_word AsanUbsan.M.loaded_segments (0x7c084 : word) = Some W_7c034.
Proof. vm_refl. Qed.
Lemma D_7c034 : decode_any W_7c034 = Some (Auipc 6 194, 4%Z).
Proof. vm_refl. Qed.

Definition W_7c038 : bv 32 := 0x83c33303.
Lemma F_7c038 : fetch_word AsanUbsan.M.loaded_segments (0x7c088 : word) = Some W_7c038.
Proof. vm_refl. Qed.
Lemma D_7c038 : decode_any W_7c038 = Some (Load SZ8 true 6 6 2108, 4%Z).
Proof. vm_refl. Qed.

Definition W_7c03c : bv 32 := 0x04e34303.
Lemma F_7c03c : fetch_word AsanUbsan.M.loaded_segments (0x7c08c : word) = Some W_7c03c.
Proof. vm_refl. Qed.
Lemma D_7c03c : decode_any W_7c03c = Some (Load SZ1 false 6 6 78, 4%Z).
Proof. vm_refl. Qed.

Definition W_7c040 : bv 32 := 0x08031e63.
Lemma F_7c040 : fetch_word AsanUbsan.M.loaded_segments (0x7c090 : word) = Some W_7c040.
Proof. vm_refl. Qed.
Lemma D_7c040 : decode_any W_7c040 = Some (Branch BC_NE 6 0 156, 4%Z).
Proof. vm_refl. Qed.

Definition W_7c044 : bv 32 := 0x04088063.
Lemma F_7c044 : fetch_word AsanUbsan.M.loaded_segments (0x7c094 : word) = Some W_7c044.
Proof. vm_refl. Qed.
Lemma D_7c044 : decode_any W_7c044 = Some (Branch BC_EQ 17 0 64, 4%Z).
Proof. vm_refl. Qed.

Definition W_7c048 : bv 32 := 0x0038d893.
Lemma F_7c048 : fetch_word AsanUbsan.M.loaded_segments (0x7c098 : word) = Some W_7c048.
Proof. vm_refl. Qed.
Lemma D_7c048 : decode_any W_7c048 = Some (ShiftImm ALU_SRL 17 17 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_7c04c : bv 32 := 0x00d888b3.
Lemma F_7c04c : fetch_word AsanUbsan.M.loaded_segments (0x7c09c : word) = Some W_7c04c.
Proof. vm_refl. Qed.
Lemma D_7c04c : decode_any W_7c04c = Some (Op ALU_ADD 17 17 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_7c050 : bv 32 := 0x06b8f063.
Lemma F_7c050 : fetch_word AsanUbsan.M.loaded_segments (0x7c0a0 : word) = Some W_7c050.
Proof. vm_refl. Qed.
Lemma D_7c050 : decode_any W_7c050 = Some (Branch BC_GEU 17 11 96, 4%Z).
Proof. vm_refl. Qed.

Definition W_7c054 : bv 32 := 0x00148893.
Lemma F_7c054 : fetch_word AsanUbsan.M.loaded_segments (0x7c0a4 : word) = Some W_7c054.
Proof. vm_refl. Qed.
Lemma D_7c054 : decode_any W_7c054 = Some (OpImm ALU_ADD 17 9 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_7c058 : bv 32 := 0x00b86863.
Lemma F_7c058 : fetch_word AsanUbsan.M.loaded_segments (0x7c0a8 : word) = Some W_7c058.
Proof. vm_refl. Qed.
Lemma D_7c058 : decode_any W_7c058 = Some (Branch BC_LTU 16 11 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_7c05c : bv 32 := 0x00375813.
Lemma F_7c05c : fetch_word AsanUbsan.M.loaded_segments (0x7c0ac : word) = Some W_7c05c.
Proof. vm_refl. Qed.
Lemma D_7c05c : decode_any W_7c05c = Some (ShiftImm ALU_SRL 16 14 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_7c060 : bv 32 := 0x01180833.
Lemma F_7c060 : fetch_word AsanUbsan.M.loaded_segments (0x7c0b0 : word) = Some W_7c060.
Proof. vm_refl. Qed.
Lemma D_7c060 : decode_any W_7c060 = Some (Op ALU_ADD 16 16 17, 4%Z).
Proof. vm_refl. Qed.

Definition W_7c064 : bv 32 := 0xeb05fae3.
Lemma F_7c064 : fetch_word AsanUbsan.M.loaded_segments (0x7c0b4 : word) = Some W_7c064.
Proof. vm_refl. Qed.
Lemma D_7c064 : decode_any W_7c064 = Some (Branch BC_GEU 11 16 7860, 4%Z).
Proof. vm_refl. Qed.

Definition W_7c068 : bv 32 := 0x00170713.
Lemma F_7c068 : fetch_word AsanUbsan.M.loaded_segments (0x7c0b8 : word) = Some W_7c068.
Proof. vm_refl. Qed.
Lemma D_7c068 : decode_any W_7c068 = Some (OpImm ALU_ADD 14 14 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_7c06c : bv 32 := 0x06e5e863.
Lemma F_7c06c : fetch_word AsanUbsan.M.loaded_segments (0x7c0bc : word) = Some W_7c06c.
Proof. vm_refl. Qed.
Lemma D_7c06c : decode_any W_7c06c = Some (Branch BC_LTU 11 14 112, 4%Z).
Proof. vm_refl. Qed.

Definition W_7c070 : bv 32 := 0x011787b3.
Lemma F_7c070 : fetch_word AsanUbsan.M.loaded_segments (0x7c0c0 : word) = Some W_7c070.
Proof. vm_refl. Qed.
Lemma D_7c070 : decode_any W_7c070 = Some (Op ALU_ADD 15 15 17, 4%Z).
Proof. vm_refl. Qed.

Definition W_7c074 : bv 32 := 0x0037d793.
Lemma F_7c074 : fetch_word AsanUbsan.M.loaded_segments (0x7c0c4 : word) = Some W_7c074.
Proof. vm_refl. Qed.
Lemma D_7c074 : decode_any W_7c074 = Some (ShiftImm ALU_SRL 15 15 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_7c078 : bv 32 := 0x00d786b3.
Lemma F_7c078 : fetch_word AsanUbsan.M.loaded_segments (0x7c0c8 : word) = Some W_7c078.
Proof. vm_refl. Qed.
Lemma D_7c078 : decode_any W_7c078 = Some (Op ALU_ADD 13 15 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_7c07c : bv 32 := 0xe8b6fee3.
Lemma F_7c07c : fetch_word AsanUbsan.M.loaded_segments (0x7c0cc : word) = Some W_7c07c.
Proof. vm_refl. Qed.
Lemma D_7c07c : decode_any W_7c07c = Some (Branch BC_GEU 13 11 7836, 4%Z).
Proof. vm_refl. Qed.

Definition W_7c080 : bv 32 := 0x05c0006f.
Lemma F_7c080 : fetch_word AsanUbsan.M.loaded_segments (0x7c0d0 : word) = Some W_7c080.
Proof. vm_refl. Qed.
Lemma D_7c080 : decode_any W_7c080 = Some (Jal 0 92, 4%Z).
Proof. vm_refl. Qed.

Definition W_7c084 : bv 32 := 0x04048463.
Lemma F_7c084 : fetch_word AsanUbsan.M.loaded_segments (0x7c0d4 : word) = Some W_7c084.
Proof. vm_refl. Qed.
Lemma D_7c084 : decode_any W_7c084 = Some (Branch BC_EQ 9 0 72, 4%Z).
Proof. vm_refl. Qed.

Definition W_7c088 : bv 32 := 0x0036d713.
Lemma F_7c088 : fetch_word AsanUbsan.M.loaded_segments (0x7c0d8 : word) = Some W_7c088.
Proof. vm_refl. Qed.
Lemma D_7c088 : decode_any W_7c088 = Some (ShiftImm ALU_SRL 14 13 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_7c08c : bv 32 := 0x00970733.
Lemma F_7c08c : fetch_word AsanUbsan.M.loaded_segments (0x7c0dc : word) = Some W_7c08c.
Proof. vm_refl. Qed.
Lemma D_7c08c : decode_any W_7c08c = Some (Op ALU_ADD 14 14 9, 4%Z).
Proof. vm_refl. Qed.

Definition W_7c090 : bv 32 := 0x00070663.
Lemma F_7c090 : fetch_word AsanUbsan.M.loaded_segments (0x7c0e0 : word) = Some W_7c090.
Proof. vm_refl. Qed.
Lemma D_7c090 : decode_any W_7c090 = Some (Branch BC_EQ 14 0 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_7c094 : bv 32 := 0x00170713.
Lemma F_7c094 : fetch_word AsanUbsan.M.loaded_segments (0x7c0e4 : word) = Some W_7c094.
Proof. vm_refl. Qed.
Lemma D_7c094 : decode_any W_7c094 = Some (OpImm ALU_ADD 14 14 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_7c098 : bv 32 := 0x04e5e263.
Lemma F_7c098 : fetch_word AsanUbsan.M.loaded_segments (0x7c0e8 : word) = Some W_7c098.
Proof. vm_refl. Qed.
Lemma D_7c098 : decode_any W_7c098 = Some (Branch BC_LTU 11 14 68, 4%Z).
Proof. vm_refl. Qed.

Definition W_7c09c : bv 32 := 0x00128293.
Lemma F_7c09c : fetch_word AsanUbsan.M.loaded_segments (0x7c0ec : word) = Some W_7c09c.
Proof. vm_refl. Qed.
Lemma D_7c09c : decode_any W_7c09c = Some (OpImm ALU_ADD 5 5 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_7c0a0 : bv 32 := 0x0032d713.
Lemma F_7c0a0 : fetch_word AsanUbsan.M.loaded_segments (0x7c0f0 : word) = Some W_7c0a0.
Proof. vm_refl. Qed.
Lemma D_7c0a0 : decode_any W_7c0a0 = Some (ShiftImm ALU_SRL 14 5 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_7c0a4 : bv 32 := 0x00d706b3.
Lemma F_7c0a4 : fetch_word AsanUbsan.M.loaded_segments (0x7c0f4 : word) = Some W_7c0a4.
Proof. vm_refl. Qed.
Lemma D_7c0a4 : decode_any W_7c0a4 = Some (Op ALU_ADD 13 14 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_7c0a8 : bv 32 := 0xe6b6f8e3.
Lemma F_7c0a8 : fetch_word AsanUbsan.M.loaded_segments (0x7c0f8 : word) = Some W_7c0a8.
Proof. vm_refl. Qed.
Lemma D_7c0a8 : decode_any W_7c0a8 = Some (Branch BC_GEU 13 11 7792, 4%Z).
Proof. vm_refl. Qed.

Definition W_7c0ac : bv 32 := 0x0300006f.
Lemma F_7c0ac : fetch_word AsanUbsan.M.loaded_segments (0x7c0fc : word) = Some W_7c0ac.
Proof. vm_refl. Qed.
Lemma D_7c0ac : decode_any W_7c0ac = Some (Jal 0 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_7c0b0 : bv 32 := 0xe60484e3.
Lemma F_7c0b0 : fetch_word AsanUbsan.M.loaded_segments (0x7c100 : word) = Some W_7c0b0.
Proof. vm_refl. Qed.
Lemma D_7c0b0 : decode_any W_7c0b0 = Some (Branch BC_EQ 9 0 7784, 4%Z).
Proof. vm_refl. Qed.

Definition W_7c0b4 : bv 32 := 0x0036d693.
Lemma F_7c0b4 : fetch_word AsanUbsan.M.loaded_segments (0x7c104 : word) = Some W_7c0b4.
Proof. vm_refl. Qed.
Lemma D_7c0b4 : decode_any W_7c0b4 = Some (ShiftImm ALU_SRL 13 13 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_7c0b8 : bv 32 := 0x009686b3.
Lemma F_7c0b8 : fetch_word AsanUbsan.M.loaded_segments (0x7c108 : word) = Some W_7c0b8.
Proof. vm_refl. Qed.
Lemma D_7c0b8 : decode_any W_7c0b8 = Some (Op ALU_ADD 13 13 9, 4%Z).
Proof. vm_refl. Qed.

Definition W_7c0bc : bv 32 := 0xe4068ee3.
Lemma F_7c0bc : fetch_word AsanUbsan.M.loaded_segments (0x7c10c : word) = Some W_7c0bc.
Proof. vm_refl. Qed.
Lemma D_7c0bc : decode_any W_7c0bc = Some (Branch BC_EQ 13 0 7772, 4%Z).
Proof. vm_refl. Qed.

Definition W_7c0c0 : bv 32 := 0x00168693.
Lemma F_7c0c0 : fetch_word AsanUbsan.M.loaded_segments (0x7c110 : word) = Some W_7c0c0.
Proof. vm_refl. Qed.
Lemma D_7c0c0 : decode_any W_7c0c0 = Some (OpImm ALU_ADD 13 13 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_7c0c4 : bv 32 := 0xe4d5fae3.
Lemma F_7c0c4 : fetch_word AsanUbsan.M.loaded_segments (0x7c114 : word) = Some W_7c0c4.
Proof. vm_refl. Qed.
Lemma D_7c0c4 : decode_any W_7c0c4 = Some (Branch BC_GEU 11 13 7764, 4%Z).
Proof. vm_refl. Qed.

Definition W_7c0c8 : bv 32 := 0x0140006f.
Lemma F_7c0c8 : fetch_word AsanUbsan.M.loaded_segments (0x7c118 : word) = Some W_7c0c8.
Proof. vm_refl. Qed.
Lemma D_7c0c8 : decode_any W_7c0c8 = Some (Jal 0 20, 4%Z).
Proof. vm_refl. Qed.

Definition W_7c0cc : bv 32 := 0x00178793.
Lemma F_7c0cc : fetch_word AsanUbsan.M.loaded_segments (0x7c11c : word) = Some W_7c0cc.
Proof. vm_refl. Qed.
Lemma D_7c0cc : decode_any W_7c0cc = Some (OpImm ALU_ADD 15 15 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_7c0d0 : bv 32 := 0x0037d793.
Lemma F_7c0d0 : fetch_word AsanUbsan.M.loaded_segments (0x7c120 : word) = Some W_7c0d0.
Proof. vm_refl. Qed.
Lemma D_7c0d0 : decode_any W_7c0d0 = Some (ShiftImm ALU_SRL 15 15 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_7c0d4 : bv 32 := 0xfff78793.
Lemma F_7c0d4 : fetch_word AsanUbsan.M.loaded_segments (0x7c124 : word) = Some W_7c0d4.
Proof. vm_refl. Qed.
Lemma D_7c0d4 : decode_any W_7c0d4 = Some (OpImm ALU_ADD 15 15 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_7c0d8 : bv 32 := 0xe4b7f0e3.
Lemma F_7c0d8 : fetch_word AsanUbsan.M.loaded_segments (0x7c128 : word) = Some W_7c0d8.
Proof. vm_refl. Qed.
Lemma D_7c0d8 : decode_any W_7c0d8 = Some (Branch BC_GEU 15 11 7744, 4%Z).
Proof. vm_refl. Qed.

Definition W_7c0dc : bv 32 := 0xfffa5517.
Lemma F_7c0dc : fetch_word AsanUbsan.M.loaded_segments (0x7c12c : word) = Some W_7c0dc.
Proof. vm_refl. Qed.
Lemma D_7c0dc : decode_any W_7c0dc = Some (Auipc 10 1048485, 4%Z).
Proof. vm_refl. Qed.

Definition W_7c0e0 : bv 32 := 0xfff98597.
Lemma F_7c0e0 : fetch_word AsanUbsan.M.loaded_segments (0x7c130 : word) = Some W_7c0e0.
Proof. vm_refl. Qed.
Lemma D_7c0e0 : decode_any W_7c0e0 = Some (Auipc 11 1048472, 4%Z).
Proof. vm_refl. Qed.

Definition W_7c0e4 : bv 32 := 0x2c950513.
Lemma F_7c0e4 : fetch_word AsanUbsan.M.loaded_segments (0x7c134 : word) = Some W_7c0e4.
Proof. vm_refl. Qed.
Lemma D_7c0e4 : decode_any W_7c0e4 = Some (OpImm ALU_ADD 10 10 713, 4%Z).
Proof. vm_refl. Qed.

Definition W_7c0e8 : bv 32 := 0xf5458613.
Lemma F_7c0e8 : fetch_word AsanUbsan.M.loaded_segments (0x7c138 : word) = Some W_7c0e8.
Proof. vm_refl. Qed.
Lemma D_7c0e8 : decode_any W_7c0e8 = Some (OpImm ALU_ADD 12 11 3924, 4%Z).
Proof. vm_refl. Qed.

Definition W_7c0ec : bv 32 := 0x03100593.
Lemma F_7c0ec : fetch_word AsanUbsan.M.loaded_segments (0x7c13c : word) = Some W_7c0ec.
Proof. vm_refl. Qed.
Lemma D_7c0ec : decode_any W_7c0ec = Some (OpImm ALU_ADD 11 0 49, 4%Z).
Proof. vm_refl. Qed.

Definition W_7c0f0 : bv 32 := 0x00000693.
Lemma F_7c0f0 : fetch_word AsanUbsan.M.loaded_segments (0x7c140 : word) = Some W_7c0f0.
Proof. vm_refl. Qed.
Lemma D_7c0f0 : decode_any W_7c0f0 = Some (OpImm ALU_ADD 13 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7c0f4 : bv 32 := 0x00000713.
Lemma F_7c0f4 : fetch_word AsanUbsan.M.loaded_segments (0x7c144 : word) = Some W_7c0f4.
Proof. vm_refl. Qed.
Lemma D_7c0f4 : decode_any W_7c0f4 = Some (OpImm ALU_ADD 14 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7c0f8 : bv 32 := 0x1e8180ef.
Lemma F_7c0f8 : fetch_word AsanUbsan.M.loaded_segments (0x7c148 : word) = Some W_7c0f8.
Proof. vm_refl. Qed.
Lemma D_7c0f8 : decode_any W_7c0f8 = Some (Jal 1 98792, 4%Z).
Proof. vm_refl. Qed.

Definition W_7c0fc : bv 32 := 0xfffa5517.
Lemma F_7c0fc : fetch_word AsanUbsan.M.loaded_segments (0x7c14c : word) = Some W_7c0fc.
Proof. vm_refl. Qed.
Lemma D_7c0fc : decode_any W_7c0fc = Some (Auipc 10 1048485, 4%Z).
Proof. vm_refl. Qed.

Definition W_7c100 : bv 32 := 0xfffa3597.
Lemma F_7c100 : fetch_word AsanUbsan.M.loaded_segments (0x7c150 : word) = Some W_7c100.
Proof. vm_refl. Qed.
Lemma D_7c100 : decode_any W_7c100 = Some (Auipc 11 1048483, 4%Z).
Proof. vm_refl. Qed.

Definition W_7c104 : bv 32 := 0x2a950513.
Lemma F_7c104 : fetch_word AsanUbsan.M.loaded_segments (0x7c154 : word) = Some W_7c104.
Proof. vm_refl. Qed.
Lemma D_7c104 : decode_any W_7c104 = Some (OpImm ALU_ADD 10 10 681, 4%Z).
Proof. vm_refl. Qed.

Definition W_7c108 : bv 32 := 0xdad58613.
Lemma F_7c108 : fetch_word AsanUbsan.M.loaded_segments (0x7c158 : word) = Some W_7c108.
Proof. vm_refl. Qed.
Lemma D_7c108 : decode_any W_7c108 = Some (OpImm ALU_ADD 12 11 3501, 4%Z).
Proof. vm_refl. Qed.

Definition W_7c10c : bv 32 := 0x02700593.
Lemma F_7c10c : fetch_word AsanUbsan.M.loaded_segments (0x7c15c : word) = Some W_7c10c.
Proof. vm_refl. Qed.
Lemma D_7c10c : decode_any W_7c10c = Some (OpImm ALU_ADD 11 0 39, 4%Z).
Proof. vm_refl. Qed.

Definition W_7c110 : bv 32 := 0x00000693.
Lemma F_7c110 : fetch_word AsanUbsan.M.loaded_segments (0x7c160 : word) = Some W_7c110.
Proof. vm_refl. Qed.
Lemma D_7c110 : decode_any W_7c110 = Some (OpImm ALU_ADD 13 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7c114 : bv 32 := 0x00000713.
Lemma F_7c114 : fetch_word AsanUbsan.M.loaded_segments (0x7c164 : word) = Some W_7c114.
Proof. vm_refl. Qed.
Lemma D_7c114 : decode_any W_7c114 = Some (OpImm ALU_ADD 14 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7c118 : bv 32 := 0x1c8180ef.
Lemma F_7c118 : fetch_word AsanUbsan.M.loaded_segments (0x7c168 : word) = Some W_7c118.
Proof. vm_refl. Qed.
Lemma D_7c118 : decode_any W_7c118 = Some (Jal 1 98760, 4%Z).
Proof. vm_refl. Qed.

Definition W_7c11c : bv 32 := 0x000c1317.
Lemma F_7c11c : fetch_word AsanUbsan.M.loaded_segments (0x7c16c : word) = Some W_7c11c.
Proof. vm_refl. Qed.
Lemma D_7c11c : decode_any W_7c11c = Some (Auipc 6 193, 4%Z).
Proof. vm_refl. Qed.

Definition W_7c120 : bv 32 := 0x79c33303.
Lemma F_7c120 : fetch_word AsanUbsan.M.loaded_segments (0x7c170 : word) = Some W_7c120.
Proof. vm_refl. Qed.
Lemma D_7c120 : decode_any W_7c120 = Some (Load SZ8 true 6 6 1948, 4%Z).
Proof. vm_refl. Qed.

Definition W_7c124 : bv 32 := 0xcc0308e3.
Lemma F_7c124 : fetch_word AsanUbsan.M.loaded_segments (0x7c174 : word) = Some W_7c124.
Proof. vm_refl. Qed.
Lemma D_7c124 : decode_any W_7c124 = Some (Branch BC_EQ 6 0 7376, 4%Z).
Proof. vm_refl. Qed.

Definition W_7c128 : bv 32 := 0x000c1517.
Lemma F_7c128 : fetch_word AsanUbsan.M.loaded_segments (0x7c178 : word) = Some W_7c128.
Proof. vm_refl. Qed.
Lemma D_7c128 : decode_any W_7c128 = Some (Auipc 10 193, 4%Z).
Proof. vm_refl. Qed.

Definition W_7c12c : bv 32 := 0x79853503.
Lemma F_7c12c : fetch_word AsanUbsan.M.loaded_segments (0x7c17c : word) = Some W_7c12c.
Proof. vm_refl. Qed.
Lemma D_7c12c : decode_any W_7c12c = Some (Load SZ8 true 10 10 1944, 4%Z).
Proof. vm_refl. Qed.

Definition W_7c130 : bv 32 := 0x00052503.
Lemma F_7c130 : fetch_word AsanUbsan.M.loaded_segments (0x7c180 : word) = Some W_7c130.
Proof. vm_refl. Qed.
Lemma D_7c130 : decode_any W_7c130 = Some (Load SZ4 true 10 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7c134 : bv 32 := 0x04051c63.
Lemma F_7c134 : fetch_word AsanUbsan.M.loaded_segments (0x7c184 : word) = Some W_7c134.
Proof. vm_refl. Qed.
Lemma D_7c134 : decode_any W_7c134 = Some (Branch BC_NE 10 0 88, 4%Z).
Proof. vm_refl. Qed.

Definition W_7c138 : bv 32 := 0x0000006f.
Lemma F_7c138 : fetch_word AsanUbsan.M.loaded_segments (0x7c188 : word) = Some W_7c138.
Proof. vm_refl. Qed.
Lemma D_7c138 : decode_any W_7c138 = Some (Jal 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7c13c : bv 32 := 0xfffa5517.
Lemma F_7c13c : fetch_word AsanUbsan.M.loaded_segments (0x7c18c : word) = Some W_7c13c.
Proof. vm_refl. Qed.
Lemma D_7c13c : decode_any W_7c13c = Some (Auipc 10 1048485, 4%Z).
Proof. vm_refl. Qed.

Definition W_7c140 : bv 32 := 0xfff97597.
Lemma F_7c140 : fetch_word AsanUbsan.M.loaded_segments (0x7c190 : word) = Some W_7c140.
Proof. vm_refl. Qed.
Lemma D_7c140 : decode_any W_7c140 = Some (Auipc 11 1048471, 4%Z).
Proof. vm_refl. Qed.

Definition W_7c144 : bv 32 := 0x26950513.
Lemma F_7c144 : fetch_word AsanUbsan.M.loaded_segments (0x7c194 : word) = Some W_7c144.
Proof. vm_refl. Qed.
Lemma D_7c144 : decode_any W_7c144 = Some (OpImm ALU_ADD 10 10 617, 4%Z).
Proof. vm_refl. Qed.

Definition W_7c148 : bv 32 := 0x54458613.
Lemma F_7c148 : fetch_word AsanUbsan.M.loaded_segments (0x7c198 : word) = Some W_7c148.
Proof. vm_refl. Qed.
Lemma D_7c148 : decode_any W_7c148 = Some (OpImm ALU_ADD 12 11 1348, 4%Z).
Proof. vm_refl. Qed.

Definition W_7c14c : bv 32 := 0x03000593.
Lemma F_7c14c : fetch_word AsanUbsan.M.loaded_segments (0x7c19c : word) = Some W_7c14c.
Proof. vm_refl. Qed.
Lemma D_7c14c : decode_any W_7c14c = Some (OpImm ALU_ADD 11 0 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_7c150 : bv 32 := 0x00000693.
Lemma F_7c150 : fetch_word AsanUbsan.M.loaded_segments (0x7c1a0 : word) = Some W_7c150.
Proof. vm_refl. Qed.
Lemma D_7c150 : decode_any W_7c150 = Some (OpImm ALU_ADD 13 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7c154 : bv 32 := 0x00000713.
Lemma F_7c154 : fetch_word AsanUbsan.M.loaded_segments (0x7c1a4 : word) = Some W_7c154.
Proof. vm_refl. Qed.
Lemma D_7c154 : decode_any W_7c154 = Some (OpImm ALU_ADD 14 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7c158 : bv 32 := 0x188180ef.
Lemma F_7c158 : fetch_word AsanUbsan.M.loaded_segments (0x7c1a8 : word) = Some W_7c158.
Proof. vm_refl. Qed.
Lemma D_7c158 : decode_any W_7c158 = Some (Jal 1 98696, 4%Z).
Proof. vm_refl. Qed.

Definition W_7c15c : bv 32 := 0xfffa5517.
Lemma F_7c15c : fetch_word AsanUbsan.M.loaded_segments (0x7c1ac : word) = Some W_7c15c.
Proof. vm_refl. Qed.
Lemma D_7c15c : decode_any W_7c15c = Some (Auipc 10 1048485, 4%Z).
Proof. vm_refl. Qed.

Definition W_7c160 : bv 32 := 0xfff9d597.
Lemma F_7c160 : fetch_word AsanUbsan.M.loaded_segments (0x7c1b0 : word) = Some W_7c160.
Proof. vm_refl. Qed.
Lemma D_7c160 : decode_any W_7c160 = Some (Auipc 11 1048477, 4%Z).
Proof. vm_refl. Qed.

Definition W_7c164 : bv 32 := 0x24950513.
Lemma F_7c164 : fetch_word AsanUbsan.M.loaded_segments (0x7c1b4 : word) = Some W_7c164.
Proof. vm_refl. Qed.
Lemma D_7c164 : decode_any W_7c164 = Some (OpImm ALU_ADD 10 10 585, 4%Z).
Proof. vm_refl. Qed.

Definition W_7c168 : bv 32 := 0x2e258613.
Lemma F_7c168 : fetch_word AsanUbsan.M.loaded_segments (0x7c1b8 : word) = Some W_7c168.
Proof. vm_refl. Qed.
Lemma D_7c168 : decode_any W_7c168 = Some (OpImm ALU_ADD 12 11 738, 4%Z).
Proof. vm_refl. Qed.

Definition W_7c16c : bv 32 := 0x03200593.
Lemma F_7c16c : fetch_word AsanUbsan.M.loaded_segments (0x7c1bc : word) = Some W_7c16c.
Proof. vm_refl. Qed.
Lemma D_7c16c : decode_any W_7c16c = Some (OpImm ALU_ADD 11 0 50, 4%Z).
Proof. vm_refl. Qed.

Definition W_7c170 : bv 32 := 0x00000693.
Lemma F_7c170 : fetch_word AsanUbsan.M.loaded_segments (0x7c1c0 : word) = Some W_7c170.
Proof. vm_refl. Qed.
Lemma D_7c170 : decode_any W_7c170 = Some (OpImm ALU_ADD 13 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7c174 : bv 32 := 0x00000713.
Lemma F_7c174 : fetch_word AsanUbsan.M.loaded_segments (0x7c1c4 : word) = Some W_7c174.
Proof. vm_refl. Qed.
Lemma D_7c174 : decode_any W_7c174 = Some (OpImm ALU_ADD 14 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7c178 : bv 32 := 0x168180ef.
Lemma F_7c178 : fetch_word AsanUbsan.M.loaded_segments (0x7c1c8 : word) = Some W_7c178.
Proof. vm_refl. Qed.
Lemma D_7c178 : decode_any W_7c178 = Some (Jal 1 98664, 4%Z).
Proof. vm_refl. Qed.

Definition W_7c17c : bv 32 := 0xfff96517.
Lemma F_7c17c : fetch_word AsanUbsan.M.loaded_segments (0x7c1cc : word) = Some W_7c17c.
Proof. vm_refl. Qed.
Lemma D_7c17c : decode_any W_7c17c = Some (Auipc 10 1048470, 4%Z).
Proof. vm_refl. Qed.

Definition W_7c180 : bv 32 := 0x72250513.
Lemma F_7c180 : fetch_word AsanUbsan.M.loaded_segments (0x7c1d0 : word) = Some W_7c180.
Proof. vm_refl. Qed.
Lemma D_7c180 : decode_any W_7c180 = Some (OpImm ALU_ADD 10 10 1826, 4%Z).
Proof. vm_refl. Qed.

Definition W_7c184 : bv 32 := 0x2ec0d0ef.
Lemma F_7c184 : fetch_word AsanUbsan.M.loaded_segments (0x7c1d4 : word) = Some W_7c184.
Proof. vm_refl. Qed.
Lemma D_7c184 : decode_any W_7c184 = Some (Jal 1 53996, 4%Z).
Proof. vm_refl. Qed.

Definition W_7c188 : bv 32 := 0x08c180ef.
Lemma F_7c188 : fetch_word AsanUbsan.M.loaded_segments (0x7c1d8 : word) = Some W_7c188.
Proof. vm_refl. Qed.
Lemma D_7c188 : decode_any W_7c188 = Some (Jal 1 98444, 4%Z).
Proof. vm_refl. Qed.

Definition W_7c18c : bv 32 := 0x1b01a0ef.
Lemma F_7c18c : fetch_word AsanUbsan.M.loaded_segments (0x7c1dc : word) = Some W_7c18c.
Proof. vm_refl. Qed.
Lemma D_7c18c : decode_any W_7c18c = Some (Jal 1 106928, 4%Z).
Proof. vm_refl. Qed.

Definition W_7c190 : bv 32 := 0x000c1597.
Lemma F_7c190 : fetch_word AsanUbsan.M.loaded_segments (0x7c1e0 : word) = Some W_7c190.
Proof. vm_refl. Qed.
Lemma D_7c190 : decode_any W_7c190 = Some (Auipc 11 193, 4%Z).
Proof. vm_refl. Qed.

Definition W_7c194 : bv 32 := 0x6e85b583.
Lemma F_7c194 : fetch_word AsanUbsan.M.loaded_segments (0x7c1e4 : word) = Some W_7c194.
Proof. vm_refl. Qed.
Lemma D_7c194 : decode_any W_7c194 = Some (Load SZ8 true 11 11 1768, 4%Z).
Proof. vm_refl. Qed.

Definition W_7c198 : bv 32 := 0x0005b583.
Lemma F_7c198 : fetch_word AsanUbsan.M.loaded_segments (0x7c1e8 : word) = Some W_7c198.
Proof. vm_refl. Qed.
Lemma D_7c198 : decode_any W_7c198 = Some (Load SZ8 true 11 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7c19c : bv 32 := 0xfff58613.
Lemma F_7c19c : fetch_word AsanUbsan.M.loaded_segments (0x7c1ec : word) = Some W_7c19c.
Proof. vm_refl. Qed.
Lemma D_7c19c : decode_any W_7c19c = Some (OpImm ALU_ADD 12 11 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_7c1a0 : bv 32 := 0x00c5b6b3.
Lemma F_7c1a0 : fetch_word AsanUbsan.M.loaded_segments (0x7c1f0 : word) = Some W_7c1a0.
Proof. vm_refl. Qed.
Lemma D_7c1a0 : decode_any W_7c1a0 = Some (Op ALU_SLTU 13 11 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_7c1a4 : bv 32 := 0xfff68693.
Lemma F_7c1a4 : fetch_word AsanUbsan.M.loaded_segments (0x7c1f4 : word) = Some W_7c1a4.
Proof. vm_refl. Qed.
Lemma D_7c1a4 : decode_any W_7c1a4 = Some (OpImm ALU_ADD 13 13 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_7c1a8 : bv 32 := 0x00c6f6b3.
Lemma F_7c1a8 : fetch_word AsanUbsan.M.loaded_segments (0x7c1f8 : word) = Some W_7c1a8.
Proof. vm_refl. Qed.
Lemma D_7c1a8 : decode_any W_7c1a8 = Some (Op ALU_AND 13 13 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_7c1ac : bv 32 := 0x04a6f263.
Lemma F_7c1ac : fetch_word AsanUbsan.M.loaded_segments (0x7c1fc : word) = Some W_7c1ac.
Proof. vm_refl. Qed.
Lemma D_7c1ac : decode_any W_7c1ac = Some (Branch BC_GEU 13 10 68, 4%Z).
Proof. vm_refl. Qed.

Definition W_7c1b0 : bv 32 := 0x000c1697.
Lemma F_7c1b0 : fetch_word AsanUbsan.M.loaded_segments (0x7c200 : word) = Some W_7c1b0.
Proof. vm_refl. Qed.
Lemma D_7c1b0 : decode_any W_7c1b0 = Some (Auipc 13 193, 4%Z).
Proof. vm_refl. Qed.

Definition W_7c1b4 : bv 32 := 0x6d06b683.
Lemma F_7c1b4 : fetch_word AsanUbsan.M.loaded_segments (0x7c204 : word) = Some W_7c1b4.
Proof. vm_refl. Qed.
Lemma D_7c1b4 : decode_any W_7c1b4 = Some (Load SZ8 true 13 13 1744, 4%Z).
Proof. vm_refl. Qed.

Definition W_7c1b8 : bv 32 := 0x000c1717.
Lemma F_7c1b8 : fetch_word AsanUbsan.M.loaded_segments (0x7c208 : word) = Some W_7c1b8.
Proof. vm_refl. Qed.
Lemma D_7c1b8 : decode_any W_7c1b8 = Some (Auipc 14 193, 4%Z).
Proof. vm_refl. Qed.

Definition W_7c1bc : bv 32 := 0x6d073703.
Lemma F_7c1bc : fetch_word AsanUbsan.M.loaded_segments (0x7c20c : word) = Some W_7c1bc.
Proof. vm_refl. Qed.
Lemma D_7c1bc : decode_any W_7c1bc = Some (Load SZ8 true 14 14 1744, 4%Z).
Proof. vm_refl. Qed.

Definition W_7c1c0 : bv 32 := 0x0006b803.
Lemma F_7c1c0 : fetch_word AsanUbsan.M.loaded_segments (0x7c210 : word) = Some W_7c1c0.
Proof. vm_refl. Qed.
Lemma D_7c1c0 : decode_any W_7c1c0 = Some (Load SZ8 true 16 13 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7c1c4 : bv 32 := 0x00073683.
Lemma F_7c1c4 : fetch_word AsanUbsan.M.loaded_segments (0x7c214 : word) = Some W_7c1c4.
Proof. vm_refl. Qed.
Lemma D_7c1c4 : decode_any W_7c1c4 = Some (Load SZ8 true 13 14 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7c1c8 : bv 32 := 0xfff80793.
Lemma F_7c1c8 : fetch_word AsanUbsan.M.loaded_segments (0x7c218 : word) = Some W_7c1c8.
Proof. vm_refl. Qed.
Lemma D_7c1c8 : decode_any W_7c1c8 = Some (OpImm ALU_ADD 15 16 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_7c1cc : bv 32 := 0x00a7f463.
Lemma F_7c1cc : fetch_word AsanUbsan.M.loaded_segments (0x7c21c : word) = Some W_7c1cc.
Proof. vm_refl. Qed.
Lemma D_7c1cc : decode_any W_7c1cc = Some (Branch BC_GEU 15 10 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_7c1d4 : bv 32 := 0x000c1717.
Lemma F_7c1d4 : fetch_word AsanUbsan.M.loaded_segments (0x7c224 : word) = Some W_7c1d4.
Proof. vm_refl. Qed.
Lemma D_7c1d4 : decode_any W_7c1d4 = Some (Auipc 14 193, 4%Z).
Proof. vm_refl. Qed.

Definition W_7c1d8 : bv 32 := 0x6bc73703.
Lemma F_7c1d8 : fetch_word AsanUbsan.M.loaded_segments (0x7c228 : word) = Some W_7c1d8.
Proof. vm_refl. Qed.
Lemma D_7c1d8 : decode_any W_7c1d8 = Some (Load SZ8 true 14 14 1724, 4%Z).
Proof. vm_refl. Qed.

Definition W_7c1dc : bv 32 := 0x00073283.
Lemma F_7c1dc : fetch_word AsanUbsan.M.loaded_segments (0x7c22c : word) = Some W_7c1dc.
Proof. vm_refl. Qed.
Lemma D_7c1dc : decode_any W_7c1dc = Some (Load SZ8 true 5 14 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_7c1e0 : bv 32 := 0x0032d713.
Lemma F_7c1e0 : fetch_word AsanUbsan.M.loaded_segments (0x7c230 : word) = Some W_7c1e0.
Proof. vm_refl. Qed.
Lemma D_7c1e0 : decode_any W_7c1e0 = Some (ShiftImm ALU_SRL 14 5 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_7c1e4 : bv 32 := 0x00b708b3.
Lemma F_7c1e4 : fetch_word AsanUbsan.M.loaded_segments (0x7c234 : word) = Some W_7c1e4.
Proof. vm_refl. Qed.
Lemma D_7c1e4 : decode_any W_7c1e4 = Some (Op ALU_ADD 17 14 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_7c1e8 : bv 32 := 0x00a2ea63.
Lemma F_7c1e8 : fetch_word AsanUbsan.M.loaded_segments (0x7c238 : word) = Some W_7c1e8.
Proof. vm_refl. Qed.
Lemma D_7c1e8 : decode_any W_7c1e8 = Some (Branch BC_LTU 5 10 20, 4%Z).
Proof. vm_refl. Qed.

Definition W_7c1ec : bv 32 := 0x00a8f863.
Lemma F_7c1ec : fetch_word AsanUbsan.M.loaded_segments (0x7c23c : word) = Some W_7c1ec.
Proof. vm_refl. Qed.
Lemma D_7c1ec : decode_any W_7c1ec = Some (Branch BC_GEU 17 10 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_7c1f0 : bv 32 := 0x00355513.
Lemma F_7c1f0 : fetch_word AsanUbsan.M.loaded_segments (0x7c240 : word) = Some W_7c1f0.
Proof. vm_refl. Qed.
Lemma D_7c1f0 : decode_any W_7c1f0 = Some (ShiftImm ALU_SRL 10 10 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_7c1f4 : bv 32 := 0x00a58533.
Lemma F_7c1f4 : fetch_word AsanUbsan.M.loaded_segments (0x7c244 : word) = Some W_7c1f4.
Proof. vm_refl. Qed.
Lemma D_7c1f4 : decode_any W_7c1f4 = Some (Op ALU_ADD 10 11 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_7c1f8 : bv 32 := 0x00008067.
Lemma F_7c1f8 : fetch_word AsanUbsan.M.loaded_segments (0x7c248 : word) = Some W_7c1f8.
Proof. vm_refl. Qed.
Lemma D_7c1f8 : decode_any W_7c1f8 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.
