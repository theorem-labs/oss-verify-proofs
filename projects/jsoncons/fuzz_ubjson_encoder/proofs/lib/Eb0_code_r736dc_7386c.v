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

Definition W_8eae4 : bv 32 := 0x00060693.
Lemma F_8eae4 : fetch_word AsanUbsan.M.loaded_segments (0x8eb34 : word) = Some W_8eae4.
Proof. vm_refl. Qed.
Lemma D_8eae4 : decode_any W_8eae4 = Some (OpImm ALU_ADD 13 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_8eae8 : bv 32 := 0x00000613.
Lemma F_8eae8 : fetch_word AsanUbsan.M.loaded_segments (0x8eb38 : word) = Some W_8eae8.
Proof. vm_refl. Qed.
Lemma D_8eae8 : decode_any W_8eae8 = Some (OpImm ALU_ADD 12 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_8eaec : bv 32 := 0x0040006f.
Lemma F_8eaec : fetch_word AsanUbsan.M.loaded_segments (0x8eb3c : word) = Some W_8eaec.
Proof. vm_refl. Qed.
Lemma D_8eaec : decode_any W_8eaec = Some (Jal 0 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_8eaf0 : bv 32 := 0xfa010113.
Lemma F_8eaf0 : fetch_word AsanUbsan.M.loaded_segments (0x8eb40 : word) = Some W_8eaf0.
Proof. vm_refl. Qed.
Lemma D_8eaf0 : decode_any W_8eaf0 = Some (OpImm ALU_ADD 2 2 4000, 4%Z).
Proof. vm_refl. Qed.

Definition W_8eaf4 : bv 32 := 0x04113c23.
Lemma F_8eaf4 : fetch_word AsanUbsan.M.loaded_segments (0x8eb44 : word) = Some W_8eaf4.
Proof. vm_refl. Qed.
Lemma D_8eaf4 : decode_any W_8eaf4 = Some (Store SZ8 2 1 88, 4%Z).
Proof. vm_refl. Qed.

Definition W_8eaf8 : bv 32 := 0x04813823.
Lemma F_8eaf8 : fetch_word AsanUbsan.M.loaded_segments (0x8eb48 : word) = Some W_8eaf8.
Proof. vm_refl. Qed.
Lemma D_8eaf8 : decode_any W_8eaf8 = Some (Store SZ8 2 8 80, 4%Z).
Proof. vm_refl. Qed.

Definition W_8eafc : bv 32 := 0x04913423.
Lemma F_8eafc : fetch_word AsanUbsan.M.loaded_segments (0x8eb4c : word) = Some W_8eafc.
Proof. vm_refl. Qed.
Lemma D_8eafc : decode_any W_8eafc = Some (Store SZ8 2 9 72, 4%Z).
Proof. vm_refl. Qed.

Definition W_8eb00 : bv 32 := 0x05213023.
Lemma F_8eb00 : fetch_word AsanUbsan.M.loaded_segments (0x8eb50 : word) = Some W_8eb00.
Proof. vm_refl. Qed.
Lemma D_8eb00 : decode_any W_8eb00 = Some (Store SZ8 2 18 64, 4%Z).
Proof. vm_refl. Qed.

Definition W_8eb04 : bv 32 := 0x03313c23.
Lemma F_8eb04 : fetch_word AsanUbsan.M.loaded_segments (0x8eb54 : word) = Some W_8eb04.
Proof. vm_refl. Qed.
Lemma D_8eb04 : decode_any W_8eb04 = Some (Store SZ8 2 19 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_8eb08 : bv 32 := 0x03413823.
Lemma F_8eb08 : fetch_word AsanUbsan.M.loaded_segments (0x8eb58 : word) = Some W_8eb08.
Proof. vm_refl. Qed.
Lemma D_8eb08 : decode_any W_8eb08 = Some (Store SZ8 2 20 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_8eb0c : bv 32 := 0x00068993.
Lemma F_8eb0c : fetch_word AsanUbsan.M.loaded_segments (0x8eb5c : word) = Some W_8eb0c.
Proof. vm_refl. Qed.
Lemma D_8eb0c : decode_any W_8eb0c = Some (OpImm ALU_ADD 19 13 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_8eb10 : bv 32 := 0x00060493.
Lemma F_8eb10 : fetch_word AsanUbsan.M.loaded_segments (0x8eb60 : word) = Some W_8eb10.
Proof. vm_refl. Qed.
Lemma D_8eb10 : decode_any W_8eb10 = Some (OpImm ALU_ADD 9 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_8eb14 : bv 32 := 0x00058413.
Lemma F_8eb14 : fetch_word AsanUbsan.M.loaded_segments (0x8eb64 : word) = Some W_8eb14.
Proof. vm_refl. Qed.
Lemma D_8eb14 : decode_any W_8eb14 = Some (OpImm ALU_ADD 8 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_8eb18 : bv 32 := 0x000af597.
Lemma F_8eb18 : fetch_word AsanUbsan.M.loaded_segments (0x8eb68 : word) = Some W_8eb18.
Proof. vm_refl. Qed.
Lemma D_8eb18 : decode_any W_8eb18 = Some (Auipc 11 175, 4%Z).
Proof. vm_refl. Qed.

Definition W_8eb1c : bv 32 := 0xd405ba03.
Lemma F_8eb1c : fetch_word AsanUbsan.M.loaded_segments (0x8eb6c : word) = Some W_8eb1c.
Proof. vm_refl. Qed.
Lemma D_8eb1c : decode_any W_8eb1c = Some (Load SZ8 true 20 11 3392, 4%Z).
Proof. vm_refl. Qed.

Definition W_8eb20 : bv 32 := 0x000a3583.
Lemma F_8eb20 : fetch_word AsanUbsan.M.loaded_segments (0x8eb70 : word) = Some W_8eb20.
Proof. vm_refl. Qed.
Lemma D_8eb20 : decode_any W_8eb20 = Some (Load SZ8 true 11 20 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_8eb24 : bv 32 := 0x00050913.
Lemma F_8eb24 : fetch_word AsanUbsan.M.loaded_segments (0x8eb74 : word) = Some W_8eb24.
Proof. vm_refl. Qed.
Lemma D_8eb24 : decode_any W_8eb24 = Some (OpImm ALU_ADD 18 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_8eb28 : bv 32 := 0x00059863.
Lemma F_8eb28 : fetch_word AsanUbsan.M.loaded_segments (0x8eb78 : word) = Some W_8eb28.
Proof. vm_refl. Qed.
Lemma D_8eb28 : decode_any W_8eb28 = Some (Branch BC_NE 11 0 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_8eb38 : bv 32 := 0xfff58513.
Lemma F_8eb38 : fetch_word AsanUbsan.M.loaded_segments (0x8eb88 : word) = Some W_8eb38.
Proof. vm_refl. Qed.
Lemma D_8eb38 : decode_any W_8eb38 = Some (OpImm ALU_ADD 10 11 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_8eb3c : bv 32 := 0x00a5f533.
Lemma F_8eb3c : fetch_word AsanUbsan.M.loaded_segments (0x8eb8c : word) = Some W_8eb3c.
Proof. vm_refl. Qed.
Lemma D_8eb3c : decode_any W_8eb3c = Some (Op ALU_AND 10 11 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_8eb40 : bv 32 := 0x0a051863.
Lemma F_8eb40 : fetch_word AsanUbsan.M.loaded_segments (0x8eb90 : word) = Some W_8eb40.
Proof. vm_refl. Qed.
Lemma D_8eb40 : decode_any W_8eb40 = Some (Branch BC_NE 10 0 176, 4%Z).
Proof. vm_refl. Qed.

Definition W_8eb44 : bv 32 := 0x00b40433.
Lemma F_8eb44 : fetch_word AsanUbsan.M.loaded_segments (0x8eb94 : word) = Some W_8eb44.
Proof. vm_refl. Qed.
Lemma D_8eb44 : decode_any W_8eb44 = Some (Op ALU_ADD 8 8 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_8eb48 : bv 32 := 0xfff40413.
Lemma F_8eb48 : fetch_word AsanUbsan.M.loaded_segments (0x8eb98 : word) = Some W_8eb48.
Proof. vm_refl. Qed.
Lemma D_8eb48 : decode_any W_8eb48 = Some (OpImm ALU_ADD 8 8 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_8eb4c : bv 32 := 0x40b00533.
Lemma F_8eb4c : fetch_word AsanUbsan.M.loaded_segments (0x8eb9c : word) = Some W_8eb4c.
Proof. vm_refl. Qed.
Lemma D_8eb4c : decode_any W_8eb4c = Some (Op ALU_SUB 10 0 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_8eb50 : bv 32 := 0x00a47433.
Lemma F_8eb50 : fetch_word AsanUbsan.M.loaded_segments (0x8eba0 : word) = Some W_8eb50.
Proof. vm_refl. Qed.
Lemma D_8eb50 : decode_any W_8eb50 = Some (Op ALU_AND 8 8 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_8eb54 : bv 32 := 0x00059863.
Lemma F_8eb54 : fetch_word AsanUbsan.M.loaded_segments (0x8eba4 : word) = Some W_8eb54.
Proof. vm_refl. Qed.
Lemma D_8eb54 : decode_any W_8eb54 = Some (Branch BC_NE 11 0 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_8eb64 : bv 32 := 0x00a97933.
Lemma F_8eb64 : fetch_word AsanUbsan.M.loaded_segments (0x8ebb4 : word) = Some W_8eb64.
Proof. vm_refl. Qed.
Lemma D_8eb64 : decode_any W_8eb64 = Some (Op ALU_AND 18 18 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_8eb68 : bv 32 := 0x03200513.
Lemma F_8eb68 : fetch_word AsanUbsan.M.loaded_segments (0x8ebb8 : word) = Some W_8eb68.
Proof. vm_refl. Qed.
Lemma D_8eb68 : decode_any W_8eb68 = Some (OpImm ALU_ADD 10 0 50, 4%Z).
Proof. vm_refl. Qed.

Definition W_8eb6c : bv 32 := 0x00a12023.
Lemma F_8eb6c : fetch_word AsanUbsan.M.loaded_segments (0x8ebbc : word) = Some W_8eb6c.
Proof. vm_refl. Qed.
Lemma D_8eb6c : decode_any W_8eb6c = Some (Store SZ4 2 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_8eb70 : bv 32 := 0x00010613.
Lemma F_8eb70 : fetch_word AsanUbsan.M.loaded_segments (0x8ebc0 : word) = Some W_8eb70.
Proof. vm_refl. Qed.
Lemma D_8eb70 : decode_any W_8eb70 = Some (OpImm ALU_ADD 12 2 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_8eb74 : bv 32 := 0x00098513.
Lemma F_8eb74 : fetch_word AsanUbsan.M.loaded_segments (0x8ebc4 : word) = Some W_8eb74.
Proof. vm_refl. Qed.
Lemma D_8eb74 : decode_any W_8eb74 = Some (OpImm ALU_ADD 10 19 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_8eb78 : bv 32 := 0x00040593.
Lemma F_8eb78 : fetch_word AsanUbsan.M.loaded_segments (0x8ebc8 : word) = Some W_8eb78.
Proof. vm_refl. Qed.
Lemma D_8eb78 : decode_any W_8eb78 = Some (OpImm ALU_ADD 11 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_8eb7c : bv 32 := 0x608000ef.
Lemma F_8eb7c : fetch_word AsanUbsan.M.loaded_segments (0x8ebcc : word) = Some W_8eb7c.
Proof. vm_refl. Qed.
Lemma D_8eb7c : decode_any W_8eb7c = Some (Jal 1 1544, 4%Z).
Proof. vm_refl. Qed.

Definition W_8eb80 : bv 32 := 0x00012683.
Lemma F_8eb80 : fetch_word AsanUbsan.M.loaded_segments (0x8ebd0 : word) = Some W_8eb80.
Proof. vm_refl. Qed.
Lemma D_8eb80 : decode_any W_8eb80 = Some (Load SZ4 true 13 2 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_8eb84 : bv 32 := 0x00050713.
Lemma F_8eb84 : fetch_word AsanUbsan.M.loaded_segments (0x8ebd4 : word) = Some W_8eb84.
Proof. vm_refl. Qed.
Lemma D_8eb84 : decode_any W_8eb84 = Some (OpImm ALU_ADD 14 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_8eb88 : bv 32 := 0x00300613.
Lemma F_8eb88 : fetch_word AsanUbsan.M.loaded_segments (0x8ebd8 : word) = Some W_8eb88.
Proof. vm_refl. Qed.
Lemma D_8eb88 : decode_any W_8eb88 = Some (OpImm ALU_ADD 12 0 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_8eb8c : bv 32 := 0x00090513.
Lemma F_8eb8c : fetch_word AsanUbsan.M.loaded_segments (0x8ebdc : word) = Some W_8eb8c.
Proof. vm_refl. Qed.
Lemma D_8eb8c : decode_any W_8eb8c = Some (OpImm ALU_ADD 10 18 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_8eb90 : bv 32 := 0x00040593.
Lemma F_8eb90 : fetch_word AsanUbsan.M.loaded_segments (0x8ebe0 : word) = Some W_8eb90.
Proof. vm_refl. Qed.
Lemma D_8eb90 : decode_any W_8eb90 = Some (OpImm ALU_ADD 11 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_8eb94 : bv 32 := 0x00000793.
Lemma F_8eb94 : fetch_word AsanUbsan.M.loaded_segments (0x8ebe4 : word) = Some W_8eb94.
Proof. vm_refl. Qed.
Lemma D_8eb94 : decode_any W_8eb94 = Some (OpImm ALU_ADD 15 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_8eb98 : bv 32 := 0xa40fe0ef.
Lemma F_8eb98 : fetch_word AsanUbsan.M.loaded_segments (0x8ebe8 : word) = Some W_8eb98.
Proof. vm_refl. Qed.
Lemma D_8eb98 : decode_any W_8eb98 = Some (Jal 1 2089536, 4%Z).
Proof. vm_refl. Qed.

Definition W_8eb9c : bv 32 := 0x00050993.
Lemma F_8eb9c : fetch_word AsanUbsan.M.loaded_segments (0x8ebec : word) = Some W_8eb9c.
Proof. vm_refl. Qed.
Lemma D_8eb9c : decode_any W_8eb9c = Some (OpImm ALU_ADD 19 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_8eba0 : bv 32 := 0x00000593.
Lemma F_8eba0 : fetch_word AsanUbsan.M.loaded_segments (0x8ebf0 : word) = Some W_8eba0.
Proof. vm_refl. Qed.
Lemma D_8eba0 : decode_any W_8eba0 = Some (OpImm ALU_ADD 11 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_8eba4 : bv 32 := 0xa14fe0ef.
Lemma F_8eba4 : fetch_word AsanUbsan.M.loaded_segments (0x8ebf4 : word) = Some W_8eba4.
Proof. vm_refl. Qed.
Lemma D_8eba4 : decode_any W_8eba4 = Some (Jal 1 2089492, 4%Z).
Proof. vm_refl. Qed.

Definition W_8eba8 : bv 32 := 0xaaaab537.
Lemma F_8eba8 : fetch_word AsanUbsan.M.loaded_segments (0x8ebf8 : word) = Some W_8eba8.
Proof. vm_refl. Qed.
Lemma D_8eba8 : decode_any W_8eba8 = Some (Lui 10 699051, 4%Z).
Proof. vm_refl. Qed.

Definition W_8ebac : bv 32 := 0xaaa50513.
Lemma F_8ebac : fetch_word AsanUbsan.M.loaded_segments (0x8ebfc : word) = Some W_8ebac.
Proof. vm_refl. Qed.
Lemma D_8ebac : decode_any W_8ebac = Some (OpImm ALU_ADD 10 10 2730, 4%Z).
Proof. vm_refl. Qed.

Definition W_8ebb0 : bv 32 := 0x02a12623.
Lemma F_8ebb0 : fetch_word AsanUbsan.M.loaded_segments (0x8ec00 : word) = Some W_8ebb0.
Proof. vm_refl. Qed.
Lemma D_8ebb0 : decode_any W_8ebb0 = Some (Store SZ4 2 10 44, 4%Z).
Proof. vm_refl. Qed.

Definition W_8ebb4 : bv 32 := 0x02c10593.
Lemma F_8ebb4 : fetch_word AsanUbsan.M.loaded_segments (0x8ec04 : word) = Some W_8ebb4.
Proof. vm_refl. Qed.
Lemma D_8ebb4 : decode_any W_8ebb4 = Some (OpImm ALU_ADD 11 2 44, 4%Z).
Proof. vm_refl. Qed.

Definition W_8ebb8 : bv 32 := 0x00098513.
Lemma F_8ebb8 : fetch_word AsanUbsan.M.loaded_segments (0x8ec08 : word) = Some W_8ebb8.
Proof. vm_refl. Qed.
Lemma D_8ebb8 : decode_any W_8ebb8 = Some (OpImm ALU_ADD 10 19 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_8ebbc : bv 32 := 0x9fcfe0ef.
Lemma F_8ebbc : fetch_word AsanUbsan.M.loaded_segments (0x8ec0c : word) = Some W_8ebbc.
Proof. vm_refl. Qed.
Lemma D_8ebbc : decode_any W_8ebbc = Some (Jal 1 2089468, 4%Z).
Proof. vm_refl. Qed.

Definition W_8ebc0 : bv 32 := 0x04051063.
Lemma F_8ebc0 : fetch_word AsanUbsan.M.loaded_segments (0x8ec10 : word) = Some W_8ebc0.
Proof. vm_refl. Qed.
Lemma D_8ebc0 : decode_any W_8ebc0 = Some (Branch BC_NE 10 0 64, 4%Z).
Proof. vm_refl. Qed.

Definition W_8ebc4 : bv 32 := 0x00040513.
Lemma F_8ebc4 : fetch_word AsanUbsan.M.loaded_segments (0x8ec14 : word) = Some W_8ebc4.
Proof. vm_refl. Qed.
Lemma D_8ebc4 : decode_any W_8ebc4 = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_8ebc8 : bv 32 := 0x8d8fa0ef.
Lemma F_8ebc8 : fetch_word AsanUbsan.M.loaded_segments (0x8ec18 : word) = Some W_8ebc8.
Proof. vm_refl. Qed.
Lemma D_8ebc8 : decode_any W_8ebc8 = Some (Jal 1 2072792, 4%Z).
Proof. vm_refl. Qed.

Definition W_8ebcc : bv 32 := 0x00098513.
Lemma F_8ebcc : fetch_word AsanUbsan.M.loaded_segments (0x8ec1c : word) = Some W_8ebcc.
Proof. vm_refl. Qed.
Lemma D_8ebcc : decode_any W_8ebcc = Some (OpImm ALU_ADD 10 19 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_8ebd0 : bv 32 := 0x05813083.
Lemma F_8ebd0 : fetch_word AsanUbsan.M.loaded_segments (0x8ec20 : word) = Some W_8ebd0.
Proof. vm_refl. Qed.
Lemma D_8ebd0 : decode_any W_8ebd0 = Some (Load SZ8 true 1 2 88, 4%Z).
Proof. vm_refl. Qed.

Definition W_8ebd4 : bv 32 := 0x05013403.
Lemma F_8ebd4 : fetch_word AsanUbsan.M.loaded_segments (0x8ec24 : word) = Some W_8ebd4.
Proof. vm_refl. Qed.
Lemma D_8ebd4 : decode_any W_8ebd4 = Some (Load SZ8 true 8 2 80, 4%Z).
Proof. vm_refl. Qed.

Definition W_8ebd8 : bv 32 := 0x04813483.
Lemma F_8ebd8 : fetch_word AsanUbsan.M.loaded_segments (0x8ec28 : word) = Some W_8ebd8.
Proof. vm_refl. Qed.
Lemma D_8ebd8 : decode_any W_8ebd8 = Some (Load SZ8 true 9 2 72, 4%Z).
Proof. vm_refl. Qed.

Definition W_8ebdc : bv 32 := 0x04013903.
Lemma F_8ebdc : fetch_word AsanUbsan.M.loaded_segments (0x8ec2c : word) = Some W_8ebdc.
Proof. vm_refl. Qed.
Lemma D_8ebdc : decode_any W_8ebdc = Some (Load SZ8 true 18 2 64, 4%Z).
Proof. vm_refl. Qed.

Definition W_8ebe0 : bv 32 := 0x03813983.
Lemma F_8ebe0 : fetch_word AsanUbsan.M.loaded_segments (0x8ec30 : word) = Some W_8ebe0.
Proof. vm_refl. Qed.
Lemma D_8ebe0 : decode_any W_8ebe0 = Some (Load SZ8 true 19 2 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_8ebe4 : bv 32 := 0x03013a03.
Lemma F_8ebe4 : fetch_word AsanUbsan.M.loaded_segments (0x8ec34 : word) = Some W_8ebe4.
Proof. vm_refl. Qed.
Lemma D_8ebe4 : decode_any W_8ebe4 = Some (Load SZ8 true 20 2 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_8ebe8 : bv 32 := 0x06010113.
Lemma F_8ebe8 : fetch_word AsanUbsan.M.loaded_segments (0x8ec38 : word) = Some W_8ebe8.
Proof. vm_refl. Qed.
Lemma D_8ebe8 : decode_any W_8ebe8 = Some (OpImm ALU_ADD 2 2 96, 4%Z).
Proof. vm_refl. Qed.

Definition W_8ebec : bv 32 := 0x00008067.
Lemma F_8ebec : fetch_word AsanUbsan.M.loaded_segments (0x8ec3c : word) = Some W_8ebec.
Proof. vm_refl. Qed.
Lemma D_8ebec : decode_any W_8ebec = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_8ec68 : bv 32 := 0x00060693.
Lemma F_8ec68 : fetch_word AsanUbsan.M.loaded_segments (0x8ecb8 : word) = Some W_8ec68.
Proof. vm_refl. Qed.
Lemma D_8ec68 : decode_any W_8ec68 = Some (OpImm ALU_ADD 13 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_8ec6c : bv 32 := 0x00100613.
Lemma F_8ec6c : fetch_word AsanUbsan.M.loaded_segments (0x8ecbc : word) = Some W_8ec6c.
Proof. vm_refl. Qed.
Lemma D_8ec6c : decode_any W_8ec6c = Some (OpImm ALU_ADD 12 0 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_8ec70 : bv 32 := 0xe81ff06f.
Lemma F_8ec70 : fetch_word AsanUbsan.M.loaded_segments (0x8ecc0 : word) = Some W_8ec70.
Proof. vm_refl. Qed.
Lemma D_8ec70 : decode_any W_8ec70 = Some (Jal 0 2096768, 4%Z).
Proof. vm_refl. Qed.
