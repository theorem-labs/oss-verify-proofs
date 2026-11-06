(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.jsoncons.fuzz_bigint.images Require Import AsanUbsan.
Open Scope bv_scope.

Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

Definition W_73aec : bv 32 := 0x00060693.
Lemma F_73aec : fetch_word AsanUbsan.M.loaded_segments (0x73aec : word) = Some W_73aec.
Proof. vm_refl. Qed.
Lemma D_73aec : decode_any W_73aec = Some (OpImm ALU_ADD 13 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_73af0 : bv 32 := 0x00000613.
Lemma F_73af0 : fetch_word AsanUbsan.M.loaded_segments (0x73af0 : word) = Some W_73af0.
Proof. vm_refl. Qed.
Lemma D_73af0 : decode_any W_73af0 = Some (OpImm ALU_ADD 12 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_73af4 : bv 32 := 0x0040006f.
Lemma F_73af4 : fetch_word AsanUbsan.M.loaded_segments (0x73af4 : word) = Some W_73af4.
Proof. vm_refl. Qed.
Lemma D_73af4 : decode_any W_73af4 = Some (Jal 0 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_73af8 : bv 32 := 0xfa010113.
Lemma F_73af8 : fetch_word AsanUbsan.M.loaded_segments (0x73af8 : word) = Some W_73af8.
Proof. vm_refl. Qed.
Lemma D_73af8 : decode_any W_73af8 = Some (OpImm ALU_ADD 2 2 4000, 4%Z).
Proof. vm_refl. Qed.

Definition W_73afc : bv 32 := 0x04113c23.
Lemma F_73afc : fetch_word AsanUbsan.M.loaded_segments (0x73afc : word) = Some W_73afc.
Proof. vm_refl. Qed.
Lemma D_73afc : decode_any W_73afc = Some (Store SZ8 2 1 88, 4%Z).
Proof. vm_refl. Qed.

Definition W_73b00 : bv 32 := 0x04813823.
Lemma F_73b00 : fetch_word AsanUbsan.M.loaded_segments (0x73b00 : word) = Some W_73b00.
Proof. vm_refl. Qed.
Lemma D_73b00 : decode_any W_73b00 = Some (Store SZ8 2 8 80, 4%Z).
Proof. vm_refl. Qed.

Definition W_73b04 : bv 32 := 0x04913423.
Lemma F_73b04 : fetch_word AsanUbsan.M.loaded_segments (0x73b04 : word) = Some W_73b04.
Proof. vm_refl. Qed.
Lemma D_73b04 : decode_any W_73b04 = Some (Store SZ8 2 9 72, 4%Z).
Proof. vm_refl. Qed.

Definition W_73b08 : bv 32 := 0x05213023.
Lemma F_73b08 : fetch_word AsanUbsan.M.loaded_segments (0x73b08 : word) = Some W_73b08.
Proof. vm_refl. Qed.
Lemma D_73b08 : decode_any W_73b08 = Some (Store SZ8 2 18 64, 4%Z).
Proof. vm_refl. Qed.

Definition W_73b0c : bv 32 := 0x03313c23.
Lemma F_73b0c : fetch_word AsanUbsan.M.loaded_segments (0x73b0c : word) = Some W_73b0c.
Proof. vm_refl. Qed.
Lemma D_73b0c : decode_any W_73b0c = Some (Store SZ8 2 19 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_73b10 : bv 32 := 0x03413823.
Lemma F_73b10 : fetch_word AsanUbsan.M.loaded_segments (0x73b10 : word) = Some W_73b10.
Proof. vm_refl. Qed.
Lemma D_73b10 : decode_any W_73b10 = Some (Store SZ8 2 20 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_73b14 : bv 32 := 0x00068993.
Lemma F_73b14 : fetch_word AsanUbsan.M.loaded_segments (0x73b14 : word) = Some W_73b14.
Proof. vm_refl. Qed.
Lemma D_73b14 : decode_any W_73b14 = Some (OpImm ALU_ADD 19 13 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_73b18 : bv 32 := 0x00060493.
Lemma F_73b18 : fetch_word AsanUbsan.M.loaded_segments (0x73b18 : word) = Some W_73b18.
Proof. vm_refl. Qed.
Lemma D_73b18 : decode_any W_73b18 = Some (OpImm ALU_ADD 9 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_73b1c : bv 32 := 0x00058413.
Lemma F_73b1c : fetch_word AsanUbsan.M.loaded_segments (0x73b1c : word) = Some W_73b1c.
Proof. vm_refl. Qed.
Lemma D_73b1c : decode_any W_73b1c = Some (OpImm ALU_ADD 8 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_73b20 : bv 32 := 0x00063597.
Lemma F_73b20 : fetch_word AsanUbsan.M.loaded_segments (0x73b20 : word) = Some W_73b20.
Proof. vm_refl. Qed.
Lemma D_73b20 : decode_any W_73b20 = Some (Auipc 11 99, 4%Z).
Proof. vm_refl. Qed.

Definition W_73b24 : bv 32 := 0x9885ba03.
Lemma F_73b24 : fetch_word AsanUbsan.M.loaded_segments (0x73b24 : word) = Some W_73b24.
Proof. vm_refl. Qed.
Lemma D_73b24 : decode_any W_73b24 = Some (Load SZ8 true 20 11 2440, 4%Z).
Proof. vm_refl. Qed.

Definition W_73b28 : bv 32 := 0x000a3583.
Lemma F_73b28 : fetch_word AsanUbsan.M.loaded_segments (0x73b28 : word) = Some W_73b28.
Proof. vm_refl. Qed.
Lemma D_73b28 : decode_any W_73b28 = Some (Load SZ8 true 11 20 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_73b2c : bv 32 := 0x00050913.
Lemma F_73b2c : fetch_word AsanUbsan.M.loaded_segments (0x73b2c : word) = Some W_73b2c.
Proof. vm_refl. Qed.
Lemma D_73b2c : decode_any W_73b2c = Some (OpImm ALU_ADD 18 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_73b30 : bv 32 := 0x00059863.
Lemma F_73b30 : fetch_word AsanUbsan.M.loaded_segments (0x73b30 : word) = Some W_73b30.
Proof. vm_refl. Qed.
Lemma D_73b30 : decode_any W_73b30 = Some (Branch BC_NE 11 0 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_73b34 : bv 32 := 0x9d8ff0ef.
Lemma F_73b34 : fetch_word AsanUbsan.M.loaded_segments (0x73b34 : word) = Some W_73b34.
Proof. vm_refl. Qed.
Lemma D_73b34 : decode_any W_73b34 = Some (Jal 1 2093528, 4%Z).
Proof. vm_refl. Qed.

Definition W_73b38 : bv 32 := 0x00050593.
Lemma F_73b38 : fetch_word AsanUbsan.M.loaded_segments (0x73b38 : word) = Some W_73b38.
Proof. vm_refl. Qed.
Lemma D_73b38 : decode_any W_73b38 = Some (OpImm ALU_ADD 11 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_73b3c : bv 32 := 0x00aa3023.
Lemma F_73b3c : fetch_word AsanUbsan.M.loaded_segments (0x73b3c : word) = Some W_73b3c.
Proof. vm_refl. Qed.
Lemma D_73b3c : decode_any W_73b3c = Some (Store SZ8 20 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_73b40 : bv 32 := 0xfff58513.
Lemma F_73b40 : fetch_word AsanUbsan.M.loaded_segments (0x73b40 : word) = Some W_73b40.
Proof. vm_refl. Qed.
Lemma D_73b40 : decode_any W_73b40 = Some (OpImm ALU_ADD 10 11 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_73b44 : bv 32 := 0x00a5f533.
Lemma F_73b44 : fetch_word AsanUbsan.M.loaded_segments (0x73b44 : word) = Some W_73b44.
Proof. vm_refl. Qed.
Lemma D_73b44 : decode_any W_73b44 = Some (Op ALU_AND 10 11 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_73b48 : bv 32 := 0x0a051863.
Lemma F_73b48 : fetch_word AsanUbsan.M.loaded_segments (0x73b48 : word) = Some W_73b48.
Proof. vm_refl. Qed.
Lemma D_73b48 : decode_any W_73b48 = Some (Branch BC_NE 10 0 176, 4%Z).
Proof. vm_refl. Qed.

Definition W_73b4c : bv 32 := 0x00b40433.
Lemma F_73b4c : fetch_word AsanUbsan.M.loaded_segments (0x73b4c : word) = Some W_73b4c.
Proof. vm_refl. Qed.
Lemma D_73b4c : decode_any W_73b4c = Some (Op ALU_ADD 8 8 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_73b50 : bv 32 := 0xfff40413.
Lemma F_73b50 : fetch_word AsanUbsan.M.loaded_segments (0x73b50 : word) = Some W_73b50.
Proof. vm_refl. Qed.
Lemma D_73b50 : decode_any W_73b50 = Some (OpImm ALU_ADD 8 8 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_73b54 : bv 32 := 0x40b00533.
Lemma F_73b54 : fetch_word AsanUbsan.M.loaded_segments (0x73b54 : word) = Some W_73b54.
Proof. vm_refl. Qed.
Lemma D_73b54 : decode_any W_73b54 = Some (Op ALU_SUB 10 0 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_73b58 : bv 32 := 0x00a47433.
Lemma F_73b58 : fetch_word AsanUbsan.M.loaded_segments (0x73b58 : word) = Some W_73b58.
Proof. vm_refl. Qed.
Lemma D_73b58 : decode_any W_73b58 = Some (Op ALU_AND 8 8 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_73b5c : bv 32 := 0x00059863.
Lemma F_73b5c : fetch_word AsanUbsan.M.loaded_segments (0x73b5c : word) = Some W_73b5c.
Proof. vm_refl. Qed.
Lemma D_73b5c : decode_any W_73b5c = Some (Branch BC_NE 11 0 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_73b60 : bv 32 := 0x9acff0ef.
Lemma F_73b60 : fetch_word AsanUbsan.M.loaded_segments (0x73b60 : word) = Some W_73b60.
Proof. vm_refl. Qed.
Lemma D_73b60 : decode_any W_73b60 = Some (Jal 1 2093484, 4%Z).
Proof. vm_refl. Qed.

Definition W_73b64 : bv 32 := 0x00aa3023.
Lemma F_73b64 : fetch_word AsanUbsan.M.loaded_segments (0x73b64 : word) = Some W_73b64.
Proof. vm_refl. Qed.
Lemma D_73b64 : decode_any W_73b64 = Some (Store SZ8 20 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_73b68 : bv 32 := 0x40a00533.
Lemma F_73b68 : fetch_word AsanUbsan.M.loaded_segments (0x73b68 : word) = Some W_73b68.
Proof. vm_refl. Qed.
Lemma D_73b68 : decode_any W_73b68 = Some (Op ALU_SUB 10 0 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_73b6c : bv 32 := 0x00a97933.
Lemma F_73b6c : fetch_word AsanUbsan.M.loaded_segments (0x73b6c : word) = Some W_73b6c.
Proof. vm_refl. Qed.
Lemma D_73b6c : decode_any W_73b6c = Some (Op ALU_AND 18 18 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_73b70 : bv 32 := 0x03200513.
Lemma F_73b70 : fetch_word AsanUbsan.M.loaded_segments (0x73b70 : word) = Some W_73b70.
Proof. vm_refl. Qed.
Lemma D_73b70 : decode_any W_73b70 = Some (OpImm ALU_ADD 10 0 50, 4%Z).
Proof. vm_refl. Qed.

Definition W_73b74 : bv 32 := 0x00a12023.
Lemma F_73b74 : fetch_word AsanUbsan.M.loaded_segments (0x73b74 : word) = Some W_73b74.
Proof. vm_refl. Qed.
Lemma D_73b74 : decode_any W_73b74 = Some (Store SZ4 2 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_73b78 : bv 32 := 0x00010613.
Lemma F_73b78 : fetch_word AsanUbsan.M.loaded_segments (0x73b78 : word) = Some W_73b78.
Proof. vm_refl. Qed.
Lemma D_73b78 : decode_any W_73b78 = Some (OpImm ALU_ADD 12 2 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_73b7c : bv 32 := 0x00098513.
Lemma F_73b7c : fetch_word AsanUbsan.M.loaded_segments (0x73b7c : word) = Some W_73b7c.
Proof. vm_refl. Qed.
Lemma D_73b7c : decode_any W_73b7c = Some (OpImm ALU_ADD 10 19 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_73b80 : bv 32 := 0x00040593.
Lemma F_73b80 : fetch_word AsanUbsan.M.loaded_segments (0x73b80 : word) = Some W_73b80.
Proof. vm_refl. Qed.
Lemma D_73b80 : decode_any W_73b80 = Some (OpImm ALU_ADD 11 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_73b84 : bv 32 := 0x608000ef.
Lemma F_73b84 : fetch_word AsanUbsan.M.loaded_segments (0x73b84 : word) = Some W_73b84.
Proof. vm_refl. Qed.
Lemma D_73b84 : decode_any W_73b84 = Some (Jal 1 1544, 4%Z).
Proof. vm_refl. Qed.

Definition W_73b88 : bv 32 := 0x00012683.
Lemma F_73b88 : fetch_word AsanUbsan.M.loaded_segments (0x73b88 : word) = Some W_73b88.
Proof. vm_refl. Qed.
Lemma D_73b88 : decode_any W_73b88 = Some (Load SZ4 true 13 2 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_73b8c : bv 32 := 0x00050713.
Lemma F_73b8c : fetch_word AsanUbsan.M.loaded_segments (0x73b8c : word) = Some W_73b8c.
Proof. vm_refl. Qed.
Lemma D_73b8c : decode_any W_73b8c = Some (OpImm ALU_ADD 14 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_73b90 : bv 32 := 0x00300613.
Lemma F_73b90 : fetch_word AsanUbsan.M.loaded_segments (0x73b90 : word) = Some W_73b90.
Proof. vm_refl. Qed.
Lemma D_73b90 : decode_any W_73b90 = Some (OpImm ALU_ADD 12 0 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_73b94 : bv 32 := 0x00090513.
Lemma F_73b94 : fetch_word AsanUbsan.M.loaded_segments (0x73b94 : word) = Some W_73b94.
Proof. vm_refl. Qed.
Lemma D_73b94 : decode_any W_73b94 = Some (OpImm ALU_ADD 10 18 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_73b98 : bv 32 := 0x00040593.
Lemma F_73b98 : fetch_word AsanUbsan.M.loaded_segments (0x73b98 : word) = Some W_73b98.
Proof. vm_refl. Qed.
Lemma D_73b98 : decode_any W_73b98 = Some (OpImm ALU_ADD 11 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_73b9c : bv 32 := 0x00000793.
Lemma F_73b9c : fetch_word AsanUbsan.M.loaded_segments (0x73b9c : word) = Some W_73b9c.
Proof. vm_refl. Qed.
Lemma D_73b9c : decode_any W_73b9c = Some (OpImm ALU_ADD 15 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_73ba0 : bv 32 := 0xa40fe0ef.
Lemma F_73ba0 : fetch_word AsanUbsan.M.loaded_segments (0x73ba0 : word) = Some W_73ba0.
Proof. vm_refl. Qed.
Lemma D_73ba0 : decode_any W_73ba0 = Some (Jal 1 2089536, 4%Z).
Proof. vm_refl. Qed.

Definition W_73ba4 : bv 32 := 0x00050993.
Lemma F_73ba4 : fetch_word AsanUbsan.M.loaded_segments (0x73ba4 : word) = Some W_73ba4.
Proof. vm_refl. Qed.
Lemma D_73ba4 : decode_any W_73ba4 = Some (OpImm ALU_ADD 19 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_73ba8 : bv 32 := 0x00000593.
Lemma F_73ba8 : fetch_word AsanUbsan.M.loaded_segments (0x73ba8 : word) = Some W_73ba8.
Proof. vm_refl. Qed.
Lemma D_73ba8 : decode_any W_73ba8 = Some (OpImm ALU_ADD 11 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_73bac : bv 32 := 0xa14fe0ef.
Lemma F_73bac : fetch_word AsanUbsan.M.loaded_segments (0x73bac : word) = Some W_73bac.
Proof. vm_refl. Qed.
Lemma D_73bac : decode_any W_73bac = Some (Jal 1 2089492, 4%Z).
Proof. vm_refl. Qed.

Definition W_73bb0 : bv 32 := 0xaaaab537.
Lemma F_73bb0 : fetch_word AsanUbsan.M.loaded_segments (0x73bb0 : word) = Some W_73bb0.
Proof. vm_refl. Qed.
Lemma D_73bb0 : decode_any W_73bb0 = Some (Lui 10 699051, 4%Z).
Proof. vm_refl. Qed.

Definition W_73bb4 : bv 32 := 0xaaa50513.
Lemma F_73bb4 : fetch_word AsanUbsan.M.loaded_segments (0x73bb4 : word) = Some W_73bb4.
Proof. vm_refl. Qed.
Lemma D_73bb4 : decode_any W_73bb4 = Some (OpImm ALU_ADD 10 10 2730, 4%Z).
Proof. vm_refl. Qed.

Definition W_73bb8 : bv 32 := 0x02a12623.
Lemma F_73bb8 : fetch_word AsanUbsan.M.loaded_segments (0x73bb8 : word) = Some W_73bb8.
Proof. vm_refl. Qed.
Lemma D_73bb8 : decode_any W_73bb8 = Some (Store SZ4 2 10 44, 4%Z).
Proof. vm_refl. Qed.

Definition W_73bbc : bv 32 := 0x02c10593.
Lemma F_73bbc : fetch_word AsanUbsan.M.loaded_segments (0x73bbc : word) = Some W_73bbc.
Proof. vm_refl. Qed.
Lemma D_73bbc : decode_any W_73bbc = Some (OpImm ALU_ADD 11 2 44, 4%Z).
Proof. vm_refl. Qed.

Definition W_73bc0 : bv 32 := 0x00098513.
Lemma F_73bc0 : fetch_word AsanUbsan.M.loaded_segments (0x73bc0 : word) = Some W_73bc0.
Proof. vm_refl. Qed.
Lemma D_73bc0 : decode_any W_73bc0 = Some (OpImm ALU_ADD 10 19 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_73bc4 : bv 32 := 0x9fcfe0ef.
Lemma F_73bc4 : fetch_word AsanUbsan.M.loaded_segments (0x73bc4 : word) = Some W_73bc4.
Proof. vm_refl. Qed.
Lemma D_73bc4 : decode_any W_73bc4 = Some (Jal 1 2089468, 4%Z).
Proof. vm_refl. Qed.

Definition W_73bc8 : bv 32 := 0x04051063.
Lemma F_73bc8 : fetch_word AsanUbsan.M.loaded_segments (0x73bc8 : word) = Some W_73bc8.
Proof. vm_refl. Qed.
Lemma D_73bc8 : decode_any W_73bc8 = Some (Branch BC_NE 10 0 64, 4%Z).
Proof. vm_refl. Qed.

Definition W_73bcc : bv 32 := 0x00040513.
Lemma F_73bcc : fetch_word AsanUbsan.M.loaded_segments (0x73bcc : word) = Some W_73bcc.
Proof. vm_refl. Qed.
Lemma D_73bcc : decode_any W_73bcc = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_73bd0 : bv 32 := 0x8f4fa0ef.
Lemma F_73bd0 : fetch_word AsanUbsan.M.loaded_segments (0x73bd0 : word) = Some W_73bd0.
Proof. vm_refl. Qed.
Lemma D_73bd0 : decode_any W_73bd0 = Some (Jal 1 2072820, 4%Z).
Proof. vm_refl. Qed.

Definition W_73bd4 : bv 32 := 0x00098513.
Lemma F_73bd4 : fetch_word AsanUbsan.M.loaded_segments (0x73bd4 : word) = Some W_73bd4.
Proof. vm_refl. Qed.
Lemma D_73bd4 : decode_any W_73bd4 = Some (OpImm ALU_ADD 10 19 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_73bd8 : bv 32 := 0x05813083.
Lemma F_73bd8 : fetch_word AsanUbsan.M.loaded_segments (0x73bd8 : word) = Some W_73bd8.
Proof. vm_refl. Qed.
Lemma D_73bd8 : decode_any W_73bd8 = Some (Load SZ8 true 1 2 88, 4%Z).
Proof. vm_refl. Qed.

Definition W_73bdc : bv 32 := 0x05013403.
Lemma F_73bdc : fetch_word AsanUbsan.M.loaded_segments (0x73bdc : word) = Some W_73bdc.
Proof. vm_refl. Qed.
Lemma D_73bdc : decode_any W_73bdc = Some (Load SZ8 true 8 2 80, 4%Z).
Proof. vm_refl. Qed.

Definition W_73be0 : bv 32 := 0x04813483.
Lemma F_73be0 : fetch_word AsanUbsan.M.loaded_segments (0x73be0 : word) = Some W_73be0.
Proof. vm_refl. Qed.
Lemma D_73be0 : decode_any W_73be0 = Some (Load SZ8 true 9 2 72, 4%Z).
Proof. vm_refl. Qed.

Definition W_73be4 : bv 32 := 0x04013903.
Lemma F_73be4 : fetch_word AsanUbsan.M.loaded_segments (0x73be4 : word) = Some W_73be4.
Proof. vm_refl. Qed.
Lemma D_73be4 : decode_any W_73be4 = Some (Load SZ8 true 18 2 64, 4%Z).
Proof. vm_refl. Qed.

Definition W_73be8 : bv 32 := 0x03813983.
Lemma F_73be8 : fetch_word AsanUbsan.M.loaded_segments (0x73be8 : word) = Some W_73be8.
Proof. vm_refl. Qed.
Lemma D_73be8 : decode_any W_73be8 = Some (Load SZ8 true 19 2 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_73bec : bv 32 := 0x03013a03.
Lemma F_73bec : fetch_word AsanUbsan.M.loaded_segments (0x73bec : word) = Some W_73bec.
Proof. vm_refl. Qed.
Lemma D_73bec : decode_any W_73bec = Some (Load SZ8 true 20 2 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_73bf0 : bv 32 := 0x06010113.
Lemma F_73bf0 : fetch_word AsanUbsan.M.loaded_segments (0x73bf0 : word) = Some W_73bf0.
Proof. vm_refl. Qed.
Lemma D_73bf0 : decode_any W_73bf0 = Some (OpImm ALU_ADD 2 2 96, 4%Z).
Proof. vm_refl. Qed.

Definition W_73bf4 : bv 32 := 0x00008067.
Lemma F_73bf4 : fetch_word AsanUbsan.M.loaded_segments (0x73bf4 : word) = Some W_73bf4.
Proof. vm_refl. Qed.
Lemma D_73bf4 : decode_any W_73bf4 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_73bf8 : bv 32 := 0xfff9f517.
Lemma F_73bf8 : fetch_word AsanUbsan.M.loaded_segments (0x73bf8 : word) = Some W_73bf8.
Proof. vm_refl. Qed.
Lemma D_73bf8 : decode_any W_73bf8 = Some (Auipc 10 1048479, 4%Z).
Proof. vm_refl. Qed.

Definition W_73bfc : bv 32 := 0xb7a50513.
Lemma F_73bfc : fetch_word AsanUbsan.M.loaded_segments (0x73bfc : word) = Some W_73bfc.
Proof. vm_refl. Qed.
Lemma D_73bfc : decode_any W_73bfc = Some (OpImm ALU_ADD 10 10 2938, 4%Z).
Proof. vm_refl. Qed.

Definition W_73c00 : bv 32 := 0x895fa0ef.
Lemma F_73c00 : fetch_word AsanUbsan.M.loaded_segments (0x73c00 : word) = Some W_73c00.
Proof. vm_refl. Qed.
Lemma D_73c00 : decode_any W_73c00 = Some (Jal 1 2074772, 4%Z).
Proof. vm_refl. Qed.

Definition W_73c04 : bv 32 := 0x618050ef.
Lemma F_73c04 : fetch_word AsanUbsan.M.loaded_segments (0x73c04 : word) = Some W_73c04.
Proof. vm_refl. Qed.
Lemma D_73c04 : decode_any W_73c04 = Some (Jal 1 22040, 4%Z).
Proof. vm_refl. Qed.

Definition W_73c08 : bv 32 := 0x00048c63.
Lemma F_73c08 : fetch_word AsanUbsan.M.loaded_segments (0x73c08 : word) = Some W_73c08.
Proof. vm_refl. Qed.
Lemma D_73c08 : decode_any W_73c08 = Some (Branch BC_EQ 9 0 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_73c0c : bv 32 := 0x02c12503.
Lemma F_73c0c : fetch_word AsanUbsan.M.loaded_segments (0x73c0c : word) = Some W_73c0c.
Proof. vm_refl. Qed.
Lemma D_73c0c : decode_any W_73c0c = Some (Load SZ4 true 10 2 44, 4%Z).
Proof. vm_refl. Qed.

Definition W_73c10 : bv 32 := 0x00c00593.
Lemma F_73c10 : fetch_word AsanUbsan.M.loaded_segments (0x73c10 : word) = Some W_73c10.
Proof. vm_refl. Qed.
Lemma D_73c10 : decode_any W_73c10 = Some (OpImm ALU_ADD 11 0 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_73c14 : bv 32 := 0x00b51663.
Lemma F_73c14 : fetch_word AsanUbsan.M.loaded_segments (0x73c14 : word) = Some W_73c14.
Proof. vm_refl. Qed.
Lemma D_73c14 : decode_any W_73c14 = Some (Branch BC_NE 10 11 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_73c18 : bv 32 := 0x00000993.
Lemma F_73c18 : fetch_word AsanUbsan.M.loaded_segments (0x73c18 : word) = Some W_73c18.
Proof. vm_refl. Qed.
Lemma D_73c18 : decode_any W_73c18 = Some (OpImm ALU_ADD 19 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_73c1c : bv 32 := 0xfb9ff06f.
Lemma F_73c1c : fetch_word AsanUbsan.M.loaded_segments (0x73c1c : word) = Some W_73c1c.
Proof. vm_refl. Qed.
Lemma D_73c1c : decode_any W_73c1c = Some (Jal 0 2097080, 4%Z).
Proof. vm_refl. Qed.

Definition W_73c20 : bv 32 := 0xfff9c517.
Lemma F_73c20 : fetch_word AsanUbsan.M.loaded_segments (0x73c20 : word) = Some W_73c20.
Proof. vm_refl. Qed.
Lemma D_73c20 : decode_any W_73c20 = Some (Auipc 10 1048476, 4%Z).
Proof. vm_refl. Qed.

Definition W_73c24 : bv 32 := 0x7e853503.
Lemma F_73c24 : fetch_word AsanUbsan.M.loaded_segments (0x73c24 : word) = Some W_73c24.
Proof. vm_refl. Qed.
Lemma D_73c24 : decode_any W_73c24 = Some (Load SZ8 true 10 10 2024, 4%Z).
Proof. vm_refl. Qed.

Definition W_73c28 : bv 32 := 0x02a13023.
Lemma F_73c28 : fetch_word AsanUbsan.M.loaded_segments (0x73c28 : word) = Some W_73c28.
Proof. vm_refl. Qed.
Lemma D_73c28 : decode_any W_73c28 = Some (Store SZ8 2 10 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_73c2c : bv 32 := 0x00a13023.
Lemma F_73c2c : fetch_word AsanUbsan.M.loaded_segments (0x73c2c : word) = Some W_73c2c.
Proof. vm_refl. Qed.
Lemma D_73c2c : decode_any W_73c2c = Some (Store SZ8 2 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_73c30 : bv 32 := 0x00a13423.
Lemma F_73c30 : fetch_word AsanUbsan.M.loaded_segments (0x73c30 : word) = Some W_73c30.
Proof. vm_refl. Qed.
Lemma D_73c30 : decode_any W_73c30 = Some (Store SZ8 2 10 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_73c34 : bv 32 := 0x00a13823.
Lemma F_73c34 : fetch_word AsanUbsan.M.loaded_segments (0x73c34 : word) = Some W_73c34.
Proof. vm_refl. Qed.
Lemma D_73c34 : decode_any W_73c34 = Some (Store SZ8 2 10 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_73c38 : bv 32 := 0x00a13c23.
Lemma F_73c38 : fetch_word AsanUbsan.M.loaded_segments (0x73c38 : word) = Some W_73c38.
Proof. vm_refl. Qed.
Lemma D_73c38 : decode_any W_73c38 = Some (Store SZ8 2 10 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_73c3c : bv 32 := 0xfffaa597.
Lemma F_73c3c : fetch_word AsanUbsan.M.loaded_segments (0x73c3c : word) = Some W_73c3c.
Proof. vm_refl. Qed.
Lemma D_73c3c : decode_any W_73c3c = Some (Auipc 11 1048490, 4%Z).
Proof. vm_refl. Qed.

Definition W_73c40 : bv 32 := 0x00010513.
Lemma F_73c40 : fetch_word AsanUbsan.M.loaded_segments (0x73c40 : word) = Some W_73c40.
Proof. vm_refl. Qed.
Lemma D_73c40 : decode_any W_73c40 = Some (OpImm ALU_ADD 10 2 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_73c44 : bv 32 := 0x45058613.
Lemma F_73c44 : fetch_word AsanUbsan.M.loaded_segments (0x73c44 : word) = Some W_73c44.
Proof. vm_refl. Qed.
Lemma D_73c44 : decode_any W_73c44 = Some (OpImm ALU_ADD 12 11 1104, 4%Z).
Proof. vm_refl. Qed.

Definition W_73c48 : bv 32 := 0x02800593.
Lemma F_73c48 : fetch_word AsanUbsan.M.loaded_segments (0x73c48 : word) = Some W_73c48.
Proof. vm_refl. Qed.
Lemma D_73c48 : decode_any W_73c48 = Some (OpImm ALU_ADD 11 0 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_73c4c : bv 32 := 0x00090693.
Lemma F_73c4c : fetch_word AsanUbsan.M.loaded_segments (0x73c4c : word) = Some W_73c4c.
Proof. vm_refl. Qed.
Lemma D_73c4c : decode_any W_73c4c = Some (OpImm ALU_ADD 13 18 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_73c50 : bv 32 := 0x605000ef.
Lemma F_73c50 : fetch_word AsanUbsan.M.loaded_segments (0x73c50 : word) = Some W_73c50.
Proof. vm_refl. Qed.
Lemma D_73c50 : decode_any W_73c50 = Some (Jal 1 3588, 4%Z).
Proof. vm_refl. Qed.

Definition W_73c54 : bv 32 := 0x02c12683.
Lemma F_73c54 : fetch_word AsanUbsan.M.loaded_segments (0x73c54 : word) = Some W_73c54.
Proof. vm_refl. Qed.
Lemma D_73c54 : decode_any W_73c54 = Some (Load SZ4 true 13 2 44, 4%Z).
Proof. vm_refl. Qed.

Definition W_73c58 : bv 32 := 0xfffa7517.
Lemma F_73c58 : fetch_word AsanUbsan.M.loaded_segments (0x73c58 : word) = Some W_73c58.
Proof. vm_refl. Qed.
Lemma D_73c58 : decode_any W_73c58 = Some (Auipc 10 1048487, 4%Z).
Proof. vm_refl. Qed.

Definition W_73c5c : bv 32 := 0xf8050613.
Lemma F_73c5c : fetch_word AsanUbsan.M.loaded_segments (0x73c5c : word) = Some W_73c5c.
Proof. vm_refl. Qed.
Lemma D_73c5c : decode_any W_73c5c = Some (OpImm ALU_ADD 12 10 3968, 4%Z).
Proof. vm_refl. Qed.

Definition W_73c60 : bv 32 := 0x00010593.
Lemma F_73c60 : fetch_word AsanUbsan.M.loaded_segments (0x73c60 : word) = Some W_73c60.
Proof. vm_refl. Qed.
Lemma D_73c60 : decode_any W_73c60 = Some (OpImm ALU_ADD 11 2 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_73c64 : bv 32 := 0x00040513.
Lemma F_73c64 : fetch_word AsanUbsan.M.loaded_segments (0x73c64 : word) = Some W_73c64.
Proof. vm_refl. Qed.
Lemma D_73c64 : decode_any W_73c64 = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_73c68 : bv 32 := 0x00000713.
Lemma F_73c68 : fetch_word AsanUbsan.M.loaded_segments (0x73c68 : word) = Some W_73c68.
Proof. vm_refl. Qed.
Lemma D_73c68 : decode_any W_73c68 = Some (OpImm ALU_ADD 14 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_73c6c : bv 32 := 0x9c1f90ef.
Lemma F_73c6c : fetch_word AsanUbsan.M.loaded_segments (0x73c6c : word) = Some W_73c6c.
Proof. vm_refl. Qed.
Lemma D_73c6c : decode_any W_73c6c = Some (Jal 1 2070976, 4%Z).
Proof. vm_refl. Qed.

Definition W_73c70 : bv 32 := 0x00060693.
Lemma F_73c70 : fetch_word AsanUbsan.M.loaded_segments (0x73c70 : word) = Some W_73c70.
Proof. vm_refl. Qed.
Lemma D_73c70 : decode_any W_73c70 = Some (OpImm ALU_ADD 13 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_73c74 : bv 32 := 0x00100613.
Lemma F_73c74 : fetch_word AsanUbsan.M.loaded_segments (0x73c74 : word) = Some W_73c74.
Proof. vm_refl. Qed.
Lemma D_73c74 : decode_any W_73c74 = Some (OpImm ALU_ADD 12 0 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_73c78 : bv 32 := 0xe81ff06f.
Lemma F_73c78 : fetch_word AsanUbsan.M.loaded_segments (0x73c78 : word) = Some W_73c78.
Proof. vm_refl. Qed.
Lemma D_73c78 : decode_any W_73c78 = Some (Jal 0 2096768, 4%Z).
Proof. vm_refl. Qed.
