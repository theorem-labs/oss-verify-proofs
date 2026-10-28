(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OssFuzzTheorems.zstd.huf_decompress.images Require Import AsanUbsan.
Open Scope bv_scope.

(* [comment removed for export] *)
Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

(* [comment removed for export] *)
Definition W_a8a94 : bv 32 := 0x0035f693.
Lemma F_a8a94 : fetch_word AsanUbsan.M.loaded_segments (0xab458 : word) = Some W_a8a94.
Proof. vm_refl. Qed.
Lemma D_a8a94 : decode_any W_a8a94 = Some (OpImm ALU_AND 13 11 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a8a98 : bv 32 := 0x10068863.
Lemma F_a8a98 : fetch_word AsanUbsan.M.loaded_segments (0xab45c : word) = Some W_a8a98.
Proof. vm_refl. Qed.
Lemma D_a8a98 : decode_any W_a8a98 = Some (Branch BC_EQ 13 0 272, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a8a9c : bv 32 := 0x02060e63.
Lemma F_a8a9c : fetch_word AsanUbsan.M.loaded_segments (0xab460 : word) = Some W_a8a9c.
Proof. vm_refl. Qed.
Lemma D_a8a9c : decode_any W_a8a9c = Some (Branch BC_EQ 12 0 60, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a8aa0 : bv 32 := 0x00158713.
Lemma F_a8aa0 : fetch_word AsanUbsan.M.loaded_segments (0xab464 : word) = Some W_a8aa0.
Proof. vm_refl. Qed.
Lemma D_a8aa0 : decode_any W_a8aa0 = Some (OpImm ALU_ADD 14 11 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a8aa4 : bv 32 := 0x00100793.
Lemma F_a8aa4 : fetch_word AsanUbsan.M.loaded_segments (0xab468 : word) = Some W_a8aa4.
Proof. vm_refl. Qed.
Lemma D_a8aa4 : decode_any W_a8aa4 = Some (OpImm ALU_ADD 15 0 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a8aa8 : bv 32 := 0x00050693.
Lemma F_a8aa8 : fetch_word AsanUbsan.M.loaded_segments (0xab46c : word) = Some W_a8aa8.
Proof. vm_refl. Qed.
Lemma D_a8aa8 : decode_any W_a8aa8 = Some (OpImm ALU_ADD 13 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a8aac : bv 32 := 0x0005c883.
Lemma F_a8aac : fetch_word AsanUbsan.M.loaded_segments (0xab470 : word) = Some W_a8aac.
Proof. vm_refl. Qed.
Lemma D_a8aac : decode_any W_a8aac = Some (Load SZ1 false 17 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a8ab0 : bv 32 := 0x00060813.
Lemma F_a8ab0 : fetch_word AsanUbsan.M.loaded_segments (0xab474 : word) = Some W_a8ab0.
Proof. vm_refl. Qed.
Lemma D_a8ab0 : decode_any W_a8ab0 = Some (OpImm ALU_ADD 16 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a8ab4 : bv 32 := 0x00158593.
Lemma F_a8ab4 : fetch_word AsanUbsan.M.loaded_segments (0xab478 : word) = Some W_a8ab4.
Proof. vm_refl. Qed.
Lemma D_a8ab4 : decode_any W_a8ab4 = Some (OpImm ALU_ADD 11 11 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a8ab8 : bv 32 := 0x00377293.
Lemma F_a8ab8 : fetch_word AsanUbsan.M.loaded_segments (0xab47c : word) = Some W_a8ab8.
Proof. vm_refl. Qed.
Lemma D_a8ab8 : decode_any W_a8ab8 = Some (OpImm ALU_AND 5 14 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a8abc : bv 32 := 0x01168023.
Lemma F_a8abc : fetch_word AsanUbsan.M.loaded_segments (0xab480 : word) = Some W_a8abc.
Proof. vm_refl. Qed.
Lemma D_a8abc : decode_any W_a8abc = Some (Store SZ1 13 17 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a8ac0 : bv 32 := 0x00168693.
Lemma F_a8ac0 : fetch_word AsanUbsan.M.loaded_segments (0xab484 : word) = Some W_a8ac0.
Proof. vm_refl. Qed.
Lemma D_a8ac0 : decode_any W_a8ac0 = Some (OpImm ALU_ADD 13 13 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a8ac4 : bv 32 := 0xfff60613.
Lemma F_a8ac4 : fetch_word AsanUbsan.M.loaded_segments (0xab488 : word) = Some W_a8ac4.
Proof. vm_refl. Qed.
Lemma D_a8ac4 : decode_any W_a8ac4 = Some (OpImm ALU_ADD 12 12 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a8ac8 : bv 32 := 0x00028a63.
Lemma F_a8ac8 : fetch_word AsanUbsan.M.loaded_segments (0xab48c : word) = Some W_a8ac8.
Proof. vm_refl. Qed.
Lemma D_a8ac8 : decode_any W_a8ac8 = Some (Branch BC_EQ 5 0 20, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a8acc : bv 32 := 0x00170713.
Lemma F_a8acc : fetch_word AsanUbsan.M.loaded_segments (0xab490 : word) = Some W_a8acc.
Proof. vm_refl. Qed.
Lemma D_a8acc : decode_any W_a8acc = Some (OpImm ALU_ADD 14 14 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a8ad0 : bv 32 := 0xfcf81ee3.
Lemma F_a8ad0 : fetch_word AsanUbsan.M.loaded_segments (0xab494 : word) = Some W_a8ad0.
Proof. vm_refl. Qed.
Lemma D_a8ad0 : decode_any W_a8ad0 = Some (Branch BC_NE 16 15 8156, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a8ad4 : bv 32 := 0x0080006f.
Lemma F_a8ad4 : fetch_word AsanUbsan.M.loaded_segments (0xab498 : word) = Some W_a8ad4.
Proof. vm_refl. Qed.
Lemma D_a8ad4 : decode_any W_a8ad4 = Some (Jal 0 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a8ad8 : bv 32 := 0x00050693.
Lemma F_a8ad8 : fetch_word AsanUbsan.M.loaded_segments (0xab49c : word) = Some W_a8ad8.
Proof. vm_refl. Qed.
Lemma D_a8ad8 : decode_any W_a8ad8 = Some (OpImm ALU_ADD 13 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a8adc : bv 32 := 0x0036f793.
Lemma F_a8adc : fetch_word AsanUbsan.M.loaded_segments (0xab4a0 : word) = Some W_a8adc.
Proof. vm_refl. Qed.
Lemma D_a8adc : decode_any W_a8adc = Some (OpImm ALU_AND 15 13 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a8ae0 : bv 32 := 0x0c078a63.
Lemma F_a8ae0 : fetch_word AsanUbsan.M.loaded_segments (0xab4a4 : word) = Some W_a8ae0.
Proof. vm_refl. Qed.
Lemma D_a8ae0 : decode_any W_a8ae0 = Some (Branch BC_EQ 15 0 212, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a8ae4 : bv 32 := 0x02000713.
Lemma F_a8ae4 : fetch_word AsanUbsan.M.loaded_segments (0xab4a8 : word) = Some W_a8ae4.
Proof. vm_refl. Qed.
Lemma D_a8ae4 : decode_any W_a8ae4 = Some (OpImm ALU_ADD 14 0 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a8ae8 : bv 32 := 0x02e67063.
Lemma F_a8ae8 : fetch_word AsanUbsan.M.loaded_segments (0xab4ac : word) = Some W_a8ae8.
Proof. vm_refl. Qed.
Lemma D_a8ae8 : decode_any W_a8ae8 = Some (Branch BC_GEU 12 14 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a8aec : bv 32 := 0x01000713.
Lemma F_a8aec : fetch_word AsanUbsan.M.loaded_segments (0xab4b0 : word) = Some W_a8aec.
Proof. vm_refl. Qed.
Lemma D_a8aec : decode_any W_a8aec = Some (OpImm ALU_ADD 14 0 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a8af0 : bv 32 := 0x24e67863.
Lemma F_a8af0 : fetch_word AsanUbsan.M.loaded_segments (0xab4b4 : word) = Some W_a8af0.
Proof. vm_refl. Qed.
Lemma D_a8af0 : decode_any W_a8af0 = Some (Branch BC_GEU 12 14 592, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a8af4 : bv 32 := 0x00867713.
Lemma F_a8af4 : fetch_word AsanUbsan.M.loaded_segments (0xab4b8 : word) = Some W_a8af4.
Proof. vm_refl. Qed.
Lemma D_a8af4 : decode_any W_a8af4 = Some (OpImm ALU_AND 14 12 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a8af8 : bv 32 := 0x2c071e63.
Lemma F_a8af8 : fetch_word AsanUbsan.M.loaded_segments (0xab4bc : word) = Some W_a8af8.
Proof. vm_refl. Qed.
Lemma D_a8af8 : decode_any W_a8af8 = Some (Branch BC_NE 14 0 732, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a8afc : bv 32 := 0x00467713.
Lemma F_a8afc : fetch_word AsanUbsan.M.loaded_segments (0xab4c0 : word) = Some W_a8afc.
Proof. vm_refl. Qed.
Lemma D_a8afc : decode_any W_a8afc = Some (OpImm ALU_AND 14 12 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a8b00 : bv 32 := 0x32071463.
Lemma F_a8b00 : fetch_word AsanUbsan.M.loaded_segments (0xab4c4 : word) = Some W_a8b00.
Proof. vm_refl. Qed.
Lemma D_a8b00 : decode_any W_a8b00 = Some (Branch BC_NE 14 0 808, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a8b04 : bv 32 := 0x3500006f.
Lemma F_a8b04 : fetch_word AsanUbsan.M.loaded_segments (0xab4c8 : word) = Some W_a8b04.
Proof. vm_refl. Qed.
Lemma D_a8b04 : decode_any W_a8b04 = Some (Jal 0 848, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a8b08 : bv 32 := 0x0005a703.
Lemma F_a8b08 : fetch_word AsanUbsan.M.loaded_segments (0xab4cc : word) = Some W_a8b08.
Proof. vm_refl. Qed.
Lemma D_a8b08 : decode_any W_a8b08 = Some (Load SZ4 true 14 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a8b0c : bv 32 := 0x00300813.
Lemma F_a8b0c : fetch_word AsanUbsan.M.loaded_segments (0xab4d0 : word) = Some W_a8b0c.
Proof. vm_refl. Qed.
Lemma D_a8b0c : decode_any W_a8b0c = Some (OpImm ALU_ADD 16 0 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a8b10 : bv 32 := 0x11078e63.
Lemma F_a8b10 : fetch_word AsanUbsan.M.loaded_segments (0xab4d4 : word) = Some W_a8b10.
Proof. vm_refl. Qed.
Lemma D_a8b10 : decode_any W_a8b10 = Some (Branch BC_EQ 15 16 284, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a8b14 : bv 32 := 0x00200813.
Lemma F_a8b14 : fetch_word AsanUbsan.M.loaded_segments (0xab4d8 : word) = Some W_a8b14.
Proof. vm_refl. Qed.
Lemma D_a8b14 : decode_any W_a8b14 = Some (OpImm ALU_ADD 16 0 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a8b18 : bv 32 := 0x19079c63.
Lemma F_a8b18 : fetch_word AsanUbsan.M.loaded_segments (0xab4dc : word) = Some W_a8b18.
Proof. vm_refl. Qed.
Lemma D_a8b18 : decode_any W_a8b18 = Some (Branch BC_NE 15 16 408, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a8b1c : bv 32 := 0x00875793.
Lemma F_a8b1c : fetch_word AsanUbsan.M.loaded_segments (0xab4e0 : word) = Some W_a8b1c.
Proof. vm_refl. Qed.
Lemma D_a8b1c : decode_any W_a8b1c = Some (ShiftImm ALU_SRL 15 14 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a8b20 : bv 32 := 0xffe60613.
Lemma F_a8b20 : fetch_word AsanUbsan.M.loaded_segments (0xab4e4 : word) = Some W_a8b20.
Proof. vm_refl. Qed.
Lemma D_a8b20 : decode_any W_a8b20 = Some (OpImm ALU_ADD 12 12 4094, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a8b24 : bv 32 := 0x00e68023.
Lemma F_a8b24 : fetch_word AsanUbsan.M.loaded_segments (0xab4e8 : word) = Some W_a8b24.
Proof. vm_refl. Qed.
Lemma D_a8b24 : decode_any W_a8b24 = Some (Store SZ1 13 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a8b28 : bv 32 := 0x00f680a3.
Lemma F_a8b28 : fetch_word AsanUbsan.M.loaded_segments (0xab4ec : word) = Some W_a8b28.
Proof. vm_refl. Qed.
Lemma D_a8b28 : decode_any W_a8b28 = Some (Store SZ1 13 15 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a8b2c : bv 32 := 0x00268693.
Lemma F_a8b2c : fetch_word AsanUbsan.M.loaded_segments (0xab4f0 : word) = Some W_a8b2c.
Proof. vm_refl. Qed.
Lemma D_a8b2c : decode_any W_a8b2c = Some (OpImm ALU_ADD 13 13 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a8b30 : bv 32 := 0x01058593.
Lemma F_a8b30 : fetch_word AsanUbsan.M.loaded_segments (0xab4f4 : word) = Some W_a8b30.
Proof. vm_refl. Qed.
Lemma D_a8b30 : decode_any W_a8b30 = Some (OpImm ALU_ADD 11 11 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a8b34 : bv 32 := 0x01100793.
Lemma F_a8b34 : fetch_word AsanUbsan.M.loaded_segments (0xab4f8 : word) = Some W_a8b34.
Proof. vm_refl. Qed.
Lemma D_a8b34 : decode_any W_a8b34 = Some (OpImm ALU_ADD 15 0 17, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a8b38 : bv 32 := 0x0107581b.
Lemma F_a8b38 : fetch_word AsanUbsan.M.loaded_segments (0xab4fc : word) = Some W_a8b38.
Proof. vm_refl. Qed.
Lemma D_a8b38 : decode_any W_a8b38 = Some (ShiftImm32 ALU_SRL 16 14 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a8b3c : bv 32 := 0xff45a883.
Lemma F_a8b3c : fetch_word AsanUbsan.M.loaded_segments (0xab500 : word) = Some W_a8b3c.
Proof. vm_refl. Qed.
Lemma D_a8b3c : decode_any W_a8b3c = Some (Load SZ4 true 17 11 4084, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a8b40 : bv 32 := 0xff85a283.
Lemma F_a8b40 : fetch_word AsanUbsan.M.loaded_segments (0xab504 : word) = Some W_a8b40.
Proof. vm_refl. Qed.
Lemma D_a8b40 : decode_any W_a8b40 = Some (Load SZ4 true 5 11 4088, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a8b44 : bv 32 := 0xffc5a303.
Lemma F_a8b44 : fetch_word AsanUbsan.M.loaded_segments (0xab508 : word) = Some W_a8b44.
Proof. vm_refl. Qed.
Lemma D_a8b44 : decode_any W_a8b44 = Some (Load SZ4 true 6 11 4092, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a8b48 : bv 32 := 0x0005a703.
Lemma F_a8b48 : fetch_word AsanUbsan.M.loaded_segments (0xab50c : word) = Some W_a8b48.
Proof. vm_refl. Qed.
Lemma D_a8b48 : decode_any W_a8b48 = Some (Load SZ4 true 14 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a8b4c : bv 32 := 0x01089393.
Lemma F_a8b4c : fetch_word AsanUbsan.M.loaded_segments (0xab510 : word) = Some W_a8b4c.
Proof. vm_refl. Qed.
Lemma D_a8b4c : decode_any W_a8b4c = Some (ShiftImm ALU_SLL 7 17 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a8b50 : bv 32 := 0x0108d89b.
Lemma F_a8b50 : fetch_word AsanUbsan.M.loaded_segments (0xab514 : word) = Some W_a8b50.
Proof. vm_refl. Qed.
Lemma D_a8b50 : decode_any W_a8b50 = Some (ShiftImm32 ALU_SRL 17 17 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a8b54 : bv 32 := 0x0103e833.
Lemma F_a8b54 : fetch_word AsanUbsan.M.loaded_segments (0xab518 : word) = Some W_a8b54.
Proof. vm_refl. Qed.
Lemma D_a8b54 : decode_any W_a8b54 = Some (Op ALU_OR 16 7 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a8b58 : bv 32 := 0x01029393.
Lemma F_a8b58 : fetch_word AsanUbsan.M.loaded_segments (0xab51c : word) = Some W_a8b58.
Proof. vm_refl. Qed.
Lemma D_a8b58 : decode_any W_a8b58 = Some (ShiftImm ALU_SLL 7 5 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a8b5c : bv 32 := 0x0102d29b.
Lemma F_a8b5c : fetch_word AsanUbsan.M.loaded_segments (0xab520 : word) = Some W_a8b5c.
Proof. vm_refl. Qed.
Lemma D_a8b5c : decode_any W_a8b5c = Some (ShiftImm32 ALU_SRL 5 5 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a8b60 : bv 32 := 0x0113e8b3.
Lemma F_a8b60 : fetch_word AsanUbsan.M.loaded_segments (0xab524 : word) = Some W_a8b60.
Proof. vm_refl. Qed.
Lemma D_a8b60 : decode_any W_a8b60 = Some (Op ALU_OR 17 7 17, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a8b64 : bv 32 := 0x01031393.
Lemma F_a8b64 : fetch_word AsanUbsan.M.loaded_segments (0xab528 : word) = Some W_a8b64.
Proof. vm_refl. Qed.
Lemma D_a8b64 : decode_any W_a8b64 = Some (ShiftImm ALU_SLL 7 6 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a8b68 : bv 32 := 0x0103531b.
Lemma F_a8b68 : fetch_word AsanUbsan.M.loaded_segments (0xab52c : word) = Some W_a8b68.
Proof. vm_refl. Qed.
Lemma D_a8b68 : decode_any W_a8b68 = Some (ShiftImm32 ALU_SRL 6 6 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a8b6c : bv 32 := 0x0053e2b3.
Lemma F_a8b6c : fetch_word AsanUbsan.M.loaded_segments (0xab530 : word) = Some W_a8b6c.
Proof. vm_refl. Qed.
Lemma D_a8b6c : decode_any W_a8b6c = Some (Op ALU_OR 5 7 5, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a8b70 : bv 32 := 0x01071393.
Lemma F_a8b70 : fetch_word AsanUbsan.M.loaded_segments (0xab534 : word) = Some W_a8b70.
Proof. vm_refl. Qed.
Lemma D_a8b70 : decode_any W_a8b70 = Some (ShiftImm ALU_SLL 7 14 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a8b74 : bv 32 := 0x0063e333.
Lemma F_a8b74 : fetch_word AsanUbsan.M.loaded_segments (0xab538 : word) = Some W_a8b74.
Proof. vm_refl. Qed.
Lemma D_a8b74 : decode_any W_a8b74 = Some (Op ALU_OR 6 7 6, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a8b78 : bv 32 := 0xff060613.
Lemma F_a8b78 : fetch_word AsanUbsan.M.loaded_segments (0xab53c : word) = Some W_a8b78.
Proof. vm_refl. Qed.
Lemma D_a8b78 : decode_any W_a8b78 = Some (OpImm ALU_ADD 12 12 4080, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a8b7c : bv 32 := 0x0106a023.
Lemma F_a8b7c : fetch_word AsanUbsan.M.loaded_segments (0xab540 : word) = Some W_a8b7c.
Proof. vm_refl. Qed.
Lemma D_a8b7c : decode_any W_a8b7c = Some (Store SZ4 13 16 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a8b80 : bv 32 := 0x0116a223.
Lemma F_a8b80 : fetch_word AsanUbsan.M.loaded_segments (0xab544 : word) = Some W_a8b80.
Proof. vm_refl. Qed.
Lemma D_a8b80 : decode_any W_a8b80 = Some (Store SZ4 13 17 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a8b84 : bv 32 := 0x0056a423.
Lemma F_a8b84 : fetch_word AsanUbsan.M.loaded_segments (0xab548 : word) = Some W_a8b84.
Proof. vm_refl. Qed.
Lemma D_a8b84 : decode_any W_a8b84 = Some (Store SZ4 13 5 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a8b88 : bv 32 := 0x0066a623.
Lemma F_a8b88 : fetch_word AsanUbsan.M.loaded_segments (0xab54c : word) = Some W_a8b88.
Proof. vm_refl. Qed.
Lemma D_a8b88 : decode_any W_a8b88 = Some (Store SZ4 13 6 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a8b8c : bv 32 := 0x01068693.
Lemma F_a8b8c : fetch_word AsanUbsan.M.loaded_segments (0xab550 : word) = Some W_a8b8c.
Proof. vm_refl. Qed.
Lemma D_a8b8c : decode_any W_a8b8c = Some (OpImm ALU_ADD 13 13 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a8b90 : bv 32 := 0x01058593.
Lemma F_a8b90 : fetch_word AsanUbsan.M.loaded_segments (0xab554 : word) = Some W_a8b90.
Proof. vm_refl. Qed.
Lemma D_a8b90 : decode_any W_a8b90 = Some (OpImm ALU_ADD 11 11 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a8b94 : bv 32 := 0xfac7e2e3.
Lemma F_a8b94 : fetch_word AsanUbsan.M.loaded_segments (0xab558 : word) = Some W_a8b94.
Proof. vm_refl. Qed.
Lemma D_a8b94 : decode_any W_a8b94 = Some (Branch BC_LTU 15 12 8100, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a8b98 : bv 32 := 0xff258593.
Lemma F_a8b98 : fetch_word AsanUbsan.M.loaded_segments (0xab55c : word) = Some W_a8b98.
Proof. vm_refl. Qed.
Lemma D_a8b98 : decode_any W_a8b98 = Some (OpImm ALU_ADD 11 11 4082, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a8b9c : bv 32 := 0x01000713.
Lemma F_a8b9c : fetch_word AsanUbsan.M.loaded_segments (0xab560 : word) = Some W_a8b9c.
Proof. vm_refl. Qed.
Lemma D_a8b9c : decode_any W_a8b9c = Some (OpImm ALU_ADD 14 0 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a8ba0 : bv 32 := 0xf4e66ae3.
Lemma F_a8ba0 : fetch_word AsanUbsan.M.loaded_segments (0xab564 : word) = Some W_a8ba0.
Proof. vm_refl. Qed.
Lemma D_a8ba0 : decode_any W_a8ba0 = Some (Branch BC_LTU 12 14 8020, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a8ba4 : bv 32 := 0x19c0006f.
Lemma F_a8ba4 : fetch_word AsanUbsan.M.loaded_segments (0xab568 : word) = Some W_a8ba4.
Proof. vm_refl. Qed.
Lemma D_a8ba4 : decode_any W_a8ba4 = Some (Jal 0 412, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a8ba8 : bv 32 := 0x00050693.
Lemma F_a8ba8 : fetch_word AsanUbsan.M.loaded_segments (0xab56c : word) = Some W_a8ba8.
Proof. vm_refl. Qed.
Lemma D_a8ba8 : decode_any W_a8ba8 = Some (OpImm ALU_ADD 13 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a8bac : bv 32 := 0x00357793.
Lemma F_a8bac : fetch_word AsanUbsan.M.loaded_segments (0xab570 : word) = Some W_a8bac.
Proof. vm_refl. Qed.
Lemma D_a8bac : decode_any W_a8bac = Some (OpImm ALU_AND 15 10 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a8bb0 : bv 32 := 0xf2079ae3.
Lemma F_a8bb0 : fetch_word AsanUbsan.M.loaded_segments (0xab574 : word) = Some W_a8bb0.
Proof. vm_refl. Qed.
Lemma D_a8bb0 : decode_any W_a8bb0 = Some (Branch BC_NE 15 0 7988, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a8bb4 : bv 32 := 0x01000713.
Lemma F_a8bb4 : fetch_word AsanUbsan.M.loaded_segments (0xab578 : word) = Some W_a8bb4.
Proof. vm_refl. Qed.
Lemma D_a8bb4 : decode_any W_a8bb4 = Some (OpImm ALU_ADD 14 0 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a8bb8 : bv 32 := 0x02e66c63.
Lemma F_a8bb8 : fetch_word AsanUbsan.M.loaded_segments (0xab57c : word) = Some W_a8bb8.
Proof. vm_refl. Qed.
Lemma D_a8bb8 : decode_any W_a8bb8 = Some (Branch BC_LTU 12 14 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a8bbc : bv 32 := 0x00f00713.
Lemma F_a8bbc : fetch_word AsanUbsan.M.loaded_segments (0xab580 : word) = Some W_a8bbc.
Proof. vm_refl. Qed.
Lemma D_a8bbc : decode_any W_a8bbc = Some (OpImm ALU_ADD 14 0 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a8bc0 : bv 32 := 0x0005a783.
Lemma F_a8bc0 : fetch_word AsanUbsan.M.loaded_segments (0xab584 : word) = Some W_a8bc0.
Proof. vm_refl. Qed.
Lemma D_a8bc0 : decode_any W_a8bc0 = Some (Load SZ4 true 15 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a8bc4 : bv 32 := 0x0045a803.
Lemma F_a8bc4 : fetch_word AsanUbsan.M.loaded_segments (0xab588 : word) = Some W_a8bc4.
Proof. vm_refl. Qed.
Lemma D_a8bc4 : decode_any W_a8bc4 = Some (Load SZ4 true 16 11 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a8bc8 : bv 32 := 0x0085a883.
Lemma F_a8bc8 : fetch_word AsanUbsan.M.loaded_segments (0xab58c : word) = Some W_a8bc8.
Proof. vm_refl. Qed.
Lemma D_a8bc8 : decode_any W_a8bc8 = Some (Load SZ4 true 17 11 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a8bcc : bv 32 := 0x00c5a283.
Lemma F_a8bcc : fetch_word AsanUbsan.M.loaded_segments (0xab590 : word) = Some W_a8bcc.
Proof. vm_refl. Qed.
Lemma D_a8bcc : decode_any W_a8bcc = Some (Load SZ4 true 5 11 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a8bd0 : bv 32 := 0x01058593.
Lemma F_a8bd0 : fetch_word AsanUbsan.M.loaded_segments (0xab594 : word) = Some W_a8bd0.
Proof. vm_refl. Qed.
Lemma D_a8bd0 : decode_any W_a8bd0 = Some (OpImm ALU_ADD 11 11 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a8bd4 : bv 32 := 0xff060613.
Lemma F_a8bd4 : fetch_word AsanUbsan.M.loaded_segments (0xab598 : word) = Some W_a8bd4.
Proof. vm_refl. Qed.
Lemma D_a8bd4 : decode_any W_a8bd4 = Some (OpImm ALU_ADD 12 12 4080, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a8bd8 : bv 32 := 0x00f6a023.
Lemma F_a8bd8 : fetch_word AsanUbsan.M.loaded_segments (0xab59c : word) = Some W_a8bd8.
Proof. vm_refl. Qed.
Lemma D_a8bd8 : decode_any W_a8bd8 = Some (Store SZ4 13 15 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a8bdc : bv 32 := 0x0106a223.
Lemma F_a8bdc : fetch_word AsanUbsan.M.loaded_segments (0xab5a0 : word) = Some W_a8bdc.
Proof. vm_refl. Qed.
Lemma D_a8bdc : decode_any W_a8bdc = Some (Store SZ4 13 16 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a8be0 : bv 32 := 0x0116a423.
Lemma F_a8be0 : fetch_word AsanUbsan.M.loaded_segments (0xab5a4 : word) = Some W_a8be0.
Proof. vm_refl. Qed.
Lemma D_a8be0 : decode_any W_a8be0 = Some (Store SZ4 13 17 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a8be4 : bv 32 := 0x0056a623.
Lemma F_a8be4 : fetch_word AsanUbsan.M.loaded_segments (0xab5a8 : word) = Some W_a8be4.
Proof. vm_refl. Qed.
Lemma D_a8be4 : decode_any W_a8be4 = Some (Store SZ4 13 5 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a8be8 : bv 32 := 0x01068693.
Lemma F_a8be8 : fetch_word AsanUbsan.M.loaded_segments (0xab5ac : word) = Some W_a8be8.
Proof. vm_refl. Qed.
Lemma D_a8be8 : decode_any W_a8be8 = Some (OpImm ALU_ADD 13 13 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a8bec : bv 32 := 0xfcc76ae3.
Lemma F_a8bec : fetch_word AsanUbsan.M.loaded_segments (0xab5b0 : word) = Some W_a8bec.
Proof. vm_refl. Qed.
Lemma D_a8bec : decode_any W_a8bec = Some (Branch BC_LTU 14 12 8148, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a8bf0 : bv 32 := 0x00800713.
Lemma F_a8bf0 : fetch_word AsanUbsan.M.loaded_segments (0xab5b4 : word) = Some W_a8bf0.
Proof. vm_refl. Qed.
Lemma D_a8bf0 : decode_any W_a8bf0 = Some (OpImm ALU_ADD 14 0 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a8bf4 : bv 32 := 0x00e66e63.
Lemma F_a8bf4 : fetch_word AsanUbsan.M.loaded_segments (0xab5b8 : word) = Some W_a8bf4.
Proof. vm_refl. Qed.
Lemma D_a8bf4 : decode_any W_a8bf4 = Some (Branch BC_LTU 12 14 28, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a8bf8 : bv 32 := 0x0005a703.
Lemma F_a8bf8 : fetch_word AsanUbsan.M.loaded_segments (0xab5bc : word) = Some W_a8bf8.
Proof. vm_refl. Qed.
Lemma D_a8bf8 : decode_any W_a8bf8 = Some (Load SZ4 true 14 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a8bfc : bv 32 := 0x0045a783.
Lemma F_a8bfc : fetch_word AsanUbsan.M.loaded_segments (0xab5c0 : word) = Some W_a8bfc.
Proof. vm_refl. Qed.
Lemma D_a8bfc : decode_any W_a8bfc = Some (Load SZ4 true 15 11 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a8c00 : bv 32 := 0x00e6a023.
Lemma F_a8c00 : fetch_word AsanUbsan.M.loaded_segments (0xab5c4 : word) = Some W_a8c00.
Proof. vm_refl. Qed.
Lemma D_a8c00 : decode_any W_a8c00 = Some (Store SZ4 13 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a8c04 : bv 32 := 0x00f6a223.
Lemma F_a8c04 : fetch_word AsanUbsan.M.loaded_segments (0xab5c8 : word) = Some W_a8c04.
Proof. vm_refl. Qed.
Lemma D_a8c04 : decode_any W_a8c04 = Some (Store SZ4 13 15 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a8c08 : bv 32 := 0x00868693.
Lemma F_a8c08 : fetch_word AsanUbsan.M.loaded_segments (0xab5cc : word) = Some W_a8c08.
Proof. vm_refl. Qed.
Lemma D_a8c08 : decode_any W_a8c08 = Some (OpImm ALU_ADD 13 13 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a8c0c : bv 32 := 0x00858593.
Lemma F_a8c0c : fetch_word AsanUbsan.M.loaded_segments (0xab5d0 : word) = Some W_a8c0c.
Proof. vm_refl. Qed.
Lemma D_a8c0c : decode_any W_a8c0c = Some (OpImm ALU_ADD 11 11 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a8c10 : bv 32 := 0x00467713.
Lemma F_a8c10 : fetch_word AsanUbsan.M.loaded_segments (0xab5d4 : word) = Some W_a8c10.
Proof. vm_refl. Qed.
Lemma D_a8c10 : decode_any W_a8c10 = Some (OpImm ALU_AND 14 12 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a8c14 : bv 32 := 0x24070063.
Lemma F_a8c14 : fetch_word AsanUbsan.M.loaded_segments (0xab5d8 : word) = Some W_a8c14.
Proof. vm_refl. Qed.
Lemma D_a8c14 : decode_any W_a8c14 = Some (Branch BC_EQ 14 0 576, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a8c18 : bv 32 := 0x0005a703.
Lemma F_a8c18 : fetch_word AsanUbsan.M.loaded_segments (0xab5dc : word) = Some W_a8c18.
Proof. vm_refl. Qed.
Lemma D_a8c18 : decode_any W_a8c18 = Some (Load SZ4 true 14 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a8c1c : bv 32 := 0x00458593.
Lemma F_a8c1c : fetch_word AsanUbsan.M.loaded_segments (0xab5e0 : word) = Some W_a8c1c.
Proof. vm_refl. Qed.
Lemma D_a8c1c : decode_any W_a8c1c = Some (OpImm ALU_ADD 11 11 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a8c20 : bv 32 := 0x00e6a023.
Lemma F_a8c20 : fetch_word AsanUbsan.M.loaded_segments (0xab5e4 : word) = Some W_a8c20.
Proof. vm_refl. Qed.
Lemma D_a8c20 : decode_any W_a8c20 = Some (Store SZ4 13 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a8c24 : bv 32 := 0x00468693.
Lemma F_a8c24 : fetch_word AsanUbsan.M.loaded_segments (0xab5e8 : word) = Some W_a8c24.
Proof. vm_refl. Qed.
Lemma D_a8c24 : decode_any W_a8c24 = Some (OpImm ALU_ADD 13 13 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a8c28 : bv 32 := 0x22c0006f.
Lemma F_a8c28 : fetch_word AsanUbsan.M.loaded_segments (0xab5ec : word) = Some W_a8c28.
Proof. vm_refl. Qed.
Lemma D_a8c28 : decode_any W_a8c28 = Some (Jal 0 556, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a8c2c : bv 32 := 0x00e68023.
Lemma F_a8c2c : fetch_word AsanUbsan.M.loaded_segments (0xab5f0 : word) = Some W_a8c2c.
Proof. vm_refl. Qed.
Lemma D_a8c2c : decode_any W_a8c2c = Some (Store SZ1 13 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a8c30 : bv 32 := 0x00168693.
Lemma F_a8c30 : fetch_word AsanUbsan.M.loaded_segments (0xab5f4 : word) = Some W_a8c30.
Proof. vm_refl. Qed.
Lemma D_a8c30 : decode_any W_a8c30 = Some (OpImm ALU_ADD 13 13 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a8c34 : bv 32 := 0xfff60613.
Lemma F_a8c34 : fetch_word AsanUbsan.M.loaded_segments (0xab5f8 : word) = Some W_a8c34.
Proof. vm_refl. Qed.
Lemma D_a8c34 : decode_any W_a8c34 = Some (OpImm ALU_ADD 12 12 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a8c38 : bv 32 := 0x01058593.
Lemma F_a8c38 : fetch_word AsanUbsan.M.loaded_segments (0xab5fc : word) = Some W_a8c38.
Proof. vm_refl. Qed.
Lemma D_a8c38 : decode_any W_a8c38 = Some (OpImm ALU_ADD 11 11 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a8c3c : bv 32 := 0x01200793.
Lemma F_a8c3c : fetch_word AsanUbsan.M.loaded_segments (0xab600 : word) = Some W_a8c3c.
Proof. vm_refl. Qed.
Lemma D_a8c3c : decode_any W_a8c3c = Some (OpImm ALU_ADD 15 0 18, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a8c40 : bv 32 := 0x0087581b.
Lemma F_a8c40 : fetch_word AsanUbsan.M.loaded_segments (0xab604 : word) = Some W_a8c40.
Proof. vm_refl. Qed.
Lemma D_a8c40 : decode_any W_a8c40 = Some (ShiftImm32 ALU_SRL 16 14 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a8c44 : bv 32 := 0xff45a883.
Lemma F_a8c44 : fetch_word AsanUbsan.M.loaded_segments (0xab608 : word) = Some W_a8c44.
Proof. vm_refl. Qed.
Lemma D_a8c44 : decode_any W_a8c44 = Some (Load SZ4 true 17 11 4084, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a8c48 : bv 32 := 0xff85a283.
Lemma F_a8c48 : fetch_word AsanUbsan.M.loaded_segments (0xab60c : word) = Some W_a8c48.
Proof. vm_refl. Qed.
Lemma D_a8c48 : decode_any W_a8c48 = Some (Load SZ4 true 5 11 4088, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a8c4c : bv 32 := 0xffc5a303.
Lemma F_a8c4c : fetch_word AsanUbsan.M.loaded_segments (0xab610 : word) = Some W_a8c4c.
Proof. vm_refl. Qed.
Lemma D_a8c4c : decode_any W_a8c4c = Some (Load SZ4 true 6 11 4092, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a8c50 : bv 32 := 0x0005a703.
Lemma F_a8c50 : fetch_word AsanUbsan.M.loaded_segments (0xab614 : word) = Some W_a8c50.
Proof. vm_refl. Qed.
Lemma D_a8c50 : decode_any W_a8c50 = Some (Load SZ4 true 14 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a8c54 : bv 32 := 0x01889393.
Lemma F_a8c54 : fetch_word AsanUbsan.M.loaded_segments (0xab618 : word) = Some W_a8c54.
Proof. vm_refl. Qed.
Lemma D_a8c54 : decode_any W_a8c54 = Some (ShiftImm ALU_SLL 7 17 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a8c58 : bv 32 := 0x0088d89b.
Lemma F_a8c58 : fetch_word AsanUbsan.M.loaded_segments (0xab61c : word) = Some W_a8c58.
Proof. vm_refl. Qed.
Lemma D_a8c58 : decode_any W_a8c58 = Some (ShiftImm32 ALU_SRL 17 17 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a8c5c : bv 32 := 0x0103e833.
Lemma F_a8c5c : fetch_word AsanUbsan.M.loaded_segments (0xab620 : word) = Some W_a8c5c.
Proof. vm_refl. Qed.
Lemma D_a8c5c : decode_any W_a8c5c = Some (Op ALU_OR 16 7 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a8c60 : bv 32 := 0x01829393.
Lemma F_a8c60 : fetch_word AsanUbsan.M.loaded_segments (0xab624 : word) = Some W_a8c60.
Proof. vm_refl. Qed.
Lemma D_a8c60 : decode_any W_a8c60 = Some (ShiftImm ALU_SLL 7 5 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a8c64 : bv 32 := 0x0082d29b.
Lemma F_a8c64 : fetch_word AsanUbsan.M.loaded_segments (0xab628 : word) = Some W_a8c64.
Proof. vm_refl. Qed.
Lemma D_a8c64 : decode_any W_a8c64 = Some (ShiftImm32 ALU_SRL 5 5 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a8c68 : bv 32 := 0x0113e8b3.
Lemma F_a8c68 : fetch_word AsanUbsan.M.loaded_segments (0xab62c : word) = Some W_a8c68.
Proof. vm_refl. Qed.
Lemma D_a8c68 : decode_any W_a8c68 = Some (Op ALU_OR 17 7 17, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a8c6c : bv 32 := 0x01831393.
Lemma F_a8c6c : fetch_word AsanUbsan.M.loaded_segments (0xab630 : word) = Some W_a8c6c.
Proof. vm_refl. Qed.
Lemma D_a8c6c : decode_any W_a8c6c = Some (ShiftImm ALU_SLL 7 6 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a8c70 : bv 32 := 0x0083531b.
Lemma F_a8c70 : fetch_word AsanUbsan.M.loaded_segments (0xab634 : word) = Some W_a8c70.
Proof. vm_refl. Qed.
Lemma D_a8c70 : decode_any W_a8c70 = Some (ShiftImm32 ALU_SRL 6 6 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a8c74 : bv 32 := 0x0053e2b3.
Lemma F_a8c74 : fetch_word AsanUbsan.M.loaded_segments (0xab638 : word) = Some W_a8c74.
Proof. vm_refl. Qed.
Lemma D_a8c74 : decode_any W_a8c74 = Some (Op ALU_OR 5 7 5, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a8c78 : bv 32 := 0x01871393.
Lemma F_a8c78 : fetch_word AsanUbsan.M.loaded_segments (0xab63c : word) = Some W_a8c78.
Proof. vm_refl. Qed.
Lemma D_a8c78 : decode_any W_a8c78 = Some (ShiftImm ALU_SLL 7 14 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a8c7c : bv 32 := 0x0063e333.
Lemma F_a8c7c : fetch_word AsanUbsan.M.loaded_segments (0xab640 : word) = Some W_a8c7c.
Proof. vm_refl. Qed.
Lemma D_a8c7c : decode_any W_a8c7c = Some (Op ALU_OR 6 7 6, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a8c80 : bv 32 := 0xff060613.
Lemma F_a8c80 : fetch_word AsanUbsan.M.loaded_segments (0xab644 : word) = Some W_a8c80.
Proof. vm_refl. Qed.
Lemma D_a8c80 : decode_any W_a8c80 = Some (OpImm ALU_ADD 12 12 4080, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a8c84 : bv 32 := 0x0106a023.
Lemma F_a8c84 : fetch_word AsanUbsan.M.loaded_segments (0xab648 : word) = Some W_a8c84.
Proof. vm_refl. Qed.
Lemma D_a8c84 : decode_any W_a8c84 = Some (Store SZ4 13 16 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a8c88 : bv 32 := 0x0116a223.
Lemma F_a8c88 : fetch_word AsanUbsan.M.loaded_segments (0xab64c : word) = Some W_a8c88.
Proof. vm_refl. Qed.
Lemma D_a8c88 : decode_any W_a8c88 = Some (Store SZ4 13 17 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a8c8c : bv 32 := 0x0056a423.
Lemma F_a8c8c : fetch_word AsanUbsan.M.loaded_segments (0xab650 : word) = Some W_a8c8c.
Proof. vm_refl. Qed.
Lemma D_a8c8c : decode_any W_a8c8c = Some (Store SZ4 13 5 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a8c90 : bv 32 := 0x0066a623.
Lemma F_a8c90 : fetch_word AsanUbsan.M.loaded_segments (0xab654 : word) = Some W_a8c90.
Proof. vm_refl. Qed.
Lemma D_a8c90 : decode_any W_a8c90 = Some (Store SZ4 13 6 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a8c94 : bv 32 := 0x01068693.
Lemma F_a8c94 : fetch_word AsanUbsan.M.loaded_segments (0xab658 : word) = Some W_a8c94.
Proof. vm_refl. Qed.
Lemma D_a8c94 : decode_any W_a8c94 = Some (OpImm ALU_ADD 13 13 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a8c98 : bv 32 := 0x01058593.
Lemma F_a8c98 : fetch_word AsanUbsan.M.loaded_segments (0xab65c : word) = Some W_a8c98.
Proof. vm_refl. Qed.
Lemma D_a8c98 : decode_any W_a8c98 = Some (OpImm ALU_ADD 11 11 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a8c9c : bv 32 := 0xfac7e2e3.
Lemma F_a8c9c : fetch_word AsanUbsan.M.loaded_segments (0xab660 : word) = Some W_a8c9c.
Proof. vm_refl. Qed.
Lemma D_a8c9c : decode_any W_a8c9c = Some (Branch BC_LTU 15 12 8100, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a8ca0 : bv 32 := 0xff158593.
Lemma F_a8ca0 : fetch_word AsanUbsan.M.loaded_segments (0xab664 : word) = Some W_a8ca0.
Proof. vm_refl. Qed.
Lemma D_a8ca0 : decode_any W_a8ca0 = Some (OpImm ALU_ADD 11 11 4081, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a8ca4 : bv 32 := 0x01000713.
Lemma F_a8ca4 : fetch_word AsanUbsan.M.loaded_segments (0xab668 : word) = Some W_a8ca4.
Proof. vm_refl. Qed.
Lemma D_a8ca4 : decode_any W_a8ca4 = Some (OpImm ALU_ADD 14 0 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a8ca8 : bv 32 := 0xe4e666e3.
Lemma F_a8ca8 : fetch_word AsanUbsan.M.loaded_segments (0xab66c : word) = Some W_a8ca8.
Proof. vm_refl. Qed.
Lemma D_a8ca8 : decode_any W_a8ca8 = Some (Branch BC_LTU 12 14 7756, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a8cac : bv 32 := 0x0940006f.
Lemma F_a8cac : fetch_word AsanUbsan.M.loaded_segments (0xab670 : word) = Some W_a8cac.
Proof. vm_refl. Qed.
Lemma D_a8cac : decode_any W_a8cac = Some (Jal 0 148, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a8cb0 : bv 32 := 0x00875793.
Lemma F_a8cb0 : fetch_word AsanUbsan.M.loaded_segments (0xab674 : word) = Some W_a8cb0.
Proof. vm_refl. Qed.
Lemma D_a8cb0 : decode_any W_a8cb0 = Some (ShiftImm ALU_SRL 15 14 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a8cb4 : bv 32 := 0x01075813.
Lemma F_a8cb4 : fetch_word AsanUbsan.M.loaded_segments (0xab678 : word) = Some W_a8cb4.
Proof. vm_refl. Qed.
Lemma D_a8cb4 : decode_any W_a8cb4 = Some (ShiftImm ALU_SRL 16 14 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a8cb8 : bv 32 := 0xffd60613.
Lemma F_a8cb8 : fetch_word AsanUbsan.M.loaded_segments (0xab67c : word) = Some W_a8cb8.
Proof. vm_refl. Qed.
Lemma D_a8cb8 : decode_any W_a8cb8 = Some (OpImm ALU_ADD 12 12 4093, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a8cbc : bv 32 := 0x00e68023.
Lemma F_a8cbc : fetch_word AsanUbsan.M.loaded_segments (0xab680 : word) = Some W_a8cbc.
Proof. vm_refl. Qed.
Lemma D_a8cbc : decode_any W_a8cbc = Some (Store SZ1 13 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a8cc0 : bv 32 := 0x00f680a3.
Lemma F_a8cc0 : fetch_word AsanUbsan.M.loaded_segments (0xab684 : word) = Some W_a8cc0.
Proof. vm_refl. Qed.
Lemma D_a8cc0 : decode_any W_a8cc0 = Some (Store SZ1 13 15 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a8cc4 : bv 32 := 0x01068123.
Lemma F_a8cc4 : fetch_word AsanUbsan.M.loaded_segments (0xab688 : word) = Some W_a8cc4.
Proof. vm_refl. Qed.
Lemma D_a8cc4 : decode_any W_a8cc4 = Some (Store SZ1 13 16 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a8cc8 : bv 32 := 0x00368693.
Lemma F_a8cc8 : fetch_word AsanUbsan.M.loaded_segments (0xab68c : word) = Some W_a8cc8.
Proof. vm_refl. Qed.
Lemma D_a8cc8 : decode_any W_a8cc8 = Some (OpImm ALU_ADD 13 13 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a8ccc : bv 32 := 0x01058593.
Lemma F_a8ccc : fetch_word AsanUbsan.M.loaded_segments (0xab690 : word) = Some W_a8ccc.
Proof. vm_refl. Qed.
Lemma D_a8ccc : decode_any W_a8ccc = Some (OpImm ALU_ADD 11 11 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a8cd0 : bv 32 := 0x01000793.
Lemma F_a8cd0 : fetch_word AsanUbsan.M.loaded_segments (0xab694 : word) = Some W_a8cd0.
Proof. vm_refl. Qed.
Lemma D_a8cd0 : decode_any W_a8cd0 = Some (OpImm ALU_ADD 15 0 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a8cd4 : bv 32 := 0x0187581b.
Lemma F_a8cd4 : fetch_word AsanUbsan.M.loaded_segments (0xab698 : word) = Some W_a8cd4.
Proof. vm_refl. Qed.
Lemma D_a8cd4 : decode_any W_a8cd4 = Some (ShiftImm32 ALU_SRL 16 14 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a8cd8 : bv 32 := 0xff45a883.
Lemma F_a8cd8 : fetch_word AsanUbsan.M.loaded_segments (0xab69c : word) = Some W_a8cd8.
Proof. vm_refl. Qed.
Lemma D_a8cd8 : decode_any W_a8cd8 = Some (Load SZ4 true 17 11 4084, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a8cdc : bv 32 := 0xff85a283.
Lemma F_a8cdc : fetch_word AsanUbsan.M.loaded_segments (0xab6a0 : word) = Some W_a8cdc.
Proof. vm_refl. Qed.
Lemma D_a8cdc : decode_any W_a8cdc = Some (Load SZ4 true 5 11 4088, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a8ce0 : bv 32 := 0xffc5a303.
Lemma F_a8ce0 : fetch_word AsanUbsan.M.loaded_segments (0xab6a4 : word) = Some W_a8ce0.
Proof. vm_refl. Qed.
Lemma D_a8ce0 : decode_any W_a8ce0 = Some (Load SZ4 true 6 11 4092, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a8ce4 : bv 32 := 0x0005a703.
Lemma F_a8ce4 : fetch_word AsanUbsan.M.loaded_segments (0xab6a8 : word) = Some W_a8ce4.
Proof. vm_refl. Qed.
Lemma D_a8ce4 : decode_any W_a8ce4 = Some (Load SZ4 true 14 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a8ce8 : bv 32 := 0x00889393.
Lemma F_a8ce8 : fetch_word AsanUbsan.M.loaded_segments (0xab6ac : word) = Some W_a8ce8.
Proof. vm_refl. Qed.
Lemma D_a8ce8 : decode_any W_a8ce8 = Some (ShiftImm ALU_SLL 7 17 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a8cec : bv 32 := 0x0188d89b.
Lemma F_a8cec : fetch_word AsanUbsan.M.loaded_segments (0xab6b0 : word) = Some W_a8cec.
Proof. vm_refl. Qed.
Lemma D_a8cec : decode_any W_a8cec = Some (ShiftImm32 ALU_SRL 17 17 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a8cf0 : bv 32 := 0x0103e833.
Lemma F_a8cf0 : fetch_word AsanUbsan.M.loaded_segments (0xab6b4 : word) = Some W_a8cf0.
Proof. vm_refl. Qed.
Lemma D_a8cf0 : decode_any W_a8cf0 = Some (Op ALU_OR 16 7 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a8cf4 : bv 32 := 0x00829393.
Lemma F_a8cf4 : fetch_word AsanUbsan.M.loaded_segments (0xab6b8 : word) = Some W_a8cf4.
Proof. vm_refl. Qed.
Lemma D_a8cf4 : decode_any W_a8cf4 = Some (ShiftImm ALU_SLL 7 5 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a8cf8 : bv 32 := 0x0182d29b.
Lemma F_a8cf8 : fetch_word AsanUbsan.M.loaded_segments (0xab6bc : word) = Some W_a8cf8.
Proof. vm_refl. Qed.
Lemma D_a8cf8 : decode_any W_a8cf8 = Some (ShiftImm32 ALU_SRL 5 5 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a8cfc : bv 32 := 0x0113e8b3.
Lemma F_a8cfc : fetch_word AsanUbsan.M.loaded_segments (0xab6c0 : word) = Some W_a8cfc.
Proof. vm_refl. Qed.
Lemma D_a8cfc : decode_any W_a8cfc = Some (Op ALU_OR 17 7 17, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a8d00 : bv 32 := 0x00831393.
Lemma F_a8d00 : fetch_word AsanUbsan.M.loaded_segments (0xab6c4 : word) = Some W_a8d00.
Proof. vm_refl. Qed.
Lemma D_a8d00 : decode_any W_a8d00 = Some (ShiftImm ALU_SLL 7 6 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a8d04 : bv 32 := 0x0183531b.
Lemma F_a8d04 : fetch_word AsanUbsan.M.loaded_segments (0xab6c8 : word) = Some W_a8d04.
Proof. vm_refl. Qed.
Lemma D_a8d04 : decode_any W_a8d04 = Some (ShiftImm32 ALU_SRL 6 6 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a8d08 : bv 32 := 0x0053e2b3.
Lemma F_a8d08 : fetch_word AsanUbsan.M.loaded_segments (0xab6cc : word) = Some W_a8d08.
Proof. vm_refl. Qed.
Lemma D_a8d08 : decode_any W_a8d08 = Some (Op ALU_OR 5 7 5, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a8d0c : bv 32 := 0x00871393.
Lemma F_a8d0c : fetch_word AsanUbsan.M.loaded_segments (0xab6d0 : word) = Some W_a8d0c.
Proof. vm_refl. Qed.
Lemma D_a8d0c : decode_any W_a8d0c = Some (ShiftImm ALU_SLL 7 14 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a8d10 : bv 32 := 0x0063e333.
Lemma F_a8d10 : fetch_word AsanUbsan.M.loaded_segments (0xab6d4 : word) = Some W_a8d10.
Proof. vm_refl. Qed.
Lemma D_a8d10 : decode_any W_a8d10 = Some (Op ALU_OR 6 7 6, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a8d14 : bv 32 := 0xff060613.
Lemma F_a8d14 : fetch_word AsanUbsan.M.loaded_segments (0xab6d8 : word) = Some W_a8d14.
Proof. vm_refl. Qed.
Lemma D_a8d14 : decode_any W_a8d14 = Some (OpImm ALU_ADD 12 12 4080, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a8d18 : bv 32 := 0x0106a023.
Lemma F_a8d18 : fetch_word AsanUbsan.M.loaded_segments (0xab6dc : word) = Some W_a8d18.
Proof. vm_refl. Qed.
Lemma D_a8d18 : decode_any W_a8d18 = Some (Store SZ4 13 16 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a8d1c : bv 32 := 0x0116a223.
Lemma F_a8d1c : fetch_word AsanUbsan.M.loaded_segments (0xab6e0 : word) = Some W_a8d1c.
Proof. vm_refl. Qed.
Lemma D_a8d1c : decode_any W_a8d1c = Some (Store SZ4 13 17 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a8d20 : bv 32 := 0x0056a423.
Lemma F_a8d20 : fetch_word AsanUbsan.M.loaded_segments (0xab6e4 : word) = Some W_a8d20.
Proof. vm_refl. Qed.
Lemma D_a8d20 : decode_any W_a8d20 = Some (Store SZ4 13 5 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a8d24 : bv 32 := 0x0066a623.
Lemma F_a8d24 : fetch_word AsanUbsan.M.loaded_segments (0xab6e8 : word) = Some W_a8d24.
Proof. vm_refl. Qed.
Lemma D_a8d24 : decode_any W_a8d24 = Some (Store SZ4 13 6 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a8d28 : bv 32 := 0x01068693.
Lemma F_a8d28 : fetch_word AsanUbsan.M.loaded_segments (0xab6ec : word) = Some W_a8d28.
Proof. vm_refl. Qed.
Lemma D_a8d28 : decode_any W_a8d28 = Some (OpImm ALU_ADD 13 13 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a8d2c : bv 32 := 0x01058593.
Lemma F_a8d2c : fetch_word AsanUbsan.M.loaded_segments (0xab6f0 : word) = Some W_a8d2c.
Proof. vm_refl. Qed.
Lemma D_a8d2c : decode_any W_a8d2c = Some (OpImm ALU_ADD 11 11 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a8d30 : bv 32 := 0xfac7e2e3.
Lemma F_a8d30 : fetch_word AsanUbsan.M.loaded_segments (0xab6f4 : word) = Some W_a8d30.
Proof. vm_refl. Qed.
Lemma D_a8d30 : decode_any W_a8d30 = Some (Branch BC_LTU 15 12 8100, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a8d34 : bv 32 := 0xff358593.
Lemma F_a8d34 : fetch_word AsanUbsan.M.loaded_segments (0xab6f8 : word) = Some W_a8d34.
Proof. vm_refl. Qed.
Lemma D_a8d34 : decode_any W_a8d34 = Some (OpImm ALU_ADD 11 11 4083, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a8d38 : bv 32 := 0x01000713.
Lemma F_a8d38 : fetch_word AsanUbsan.M.loaded_segments (0xab6fc : word) = Some W_a8d38.
Proof. vm_refl. Qed.
Lemma D_a8d38 : decode_any W_a8d38 = Some (OpImm ALU_ADD 14 0 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a8d3c : bv 32 := 0xdae66ce3.
Lemma F_a8d3c : fetch_word AsanUbsan.M.loaded_segments (0xab700 : word) = Some W_a8d3c.
Proof. vm_refl. Qed.
Lemma D_a8d3c : decode_any W_a8d3c = Some (Branch BC_LTU 12 14 7608, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a8d40 : bv 32 := 0x0005c703.
Lemma F_a8d40 : fetch_word AsanUbsan.M.loaded_segments (0xab704 : word) = Some W_a8d40.
Proof. vm_refl. Qed.
Lemma D_a8d40 : decode_any W_a8d40 = Some (Load SZ1 false 14 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a8d44 : bv 32 := 0x0015c783.
Lemma F_a8d44 : fetch_word AsanUbsan.M.loaded_segments (0xab708 : word) = Some W_a8d44.
Proof. vm_refl. Qed.
Lemma D_a8d44 : decode_any W_a8d44 = Some (Load SZ1 false 15 11 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a8d48 : bv 32 := 0x0025c803.
Lemma F_a8d48 : fetch_word AsanUbsan.M.loaded_segments (0xab70c : word) = Some W_a8d48.
Proof. vm_refl. Qed.
Lemma D_a8d48 : decode_any W_a8d48 = Some (Load SZ1 false 16 11 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a8d4c : bv 32 := 0x0035c883.
Lemma F_a8d4c : fetch_word AsanUbsan.M.loaded_segments (0xab710 : word) = Some W_a8d4c.
Proof. vm_refl. Qed.
Lemma D_a8d4c : decode_any W_a8d4c = Some (Load SZ1 false 17 11 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a8d50 : bv 32 := 0x0045c283.
Lemma F_a8d50 : fetch_word AsanUbsan.M.loaded_segments (0xab714 : word) = Some W_a8d50.
Proof. vm_refl. Qed.
Lemma D_a8d50 : decode_any W_a8d50 = Some (Load SZ1 false 5 11 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a8d54 : bv 32 := 0x0055c303.
Lemma F_a8d54 : fetch_word AsanUbsan.M.loaded_segments (0xab718 : word) = Some W_a8d54.
Proof. vm_refl. Qed.
Lemma D_a8d54 : decode_any W_a8d54 = Some (Load SZ1 false 6 11 5, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a8d58 : bv 32 := 0x0065c383.
Lemma F_a8d58 : fetch_word AsanUbsan.M.loaded_segments (0xab71c : word) = Some W_a8d58.
Proof. vm_refl. Qed.
Lemma D_a8d58 : decode_any W_a8d58 = Some (Load SZ1 false 7 11 6, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a8d5c : bv 32 := 0x0075ce03.
Lemma F_a8d5c : fetch_word AsanUbsan.M.loaded_segments (0xab720 : word) = Some W_a8d5c.
Proof. vm_refl. Qed.
Lemma D_a8d5c : decode_any W_a8d5c = Some (Load SZ1 false 28 11 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a8d60 : bv 32 := 0x00e68023.
Lemma F_a8d60 : fetch_word AsanUbsan.M.loaded_segments (0xab724 : word) = Some W_a8d60.
Proof. vm_refl. Qed.
Lemma D_a8d60 : decode_any W_a8d60 = Some (Store SZ1 13 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a8d64 : bv 32 := 0x00f680a3.
Lemma F_a8d64 : fetch_word AsanUbsan.M.loaded_segments (0xab728 : word) = Some W_a8d64.
Proof. vm_refl. Qed.
Lemma D_a8d64 : decode_any W_a8d64 = Some (Store SZ1 13 15 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a8d68 : bv 32 := 0x01068123.
Lemma F_a8d68 : fetch_word AsanUbsan.M.loaded_segments (0xab72c : word) = Some W_a8d68.
Proof. vm_refl. Qed.
Lemma D_a8d68 : decode_any W_a8d68 = Some (Store SZ1 13 16 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a8d6c : bv 32 := 0x011681a3.
Lemma F_a8d6c : fetch_word AsanUbsan.M.loaded_segments (0xab730 : word) = Some W_a8d6c.
Proof. vm_refl. Qed.
Lemma D_a8d6c : decode_any W_a8d6c = Some (Store SZ1 13 17 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a8d70 : bv 32 := 0x0085c703.
Lemma F_a8d70 : fetch_word AsanUbsan.M.loaded_segments (0xab734 : word) = Some W_a8d70.
Proof. vm_refl. Qed.
Lemma D_a8d70 : decode_any W_a8d70 = Some (Load SZ1 false 14 11 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a8d74 : bv 32 := 0x0095c783.
Lemma F_a8d74 : fetch_word AsanUbsan.M.loaded_segments (0xab738 : word) = Some W_a8d74.
Proof. vm_refl. Qed.
Lemma D_a8d74 : decode_any W_a8d74 = Some (Load SZ1 false 15 11 9, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a8d78 : bv 32 := 0x00a5c803.
Lemma F_a8d78 : fetch_word AsanUbsan.M.loaded_segments (0xab73c : word) = Some W_a8d78.
Proof. vm_refl. Qed.
Lemma D_a8d78 : decode_any W_a8d78 = Some (Load SZ1 false 16 11 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a8d7c : bv 32 := 0x00b5c883.
Lemma F_a8d7c : fetch_word AsanUbsan.M.loaded_segments (0xab740 : word) = Some W_a8d7c.
Proof. vm_refl. Qed.
Lemma D_a8d7c : decode_any W_a8d7c = Some (Load SZ1 false 17 11 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a8d80 : bv 32 := 0x00568223.
Lemma F_a8d80 : fetch_word AsanUbsan.M.loaded_segments (0xab744 : word) = Some W_a8d80.
Proof. vm_refl. Qed.
Lemma D_a8d80 : decode_any W_a8d80 = Some (Store SZ1 13 5 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a8d84 : bv 32 := 0x006682a3.
Lemma F_a8d84 : fetch_word AsanUbsan.M.loaded_segments (0xab748 : word) = Some W_a8d84.
Proof. vm_refl. Qed.
Lemma D_a8d84 : decode_any W_a8d84 = Some (Store SZ1 13 6 5, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a8d88 : bv 32 := 0x00768323.
Lemma F_a8d88 : fetch_word AsanUbsan.M.loaded_segments (0xab74c : word) = Some W_a8d88.
Proof. vm_refl. Qed.
Lemma D_a8d88 : decode_any W_a8d88 = Some (Store SZ1 13 7 6, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a8d8c : bv 32 := 0x01c683a3.
Lemma F_a8d8c : fetch_word AsanUbsan.M.loaded_segments (0xab750 : word) = Some W_a8d8c.
Proof. vm_refl. Qed.
Lemma D_a8d8c : decode_any W_a8d8c = Some (Store SZ1 13 28 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a8d90 : bv 32 := 0x00c5c283.
Lemma F_a8d90 : fetch_word AsanUbsan.M.loaded_segments (0xab754 : word) = Some W_a8d90.
Proof. vm_refl. Qed.
Lemma D_a8d90 : decode_any W_a8d90 = Some (Load SZ1 false 5 11 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a8d94 : bv 32 := 0x00d5c303.
Lemma F_a8d94 : fetch_word AsanUbsan.M.loaded_segments (0xab758 : word) = Some W_a8d94.
Proof. vm_refl. Qed.
Lemma D_a8d94 : decode_any W_a8d94 = Some (Load SZ1 false 6 11 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a8d98 : bv 32 := 0x00e5c383.
Lemma F_a8d98 : fetch_word AsanUbsan.M.loaded_segments (0xab75c : word) = Some W_a8d98.
Proof. vm_refl. Qed.
Lemma D_a8d98 : decode_any W_a8d98 = Some (Load SZ1 false 7 11 14, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a8d9c : bv 32 := 0x00f5ce03.
Lemma F_a8d9c : fetch_word AsanUbsan.M.loaded_segments (0xab760 : word) = Some W_a8d9c.
Proof. vm_refl. Qed.
Lemma D_a8d9c : decode_any W_a8d9c = Some (Load SZ1 false 28 11 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a8da0 : bv 32 := 0x01058593.
Lemma F_a8da0 : fetch_word AsanUbsan.M.loaded_segments (0xab764 : word) = Some W_a8da0.
Proof. vm_refl. Qed.
Lemma D_a8da0 : decode_any W_a8da0 = Some (OpImm ALU_ADD 11 11 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a8da4 : bv 32 := 0x00e68423.
Lemma F_a8da4 : fetch_word AsanUbsan.M.loaded_segments (0xab768 : word) = Some W_a8da4.
Proof. vm_refl. Qed.
Lemma D_a8da4 : decode_any W_a8da4 = Some (Store SZ1 13 14 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a8da8 : bv 32 := 0x00f684a3.
Lemma F_a8da8 : fetch_word AsanUbsan.M.loaded_segments (0xab76c : word) = Some W_a8da8.
Proof. vm_refl. Qed.
Lemma D_a8da8 : decode_any W_a8da8 = Some (Store SZ1 13 15 9, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a8dac : bv 32 := 0x01068523.
Lemma F_a8dac : fetch_word AsanUbsan.M.loaded_segments (0xab770 : word) = Some W_a8dac.
Proof. vm_refl. Qed.
Lemma D_a8dac : decode_any W_a8dac = Some (Store SZ1 13 16 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a8db0 : bv 32 := 0x011685a3.
Lemma F_a8db0 : fetch_word AsanUbsan.M.loaded_segments (0xab774 : word) = Some W_a8db0.
Proof. vm_refl. Qed.
Lemma D_a8db0 : decode_any W_a8db0 = Some (Store SZ1 13 17 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a8db4 : bv 32 := 0x01068713.
Lemma F_a8db4 : fetch_word AsanUbsan.M.loaded_segments (0xab778 : word) = Some W_a8db4.
Proof. vm_refl. Qed.
Lemma D_a8db4 : decode_any W_a8db4 = Some (OpImm ALU_ADD 14 13 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a8db8 : bv 32 := 0x00568623.
Lemma F_a8db8 : fetch_word AsanUbsan.M.loaded_segments (0xab77c : word) = Some W_a8db8.
Proof. vm_refl. Qed.
Lemma D_a8db8 : decode_any W_a8db8 = Some (Store SZ1 13 5 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a8dbc : bv 32 := 0x006686a3.
Lemma F_a8dbc : fetch_word AsanUbsan.M.loaded_segments (0xab780 : word) = Some W_a8dbc.
Proof. vm_refl. Qed.
Lemma D_a8dbc : decode_any W_a8dbc = Some (Store SZ1 13 6 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a8dc0 : bv 32 := 0x00768723.
Lemma F_a8dc0 : fetch_word AsanUbsan.M.loaded_segments (0xab784 : word) = Some W_a8dc0.
Proof. vm_refl. Qed.
Lemma D_a8dc0 : decode_any W_a8dc0 = Some (Store SZ1 13 7 14, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a8dc4 : bv 32 := 0x01c687a3.
Lemma F_a8dc4 : fetch_word AsanUbsan.M.loaded_segments (0xab788 : word) = Some W_a8dc4.
Proof. vm_refl. Qed.
Lemma D_a8dc4 : decode_any W_a8dc4 = Some (Store SZ1 13 28 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a8dc8 : bv 32 := 0x00070693.
Lemma F_a8dc8 : fetch_word AsanUbsan.M.loaded_segments (0xab78c : word) = Some W_a8dc8.
Proof. vm_refl. Qed.
Lemma D_a8dc8 : decode_any W_a8dc8 = Some (OpImm ALU_ADD 13 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a8dcc : bv 32 := 0x00867713.
Lemma F_a8dcc : fetch_word AsanUbsan.M.loaded_segments (0xab790 : word) = Some W_a8dcc.
Proof. vm_refl. Qed.
Lemma D_a8dcc : decode_any W_a8dcc = Some (OpImm ALU_AND 14 12 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a8dd0 : bv 32 := 0xd20706e3.
Lemma F_a8dd0 : fetch_word AsanUbsan.M.loaded_segments (0xab794 : word) = Some W_a8dd0.
Proof. vm_refl. Qed.
Lemma D_a8dd0 : decode_any W_a8dd0 = Some (Branch BC_EQ 14 0 7468, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a8dd4 : bv 32 := 0x0005c703.
Lemma F_a8dd4 : fetch_word AsanUbsan.M.loaded_segments (0xab798 : word) = Some W_a8dd4.
Proof. vm_refl. Qed.
Lemma D_a8dd4 : decode_any W_a8dd4 = Some (Load SZ1 false 14 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a8dd8 : bv 32 := 0x0015c783.
Lemma F_a8dd8 : fetch_word AsanUbsan.M.loaded_segments (0xab79c : word) = Some W_a8dd8.
Proof. vm_refl. Qed.
Lemma D_a8dd8 : decode_any W_a8dd8 = Some (Load SZ1 false 15 11 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a8ddc : bv 32 := 0x0025c803.
Lemma F_a8ddc : fetch_word AsanUbsan.M.loaded_segments (0xab7a0 : word) = Some W_a8ddc.
Proof. vm_refl. Qed.
Lemma D_a8ddc : decode_any W_a8ddc = Some (Load SZ1 false 16 11 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a8de0 : bv 32 := 0x0035c883.
Lemma F_a8de0 : fetch_word AsanUbsan.M.loaded_segments (0xab7a4 : word) = Some W_a8de0.
Proof. vm_refl. Qed.
Lemma D_a8de0 : decode_any W_a8de0 = Some (Load SZ1 false 17 11 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a8de4 : bv 32 := 0x0045c283.
Lemma F_a8de4 : fetch_word AsanUbsan.M.loaded_segments (0xab7a8 : word) = Some W_a8de4.
Proof. vm_refl. Qed.
Lemma D_a8de4 : decode_any W_a8de4 = Some (Load SZ1 false 5 11 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a8de8 : bv 32 := 0x0055c303.
Lemma F_a8de8 : fetch_word AsanUbsan.M.loaded_segments (0xab7ac : word) = Some W_a8de8.
Proof. vm_refl. Qed.
Lemma D_a8de8 : decode_any W_a8de8 = Some (Load SZ1 false 6 11 5, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a8dec : bv 32 := 0x0065c383.
Lemma F_a8dec : fetch_word AsanUbsan.M.loaded_segments (0xab7b0 : word) = Some W_a8dec.
Proof. vm_refl. Qed.
Lemma D_a8dec : decode_any W_a8dec = Some (Load SZ1 false 7 11 6, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a8df0 : bv 32 := 0x0075ce03.
Lemma F_a8df0 : fetch_word AsanUbsan.M.loaded_segments (0xab7b4 : word) = Some W_a8df0.
Proof. vm_refl. Qed.
Lemma D_a8df0 : decode_any W_a8df0 = Some (Load SZ1 false 28 11 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a8df4 : bv 32 := 0x00858593.
Lemma F_a8df4 : fetch_word AsanUbsan.M.loaded_segments (0xab7b8 : word) = Some W_a8df4.
Proof. vm_refl. Qed.
Lemma D_a8df4 : decode_any W_a8df4 = Some (OpImm ALU_ADD 11 11 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a8df8 : bv 32 := 0x00e68023.
Lemma F_a8df8 : fetch_word AsanUbsan.M.loaded_segments (0xab7bc : word) = Some W_a8df8.
Proof. vm_refl. Qed.
Lemma D_a8df8 : decode_any W_a8df8 = Some (Store SZ1 13 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a8dfc : bv 32 := 0x00f680a3.
Lemma F_a8dfc : fetch_word AsanUbsan.M.loaded_segments (0xab7c0 : word) = Some W_a8dfc.
Proof. vm_refl. Qed.
Lemma D_a8dfc : decode_any W_a8dfc = Some (Store SZ1 13 15 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a8e00 : bv 32 := 0x01068123.
Lemma F_a8e00 : fetch_word AsanUbsan.M.loaded_segments (0xab7c4 : word) = Some W_a8e00.
Proof. vm_refl. Qed.
Lemma D_a8e00 : decode_any W_a8e00 = Some (Store SZ1 13 16 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a8e04 : bv 32 := 0x011681a3.
Lemma F_a8e04 : fetch_word AsanUbsan.M.loaded_segments (0xab7c8 : word) = Some W_a8e04.
Proof. vm_refl. Qed.
Lemma D_a8e04 : decode_any W_a8e04 = Some (Store SZ1 13 17 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a8e08 : bv 32 := 0x00868713.
Lemma F_a8e08 : fetch_word AsanUbsan.M.loaded_segments (0xab7cc : word) = Some W_a8e08.
Proof. vm_refl. Qed.
Lemma D_a8e08 : decode_any W_a8e08 = Some (OpImm ALU_ADD 14 13 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a8e0c : bv 32 := 0x00568223.
Lemma F_a8e0c : fetch_word AsanUbsan.M.loaded_segments (0xab7d0 : word) = Some W_a8e0c.
Proof. vm_refl. Qed.
Lemma D_a8e0c : decode_any W_a8e0c = Some (Store SZ1 13 5 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a8e10 : bv 32 := 0x006682a3.
Lemma F_a8e10 : fetch_word AsanUbsan.M.loaded_segments (0xab7d4 : word) = Some W_a8e10.
Proof. vm_refl. Qed.
Lemma D_a8e10 : decode_any W_a8e10 = Some (Store SZ1 13 6 5, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a8e14 : bv 32 := 0x00768323.
Lemma F_a8e14 : fetch_word AsanUbsan.M.loaded_segments (0xab7d8 : word) = Some W_a8e14.
Proof. vm_refl. Qed.
Lemma D_a8e14 : decode_any W_a8e14 = Some (Store SZ1 13 7 6, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a8e18 : bv 32 := 0x01c683a3.
Lemma F_a8e18 : fetch_word AsanUbsan.M.loaded_segments (0xab7dc : word) = Some W_a8e18.
Proof. vm_refl. Qed.
Lemma D_a8e18 : decode_any W_a8e18 = Some (Store SZ1 13 28 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a8e1c : bv 32 := 0x00070693.
Lemma F_a8e1c : fetch_word AsanUbsan.M.loaded_segments (0xab7e0 : word) = Some W_a8e1c.
Proof. vm_refl. Qed.
Lemma D_a8e1c : decode_any W_a8e1c = Some (OpImm ALU_ADD 13 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a8e20 : bv 32 := 0x00467713.
Lemma F_a8e20 : fetch_word AsanUbsan.M.loaded_segments (0xab7e4 : word) = Some W_a8e20.
Proof. vm_refl. Qed.
Lemma D_a8e20 : decode_any W_a8e20 = Some (OpImm ALU_AND 14 12 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a8e24 : bv 32 := 0x02070863.
Lemma F_a8e24 : fetch_word AsanUbsan.M.loaded_segments (0xab7e8 : word) = Some W_a8e24.
Proof. vm_refl. Qed.
Lemma D_a8e24 : decode_any W_a8e24 = Some (Branch BC_EQ 14 0 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a8e28 : bv 32 := 0x0005c703.
Lemma F_a8e28 : fetch_word AsanUbsan.M.loaded_segments (0xab7ec : word) = Some W_a8e28.
Proof. vm_refl. Qed.
Lemma D_a8e28 : decode_any W_a8e28 = Some (Load SZ1 false 14 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a8e2c : bv 32 := 0x0015c783.
Lemma F_a8e2c : fetch_word AsanUbsan.M.loaded_segments (0xab7f0 : word) = Some W_a8e2c.
Proof. vm_refl. Qed.
Lemma D_a8e2c : decode_any W_a8e2c = Some (Load SZ1 false 15 11 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a8e30 : bv 32 := 0x0025c803.
Lemma F_a8e30 : fetch_word AsanUbsan.M.loaded_segments (0xab7f4 : word) = Some W_a8e30.
Proof. vm_refl. Qed.
Lemma D_a8e30 : decode_any W_a8e30 = Some (Load SZ1 false 16 11 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a8e34 : bv 32 := 0x0035c883.
Lemma F_a8e34 : fetch_word AsanUbsan.M.loaded_segments (0xab7f8 : word) = Some W_a8e34.
Proof. vm_refl. Qed.
Lemma D_a8e34 : decode_any W_a8e34 = Some (Load SZ1 false 17 11 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a8e38 : bv 32 := 0x00458593.
Lemma F_a8e38 : fetch_word AsanUbsan.M.loaded_segments (0xab7fc : word) = Some W_a8e38.
Proof. vm_refl. Qed.
Lemma D_a8e38 : decode_any W_a8e38 = Some (OpImm ALU_ADD 11 11 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a8e3c : bv 32 := 0x00468293.
Lemma F_a8e3c : fetch_word AsanUbsan.M.loaded_segments (0xab800 : word) = Some W_a8e3c.
Proof. vm_refl. Qed.
Lemma D_a8e3c : decode_any W_a8e3c = Some (OpImm ALU_ADD 5 13 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a8e40 : bv 32 := 0x00e68023.
Lemma F_a8e40 : fetch_word AsanUbsan.M.loaded_segments (0xab804 : word) = Some W_a8e40.
Proof. vm_refl. Qed.
Lemma D_a8e40 : decode_any W_a8e40 = Some (Store SZ1 13 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a8e44 : bv 32 := 0x00f680a3.
Lemma F_a8e44 : fetch_word AsanUbsan.M.loaded_segments (0xab808 : word) = Some W_a8e44.
Proof. vm_refl. Qed.
Lemma D_a8e44 : decode_any W_a8e44 = Some (Store SZ1 13 15 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a8e48 : bv 32 := 0x01068123.
Lemma F_a8e48 : fetch_word AsanUbsan.M.loaded_segments (0xab80c : word) = Some W_a8e48.
Proof. vm_refl. Qed.
Lemma D_a8e48 : decode_any W_a8e48 = Some (Store SZ1 13 16 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a8e4c : bv 32 := 0x011681a3.
Lemma F_a8e4c : fetch_word AsanUbsan.M.loaded_segments (0xab810 : word) = Some W_a8e4c.
Proof. vm_refl. Qed.
Lemma D_a8e4c : decode_any W_a8e4c = Some (Store SZ1 13 17 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a8e50 : bv 32 := 0x00028693.
Lemma F_a8e50 : fetch_word AsanUbsan.M.loaded_segments (0xab814 : word) = Some W_a8e50.
Proof. vm_refl. Qed.
Lemma D_a8e50 : decode_any W_a8e50 = Some (OpImm ALU_ADD 13 5 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a8e54 : bv 32 := 0x00267713.
Lemma F_a8e54 : fetch_word AsanUbsan.M.loaded_segments (0xab818 : word) = Some W_a8e54.
Proof. vm_refl. Qed.
Lemma D_a8e54 : decode_any W_a8e54 = Some (OpImm ALU_AND 14 12 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a8e58 : bv 32 := 0x00071863.
Lemma F_a8e58 : fetch_word AsanUbsan.M.loaded_segments (0xab81c : word) = Some W_a8e58.
Proof. vm_refl. Qed.
Lemma D_a8e58 : decode_any W_a8e58 = Some (Branch BC_NE 14 0 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a8e5c : bv 32 := 0x00167613.
Lemma F_a8e5c : fetch_word AsanUbsan.M.loaded_segments (0xab820 : word) = Some W_a8e5c.
Proof. vm_refl. Qed.
Lemma D_a8e5c : decode_any W_a8e5c = Some (OpImm ALU_AND 12 12 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a8e60 : bv 32 := 0x02061663.
Lemma F_a8e60 : fetch_word AsanUbsan.M.loaded_segments (0xab824 : word) = Some W_a8e60.
Proof. vm_refl. Qed.
Lemma D_a8e60 : decode_any W_a8e60 = Some (Branch BC_NE 12 0 44, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a8e64 : bv 32 := 0x00008067.
Lemma F_a8e64 : fetch_word AsanUbsan.M.loaded_segments (0xab828 : word) = Some W_a8e64.
Proof. vm_refl. Qed.
Lemma D_a8e64 : decode_any W_a8e64 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a8e68 : bv 32 := 0x0005c703.
Lemma F_a8e68 : fetch_word AsanUbsan.M.loaded_segments (0xab82c : word) = Some W_a8e68.
Proof. vm_refl. Qed.
Lemma D_a8e68 : decode_any W_a8e68 = Some (Load SZ1 false 14 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a8e6c : bv 32 := 0x0015c783.
Lemma F_a8e6c : fetch_word AsanUbsan.M.loaded_segments (0xab830 : word) = Some W_a8e6c.
Proof. vm_refl. Qed.
Lemma D_a8e6c : decode_any W_a8e6c = Some (Load SZ1 false 15 11 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a8e70 : bv 32 := 0x00258593.
Lemma F_a8e70 : fetch_word AsanUbsan.M.loaded_segments (0xab834 : word) = Some W_a8e70.
Proof. vm_refl. Qed.
Lemma D_a8e70 : decode_any W_a8e70 = Some (OpImm ALU_ADD 11 11 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a8e74 : bv 32 := 0x00268813.
Lemma F_a8e74 : fetch_word AsanUbsan.M.loaded_segments (0xab838 : word) = Some W_a8e74.
Proof. vm_refl. Qed.
Lemma D_a8e74 : decode_any W_a8e74 = Some (OpImm ALU_ADD 16 13 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a8e78 : bv 32 := 0x00e68023.
Lemma F_a8e78 : fetch_word AsanUbsan.M.loaded_segments (0xab83c : word) = Some W_a8e78.
Proof. vm_refl. Qed.
Lemma D_a8e78 : decode_any W_a8e78 = Some (Store SZ1 13 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a8e7c : bv 32 := 0x00f680a3.
Lemma F_a8e7c : fetch_word AsanUbsan.M.loaded_segments (0xab840 : word) = Some W_a8e7c.
Proof. vm_refl. Qed.
Lemma D_a8e7c : decode_any W_a8e7c = Some (Store SZ1 13 15 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a8e80 : bv 32 := 0x00080693.
Lemma F_a8e80 : fetch_word AsanUbsan.M.loaded_segments (0xab844 : word) = Some W_a8e80.
Proof. vm_refl. Qed.
Lemma D_a8e80 : decode_any W_a8e80 = Some (OpImm ALU_ADD 13 16 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a8e84 : bv 32 := 0x00167613.
Lemma F_a8e84 : fetch_word AsanUbsan.M.loaded_segments (0xab848 : word) = Some W_a8e84.
Proof. vm_refl. Qed.
Lemma D_a8e84 : decode_any W_a8e84 = Some (OpImm ALU_AND 12 12 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a8e88 : bv 32 := 0xfc060ee3.
Lemma F_a8e88 : fetch_word AsanUbsan.M.loaded_segments (0xab84c : word) = Some W_a8e88.
Proof. vm_refl. Qed.
Lemma D_a8e88 : decode_any W_a8e88 = Some (Branch BC_EQ 12 0 8156, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a8e8c : bv 32 := 0x0005c583.
Lemma F_a8e8c : fetch_word AsanUbsan.M.loaded_segments (0xab850 : word) = Some W_a8e8c.
Proof. vm_refl. Qed.
Lemma D_a8e8c : decode_any W_a8e8c = Some (Load SZ1 false 11 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a8e90 : bv 32 := 0x00b68023.
Lemma F_a8e90 : fetch_word AsanUbsan.M.loaded_segments (0xab854 : word) = Some W_a8e90.
Proof. vm_refl. Qed.
Lemma D_a8e90 : decode_any W_a8e90 = Some (Store SZ1 13 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a8e94 : bv 32 := 0x00008067.
Lemma F_a8e94 : fetch_word AsanUbsan.M.loaded_segments (0xab858 : word) = Some W_a8e94.
Proof. vm_refl. Qed.
Lemma D_a8e94 : decode_any W_a8e94 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.
