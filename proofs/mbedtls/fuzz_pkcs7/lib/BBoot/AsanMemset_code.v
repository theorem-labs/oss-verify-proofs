(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OssFuzzTheorems.mbedtls.fuzz_pkcs7.images Require Import AsanUbsan.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.ABoot Require Import PropExec.
Local Instance asanreflect_fx : PropExec.FPState := PropExec.fx0.   (* [comment removed for export] *)
Open Scope bv_scope.

(* [comment removed for export] *)
Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

(* [comment removed for export] *)
Definition W_e7a14 : bv 32 := 0x0e060a63.
Lemma F_e7a14 : fetch_word AsanUbsan.M.loaded_segments (0x0eadc4 : word) = Some W_e7a14.
Proof. vm_refl. Qed.
Lemma D_e7a14 : decode_any W_e7a14 = Some (Branch BC_EQ 12 0 244, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_e7a18 : bv 32 := 0x00b50023.
Lemma F_e7a18 : fetch_word AsanUbsan.M.loaded_segments (0x0eadc8 : word) = Some W_e7a18.
Proof. vm_refl. Qed.
Lemma D_e7a18 : decode_any W_e7a18 = Some (Store SZ1 10 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_e7a1c : bv 32 := 0x00c506b3.
Lemma F_e7a1c : fetch_word AsanUbsan.M.loaded_segments (0x0eadcc : word) = Some W_e7a1c.
Proof. vm_refl. Qed.
Lemma D_e7a1c : decode_any W_e7a1c = Some (Op ALU_ADD 13 10 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_e7a20 : bv 32 := 0x00300713.
Lemma F_e7a20 : fetch_word AsanUbsan.M.loaded_segments (0x0eadd0 : word) = Some W_e7a20.
Proof. vm_refl. Qed.
Lemma D_e7a20 : decode_any W_e7a20 = Some (OpImm ALU_ADD 14 0 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_e7a24 : bv 32 := 0xfeb68fa3.
Lemma F_e7a24 : fetch_word AsanUbsan.M.loaded_segments (0x0eadd4 : word) = Some W_e7a24.
Proof. vm_refl. Qed.
Lemma D_e7a24 : decode_any W_e7a24 = Some (Store SZ1 13 11 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_e7a28 : bv 32 := 0x0ee66063.
Lemma F_e7a28 : fetch_word AsanUbsan.M.loaded_segments (0x0eadd8 : word) = Some W_e7a28.
Proof. vm_refl. Qed.
Lemma D_e7a28 : decode_any W_e7a28 = Some (Branch BC_LTU 12 14 224, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_e7a2c : bv 32 := 0x00b500a3.
Lemma F_e7a2c : fetch_word AsanUbsan.M.loaded_segments (0x0eaddc : word) = Some W_e7a2c.
Proof. vm_refl. Qed.
Lemma D_e7a2c : decode_any W_e7a2c = Some (Store SZ1 10 11 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_e7a30 : bv 32 := 0x00b50123.
Lemma F_e7a30 : fetch_word AsanUbsan.M.loaded_segments (0x0eade0 : word) = Some W_e7a30.
Proof. vm_refl. Qed.
Lemma D_e7a30 : decode_any W_e7a30 = Some (Store SZ1 10 11 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_e7a34 : bv 32 := 0x00700713.
Lemma F_e7a34 : fetch_word AsanUbsan.M.loaded_segments (0x0eade4 : word) = Some W_e7a34.
Proof. vm_refl. Qed.
Lemma D_e7a34 : decode_any W_e7a34 = Some (OpImm ALU_ADD 14 0 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_e7a38 : bv 32 := 0xfeb68ea3.
Lemma F_e7a38 : fetch_word AsanUbsan.M.loaded_segments (0x0eade8 : word) = Some W_e7a38.
Proof. vm_refl. Qed.
Lemma D_e7a38 : decode_any W_e7a38 = Some (Store SZ1 13 11 4093, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_e7a3c : bv 32 := 0xfeb68f23.
Lemma F_e7a3c : fetch_word AsanUbsan.M.loaded_segments (0x0eadec : word) = Some W_e7a3c.
Proof. vm_refl. Qed.
Lemma D_e7a3c : decode_any W_e7a3c = Some (Store SZ1 13 11 4094, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_e7a40 : bv 32 := 0x0ce66463.
Lemma F_e7a40 : fetch_word AsanUbsan.M.loaded_segments (0x0eadf0 : word) = Some W_e7a40.
Proof. vm_refl. Qed.
Lemma D_e7a40 : decode_any W_e7a40 = Some (Branch BC_LTU 12 14 200, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_e7a44 : bv 32 := 0x00b501a3.
Lemma F_e7a44 : fetch_word AsanUbsan.M.loaded_segments (0x0eadf4 : word) = Some W_e7a44.
Proof. vm_refl. Qed.
Lemma D_e7a44 : decode_any W_e7a44 = Some (Store SZ1 10 11 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_e7a48 : bv 32 := 0x00900793.
Lemma F_e7a48 : fetch_word AsanUbsan.M.loaded_segments (0x0eadf8 : word) = Some W_e7a48.
Proof. vm_refl. Qed.
Lemma D_e7a48 : decode_any W_e7a48 = Some (OpImm ALU_ADD 15 0 9, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_e7a4c : bv 32 := 0xfeb68e23.
Lemma F_e7a4c : fetch_word AsanUbsan.M.loaded_segments (0x0eadfc : word) = Some W_e7a4c.
Proof. vm_refl. Qed.
Lemma D_e7a4c : decode_any W_e7a4c = Some (Store SZ1 13 11 4092, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_e7a50 : bv 32 := 0x0af66c63.
Lemma F_e7a50 : fetch_word AsanUbsan.M.loaded_segments (0x0eae00 : word) = Some W_e7a50.
Proof. vm_refl. Qed.
Lemma D_e7a50 : decode_any W_e7a50 = Some (Branch BC_LTU 12 15 184, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_e7a54 : bv 32 := 0x40a006bb.
Lemma F_e7a54 : fetch_word AsanUbsan.M.loaded_segments (0x0eae04 : word) = Some W_e7a54.
Proof. vm_refl. Qed.
Lemma D_e7a54 : decode_any W_e7a54 = Some (Op32 ALU_SUB 13 0 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_e7a58 : bv 32 := 0x03859813.
Lemma F_e7a58 : fetch_word AsanUbsan.M.loaded_segments (0x0eae08 : word) = Some W_e7a58.
Proof. vm_refl. Qed.
Lemma D_e7a58 : decode_any W_e7a58 = Some (ShiftImm ALU_SLL 16 11 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_e7a5c : bv 32 := 0x101015b7.
Lemma F_e7a5c : fetch_word AsanUbsan.M.loaded_segments (0x0eae0c : word) = Some W_e7a5c.
Proof. vm_refl. Qed.
Lemma D_e7a5c : decode_any W_e7a5c = Some (Lui 11 65793, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_e7a60 : bv 32 := 0x0036f693.
Lemma F_e7a60 : fetch_word AsanUbsan.M.loaded_segments (0x0eae10 : word) = Some W_e7a60.
Proof. vm_refl. Qed.
Lemma D_e7a60 : decode_any W_e7a60 = Some (OpImm ALU_AND 13 13 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_e7a64 : bv 32 := 0x00459713.
Lemma F_e7a64 : fetch_word AsanUbsan.M.loaded_segments (0x0eae14 : word) = Some W_e7a64.
Proof. vm_refl. Qed.
Lemma D_e7a64 : decode_any W_e7a64 = Some (ShiftImm ALU_SLL 14 11 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_e7a68 : bv 32 := 0x40d60633.
Lemma F_e7a68 : fetch_word AsanUbsan.M.loaded_segments (0x0eae18 : word) = Some W_e7a68.
Proof. vm_refl. Qed.
Lemma D_e7a68 : decode_any W_e7a68 = Some (Op ALU_SUB 12 12 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_e7a6c : bv 32 := 0x00d505b3.
Lemma F_e7a6c : fetch_word AsanUbsan.M.loaded_segments (0x0eae1c : word) = Some W_e7a6c.
Proof. vm_refl. Qed.
Lemma D_e7a6c : decode_any W_e7a6c = Some (Op ALU_ADD 11 10 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_e7a70 : bv 32 := 0x10070693.
Lemma F_e7a70 : fetch_word AsanUbsan.M.loaded_segments (0x0eae20 : word) = Some W_e7a70.
Proof. vm_refl. Qed.
Lemma D_e7a70 : decode_any W_e7a70 = Some (OpImm ALU_ADD 13 14 256, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_e7a74 : bv 32 := 0xffc67713.
Lemma F_e7a74 : fetch_word AsanUbsan.M.loaded_segments (0x0eae24 : word) = Some W_e7a74.
Proof. vm_refl. Qed.
Lemma D_e7a74 : decode_any W_e7a74 = Some (OpImm ALU_AND 14 12 4092, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_e7a78 : bv 32 := 0x02d83633.
Lemma F_e7a78 : fetch_word AsanUbsan.M.loaded_segments (0x0eae28 : word) = Some W_e7a78.
Proof. vm_refl. Qed.
Lemma D_e7a78 : decode_any W_e7a78 = Some (Mul M_MULHU 12 16 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_e7a7c : bv 32 := 0x00c5a023.
Lemma F_e7a7c : fetch_word AsanUbsan.M.loaded_segments (0x0eae2c : word) = Some W_e7a7c.
Proof. vm_refl. Qed.
Lemma D_e7a7c : decode_any W_e7a7c = Some (Store SZ4 11 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_e7a80 : bv 32 := 0x00e586b3.
Lemma F_e7a80 : fetch_word AsanUbsan.M.loaded_segments (0x0eae30 : word) = Some W_e7a80.
Proof. vm_refl. Qed.
Lemma D_e7a80 : decode_any W_e7a80 = Some (Op ALU_ADD 13 11 14, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_e7a84 : bv 32 := 0xfec6ae23.
Lemma F_e7a84 : fetch_word AsanUbsan.M.loaded_segments (0x0eae34 : word) = Some W_e7a84.
Proof. vm_refl. Qed.
Lemma D_e7a84 : decode_any W_e7a84 = Some (Store SZ4 13 12 4092, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_e7a88 : bv 32 := 0x08f76063.
Lemma F_e7a88 : fetch_word AsanUbsan.M.loaded_segments (0x0eae38 : word) = Some W_e7a88.
Proof. vm_refl. Qed.
Lemma D_e7a88 : decode_any W_e7a88 = Some (Branch BC_LTU 14 15 128, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_e7a8c : bv 32 := 0x00c5a223.
Lemma F_e7a8c : fetch_word AsanUbsan.M.loaded_segments (0x0eae3c : word) = Some W_e7a8c.
Proof. vm_refl. Qed.
Lemma D_e7a8c : decode_any W_e7a8c = Some (Store SZ4 11 12 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_e7a90 : bv 32 := 0x00c5a423.
Lemma F_e7a90 : fetch_word AsanUbsan.M.loaded_segments (0x0eae40 : word) = Some W_e7a90.
Proof. vm_refl. Qed.
Lemma D_e7a90 : decode_any W_e7a90 = Some (Store SZ4 11 12 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_e7a94 : bv 32 := 0x01900793.
Lemma F_e7a94 : fetch_word AsanUbsan.M.loaded_segments (0x0eae44 : word) = Some W_e7a94.
Proof. vm_refl. Qed.
Lemma D_e7a94 : decode_any W_e7a94 = Some (OpImm ALU_ADD 15 0 25, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_e7a98 : bv 32 := 0xfec6aa23.
Lemma F_e7a98 : fetch_word AsanUbsan.M.loaded_segments (0x0eae48 : word) = Some W_e7a98.
Proof. vm_refl. Qed.
Lemma D_e7a98 : decode_any W_e7a98 = Some (Store SZ4 13 12 4084, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_e7a9c : bv 32 := 0xfec6ac23.
Lemma F_e7a9c : fetch_word AsanUbsan.M.loaded_segments (0x0eae4c : word) = Some W_e7a9c.
Proof. vm_refl. Qed.
Lemma D_e7a9c : decode_any W_e7a9c = Some (Store SZ4 13 12 4088, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_e7aa0 : bv 32 := 0x06f76463.
Lemma F_e7aa0 : fetch_word AsanUbsan.M.loaded_segments (0x0eae50 : word) = Some W_e7aa0.
Proof. vm_refl. Qed.
Lemma D_e7aa0 : decode_any W_e7aa0 = Some (Branch BC_LTU 14 15 104, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_e7aa4 : bv 32 := 0x00c5a623.
Lemma F_e7aa4 : fetch_word AsanUbsan.M.loaded_segments (0x0eae54 : word) = Some W_e7aa4.
Proof. vm_refl. Qed.
Lemma D_e7aa4 : decode_any W_e7aa4 = Some (Store SZ4 11 12 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_e7aa8 : bv 32 := 0x00c5a823.
Lemma F_e7aa8 : fetch_word AsanUbsan.M.loaded_segments (0x0eae58 : word) = Some W_e7aa8.
Proof. vm_refl. Qed.
Lemma D_e7aa8 : decode_any W_e7aa8 = Some (Store SZ4 11 12 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_e7aac : bv 32 := 0x00c5aa23.
Lemma F_e7aac : fetch_word AsanUbsan.M.loaded_segments (0x0eae5c : word) = Some W_e7aac.
Proof. vm_refl. Qed.
Lemma D_e7aac : decode_any W_e7aac = Some (Store SZ4 11 12 20, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_e7ab0 : bv 32 := 0x00c5ac23.
Lemma F_e7ab0 : fetch_word AsanUbsan.M.loaded_segments (0x0eae60 : word) = Some W_e7ab0.
Proof. vm_refl. Qed.
Lemma D_e7ab0 : decode_any W_e7ab0 = Some (Store SZ4 11 12 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_e7ab4 : bv 32 := 0x0045f793.
Lemma F_e7ab4 : fetch_word AsanUbsan.M.loaded_segments (0x0eae64 : word) = Some W_e7ab4.
Proof. vm_refl. Qed.
Lemma D_e7ab4 : decode_any W_e7ab4 = Some (OpImm ALU_AND 15 11 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_e7ab8 : bv 32 := 0x02000813.
Lemma F_e7ab8 : fetch_word AsanUbsan.M.loaded_segments (0x0eae68 : word) = Some W_e7ab8.
Proof. vm_refl. Qed.
Lemma D_e7ab8 : decode_any W_e7ab8 = Some (OpImm ALU_ADD 16 0 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_e7abc : bv 32 := 0x01878793.
Lemma F_e7abc : fetch_word AsanUbsan.M.loaded_segments (0x0eae6c : word) = Some W_e7abc.
Proof. vm_refl. Qed.
Lemma D_e7abc : decode_any W_e7abc = Some (OpImm ALU_ADD 15 15 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_e7ac0 : bv 32 := 0x40f70733.
Lemma F_e7ac0 : fetch_word AsanUbsan.M.loaded_segments (0x0eae70 : word) = Some W_e7ac0.
Proof. vm_refl. Qed.
Lemma D_e7ac0 : decode_any W_e7ac0 = Some (Op ALU_SUB 14 14 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_e7ac4 : bv 32 := 0xfec6a223.
Lemma F_e7ac4 : fetch_word AsanUbsan.M.loaded_segments (0x0eae74 : word) = Some W_e7ac4.
Proof. vm_refl. Qed.
Lemma D_e7ac4 : decode_any W_e7ac4 = Some (Store SZ4 13 12 4068, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_e7ac8 : bv 32 := 0xfec6a423.
Lemma F_e7ac8 : fetch_word AsanUbsan.M.loaded_segments (0x0eae78 : word) = Some W_e7ac8.
Proof. vm_refl. Qed.
Lemma D_e7ac8 : decode_any W_e7ac8 = Some (Store SZ4 13 12 4072, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_e7acc : bv 32 := 0xfec6a623.
Lemma F_e7acc : fetch_word AsanUbsan.M.loaded_segments (0x0eae7c : word) = Some W_e7acc.
Proof. vm_refl. Qed.
Lemma D_e7acc : decode_any W_e7acc = Some (Store SZ4 13 12 4076, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_e7ad0 : bv 32 := 0xfec6a823.
Lemma F_e7ad0 : fetch_word AsanUbsan.M.loaded_segments (0x0eae80 : word) = Some W_e7ad0.
Proof. vm_refl. Qed.
Lemma D_e7ad0 : decode_any W_e7ad0 = Some (Store SZ4 13 12 4080, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_e7ad4 : bv 32 := 0x03076a63.
Lemma F_e7ad4 : fetch_word AsanUbsan.M.loaded_segments (0x0eae84 : word) = Some W_e7ad4.
Proof. vm_refl. Qed.
Lemma D_e7ad4 : decode_any W_e7ad4 = Some (Branch BC_LTU 14 16 52, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_e7ad8 : bv 32 := 0x02061613.
Lemma F_e7ad8 : fetch_word AsanUbsan.M.loaded_segments (0x0eae88 : word) = Some W_e7ad8.
Proof. vm_refl. Qed.
Lemma D_e7ad8 : decode_any W_e7ad8 = Some (ShiftImm ALU_SLL 12 12 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_e7adc : bv 32 := 0x00f585b3.
Lemma F_e7adc : fetch_word AsanUbsan.M.loaded_segments (0x0eae8c : word) = Some W_e7adc.
Proof. vm_refl. Qed.
Lemma D_e7adc : decode_any W_e7adc = Some (Op ALU_ADD 11 11 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_e7ae0 : bv 32 := 0x02065693.
Lemma F_e7ae0 : fetch_word AsanUbsan.M.loaded_segments (0x0eae90 : word) = Some W_e7ae0.
Proof. vm_refl. Qed.
Lemma D_e7ae0 : decode_any W_e7ae0 = Some (ShiftImm ALU_SRL 13 12 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_e7ae4 : bv 32 := 0x00d66633.
Lemma F_e7ae4 : fetch_word AsanUbsan.M.loaded_segments (0x0eae94 : word) = Some W_e7ae4.
Proof. vm_refl. Qed.
Lemma D_e7ae4 : decode_any W_e7ae4 = Some (Op ALU_OR 12 12 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_e7ae8 : bv 32 := 0x01f00693.
Lemma F_e7ae8 : fetch_word AsanUbsan.M.loaded_segments (0x0eae98 : word) = Some W_e7ae8.
Proof. vm_refl. Qed.
Lemma D_e7ae8 : decode_any W_e7ae8 = Some (OpImm ALU_ADD 13 0 31, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_e7aec : bv 32 := 0x00c5b023.
Lemma F_e7aec : fetch_word AsanUbsan.M.loaded_segments (0x0eae9c : word) = Some W_e7aec.
Proof. vm_refl. Qed.
Lemma D_e7aec : decode_any W_e7aec = Some (Store SZ8 11 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_e7af0 : bv 32 := 0x00c5b423.
Lemma F_e7af0 : fetch_word AsanUbsan.M.loaded_segments (0x0eaea0 : word) = Some W_e7af0.
Proof. vm_refl. Qed.
Lemma D_e7af0 : decode_any W_e7af0 = Some (Store SZ8 11 12 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_e7af4 : bv 32 := 0x00c5b823.
Lemma F_e7af4 : fetch_word AsanUbsan.M.loaded_segments (0x0eaea4 : word) = Some W_e7af4.
Proof. vm_refl. Qed.
Lemma D_e7af4 : decode_any W_e7af4 = Some (Store SZ8 11 12 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_e7af8 : bv 32 := 0x00c5bc23.
Lemma F_e7af8 : fetch_word AsanUbsan.M.loaded_segments (0x0eaea8 : word) = Some W_e7af8.
Proof. vm_refl. Qed.
Lemma D_e7af8 : decode_any W_e7af8 = Some (Store SZ8 11 12 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_e7afc : bv 32 := 0xfe070713.
Lemma F_e7afc : fetch_word AsanUbsan.M.loaded_segments (0x0eaeac : word) = Some W_e7afc.
Proof. vm_refl. Qed.
Lemma D_e7afc : decode_any W_e7afc = Some (OpImm ALU_ADD 14 14 4064, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_e7b00 : bv 32 := 0x02058593.
Lemma F_e7b00 : fetch_word AsanUbsan.M.loaded_segments (0x0eaeb0 : word) = Some W_e7b00.
Proof. vm_refl. Qed.
Lemma D_e7b00 : decode_any W_e7b00 = Some (OpImm ALU_ADD 11 11 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_e7b04 : bv 32 := 0xfee6e4e3.
Lemma F_e7b04 : fetch_word AsanUbsan.M.loaded_segments (0x0eaeb4 : word) = Some W_e7b04.
Proof. vm_refl. Qed.
Lemma D_e7b04 : decode_any W_e7b04 = Some (Branch BC_LTU 13 14 8168, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_e7b08 : bv 32 := 0x00008067.
Lemma F_e7b08 : fetch_word AsanUbsan.M.loaded_segments (0x0eaeb8 : word) = Some W_e7b08.
Proof. vm_refl. Qed.
Lemma D_e7b08 : decode_any W_e7b08 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Abbreviation MSEGS := AsanUbsan.M.loaded_segments.
Definition ms_base : Z := 0x0eadc4%Z.
Definition Fo_000 := F_e7a14.
Definition Do_000 := D_e7a14.
Definition Fo_004 := F_e7a18.
Definition Do_004 := D_e7a18.
Definition Fo_008 := F_e7a1c.
Definition Do_008 := D_e7a1c.
Definition Fo_00c := F_e7a20.
Definition Do_00c := D_e7a20.
Definition Fo_010 := F_e7a24.
Definition Do_010 := D_e7a24.
Definition Fo_014 := F_e7a28.
Definition Do_014 := D_e7a28.
Definition Fo_018 := F_e7a2c.
Definition Do_018 := D_e7a2c.
Definition Fo_01c := F_e7a30.
Definition Do_01c := D_e7a30.
Definition Fo_020 := F_e7a34.
Definition Do_020 := D_e7a34.
Definition Fo_024 := F_e7a38.
Definition Do_024 := D_e7a38.
Definition Fo_028 := F_e7a3c.
Definition Do_028 := D_e7a3c.
Definition Fo_02c := F_e7a40.
Definition Do_02c := D_e7a40.
Definition Fo_030 := F_e7a44.
Definition Do_030 := D_e7a44.
Definition Fo_034 := F_e7a48.
Definition Do_034 := D_e7a48.
Definition Fo_038 := F_e7a4c.
Definition Do_038 := D_e7a4c.
Definition Fo_03c := F_e7a50.
Definition Do_03c := D_e7a50.
Definition Fo_040 := F_e7a54.
Definition Do_040 := D_e7a54.
Definition Fo_044 := F_e7a58.
Definition Do_044 := D_e7a58.
Definition Fo_048 := F_e7a5c.
Definition Do_048 := D_e7a5c.
Definition Fo_04c := F_e7a60.
Definition Do_04c := D_e7a60.
Definition Fo_050 := F_e7a64.
Definition Do_050 := D_e7a64.
Definition Fo_054 := F_e7a68.
Definition Do_054 := D_e7a68.
Definition Fo_058 := F_e7a6c.
Definition Do_058 := D_e7a6c.
Definition Fo_05c := F_e7a70.
Definition Do_05c := D_e7a70.
Definition Fo_060 := F_e7a74.
Definition Do_060 := D_e7a74.
Definition Fo_064 := F_e7a78.
Definition Do_064 := D_e7a78.
Definition Fo_068 := F_e7a7c.
Definition Do_068 := D_e7a7c.
Definition Fo_06c := F_e7a80.
Definition Do_06c := D_e7a80.
Definition Fo_070 := F_e7a84.
Definition Do_070 := D_e7a84.
Definition Fo_074 := F_e7a88.
Definition Do_074 := D_e7a88.
Definition Fo_078 := F_e7a8c.
Definition Do_078 := D_e7a8c.
Definition Fo_07c := F_e7a90.
Definition Do_07c := D_e7a90.
Definition Fo_080 := F_e7a94.
Definition Do_080 := D_e7a94.
Definition Fo_084 := F_e7a98.
Definition Do_084 := D_e7a98.
Definition Fo_088 := F_e7a9c.
Definition Do_088 := D_e7a9c.
Definition Fo_08c := F_e7aa0.
Definition Do_08c := D_e7aa0.
Definition Fo_090 := F_e7aa4.
Definition Do_090 := D_e7aa4.
Definition Fo_094 := F_e7aa8.
Definition Do_094 := D_e7aa8.
Definition Fo_098 := F_e7aac.
Definition Do_098 := D_e7aac.
Definition Fo_09c := F_e7ab0.
Definition Do_09c := D_e7ab0.
Definition Fo_0a0 := F_e7ab4.
Definition Do_0a0 := D_e7ab4.
Definition Fo_0a4 := F_e7ab8.
Definition Do_0a4 := D_e7ab8.
Definition Fo_0a8 := F_e7abc.
Definition Do_0a8 := D_e7abc.
Definition Fo_0ac := F_e7ac0.
Definition Do_0ac := D_e7ac0.
Definition Fo_0b0 := F_e7ac4.
Definition Do_0b0 := D_e7ac4.
Definition Fo_0b4 := F_e7ac8.
Definition Do_0b4 := D_e7ac8.
Definition Fo_0b8 := F_e7acc.
Definition Do_0b8 := D_e7acc.
Definition Fo_0bc := F_e7ad0.
Definition Do_0bc := D_e7ad0.
Definition Fo_0c0 := F_e7ad4.
Definition Do_0c0 := D_e7ad4.
Definition Fo_0c4 := F_e7ad8.
Definition Do_0c4 := D_e7ad8.
Definition Fo_0c8 := F_e7adc.
Definition Do_0c8 := D_e7adc.
Definition Fo_0cc := F_e7ae0.
Definition Do_0cc := D_e7ae0.
Definition Fo_0d0 := F_e7ae4.
Definition Do_0d0 := D_e7ae4.
Definition Fo_0d4 := F_e7ae8.
Definition Do_0d4 := D_e7ae8.
Definition Fo_0d8 := F_e7aec.
Definition Do_0d8 := D_e7aec.
Definition Fo_0dc := F_e7af0.
Definition Do_0dc := D_e7af0.
Definition Fo_0e0 := F_e7af4.
Definition Do_0e0 := D_e7af4.
Definition Fo_0e4 := F_e7af8.
Definition Do_0e4 := D_e7af8.
Definition Fo_0e8 := F_e7afc.
Definition Do_0e8 := D_e7afc.
Definition Fo_0ec := F_e7b00.
Definition Do_0ec := D_e7b00.
Definition Fo_0f0 := F_e7b04.
Definition Do_0f0 := D_e7b04.
Definition Fo_0f4 := F_e7b08.
Definition Do_0f4 := D_e7b08.
