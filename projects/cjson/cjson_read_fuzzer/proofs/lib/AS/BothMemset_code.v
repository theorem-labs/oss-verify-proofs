(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
(* [comment removed for export] *)
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
From OSSVerify.cjson.cjson_read_fuzzer.images Require Import AsanUbsan.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Open Scope bv_scope.

(* [comment removed for export] *)
Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

(* [comment removed for export] *)
Definition W_9ad74 : bv 32 := 0x0e060a63.
Lemma F_9ad74 : fetch_word AsanUbsan.M.loaded_segments (0x9ad74 : word) = Some W_9ad74.
Proof. vm_refl. Qed.
Lemma D_9ad74 : decode_any W_9ad74 = Some (Branch BC_EQ 12 0 244, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9ad78 : bv 32 := 0x00b50023.
Lemma F_9ad78 : fetch_word AsanUbsan.M.loaded_segments (0x9ad78 : word) = Some W_9ad78.
Proof. vm_refl. Qed.
Lemma D_9ad78 : decode_any W_9ad78 = Some (Store SZ1 10 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9ad7c : bv 32 := 0x00c506b3.
Lemma F_9ad7c : fetch_word AsanUbsan.M.loaded_segments (0x9ad7c : word) = Some W_9ad7c.
Proof. vm_refl. Qed.
Lemma D_9ad7c : decode_any W_9ad7c = Some (Op ALU_ADD 13 10 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9ad80 : bv 32 := 0x00300713.
Lemma F_9ad80 : fetch_word AsanUbsan.M.loaded_segments (0x9ad80 : word) = Some W_9ad80.
Proof. vm_refl. Qed.
Lemma D_9ad80 : decode_any W_9ad80 = Some (OpImm ALU_ADD 14 0 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9ad84 : bv 32 := 0xfeb68fa3.
Lemma F_9ad84 : fetch_word AsanUbsan.M.loaded_segments (0x9ad84 : word) = Some W_9ad84.
Proof. vm_refl. Qed.
Lemma D_9ad84 : decode_any W_9ad84 = Some (Store SZ1 13 11 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9ad88 : bv 32 := 0x0ee66063.
Lemma F_9ad88 : fetch_word AsanUbsan.M.loaded_segments (0x9ad88 : word) = Some W_9ad88.
Proof. vm_refl. Qed.
Lemma D_9ad88 : decode_any W_9ad88 = Some (Branch BC_LTU 12 14 224, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9ad8c : bv 32 := 0x00b500a3.
Lemma F_9ad8c : fetch_word AsanUbsan.M.loaded_segments (0x9ad8c : word) = Some W_9ad8c.
Proof. vm_refl. Qed.
Lemma D_9ad8c : decode_any W_9ad8c = Some (Store SZ1 10 11 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9ad90 : bv 32 := 0x00b50123.
Lemma F_9ad90 : fetch_word AsanUbsan.M.loaded_segments (0x9ad90 : word) = Some W_9ad90.
Proof. vm_refl. Qed.
Lemma D_9ad90 : decode_any W_9ad90 = Some (Store SZ1 10 11 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9ad94 : bv 32 := 0x00700713.
Lemma F_9ad94 : fetch_word AsanUbsan.M.loaded_segments (0x9ad94 : word) = Some W_9ad94.
Proof. vm_refl. Qed.
Lemma D_9ad94 : decode_any W_9ad94 = Some (OpImm ALU_ADD 14 0 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9ad98 : bv 32 := 0xfeb68ea3.
Lemma F_9ad98 : fetch_word AsanUbsan.M.loaded_segments (0x9ad98 : word) = Some W_9ad98.
Proof. vm_refl. Qed.
Lemma D_9ad98 : decode_any W_9ad98 = Some (Store SZ1 13 11 4093, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9ad9c : bv 32 := 0xfeb68f23.
Lemma F_9ad9c : fetch_word AsanUbsan.M.loaded_segments (0x9ad9c : word) = Some W_9ad9c.
Proof. vm_refl. Qed.
Lemma D_9ad9c : decode_any W_9ad9c = Some (Store SZ1 13 11 4094, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9ada0 : bv 32 := 0x0ce66463.
Lemma F_9ada0 : fetch_word AsanUbsan.M.loaded_segments (0x9ada0 : word) = Some W_9ada0.
Proof. vm_refl. Qed.
Lemma D_9ada0 : decode_any W_9ada0 = Some (Branch BC_LTU 12 14 200, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9ada4 : bv 32 := 0x00b501a3.
Lemma F_9ada4 : fetch_word AsanUbsan.M.loaded_segments (0x9ada4 : word) = Some W_9ada4.
Proof. vm_refl. Qed.
Lemma D_9ada4 : decode_any W_9ada4 = Some (Store SZ1 10 11 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9ada8 : bv 32 := 0x00900793.
Lemma F_9ada8 : fetch_word AsanUbsan.M.loaded_segments (0x9ada8 : word) = Some W_9ada8.
Proof. vm_refl. Qed.
Lemma D_9ada8 : decode_any W_9ada8 = Some (OpImm ALU_ADD 15 0 9, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9adac : bv 32 := 0xfeb68e23.
Lemma F_9adac : fetch_word AsanUbsan.M.loaded_segments (0x9adac : word) = Some W_9adac.
Proof. vm_refl. Qed.
Lemma D_9adac : decode_any W_9adac = Some (Store SZ1 13 11 4092, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9adb0 : bv 32 := 0x0af66c63.
Lemma F_9adb0 : fetch_word AsanUbsan.M.loaded_segments (0x9adb0 : word) = Some W_9adb0.
Proof. vm_refl. Qed.
Lemma D_9adb0 : decode_any W_9adb0 = Some (Branch BC_LTU 12 15 184, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9adb4 : bv 32 := 0x40a006bb.
Lemma F_9adb4 : fetch_word AsanUbsan.M.loaded_segments (0x9adb4 : word) = Some W_9adb4.
Proof. vm_refl. Qed.
Lemma D_9adb4 : decode_any W_9adb4 = Some (Op32 ALU_SUB 13 0 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9adb8 : bv 32 := 0x03859813.
Lemma F_9adb8 : fetch_word AsanUbsan.M.loaded_segments (0x9adb8 : word) = Some W_9adb8.
Proof. vm_refl. Qed.
Lemma D_9adb8 : decode_any W_9adb8 = Some (ShiftImm ALU_SLL 16 11 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9adbc : bv 32 := 0x101015b7.
Lemma F_9adbc : fetch_word AsanUbsan.M.loaded_segments (0x9adbc : word) = Some W_9adbc.
Proof. vm_refl. Qed.
Lemma D_9adbc : decode_any W_9adbc = Some (Lui 11 65793, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9adc0 : bv 32 := 0x0036f693.
Lemma F_9adc0 : fetch_word AsanUbsan.M.loaded_segments (0x9adc0 : word) = Some W_9adc0.
Proof. vm_refl. Qed.
Lemma D_9adc0 : decode_any W_9adc0 = Some (OpImm ALU_AND 13 13 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9adc4 : bv 32 := 0x00459713.
Lemma F_9adc4 : fetch_word AsanUbsan.M.loaded_segments (0x9adc4 : word) = Some W_9adc4.
Proof. vm_refl. Qed.
Lemma D_9adc4 : decode_any W_9adc4 = Some (ShiftImm ALU_SLL 14 11 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9adc8 : bv 32 := 0x40d60633.
Lemma F_9adc8 : fetch_word AsanUbsan.M.loaded_segments (0x9adc8 : word) = Some W_9adc8.
Proof. vm_refl. Qed.
Lemma D_9adc8 : decode_any W_9adc8 = Some (Op ALU_SUB 12 12 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9adcc : bv 32 := 0x00d505b3.
Lemma F_9adcc : fetch_word AsanUbsan.M.loaded_segments (0x9adcc : word) = Some W_9adcc.
Proof. vm_refl. Qed.
Lemma D_9adcc : decode_any W_9adcc = Some (Op ALU_ADD 11 10 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9add0 : bv 32 := 0x10070693.
Lemma F_9add0 : fetch_word AsanUbsan.M.loaded_segments (0x9add0 : word) = Some W_9add0.
Proof. vm_refl. Qed.
Lemma D_9add0 : decode_any W_9add0 = Some (OpImm ALU_ADD 13 14 256, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9add4 : bv 32 := 0xffc67713.
Lemma F_9add4 : fetch_word AsanUbsan.M.loaded_segments (0x9add4 : word) = Some W_9add4.
Proof. vm_refl. Qed.
Lemma D_9add4 : decode_any W_9add4 = Some (OpImm ALU_AND 14 12 4092, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9add8 : bv 32 := 0x02d83633.
Lemma F_9add8 : fetch_word AsanUbsan.M.loaded_segments (0x9add8 : word) = Some W_9add8.
Proof. vm_refl. Qed.
Lemma D_9add8 : decode_any W_9add8 = Some (Mul M_MULHU 12 16 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9addc : bv 32 := 0x00c5a023.
Lemma F_9addc : fetch_word AsanUbsan.M.loaded_segments (0x9addc : word) = Some W_9addc.
Proof. vm_refl. Qed.
Lemma D_9addc : decode_any W_9addc = Some (Store SZ4 11 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9ade0 : bv 32 := 0x00e586b3.
Lemma F_9ade0 : fetch_word AsanUbsan.M.loaded_segments (0x9ade0 : word) = Some W_9ade0.
Proof. vm_refl. Qed.
Lemma D_9ade0 : decode_any W_9ade0 = Some (Op ALU_ADD 13 11 14, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9ade4 : bv 32 := 0xfec6ae23.
Lemma F_9ade4 : fetch_word AsanUbsan.M.loaded_segments (0x9ade4 : word) = Some W_9ade4.
Proof. vm_refl. Qed.
Lemma D_9ade4 : decode_any W_9ade4 = Some (Store SZ4 13 12 4092, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9ade8 : bv 32 := 0x08f76063.
Lemma F_9ade8 : fetch_word AsanUbsan.M.loaded_segments (0x9ade8 : word) = Some W_9ade8.
Proof. vm_refl. Qed.
Lemma D_9ade8 : decode_any W_9ade8 = Some (Branch BC_LTU 14 15 128, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9adec : bv 32 := 0x00c5a223.
Lemma F_9adec : fetch_word AsanUbsan.M.loaded_segments (0x9adec : word) = Some W_9adec.
Proof. vm_refl. Qed.
Lemma D_9adec : decode_any W_9adec = Some (Store SZ4 11 12 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9adf0 : bv 32 := 0x00c5a423.
Lemma F_9adf0 : fetch_word AsanUbsan.M.loaded_segments (0x9adf0 : word) = Some W_9adf0.
Proof. vm_refl. Qed.
Lemma D_9adf0 : decode_any W_9adf0 = Some (Store SZ4 11 12 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9adf4 : bv 32 := 0x01900793.
Lemma F_9adf4 : fetch_word AsanUbsan.M.loaded_segments (0x9adf4 : word) = Some W_9adf4.
Proof. vm_refl. Qed.
Lemma D_9adf4 : decode_any W_9adf4 = Some (OpImm ALU_ADD 15 0 25, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9adf8 : bv 32 := 0xfec6aa23.
Lemma F_9adf8 : fetch_word AsanUbsan.M.loaded_segments (0x9adf8 : word) = Some W_9adf8.
Proof. vm_refl. Qed.
Lemma D_9adf8 : decode_any W_9adf8 = Some (Store SZ4 13 12 4084, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9adfc : bv 32 := 0xfec6ac23.
Lemma F_9adfc : fetch_word AsanUbsan.M.loaded_segments (0x9adfc : word) = Some W_9adfc.
Proof. vm_refl. Qed.
Lemma D_9adfc : decode_any W_9adfc = Some (Store SZ4 13 12 4088, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9ae00 : bv 32 := 0x06f76463.
Lemma F_9ae00 : fetch_word AsanUbsan.M.loaded_segments (0x9ae00 : word) = Some W_9ae00.
Proof. vm_refl. Qed.
Lemma D_9ae00 : decode_any W_9ae00 = Some (Branch BC_LTU 14 15 104, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9ae04 : bv 32 := 0x00c5a623.
Lemma F_9ae04 : fetch_word AsanUbsan.M.loaded_segments (0x9ae04 : word) = Some W_9ae04.
Proof. vm_refl. Qed.
Lemma D_9ae04 : decode_any W_9ae04 = Some (Store SZ4 11 12 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9ae08 : bv 32 := 0x00c5a823.
Lemma F_9ae08 : fetch_word AsanUbsan.M.loaded_segments (0x9ae08 : word) = Some W_9ae08.
Proof. vm_refl. Qed.
Lemma D_9ae08 : decode_any W_9ae08 = Some (Store SZ4 11 12 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9ae0c : bv 32 := 0x00c5aa23.
Lemma F_9ae0c : fetch_word AsanUbsan.M.loaded_segments (0x9ae0c : word) = Some W_9ae0c.
Proof. vm_refl. Qed.
Lemma D_9ae0c : decode_any W_9ae0c = Some (Store SZ4 11 12 20, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9ae10 : bv 32 := 0x00c5ac23.
Lemma F_9ae10 : fetch_word AsanUbsan.M.loaded_segments (0x9ae10 : word) = Some W_9ae10.
Proof. vm_refl. Qed.
Lemma D_9ae10 : decode_any W_9ae10 = Some (Store SZ4 11 12 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9ae14 : bv 32 := 0x0045f793.
Lemma F_9ae14 : fetch_word AsanUbsan.M.loaded_segments (0x9ae14 : word) = Some W_9ae14.
Proof. vm_refl. Qed.
Lemma D_9ae14 : decode_any W_9ae14 = Some (OpImm ALU_AND 15 11 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9ae18 : bv 32 := 0x02000813.
Lemma F_9ae18 : fetch_word AsanUbsan.M.loaded_segments (0x9ae18 : word) = Some W_9ae18.
Proof. vm_refl. Qed.
Lemma D_9ae18 : decode_any W_9ae18 = Some (OpImm ALU_ADD 16 0 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9ae1c : bv 32 := 0x01878793.
Lemma F_9ae1c : fetch_word AsanUbsan.M.loaded_segments (0x9ae1c : word) = Some W_9ae1c.
Proof. vm_refl. Qed.
Lemma D_9ae1c : decode_any W_9ae1c = Some (OpImm ALU_ADD 15 15 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9ae20 : bv 32 := 0x40f70733.
Lemma F_9ae20 : fetch_word AsanUbsan.M.loaded_segments (0x9ae20 : word) = Some W_9ae20.
Proof. vm_refl. Qed.
Lemma D_9ae20 : decode_any W_9ae20 = Some (Op ALU_SUB 14 14 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9ae24 : bv 32 := 0xfec6a223.
Lemma F_9ae24 : fetch_word AsanUbsan.M.loaded_segments (0x9ae24 : word) = Some W_9ae24.
Proof. vm_refl. Qed.
Lemma D_9ae24 : decode_any W_9ae24 = Some (Store SZ4 13 12 4068, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9ae28 : bv 32 := 0xfec6a423.
Lemma F_9ae28 : fetch_word AsanUbsan.M.loaded_segments (0x9ae28 : word) = Some W_9ae28.
Proof. vm_refl. Qed.
Lemma D_9ae28 : decode_any W_9ae28 = Some (Store SZ4 13 12 4072, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9ae2c : bv 32 := 0xfec6a623.
Lemma F_9ae2c : fetch_word AsanUbsan.M.loaded_segments (0x9ae2c : word) = Some W_9ae2c.
Proof. vm_refl. Qed.
Lemma D_9ae2c : decode_any W_9ae2c = Some (Store SZ4 13 12 4076, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9ae30 : bv 32 := 0xfec6a823.
Lemma F_9ae30 : fetch_word AsanUbsan.M.loaded_segments (0x9ae30 : word) = Some W_9ae30.
Proof. vm_refl. Qed.
Lemma D_9ae30 : decode_any W_9ae30 = Some (Store SZ4 13 12 4080, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9ae34 : bv 32 := 0x03076a63.
Lemma F_9ae34 : fetch_word AsanUbsan.M.loaded_segments (0x9ae34 : word) = Some W_9ae34.
Proof. vm_refl. Qed.
Lemma D_9ae34 : decode_any W_9ae34 = Some (Branch BC_LTU 14 16 52, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9ae38 : bv 32 := 0x02061613.
Lemma F_9ae38 : fetch_word AsanUbsan.M.loaded_segments (0x9ae38 : word) = Some W_9ae38.
Proof. vm_refl. Qed.
Lemma D_9ae38 : decode_any W_9ae38 = Some (ShiftImm ALU_SLL 12 12 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9ae3c : bv 32 := 0x00f585b3.
Lemma F_9ae3c : fetch_word AsanUbsan.M.loaded_segments (0x9ae3c : word) = Some W_9ae3c.
Proof. vm_refl. Qed.
Lemma D_9ae3c : decode_any W_9ae3c = Some (Op ALU_ADD 11 11 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9ae40 : bv 32 := 0x02065693.
Lemma F_9ae40 : fetch_word AsanUbsan.M.loaded_segments (0x9ae40 : word) = Some W_9ae40.
Proof. vm_refl. Qed.
Lemma D_9ae40 : decode_any W_9ae40 = Some (ShiftImm ALU_SRL 13 12 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9ae44 : bv 32 := 0x00d66633.
Lemma F_9ae44 : fetch_word AsanUbsan.M.loaded_segments (0x9ae44 : word) = Some W_9ae44.
Proof. vm_refl. Qed.
Lemma D_9ae44 : decode_any W_9ae44 = Some (Op ALU_OR 12 12 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9ae48 : bv 32 := 0x01f00693.
Lemma F_9ae48 : fetch_word AsanUbsan.M.loaded_segments (0x9ae48 : word) = Some W_9ae48.
Proof. vm_refl. Qed.
Lemma D_9ae48 : decode_any W_9ae48 = Some (OpImm ALU_ADD 13 0 31, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9ae4c : bv 32 := 0x00c5b023.
Lemma F_9ae4c : fetch_word AsanUbsan.M.loaded_segments (0x9ae4c : word) = Some W_9ae4c.
Proof. vm_refl. Qed.
Lemma D_9ae4c : decode_any W_9ae4c = Some (Store SZ8 11 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9ae50 : bv 32 := 0x00c5b423.
Lemma F_9ae50 : fetch_word AsanUbsan.M.loaded_segments (0x9ae50 : word) = Some W_9ae50.
Proof. vm_refl. Qed.
Lemma D_9ae50 : decode_any W_9ae50 = Some (Store SZ8 11 12 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9ae54 : bv 32 := 0x00c5b823.
Lemma F_9ae54 : fetch_word AsanUbsan.M.loaded_segments (0x9ae54 : word) = Some W_9ae54.
Proof. vm_refl. Qed.
Lemma D_9ae54 : decode_any W_9ae54 = Some (Store SZ8 11 12 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9ae58 : bv 32 := 0x00c5bc23.
Lemma F_9ae58 : fetch_word AsanUbsan.M.loaded_segments (0x9ae58 : word) = Some W_9ae58.
Proof. vm_refl. Qed.
Lemma D_9ae58 : decode_any W_9ae58 = Some (Store SZ8 11 12 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9ae5c : bv 32 := 0xfe070713.
Lemma F_9ae5c : fetch_word AsanUbsan.M.loaded_segments (0x9ae5c : word) = Some W_9ae5c.
Proof. vm_refl. Qed.
Lemma D_9ae5c : decode_any W_9ae5c = Some (OpImm ALU_ADD 14 14 4064, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9ae60 : bv 32 := 0x02058593.
Lemma F_9ae60 : fetch_word AsanUbsan.M.loaded_segments (0x9ae60 : word) = Some W_9ae60.
Proof. vm_refl. Qed.
Lemma D_9ae60 : decode_any W_9ae60 = Some (OpImm ALU_ADD 11 11 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9ae64 : bv 32 := 0xfee6e4e3.
Lemma F_9ae64 : fetch_word AsanUbsan.M.loaded_segments (0x9ae64 : word) = Some W_9ae64.
Proof. vm_refl. Qed.
Lemma D_9ae64 : decode_any W_9ae64 = Some (Branch BC_LTU 13 14 8168, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9ae68 : bv 32 := 0x00008067.
Lemma F_9ae68 : fetch_word AsanUbsan.M.loaded_segments (0x9ae68 : word) = Some W_9ae68.
Proof. vm_refl. Qed.
Lemma D_9ae68 : decode_any W_9ae68 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Abbreviation MSEGS := AsanUbsan.M.loaded_segments.
Definition ms_base : Z := 0x9ad74%Z.
Definition Fo_000 := F_9ad74.
Definition Do_000 := D_9ad74.
Definition Fo_004 := F_9ad78.
Definition Do_004 := D_9ad78.
Definition Fo_008 := F_9ad7c.
Definition Do_008 := D_9ad7c.
Definition Fo_00c := F_9ad80.
Definition Do_00c := D_9ad80.
Definition Fo_010 := F_9ad84.
Definition Do_010 := D_9ad84.
Definition Fo_014 := F_9ad88.
Definition Do_014 := D_9ad88.
Definition Fo_018 := F_9ad8c.
Definition Do_018 := D_9ad8c.
Definition Fo_01c := F_9ad90.
Definition Do_01c := D_9ad90.
Definition Fo_020 := F_9ad94.
Definition Do_020 := D_9ad94.
Definition Fo_024 := F_9ad98.
Definition Do_024 := D_9ad98.
Definition Fo_028 := F_9ad9c.
Definition Do_028 := D_9ad9c.
Definition Fo_02c := F_9ada0.
Definition Do_02c := D_9ada0.
Definition Fo_030 := F_9ada4.
Definition Do_030 := D_9ada4.
Definition Fo_034 := F_9ada8.
Definition Do_034 := D_9ada8.
Definition Fo_038 := F_9adac.
Definition Do_038 := D_9adac.
Definition Fo_03c := F_9adb0.
Definition Do_03c := D_9adb0.
Definition Fo_040 := F_9adb4.
Definition Do_040 := D_9adb4.
Definition Fo_044 := F_9adb8.
Definition Do_044 := D_9adb8.
Definition Fo_048 := F_9adbc.
Definition Do_048 := D_9adbc.
Definition Fo_04c := F_9adc0.
Definition Do_04c := D_9adc0.
Definition Fo_050 := F_9adc4.
Definition Do_050 := D_9adc4.
Definition Fo_054 := F_9adc8.
Definition Do_054 := D_9adc8.
Definition Fo_058 := F_9adcc.
Definition Do_058 := D_9adcc.
Definition Fo_05c := F_9add0.
Definition Do_05c := D_9add0.
Definition Fo_060 := F_9add4.
Definition Do_060 := D_9add4.
Definition Fo_064 := F_9add8.
Definition Do_064 := D_9add8.
Definition Fo_068 := F_9addc.
Definition Do_068 := D_9addc.
Definition Fo_06c := F_9ade0.
Definition Do_06c := D_9ade0.
Definition Fo_070 := F_9ade4.
Definition Do_070 := D_9ade4.
Definition Fo_074 := F_9ade8.
Definition Do_074 := D_9ade8.
Definition Fo_078 := F_9adec.
Definition Do_078 := D_9adec.
Definition Fo_07c := F_9adf0.
Definition Do_07c := D_9adf0.
Definition Fo_080 := F_9adf4.
Definition Do_080 := D_9adf4.
Definition Fo_084 := F_9adf8.
Definition Do_084 := D_9adf8.
Definition Fo_088 := F_9adfc.
Definition Do_088 := D_9adfc.
Definition Fo_08c := F_9ae00.
Definition Do_08c := D_9ae00.
Definition Fo_090 := F_9ae04.
Definition Do_090 := D_9ae04.
Definition Fo_094 := F_9ae08.
Definition Do_094 := D_9ae08.
Definition Fo_098 := F_9ae0c.
Definition Do_098 := D_9ae0c.
Definition Fo_09c := F_9ae10.
Definition Do_09c := D_9ae10.
Definition Fo_0a0 := F_9ae14.
Definition Do_0a0 := D_9ae14.
Definition Fo_0a4 := F_9ae18.
Definition Do_0a4 := D_9ae18.
Definition Fo_0a8 := F_9ae1c.
Definition Do_0a8 := D_9ae1c.
Definition Fo_0ac := F_9ae20.
Definition Do_0ac := D_9ae20.
Definition Fo_0b0 := F_9ae24.
Definition Do_0b0 := D_9ae24.
Definition Fo_0b4 := F_9ae28.
Definition Do_0b4 := D_9ae28.
Definition Fo_0b8 := F_9ae2c.
Definition Do_0b8 := D_9ae2c.
Definition Fo_0bc := F_9ae30.
Definition Do_0bc := D_9ae30.
Definition Fo_0c0 := F_9ae34.
Definition Do_0c0 := D_9ae34.
Definition Fo_0c4 := F_9ae38.
Definition Do_0c4 := D_9ae38.
Definition Fo_0c8 := F_9ae3c.
Definition Do_0c8 := D_9ae3c.
Definition Fo_0cc := F_9ae40.
Definition Do_0cc := D_9ae40.
Definition Fo_0d0 := F_9ae44.
Definition Do_0d0 := D_9ae44.
Definition Fo_0d4 := F_9ae48.
Definition Do_0d4 := D_9ae48.
Definition Fo_0d8 := F_9ae4c.
Definition Do_0d8 := D_9ae4c.
Definition Fo_0dc := F_9ae50.
Definition Do_0dc := D_9ae50.
Definition Fo_0e0 := F_9ae54.
Definition Do_0e0 := D_9ae54.
Definition Fo_0e4 := F_9ae58.
Definition Do_0e4 := D_9ae58.
Definition Fo_0e8 := F_9ae5c.
Definition Do_0e8 := D_9ae5c.
Definition Fo_0ec := F_9ae60.
Definition Do_0ec := D_9ae60.
Definition Fo_0f0 := F_9ae64.
Definition Do_0f0 := D_9ae64.
Definition Fo_0f4 := F_9ae68.
Definition Do_0f4 := D_9ae68.
