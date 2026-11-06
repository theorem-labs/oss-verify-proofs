(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
(* [comment removed for export] *)

From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.H Require GcFlushS23.   (* [comment removed for export] *)
From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.leptonica.pix_orient_fuzzer.images Require Import Plain.
Open Scope bv_scope.
#[local] Hint Extern 0 (BvWf _ _) => (lazymatch goal with |- BvWf ?n ?v => is_closed_term n; is_closed_term v end; exact I) : typeclass_instances.   (* [comment removed for export] *)

(* [comment removed for export] *)
Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

(* [comment removed for export] *)




(* [comment removed for export] *)
Definition W_10a1e8 : bv 32 := 0x0e060a63.
Lemma F_10a1e8 : fetch_word Plain.M.loaded_segments (0x10a230 : word) = Some W_10a1e8.
Proof. vm_refl. Qed.
Lemma D_10a1e8 : decode_any W_10a1e8 = Some (Branch BC_EQ 12 0 244, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_10a1ec : bv 32 := 0x00b50023.
Lemma F_10a1ec : fetch_word Plain.M.loaded_segments (0x10a234 : word) = Some W_10a1ec.
Proof. vm_refl. Qed.
Lemma D_10a1ec : decode_any W_10a1ec = Some (Store SZ1 10 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_10a1f0 : bv 32 := 0x00c506b3.
Lemma F_10a1f0 : fetch_word Plain.M.loaded_segments (0x10a238 : word) = Some W_10a1f0.
Proof. vm_refl. Qed.
Lemma D_10a1f0 : decode_any W_10a1f0 = Some (Op ALU_ADD 13 10 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_10a1f4 : bv 32 := 0x00300713.
Lemma F_10a1f4 : fetch_word Plain.M.loaded_segments (0x10a23c : word) = Some W_10a1f4.
Proof. vm_refl. Qed.
Lemma D_10a1f4 : decode_any W_10a1f4 = Some (OpImm ALU_ADD 14 0 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_10a1f8 : bv 32 := 0xfeb68fa3.
Lemma F_10a1f8 : fetch_word Plain.M.loaded_segments (0x10a240 : word) = Some W_10a1f8.
Proof. vm_refl. Qed.
Lemma D_10a1f8 : decode_any W_10a1f8 = Some (Store SZ1 13 11 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_10a1fc : bv 32 := 0x0ee66063.
Lemma F_10a1fc : fetch_word Plain.M.loaded_segments (0x10a244 : word) = Some W_10a1fc.
Proof. vm_refl. Qed.
Lemma D_10a1fc : decode_any W_10a1fc = Some (Branch BC_LTU 12 14 224, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_10a200 : bv 32 := 0x00b500a3.
Lemma F_10a200 : fetch_word Plain.M.loaded_segments (0x10a248 : word) = Some W_10a200.
Proof. vm_refl. Qed.
Lemma D_10a200 : decode_any W_10a200 = Some (Store SZ1 10 11 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_10a204 : bv 32 := 0x00b50123.
Lemma F_10a204 : fetch_word Plain.M.loaded_segments (0x10a24c : word) = Some W_10a204.
Proof. vm_refl. Qed.
Lemma D_10a204 : decode_any W_10a204 = Some (Store SZ1 10 11 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_10a208 : bv 32 := 0x00700713.
Lemma F_10a208 : fetch_word Plain.M.loaded_segments (0x10a250 : word) = Some W_10a208.
Proof. vm_refl. Qed.
Lemma D_10a208 : decode_any W_10a208 = Some (OpImm ALU_ADD 14 0 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_10a20c : bv 32 := 0xfeb68ea3.
Lemma F_10a20c : fetch_word Plain.M.loaded_segments (0x10a254 : word) = Some W_10a20c.
Proof. vm_refl. Qed.
Lemma D_10a20c : decode_any W_10a20c = Some (Store SZ1 13 11 4093, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_10a210 : bv 32 := 0xfeb68f23.
Lemma F_10a210 : fetch_word Plain.M.loaded_segments (0x10a258 : word) = Some W_10a210.
Proof. vm_refl. Qed.
Lemma D_10a210 : decode_any W_10a210 = Some (Store SZ1 13 11 4094, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_10a214 : bv 32 := 0x0ce66463.
Lemma F_10a214 : fetch_word Plain.M.loaded_segments (0x10a25c : word) = Some W_10a214.
Proof. vm_refl. Qed.
Lemma D_10a214 : decode_any W_10a214 = Some (Branch BC_LTU 12 14 200, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_10a218 : bv 32 := 0x00b501a3.
Lemma F_10a218 : fetch_word Plain.M.loaded_segments (0x10a260 : word) = Some W_10a218.
Proof. vm_refl. Qed.
Lemma D_10a218 : decode_any W_10a218 = Some (Store SZ1 10 11 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_10a21c : bv 32 := 0x00900793.
Lemma F_10a21c : fetch_word Plain.M.loaded_segments (0x10a264 : word) = Some W_10a21c.
Proof. vm_refl. Qed.
Lemma D_10a21c : decode_any W_10a21c = Some (OpImm ALU_ADD 15 0 9, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_10a220 : bv 32 := 0xfeb68e23.
Lemma F_10a220 : fetch_word Plain.M.loaded_segments (0x10a268 : word) = Some W_10a220.
Proof. vm_refl. Qed.
Lemma D_10a220 : decode_any W_10a220 = Some (Store SZ1 13 11 4092, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_10a224 : bv 32 := 0x0af66c63.
Lemma F_10a224 : fetch_word Plain.M.loaded_segments (0x10a26c : word) = Some W_10a224.
Proof. vm_refl. Qed.
Lemma D_10a224 : decode_any W_10a224 = Some (Branch BC_LTU 12 15 184, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_10a228 : bv 32 := 0x40a006bb.
Lemma F_10a228 : fetch_word Plain.M.loaded_segments (0x10a270 : word) = Some W_10a228.
Proof. vm_refl. Qed.
Lemma D_10a228 : decode_any W_10a228 = Some (Op32 ALU_SUB 13 0 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_10a22c : bv 32 := 0x03859813.
Lemma F_10a22c : fetch_word Plain.M.loaded_segments (0x10a274 : word) = Some W_10a22c.
Proof. vm_refl. Qed.
Lemma D_10a22c : decode_any W_10a22c = Some (ShiftImm ALU_SLL 16 11 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_10a230 : bv 32 := 0x101015b7.
Lemma F_10a230 : fetch_word Plain.M.loaded_segments (0x10a278 : word) = Some W_10a230.
Proof. vm_refl. Qed.
Lemma D_10a230 : decode_any W_10a230 = Some (Lui 11 65793, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_10a234 : bv 32 := 0x0036f693.
Lemma F_10a234 : fetch_word Plain.M.loaded_segments (0x10a27c : word) = Some W_10a234.
Proof. vm_refl. Qed.
Lemma D_10a234 : decode_any W_10a234 = Some (OpImm ALU_AND 13 13 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_10a238 : bv 32 := 0x00459713.
Lemma F_10a238 : fetch_word Plain.M.loaded_segments (0x10a280 : word) = Some W_10a238.
Proof. vm_refl. Qed.
Lemma D_10a238 : decode_any W_10a238 = Some (ShiftImm ALU_SLL 14 11 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_10a23c : bv 32 := 0x40d60633.
Lemma F_10a23c : fetch_word Plain.M.loaded_segments (0x10a284 : word) = Some W_10a23c.
Proof. vm_refl. Qed.
Lemma D_10a23c : decode_any W_10a23c = Some (Op ALU_SUB 12 12 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_10a240 : bv 32 := 0x00d505b3.
Lemma F_10a240 : fetch_word Plain.M.loaded_segments (0x10a288 : word) = Some W_10a240.
Proof. vm_refl. Qed.
Lemma D_10a240 : decode_any W_10a240 = Some (Op ALU_ADD 11 10 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_10a244 : bv 32 := 0x10070693.
Lemma F_10a244 : fetch_word Plain.M.loaded_segments (0x10a28c : word) = Some W_10a244.
Proof. vm_refl. Qed.
Lemma D_10a244 : decode_any W_10a244 = Some (OpImm ALU_ADD 13 14 256, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_10a248 : bv 32 := 0xffc67713.
Lemma F_10a248 : fetch_word Plain.M.loaded_segments (0x10a290 : word) = Some W_10a248.
Proof. vm_refl. Qed.
Lemma D_10a248 : decode_any W_10a248 = Some (OpImm ALU_AND 14 12 4092, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_10a24c : bv 32 := 0x02d83633.
Lemma F_10a24c : fetch_word Plain.M.loaded_segments (0x10a294 : word) = Some W_10a24c.
Proof. vm_refl. Qed.
Lemma D_10a24c : decode_any W_10a24c = Some (Mul M_MULHU 12 16 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_10a250 : bv 32 := 0x00c5a023.
Lemma F_10a250 : fetch_word Plain.M.loaded_segments (0x10a298 : word) = Some W_10a250.
Proof. vm_refl. Qed.
Lemma D_10a250 : decode_any W_10a250 = Some (Store SZ4 11 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_10a254 : bv 32 := 0x00e586b3.
Lemma F_10a254 : fetch_word Plain.M.loaded_segments (0x10a29c : word) = Some W_10a254.
Proof. vm_refl. Qed.
Lemma D_10a254 : decode_any W_10a254 = Some (Op ALU_ADD 13 11 14, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_10a258 : bv 32 := 0xfec6ae23.
Lemma F_10a258 : fetch_word Plain.M.loaded_segments (0x10a2a0 : word) = Some W_10a258.
Proof. vm_refl. Qed.
Lemma D_10a258 : decode_any W_10a258 = Some (Store SZ4 13 12 4092, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_10a25c : bv 32 := 0x08f76063.
Lemma F_10a25c : fetch_word Plain.M.loaded_segments (0x10a2a4 : word) = Some W_10a25c.
Proof. vm_refl. Qed.
Lemma D_10a25c : decode_any W_10a25c = Some (Branch BC_LTU 14 15 128, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_10a260 : bv 32 := 0x00c5a223.
Lemma F_10a260 : fetch_word Plain.M.loaded_segments (0x10a2a8 : word) = Some W_10a260.
Proof. vm_refl. Qed.
Lemma D_10a260 : decode_any W_10a260 = Some (Store SZ4 11 12 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_10a264 : bv 32 := 0x00c5a423.
Lemma F_10a264 : fetch_word Plain.M.loaded_segments (0x10a2ac : word) = Some W_10a264.
Proof. vm_refl. Qed.
Lemma D_10a264 : decode_any W_10a264 = Some (Store SZ4 11 12 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_10a268 : bv 32 := 0x01900793.
Lemma F_10a268 : fetch_word Plain.M.loaded_segments (0x10a2b0 : word) = Some W_10a268.
Proof. vm_refl. Qed.
Lemma D_10a268 : decode_any W_10a268 = Some (OpImm ALU_ADD 15 0 25, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_10a26c : bv 32 := 0xfec6aa23.
Lemma F_10a26c : fetch_word Plain.M.loaded_segments (0x10a2b4 : word) = Some W_10a26c.
Proof. vm_refl. Qed.
Lemma D_10a26c : decode_any W_10a26c = Some (Store SZ4 13 12 4084, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_10a270 : bv 32 := 0xfec6ac23.
Lemma F_10a270 : fetch_word Plain.M.loaded_segments (0x10a2b8 : word) = Some W_10a270.
Proof. vm_refl. Qed.
Lemma D_10a270 : decode_any W_10a270 = Some (Store SZ4 13 12 4088, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_10a274 : bv 32 := 0x06f76463.
Lemma F_10a274 : fetch_word Plain.M.loaded_segments (0x10a2bc : word) = Some W_10a274.
Proof. vm_refl. Qed.
Lemma D_10a274 : decode_any W_10a274 = Some (Branch BC_LTU 14 15 104, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_10a278 : bv 32 := 0x00c5a623.
Lemma F_10a278 : fetch_word Plain.M.loaded_segments (0x10a2c0 : word) = Some W_10a278.
Proof. vm_refl. Qed.
Lemma D_10a278 : decode_any W_10a278 = Some (Store SZ4 11 12 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_10a27c : bv 32 := 0x00c5a823.
Lemma F_10a27c : fetch_word Plain.M.loaded_segments (0x10a2c4 : word) = Some W_10a27c.
Proof. vm_refl. Qed.
Lemma D_10a27c : decode_any W_10a27c = Some (Store SZ4 11 12 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_10a280 : bv 32 := 0x00c5aa23.
Lemma F_10a280 : fetch_word Plain.M.loaded_segments (0x10a2c8 : word) = Some W_10a280.
Proof. vm_refl. Qed.
Lemma D_10a280 : decode_any W_10a280 = Some (Store SZ4 11 12 20, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_10a284 : bv 32 := 0x00c5ac23.
Lemma F_10a284 : fetch_word Plain.M.loaded_segments (0x10a2cc : word) = Some W_10a284.
Proof. vm_refl. Qed.
Lemma D_10a284 : decode_any W_10a284 = Some (Store SZ4 11 12 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_10a288 : bv 32 := 0x0045f793.
Lemma F_10a288 : fetch_word Plain.M.loaded_segments (0x10a2d0 : word) = Some W_10a288.
Proof. vm_refl. Qed.
Lemma D_10a288 : decode_any W_10a288 = Some (OpImm ALU_AND 15 11 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_10a28c : bv 32 := 0x02000813.
Lemma F_10a28c : fetch_word Plain.M.loaded_segments (0x10a2d4 : word) = Some W_10a28c.
Proof. vm_refl. Qed.
Lemma D_10a28c : decode_any W_10a28c = Some (OpImm ALU_ADD 16 0 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_10a290 : bv 32 := 0x01878793.
Lemma F_10a290 : fetch_word Plain.M.loaded_segments (0x10a2d8 : word) = Some W_10a290.
Proof. vm_refl. Qed.
Lemma D_10a290 : decode_any W_10a290 = Some (OpImm ALU_ADD 15 15 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_10a294 : bv 32 := 0x40f70733.
Lemma F_10a294 : fetch_word Plain.M.loaded_segments (0x10a2dc : word) = Some W_10a294.
Proof. vm_refl. Qed.
Lemma D_10a294 : decode_any W_10a294 = Some (Op ALU_SUB 14 14 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_10a298 : bv 32 := 0xfec6a223.
Lemma F_10a298 : fetch_word Plain.M.loaded_segments (0x10a2e0 : word) = Some W_10a298.
Proof. vm_refl. Qed.
Lemma D_10a298 : decode_any W_10a298 = Some (Store SZ4 13 12 4068, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_10a29c : bv 32 := 0xfec6a423.
Lemma F_10a29c : fetch_word Plain.M.loaded_segments (0x10a2e4 : word) = Some W_10a29c.
Proof. vm_refl. Qed.
Lemma D_10a29c : decode_any W_10a29c = Some (Store SZ4 13 12 4072, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_10a2a0 : bv 32 := 0xfec6a623.
Lemma F_10a2a0 : fetch_word Plain.M.loaded_segments (0x10a2e8 : word) = Some W_10a2a0.
Proof. vm_refl. Qed.
Lemma D_10a2a0 : decode_any W_10a2a0 = Some (Store SZ4 13 12 4076, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_10a2a4 : bv 32 := 0xfec6a823.
Lemma F_10a2a4 : fetch_word Plain.M.loaded_segments (0x10a2ec : word) = Some W_10a2a4.
Proof. vm_refl. Qed.
Lemma D_10a2a4 : decode_any W_10a2a4 = Some (Store SZ4 13 12 4080, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_10a2a8 : bv 32 := 0x03076a63.
Lemma F_10a2a8 : fetch_word Plain.M.loaded_segments (0x10a2f0 : word) = Some W_10a2a8.
Proof. vm_refl. Qed.
Lemma D_10a2a8 : decode_any W_10a2a8 = Some (Branch BC_LTU 14 16 52, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_10a2ac : bv 32 := 0x02061613.
Lemma F_10a2ac : fetch_word Plain.M.loaded_segments (0x10a2f4 : word) = Some W_10a2ac.
Proof. vm_refl. Qed.
Lemma D_10a2ac : decode_any W_10a2ac = Some (ShiftImm ALU_SLL 12 12 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_10a2b0 : bv 32 := 0x00f585b3.
Lemma F_10a2b0 : fetch_word Plain.M.loaded_segments (0x10a2f8 : word) = Some W_10a2b0.
Proof. vm_refl. Qed.
Lemma D_10a2b0 : decode_any W_10a2b0 = Some (Op ALU_ADD 11 11 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_10a2b4 : bv 32 := 0x02065693.
Lemma F_10a2b4 : fetch_word Plain.M.loaded_segments (0x10a2fc : word) = Some W_10a2b4.
Proof. vm_refl. Qed.
Lemma D_10a2b4 : decode_any W_10a2b4 = Some (ShiftImm ALU_SRL 13 12 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_10a2b8 : bv 32 := 0x00d66633.
Lemma F_10a2b8 : fetch_word Plain.M.loaded_segments (0x10a300 : word) = Some W_10a2b8.
Proof. vm_refl. Qed.
Lemma D_10a2b8 : decode_any W_10a2b8 = Some (Op ALU_OR 12 12 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_10a2bc : bv 32 := 0x01f00693.
Lemma F_10a2bc : fetch_word Plain.M.loaded_segments (0x10a304 : word) = Some W_10a2bc.
Proof. vm_refl. Qed.
Lemma D_10a2bc : decode_any W_10a2bc = Some (OpImm ALU_ADD 13 0 31, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_10a2c0 : bv 32 := 0x00c5b023.
Lemma F_10a2c0 : fetch_word Plain.M.loaded_segments (0x10a308 : word) = Some W_10a2c0.
Proof. vm_refl. Qed.
Lemma D_10a2c0 : decode_any W_10a2c0 = Some (Store SZ8 11 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_10a2c4 : bv 32 := 0x00c5b423.
Lemma F_10a2c4 : fetch_word Plain.M.loaded_segments (0x10a30c : word) = Some W_10a2c4.
Proof. vm_refl. Qed.
Lemma D_10a2c4 : decode_any W_10a2c4 = Some (Store SZ8 11 12 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_10a2c8 : bv 32 := 0x00c5b823.
Lemma F_10a2c8 : fetch_word Plain.M.loaded_segments (0x10a310 : word) = Some W_10a2c8.
Proof. vm_refl. Qed.
Lemma D_10a2c8 : decode_any W_10a2c8 = Some (Store SZ8 11 12 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_10a2cc : bv 32 := 0x00c5bc23.
Lemma F_10a2cc : fetch_word Plain.M.loaded_segments (0x10a314 : word) = Some W_10a2cc.
Proof. vm_refl. Qed.
Lemma D_10a2cc : decode_any W_10a2cc = Some (Store SZ8 11 12 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_10a2d0 : bv 32 := 0xfe070713.
Lemma F_10a2d0 : fetch_word Plain.M.loaded_segments (0x10a318 : word) = Some W_10a2d0.
Proof. vm_refl. Qed.
Lemma D_10a2d0 : decode_any W_10a2d0 = Some (OpImm ALU_ADD 14 14 4064, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_10a2d4 : bv 32 := 0x02058593.
Lemma F_10a2d4 : fetch_word Plain.M.loaded_segments (0x10a31c : word) = Some W_10a2d4.
Proof. vm_refl. Qed.
Lemma D_10a2d4 : decode_any W_10a2d4 = Some (OpImm ALU_ADD 11 11 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_10a2d8 : bv 32 := 0xfee6e4e3.
Lemma F_10a2d8 : fetch_word Plain.M.loaded_segments (0x10a320 : word) = Some W_10a2d8.
Proof. vm_refl. Qed.
Lemma D_10a2d8 : decode_any W_10a2d8 = Some (Branch BC_LTU 13 14 8168, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_10a2dc : bv 32 := 0x00008067.
Lemma F_10a2dc : fetch_word Plain.M.loaded_segments (0x10a324 : word) = Some W_10a2dc.
Proof. vm_refl. Qed.
Lemma D_10a2dc : decode_any W_10a2dc = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.
