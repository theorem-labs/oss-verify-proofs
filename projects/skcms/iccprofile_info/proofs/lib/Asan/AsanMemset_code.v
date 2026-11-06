(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.skcms.iccprofile_info.images Require Import Asan.
Unset Lia Cache. Unset Nia Cache.  (* [comment removed for export] *)
Open Scope bv_scope.

(* [comment removed for export] *)
Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

(* [comment removed for export] *)
Definition W_98220 : bv 32 := 0x0e060a63.
Lemma F_98220 : fetch_word Asan.M.loaded_segments (0x98220 : word) = Some W_98220.
Proof. vm_refl. Qed.
Lemma D_98220 : decode_any W_98220 = Some (Branch BC_EQ 12 0 244, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_98224 : bv 32 := 0x00b50023.
Lemma F_98224 : fetch_word Asan.M.loaded_segments (0x98224 : word) = Some W_98224.
Proof. vm_refl. Qed.
Lemma D_98224 : decode_any W_98224 = Some (Store SZ1 10 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_98228 : bv 32 := 0x00c506b3.
Lemma F_98228 : fetch_word Asan.M.loaded_segments (0x98228 : word) = Some W_98228.
Proof. vm_refl. Qed.
Lemma D_98228 : decode_any W_98228 = Some (Op ALU_ADD 13 10 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9822c : bv 32 := 0x00300713.
Lemma F_9822c : fetch_word Asan.M.loaded_segments (0x9822c : word) = Some W_9822c.
Proof. vm_refl. Qed.
Lemma D_9822c : decode_any W_9822c = Some (OpImm ALU_ADD 14 0 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_98230 : bv 32 := 0xfeb68fa3.
Lemma F_98230 : fetch_word Asan.M.loaded_segments (0x98230 : word) = Some W_98230.
Proof. vm_refl. Qed.
Lemma D_98230 : decode_any W_98230 = Some (Store SZ1 13 11 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_98234 : bv 32 := 0x0ee66063.
Lemma F_98234 : fetch_word Asan.M.loaded_segments (0x98234 : word) = Some W_98234.
Proof. vm_refl. Qed.
Lemma D_98234 : decode_any W_98234 = Some (Branch BC_LTU 12 14 224, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_98238 : bv 32 := 0x00b500a3.
Lemma F_98238 : fetch_word Asan.M.loaded_segments (0x98238 : word) = Some W_98238.
Proof. vm_refl. Qed.
Lemma D_98238 : decode_any W_98238 = Some (Store SZ1 10 11 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9823c : bv 32 := 0x00b50123.
Lemma F_9823c : fetch_word Asan.M.loaded_segments (0x9823c : word) = Some W_9823c.
Proof. vm_refl. Qed.
Lemma D_9823c : decode_any W_9823c = Some (Store SZ1 10 11 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_98240 : bv 32 := 0x00700713.
Lemma F_98240 : fetch_word Asan.M.loaded_segments (0x98240 : word) = Some W_98240.
Proof. vm_refl. Qed.
Lemma D_98240 : decode_any W_98240 = Some (OpImm ALU_ADD 14 0 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_98244 : bv 32 := 0xfeb68ea3.
Lemma F_98244 : fetch_word Asan.M.loaded_segments (0x98244 : word) = Some W_98244.
Proof. vm_refl. Qed.
Lemma D_98244 : decode_any W_98244 = Some (Store SZ1 13 11 4093, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_98248 : bv 32 := 0xfeb68f23.
Lemma F_98248 : fetch_word Asan.M.loaded_segments (0x98248 : word) = Some W_98248.
Proof. vm_refl. Qed.
Lemma D_98248 : decode_any W_98248 = Some (Store SZ1 13 11 4094, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9824c : bv 32 := 0x0ce66463.
Lemma F_9824c : fetch_word Asan.M.loaded_segments (0x9824c : word) = Some W_9824c.
Proof. vm_refl. Qed.
Lemma D_9824c : decode_any W_9824c = Some (Branch BC_LTU 12 14 200, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_98250 : bv 32 := 0x00b501a3.
Lemma F_98250 : fetch_word Asan.M.loaded_segments (0x98250 : word) = Some W_98250.
Proof. vm_refl. Qed.
Lemma D_98250 : decode_any W_98250 = Some (Store SZ1 10 11 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_98254 : bv 32 := 0x00900793.
Lemma F_98254 : fetch_word Asan.M.loaded_segments (0x98254 : word) = Some W_98254.
Proof. vm_refl. Qed.
Lemma D_98254 : decode_any W_98254 = Some (OpImm ALU_ADD 15 0 9, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_98258 : bv 32 := 0xfeb68e23.
Lemma F_98258 : fetch_word Asan.M.loaded_segments (0x98258 : word) = Some W_98258.
Proof. vm_refl. Qed.
Lemma D_98258 : decode_any W_98258 = Some (Store SZ1 13 11 4092, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9825c : bv 32 := 0x0af66c63.
Lemma F_9825c : fetch_word Asan.M.loaded_segments (0x9825c : word) = Some W_9825c.
Proof. vm_refl. Qed.
Lemma D_9825c : decode_any W_9825c = Some (Branch BC_LTU 12 15 184, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_98260 : bv 32 := 0x40a006bb.
Lemma F_98260 : fetch_word Asan.M.loaded_segments (0x98260 : word) = Some W_98260.
Proof. vm_refl. Qed.
Lemma D_98260 : decode_any W_98260 = Some (Op32 ALU_SUB 13 0 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_98264 : bv 32 := 0x03859813.
Lemma F_98264 : fetch_word Asan.M.loaded_segments (0x98264 : word) = Some W_98264.
Proof. vm_refl. Qed.
Lemma D_98264 : decode_any W_98264 = Some (ShiftImm ALU_SLL 16 11 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_98268 : bv 32 := 0x101015b7.
Lemma F_98268 : fetch_word Asan.M.loaded_segments (0x98268 : word) = Some W_98268.
Proof. vm_refl. Qed.
Lemma D_98268 : decode_any W_98268 = Some (Lui 11 65793, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9826c : bv 32 := 0x0036f693.
Lemma F_9826c : fetch_word Asan.M.loaded_segments (0x9826c : word) = Some W_9826c.
Proof. vm_refl. Qed.
Lemma D_9826c : decode_any W_9826c = Some (OpImm ALU_AND 13 13 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_98270 : bv 32 := 0x00459713.
Lemma F_98270 : fetch_word Asan.M.loaded_segments (0x98270 : word) = Some W_98270.
Proof. vm_refl. Qed.
Lemma D_98270 : decode_any W_98270 = Some (ShiftImm ALU_SLL 14 11 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_98274 : bv 32 := 0x40d60633.
Lemma F_98274 : fetch_word Asan.M.loaded_segments (0x98274 : word) = Some W_98274.
Proof. vm_refl. Qed.
Lemma D_98274 : decode_any W_98274 = Some (Op ALU_SUB 12 12 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_98278 : bv 32 := 0x00d505b3.
Lemma F_98278 : fetch_word Asan.M.loaded_segments (0x98278 : word) = Some W_98278.
Proof. vm_refl. Qed.
Lemma D_98278 : decode_any W_98278 = Some (Op ALU_ADD 11 10 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9827c : bv 32 := 0x10070693.
Lemma F_9827c : fetch_word Asan.M.loaded_segments (0x9827c : word) = Some W_9827c.
Proof. vm_refl. Qed.
Lemma D_9827c : decode_any W_9827c = Some (OpImm ALU_ADD 13 14 256, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_98280 : bv 32 := 0xffc67713.
Lemma F_98280 : fetch_word Asan.M.loaded_segments (0x98280 : word) = Some W_98280.
Proof. vm_refl. Qed.
Lemma D_98280 : decode_any W_98280 = Some (OpImm ALU_AND 14 12 4092, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_98284 : bv 32 := 0x02d83633.
Lemma F_98284 : fetch_word Asan.M.loaded_segments (0x98284 : word) = Some W_98284.
Proof. vm_refl. Qed.
Lemma D_98284 : decode_any W_98284 = Some (Mul M_MULHU 12 16 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_98288 : bv 32 := 0x00c5a023.
Lemma F_98288 : fetch_word Asan.M.loaded_segments (0x98288 : word) = Some W_98288.
Proof. vm_refl. Qed.
Lemma D_98288 : decode_any W_98288 = Some (Store SZ4 11 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9828c : bv 32 := 0x00e586b3.
Lemma F_9828c : fetch_word Asan.M.loaded_segments (0x9828c : word) = Some W_9828c.
Proof. vm_refl. Qed.
Lemma D_9828c : decode_any W_9828c = Some (Op ALU_ADD 13 11 14, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_98290 : bv 32 := 0xfec6ae23.
Lemma F_98290 : fetch_word Asan.M.loaded_segments (0x98290 : word) = Some W_98290.
Proof. vm_refl. Qed.
Lemma D_98290 : decode_any W_98290 = Some (Store SZ4 13 12 4092, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_98294 : bv 32 := 0x08f76063.
Lemma F_98294 : fetch_word Asan.M.loaded_segments (0x98294 : word) = Some W_98294.
Proof. vm_refl. Qed.
Lemma D_98294 : decode_any W_98294 = Some (Branch BC_LTU 14 15 128, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_98298 : bv 32 := 0x00c5a223.
Lemma F_98298 : fetch_word Asan.M.loaded_segments (0x98298 : word) = Some W_98298.
Proof. vm_refl. Qed.
Lemma D_98298 : decode_any W_98298 = Some (Store SZ4 11 12 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9829c : bv 32 := 0x00c5a423.
Lemma F_9829c : fetch_word Asan.M.loaded_segments (0x9829c : word) = Some W_9829c.
Proof. vm_refl. Qed.
Lemma D_9829c : decode_any W_9829c = Some (Store SZ4 11 12 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_982a0 : bv 32 := 0x01900793.
Lemma F_982a0 : fetch_word Asan.M.loaded_segments (0x982a0 : word) = Some W_982a0.
Proof. vm_refl. Qed.
Lemma D_982a0 : decode_any W_982a0 = Some (OpImm ALU_ADD 15 0 25, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_982a4 : bv 32 := 0xfec6aa23.
Lemma F_982a4 : fetch_word Asan.M.loaded_segments (0x982a4 : word) = Some W_982a4.
Proof. vm_refl. Qed.
Lemma D_982a4 : decode_any W_982a4 = Some (Store SZ4 13 12 4084, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_982a8 : bv 32 := 0xfec6ac23.
Lemma F_982a8 : fetch_word Asan.M.loaded_segments (0x982a8 : word) = Some W_982a8.
Proof. vm_refl. Qed.
Lemma D_982a8 : decode_any W_982a8 = Some (Store SZ4 13 12 4088, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_982ac : bv 32 := 0x06f76463.
Lemma F_982ac : fetch_word Asan.M.loaded_segments (0x982ac : word) = Some W_982ac.
Proof. vm_refl. Qed.
Lemma D_982ac : decode_any W_982ac = Some (Branch BC_LTU 14 15 104, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_982b0 : bv 32 := 0x00c5a623.
Lemma F_982b0 : fetch_word Asan.M.loaded_segments (0x982b0 : word) = Some W_982b0.
Proof. vm_refl. Qed.
Lemma D_982b0 : decode_any W_982b0 = Some (Store SZ4 11 12 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_982b4 : bv 32 := 0x00c5a823.
Lemma F_982b4 : fetch_word Asan.M.loaded_segments (0x982b4 : word) = Some W_982b4.
Proof. vm_refl. Qed.
Lemma D_982b4 : decode_any W_982b4 = Some (Store SZ4 11 12 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_982b8 : bv 32 := 0x00c5aa23.
Lemma F_982b8 : fetch_word Asan.M.loaded_segments (0x982b8 : word) = Some W_982b8.
Proof. vm_refl. Qed.
Lemma D_982b8 : decode_any W_982b8 = Some (Store SZ4 11 12 20, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_982bc : bv 32 := 0x00c5ac23.
Lemma F_982bc : fetch_word Asan.M.loaded_segments (0x982bc : word) = Some W_982bc.
Proof. vm_refl. Qed.
Lemma D_982bc : decode_any W_982bc = Some (Store SZ4 11 12 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_982c0 : bv 32 := 0x0045f793.
Lemma F_982c0 : fetch_word Asan.M.loaded_segments (0x982c0 : word) = Some W_982c0.
Proof. vm_refl. Qed.
Lemma D_982c0 : decode_any W_982c0 = Some (OpImm ALU_AND 15 11 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_982c4 : bv 32 := 0x02000813.
Lemma F_982c4 : fetch_word Asan.M.loaded_segments (0x982c4 : word) = Some W_982c4.
Proof. vm_refl. Qed.
Lemma D_982c4 : decode_any W_982c4 = Some (OpImm ALU_ADD 16 0 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_982c8 : bv 32 := 0x01878793.
Lemma F_982c8 : fetch_word Asan.M.loaded_segments (0x982c8 : word) = Some W_982c8.
Proof. vm_refl. Qed.
Lemma D_982c8 : decode_any W_982c8 = Some (OpImm ALU_ADD 15 15 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_982cc : bv 32 := 0x40f70733.
Lemma F_982cc : fetch_word Asan.M.loaded_segments (0x982cc : word) = Some W_982cc.
Proof. vm_refl. Qed.
Lemma D_982cc : decode_any W_982cc = Some (Op ALU_SUB 14 14 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_982d0 : bv 32 := 0xfec6a223.
Lemma F_982d0 : fetch_word Asan.M.loaded_segments (0x982d0 : word) = Some W_982d0.
Proof. vm_refl. Qed.
Lemma D_982d0 : decode_any W_982d0 = Some (Store SZ4 13 12 4068, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_982d4 : bv 32 := 0xfec6a423.
Lemma F_982d4 : fetch_word Asan.M.loaded_segments (0x982d4 : word) = Some W_982d4.
Proof. vm_refl. Qed.
Lemma D_982d4 : decode_any W_982d4 = Some (Store SZ4 13 12 4072, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_982d8 : bv 32 := 0xfec6a623.
Lemma F_982d8 : fetch_word Asan.M.loaded_segments (0x982d8 : word) = Some W_982d8.
Proof. vm_refl. Qed.
Lemma D_982d8 : decode_any W_982d8 = Some (Store SZ4 13 12 4076, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_982dc : bv 32 := 0xfec6a823.
Lemma F_982dc : fetch_word Asan.M.loaded_segments (0x982dc : word) = Some W_982dc.
Proof. vm_refl. Qed.
Lemma D_982dc : decode_any W_982dc = Some (Store SZ4 13 12 4080, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_982e0 : bv 32 := 0x03076a63.
Lemma F_982e0 : fetch_word Asan.M.loaded_segments (0x982e0 : word) = Some W_982e0.
Proof. vm_refl. Qed.
Lemma D_982e0 : decode_any W_982e0 = Some (Branch BC_LTU 14 16 52, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_982e4 : bv 32 := 0x02061613.
Lemma F_982e4 : fetch_word Asan.M.loaded_segments (0x982e4 : word) = Some W_982e4.
Proof. vm_refl. Qed.
Lemma D_982e4 : decode_any W_982e4 = Some (ShiftImm ALU_SLL 12 12 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_982e8 : bv 32 := 0x00f585b3.
Lemma F_982e8 : fetch_word Asan.M.loaded_segments (0x982e8 : word) = Some W_982e8.
Proof. vm_refl. Qed.
Lemma D_982e8 : decode_any W_982e8 = Some (Op ALU_ADD 11 11 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_982ec : bv 32 := 0x02065693.
Lemma F_982ec : fetch_word Asan.M.loaded_segments (0x982ec : word) = Some W_982ec.
Proof. vm_refl. Qed.
Lemma D_982ec : decode_any W_982ec = Some (ShiftImm ALU_SRL 13 12 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_982f0 : bv 32 := 0x00d66633.
Lemma F_982f0 : fetch_word Asan.M.loaded_segments (0x982f0 : word) = Some W_982f0.
Proof. vm_refl. Qed.
Lemma D_982f0 : decode_any W_982f0 = Some (Op ALU_OR 12 12 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_982f4 : bv 32 := 0x01f00693.
Lemma F_982f4 : fetch_word Asan.M.loaded_segments (0x982f4 : word) = Some W_982f4.
Proof. vm_refl. Qed.
Lemma D_982f4 : decode_any W_982f4 = Some (OpImm ALU_ADD 13 0 31, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_982f8 : bv 32 := 0x00c5b023.
Lemma F_982f8 : fetch_word Asan.M.loaded_segments (0x982f8 : word) = Some W_982f8.
Proof. vm_refl. Qed.
Lemma D_982f8 : decode_any W_982f8 = Some (Store SZ8 11 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_982fc : bv 32 := 0x00c5b423.
Lemma F_982fc : fetch_word Asan.M.loaded_segments (0x982fc : word) = Some W_982fc.
Proof. vm_refl. Qed.
Lemma D_982fc : decode_any W_982fc = Some (Store SZ8 11 12 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_98300 : bv 32 := 0x00c5b823.
Lemma F_98300 : fetch_word Asan.M.loaded_segments (0x98300 : word) = Some W_98300.
Proof. vm_refl. Qed.
Lemma D_98300 : decode_any W_98300 = Some (Store SZ8 11 12 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_98304 : bv 32 := 0x00c5bc23.
Lemma F_98304 : fetch_word Asan.M.loaded_segments (0x98304 : word) = Some W_98304.
Proof. vm_refl. Qed.
Lemma D_98304 : decode_any W_98304 = Some (Store SZ8 11 12 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_98308 : bv 32 := 0xfe070713.
Lemma F_98308 : fetch_word Asan.M.loaded_segments (0x98308 : word) = Some W_98308.
Proof. vm_refl. Qed.
Lemma D_98308 : decode_any W_98308 = Some (OpImm ALU_ADD 14 14 4064, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9830c : bv 32 := 0x02058593.
Lemma F_9830c : fetch_word Asan.M.loaded_segments (0x9830c : word) = Some W_9830c.
Proof. vm_refl. Qed.
Lemma D_9830c : decode_any W_9830c = Some (OpImm ALU_ADD 11 11 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_98310 : bv 32 := 0xfee6e4e3.
Lemma F_98310 : fetch_word Asan.M.loaded_segments (0x98310 : word) = Some W_98310.
Proof. vm_refl. Qed.
Lemma D_98310 : decode_any W_98310 = Some (Branch BC_LTU 13 14 8168, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_98314 : bv 32 := 0x00008067.
Lemma F_98314 : fetch_word Asan.M.loaded_segments (0x98314 : word) = Some W_98314.
Proof. vm_refl. Qed.
Lemma D_98314 : decode_any W_98314 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Abbreviation MSEGS := Asan.M.loaded_segments.
Definition ms_base : Z := 0x98220%Z.
Definition Fo_000 := F_98220.
Definition Do_000 := D_98220.
Definition Fo_004 := F_98224.
Definition Do_004 := D_98224.
Definition Fo_008 := F_98228.
Definition Do_008 := D_98228.
Definition Fo_00c := F_9822c.
Definition Do_00c := D_9822c.
Definition Fo_010 := F_98230.
Definition Do_010 := D_98230.
Definition Fo_014 := F_98234.
Definition Do_014 := D_98234.
Definition Fo_018 := F_98238.
Definition Do_018 := D_98238.
Definition Fo_01c := F_9823c.
Definition Do_01c := D_9823c.
Definition Fo_020 := F_98240.
Definition Do_020 := D_98240.
Definition Fo_024 := F_98244.
Definition Do_024 := D_98244.
Definition Fo_028 := F_98248.
Definition Do_028 := D_98248.
Definition Fo_02c := F_9824c.
Definition Do_02c := D_9824c.
Definition Fo_030 := F_98250.
Definition Do_030 := D_98250.
Definition Fo_034 := F_98254.
Definition Do_034 := D_98254.
Definition Fo_038 := F_98258.
Definition Do_038 := D_98258.
Definition Fo_03c := F_9825c.
Definition Do_03c := D_9825c.
Definition Fo_040 := F_98260.
Definition Do_040 := D_98260.
Definition Fo_044 := F_98264.
Definition Do_044 := D_98264.
Definition Fo_048 := F_98268.
Definition Do_048 := D_98268.
Definition Fo_04c := F_9826c.
Definition Do_04c := D_9826c.
Definition Fo_050 := F_98270.
Definition Do_050 := D_98270.
Definition Fo_054 := F_98274.
Definition Do_054 := D_98274.
Definition Fo_058 := F_98278.
Definition Do_058 := D_98278.
Definition Fo_05c := F_9827c.
Definition Do_05c := D_9827c.
Definition Fo_060 := F_98280.
Definition Do_060 := D_98280.
Definition Fo_064 := F_98284.
Definition Do_064 := D_98284.
Definition Fo_068 := F_98288.
Definition Do_068 := D_98288.
Definition Fo_06c := F_9828c.
Definition Do_06c := D_9828c.
Definition Fo_070 := F_98290.
Definition Do_070 := D_98290.
Definition Fo_074 := F_98294.
Definition Do_074 := D_98294.
Definition Fo_078 := F_98298.
Definition Do_078 := D_98298.
Definition Fo_07c := F_9829c.
Definition Do_07c := D_9829c.
Definition Fo_080 := F_982a0.
Definition Do_080 := D_982a0.
Definition Fo_084 := F_982a4.
Definition Do_084 := D_982a4.
Definition Fo_088 := F_982a8.
Definition Do_088 := D_982a8.
Definition Fo_08c := F_982ac.
Definition Do_08c := D_982ac.
Definition Fo_090 := F_982b0.
Definition Do_090 := D_982b0.
Definition Fo_094 := F_982b4.
Definition Do_094 := D_982b4.
Definition Fo_098 := F_982b8.
Definition Do_098 := D_982b8.
Definition Fo_09c := F_982bc.
Definition Do_09c := D_982bc.
Definition Fo_0a0 := F_982c0.
Definition Do_0a0 := D_982c0.
Definition Fo_0a4 := F_982c4.
Definition Do_0a4 := D_982c4.
Definition Fo_0a8 := F_982c8.
Definition Do_0a8 := D_982c8.
Definition Fo_0ac := F_982cc.
Definition Do_0ac := D_982cc.
Definition Fo_0b0 := F_982d0.
Definition Do_0b0 := D_982d0.
Definition Fo_0b4 := F_982d4.
Definition Do_0b4 := D_982d4.
Definition Fo_0b8 := F_982d8.
Definition Do_0b8 := D_982d8.
Definition Fo_0bc := F_982dc.
Definition Do_0bc := D_982dc.
Definition Fo_0c0 := F_982e0.
Definition Do_0c0 := D_982e0.
Definition Fo_0c4 := F_982e4.
Definition Do_0c4 := D_982e4.
Definition Fo_0c8 := F_982e8.
Definition Do_0c8 := D_982e8.
Definition Fo_0cc := F_982ec.
Definition Do_0cc := D_982ec.
Definition Fo_0d0 := F_982f0.
Definition Do_0d0 := D_982f0.
Definition Fo_0d4 := F_982f4.
Definition Do_0d4 := D_982f4.
Definition Fo_0d8 := F_982f8.
Definition Do_0d8 := D_982f8.
Definition Fo_0dc := F_982fc.
Definition Do_0dc := D_982fc.
Definition Fo_0e0 := F_98300.
Definition Do_0e0 := D_98300.
Definition Fo_0e4 := F_98304.
Definition Do_0e4 := D_98304.
Definition Fo_0e8 := F_98308.
Definition Do_0e8 := D_98308.
Definition Fo_0ec := F_9830c.
Definition Do_0ec := D_9830c.
Definition Fo_0f0 := F_98310.
Definition Do_0f0 := D_98310.
Definition Fo_0f4 := F_98314.
Definition Do_0f4 := D_98314.
