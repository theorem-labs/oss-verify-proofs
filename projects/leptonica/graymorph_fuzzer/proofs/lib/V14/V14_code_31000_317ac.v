(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
(* [comment removed for export] *)

From OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.H Require GcFlushU14.   (* [comment removed for export] *)
From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.leptonica.graymorph_fuzzer.images Require Import Ubsan.
Open Scope bv_scope.
#[local] Hint Extern 0 (BvWf _ _) => (lazymatch goal with |- BvWf ?n ?v => is_closed_term n; is_closed_term v end; exact I) : typeclass_instances.   (* [comment removed for export] *)

(* [comment removed for export] *)
Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

(* [comment removed for export] *)



(* [comment removed for export] *)
Definition W_3121c : bv 32 := 0x0e060a63.
Lemma F_3121c : fetch_word Ubsan.M.loaded_segments (0x31758 : word) = Some W_3121c.
Proof. vm_refl. Qed.
Lemma D_3121c : decode_any W_3121c = Some (Branch BC_EQ 12 0 244, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_31220 : bv 32 := 0x00b50023.
Lemma F_31220 : fetch_word Ubsan.M.loaded_segments (0x3175c : word) = Some W_31220.
Proof. vm_refl. Qed.
Lemma D_31220 : decode_any W_31220 = Some (Store SZ1 10 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_31224 : bv 32 := 0x00c506b3.
Lemma F_31224 : fetch_word Ubsan.M.loaded_segments (0x31760 : word) = Some W_31224.
Proof. vm_refl. Qed.
Lemma D_31224 : decode_any W_31224 = Some (Op ALU_ADD 13 10 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_31228 : bv 32 := 0x00300713.
Lemma F_31228 : fetch_word Ubsan.M.loaded_segments (0x31764 : word) = Some W_31228.
Proof. vm_refl. Qed.
Lemma D_31228 : decode_any W_31228 = Some (OpImm ALU_ADD 14 0 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3122c : bv 32 := 0xfeb68fa3.
Lemma F_3122c : fetch_word Ubsan.M.loaded_segments (0x31768 : word) = Some W_3122c.
Proof. vm_refl. Qed.
Lemma D_3122c : decode_any W_3122c = Some (Store SZ1 13 11 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_31230 : bv 32 := 0x0ee66063.
Lemma F_31230 : fetch_word Ubsan.M.loaded_segments (0x3176c : word) = Some W_31230.
Proof. vm_refl. Qed.
Lemma D_31230 : decode_any W_31230 = Some (Branch BC_LTU 12 14 224, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_31234 : bv 32 := 0x00b500a3.
Lemma F_31234 : fetch_word Ubsan.M.loaded_segments (0x31770 : word) = Some W_31234.
Proof. vm_refl. Qed.
Lemma D_31234 : decode_any W_31234 = Some (Store SZ1 10 11 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_31238 : bv 32 := 0x00b50123.
Lemma F_31238 : fetch_word Ubsan.M.loaded_segments (0x31774 : word) = Some W_31238.
Proof. vm_refl. Qed.
Lemma D_31238 : decode_any W_31238 = Some (Store SZ1 10 11 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3123c : bv 32 := 0x00700713.
Lemma F_3123c : fetch_word Ubsan.M.loaded_segments (0x31778 : word) = Some W_3123c.
Proof. vm_refl. Qed.
Lemma D_3123c : decode_any W_3123c = Some (OpImm ALU_ADD 14 0 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_31240 : bv 32 := 0xfeb68ea3.
Lemma F_31240 : fetch_word Ubsan.M.loaded_segments (0x3177c : word) = Some W_31240.
Proof. vm_refl. Qed.
Lemma D_31240 : decode_any W_31240 = Some (Store SZ1 13 11 4093, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_31244 : bv 32 := 0xfeb68f23.
Lemma F_31244 : fetch_word Ubsan.M.loaded_segments (0x31780 : word) = Some W_31244.
Proof. vm_refl. Qed.
Lemma D_31244 : decode_any W_31244 = Some (Store SZ1 13 11 4094, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_31248 : bv 32 := 0x0ce66463.
Lemma F_31248 : fetch_word Ubsan.M.loaded_segments (0x31784 : word) = Some W_31248.
Proof. vm_refl. Qed.
Lemma D_31248 : decode_any W_31248 = Some (Branch BC_LTU 12 14 200, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3124c : bv 32 := 0x00b501a3.
Lemma F_3124c : fetch_word Ubsan.M.loaded_segments (0x31788 : word) = Some W_3124c.
Proof. vm_refl. Qed.
Lemma D_3124c : decode_any W_3124c = Some (Store SZ1 10 11 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_31250 : bv 32 := 0x00900793.
Lemma F_31250 : fetch_word Ubsan.M.loaded_segments (0x3178c : word) = Some W_31250.
Proof. vm_refl. Qed.
Lemma D_31250 : decode_any W_31250 = Some (OpImm ALU_ADD 15 0 9, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_31254 : bv 32 := 0xfeb68e23.
Lemma F_31254 : fetch_word Ubsan.M.loaded_segments (0x31790 : word) = Some W_31254.
Proof. vm_refl. Qed.
Lemma D_31254 : decode_any W_31254 = Some (Store SZ1 13 11 4092, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_31258 : bv 32 := 0x0af66c63.
Lemma F_31258 : fetch_word Ubsan.M.loaded_segments (0x31794 : word) = Some W_31258.
Proof. vm_refl. Qed.
Lemma D_31258 : decode_any W_31258 = Some (Branch BC_LTU 12 15 184, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3125c : bv 32 := 0x40a006bb.
Lemma F_3125c : fetch_word Ubsan.M.loaded_segments (0x31798 : word) = Some W_3125c.
Proof. vm_refl. Qed.
Lemma D_3125c : decode_any W_3125c = Some (Op32 ALU_SUB 13 0 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_31260 : bv 32 := 0x03859813.
Lemma F_31260 : fetch_word Ubsan.M.loaded_segments (0x3179c : word) = Some W_31260.
Proof. vm_refl. Qed.
Lemma D_31260 : decode_any W_31260 = Some (ShiftImm ALU_SLL 16 11 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_31264 : bv 32 := 0x101015b7.
Lemma F_31264 : fetch_word Ubsan.M.loaded_segments (0x317a0 : word) = Some W_31264.
Proof. vm_refl. Qed.
Lemma D_31264 : decode_any W_31264 = Some (Lui 11 65793, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_31268 : bv 32 := 0x0036f693.
Lemma F_31268 : fetch_word Ubsan.M.loaded_segments (0x317a4 : word) = Some W_31268.
Proof. vm_refl. Qed.
Lemma D_31268 : decode_any W_31268 = Some (OpImm ALU_AND 13 13 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3126c : bv 32 := 0x00459713.
Lemma F_3126c : fetch_word Ubsan.M.loaded_segments (0x317a8 : word) = Some W_3126c.
Proof. vm_refl. Qed.
Lemma D_3126c : decode_any W_3126c = Some (ShiftImm ALU_SLL 14 11 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_31270 : bv 32 := 0x40d60633.
Lemma F_31270 : fetch_word Ubsan.M.loaded_segments (0x317ac : word) = Some W_31270.
Proof. vm_refl. Qed.
Lemma D_31270 : decode_any W_31270 = Some (Op ALU_SUB 12 12 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_31274 : bv 32 := 0x00d505b3.
Lemma F_31274 : fetch_word Ubsan.M.loaded_segments (0x317b0 : word) = Some W_31274.
Proof. vm_refl. Qed.
Lemma D_31274 : decode_any W_31274 = Some (Op ALU_ADD 11 10 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_31278 : bv 32 := 0x10070693.
Lemma F_31278 : fetch_word Ubsan.M.loaded_segments (0x317b4 : word) = Some W_31278.
Proof. vm_refl. Qed.
Lemma D_31278 : decode_any W_31278 = Some (OpImm ALU_ADD 13 14 256, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3127c : bv 32 := 0xffc67713.
Lemma F_3127c : fetch_word Ubsan.M.loaded_segments (0x317b8 : word) = Some W_3127c.
Proof. vm_refl. Qed.
Lemma D_3127c : decode_any W_3127c = Some (OpImm ALU_AND 14 12 4092, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_31280 : bv 32 := 0x02d83633.
Lemma F_31280 : fetch_word Ubsan.M.loaded_segments (0x317bc : word) = Some W_31280.
Proof. vm_refl. Qed.
Lemma D_31280 : decode_any W_31280 = Some (Mul M_MULHU 12 16 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_31284 : bv 32 := 0x00c5a023.
Lemma F_31284 : fetch_word Ubsan.M.loaded_segments (0x317c0 : word) = Some W_31284.
Proof. vm_refl. Qed.
Lemma D_31284 : decode_any W_31284 = Some (Store SZ4 11 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_31288 : bv 32 := 0x00e586b3.
Lemma F_31288 : fetch_word Ubsan.M.loaded_segments (0x317c4 : word) = Some W_31288.
Proof. vm_refl. Qed.
Lemma D_31288 : decode_any W_31288 = Some (Op ALU_ADD 13 11 14, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3128c : bv 32 := 0xfec6ae23.
Lemma F_3128c : fetch_word Ubsan.M.loaded_segments (0x317c8 : word) = Some W_3128c.
Proof. vm_refl. Qed.
Lemma D_3128c : decode_any W_3128c = Some (Store SZ4 13 12 4092, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_31290 : bv 32 := 0x08f76063.
Lemma F_31290 : fetch_word Ubsan.M.loaded_segments (0x317cc : word) = Some W_31290.
Proof. vm_refl. Qed.
Lemma D_31290 : decode_any W_31290 = Some (Branch BC_LTU 14 15 128, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_31294 : bv 32 := 0x00c5a223.
Lemma F_31294 : fetch_word Ubsan.M.loaded_segments (0x317d0 : word) = Some W_31294.
Proof. vm_refl. Qed.
Lemma D_31294 : decode_any W_31294 = Some (Store SZ4 11 12 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_31298 : bv 32 := 0x00c5a423.
Lemma F_31298 : fetch_word Ubsan.M.loaded_segments (0x317d4 : word) = Some W_31298.
Proof. vm_refl. Qed.
Lemma D_31298 : decode_any W_31298 = Some (Store SZ4 11 12 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3129c : bv 32 := 0x01900793.
Lemma F_3129c : fetch_word Ubsan.M.loaded_segments (0x317d8 : word) = Some W_3129c.
Proof. vm_refl. Qed.
Lemma D_3129c : decode_any W_3129c = Some (OpImm ALU_ADD 15 0 25, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_312a0 : bv 32 := 0xfec6aa23.
Lemma F_312a0 : fetch_word Ubsan.M.loaded_segments (0x317dc : word) = Some W_312a0.
Proof. vm_refl. Qed.
Lemma D_312a0 : decode_any W_312a0 = Some (Store SZ4 13 12 4084, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_312a4 : bv 32 := 0xfec6ac23.
Lemma F_312a4 : fetch_word Ubsan.M.loaded_segments (0x317e0 : word) = Some W_312a4.
Proof. vm_refl. Qed.
Lemma D_312a4 : decode_any W_312a4 = Some (Store SZ4 13 12 4088, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_312a8 : bv 32 := 0x06f76463.
Lemma F_312a8 : fetch_word Ubsan.M.loaded_segments (0x317e4 : word) = Some W_312a8.
Proof. vm_refl. Qed.
Lemma D_312a8 : decode_any W_312a8 = Some (Branch BC_LTU 14 15 104, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_312ac : bv 32 := 0x00c5a623.
Lemma F_312ac : fetch_word Ubsan.M.loaded_segments (0x317e8 : word) = Some W_312ac.
Proof. vm_refl. Qed.
Lemma D_312ac : decode_any W_312ac = Some (Store SZ4 11 12 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_312b0 : bv 32 := 0x00c5a823.
Lemma F_312b0 : fetch_word Ubsan.M.loaded_segments (0x317ec : word) = Some W_312b0.
Proof. vm_refl. Qed.
Lemma D_312b0 : decode_any W_312b0 = Some (Store SZ4 11 12 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_312b4 : bv 32 := 0x00c5aa23.
Lemma F_312b4 : fetch_word Ubsan.M.loaded_segments (0x317f0 : word) = Some W_312b4.
Proof. vm_refl. Qed.
Lemma D_312b4 : decode_any W_312b4 = Some (Store SZ4 11 12 20, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_312b8 : bv 32 := 0x00c5ac23.
Lemma F_312b8 : fetch_word Ubsan.M.loaded_segments (0x317f4 : word) = Some W_312b8.
Proof. vm_refl. Qed.
Lemma D_312b8 : decode_any W_312b8 = Some (Store SZ4 11 12 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_312bc : bv 32 := 0x0045f793.
Lemma F_312bc : fetch_word Ubsan.M.loaded_segments (0x317f8 : word) = Some W_312bc.
Proof. vm_refl. Qed.
Lemma D_312bc : decode_any W_312bc = Some (OpImm ALU_AND 15 11 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_312c0 : bv 32 := 0x02000813.
Lemma F_312c0 : fetch_word Ubsan.M.loaded_segments (0x317fc : word) = Some W_312c0.
Proof. vm_refl. Qed.
Lemma D_312c0 : decode_any W_312c0 = Some (OpImm ALU_ADD 16 0 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_312c4 : bv 32 := 0x01878793.
Lemma F_312c4 : fetch_word Ubsan.M.loaded_segments (0x31800 : word) = Some W_312c4.
Proof. vm_refl. Qed.
Lemma D_312c4 : decode_any W_312c4 = Some (OpImm ALU_ADD 15 15 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_312c8 : bv 32 := 0x40f70733.
Lemma F_312c8 : fetch_word Ubsan.M.loaded_segments (0x31804 : word) = Some W_312c8.
Proof. vm_refl. Qed.
Lemma D_312c8 : decode_any W_312c8 = Some (Op ALU_SUB 14 14 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_312cc : bv 32 := 0xfec6a223.
Lemma F_312cc : fetch_word Ubsan.M.loaded_segments (0x31808 : word) = Some W_312cc.
Proof. vm_refl. Qed.
Lemma D_312cc : decode_any W_312cc = Some (Store SZ4 13 12 4068, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_312d0 : bv 32 := 0xfec6a423.
Lemma F_312d0 : fetch_word Ubsan.M.loaded_segments (0x3180c : word) = Some W_312d0.
Proof. vm_refl. Qed.
Lemma D_312d0 : decode_any W_312d0 = Some (Store SZ4 13 12 4072, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_312d4 : bv 32 := 0xfec6a623.
Lemma F_312d4 : fetch_word Ubsan.M.loaded_segments (0x31810 : word) = Some W_312d4.
Proof. vm_refl. Qed.
Lemma D_312d4 : decode_any W_312d4 = Some (Store SZ4 13 12 4076, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_312d8 : bv 32 := 0xfec6a823.
Lemma F_312d8 : fetch_word Ubsan.M.loaded_segments (0x31814 : word) = Some W_312d8.
Proof. vm_refl. Qed.
Lemma D_312d8 : decode_any W_312d8 = Some (Store SZ4 13 12 4080, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_312dc : bv 32 := 0x03076a63.
Lemma F_312dc : fetch_word Ubsan.M.loaded_segments (0x31818 : word) = Some W_312dc.
Proof. vm_refl. Qed.
Lemma D_312dc : decode_any W_312dc = Some (Branch BC_LTU 14 16 52, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_312e0 : bv 32 := 0x02061613.
Lemma F_312e0 : fetch_word Ubsan.M.loaded_segments (0x3181c : word) = Some W_312e0.
Proof. vm_refl. Qed.
Lemma D_312e0 : decode_any W_312e0 = Some (ShiftImm ALU_SLL 12 12 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_312e4 : bv 32 := 0x00f585b3.
Lemma F_312e4 : fetch_word Ubsan.M.loaded_segments (0x31820 : word) = Some W_312e4.
Proof. vm_refl. Qed.
Lemma D_312e4 : decode_any W_312e4 = Some (Op ALU_ADD 11 11 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_312e8 : bv 32 := 0x02065693.
Lemma F_312e8 : fetch_word Ubsan.M.loaded_segments (0x31824 : word) = Some W_312e8.
Proof. vm_refl. Qed.
Lemma D_312e8 : decode_any W_312e8 = Some (ShiftImm ALU_SRL 13 12 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_312ec : bv 32 := 0x00d66633.
Lemma F_312ec : fetch_word Ubsan.M.loaded_segments (0x31828 : word) = Some W_312ec.
Proof. vm_refl. Qed.
Lemma D_312ec : decode_any W_312ec = Some (Op ALU_OR 12 12 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_312f0 : bv 32 := 0x01f00693.
Lemma F_312f0 : fetch_word Ubsan.M.loaded_segments (0x3182c : word) = Some W_312f0.
Proof. vm_refl. Qed.
Lemma D_312f0 : decode_any W_312f0 = Some (OpImm ALU_ADD 13 0 31, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_312f4 : bv 32 := 0x00c5b023.
Lemma F_312f4 : fetch_word Ubsan.M.loaded_segments (0x31830 : word) = Some W_312f4.
Proof. vm_refl. Qed.
Lemma D_312f4 : decode_any W_312f4 = Some (Store SZ8 11 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_312f8 : bv 32 := 0x00c5b423.
Lemma F_312f8 : fetch_word Ubsan.M.loaded_segments (0x31834 : word) = Some W_312f8.
Proof. vm_refl. Qed.
Lemma D_312f8 : decode_any W_312f8 = Some (Store SZ8 11 12 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_312fc : bv 32 := 0x00c5b823.
Lemma F_312fc : fetch_word Ubsan.M.loaded_segments (0x31838 : word) = Some W_312fc.
Proof. vm_refl. Qed.
Lemma D_312fc : decode_any W_312fc = Some (Store SZ8 11 12 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_31300 : bv 32 := 0x00c5bc23.
Lemma F_31300 : fetch_word Ubsan.M.loaded_segments (0x3183c : word) = Some W_31300.
Proof. vm_refl. Qed.
Lemma D_31300 : decode_any W_31300 = Some (Store SZ8 11 12 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_31304 : bv 32 := 0xfe070713.
Lemma F_31304 : fetch_word Ubsan.M.loaded_segments (0x31840 : word) = Some W_31304.
Proof. vm_refl. Qed.
Lemma D_31304 : decode_any W_31304 = Some (OpImm ALU_ADD 14 14 4064, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_31308 : bv 32 := 0x02058593.
Lemma F_31308 : fetch_word Ubsan.M.loaded_segments (0x31844 : word) = Some W_31308.
Proof. vm_refl. Qed.
Lemma D_31308 : decode_any W_31308 = Some (OpImm ALU_ADD 11 11 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3130c : bv 32 := 0xfee6e4e3.
Lemma F_3130c : fetch_word Ubsan.M.loaded_segments (0x31848 : word) = Some W_3130c.
Proof. vm_refl. Qed.
Lemma D_3130c : decode_any W_3130c = Some (Branch BC_LTU 13 14 8168, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_31310 : bv 32 := 0x00008067.
Lemma F_31310 : fetch_word Ubsan.M.loaded_segments (0x3184c : word) = Some W_31310.
Proof. vm_refl. Qed.
Lemma D_31310 : decode_any W_31310 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.
