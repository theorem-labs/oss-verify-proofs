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
From OSSVerify.varnish.esi_parse_fuzzer.images Require Import Asan.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.

(* [comment removed for export] *)
Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

(* [comment removed for export] *)
Definition W_a25c8 : bv 32 := 0x0e060a63.
Lemma F_a25c8 : fetch_word Asan.M.loaded_segments (0xa25c8 : word) = Some W_a25c8.
Proof. vm_refl. Qed.
Lemma D_a25c8 : decode_any W_a25c8 = Some (Branch BC_EQ 12 0 244, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a25cc : bv 32 := 0x00b50023.
Lemma F_a25cc : fetch_word Asan.M.loaded_segments (0xa25cc : word) = Some W_a25cc.
Proof. vm_refl. Qed.
Lemma D_a25cc : decode_any W_a25cc = Some (Store SZ1 10 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a25d0 : bv 32 := 0x00c506b3.
Lemma F_a25d0 : fetch_word Asan.M.loaded_segments (0xa25d0 : word) = Some W_a25d0.
Proof. vm_refl. Qed.
Lemma D_a25d0 : decode_any W_a25d0 = Some (Op ALU_ADD 13 10 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a25d4 : bv 32 := 0x00300713.
Lemma F_a25d4 : fetch_word Asan.M.loaded_segments (0xa25d4 : word) = Some W_a25d4.
Proof. vm_refl. Qed.
Lemma D_a25d4 : decode_any W_a25d4 = Some (OpImm ALU_ADD 14 0 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a25d8 : bv 32 := 0xfeb68fa3.
Lemma F_a25d8 : fetch_word Asan.M.loaded_segments (0xa25d8 : word) = Some W_a25d8.
Proof. vm_refl. Qed.
Lemma D_a25d8 : decode_any W_a25d8 = Some (Store SZ1 13 11 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a25dc : bv 32 := 0x0ee66063.
Lemma F_a25dc : fetch_word Asan.M.loaded_segments (0xa25dc : word) = Some W_a25dc.
Proof. vm_refl. Qed.
Lemma D_a25dc : decode_any W_a25dc = Some (Branch BC_LTU 12 14 224, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a25e0 : bv 32 := 0x00b500a3.
Lemma F_a25e0 : fetch_word Asan.M.loaded_segments (0xa25e0 : word) = Some W_a25e0.
Proof. vm_refl. Qed.
Lemma D_a25e0 : decode_any W_a25e0 = Some (Store SZ1 10 11 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a25e4 : bv 32 := 0x00b50123.
Lemma F_a25e4 : fetch_word Asan.M.loaded_segments (0xa25e4 : word) = Some W_a25e4.
Proof. vm_refl. Qed.
Lemma D_a25e4 : decode_any W_a25e4 = Some (Store SZ1 10 11 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a25e8 : bv 32 := 0x00700713.
Lemma F_a25e8 : fetch_word Asan.M.loaded_segments (0xa25e8 : word) = Some W_a25e8.
Proof. vm_refl. Qed.
Lemma D_a25e8 : decode_any W_a25e8 = Some (OpImm ALU_ADD 14 0 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a25ec : bv 32 := 0xfeb68ea3.
Lemma F_a25ec : fetch_word Asan.M.loaded_segments (0xa25ec : word) = Some W_a25ec.
Proof. vm_refl. Qed.
Lemma D_a25ec : decode_any W_a25ec = Some (Store SZ1 13 11 4093, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a25f0 : bv 32 := 0xfeb68f23.
Lemma F_a25f0 : fetch_word Asan.M.loaded_segments (0xa25f0 : word) = Some W_a25f0.
Proof. vm_refl. Qed.
Lemma D_a25f0 : decode_any W_a25f0 = Some (Store SZ1 13 11 4094, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a25f4 : bv 32 := 0x0ce66463.
Lemma F_a25f4 : fetch_word Asan.M.loaded_segments (0xa25f4 : word) = Some W_a25f4.
Proof. vm_refl. Qed.
Lemma D_a25f4 : decode_any W_a25f4 = Some (Branch BC_LTU 12 14 200, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a25f8 : bv 32 := 0x00b501a3.
Lemma F_a25f8 : fetch_word Asan.M.loaded_segments (0xa25f8 : word) = Some W_a25f8.
Proof. vm_refl. Qed.
Lemma D_a25f8 : decode_any W_a25f8 = Some (Store SZ1 10 11 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a25fc : bv 32 := 0x00900793.
Lemma F_a25fc : fetch_word Asan.M.loaded_segments (0xa25fc : word) = Some W_a25fc.
Proof. vm_refl. Qed.
Lemma D_a25fc : decode_any W_a25fc = Some (OpImm ALU_ADD 15 0 9, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a2600 : bv 32 := 0xfeb68e23.
Lemma F_a2600 : fetch_word Asan.M.loaded_segments (0xa2600 : word) = Some W_a2600.
Proof. vm_refl. Qed.
Lemma D_a2600 : decode_any W_a2600 = Some (Store SZ1 13 11 4092, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a2604 : bv 32 := 0x0af66c63.
Lemma F_a2604 : fetch_word Asan.M.loaded_segments (0xa2604 : word) = Some W_a2604.
Proof. vm_refl. Qed.
Lemma D_a2604 : decode_any W_a2604 = Some (Branch BC_LTU 12 15 184, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a2608 : bv 32 := 0x40a006bb.
Lemma F_a2608 : fetch_word Asan.M.loaded_segments (0xa2608 : word) = Some W_a2608.
Proof. vm_refl. Qed.
Lemma D_a2608 : decode_any W_a2608 = Some (Op32 ALU_SUB 13 0 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a260c : bv 32 := 0x03859813.
Lemma F_a260c : fetch_word Asan.M.loaded_segments (0xa260c : word) = Some W_a260c.
Proof. vm_refl. Qed.
Lemma D_a260c : decode_any W_a260c = Some (ShiftImm ALU_SLL 16 11 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a2610 : bv 32 := 0x101015b7.
Lemma F_a2610 : fetch_word Asan.M.loaded_segments (0xa2610 : word) = Some W_a2610.
Proof. vm_refl. Qed.
Lemma D_a2610 : decode_any W_a2610 = Some (Lui 11 65793, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a2614 : bv 32 := 0x0036f693.
Lemma F_a2614 : fetch_word Asan.M.loaded_segments (0xa2614 : word) = Some W_a2614.
Proof. vm_refl. Qed.
Lemma D_a2614 : decode_any W_a2614 = Some (OpImm ALU_AND 13 13 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a2618 : bv 32 := 0x00459713.
Lemma F_a2618 : fetch_word Asan.M.loaded_segments (0xa2618 : word) = Some W_a2618.
Proof. vm_refl. Qed.
Lemma D_a2618 : decode_any W_a2618 = Some (ShiftImm ALU_SLL 14 11 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a261c : bv 32 := 0x40d60633.
Lemma F_a261c : fetch_word Asan.M.loaded_segments (0xa261c : word) = Some W_a261c.
Proof. vm_refl. Qed.
Lemma D_a261c : decode_any W_a261c = Some (Op ALU_SUB 12 12 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a2620 : bv 32 := 0x00d505b3.
Lemma F_a2620 : fetch_word Asan.M.loaded_segments (0xa2620 : word) = Some W_a2620.
Proof. vm_refl. Qed.
Lemma D_a2620 : decode_any W_a2620 = Some (Op ALU_ADD 11 10 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a2624 : bv 32 := 0x10070693.
Lemma F_a2624 : fetch_word Asan.M.loaded_segments (0xa2624 : word) = Some W_a2624.
Proof. vm_refl. Qed.
Lemma D_a2624 : decode_any W_a2624 = Some (OpImm ALU_ADD 13 14 256, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a2628 : bv 32 := 0xffc67713.
Lemma F_a2628 : fetch_word Asan.M.loaded_segments (0xa2628 : word) = Some W_a2628.
Proof. vm_refl. Qed.
Lemma D_a2628 : decode_any W_a2628 = Some (OpImm ALU_AND 14 12 4092, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a262c : bv 32 := 0x02d83633.
Lemma F_a262c : fetch_word Asan.M.loaded_segments (0xa262c : word) = Some W_a262c.
Proof. vm_refl. Qed.
Lemma D_a262c : decode_any W_a262c = Some (Mul M_MULHU 12 16 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a2630 : bv 32 := 0x00c5a023.
Lemma F_a2630 : fetch_word Asan.M.loaded_segments (0xa2630 : word) = Some W_a2630.
Proof. vm_refl. Qed.
Lemma D_a2630 : decode_any W_a2630 = Some (Store SZ4 11 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a2634 : bv 32 := 0x00e586b3.
Lemma F_a2634 : fetch_word Asan.M.loaded_segments (0xa2634 : word) = Some W_a2634.
Proof. vm_refl. Qed.
Lemma D_a2634 : decode_any W_a2634 = Some (Op ALU_ADD 13 11 14, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a2638 : bv 32 := 0xfec6ae23.
Lemma F_a2638 : fetch_word Asan.M.loaded_segments (0xa2638 : word) = Some W_a2638.
Proof. vm_refl. Qed.
Lemma D_a2638 : decode_any W_a2638 = Some (Store SZ4 13 12 4092, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a263c : bv 32 := 0x08f76063.
Lemma F_a263c : fetch_word Asan.M.loaded_segments (0xa263c : word) = Some W_a263c.
Proof. vm_refl. Qed.
Lemma D_a263c : decode_any W_a263c = Some (Branch BC_LTU 14 15 128, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a2640 : bv 32 := 0x00c5a223.
Lemma F_a2640 : fetch_word Asan.M.loaded_segments (0xa2640 : word) = Some W_a2640.
Proof. vm_refl. Qed.
Lemma D_a2640 : decode_any W_a2640 = Some (Store SZ4 11 12 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a2644 : bv 32 := 0x00c5a423.
Lemma F_a2644 : fetch_word Asan.M.loaded_segments (0xa2644 : word) = Some W_a2644.
Proof. vm_refl. Qed.
Lemma D_a2644 : decode_any W_a2644 = Some (Store SZ4 11 12 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a2648 : bv 32 := 0x01900793.
Lemma F_a2648 : fetch_word Asan.M.loaded_segments (0xa2648 : word) = Some W_a2648.
Proof. vm_refl. Qed.
Lemma D_a2648 : decode_any W_a2648 = Some (OpImm ALU_ADD 15 0 25, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a264c : bv 32 := 0xfec6aa23.
Lemma F_a264c : fetch_word Asan.M.loaded_segments (0xa264c : word) = Some W_a264c.
Proof. vm_refl. Qed.
Lemma D_a264c : decode_any W_a264c = Some (Store SZ4 13 12 4084, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a2650 : bv 32 := 0xfec6ac23.
Lemma F_a2650 : fetch_word Asan.M.loaded_segments (0xa2650 : word) = Some W_a2650.
Proof. vm_refl. Qed.
Lemma D_a2650 : decode_any W_a2650 = Some (Store SZ4 13 12 4088, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a2654 : bv 32 := 0x06f76463.
Lemma F_a2654 : fetch_word Asan.M.loaded_segments (0xa2654 : word) = Some W_a2654.
Proof. vm_refl. Qed.
Lemma D_a2654 : decode_any W_a2654 = Some (Branch BC_LTU 14 15 104, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a2658 : bv 32 := 0x00c5a623.
Lemma F_a2658 : fetch_word Asan.M.loaded_segments (0xa2658 : word) = Some W_a2658.
Proof. vm_refl. Qed.
Lemma D_a2658 : decode_any W_a2658 = Some (Store SZ4 11 12 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a265c : bv 32 := 0x00c5a823.
Lemma F_a265c : fetch_word Asan.M.loaded_segments (0xa265c : word) = Some W_a265c.
Proof. vm_refl. Qed.
Lemma D_a265c : decode_any W_a265c = Some (Store SZ4 11 12 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a2660 : bv 32 := 0x00c5aa23.
Lemma F_a2660 : fetch_word Asan.M.loaded_segments (0xa2660 : word) = Some W_a2660.
Proof. vm_refl. Qed.
Lemma D_a2660 : decode_any W_a2660 = Some (Store SZ4 11 12 20, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a2664 : bv 32 := 0x00c5ac23.
Lemma F_a2664 : fetch_word Asan.M.loaded_segments (0xa2664 : word) = Some W_a2664.
Proof. vm_refl. Qed.
Lemma D_a2664 : decode_any W_a2664 = Some (Store SZ4 11 12 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a2668 : bv 32 := 0x0045f793.
Lemma F_a2668 : fetch_word Asan.M.loaded_segments (0xa2668 : word) = Some W_a2668.
Proof. vm_refl. Qed.
Lemma D_a2668 : decode_any W_a2668 = Some (OpImm ALU_AND 15 11 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a266c : bv 32 := 0x02000813.
Lemma F_a266c : fetch_word Asan.M.loaded_segments (0xa266c : word) = Some W_a266c.
Proof. vm_refl. Qed.
Lemma D_a266c : decode_any W_a266c = Some (OpImm ALU_ADD 16 0 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a2670 : bv 32 := 0x01878793.
Lemma F_a2670 : fetch_word Asan.M.loaded_segments (0xa2670 : word) = Some W_a2670.
Proof. vm_refl. Qed.
Lemma D_a2670 : decode_any W_a2670 = Some (OpImm ALU_ADD 15 15 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a2674 : bv 32 := 0x40f70733.
Lemma F_a2674 : fetch_word Asan.M.loaded_segments (0xa2674 : word) = Some W_a2674.
Proof. vm_refl. Qed.
Lemma D_a2674 : decode_any W_a2674 = Some (Op ALU_SUB 14 14 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a2678 : bv 32 := 0xfec6a223.
Lemma F_a2678 : fetch_word Asan.M.loaded_segments (0xa2678 : word) = Some W_a2678.
Proof. vm_refl. Qed.
Lemma D_a2678 : decode_any W_a2678 = Some (Store SZ4 13 12 4068, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a267c : bv 32 := 0xfec6a423.
Lemma F_a267c : fetch_word Asan.M.loaded_segments (0xa267c : word) = Some W_a267c.
Proof. vm_refl. Qed.
Lemma D_a267c : decode_any W_a267c = Some (Store SZ4 13 12 4072, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a2680 : bv 32 := 0xfec6a623.
Lemma F_a2680 : fetch_word Asan.M.loaded_segments (0xa2680 : word) = Some W_a2680.
Proof. vm_refl. Qed.
Lemma D_a2680 : decode_any W_a2680 = Some (Store SZ4 13 12 4076, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a2684 : bv 32 := 0xfec6a823.
Lemma F_a2684 : fetch_word Asan.M.loaded_segments (0xa2684 : word) = Some W_a2684.
Proof. vm_refl. Qed.
Lemma D_a2684 : decode_any W_a2684 = Some (Store SZ4 13 12 4080, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a2688 : bv 32 := 0x03076a63.
Lemma F_a2688 : fetch_word Asan.M.loaded_segments (0xa2688 : word) = Some W_a2688.
Proof. vm_refl. Qed.
Lemma D_a2688 : decode_any W_a2688 = Some (Branch BC_LTU 14 16 52, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a268c : bv 32 := 0x02061613.
Lemma F_a268c : fetch_word Asan.M.loaded_segments (0xa268c : word) = Some W_a268c.
Proof. vm_refl. Qed.
Lemma D_a268c : decode_any W_a268c = Some (ShiftImm ALU_SLL 12 12 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a2690 : bv 32 := 0x00f585b3.
Lemma F_a2690 : fetch_word Asan.M.loaded_segments (0xa2690 : word) = Some W_a2690.
Proof. vm_refl. Qed.
Lemma D_a2690 : decode_any W_a2690 = Some (Op ALU_ADD 11 11 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a2694 : bv 32 := 0x02065693.
Lemma F_a2694 : fetch_word Asan.M.loaded_segments (0xa2694 : word) = Some W_a2694.
Proof. vm_refl. Qed.
Lemma D_a2694 : decode_any W_a2694 = Some (ShiftImm ALU_SRL 13 12 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a2698 : bv 32 := 0x00d66633.
Lemma F_a2698 : fetch_word Asan.M.loaded_segments (0xa2698 : word) = Some W_a2698.
Proof. vm_refl. Qed.
Lemma D_a2698 : decode_any W_a2698 = Some (Op ALU_OR 12 12 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a269c : bv 32 := 0x01f00693.
Lemma F_a269c : fetch_word Asan.M.loaded_segments (0xa269c : word) = Some W_a269c.
Proof. vm_refl. Qed.
Lemma D_a269c : decode_any W_a269c = Some (OpImm ALU_ADD 13 0 31, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a26a0 : bv 32 := 0x00c5b023.
Lemma F_a26a0 : fetch_word Asan.M.loaded_segments (0xa26a0 : word) = Some W_a26a0.
Proof. vm_refl. Qed.
Lemma D_a26a0 : decode_any W_a26a0 = Some (Store SZ8 11 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a26a4 : bv 32 := 0x00c5b423.
Lemma F_a26a4 : fetch_word Asan.M.loaded_segments (0xa26a4 : word) = Some W_a26a4.
Proof. vm_refl. Qed.
Lemma D_a26a4 : decode_any W_a26a4 = Some (Store SZ8 11 12 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a26a8 : bv 32 := 0x00c5b823.
Lemma F_a26a8 : fetch_word Asan.M.loaded_segments (0xa26a8 : word) = Some W_a26a8.
Proof. vm_refl. Qed.
Lemma D_a26a8 : decode_any W_a26a8 = Some (Store SZ8 11 12 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a26ac : bv 32 := 0x00c5bc23.
Lemma F_a26ac : fetch_word Asan.M.loaded_segments (0xa26ac : word) = Some W_a26ac.
Proof. vm_refl. Qed.
Lemma D_a26ac : decode_any W_a26ac = Some (Store SZ8 11 12 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a26b0 : bv 32 := 0xfe070713.
Lemma F_a26b0 : fetch_word Asan.M.loaded_segments (0xa26b0 : word) = Some W_a26b0.
Proof. vm_refl. Qed.
Lemma D_a26b0 : decode_any W_a26b0 = Some (OpImm ALU_ADD 14 14 4064, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a26b4 : bv 32 := 0x02058593.
Lemma F_a26b4 : fetch_word Asan.M.loaded_segments (0xa26b4 : word) = Some W_a26b4.
Proof. vm_refl. Qed.
Lemma D_a26b4 : decode_any W_a26b4 = Some (OpImm ALU_ADD 11 11 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a26b8 : bv 32 := 0xfee6e4e3.
Lemma F_a26b8 : fetch_word Asan.M.loaded_segments (0xa26b8 : word) = Some W_a26b8.
Proof. vm_refl. Qed.
Lemma D_a26b8 : decode_any W_a26b8 = Some (Branch BC_LTU 13 14 8168, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a26bc : bv 32 := 0x00008067.
Lemma F_a26bc : fetch_word Asan.M.loaded_segments (0xa26bc : word) = Some W_a26bc.
Proof. vm_refl. Qed.
Lemma D_a26bc : decode_any W_a26bc = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Abbreviation MSEGS := Asan.M.loaded_segments.
Definition ms_base : Z := 0xa25c8%Z.
Definition Fo_000 := F_a25c8.
Definition Do_000 := D_a25c8.
Definition Fo_004 := F_a25cc.
Definition Do_004 := D_a25cc.
Definition Fo_008 := F_a25d0.
Definition Do_008 := D_a25d0.
Definition Fo_00c := F_a25d4.
Definition Do_00c := D_a25d4.
Definition Fo_010 := F_a25d8.
Definition Do_010 := D_a25d8.
Definition Fo_014 := F_a25dc.
Definition Do_014 := D_a25dc.
Definition Fo_018 := F_a25e0.
Definition Do_018 := D_a25e0.
Definition Fo_01c := F_a25e4.
Definition Do_01c := D_a25e4.
Definition Fo_020 := F_a25e8.
Definition Do_020 := D_a25e8.
Definition Fo_024 := F_a25ec.
Definition Do_024 := D_a25ec.
Definition Fo_028 := F_a25f0.
Definition Do_028 := D_a25f0.
Definition Fo_02c := F_a25f4.
Definition Do_02c := D_a25f4.
Definition Fo_030 := F_a25f8.
Definition Do_030 := D_a25f8.
Definition Fo_034 := F_a25fc.
Definition Do_034 := D_a25fc.
Definition Fo_038 := F_a2600.
Definition Do_038 := D_a2600.
Definition Fo_03c := F_a2604.
Definition Do_03c := D_a2604.
Definition Fo_040 := F_a2608.
Definition Do_040 := D_a2608.
Definition Fo_044 := F_a260c.
Definition Do_044 := D_a260c.
Definition Fo_048 := F_a2610.
Definition Do_048 := D_a2610.
Definition Fo_04c := F_a2614.
Definition Do_04c := D_a2614.
Definition Fo_050 := F_a2618.
Definition Do_050 := D_a2618.
Definition Fo_054 := F_a261c.
Definition Do_054 := D_a261c.
Definition Fo_058 := F_a2620.
Definition Do_058 := D_a2620.
Definition Fo_05c := F_a2624.
Definition Do_05c := D_a2624.
Definition Fo_060 := F_a2628.
Definition Do_060 := D_a2628.
Definition Fo_064 := F_a262c.
Definition Do_064 := D_a262c.
Definition Fo_068 := F_a2630.
Definition Do_068 := D_a2630.
Definition Fo_06c := F_a2634.
Definition Do_06c := D_a2634.
Definition Fo_070 := F_a2638.
Definition Do_070 := D_a2638.
Definition Fo_074 := F_a263c.
Definition Do_074 := D_a263c.
Definition Fo_078 := F_a2640.
Definition Do_078 := D_a2640.
Definition Fo_07c := F_a2644.
Definition Do_07c := D_a2644.
Definition Fo_080 := F_a2648.
Definition Do_080 := D_a2648.
Definition Fo_084 := F_a264c.
Definition Do_084 := D_a264c.
Definition Fo_088 := F_a2650.
Definition Do_088 := D_a2650.
Definition Fo_08c := F_a2654.
Definition Do_08c := D_a2654.
Definition Fo_090 := F_a2658.
Definition Do_090 := D_a2658.
Definition Fo_094 := F_a265c.
Definition Do_094 := D_a265c.
Definition Fo_098 := F_a2660.
Definition Do_098 := D_a2660.
Definition Fo_09c := F_a2664.
Definition Do_09c := D_a2664.
Definition Fo_0a0 := F_a2668.
Definition Do_0a0 := D_a2668.
Definition Fo_0a4 := F_a266c.
Definition Do_0a4 := D_a266c.
Definition Fo_0a8 := F_a2670.
Definition Do_0a8 := D_a2670.
Definition Fo_0ac := F_a2674.
Definition Do_0ac := D_a2674.
Definition Fo_0b0 := F_a2678.
Definition Do_0b0 := D_a2678.
Definition Fo_0b4 := F_a267c.
Definition Do_0b4 := D_a267c.
Definition Fo_0b8 := F_a2680.
Definition Do_0b8 := D_a2680.
Definition Fo_0bc := F_a2684.
Definition Do_0bc := D_a2684.
Definition Fo_0c0 := F_a2688.
Definition Do_0c0 := D_a2688.
Definition Fo_0c4 := F_a268c.
Definition Do_0c4 := D_a268c.
Definition Fo_0c8 := F_a2690.
Definition Do_0c8 := D_a2690.
Definition Fo_0cc := F_a2694.
Definition Do_0cc := D_a2694.
Definition Fo_0d0 := F_a2698.
Definition Do_0d0 := D_a2698.
Definition Fo_0d4 := F_a269c.
Definition Do_0d4 := D_a269c.
Definition Fo_0d8 := F_a26a0.
Definition Do_0d8 := D_a26a0.
Definition Fo_0dc := F_a26a4.
Definition Do_0dc := D_a26a4.
Definition Fo_0e0 := F_a26a8.
Definition Do_0e0 := D_a26a8.
Definition Fo_0e4 := F_a26ac.
Definition Do_0e4 := D_a26ac.
Definition Fo_0e8 := F_a26b0.
Definition Do_0e8 := D_a26b0.
Definition Fo_0ec := F_a26b4.
Definition Do_0ec := D_a26b4.
Definition Fo_0f0 := F_a26b8.
Definition Do_0f0 := D_a26b8.
Definition Fo_0f4 := F_a26bc.
Definition Do_0f4 := D_a26bc.
