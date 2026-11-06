(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.jsoncons.fuzz_json_cursor.images Require Import Asan.
Open Scope bv_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Hint Extern 0 (BvWf _ _) =>
  (lazymatch goal with |- BvWf ?n ?v => is_closed_term n; is_closed_term v end; exact I) : typeclass_instances.
Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

Definition W_92574 : bv 32 := 0x02060063.
Lemma F_92574 : fetch_word Asan.M.loaded_segments (0x925c4 : word) = Some W_92574.
Proof. vm_refl. Qed.
Lemma D_92574 : decode_any W_92574 = Some (Branch BC_EQ 12 0 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_92578 : bv 32 := 0x00c50633.
Lemma F_92578 : fetch_word Asan.M.loaded_segments (0x925c8 : word) = Some W_92578.
Proof. vm_refl. Qed.
Lemma D_92578 : decode_any W_92578 = Some (Op ALU_ADD 12 10 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_9257c : bv 32 := 0x00050693.
Lemma F_9257c : fetch_word Asan.M.loaded_segments (0x925cc : word) = Some W_9257c.
Proof. vm_refl. Qed.
Lemma D_9257c : decode_any W_9257c = Some (OpImm ALU_ADD 13 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_92580 : bv 32 := 0x0005c703.
Lemma F_92580 : fetch_word Asan.M.loaded_segments (0x925d0 : word) = Some W_92580.
Proof. vm_refl. Qed.
Lemma D_92580 : decode_any W_92580 = Some (Load SZ1 false 14 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_92584 : bv 32 := 0x00e68023.
Lemma F_92584 : fetch_word Asan.M.loaded_segments (0x925d4 : word) = Some W_92584.
Proof. vm_refl. Qed.
Lemma D_92584 : decode_any W_92584 = Some (Store SZ1 13 14 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_92588 : bv 32 := 0x00168693.
Lemma F_92588 : fetch_word Asan.M.loaded_segments (0x925d8 : word) = Some W_92588.
Proof. vm_refl. Qed.
Lemma D_92588 : decode_any W_92588 = Some (OpImm ALU_ADD 13 13 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_9258c : bv 32 := 0x00158593.
Lemma F_9258c : fetch_word Asan.M.loaded_segments (0x925dc : word) = Some W_9258c.
Proof. vm_refl. Qed.
Lemma D_9258c : decode_any W_9258c = Some (OpImm ALU_ADD 11 11 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_92590 : bv 32 := 0xfec698e3.
Lemma F_92590 : fetch_word Asan.M.loaded_segments (0x925e0 : word) = Some W_92590.
Proof. vm_refl. Qed.
Lemma D_92590 : decode_any W_92590 = Some (Branch BC_NE 13 12 8176, 4%Z).
Proof. vm_refl. Qed.

Definition W_92594 : bv 32 := 0x00008067.
Lemma F_92594 : fetch_word Asan.M.loaded_segments (0x925e4 : word) = Some W_92594.
Proof. vm_refl. Qed.
Lemma D_92594 : decode_any W_92594 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_92598 : bv 32 := 0x02b57463.
Lemma F_92598 : fetch_word Asan.M.loaded_segments (0x925e8 : word) = Some W_92598.
Proof. vm_refl. Qed.
Lemma D_92598 : decode_any W_92598 = Some (Branch BC_GEU 10 11 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_9259c : bv 32 := 0x04c05863.
Lemma F_9259c : fetch_word Asan.M.loaded_segments (0x925ec : word) = Some W_9259c.
Proof. vm_refl. Qed.
Lemma D_9259c : decode_any W_9259c = Some (Branch BC_GE 0 12 80, 4%Z).
Proof. vm_refl. Qed.

Definition W_925a0 : bv 32 := 0x00c50633.
Lemma F_925a0 : fetch_word Asan.M.loaded_segments (0x925f0 : word) = Some W_925a0.
Proof. vm_refl. Qed.
Lemma D_925a0 : decode_any W_925a0 = Some (Op ALU_ADD 12 10 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_925a4 : bv 32 := 0x00050693.
Lemma F_925a4 : fetch_word Asan.M.loaded_segments (0x925f4 : word) = Some W_925a4.
Proof. vm_refl. Qed.
Lemma D_925a4 : decode_any W_925a4 = Some (OpImm ALU_ADD 13 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_925a8 : bv 32 := 0x0005c703.
Lemma F_925a8 : fetch_word Asan.M.loaded_segments (0x925f8 : word) = Some W_925a8.
Proof. vm_refl. Qed.
Lemma D_925a8 : decode_any W_925a8 = Some (Load SZ1 false 14 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_925ac : bv 32 := 0x00e68023.
Lemma F_925ac : fetch_word Asan.M.loaded_segments (0x925fc : word) = Some W_925ac.
Proof. vm_refl. Qed.
Lemma D_925ac : decode_any W_925ac = Some (Store SZ1 13 14 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_925b0 : bv 32 := 0x00168693.
Lemma F_925b0 : fetch_word Asan.M.loaded_segments (0x92600 : word) = Some W_925b0.
Proof. vm_refl. Qed.
Lemma D_925b0 : decode_any W_925b0 = Some (OpImm ALU_ADD 13 13 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_925b4 : bv 32 := 0x00158593.
Lemma F_925b4 : fetch_word Asan.M.loaded_segments (0x92604 : word) = Some W_925b4.
Proof. vm_refl. Qed.
Lemma D_925b4 : decode_any W_925b4 = Some (OpImm ALU_ADD 11 11 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_925b8 : bv 32 := 0xfec698e3.
Lemma F_925b8 : fetch_word Asan.M.loaded_segments (0x92608 : word) = Some W_925b8.
Proof. vm_refl. Qed.
Lemma D_925b8 : decode_any W_925b8 = Some (Branch BC_NE 13 12 8176, 4%Z).
Proof. vm_refl. Qed.

Definition W_925bc : bv 32 := 0x0300006f.
Lemma F_925bc : fetch_word Asan.M.loaded_segments (0x9260c : word) = Some W_925bc.
Proof. vm_refl. Qed.
Lemma D_925bc : decode_any W_925bc = Some (Jal 0 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_925c0 : bv 32 := 0x02a5f663.
Lemma F_925c0 : fetch_word Asan.M.loaded_segments (0x92610 : word) = Some W_925c0.
Proof. vm_refl. Qed.
Lemma D_925c0 : decode_any W_925c0 = Some (Branch BC_GEU 11 10 44, 4%Z).
Proof. vm_refl. Qed.

Definition W_925c4 : bv 32 := 0x02c05463.
Lemma F_925c4 : fetch_word Asan.M.loaded_segments (0x92614 : word) = Some W_925c4.
Proof. vm_refl. Qed.
Lemma D_925c4 : decode_any W_925c4 = Some (Branch BC_GE 0 12 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_925c8 : bv 32 := 0xfff60693.
Lemma F_925c8 : fetch_word Asan.M.loaded_segments (0x92618 : word) = Some W_925c8.
Proof. vm_refl. Qed.
Lemma D_925c8 : decode_any W_925c8 = Some (OpImm ALU_ADD 13 12 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_925cc : bv 32 := 0x00100613.
Lemma F_925cc : fetch_word Asan.M.loaded_segments (0x9261c : word) = Some W_925cc.
Proof. vm_refl. Qed.
Lemma D_925cc : decode_any W_925cc = Some (OpImm ALU_ADD 12 0 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_925d0 : bv 32 := 0x00d58733.
Lemma F_925d0 : fetch_word Asan.M.loaded_segments (0x92620 : word) = Some W_925d0.
Proof. vm_refl. Qed.
Lemma D_925d0 : decode_any W_925d0 = Some (Op ALU_ADD 14 11 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_925d4 : bv 32 := 0x00074703.
Lemma F_925d4 : fetch_word Asan.M.loaded_segments (0x92624 : word) = Some W_925d4.
Proof. vm_refl. Qed.
Lemma D_925d4 : decode_any W_925d4 = Some (Load SZ1 false 14 14 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_925d8 : bv 32 := 0x00d507b3.
Lemma F_925d8 : fetch_word Asan.M.loaded_segments (0x92628 : word) = Some W_925d8.
Proof. vm_refl. Qed.
Lemma D_925d8 : decode_any W_925d8 = Some (Op ALU_ADD 15 10 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_925dc : bv 32 := 0x00168813.
Lemma F_925dc : fetch_word Asan.M.loaded_segments (0x9262c : word) = Some W_925dc.
Proof. vm_refl. Qed.
Lemma D_925dc : decode_any W_925dc = Some (OpImm ALU_ADD 16 13 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_925e0 : bv 32 := 0xfff68693.
Lemma F_925e0 : fetch_word Asan.M.loaded_segments (0x92630 : word) = Some W_925e0.
Proof. vm_refl. Qed.
Lemma D_925e0 : decode_any W_925e0 = Some (OpImm ALU_ADD 13 13 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_925e4 : bv 32 := 0x00e78023.
Lemma F_925e4 : fetch_word Asan.M.loaded_segments (0x92634 : word) = Some W_925e4.
Proof. vm_refl. Qed.
Lemma D_925e4 : decode_any W_925e4 = Some (Store SZ1 15 14 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_925e8 : bv 32 := 0xff0664e3.
Lemma F_925e8 : fetch_word Asan.M.loaded_segments (0x92638 : word) = Some W_925e8.
Proof. vm_refl. Qed.
Lemma D_925e8 : decode_any W_925e8 = Some (Branch BC_LTU 12 16 8168, 4%Z).
Proof. vm_refl. Qed.

Definition W_925ec : bv 32 := 0x00008067.
Lemma F_925ec : fetch_word Asan.M.loaded_segments (0x9263c : word) = Some W_925ec.
Proof. vm_refl. Qed.
Lemma D_925ec : decode_any W_925ec = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_925f0 : bv 32 := 0x00a666b3.
Lemma F_925f0 : fetch_word Asan.M.loaded_segments (0x92640 : word) = Some W_925f0.
Proof. vm_refl. Qed.
Lemma D_925f0 : decode_any W_925f0 = Some (Op ALU_OR 13 12 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_925f4 : bv 32 := 0x00f6f693.
Lemma F_925f4 : fetch_word Asan.M.loaded_segments (0x92644 : word) = Some W_925f4.
Proof. vm_refl. Qed.
Lemma D_925f4 : decode_any W_925f4 = Some (OpImm ALU_AND 13 13 15, 4%Z).
Proof. vm_refl. Qed.

Definition W_925f8 : bv 32 := 0x02068063.
Lemma F_925f8 : fetch_word Asan.M.loaded_segments (0x92648 : word) = Some W_925f8.
Proof. vm_refl. Qed.
Lemma D_925f8 : decode_any W_925f8 = Some (Branch BC_EQ 13 0 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_925fc : bv 32 := 0x04060863.
Lemma F_925fc : fetch_word Asan.M.loaded_segments (0x9264c : word) = Some W_925fc.
Proof. vm_refl. Qed.
Lemma D_925fc : decode_any W_925fc = Some (Branch BC_EQ 12 0 80, 4%Z).
Proof. vm_refl. Qed.

Definition W_92600 : bv 32 := 0x00c50633.
Lemma F_92600 : fetch_word Asan.M.loaded_segments (0x92650 : word) = Some W_92600.
Proof. vm_refl. Qed.
Lemma D_92600 : decode_any W_92600 = Some (Op ALU_ADD 12 10 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_92604 : bv 32 := 0x00050693.
Lemma F_92604 : fetch_word Asan.M.loaded_segments (0x92654 : word) = Some W_92604.
Proof. vm_refl. Qed.
Lemma D_92604 : decode_any W_92604 = Some (OpImm ALU_ADD 13 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_92608 : bv 32 := 0x00b68023.
Lemma F_92608 : fetch_word Asan.M.loaded_segments (0x92658 : word) = Some W_92608.
Proof. vm_refl. Qed.
Lemma D_92608 : decode_any W_92608 = Some (Store SZ1 13 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_9260c : bv 32 := 0x00168693.
Lemma F_9260c : fetch_word Asan.M.loaded_segments (0x9265c : word) = Some W_9260c.
Proof. vm_refl. Qed.
Lemma D_9260c : decode_any W_9260c = Some (OpImm ALU_ADD 13 13 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_92610 : bv 32 := 0xfec69ce3.
Lemma F_92610 : fetch_word Asan.M.loaded_segments (0x92660 : word) = Some W_92610.
Proof. vm_refl. Qed.
Lemma D_92610 : decode_any W_92610 = Some (Branch BC_NE 13 12 8184, 4%Z).
Proof. vm_refl. Qed.

Definition W_92614 : bv 32 := 0x0380006f.
Lemma F_92614 : fetch_word Asan.M.loaded_segments (0x92664 : word) = Some W_92614.
Proof. vm_refl. Qed.
Lemma D_92614 : decode_any W_92614 = Some (Jal 0 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_92618 : bv 32 := 0x02060a63.
Lemma F_92618 : fetch_word Asan.M.loaded_segments (0x92668 : word) = Some W_92618.
Proof. vm_refl. Qed.
Lemma D_92618 : decode_any W_92618 = Some (Branch BC_EQ 12 0 52, 4%Z).
Proof. vm_refl. Qed.

Definition W_9261c : bv 32 := 0x00c50633.
Lemma F_9261c : fetch_word Asan.M.loaded_segments (0x9266c : word) = Some W_9261c.
Proof. vm_refl. Qed.
Lemma D_9261c : decode_any W_9261c = Some (Op ALU_ADD 12 10 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_92620 : bv 32 := 0x00859693.
Lemma F_92620 : fetch_word Asan.M.loaded_segments (0x92670 : word) = Some W_92620.
Proof. vm_refl. Qed.
Lemma D_92620 : decode_any W_92620 = Some (ShiftImm ALU_SLL 13 11 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_92624 : bv 32 := 0x00b6e5b3.
Lemma F_92624 : fetch_word Asan.M.loaded_segments (0x92674 : word) = Some W_92624.
Proof. vm_refl. Qed.
Lemma D_92624 : decode_any W_92624 = Some (Op ALU_OR 11 13 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_92628 : bv 32 := 0x01059693.
Lemma F_92628 : fetch_word Asan.M.loaded_segments (0x92678 : word) = Some W_92628.
Proof. vm_refl. Qed.
Lemma D_92628 : decode_any W_92628 = Some (ShiftImm ALU_SLL 13 11 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_9262c : bv 32 := 0x00b6e5b3.
Lemma F_9262c : fetch_word Asan.M.loaded_segments (0x9267c : word) = Some W_9262c.
Proof. vm_refl. Qed.
Lemma D_9262c : decode_any W_9262c = Some (Op ALU_OR 11 13 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_92630 : bv 32 := 0x02059693.
Lemma F_92630 : fetch_word Asan.M.loaded_segments (0x92680 : word) = Some W_92630.
Proof. vm_refl. Qed.
Lemma D_92630 : decode_any W_92630 = Some (ShiftImm ALU_SLL 13 11 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_92634 : bv 32 := 0x00b6e5b3.
Lemma F_92634 : fetch_word Asan.M.loaded_segments (0x92684 : word) = Some W_92634.
Proof. vm_refl. Qed.
Lemma D_92634 : decode_any W_92634 = Some (Op ALU_OR 11 13 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_92638 : bv 32 := 0x00050693.
Lemma F_92638 : fetch_word Asan.M.loaded_segments (0x92688 : word) = Some W_92638.
Proof. vm_refl. Qed.
Lemma D_92638 : decode_any W_92638 = Some (OpImm ALU_ADD 13 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_9263c : bv 32 := 0x00b6b023.
Lemma F_9263c : fetch_word Asan.M.loaded_segments (0x9268c : word) = Some W_9263c.
Proof. vm_refl. Qed.
Lemma D_9263c : decode_any W_9263c = Some (Store SZ8 13 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_92640 : bv 32 := 0x00b6b423.
Lemma F_92640 : fetch_word Asan.M.loaded_segments (0x92690 : word) = Some W_92640.
Proof. vm_refl. Qed.
Lemma D_92640 : decode_any W_92640 = Some (Store SZ8 13 11 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_92644 : bv 32 := 0x01068693.
Lemma F_92644 : fetch_word Asan.M.loaded_segments (0x92694 : word) = Some W_92644.
Proof. vm_refl. Qed.
Lemma D_92644 : decode_any W_92644 = Some (OpImm ALU_ADD 13 13 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_92648 : bv 32 := 0xfec6eae3.
Lemma F_92648 : fetch_word Asan.M.loaded_segments (0x92698 : word) = Some W_92648.
Proof. vm_refl. Qed.
Lemma D_92648 : decode_any W_92648 = Some (Branch BC_LTU 13 12 8180, 4%Z).
Proof. vm_refl. Qed.

Definition W_9264c : bv 32 := 0x00008067.
Lemma F_9264c : fetch_word Asan.M.loaded_segments (0x9269c : word) = Some W_9264c.
Proof. vm_refl. Qed.
Lemma D_9264c : decode_any W_9264c = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_92744 : bv 32 := 0x00000593.
Lemma F_92744 : fetch_word Asan.M.loaded_segments (0x92794 : word) = Some W_92744.
Proof. vm_refl. Qed.
Lemma D_92744 : decode_any W_92744 = Some (OpImm ALU_ADD 11 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_92748 : bv 32 := 0x00b50633.
Lemma F_92748 : fetch_word Asan.M.loaded_segments (0x92798 : word) = Some W_92748.
Proof. vm_refl. Qed.
Lemma D_92748 : decode_any W_92748 = Some (Op ALU_ADD 12 10 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_9274c : bv 32 := 0x00064603.
Lemma F_9274c : fetch_word Asan.M.loaded_segments (0x9279c : word) = Some W_9274c.
Proof. vm_refl. Qed.
Lemma D_9274c : decode_any W_9274c = Some (Load SZ1 false 12 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_92750 : bv 32 := 0x00158593.
Lemma F_92750 : fetch_word Asan.M.loaded_segments (0x927a0 : word) = Some W_92750.
Proof. vm_refl. Qed.
Lemma D_92750 : decode_any W_92750 = Some (OpImm ALU_ADD 11 11 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_92754 : bv 32 := 0xfe061ae3.
Lemma F_92754 : fetch_word Asan.M.loaded_segments (0x927a4 : word) = Some W_92754.
Proof. vm_refl. Qed.
Lemma D_92754 : decode_any W_92754 = Some (Branch BC_NE 12 0 8180, 4%Z).
Proof. vm_refl. Qed.

Definition W_92758 : bv 32 := 0xfff58513.
Lemma F_92758 : fetch_word Asan.M.loaded_segments (0x927a8 : word) = Some W_92758.
Proof. vm_refl. Qed.
Lemma D_92758 : decode_any W_92758 = Some (OpImm ALU_ADD 10 11 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_9275c : bv 32 := 0x00008067.
Lemma F_9275c : fetch_word Asan.M.loaded_segments (0x927ac : word) = Some W_9275c.
Proof. vm_refl. Qed.
Lemma D_9275c : decode_any W_9275c = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_92b3c : bv 32 := 0xff010113.
Lemma F_92b3c : fetch_word Asan.M.loaded_segments (0x92b8c : word) = Some W_92b3c.
Proof. vm_refl. Qed.
Lemma D_92b3c : decode_any W_92b3c = Some (OpImm ALU_ADD 2 2 4080, 4%Z).
Proof. vm_refl. Qed.

Definition W_92b40 : bv 32 := 0x00113423.
Lemma F_92b40 : fetch_word Asan.M.loaded_segments (0x92b90 : word) = Some W_92b40.
Proof. vm_refl. Qed.
Lemma D_92b40 : decode_any W_92b40 = Some (Store SZ8 2 1 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_92b44 : bv 32 := 0x00058693.
Lemma F_92b44 : fetch_word Asan.M.loaded_segments (0x92b94 : word) = Some W_92b44.
Proof. vm_refl. Qed.
Lemma D_92b44 : decode_any W_92b44 = Some (OpImm ALU_ADD 13 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_92b48 : bv 32 := 0x00100713.
Lemma F_92b48 : fetch_word Asan.M.loaded_segments (0x92b98 : word) = Some W_92b48.
Proof. vm_refl. Qed.
Lemma D_92b48 : decode_any W_92b48 = Some (OpImm ALU_ADD 14 0 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_92b4c : bv 32 := 0x02871713.
Lemma F_92b4c : fetch_word Asan.M.loaded_segments (0x92b9c : word) = Some W_92b4c.
Proof. vm_refl. Qed.
Lemma D_92b4c : decode_any W_92b4c = Some (ShiftImm ALU_SLL 14 14 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_92b50 : bv 32 := 0x00170593.
Lemma F_92b50 : fetch_word Asan.M.loaded_segments (0x92ba0 : word) = Some W_92b50.
Proof. vm_refl. Qed.
Lemma D_92b50 : decode_any W_92b50 = Some (OpImm ALU_ADD 11 14 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_92b54 : bv 32 := 0x08b6f263.
Lemma F_92b54 : fetch_word Asan.M.loaded_segments (0x92ba4 : word) = Some W_92b54.
Proof. vm_refl. Qed.
Lemma D_92b54 : decode_any W_92b54 = Some (Branch BC_GEU 13 11 132, 4%Z).
Proof. vm_refl. Qed.

Definition W_92b58 : bv 32 := 0x00000593.
Lemma F_92b58 : fetch_word Asan.M.loaded_segments (0x92ba8 : word) = Some W_92b58.
Proof. vm_refl. Qed.
Lemma D_92b58 : decode_any W_92b58 = Some (OpImm ALU_ADD 11 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_92b5c : bv 32 := 0x00d50733.
Lemma F_92b5c : fetch_word Asan.M.loaded_segments (0x92bac : word) = Some W_92b5c.
Proof. vm_refl. Qed.
Lemma D_92b5c : decode_any W_92b5c = Some (Op ALU_ADD 14 10 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_92b60 : bv 32 := 0x00750793.
Lemma F_92b60 : fetch_word Asan.M.loaded_segments (0x92bb0 : word) = Some W_92b60.
Proof. vm_refl. Qed.
Lemma D_92b60 : decode_any W_92b60 = Some (OpImm ALU_ADD 15 10 7, 4%Z).
Proof. vm_refl. Qed.

Definition W_92b64 : bv 32 := 0xff87f793.
Lemma F_92b64 : fetch_word Asan.M.loaded_segments (0x92bb4 : word) = Some W_92b64.
Proof. vm_refl. Qed.
Lemma D_92b64 : decode_any W_92b64 = Some (OpImm ALU_AND 15 15 4088, 4%Z).
Proof. vm_refl. Qed.

Definition W_92b68 : bv 32 := 0xff877613.
Lemma F_92b68 : fetch_word Asan.M.loaded_segments (0x92bb8 : word) = Some W_92b68.
Proof. vm_refl. Qed.
Lemma D_92b68 : decode_any W_92b68 = Some (OpImm ALU_AND 12 14 4088, 4%Z).
Proof. vm_refl. Qed.

Definition W_92b6c : bv 32 := 0x02f57463.
Lemma F_92b6c : fetch_word Asan.M.loaded_segments (0x92bbc : word) = Some W_92b6c.
Proof. vm_refl. Qed.
Lemma D_92b6c : decode_any W_92b6c = Some (Branch BC_GEU 10 15 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_92b70 : bv 32 := 0x02068263.
Lemma F_92b70 : fetch_word Asan.M.loaded_segments (0x92bc0 : word) = Some W_92b70.
Proof. vm_refl. Qed.
Lemma D_92b70 : decode_any W_92b70 = Some (Branch BC_EQ 13 0 36, 4%Z).
Proof. vm_refl. Qed.

Definition W_92b74 : bv 32 := 0x00000593.
Lemma F_92b74 : fetch_word Asan.M.loaded_segments (0x92bc4 : word) = Some W_92b74.
Proof. vm_refl. Qed.
Lemma D_92b74 : decode_any W_92b74 = Some (OpImm ALU_ADD 11 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_92b78 : bv 32 := 0x00150693.
Lemma F_92b78 : fetch_word Asan.M.loaded_segments (0x92bc8 : word) = Some W_92b78.
Proof. vm_refl. Qed.
Lemma D_92b78 : decode_any W_92b78 = Some (OpImm ALU_ADD 13 10 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_92b7c : bv 32 := 0x00068813.
Lemma F_92b7c : fetch_word Asan.M.loaded_segments (0x92bcc : word) = Some W_92b7c.
Proof. vm_refl. Qed.
Lemma D_92b7c : decode_any W_92b7c = Some (OpImm ALU_ADD 16 13 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_92b80 : bv 32 := 0xfff6c683.
Lemma F_92b80 : fetch_word Asan.M.loaded_segments (0x92bd0 : word) = Some W_92b80.
Proof. vm_refl. Qed.
Lemma D_92b80 : decode_any W_92b80 = Some (Load SZ1 false 13 13 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_92b84 : bv 32 := 0x00d5e5b3.
Lemma F_92b84 : fetch_word Asan.M.loaded_segments (0x92bd4 : word) = Some W_92b84.
Proof. vm_refl. Qed.
Lemma D_92b84 : decode_any W_92b84 = Some (Op ALU_OR 11 11 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_92b88 : bv 32 := 0x00f87663.
Lemma F_92b88 : fetch_word Asan.M.loaded_segments (0x92bd8 : word) = Some W_92b88.
Proof. vm_refl. Qed.
Lemma D_92b88 : decode_any W_92b88 = Some (Branch BC_GEU 16 15 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_92b8c : bv 32 := 0x00180693.
Lemma F_92b8c : fetch_word Asan.M.loaded_segments (0x92bdc : word) = Some W_92b8c.
Proof. vm_refl. Qed.
Lemma D_92b8c : decode_any W_92b8c = Some (OpImm ALU_ADD 13 16 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_92b90 : bv 32 := 0xfee866e3.
Lemma F_92b90 : fetch_word Asan.M.loaded_segments (0x92be0 : word) = Some W_92b90.
Proof. vm_refl. Qed.
Lemma D_92b90 : decode_any W_92b90 = Some (Branch BC_LTU 16 14 8172, 4%Z).
Proof. vm_refl. Qed.

Definition W_92b94 : bv 32 := 0x00c7fa63.
Lemma F_92b94 : fetch_word Asan.M.loaded_segments (0x92be4 : word) = Some W_92b94.
Proof. vm_refl. Qed.
Lemma D_92b94 : decode_any W_92b94 = Some (Branch BC_GEU 15 12 20, 4%Z).
Proof. vm_refl. Qed.

Definition W_92b98 : bv 32 := 0x0007b683.
Lemma F_92b98 : fetch_word Asan.M.loaded_segments (0x92be8 : word) = Some W_92b98.
Proof. vm_refl. Qed.
Lemma D_92b98 : decode_any W_92b98 = Some (Load SZ8 true 13 15 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_92b9c : bv 32 := 0x00878793.
Lemma F_92b9c : fetch_word Asan.M.loaded_segments (0x92bec : word) = Some W_92b9c.
Proof. vm_refl. Qed.
Lemma D_92b9c : decode_any W_92b9c = Some (OpImm ALU_ADD 15 15 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_92ba0 : bv 32 := 0x00b6e5b3.
Lemma F_92ba0 : fetch_word Asan.M.loaded_segments (0x92bf0 : word) = Some W_92ba0.
Proof. vm_refl. Qed.
Lemma D_92ba0 : decode_any W_92ba0 = Some (Op ALU_OR 11 13 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_92ba4 : bv 32 := 0xfec7eae3.
Lemma F_92ba4 : fetch_word Asan.M.loaded_segments (0x92bf4 : word) = Some W_92ba4.
Proof. vm_refl. Qed.
Lemma D_92ba4 : decode_any W_92ba4 = Some (Branch BC_LTU 15 12 8180, 4%Z).
Proof. vm_refl. Qed.

Definition W_92ba8 : bv 32 := 0x02a66063.
Lemma F_92ba8 : fetch_word Asan.M.loaded_segments (0x92bf8 : word) = Some W_92ba8.
Proof. vm_refl. Qed.
Lemma D_92ba8 : decode_any W_92ba8 = Some (Branch BC_LTU 12 10 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_92bac : bv 32 := 0x00e67e63.
Lemma F_92bac : fetch_word Asan.M.loaded_segments (0x92bfc : word) = Some W_92bac.
Proof. vm_refl. Qed.
Lemma D_92bac : decode_any W_92bac = Some (Branch BC_GEU 12 14 28, 4%Z).
Proof. vm_refl. Qed.

Definition W_92bb0 : bv 32 := 0x40c70733.
Lemma F_92bb0 : fetch_word Asan.M.loaded_segments (0x92c00 : word) = Some W_92bb0.
Proof. vm_refl. Qed.
Lemma D_92bb0 : decode_any W_92bb0 = Some (Op ALU_SUB 14 14 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_92bb4 : bv 32 := 0x00064503.
Lemma F_92bb4 : fetch_word Asan.M.loaded_segments (0x92c04 : word) = Some W_92bb4.
Proof. vm_refl. Qed.
Lemma D_92bb4 : decode_any W_92bb4 = Some (Load SZ1 false 10 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_92bb8 : bv 32 := 0xfff70713.
Lemma F_92bb8 : fetch_word Asan.M.loaded_segments (0x92c08 : word) = Some W_92bb8.
Proof. vm_refl. Qed.
Lemma D_92bb8 : decode_any W_92bb8 = Some (OpImm ALU_ADD 14 14 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_92bbc : bv 32 := 0x00a5e5b3.
Lemma F_92bbc : fetch_word Asan.M.loaded_segments (0x92c0c : word) = Some W_92bbc.
Proof. vm_refl. Qed.
Lemma D_92bbc : decode_any W_92bbc = Some (Op ALU_OR 11 11 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_92bc0 : bv 32 := 0x00160613.
Lemma F_92bc0 : fetch_word Asan.M.loaded_segments (0x92c10 : word) = Some W_92bc0.
Proof. vm_refl. Qed.
Lemma D_92bc0 : decode_any W_92bc0 = Some (OpImm ALU_ADD 12 12 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_92bc4 : bv 32 := 0xfe0718e3.
Lemma F_92bc4 : fetch_word Asan.M.loaded_segments (0x92c14 : word) = Some W_92bc4.
Proof. vm_refl. Qed.
Lemma D_92bc4 : decode_any W_92bc4 = Some (Branch BC_NE 14 0 8176, 4%Z).
Proof. vm_refl. Qed.

Definition W_92bc8 : bv 32 := 0x0015b513.
Lemma F_92bc8 : fetch_word Asan.M.loaded_segments (0x92c18 : word) = Some W_92bc8.
Proof. vm_refl. Qed.
Lemma D_92bc8 : decode_any W_92bc8 = Some (OpImm ALU_SLTU 10 11 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_92bcc : bv 32 := 0x00813083.
Lemma F_92bcc : fetch_word Asan.M.loaded_segments (0x92c1c : word) = Some W_92bcc.
Proof. vm_refl. Qed.
Lemma D_92bcc : decode_any W_92bcc = Some (Load SZ8 true 1 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_92bd0 : bv 32 := 0x01010113.
Lemma F_92bd0 : fetch_word Asan.M.loaded_segments (0x92c20 : word) = Some W_92bd0.
Proof. vm_refl. Qed.
Lemma D_92bd0 : decode_any W_92bd0 = Some (OpImm ALU_ADD 2 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_92bd4 : bv 32 := 0x00008067.
Lemma F_92bd4 : fetch_word Asan.M.loaded_segments (0x92c24 : word) = Some W_92bd4.
Proof. vm_refl. Qed.
Lemma D_92bd4 : decode_any W_92bd4 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_92dec : bv 32 := 0xfffff637.
Lemma F_92dec : fetch_word Asan.M.loaded_segments (0x92e3c : word) = Some W_92dec.
Proof. vm_refl. Qed.
Lemma D_92dec : decode_any W_92dec = Some (Lui 12 1048575, 4%Z).
Proof. vm_refl. Qed.

Definition W_92df0 : bv 32 := 0x0016069b.
Lemma F_92df0 : fetch_word Asan.M.loaded_segments (0x92e40 : word) = Some W_92df0.
Proof. vm_refl. Qed.
Lemma D_92df0 : decode_any W_92df0 = Some (OpImm32 13 12 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_92df4 : bv 32 := 0x00d56863.
Lemma F_92df4 : fetch_word Asan.M.loaded_segments (0x92e44 : word) = Some W_92df4.
Proof. vm_refl. Qed.
Lemma D_92df4 : decode_any W_92df4 = Some (Branch BC_LTU 10 13 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_92e04 : bv 32 := 0x00a63533.
Lemma F_92e04 : fetch_word Asan.M.loaded_segments (0x92e54 : word) = Some W_92e04.
Proof. vm_refl. Qed.
Lemma D_92e04 : decode_any W_92e04 = Some (Op ALU_SLTU 10 12 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_92e08 : bv 32 := 0x00008067.
Lemma F_92e08 : fetch_word Asan.M.loaded_segments (0x92e58 : word) = Some W_92e08.
Proof. vm_refl. Qed.
Lemma D_92e08 : decode_any W_92e08 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_92e0c : bv 32 := 0x0de00893.
Lemma F_92e0c : fetch_word Asan.M.loaded_segments (0x92e5c : word) = Some W_92e0c.
Proof. vm_refl. Qed.
Lemma D_92e0c : decode_any W_92e0c = Some (OpImm ALU_ADD 17 0 222, 4%Z).
Proof. vm_refl. Qed.

Definition W_92e10 : bv 32 := 0x00000073.
Lemma F_92e10 : fetch_word Asan.M.loaded_segments (0x92e60 : word) = Some W_92e10.
Proof. vm_refl. Qed.
Lemma D_92e10 : decode_any W_92e10 = Some (Ecall, 4%Z).
Proof. vm_refl. Qed.
Lemma E_92e10 : is_ecall W_92e10 = true.
Proof. reflexivity. Qed.

Definition W_92e14 : bv 32 := 0x00008067.
Lemma F_92e14 : fetch_word Asan.M.loaded_segments (0x92e64 : word) = Some W_92e14.
Proof. vm_refl. Qed.
Lemma D_92e14 : decode_any W_92e14 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_92e18 : bv 32 := 0x0d700893.
Lemma F_92e18 : fetch_word Asan.M.loaded_segments (0x92e68 : word) = Some W_92e18.
Proof. vm_refl. Qed.
Lemma D_92e18 : decode_any W_92e18 = Some (OpImm ALU_ADD 17 0 215, 4%Z).
Proof. vm_refl. Qed.

Definition W_92e1c : bv 32 := 0x00000073.
Lemma F_92e1c : fetch_word Asan.M.loaded_segments (0x92e6c : word) = Some W_92e1c.
Proof. vm_refl. Qed.
Lemma D_92e1c : decode_any W_92e1c = Some (Ecall, 4%Z).
Proof. vm_refl. Qed.
Lemma E_92e1c : is_ecall W_92e1c = true.
Proof. reflexivity. Qed.

Definition W_92e20 : bv 32 := 0x00008067.
Lemma F_92e20 : fetch_word Asan.M.loaded_segments (0x92e70 : word) = Some W_92e20.
Proof. vm_refl. Qed.
Lemma D_92e20 : decode_any W_92e20 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_92e34 : bv 32 := 0x000c0697.
Lemma F_92e34 : fetch_word Asan.M.loaded_segments (0x92e84 : word) = Some W_92e34.
Proof. vm_refl. Qed.
Lemma D_92e34 : decode_any W_92e34 = Some (Auipc 13 192, 4%Z).
Proof. vm_refl. Qed.

Definition W_92e38 : bv 32 := 0x2f46b683.
Lemma F_92e38 : fetch_word Asan.M.loaded_segments (0x92e88 : word) = Some W_92e38.
Proof. vm_refl. Qed.
Lemma D_92e38 : decode_any W_92e38 = Some (Load SZ8 true 13 13 756, 4%Z).
Proof. vm_refl. Qed.

Definition W_92e3c : bv 32 := 0x00068a63.
Lemma F_92e3c : fetch_word Asan.M.loaded_segments (0x92e8c : word) = Some W_92e3c.
Proof. vm_refl. Qed.
Lemma D_92e3c : decode_any W_92e3c = Some (Branch BC_EQ 13 0 20, 4%Z).
Proof. vm_refl. Qed.

Definition W_92e40 : bv 32 := 0x00400693.
Lemma F_92e40 : fetch_word Asan.M.loaded_segments (0x92e90 : word) = Some W_92e40.
Proof. vm_refl. Qed.
Lemma D_92e40 : decode_any W_92e40 = Some (OpImm ALU_ADD 13 0 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_92e44 : bv 32 := 0x00d60663.
Lemma F_92e44 : fetch_word Asan.M.loaded_segments (0x92e94 : word) = Some W_92e44.
Proof. vm_refl. Qed.
Lemma D_92e44 : decode_any W_92e44 = Some (Branch BC_EQ 12 13 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_92e50 : bv 32 := 0x0e900893.
Lemma F_92e50 : fetch_word Asan.M.loaded_segments (0x92ea0 : word) = Some W_92e50.
Proof. vm_refl. Qed.
Lemma D_92e50 : decode_any W_92e50 = Some (OpImm ALU_ADD 17 0 233, 4%Z).
Proof. vm_refl. Qed.

Definition W_92e54 : bv 32 := 0x00000073.
Lemma F_92e54 : fetch_word Asan.M.loaded_segments (0x92ea4 : word) = Some W_92e54.
Proof. vm_refl. Qed.
Lemma D_92e54 : decode_any W_92e54 = Some (Ecall, 4%Z).
Proof. vm_refl. Qed.
Lemma E_92e54 : is_ecall W_92e54 = true.
Proof. reflexivity. Qed.

Definition W_92e58 : bv 32 := 0x0005051b.
Lemma F_92e58 : fetch_word Asan.M.loaded_segments (0x92ea8 : word) = Some W_92e58.
Proof. vm_refl. Qed.
Lemma D_92e58 : decode_any W_92e58 = Some (OpImm32 10 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_92e5c : bv 32 := 0x00008067.
Lemma F_92e5c : fetch_word Asan.M.loaded_segments (0x92eac : word) = Some W_92e5c.
Proof. vm_refl. Qed.
Lemma D_92e5c : decode_any W_92e5c = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

