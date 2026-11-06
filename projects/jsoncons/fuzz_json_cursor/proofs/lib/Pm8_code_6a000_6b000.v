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

Definition W_6a4fc : bv 32 := 0x0e40006f.
Lemma F_6a4fc : fetch_word Asan.M.loaded_segments (0x6a54c : word) = Some W_6a4fc.
Proof. vm_refl. Qed.
Lemma D_6a4fc : decode_any W_6a4fc = Some (Jal 0 228, 4%Z).
Proof. vm_refl. Qed.

Definition W_6a520 : bv 32 := 0x1dc0206f.
Lemma F_6a520 : fetch_word Asan.M.loaded_segments (0x6a570 : word) = Some W_6a520.
Proof. vm_refl. Qed.
Lemma D_6a520 : decode_any W_6a520 = Some (Jal 0 8668, 4%Z).
Proof. vm_refl. Qed.

Definition W_6a580 : bv 32 := 0x4a50706f.
Lemma F_6a580 : fetch_word Asan.M.loaded_segments (0x6a5d0 : word) = Some W_6a580.
Proof. vm_refl. Qed.
Lemma D_6a580 : decode_any W_6a580 = Some (Jal 0 31908, 4%Z).
Proof. vm_refl. Qed.

Definition W_6a5e0 : bv 32 := 0x81010113.
Lemma F_6a5e0 : fetch_word Asan.M.loaded_segments (0x6a630 : word) = Some W_6a5e0.
Proof. vm_refl. Qed.
Lemma D_6a5e0 : decode_any W_6a5e0 = Some (OpImm ALU_ADD 2 2 2064, 4%Z).
Proof. vm_refl. Qed.

Definition W_6a5e4 : bv 32 := 0x7e113423.
Lemma F_6a5e4 : fetch_word Asan.M.loaded_segments (0x6a634 : word) = Some W_6a5e4.
Proof. vm_refl. Qed.
Lemma D_6a5e4 : decode_any W_6a5e4 = Some (Store SZ8 2 1 2024, 4%Z).
Proof. vm_refl. Qed.

Definition W_6a5e8 : bv 32 := 0x7e813023.
Lemma F_6a5e8 : fetch_word Asan.M.loaded_segments (0x6a638 : word) = Some W_6a5e8.
Proof. vm_refl. Qed.
Lemma D_6a5e8 : decode_any W_6a5e8 = Some (Store SZ8 2 8 2016, 4%Z).
Proof. vm_refl. Qed.

Definition W_6a5ec : bv 32 := 0x7c913c23.
Lemma F_6a5ec : fetch_word Asan.M.loaded_segments (0x6a63c : word) = Some W_6a5ec.
Proof. vm_refl. Qed.
Lemma D_6a5ec : decode_any W_6a5ec = Some (Store SZ8 2 9 2008, 4%Z).
Proof. vm_refl. Qed.

Definition W_6a5f0 : bv 32 := 0x7d213823.
Lemma F_6a5f0 : fetch_word Asan.M.loaded_segments (0x6a640 : word) = Some W_6a5f0.
Proof. vm_refl. Qed.
Lemma D_6a5f0 : decode_any W_6a5f0 = Some (Store SZ8 2 18 2000, 4%Z).
Proof. vm_refl. Qed.

Definition W_6a5f4 : bv 32 := 0x7d313423.
Lemma F_6a5f4 : fetch_word Asan.M.loaded_segments (0x6a644 : word) = Some W_6a5f4.
Proof. vm_refl. Qed.
Lemma D_6a5f4 : decode_any W_6a5f4 = Some (Store SZ8 2 19 1992, 4%Z).
Proof. vm_refl. Qed.

Definition W_6a5f8 : bv 32 := 0x7d413023.
Lemma F_6a5f8 : fetch_word Asan.M.loaded_segments (0x6a648 : word) = Some W_6a5f8.
Proof. vm_refl. Qed.
Lemma D_6a5f8 : decode_any W_6a5f8 = Some (Store SZ8 2 20 1984, 4%Z).
Proof. vm_refl. Qed.

Definition W_6a5fc : bv 32 := 0x7b513c23.
Lemma F_6a5fc : fetch_word Asan.M.loaded_segments (0x6a64c : word) = Some W_6a5fc.
Proof. vm_refl. Qed.
Lemma D_6a5fc : decode_any W_6a5fc = Some (Store SZ8 2 21 1976, 4%Z).
Proof. vm_refl. Qed.

Definition W_6a600 : bv 32 := 0x7b613823.
Lemma F_6a600 : fetch_word Asan.M.loaded_segments (0x6a650 : word) = Some W_6a600.
Proof. vm_refl. Qed.
Lemma D_6a600 : decode_any W_6a600 = Some (Store SZ8 2 22 1968, 4%Z).
Proof. vm_refl. Qed.

Definition W_6a604 : bv 32 := 0x7f010413.
Lemma F_6a604 : fetch_word Asan.M.loaded_segments (0x6a654 : word) = Some W_6a604.
Proof. vm_refl. Qed.
Lemma D_6a604 : decode_any W_6a604 = Some (OpImm ALU_ADD 8 2 2032, 4%Z).
Proof. vm_refl. Qed.

Definition W_6a608 : bv 32 := 0xf9010113.
Lemma F_6a608 : fetch_word Asan.M.loaded_segments (0x6a658 : word) = Some W_6a608.
Proof. vm_refl. Qed.
Lemma D_6a608 : decode_any W_6a608 = Some (OpImm ALU_ADD 2 2 3984, 4%Z).
Proof. vm_refl. Qed.

Definition W_6a60c : bv 32 := 0x00050913.
Lemma F_6a60c : fetch_word Asan.M.loaded_segments (0x6a65c : word) = Some W_6a60c.
Proof. vm_refl. Qed.
Lemma D_6a60c : decode_any W_6a60c = Some (OpImm ALU_ADD 18 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_6a610 : bv 32 := 0x5551c0ef.
Lemma F_6a610 : fetch_word Asan.M.loaded_segments (0x6a660 : word) = Some W_6a610.
Proof. vm_refl. Qed.
Lemma D_6a610 : decode_any W_6a610 = Some (Jal 1 118100, 4%Z).
Proof. vm_refl. Qed.

Definition W_6a614 : bv 32 := 0x0a050863.
Lemma F_6a614 : fetch_word Asan.M.loaded_segments (0x6a664 : word) = Some W_6a614.
Proof. vm_refl. Qed.
Lemma D_6a614 : decode_any W_6a614 = Some (Branch BC_EQ 10 0 176, 4%Z).
Proof. vm_refl. Qed.

Definition W_6a618 : bv 32 := 0x45d1d0ef.
Lemma F_6a618 : fetch_word Asan.M.loaded_segments (0x6a668 : word) = Some W_6a618.
Proof. vm_refl. Qed.
Lemma D_6a618 : decode_any W_6a618 = Some (Jal 1 121948, 4%Z).
Proof. vm_refl. Qed.

Definition W_6a61c : bv 32 := 0x000eb597.
Lemma F_6a61c : fetch_word Asan.M.loaded_segments (0x6a66c : word) = Some W_6a61c.
Proof. vm_refl. Qed.
Lemma D_6a61c : decode_any W_6a61c = Some (Auipc 11 235, 4%Z).
Proof. vm_refl. Qed.

Definition W_6a620 : bv 32 := 0x8fc5b583.
Lemma F_6a620 : fetch_word Asan.M.loaded_segments (0x6a670 : word) = Some W_6a620.
Proof. vm_refl. Qed.
Lemma D_6a620 : decode_any W_6a620 = Some (Load SZ8 true 11 11 2300, 4%Z).
Proof. vm_refl. Qed.

Definition W_6a624 : bv 32 := 0x00050493.
Lemma F_6a624 : fetch_word Asan.M.loaded_segments (0x6a674 : word) = Some W_6a624.
Proof. vm_refl. Qed.
Lemma D_6a624 : decode_any W_6a624 = Some (OpImm ALU_ADD 9 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_6a628 : bv 32 := 0x00090513.
Lemma F_6a628 : fetch_word Asan.M.loaded_segments (0x6a678 : word) = Some W_6a628.
Proof. vm_refl. Qed.
Lemma D_6a628 : decode_any W_6a628 = Some (OpImm ALU_ADD 10 18 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_6a62c : bv 32 := 0x000580e7.
Lemma F_6a62c : fetch_word Asan.M.loaded_segments (0x6a67c : word) = Some W_6a62c.
Proof. vm_refl. Qed.
Lemma D_6a62c : decode_any W_6a62c = Some (Jalr 1 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_6a630 : bv 32 := 0x06048463.
Lemma F_6a630 : fetch_word Asan.M.loaded_segments (0x6a680 : word) = Some W_6a630.
Proof. vm_refl. Qed.
Lemma D_6a630 : decode_any W_6a630 = Some (Branch BC_EQ 9 0 104, 4%Z).
Proof. vm_refl. Qed.

Definition W_6a634 : bv 32 := 0x000e9597.
Lemma F_6a634 : fetch_word Asan.M.loaded_segments (0x6a684 : word) = Some W_6a634.
Proof. vm_refl. Qed.
Lemma D_6a634 : decode_any W_6a634 = Some (Auipc 11 233, 4%Z).
Proof. vm_refl. Qed.

Definition W_6a638 : bv 32 := 0xaa45b983.
Lemma F_6a638 : fetch_word Asan.M.loaded_segments (0x6a688 : word) = Some W_6a638.
Proof. vm_refl. Qed.
Lemma D_6a638 : decode_any W_6a638 = Some (Load SZ8 true 19 11 2724, 4%Z).
Proof. vm_refl. Qed.

Definition W_6a63c : bv 32 := 0x0fb9c583.
Lemma F_6a63c : fetch_word Asan.M.loaded_segments (0x6a68c : word) = Some W_6a63c.
Proof. vm_refl. Qed.
Lemma D_6a63c : decode_any W_6a63c = Some (Load SZ1 false 11 19 251, 4%Z).
Proof. vm_refl. Qed.

Definition W_6a640 : bv 32 := 0x04058c63.
Lemma F_6a640 : fetch_word Asan.M.loaded_segments (0x6a690 : word) = Some W_6a640.
Proof. vm_refl. Qed.
Lemma D_6a640 : decode_any W_6a640 = Some (Branch BC_EQ 11 0 88, 4%Z).
Proof. vm_refl. Qed.

Definition W_6a644 : bv 32 := 0x00150493.
Lemma F_6a644 : fetch_word Asan.M.loaded_segments (0x6a694 : word) = Some W_6a644.
Proof. vm_refl. Qed.
Lemma D_6a644 : decode_any W_6a644 = Some (OpImm ALU_ADD 9 10 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_6a648 : bv 32 := 0xfff94593.
Lemma F_6a648 : fetch_word Asan.M.loaded_segments (0x6a698 : word) = Some W_6a648.
Proof. vm_refl. Qed.
Lemma D_6a648 : decode_any W_6a648 = Some (OpImm ALU_XOR 11 18 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_6a64c : bv 32 := 0x80040a13.
Lemma F_6a64c : fetch_word Asan.M.loaded_segments (0x6a69c : word) = Some W_6a64c.
Proof. vm_refl. Qed.
Lemma D_6a64c : decode_any W_6a64c = Some (OpImm ALU_ADD 20 8 2048, 4%Z).
Proof. vm_refl. Qed.

Definition W_6a650 : bv 32 := 0xfa8a0a13.
Lemma F_6a650 : fetch_word Asan.M.loaded_segments (0x6a6a0 : word) = Some W_6a650.
Proof. vm_refl. Qed.
Lemma D_6a650 : decode_any W_6a650 = Some (OpImm ALU_ADD 20 20 4008, 4%Z).
Proof. vm_refl. Qed.

Definition W_6a654 : bv 32 := 0x0a95e063.
Lemma F_6a654 : fetch_word Asan.M.loaded_segments (0x6a6a4 : word) = Some W_6a654.
Proof. vm_refl. Qed.
Lemma D_6a654 : decode_any W_6a654 = Some (Branch BC_LTU 11 9 160, 4%Z).
Proof. vm_refl. Qed.

Definition W_6a658 : bv 32 := 0x04000593.
Lemma F_6a658 : fetch_word Asan.M.loaded_segments (0x6a6a8 : word) = Some W_6a658.
Proof. vm_refl. Qed.
Lemma D_6a658 : decode_any W_6a658 = Some (OpImm ALU_ADD 11 0 64, 4%Z).
Proof. vm_refl. Qed.

Definition W_6a65c : bv 32 := 0x10b57263.
Lemma F_6a65c : fetch_word Asan.M.loaded_segments (0x6a6ac : word) = Some W_6a65c.
Proof. vm_refl. Qed.
Lemma D_6a65c : decode_any W_6a65c = Some (Branch BC_GEU 10 11 260, 4%Z).
Proof. vm_refl. Qed.

Definition W_6a660 : bv 32 := 0x000e9597.
Lemma F_6a660 : fetch_word Asan.M.loaded_segments (0x6a6b0 : word) = Some W_6a660.
Proof. vm_refl. Qed.
Lemma D_6a660 : decode_any W_6a660 = Some (Auipc 11 233, 4%Z).
Proof. vm_refl. Qed.

Definition W_6a664 : bv 32 := 0xa885b583.
Lemma F_6a664 : fetch_word Asan.M.loaded_segments (0x6a6b4 : word) = Some W_6a664.
Proof. vm_refl. Qed.
Lemma D_6a664 : decode_any W_6a664 = Some (Load SZ8 true 11 11 2696, 4%Z).
Proof. vm_refl. Qed.

Definition W_6a668 : bv 32 := 0x0005b603.
Lemma F_6a668 : fetch_word Asan.M.loaded_segments (0x6a6b8 : word) = Some W_6a668.
Proof. vm_refl. Qed.
Lemma D_6a668 : decode_any W_6a668 = Some (Load SZ8 true 12 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_6a66c : bv 32 := 0x012506b3.
Lemma F_6a66c : fetch_word Asan.M.loaded_segments (0x6a6bc : word) = Some W_6a66c.
Proof. vm_refl. Qed.
Lemma D_6a66c : decode_any W_6a66c = Some (Op ALU_ADD 13 10 18, 4%Z).
Proof. vm_refl. Qed.

Definition W_6a670 : bv 32 := 0x00395593.
Lemma F_6a670 : fetch_word Asan.M.loaded_segments (0x6a6c0 : word) = Some W_6a670.
Proof. vm_refl. Qed.
Lemma D_6a670 : decode_any W_6a670 = Some (ShiftImm ALU_SRL 11 18 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_6a674 : bv 32 := 0x0036d713.
Lemma F_6a674 : fetch_word Asan.M.loaded_segments (0x6a6c4 : word) = Some W_6a674.
Proof. vm_refl. Qed.
Lemma D_6a674 : decode_any W_6a674 = Some (ShiftImm ALU_SRL 14 13 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_6a678 : bv 32 := 0x00b605b3.
Lemma F_6a678 : fetch_word Asan.M.loaded_segments (0x6a6c8 : word) = Some W_6a678.
Proof. vm_refl. Qed.
Lemma D_6a678 : decode_any W_6a678 = Some (Op ALU_ADD 11 12 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_6a67c : bv 32 := 0x00e60633.
Lemma F_6a67c : fetch_word Asan.M.loaded_segments (0x6a6cc : word) = Some W_6a67c.
Proof. vm_refl. Qed.
Lemma D_6a67c : decode_any W_6a67c = Some (Op ALU_ADD 12 12 14, 4%Z).
Proof. vm_refl. Qed.

Definition W_6a680 : bv 32 := 0xff85f713.
Lemma F_6a680 : fetch_word Asan.M.loaded_segments (0x6a6d0 : word) = Some W_6a680.
Proof. vm_refl. Qed.
Lemma D_6a680 : decode_any W_6a680 = Some (OpImm ALU_AND 14 11 4088, 4%Z).
Proof. vm_refl. Qed.

Definition W_6a684 : bv 32 := 0xff867793.
Lemma F_6a684 : fetch_word Asan.M.loaded_segments (0x6a6d4 : word) = Some W_6a684.
Proof. vm_refl. Qed.
Lemma D_6a684 : decode_any W_6a684 = Some (OpImm ALU_AND 15 12 4088, 4%Z).
Proof. vm_refl. Qed.

Definition W_6a688 : bv 32 := 0x00073703.
Lemma F_6a688 : fetch_word Asan.M.loaded_segments (0x6a6d8 : word) = Some W_6a688.
Proof. vm_refl. Qed.
Lemma D_6a688 : decode_any W_6a688 = Some (Load SZ8 true 14 14 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_6a68c : bv 32 := 0x0007b783.
Lemma F_6a68c : fetch_word Asan.M.loaded_segments (0x6a6dc : word) = Some W_6a68c.
Proof. vm_refl. Qed.
Lemma D_6a68c : decode_any W_6a68c = Some (Load SZ8 true 15 15 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_6a690 : bv 32 := 0x00e7e733.
Lemma F_6a690 : fetch_word Asan.M.loaded_segments (0x6a6e0 : word) = Some W_6a690.
Proof. vm_refl. Qed.
Lemma D_6a690 : decode_any W_6a690 = Some (Op ALU_OR 14 15 14, 4%Z).
Proof. vm_refl. Qed.

Definition W_6a694 : bv 32 := 0x0c071e63.
Lemma F_6a694 : fetch_word Asan.M.loaded_segments (0x6a6e4 : word) = Some W_6a694.
Proof. vm_refl. Qed.
Lemma D_6a694 : decode_any W_6a694 = Some (Branch BC_NE 14 0 220, 4%Z).
Proof. vm_refl. Qed.

Definition W_6a698 : bv 32 := 0x07010113.
Lemma F_6a698 : fetch_word Asan.M.loaded_segments (0x6a6e8 : word) = Some W_6a698.
Proof. vm_refl. Qed.
Lemma D_6a698 : decode_any W_6a698 = Some (OpImm ALU_ADD 2 2 112, 4%Z).
Proof. vm_refl. Qed.

Definition W_6a69c : bv 32 := 0x7e813083.
Lemma F_6a69c : fetch_word Asan.M.loaded_segments (0x6a6ec : word) = Some W_6a69c.
Proof. vm_refl. Qed.
Lemma D_6a69c : decode_any W_6a69c = Some (Load SZ8 true 1 2 2024, 4%Z).
Proof. vm_refl. Qed.

Definition W_6a6a0 : bv 32 := 0x7e013403.
Lemma F_6a6a0 : fetch_word Asan.M.loaded_segments (0x6a6f0 : word) = Some W_6a6a0.
Proof. vm_refl. Qed.
Lemma D_6a6a0 : decode_any W_6a6a0 = Some (Load SZ8 true 8 2 2016, 4%Z).
Proof. vm_refl. Qed.

Definition W_6a6a4 : bv 32 := 0x7d813483.
Lemma F_6a6a4 : fetch_word Asan.M.loaded_segments (0x6a6f4 : word) = Some W_6a6a4.
Proof. vm_refl. Qed.
Lemma D_6a6a4 : decode_any W_6a6a4 = Some (Load SZ8 true 9 2 2008, 4%Z).
Proof. vm_refl. Qed.

Definition W_6a6a8 : bv 32 := 0x7d013903.
Lemma F_6a6a8 : fetch_word Asan.M.loaded_segments (0x6a6f8 : word) = Some W_6a6a8.
Proof. vm_refl. Qed.
Lemma D_6a6a8 : decode_any W_6a6a8 = Some (Load SZ8 true 18 2 2000, 4%Z).
Proof. vm_refl. Qed.

Definition W_6a6ac : bv 32 := 0x7c813983.
Lemma F_6a6ac : fetch_word Asan.M.loaded_segments (0x6a6fc : word) = Some W_6a6ac.
Proof. vm_refl. Qed.
Lemma D_6a6ac : decode_any W_6a6ac = Some (Load SZ8 true 19 2 1992, 4%Z).
Proof. vm_refl. Qed.

Definition W_6a6b0 : bv 32 := 0x7c013a03.
Lemma F_6a6b0 : fetch_word Asan.M.loaded_segments (0x6a700 : word) = Some W_6a6b0.
Proof. vm_refl. Qed.
Lemma D_6a6b0 : decode_any W_6a6b0 = Some (Load SZ8 true 20 2 1984, 4%Z).
Proof. vm_refl. Qed.

Definition W_6a6b4 : bv 32 := 0x7b813a83.
Lemma F_6a6b4 : fetch_word Asan.M.loaded_segments (0x6a704 : word) = Some W_6a6b4.
Proof. vm_refl. Qed.
Lemma D_6a6b4 : decode_any W_6a6b4 = Some (Load SZ8 true 21 2 1976, 4%Z).
Proof. vm_refl. Qed.

Definition W_6a6b8 : bv 32 := 0x7b013b03.
Lemma F_6a6b8 : fetch_word Asan.M.loaded_segments (0x6a708 : word) = Some W_6a6b8.
Proof. vm_refl. Qed.
Lemma D_6a6b8 : decode_any W_6a6b8 = Some (Load SZ8 true 22 2 1968, 4%Z).
Proof. vm_refl. Qed.

Definition W_6a6bc : bv 32 := 0x7f010113.
Lemma F_6a6bc : fetch_word Asan.M.loaded_segments (0x6a70c : word) = Some W_6a6bc.
Proof. vm_refl. Qed.
Lemma D_6a6bc : decode_any W_6a6bc = Some (OpImm ALU_ADD 2 2 2032, 4%Z).
Proof. vm_refl. Qed.

Definition W_6a6c0 : bv 32 := 0x00008067.
Lemma F_6a6c0 : fetch_word Asan.M.loaded_segments (0x6a710 : word) = Some W_6a6c0.
Proof. vm_refl. Qed.
Lemma D_6a6c0 : decode_any W_6a6c0 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_6a760 : bv 32 := 0x00050a93.
Lemma F_6a760 : fetch_word Asan.M.loaded_segments (0x6a7b0 : word) = Some W_6a760.
Proof. vm_refl. Qed.
Lemma D_6a760 : decode_any W_6a760 = Some (OpImm ALU_ADD 21 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_6a764 : bv 32 := 0x04049263.
Lemma F_6a764 : fetch_word Asan.M.loaded_segments (0x6a7b4 : word) = Some W_6a764.
Proof. vm_refl. Qed.
Lemma D_6a764 : decode_any W_6a764 = Some (Branch BC_NE 9 0 68, 4%Z).
Proof. vm_refl. Qed.

Definition W_6a770 : bv 32 := 0x00050a93.
Lemma F_6a770 : fetch_word Asan.M.loaded_segments (0x6a7c0 : word) = Some W_6a770.
Proof. vm_refl. Qed.
Lemma D_6a770 : decode_any W_6a770 = Some (OpImm ALU_ADD 21 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_6a774 : bv 32 := 0x00060503.
Lemma F_6a774 : fetch_word Asan.M.loaded_segments (0x6a7c4 : word) = Some W_6a774.
Proof. vm_refl. Qed.
Lemma D_6a774 : decode_any W_6a774 = Some (Load SZ1 true 10 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_6a778 : bv 32 := 0x0076f693.
Lemma F_6a778 : fetch_word Asan.M.loaded_segments (0x6a7c8 : word) = Some W_6a778.
Proof. vm_refl. Qed.
Lemma D_6a778 : decode_any W_6a778 = Some (OpImm ALU_AND 13 13 7, 4%Z).
Proof. vm_refl. Qed.

Definition W_6a77c : bv 32 := 0x00a03733.
Lemma F_6a77c : fetch_word Asan.M.loaded_segments (0x6a7cc : word) = Some W_6a77c.
Proof. vm_refl. Qed.
Lemma D_6a77c : decode_any W_6a77c = Some (Op ALU_SLTU 14 0 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_6a780 : bv 32 := 0x00a6a533.
Lemma F_6a780 : fetch_word Asan.M.loaded_segments (0x6a7d0 : word) = Some W_6a780.
Proof. vm_refl. Qed.
Lemma D_6a780 : decode_any W_6a780 = Some (Op ALU_SLT 10 13 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_6a784 : bv 32 := 0x00154513.
Lemma F_6a784 : fetch_word Asan.M.loaded_segments (0x6a7d4 : word) = Some W_6a784.
Proof. vm_refl. Qed.
Lemma D_6a784 : decode_any W_6a784 = Some (OpImm ALU_XOR 10 10 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_6a788 : bv 32 := 0x00a77533.
Lemma F_6a788 : fetch_word Asan.M.loaded_segments (0x6a7d8 : word) = Some W_6a788.
Proof. vm_refl. Qed.
Lemma D_6a788 : decode_any W_6a788 = Some (Op ALU_AND 10 14 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_6a78c : bv 32 := 0x00c5fa63.
Lemma F_6a78c : fetch_word Asan.M.loaded_segments (0x6a7dc : word) = Some W_6a78c.
Proof. vm_refl. Qed.
Lemma D_6a78c : decode_any W_6a78c = Some (Branch BC_GEU 11 12 20, 4%Z).
Proof. vm_refl. Qed.

Definition W_6a790 : bv 32 := 0x0005c683.
Lemma F_6a790 : fetch_word Asan.M.loaded_segments (0x6a7e0 : word) = Some W_6a790.
Proof. vm_refl. Qed.
Lemma D_6a790 : decode_any W_6a790 = Some (Load SZ1 false 13 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_6a794 : bv 32 := 0x00158593.
Lemma F_6a794 : fetch_word Asan.M.loaded_segments (0x6a7e4 : word) = Some W_6a794.
Proof. vm_refl. Qed.
Lemma D_6a794 : decode_any W_6a794 = Some (OpImm ALU_ADD 11 11 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_6a798 : bv 32 := 0x00a6e533.
Lemma F_6a798 : fetch_word Asan.M.loaded_segments (0x6a7e8 : word) = Some W_6a798.
Proof. vm_refl. Qed.
Lemma D_6a798 : decode_any W_6a798 = Some (Op ALU_OR 10 13 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_6a79c : bv 32 := 0xfec59ae3.
Lemma F_6a79c : fetch_word Asan.M.loaded_segments (0x6a7ec : word) = Some W_6a79c.
Proof. vm_refl. Qed.
Lemma D_6a79c : decode_any W_6a79c = Some (Branch BC_NE 11 12 8180, 4%Z).
Proof. vm_refl. Qed.

Definition W_6a7a0 : bv 32 := 0x0ff57513.
Lemma F_6a7a0 : fetch_word Asan.M.loaded_segments (0x6a7f0 : word) = Some W_6a7a0.
Proof. vm_refl. Qed.
Lemma D_6a7a0 : decode_any W_6a7a0 = Some (OpImm ALU_AND 10 10 255, 4%Z).
Proof. vm_refl. Qed.

Definition W_6a7a4 : bv 32 := 0x0c050463.
Lemma F_6a7a4 : fetch_word Asan.M.loaded_segments (0x6a7f4 : word) = Some W_6a7a4.
Proof. vm_refl. Qed.
Lemma D_6a7a4 : decode_any W_6a7a4 = Some (Branch BC_EQ 10 0 200, 4%Z).
Proof. vm_refl. Qed.

Definition W_6a7a8 : bv 32 := 0x00090513.
Lemma F_6a7a8 : fetch_word Asan.M.loaded_segments (0x6a7f8 : word) = Some W_6a7a8.
Proof. vm_refl. Qed.
Lemma D_6a7a8 : decode_any W_6a7a8 = Some (OpImm ALU_ADD 10 18 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_6a7ac : bv 32 := 0x00048593.
Lemma F_6a7ac : fetch_word Asan.M.loaded_segments (0x6a7fc : word) = Some W_6a7ac.
Proof. vm_refl. Qed.
Lemma D_6a7ac : decode_any W_6a7ac = Some (OpImm ALU_ADD 11 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_6a7b0 : bv 32 := 0x6a1170ef.
Lemma F_6a7b0 : fetch_word Asan.M.loaded_segments (0x6a800 : word) = Some W_6a7b0.
Proof. vm_refl. Qed.
Lemma D_6a7b0 : decode_any W_6a7b0 = Some (Jal 1 97952, 4%Z).
Proof. vm_refl. Qed.

Definition W_6a7b4 : bv 32 := 0x0a050c63.
Lemma F_6a7b4 : fetch_word Asan.M.loaded_segments (0x6a804 : word) = Some W_6a7b4.
Proof. vm_refl. Qed.
Lemma D_6a7b4 : decode_any W_6a7b4 = Some (Branch BC_EQ 10 0 184, 4%Z).
Proof. vm_refl. Qed.

Definition W_6a86c : bv 32 := 0x000a8513.
Lemma F_6a86c : fetch_word Asan.M.loaded_segments (0x6a8bc : word) = Some W_6a86c.
Proof. vm_refl. Qed.
Lemma D_6a86c : decode_any W_6a86c = Some (OpImm ALU_ADD 10 21 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_6a870 : bv 32 := 0xe29ff06f.
Lemma F_6a870 : fetch_word Asan.M.loaded_segments (0x6a8c0 : word) = Some W_6a870.
Proof. vm_refl. Qed.
Lemma D_6a870 : decode_any W_6a870 = Some (Jal 0 2096680, 4%Z).
Proof. vm_refl. Qed.

Definition W_6a8c4 : bv 32 := 0x06048a63.
Lemma F_6a8c4 : fetch_word Asan.M.loaded_segments (0x6a914 : word) = Some W_6a8c4.
Proof. vm_refl. Qed.
Lemma D_6a8c4 : decode_any W_6a8c4 = Some (Branch BC_EQ 9 0 116, 4%Z).
Proof. vm_refl. Qed.

Definition W_6a8c8 : bv 32 := 0x000e9597.
Lemma F_6a8c8 : fetch_word Asan.M.loaded_segments (0x6a918 : word) = Some W_6a8c8.
Proof. vm_refl. Qed.
Lemma D_6a8c8 : decode_any W_6a8c8 = Some (Auipc 11 233, 4%Z).
Proof. vm_refl. Qed.

Definition W_6a8cc : bv 32 := 0x8105ba83.
Lemma F_6a8cc : fetch_word Asan.M.loaded_segments (0x6a91c : word) = Some W_6a8cc.
Proof. vm_refl. Qed.
Lemma D_6a8cc : decode_any W_6a8cc = Some (Load SZ8 true 21 11 2064, 4%Z).
Proof. vm_refl. Qed.

Definition W_6a8d0 : bv 32 := 0x0fbac583.
Lemma F_6a8d0 : fetch_word Asan.M.loaded_segments (0x6a920 : word) = Some W_6a8d0.
Proof. vm_refl. Qed.
Lemma D_6a8d0 : decode_any W_6a8d0 = Some (Load SZ1 false 11 21 251, 4%Z).
Proof. vm_refl. Qed.

Definition W_6a8d4 : bv 32 := 0x06058263.
Lemma F_6a8d4 : fetch_word Asan.M.loaded_segments (0x6a924 : word) = Some W_6a8d4.
Proof. vm_refl. Qed.
Lemma D_6a8d4 : decode_any W_6a8d4 = Some (Branch BC_EQ 11 0 100, 4%Z).
Proof. vm_refl. Qed.

Definition W_6a8d8 : bv 32 := 0x00150493.
Lemma F_6a8d8 : fetch_word Asan.M.loaded_segments (0x6a928 : word) = Some W_6a8d8.
Proof. vm_refl. Qed.
Lemma D_6a8d8 : decode_any W_6a8d8 = Some (OpImm ALU_ADD 9 10 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_6a8dc : bv 32 := 0x0934f463.
Lemma F_6a8dc : fetch_word Asan.M.loaded_segments (0x6a92c : word) = Some W_6a8dc.
Proof. vm_refl. Qed.
Lemma D_6a8dc : decode_any W_6a8dc = Some (Branch BC_GEU 9 19 136, 4%Z).
Proof. vm_refl. Qed.

Definition W_6a8e0 : bv 32 := 0xfff94593.
Lemma F_6a8e0 : fetch_word Asan.M.loaded_segments (0x6a930 : word) = Some W_6a8e0.
Proof. vm_refl. Qed.
Lemma D_6a8e0 : decode_any W_6a8e0 = Some (OpImm ALU_XOR 11 18 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_6a8e4 : bv 32 := 0x80040a13.
Lemma F_6a8e4 : fetch_word Asan.M.loaded_segments (0x6a934 : word) = Some W_6a8e4.
Proof. vm_refl. Qed.
Lemma D_6a8e4 : decode_any W_6a8e4 = Some (OpImm ALU_ADD 20 8 2048, 4%Z).
Proof. vm_refl. Qed.

Definition W_6a8e8 : bv 32 := 0xfa8a0a13.
Lemma F_6a8e8 : fetch_word Asan.M.loaded_segments (0x6a938 : word) = Some W_6a8e8.
Proof. vm_refl. Qed.
Lemma D_6a8e8 : decode_any W_6a8e8 = Some (OpImm ALU_ADD 20 20 4008, 4%Z).
Proof. vm_refl. Qed.

Definition W_6a8ec : bv 32 := 0x0895e663.
Lemma F_6a8ec : fetch_word Asan.M.loaded_segments (0x6a93c : word) = Some W_6a8ec.
Proof. vm_refl. Qed.
Lemma D_6a8ec : decode_any W_6a8ec = Some (Branch BC_LTU 11 9 140, 4%Z).
Proof. vm_refl. Qed.

Definition W_6a8f0 : bv 32 := 0xfbf48593.
Lemma F_6a8f0 : fetch_word Asan.M.loaded_segments (0x6a940 : word) = Some W_6a8f0.
Proof. vm_refl. Qed.
Lemma D_6a8f0 : decode_any W_6a8f0 = Some (OpImm ALU_ADD 11 9 4031, 4%Z).
Proof. vm_refl. Qed.

Definition W_6a8f4 : bv 32 := 0xfbf00613.
Lemma F_6a8f4 : fetch_word Asan.M.loaded_segments (0x6a944 : word) = Some W_6a8f4.
Proof. vm_refl. Qed.
Lemma D_6a8f4 : decode_any W_6a8f4 = Some (OpImm ALU_ADD 12 0 4031, 4%Z).
Proof. vm_refl. Qed.

Definition W_6a8f8 : bv 32 := 0x0eb67863.
Lemma F_6a8f8 : fetch_word Asan.M.loaded_segments (0x6a948 : word) = Some W_6a8f8.
Proof. vm_refl. Qed.
Lemma D_6a8f8 : decode_any W_6a8f8 = Some (Branch BC_GEU 12 11 240, 4%Z).
Proof. vm_refl. Qed.

Definition W_6a8fc : bv 32 := 0x000e8597.
Lemma F_6a8fc : fetch_word Asan.M.loaded_segments (0x6a94c : word) = Some W_6a8fc.
Proof. vm_refl. Qed.
Lemma D_6a8fc : decode_any W_6a8fc = Some (Auipc 11 232, 4%Z).
Proof. vm_refl. Qed.

Definition W_6a900 : bv 32 := 0x7ec5b583.
Lemma F_6a900 : fetch_word Asan.M.loaded_segments (0x6a950 : word) = Some W_6a900.
Proof. vm_refl. Qed.
Lemma D_6a900 : decode_any W_6a900 = Some (Load SZ8 true 11 11 2028, 4%Z).
Proof. vm_refl. Qed.

Definition W_6a904 : bv 32 := 0x009906b3.
Lemma F_6a904 : fetch_word Asan.M.loaded_segments (0x6a954 : word) = Some W_6a904.
Proof. vm_refl. Qed.
Lemma D_6a904 : decode_any W_6a904 = Some (Op ALU_ADD 13 18 9, 4%Z).
Proof. vm_refl. Qed.

Definition W_6a908 : bv 32 := 0x0005b603.
Lemma F_6a908 : fetch_word Asan.M.loaded_segments (0x6a958 : word) = Some W_6a908.
Proof. vm_refl. Qed.
Lemma D_6a908 : decode_any W_6a908 = Some (Load SZ8 true 12 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_6a90c : bv 32 := 0x00395593.
Lemma F_6a90c : fetch_word Asan.M.loaded_segments (0x6a95c : word) = Some W_6a90c.
Proof. vm_refl. Qed.
Lemma D_6a90c : decode_any W_6a90c = Some (ShiftImm ALU_SRL 11 18 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_6a910 : bv 32 := 0xfff68693.
Lemma F_6a910 : fetch_word Asan.M.loaded_segments (0x6a960 : word) = Some W_6a910.
Proof. vm_refl. Qed.
Lemma D_6a910 : decode_any W_6a910 = Some (OpImm ALU_ADD 13 13 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_6a914 : bv 32 := 0x0036d713.
Lemma F_6a914 : fetch_word Asan.M.loaded_segments (0x6a964 : word) = Some W_6a914.
Proof. vm_refl. Qed.
Lemma D_6a914 : decode_any W_6a914 = Some (ShiftImm ALU_SRL 14 13 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_6a918 : bv 32 := 0x00b605b3.
Lemma F_6a918 : fetch_word Asan.M.loaded_segments (0x6a968 : word) = Some W_6a918.
Proof. vm_refl. Qed.
Lemma D_6a918 : decode_any W_6a918 = Some (Op ALU_ADD 11 12 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_6a91c : bv 32 := 0x00e60633.
Lemma F_6a91c : fetch_word Asan.M.loaded_segments (0x6a96c : word) = Some W_6a91c.
Proof. vm_refl. Qed.
Lemma D_6a91c : decode_any W_6a91c = Some (Op ALU_ADD 12 12 14, 4%Z).
Proof. vm_refl. Qed.

Definition W_6a920 : bv 32 := 0xff85f713.
Lemma F_6a920 : fetch_word Asan.M.loaded_segments (0x6a970 : word) = Some W_6a920.
Proof. vm_refl. Qed.
Lemma D_6a920 : decode_any W_6a920 = Some (OpImm ALU_AND 14 11 4088, 4%Z).
Proof. vm_refl. Qed.

Definition W_6a924 : bv 32 := 0xff867793.
Lemma F_6a924 : fetch_word Asan.M.loaded_segments (0x6a974 : word) = Some W_6a924.
Proof. vm_refl. Qed.
Lemma D_6a924 : decode_any W_6a924 = Some (OpImm ALU_AND 15 12 4088, 4%Z).
Proof. vm_refl. Qed.

Definition W_6a928 : bv 32 := 0x00073703.
Lemma F_6a928 : fetch_word Asan.M.loaded_segments (0x6a978 : word) = Some W_6a928.
Proof. vm_refl. Qed.
Lemma D_6a928 : decode_any W_6a928 = Some (Load SZ8 true 14 14 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_6a92c : bv 32 := 0x0007b783.
Lemma F_6a92c : fetch_word Asan.M.loaded_segments (0x6a97c : word) = Some W_6a92c.
Proof. vm_refl. Qed.
Lemma D_6a92c : decode_any W_6a92c = Some (Load SZ8 true 15 15 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_6a930 : bv 32 := 0x00e7e733.
Lemma F_6a930 : fetch_word Asan.M.loaded_segments (0x6a980 : word) = Some W_6a930.
Proof. vm_refl. Qed.
Lemma D_6a930 : decode_any W_6a930 = Some (Op ALU_OR 14 15 14, 4%Z).
Proof. vm_refl. Qed.

Definition W_6a934 : bv 32 := 0x0a071e63.
Lemma F_6a934 : fetch_word Asan.M.loaded_segments (0x6a984 : word) = Some W_6a934.
Proof. vm_refl. Qed.
Lemma D_6a934 : decode_any W_6a934 = Some (Branch BC_NE 14 0 188, 4%Z).
Proof. vm_refl. Qed.

Definition W_6a9e8 : bv 32 := 0x02049e63.
Lemma F_6a9e8 : fetch_word Asan.M.loaded_segments (0x6aa38 : word) = Some W_6a9e8.
Proof. vm_refl. Qed.
Lemma D_6a9e8 : decode_any W_6a9e8 = Some (Branch BC_NE 9 0 60, 4%Z).
Proof. vm_refl. Qed.

Definition W_6aa24 : bv 32 := 0x00050b13.
Lemma F_6aa24 : fetch_word Asan.M.loaded_segments (0x6aa74 : word) = Some W_6aa24.
Proof. vm_refl. Qed.
Lemma D_6aa24 : decode_any W_6aa24 = Some (OpImm ALU_ADD 22 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_6aa28 : bv 32 := 0x00090513.
Lemma F_6aa28 : fetch_word Asan.M.loaded_segments (0x6aa78 : word) = Some W_6aa28.
Proof. vm_refl. Qed.
Lemma D_6aa28 : decode_any W_6aa28 = Some (OpImm ALU_ADD 10 18 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_6aa2c : bv 32 := 0x00048593.
Lemma F_6aa2c : fetch_word Asan.M.loaded_segments (0x6aa7c : word) = Some W_6aa2c.
Proof. vm_refl. Qed.
Lemma D_6aa2c : decode_any W_6aa2c = Some (OpImm ALU_ADD 11 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_6aa30 : bv 32 := 0x421170ef.
Lemma F_6aa30 : fetch_word Asan.M.loaded_segments (0x6aa80 : word) = Some W_6aa30.
Proof. vm_refl. Qed.
Lemma D_6aa30 : decode_any W_6aa30 = Some (Jal 1 97312, 4%Z).
Proof. vm_refl. Qed.

Definition W_6aa34 : bv 32 := 0x00050913.
Lemma F_6aa34 : fetch_word Asan.M.loaded_segments (0x6aa84 : word) = Some W_6aa34.
Proof. vm_refl. Qed.
Lemma D_6aa34 : decode_any W_6aa34 = Some (OpImm ALU_ADD 18 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_6aa38 : bv 32 := 0x000b0513.
Lemma F_6aa38 : fetch_word Asan.M.loaded_segments (0x6aa88 : word) = Some W_6aa38.
Proof. vm_refl. Qed.
Lemma D_6aa38 : decode_any W_6aa38 = Some (OpImm ALU_ADD 10 22 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_6aa3c : bv 32 := 0xee090ee3.
Lemma F_6aa3c : fetch_word Asan.M.loaded_segments (0x6aa8c : word) = Some W_6aa3c.
Proof. vm_refl. Qed.
Lemma D_6aa3c : decode_any W_6aa3c = Some (Branch BC_EQ 18 0 7932, 4%Z).
Proof. vm_refl. Qed.

