(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
(* [comment removed for export] *)

From OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.H Require GcFlushS10.   (* [comment removed for export] *)
From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.leptonica.fhmtgen_fuzzer.images Require Import Plain.
Open Scope bv_scope.
#[local] Hint Extern 0 (BvWf _ _) => (lazymatch goal with |- BvWf ?n ?v => is_closed_term n; is_closed_term v end; exact I) : typeclass_instances.   (* [comment removed for export] *)

(* [comment removed for export] *)
Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

(* [comment removed for export] *)



(* [comment removed for export] *)
Definition W_15570 : bv 32 := 0xff010113.
Lemma F_15570 : fetch_word Plain.M.loaded_segments (0x1566c : word) = Some W_15570.
Proof. vm_refl. Qed.
Lemma D_15570 : decode_any W_15570 = Some (OpImm ALU_ADD 2 2 4080, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15574 : bv 32 := 0x00113423.
Lemma F_15574 : fetch_word Plain.M.loaded_segments (0x15670 : word) = Some W_15574.
Proof. vm_refl. Qed.
Lemma D_15574 : decode_any W_15574 = Some (Store SZ8 2 1 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15578 : bv 32 := 0x00813023.
Lemma F_15578 : fetch_word Plain.M.loaded_segments (0x15674 : word) = Some W_15578.
Proof. vm_refl. Qed.
Lemma D_15578 : decode_any W_15578 = Some (Store SZ8 2 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1557c : bv 32 := 0x00060413.
Lemma F_1557c : fetch_word Plain.M.loaded_segments (0x15678 : word) = Some W_1557c.
Proof. vm_refl. Qed.
Lemma D_1557c : decode_any W_1557c = Some (OpImm ALU_ADD 8 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15580 : bv 32 := 0x00050613.
Lemma F_15580 : fetch_word Plain.M.loaded_segments (0x1567c : word) = Some W_15580.
Proof. vm_refl. Qed.
Lemma D_15580 : decode_any W_15580 = Some (OpImm ALU_ADD 12 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15584 : bv 32 := 0xffffc517.
Lemma F_15584 : fetch_word Plain.M.loaded_segments (0x15680 : word) = Some W_15584.
Proof. vm_refl. Qed.
Lemma D_15584 : decode_any W_15584 = Some (Auipc 10 1048572, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15588 : bv 32 := 0xf4f50513.
Lemma F_15588 : fetch_word Plain.M.loaded_segments (0x15684 : word) = Some W_15588.
Proof. vm_refl. Qed.
Lemma D_15588 : decode_any W_15588 = Some (OpImm ALU_ADD 10 10 3919, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1558c : bv 32 := 0x018000ef.
Lemma F_1558c : fetch_word Plain.M.loaded_segments (0x15688 : word) = Some W_1558c.
Proof. vm_refl. Qed.
Lemma D_1558c : decode_any W_1558c = Some (Jal 1 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15590 : bv 32 := 0x00040513.
Lemma F_15590 : fetch_word Plain.M.loaded_segments (0x1568c : word) = Some W_15590.
Proof. vm_refl. Qed.
Lemma D_15590 : decode_any W_15590 = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15594 : bv 32 := 0x00813083.
Lemma F_15594 : fetch_word Plain.M.loaded_segments (0x15690 : word) = Some W_15594.
Proof. vm_refl. Qed.
Lemma D_15594 : decode_any W_15594 = Some (Load SZ8 true 1 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15598 : bv 32 := 0x00013403.
Lemma F_15598 : fetch_word Plain.M.loaded_segments (0x15694 : word) = Some W_15598.
Proof. vm_refl. Qed.
Lemma D_15598 : decode_any W_15598 = Some (Load SZ8 true 8 2 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1559c : bv 32 := 0x01010113.
Lemma F_1559c : fetch_word Plain.M.loaded_segments (0x15698 : word) = Some W_1559c.
Proof. vm_refl. Qed.
Lemma D_1559c : decode_any W_1559c = Some (OpImm ALU_ADD 2 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_155a0 : bv 32 := 0x00008067.
Lemma F_155a0 : fetch_word Plain.M.loaded_segments (0x1569c : word) = Some W_155a0.
Proof. vm_refl. Qed.
Lemma D_155a0 : decode_any W_155a0 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15640 : bv 32 := 0xff010113.
Lemma F_15640 : fetch_word Plain.M.loaded_segments (0x1573c : word) = Some W_15640.
Proof. vm_refl. Qed.
Lemma D_15640 : decode_any W_15640 = Some (OpImm ALU_ADD 2 2 4080, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15644 : bv 32 := 0x00113423.
Lemma F_15644 : fetch_word Plain.M.loaded_segments (0x15740 : word) = Some W_15644.
Proof. vm_refl. Qed.
Lemma D_15644 : decode_any W_15644 = Some (Store SZ8 2 1 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15648 : bv 32 := 0x00813023.
Lemma F_15648 : fetch_word Plain.M.loaded_segments (0x15744 : word) = Some W_15648.
Proof. vm_refl. Qed.
Lemma D_15648 : decode_any W_15648 = Some (Store SZ8 2 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1564c : bv 32 := 0x00060413.
Lemma F_1564c : fetch_word Plain.M.loaded_segments (0x15748 : word) = Some W_1564c.
Proof. vm_refl. Qed.
Lemma D_1564c : decode_any W_1564c = Some (OpImm ALU_ADD 8 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15650 : bv 32 := 0x00050613.
Lemma F_15650 : fetch_word Plain.M.loaded_segments (0x1574c : word) = Some W_15650.
Proof. vm_refl. Qed.
Lemma D_15650 : decode_any W_15650 = Some (OpImm ALU_ADD 12 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15654 : bv 32 := 0xffffc517.
Lemma F_15654 : fetch_word Plain.M.loaded_segments (0x15750 : word) = Some W_15654.
Proof. vm_refl. Qed.
Lemma D_15654 : decode_any W_15654 = Some (Auipc 10 1048572, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15658 : bv 32 := 0xe7f50513.
Lemma F_15658 : fetch_word Plain.M.loaded_segments (0x15754 : word) = Some W_15658.
Proof. vm_refl. Qed.
Lemma D_15658 : decode_any W_15658 = Some (OpImm ALU_ADD 10 10 3711, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1565c : bv 32 := 0xf49ff0ef.
Lemma F_1565c : fetch_word Plain.M.loaded_segments (0x15758 : word) = Some W_1565c.
Proof. vm_refl. Qed.
Lemma D_1565c : decode_any W_1565c = Some (Jal 1 2096968, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15660 : bv 32 := 0x00040513.
Lemma F_15660 : fetch_word Plain.M.loaded_segments (0x1575c : word) = Some W_15660.
Proof. vm_refl. Qed.
Lemma D_15660 : decode_any W_15660 = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15664 : bv 32 := 0x00813083.
Lemma F_15664 : fetch_word Plain.M.loaded_segments (0x15760 : word) = Some W_15664.
Proof. vm_refl. Qed.
Lemma D_15664 : decode_any W_15664 = Some (Load SZ8 true 1 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15668 : bv 32 := 0x00013403.
Lemma F_15668 : fetch_word Plain.M.loaded_segments (0x15764 : word) = Some W_15668.
Proof. vm_refl. Qed.
Lemma D_15668 : decode_any W_15668 = Some (Load SZ8 true 8 2 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1566c : bv 32 := 0x01010113.
Lemma F_1566c : fetch_word Plain.M.loaded_segments (0x15768 : word) = Some W_1566c.
Proof. vm_refl. Qed.
Lemma D_1566c : decode_any W_1566c = Some (OpImm ALU_ADD 2 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15670 : bv 32 := 0x00008067.
Lemma F_15670 : fetch_word Plain.M.loaded_segments (0x1576c : word) = Some W_15670.
Proof. vm_refl. Qed.
Lemma D_15670 : decode_any W_15670 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_157e8 : bv 32 := 0x02050e63.
Lemma F_157e8 : fetch_word Plain.M.loaded_segments (0x158e4 : word) = Some W_157e8.
Proof. vm_refl. Qed.
Lemma D_157e8 : decode_any W_157e8 = Some (Branch BC_EQ 10 0 60, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_157ec : bv 32 := 0xfe010113.
Lemma F_157ec : fetch_word Plain.M.loaded_segments (0x158e8 : word) = Some W_157ec.
Proof. vm_refl. Qed.
Lemma D_157ec : decode_any W_157ec = Some (OpImm ALU_ADD 2 2 4064, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_157f0 : bv 32 := 0x00113c23.
Lemma F_157f0 : fetch_word Plain.M.loaded_segments (0x158ec : word) = Some W_157f0.
Proof. vm_refl. Qed.
Lemma D_157f0 : decode_any W_157f0 = Some (Store SZ8 2 1 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_157f4 : bv 32 := 0x00813823.
Lemma F_157f4 : fetch_word Plain.M.loaded_segments (0x158f0 : word) = Some W_157f4.
Proof. vm_refl. Qed.
Lemma D_157f4 : decode_any W_157f4 = Some (Store SZ8 2 8 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_157f8 : bv 32 := 0x00913423.
Lemma F_157f8 : fetch_word Plain.M.loaded_segments (0x158f4 : word) = Some W_157f8.
Proof. vm_refl. Qed.
Lemma D_157f8 : decode_any W_157f8 = Some (Store SZ8 2 9 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_157fc : bv 32 := 0x00058493.
Lemma F_157fc : fetch_word Plain.M.loaded_segments (0x158f8 : word) = Some W_157fc.
Proof. vm_refl. Qed.
Lemma D_157fc : decode_any W_157fc = Some (OpImm ALU_ADD 9 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15800 : bv 32 := 0x00050413.
Lemma F_15800 : fetch_word Plain.M.loaded_segments (0x158fc : word) = Some W_15800.
Proof. vm_refl. Qed.
Lemma D_15800 : decode_any W_15800 = Some (OpImm ALU_ADD 8 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15804 : bv 32 := 0x00053503.
Lemma F_15804 : fetch_word Plain.M.loaded_segments (0x15900 : word) = Some W_15804.
Proof. vm_refl. Qed.
Lemma D_15804 : decode_any W_15804 = Some (Load SZ8 true 10 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15808 : bv 32 := 0x00050463.
Lemma F_15808 : fetch_word Plain.M.loaded_segments (0x15904 : word) = Some W_15808.
Proof. vm_refl. Qed.
Lemma D_15808 : decode_any W_15808 = Some (Branch BC_EQ 10 0 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15810 : bv 32 := 0x04048063.
Lemma F_15810 : fetch_word Plain.M.loaded_segments (0x1590c : word) = Some W_15810.
Proof. vm_refl. Qed.
Lemma D_15810 : decode_any W_15810 = Some (Branch BC_EQ 9 0 64, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15850 : bv 32 := 0x00000593.
Lemma F_15850 : fetch_word Plain.M.loaded_segments (0x1594c : word) = Some W_15850.
Proof. vm_refl. Qed.
Lemma D_15850 : decode_any W_15850 = Some (OpImm ALU_ADD 11 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15854 : bv 32 := 0x00000513.
Lemma F_15854 : fetch_word Plain.M.loaded_segments (0x15950 : word) = Some W_15854.
Proof. vm_refl. Qed.
Lemma D_15854 : decode_any W_15854 = Some (OpImm ALU_ADD 10 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15858 : bv 32 := 0x00b43023.
Lemma F_15858 : fetch_word Plain.M.loaded_segments (0x15954 : word) = Some W_15858.
Proof. vm_refl. Qed.
Lemma D_15858 : decode_any W_15858 = Some (Store SZ8 8 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1585c : bv 32 := 0x01813083.
Lemma F_1585c : fetch_word Plain.M.loaded_segments (0x15958 : word) = Some W_1585c.
Proof. vm_refl. Qed.
Lemma D_1585c : decode_any W_1585c = Some (Load SZ8 true 1 2 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15860 : bv 32 := 0x01013403.
Lemma F_15860 : fetch_word Plain.M.loaded_segments (0x1595c : word) = Some W_15860.
Proof. vm_refl. Qed.
Lemma D_15860 : decode_any W_15860 = Some (Load SZ8 true 8 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15864 : bv 32 := 0x00813483.
Lemma F_15864 : fetch_word Plain.M.loaded_segments (0x15960 : word) = Some W_15864.
Proof. vm_refl. Qed.
Lemma D_15864 : decode_any W_15864 = Some (Load SZ8 true 9 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15868 : bv 32 := 0x02010113.
Lemma F_15868 : fetch_word Plain.M.loaded_segments (0x15964 : word) = Some W_15868.
Proof. vm_refl. Qed.
Lemma D_15868 : decode_any W_15868 = Some (OpImm ALU_ADD 2 2 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1586c : bv 32 := 0x00008067.
Lemma F_1586c : fetch_word Plain.M.loaded_segments (0x15968 : word) = Some W_1586c.
Proof. vm_refl. Qed.
Lemma D_1586c : decode_any W_1586c = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_159b4 : bv 32 := 0xff010113.
Lemma F_159b4 : fetch_word Plain.M.loaded_segments (0x15ab0 : word) = Some W_159b4.
Proof. vm_refl. Qed.
Lemma D_159b4 : decode_any W_159b4 = Some (OpImm ALU_ADD 2 2 4080, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_159b8 : bv 32 := 0x00113423.
Lemma F_159b8 : fetch_word Plain.M.loaded_segments (0x15ab4 : word) = Some W_159b8.
Proof. vm_refl. Qed.
Lemma D_159b8 : decode_any W_159b8 = Some (Store SZ8 2 1 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_159bc : bv 32 := 0x00813023.
Lemma F_159bc : fetch_word Plain.M.loaded_segments (0x15ab8 : word) = Some W_159bc.
Proof. vm_refl. Qed.
Lemma D_159bc : decode_any W_159bc = Some (Store SZ8 2 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_159c0 : bv 32 := 0x080000ef.
Lemma F_159c0 : fetch_word Plain.M.loaded_segments (0x15abc : word) = Some W_159c0.
Proof. vm_refl. Qed.
Lemma D_159c0 : decode_any W_159c0 = Some (Jal 1 128, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_159c4 : bv 32 := 0x02050863.
Lemma F_159c4 : fetch_word Plain.M.loaded_segments (0x15ac0 : word) = Some W_159c4.
Proof. vm_refl. Qed.
Lemma D_159c4 : decode_any W_159c4 = Some (Branch BC_EQ 10 0 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_159c8 : bv 32 := 0x00456603.
Lemma F_159c8 : fetch_word Plain.M.loaded_segments (0x15ac4 : word) = Some W_159c8.
Proof. vm_refl. Qed.
Lemma D_159c8 : decode_any W_159c8 = Some (Load SZ4 false 12 10 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_159cc : bv 32 := 0x01056683.
Lemma F_159cc : fetch_word Plain.M.loaded_segments (0x15ac8 : word) = Some W_159cc.
Proof. vm_refl. Qed.
Lemma D_159cc : decode_any W_159cc = Some (Load SZ4 false 13 10 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_159d0 : bv 32 := 0x03853583.
Lemma F_159d0 : fetch_word Plain.M.loaded_segments (0x15acc : word) = Some W_159d0.
Proof. vm_refl. Qed.
Lemma D_159d0 : decode_any W_159d0 = Some (Load SZ8 true 11 10 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_159d4 : bv 32 := 0x02c68633.
Lemma F_159d4 : fetch_word Plain.M.loaded_segments (0x15ad0 : word) = Some W_159d4.
Proof. vm_refl. Qed.
Lemma D_159d4 : decode_any W_159d4 = Some (Mul M_MUL 12 13 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_159d8 : bv 32 := 0x00261613.
Lemma F_159d8 : fetch_word Plain.M.loaded_segments (0x15ad4 : word) = Some W_159d8.
Proof. vm_refl. Qed.
Lemma D_159d8 : decode_any W_159d8 = Some (ShiftImm ALU_SLL 12 12 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_159dc : bv 32 := 0x00050413.
Lemma F_159dc : fetch_word Plain.M.loaded_segments (0x15ad8 : word) = Some W_159dc.
Proof. vm_refl. Qed.
Lemma D_159dc : decode_any W_159dc = Some (OpImm ALU_ADD 8 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_159e0 : bv 32 := 0x00058513.
Lemma F_159e0 : fetch_word Plain.M.loaded_segments (0x15adc : word) = Some W_159e0.
Proof. vm_refl. Qed.
Lemma D_159e0 : decode_any W_159e0 = Some (OpImm ALU_ADD 10 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_159e4 : bv 32 := 0x00000593.
Lemma F_159e4 : fetch_word Plain.M.loaded_segments (0x15ae0 : word) = Some W_159e4.
Proof. vm_refl. Qed.
Lemma D_159e4 : decode_any W_159e4 = Some (OpImm ALU_ADD 11 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_159e8 : bv 32 := 0x0e9140ef.
Lemma F_159e8 : fetch_word Plain.M.loaded_segments (0x15ae4 : word) = Some W_159e8.
Proof. vm_refl. Qed.
Lemma D_159e8 : decode_any W_159e8 = Some (Jal 1 84200, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_159ec : bv 32 := 0x00040513.
Lemma F_159ec : fetch_word Plain.M.loaded_segments (0x15ae8 : word) = Some W_159ec.
Proof. vm_refl. Qed.
Lemma D_159ec : decode_any W_159ec = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_159f0 : bv 32 := 0x0400006f.
Lemma F_159f0 : fetch_word Plain.M.loaded_segments (0x15aec : word) = Some W_159f0.
Proof. vm_refl. Qed.
Lemma D_159f0 : decode_any W_159f0 = Some (Jal 0 64, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_159f4 : bv 32 := 0x00016517.
Lemma F_159f4 : fetch_word Plain.M.loaded_segments (0x15af0 : word) = Some W_159f4.
Proof. vm_refl. Qed.
Lemma D_159f4 : decode_any W_159f4 = Some (Auipc 10 22, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_159f8 : bv 32 := 0xf2853503.
Lemma F_159f8 : fetch_word Plain.M.loaded_segments (0x15af4 : word) = Some W_159f8.
Proof. vm_refl. Qed.
Lemma D_159f8 : decode_any W_159f8 = Some (Load SZ8 true 10 10 3880, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_159fc : bv 32 := 0x00052503.
Lemma F_159fc : fetch_word Plain.M.loaded_segments (0x15af8 : word) = Some W_159fc.
Proof. vm_refl. Qed.
Lemma D_159fc : decode_any W_159fc = Some (Load SZ4 true 10 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15a00 : bv 32 := 0x00500593.
Lemma F_15a00 : fetch_word Plain.M.loaded_segments (0x15afc : word) = Some W_15a00.
Proof. vm_refl. Qed.
Lemma D_15a00 : decode_any W_15a00 = Some (OpImm ALU_ADD 11 0 5, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15a04 : bv 32 := 0x02a5c463.
Lemma F_15a04 : fetch_word Plain.M.loaded_segments (0x15b00 : word) = Some W_15a04.
Proof. vm_refl. Qed.
Lemma D_15a04 : decode_any W_15a04 = Some (Branch BC_LT 11 10 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15a08 : bv 32 := 0xffffb517.
Lemma F_15a08 : fetch_word Plain.M.loaded_segments (0x15b04 : word) = Some W_15a08.
Proof. vm_refl. Qed.
Lemma D_15a08 : decode_any W_15a08 = Some (Auipc 10 1048571, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15a0c : bv 32 := 0xffffb597.
Lemma F_15a0c : fetch_word Plain.M.loaded_segments (0x15b08 : word) = Some W_15a0c.
Proof. vm_refl. Qed.
Lemma D_15a0c : decode_any W_15a0c = Some (Auipc 11 1048571, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15a10 : bv 32 := 0xa4650513.
Lemma F_15a10 : fetch_word Plain.M.loaded_segments (0x15b0c : word) = Some W_15a10.
Proof. vm_refl. Qed.
Lemma D_15a10 : decode_any W_15a10 = Some (OpImm ALU_ADD 10 10 2630, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15a14 : bv 32 := 0xebd58593.
Lemma F_15a14 : fetch_word Plain.M.loaded_segments (0x15b10 : word) = Some W_15a14.
Proof. vm_refl. Qed.
Lemma D_15a14 : decode_any W_15a14 = Some (OpImm ALU_ADD 11 11 3773, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15a18 : bv 32 := 0x00000613.
Lemma F_15a18 : fetch_word Plain.M.loaded_segments (0x15b14 : word) = Some W_15a18.
Proof. vm_refl. Qed.
Lemma D_15a18 : decode_any W_15a18 = Some (OpImm ALU_ADD 12 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15a1c : bv 32 := 0x00813083.
Lemma F_15a1c : fetch_word Plain.M.loaded_segments (0x15b18 : word) = Some W_15a1c.
Proof. vm_refl. Qed.
Lemma D_15a1c : decode_any W_15a1c = Some (Load SZ8 true 1 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15a20 : bv 32 := 0x00013403.
Lemma F_15a20 : fetch_word Plain.M.loaded_segments (0x15b1c : word) = Some W_15a20.
Proof. vm_refl. Qed.
Lemma D_15a20 : decode_any W_15a20 = Some (Load SZ8 true 8 2 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15a24 : bv 32 := 0x01010113.
Lemma F_15a24 : fetch_word Plain.M.loaded_segments (0x15b20 : word) = Some W_15a24.
Proof. vm_refl. Qed.
Lemma D_15a24 : decode_any W_15a24 = Some (OpImm ALU_ADD 2 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15a28 : bv 32 := 0xc19ff06f.
Lemma F_15a28 : fetch_word Plain.M.loaded_segments (0x15b24 : word) = Some W_15a28.
Proof. vm_refl. Qed.
Lemma D_15a28 : decode_any W_15a28 = Some (Jal 0 2096152, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15a30 : bv 32 := 0x00813083.
Lemma F_15a30 : fetch_word Plain.M.loaded_segments (0x15b2c : word) = Some W_15a30.
Proof. vm_refl. Qed.
Lemma D_15a30 : decode_any W_15a30 = Some (Load SZ8 true 1 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15a34 : bv 32 := 0x00013403.
Lemma F_15a34 : fetch_word Plain.M.loaded_segments (0x15b30 : word) = Some W_15a34.
Proof. vm_refl. Qed.
Lemma D_15a34 : decode_any W_15a34 = Some (Load SZ8 true 8 2 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15a38 : bv 32 := 0x01010113.
Lemma F_15a38 : fetch_word Plain.M.loaded_segments (0x15b34 : word) = Some W_15a38.
Proof. vm_refl. Qed.
Lemma D_15a38 : decode_any W_15a38 = Some (OpImm ALU_ADD 2 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15a3c : bv 32 := 0x00008067.
Lemma F_15a3c : fetch_word Plain.M.loaded_segments (0x15b38 : word) = Some W_15a3c.
Proof. vm_refl. Qed.
Lemma D_15a3c : decode_any W_15a3c = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15a40 : bv 32 := 0xfd010113.
Lemma F_15a40 : fetch_word Plain.M.loaded_segments (0x15b3c : word) = Some W_15a40.
Proof. vm_refl. Qed.
Lemma D_15a40 : decode_any W_15a40 = Some (OpImm ALU_ADD 2 2 4048, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15a44 : bv 32 := 0x02113423.
Lemma F_15a44 : fetch_word Plain.M.loaded_segments (0x15b40 : word) = Some W_15a44.
Proof. vm_refl. Qed.
Lemma D_15a44 : decode_any W_15a44 = Some (Store SZ8 2 1 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15a48 : bv 32 := 0x02813023.
Lemma F_15a48 : fetch_word Plain.M.loaded_segments (0x15b44 : word) = Some W_15a48.
Proof. vm_refl. Qed.
Lemma D_15a48 : decode_any W_15a48 = Some (Store SZ8 2 8 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15a4c : bv 32 := 0x00913c23.
Lemma F_15a4c : fetch_word Plain.M.loaded_segments (0x15b48 : word) = Some W_15a4c.
Proof. vm_refl. Qed.
Lemma D_15a4c : decode_any W_15a4c = Some (Store SZ8 2 9 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15a50 : bv 32 := 0x01213823.
Lemma F_15a50 : fetch_word Plain.M.loaded_segments (0x15b4c : word) = Some W_15a50.
Proof. vm_refl. Qed.
Lemma D_15a50 : decode_any W_15a50 = Some (Store SZ8 2 18 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15a54 : bv 32 := 0x00058493.
Lemma F_15a54 : fetch_word Plain.M.loaded_segments (0x15b50 : word) = Some W_15a54.
Proof. vm_refl. Qed.
Lemma D_15a54 : decode_any W_15a54 = Some (OpImm ALU_ADD 9 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15a58 : bv 32 := 0x124000ef.
Lemma F_15a58 : fetch_word Plain.M.loaded_segments (0x15b54 : word) = Some W_15a58.
Proof. vm_refl. Qed.
Lemma D_15a58 : decode_any W_15a58 = Some (Jal 1 292, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15a5c : bv 32 := 0x02050e63.
Lemma F_15a5c : fetch_word Plain.M.loaded_segments (0x15b58 : word) = Some W_15a5c.
Proof. vm_refl. Qed.
Lemma D_15a5c : decode_any W_15a5c = Some (Branch BC_EQ 10 0 60, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15a60 : bv 32 := 0x00050413.
Lemma F_15a60 : fetch_word Plain.M.loaded_segments (0x15b5c : word) = Some W_15a60.
Proof. vm_refl. Qed.
Lemma D_15a60 : decode_any W_15a60 = Some (OpImm ALU_ADD 8 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15a64 : bv 32 := 0x01052503.
Lemma F_15a64 : fetch_word Plain.M.loaded_segments (0x15b60 : word) = Some W_15a64.
Proof. vm_refl. Qed.
Lemma D_15a64 : decode_any W_15a64 = Some (Load SZ4 true 10 10 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15a68 : bv 32 := 0x00017597.
Lemma F_15a68 : fetch_word Plain.M.loaded_segments (0x15b64 : word) = Some W_15a68.
Proof. vm_refl. Qed.
Lemma D_15a68 : decode_any W_15a68 = Some (Auipc 11 23, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15a6c : bv 32 := 0xf3458913.
Lemma F_15a6c : fetch_word Plain.M.loaded_segments (0x15b68 : word) = Some W_15a6c.
Proof. vm_refl. Qed.
Lemma D_15a6c : decode_any W_15a6c = Some (OpImm ALU_ADD 18 11 3892, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15a70 : bv 32 := 0x00093583.
Lemma F_15a70 : fetch_word Plain.M.loaded_segments (0x15b6c : word) = Some W_15a70.
Proof. vm_refl. Qed.
Lemma D_15a70 : decode_any W_15a70 = Some (Load SZ8 true 11 18 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15a74 : bv 32 := 0x02a48533.
Lemma F_15a74 : fetch_word Plain.M.loaded_segments (0x15b70 : word) = Some W_15a74.
Proof. vm_refl. Qed.
Lemma D_15a74 : decode_any W_15a74 = Some (Mul M_MUL 10 9 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15a78 : bv 32 := 0x00251513.
Lemma F_15a78 : fetch_word Plain.M.loaded_segments (0x15b74 : word) = Some W_15a78.
Proof. vm_refl. Qed.
Lemma D_15a78 : decode_any W_15a78 = Some (ShiftImm ALU_SLL 10 10 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15a7c : bv 32 := 0x000580e7.
Lemma F_15a7c : fetch_word Plain.M.loaded_segments (0x15b78 : word) = Some W_15a7c.
Proof. vm_refl. Qed.
Lemma D_15a7c : decode_any W_15a7c = Some (Jalr 1 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15a80 : bv 32 := 0x04050c63.
Lemma F_15a80 : fetch_word Plain.M.loaded_segments (0x15b7c : word) = Some W_15a80.
Proof. vm_refl. Qed.
Lemma D_15a80 : decode_any W_15a80 = Some (Branch BC_EQ 10 0 88, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15a84 : bv 32 := 0x02a43c23.
Lemma F_15a84 : fetch_word Plain.M.loaded_segments (0x15b80 : word) = Some W_15a84.
Proof. vm_refl. Qed.
Lemma D_15a84 : decode_any W_15a84 = Some (Store SZ8 8 10 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15a88 : bv 32 := 0x00040513.
Lemma F_15a88 : fetch_word Plain.M.loaded_segments (0x15b84 : word) = Some W_15a88.
Proof. vm_refl. Qed.
Lemma D_15a88 : decode_any W_15a88 = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15a8c : bv 32 := 0x00000593.
Lemma F_15a8c : fetch_word Plain.M.loaded_segments (0x15b88 : word) = Some W_15a8c.
Proof. vm_refl. Qed.
Lemma D_15a8c : decode_any W_15a8c = Some (OpImm ALU_ADD 11 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15a90 : bv 32 := 0x279010ef.
Lemma F_15a90 : fetch_word Plain.M.loaded_segments (0x15b8c : word) = Some W_15a90.
Proof. vm_refl. Qed.
Lemma D_15a90 : decode_any W_15a90 = Some (Jal 1 6776, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15a94 : bv 32 := 0x0cc0006f.
Lemma F_15a94 : fetch_word Plain.M.loaded_segments (0x15b90 : word) = Some W_15a94.
Proof. vm_refl. Qed.
Lemma D_15a94 : decode_any W_15a94 = Some (Jal 0 204, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15a98 : bv 32 := 0x00016517.
Lemma F_15a98 : fetch_word Plain.M.loaded_segments (0x15b94 : word) = Some W_15a98.
Proof. vm_refl. Qed.
Lemma D_15a98 : decode_any W_15a98 = Some (Auipc 10 22, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15a9c : bv 32 := 0xe8453503.
Lemma F_15a9c : fetch_word Plain.M.loaded_segments (0x15b98 : word) = Some W_15a9c.
Proof. vm_refl. Qed.
Lemma D_15a9c : decode_any W_15a9c = Some (Load SZ8 true 10 10 3716, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15aa0 : bv 32 := 0x00052503.
Lemma F_15aa0 : fetch_word Plain.M.loaded_segments (0x15b9c : word) = Some W_15aa0.
Proof. vm_refl. Qed.
Lemma D_15aa0 : decode_any W_15aa0 = Some (Load SZ4 true 10 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15aa4 : bv 32 := 0x00500593.
Lemma F_15aa4 : fetch_word Plain.M.loaded_segments (0x15ba0 : word) = Some W_15aa4.
Proof. vm_refl. Qed.
Lemma D_15aa4 : decode_any W_15aa4 = Some (OpImm ALU_ADD 11 0 5, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15aa8 : bv 32 := 0x0aa5ca63.
Lemma F_15aa8 : fetch_word Plain.M.loaded_segments (0x15ba4 : word) = Some W_15aa8.
Proof. vm_refl. Qed.
Lemma D_15aa8 : decode_any W_15aa8 = Some (Branch BC_LT 11 10 180, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15aac : bv 32 := 0xffffb517.
Lemma F_15aac : fetch_word Plain.M.loaded_segments (0x15ba8 : word) = Some W_15aac.
Proof. vm_refl. Qed.
Lemma D_15aac : decode_any W_15aac = Some (Auipc 10 1048571, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15ab0 : bv 32 := 0xffffb597.
Lemma F_15ab0 : fetch_word Plain.M.loaded_segments (0x15bac : word) = Some W_15ab0.
Proof. vm_refl. Qed.
Lemma D_15ab0 : decode_any W_15ab0 = Some (Auipc 11 1048571, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15ab4 : bv 32 := 0x9a250513.
Lemma F_15ab4 : fetch_word Plain.M.loaded_segments (0x15bb0 : word) = Some W_15ab4.
Proof. vm_refl. Qed.
Lemma D_15ab4 : decode_any W_15ab4 = Some (OpImm ALU_ADD 10 10 2466, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15ab8 : bv 32 := 0xbde58593.
Lemma F_15ab8 : fetch_word Plain.M.loaded_segments (0x15bb4 : word) = Some W_15ab8.
Proof. vm_refl. Qed.
Lemma D_15ab8 : decode_any W_15ab8 = Some (OpImm ALU_ADD 11 11 3038, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15abc : bv 32 := 0x00000613.
Lemma F_15abc : fetch_word Plain.M.loaded_segments (0x15bb8 : word) = Some W_15abc.
Proof. vm_refl. Qed.
Lemma D_15abc : decode_any W_15abc = Some (OpImm ALU_ADD 12 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15ac0 : bv 32 := 0x02813083.
Lemma F_15ac0 : fetch_word Plain.M.loaded_segments (0x15bbc : word) = Some W_15ac0.
Proof. vm_refl. Qed.
Lemma D_15ac0 : decode_any W_15ac0 = Some (Load SZ8 true 1 2 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15ac4 : bv 32 := 0x02013403.
Lemma F_15ac4 : fetch_word Plain.M.loaded_segments (0x15bc0 : word) = Some W_15ac4.
Proof. vm_refl. Qed.
Lemma D_15ac4 : decode_any W_15ac4 = Some (Load SZ8 true 8 2 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15ac8 : bv 32 := 0x01813483.
Lemma F_15ac8 : fetch_word Plain.M.loaded_segments (0x15bc4 : word) = Some W_15ac8.
Proof. vm_refl. Qed.
Lemma D_15ac8 : decode_any W_15ac8 = Some (Load SZ8 true 9 2 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15acc : bv 32 := 0x01013903.
Lemma F_15acc : fetch_word Plain.M.loaded_segments (0x15bc8 : word) = Some W_15acc.
Proof. vm_refl. Qed.
Lemma D_15acc : decode_any W_15acc = Some (Load SZ8 true 18 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15ad0 : bv 32 := 0x03010113.
Lemma F_15ad0 : fetch_word Plain.M.loaded_segments (0x15bcc : word) = Some W_15ad0.
Proof. vm_refl. Qed.
Lemma D_15ad0 : decode_any W_15ad0 = Some (OpImm ALU_ADD 2 2 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15ad4 : bv 32 := 0xb6dff06f.
Lemma F_15ad4 : fetch_word Plain.M.loaded_segments (0x15bd0 : word) = Some W_15ad4.
Proof. vm_refl. Qed.
Lemma D_15ad4 : decode_any W_15ad4 = Some (Jal 0 2095980, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15ad8 : bv 32 := 0x01440513.
Lemma F_15ad8 : fetch_word Plain.M.loaded_segments (0x15bd4 : word) = Some W_15ad8.
Proof. vm_refl. Qed.
Lemma D_15ad8 : decode_any W_15ad8 = Some (OpImm ALU_ADD 10 8 20, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15adc : bv 32 := 0xfff00593.
Lemma F_15adc : fetch_word Plain.M.loaded_segments (0x15bd8 : word) = Some W_15adc.
Proof. vm_refl. Qed.
Lemma D_15adc : decode_any W_15adc = Some (OpImm ALU_ADD 11 0 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15ae0 : bv 32 := 0x06b5252f.
Lemma F_15ae0 : fetch_word Plain.M.loaded_segments (0x15bdc : word) = Some W_15ae0.
Proof. vm_refl. Qed.
Lemma D_15ae0 : decode_any W_15ae0 = Some (Amo AMO_ADD AW true true 10 10 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15ae4 : bv 32 := 0x00100593.
Lemma F_15ae4 : fetch_word Plain.M.loaded_segments (0x15be0 : word) = Some W_15ae4.
Proof. vm_refl. Qed.
Lemma D_15ae4 : decode_any W_15ae4 = Some (OpImm ALU_ADD 11 0 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15ae8 : bv 32 := 0x04b51063.
Lemma F_15ae8 : fetch_word Plain.M.loaded_segments (0x15be4 : word) = Some W_15ae8.
Proof. vm_refl. Qed.
Lemma D_15ae8 : decode_any W_15ae8 = Some (Branch BC_NE 10 11 64, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15aec : bv 32 := 0x03843503.
Lemma F_15aec : fetch_word Plain.M.loaded_segments (0x15be8 : word) = Some W_15aec.
Proof. vm_refl. Qed.
Lemma D_15aec : decode_any W_15aec = Some (Load SZ8 true 10 8 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15af0 : bv 32 := 0x00050663.
Lemma F_15af0 : fetch_word Plain.M.loaded_segments (0x15bec : word) = Some W_15af0.
Proof. vm_refl. Qed.
Lemma D_15af0 : decode_any W_15af0 = Some (Branch BC_EQ 10 0 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15afc : bv 32 := 0x02843503.
Lemma F_15afc : fetch_word Plain.M.loaded_segments (0x15bf8 : word) = Some W_15afc.
Proof. vm_refl. Qed.
Lemma D_15afc : decode_any W_15afc = Some (Load SZ8 true 10 8 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15b00 : bv 32 := 0x00050463.
Lemma F_15b00 : fetch_word Plain.M.loaded_segments (0x15bfc : word) = Some W_15b00.
Proof. vm_refl. Qed.
Lemma D_15b00 : decode_any W_15b00 = Some (Branch BC_EQ 10 0 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15b08 : bv 32 := 0x03043503.
Lemma F_15b08 : fetch_word Plain.M.loaded_segments (0x15c04 : word) = Some W_15b08.
Proof. vm_refl. Qed.
Lemma D_15b08 : decode_any W_15b08 = Some (Load SZ8 true 10 8 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15b0c : bv 32 := 0x00a13423.
Lemma F_15b0c : fetch_word Plain.M.loaded_segments (0x15c08 : word) = Some W_15b0c.
Proof. vm_refl. Qed.
Lemma D_15b0c : decode_any W_15b0c = Some (Store SZ8 2 10 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15b10 : bv 32 := 0x00050863.
Lemma F_15b10 : fetch_word Plain.M.loaded_segments (0x15c0c : word) = Some W_15b10.
Proof. vm_refl. Qed.
Lemma D_15b10 : decode_any W_15b10 = Some (Branch BC_EQ 10 0 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15b20 : bv 32 := 0x00040513.
Lemma F_15b20 : fetch_word Plain.M.loaded_segments (0x15c1c : word) = Some W_15b20.
Proof. vm_refl. Qed.
Lemma D_15b20 : decode_any W_15b20 = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15b24 : bv 32 := 0x2740d0ef.
Lemma F_15b24 : fetch_word Plain.M.loaded_segments (0x15c20 : word) = Some W_15b24.
Proof. vm_refl. Qed.
Lemma D_15b24 : decode_any W_15b24 = Some (Jal 1 53876, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15b28 : bv 32 := 0x00016517.
Lemma F_15b28 : fetch_word Plain.M.loaded_segments (0x15c24 : word) = Some W_15b28.
Proof. vm_refl. Qed.
Lemma D_15b28 : decode_any W_15b28 = Some (Auipc 10 22, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15b2c : bv 32 := 0xdf453503.
Lemma F_15b2c : fetch_word Plain.M.loaded_segments (0x15c28 : word) = Some W_15b2c.
Proof. vm_refl. Qed.
Lemma D_15b2c : decode_any W_15b2c = Some (Load SZ8 true 10 10 3572, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15b30 : bv 32 := 0x00052503.
Lemma F_15b30 : fetch_word Plain.M.loaded_segments (0x15c2c : word) = Some W_15b30.
Proof. vm_refl. Qed.
Lemma D_15b30 : decode_any W_15b30 = Some (Load SZ4 true 10 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15b34 : bv 32 := 0x00500593.
Lemma F_15b34 : fetch_word Plain.M.loaded_segments (0x15c30 : word) = Some W_15b34.
Proof. vm_refl. Qed.
Lemma D_15b34 : decode_any W_15b34 = Some (OpImm ALU_ADD 11 0 5, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15b38 : bv 32 := 0x02a5c263.
Lemma F_15b38 : fetch_word Plain.M.loaded_segments (0x15c34 : word) = Some W_15b38.
Proof. vm_refl. Qed.
Lemma D_15b38 : decode_any W_15b38 = Some (Branch BC_LT 11 10 36, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15b3c : bv 32 := 0xffffb517.
Lemma F_15b3c : fetch_word Plain.M.loaded_segments (0x15c38 : word) = Some W_15b3c.
Proof. vm_refl. Qed.
Lemma D_15b3c : decode_any W_15b3c = Some (Auipc 10 1048571, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15b40 : bv 32 := 0xffffb597.
Lemma F_15b40 : fetch_word Plain.M.loaded_segments (0x15c3c : word) = Some W_15b40.
Proof. vm_refl. Qed.
Lemma D_15b40 : decode_any W_15b40 = Some (Auipc 11 1048571, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15b44 : bv 32 := 0x5d350513.
Lemma F_15b44 : fetch_word Plain.M.loaded_segments (0x15c40 : word) = Some W_15b44.
Proof. vm_refl. Qed.
Lemma D_15b44 : decode_any W_15b44 = Some (OpImm ALU_ADD 10 10 1491, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15b48 : bv 32 := 0xb4e58593.
Lemma F_15b48 : fetch_word Plain.M.loaded_segments (0x15c44 : word) = Some W_15b48.
Proof. vm_refl. Qed.
Lemma D_15b48 : decode_any W_15b48 = Some (OpImm ALU_ADD 11 11 2894, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15b4c : bv 32 := 0x00000613.
Lemma F_15b4c : fetch_word Plain.M.loaded_segments (0x15c48 : word) = Some W_15b4c.
Proof. vm_refl. Qed.
Lemma D_15b4c : decode_any W_15b4c = Some (OpImm ALU_ADD 12 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15b50 : bv 32 := 0xaf1ff0ef.
Lemma F_15b50 : fetch_word Plain.M.loaded_segments (0x15c4c : word) = Some W_15b50.
Proof. vm_refl. Qed.
Lemma D_15b50 : decode_any W_15b50 = Some (Jal 1 2095856, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15b54 : bv 32 := 0x00050413.
Lemma F_15b54 : fetch_word Plain.M.loaded_segments (0x15c50 : word) = Some W_15b54.
Proof. vm_refl. Qed.
Lemma D_15b54 : decode_any W_15b54 = Some (OpImm ALU_ADD 8 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15b58 : bv 32 := 0x0080006f.
Lemma F_15b58 : fetch_word Plain.M.loaded_segments (0x15c54 : word) = Some W_15b58.
Proof. vm_refl. Qed.
Lemma D_15b58 : decode_any W_15b58 = Some (Jal 0 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15b60 : bv 32 := 0x00040513.
Lemma F_15b60 : fetch_word Plain.M.loaded_segments (0x15c5c : word) = Some W_15b60.
Proof. vm_refl. Qed.
Lemma D_15b60 : decode_any W_15b60 = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15b64 : bv 32 := 0x02813083.
Lemma F_15b64 : fetch_word Plain.M.loaded_segments (0x15c60 : word) = Some W_15b64.
Proof. vm_refl. Qed.
Lemma D_15b64 : decode_any W_15b64 = Some (Load SZ8 true 1 2 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15b68 : bv 32 := 0x02013403.
Lemma F_15b68 : fetch_word Plain.M.loaded_segments (0x15c64 : word) = Some W_15b68.
Proof. vm_refl. Qed.
Lemma D_15b68 : decode_any W_15b68 = Some (Load SZ8 true 8 2 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15b6c : bv 32 := 0x01813483.
Lemma F_15b6c : fetch_word Plain.M.loaded_segments (0x15c68 : word) = Some W_15b6c.
Proof. vm_refl. Qed.
Lemma D_15b6c : decode_any W_15b6c = Some (Load SZ8 true 9 2 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15b70 : bv 32 := 0x01013903.
Lemma F_15b70 : fetch_word Plain.M.loaded_segments (0x15c6c : word) = Some W_15b70.
Proof. vm_refl. Qed.
Lemma D_15b70 : decode_any W_15b70 = Some (Load SZ8 true 18 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15b74 : bv 32 := 0x03010113.
Lemma F_15b74 : fetch_word Plain.M.loaded_segments (0x15c70 : word) = Some W_15b74.
Proof. vm_refl. Qed.
Lemma D_15b74 : decode_any W_15b74 = Some (OpImm ALU_ADD 2 2 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15b78 : bv 32 := 0x00008067.
Lemma F_15b78 : fetch_word Plain.M.loaded_segments (0x15c74 : word) = Some W_15b78.
Proof. vm_refl. Qed.
Lemma D_15b78 : decode_any W_15b78 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.
