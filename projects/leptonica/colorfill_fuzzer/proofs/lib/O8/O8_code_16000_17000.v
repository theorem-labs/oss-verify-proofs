(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
(* [comment removed for export] *)

From OSSVerify.Proofs.leptonica.colorfill_fuzzer.lib.H Require GcFlushS8.   (* [comment removed for export] *)
From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.leptonica.colorfill_fuzzer.images Require Import Plain.
Open Scope bv_scope.
#[local] Hint Extern 0 (BvWf _ _) => (lazymatch goal with |- BvWf ?n ?v => is_closed_term n; is_closed_term v end; exact I) : typeclass_instances.   (* [comment removed for export] *)

(* [comment removed for export] *)
Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

(* [comment removed for export] *)



(* [comment removed for export] *)
Definition W_160b0 : bv 32 := 0x0040006f.
Lemma F_160b0 : fetch_word Plain.M.loaded_segments (0x161b4 : word) = Some W_160b0.
Proof. vm_refl. Qed.
Lemma D_160b0 : decode_any W_160b0 = Some (Jal 0 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16500 : bv 32 := 0xf9010113.
Lemma F_16500 : fetch_word Plain.M.loaded_segments (0x16604 : word) = Some W_16500.
Proof. vm_refl. Qed.
Lemma D_16500 : decode_any W_16500 = Some (OpImm ALU_ADD 2 2 3984, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16504 : bv 32 := 0x06113423.
Lemma F_16504 : fetch_word Plain.M.loaded_segments (0x16608 : word) = Some W_16504.
Proof. vm_refl. Qed.
Lemma D_16504 : decode_any W_16504 = Some (Store SZ8 2 1 104, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16508 : bv 32 := 0x06813023.
Lemma F_16508 : fetch_word Plain.M.loaded_segments (0x1660c : word) = Some W_16508.
Proof. vm_refl. Qed.
Lemma D_16508 : decode_any W_16508 = Some (Store SZ8 2 8 96, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1650c : bv 32 := 0x04913c23.
Lemma F_1650c : fetch_word Plain.M.loaded_segments (0x16610 : word) = Some W_1650c.
Proof. vm_refl. Qed.
Lemma D_1650c : decode_any W_1650c = Some (Store SZ8 2 9 88, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16510 : bv 32 := 0x05213823.
Lemma F_16510 : fetch_word Plain.M.loaded_segments (0x16614 : word) = Some W_16510.
Proof. vm_refl. Qed.
Lemma D_16510 : decode_any W_16510 = Some (Store SZ8 2 18 80, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16514 : bv 32 := 0x05313423.
Lemma F_16514 : fetch_word Plain.M.loaded_segments (0x16618 : word) = Some W_16514.
Proof. vm_refl. Qed.
Lemma D_16514 : decode_any W_16514 = Some (Store SZ8 2 19 72, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16518 : bv 32 := 0x05413023.
Lemma F_16518 : fetch_word Plain.M.loaded_segments (0x1661c : word) = Some W_16518.
Proof. vm_refl. Qed.
Lemma D_16518 : decode_any W_16518 = Some (Store SZ8 2 20 64, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1651c : bv 32 := 0x03513c23.
Lemma F_1651c : fetch_word Plain.M.loaded_segments (0x16620 : word) = Some W_1651c.
Proof. vm_refl. Qed.
Lemma D_1651c : decode_any W_1651c = Some (Store SZ8 2 21 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16520 : bv 32 := 0x03613823.
Lemma F_16520 : fetch_word Plain.M.loaded_segments (0x16624 : word) = Some W_16520.
Proof. vm_refl. Qed.
Lemma D_16520 : decode_any W_16520 = Some (Store SZ8 2 22 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16524 : bv 32 := 0x03713423.
Lemma F_16524 : fetch_word Plain.M.loaded_segments (0x16628 : word) = Some W_16524.
Proof. vm_refl. Qed.
Lemma D_16524 : decode_any W_16524 = Some (Store SZ8 2 23 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16528 : bv 32 := 0x03813023.
Lemma F_16528 : fetch_word Plain.M.loaded_segments (0x1662c : word) = Some W_16528.
Proof. vm_refl. Qed.
Lemma D_16528 : decode_any W_16528 = Some (Store SZ8 2 24 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1652c : bv 32 := 0x01913c23.
Lemma F_1652c : fetch_word Plain.M.loaded_segments (0x16630 : word) = Some W_1652c.
Proof. vm_refl. Qed.
Lemma D_1652c : decode_any W_1652c = Some (Store SZ8 2 25 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16530 : bv 32 := 0x01a13823.
Lemma F_16530 : fetch_word Plain.M.loaded_segments (0x16634 : word) = Some W_16530.
Proof. vm_refl. Qed.
Lemma D_16530 : decode_any W_16530 = Some (Store SZ8 2 26 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16534 : bv 32 := 0x0a050c63.
Lemma F_16534 : fetch_word Plain.M.loaded_segments (0x16638 : word) = Some W_16534.
Proof. vm_refl. Qed.
Lemma D_16534 : decode_any W_16534 = Some (Branch BC_EQ 10 0 184, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16538 : bv 32 := 0x00060413.
Lemma F_16538 : fetch_word Plain.M.loaded_segments (0x1663c : word) = Some W_16538.
Proof. vm_refl. Qed.
Lemma D_16538 : decode_any W_16538 = Some (OpImm ALU_ADD 8 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1653c : bv 32 := 0x00058493.
Lemma F_1653c : fetch_word Plain.M.loaded_segments (0x16640 : word) = Some W_1653c.
Proof. vm_refl. Qed.
Lemma D_1653c : decode_any W_1653c = Some (OpImm ALU_ADD 9 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16540 : bv 32 := 0x00050913.
Lemma F_16540 : fetch_word Plain.M.loaded_segments (0x16644 : word) = Some W_16540.
Proof. vm_refl. Qed.
Lemma D_16540 : decode_any W_16540 = Some (OpImm ALU_ADD 18 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16544 : bv 32 := 0xf25fe0ef.
Lemma F_16544 : fetch_word Plain.M.loaded_segments (0x16648 : word) = Some W_16544.
Proof. vm_refl. Qed.
Lemma D_16544 : decode_any W_16544 = Some (Jal 1 2092836, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16548 : bv 32 := 0x02000593.
Lemma F_16548 : fetch_word Plain.M.loaded_segments (0x1664c : word) = Some W_16548.
Proof. vm_refl. Qed.
Lemma D_16548 : decode_any W_16548 = Some (OpImm ALU_ADD 11 0 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1654c : bv 32 := 0x0cb51463.
Lemma F_1654c : fetch_word Plain.M.loaded_segments (0x16650 : word) = Some W_1654c.
Proof. vm_refl. Qed.
Lemma D_1654c : decode_any W_1654c = Some (Branch BC_NE 10 11 200, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16550 : bv 32 := 0x00c10593.
Lemma F_16550 : fetch_word Plain.M.loaded_segments (0x16654 : word) = Some W_16550.
Proof. vm_refl. Qed.
Lemma D_16550 : decode_any W_16550 = Some (OpImm ALU_ADD 11 2 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16554 : bv 32 := 0x00810613.
Lemma F_16554 : fetch_word Plain.M.loaded_segments (0x16658 : word) = Some W_16554.
Proof. vm_refl. Qed.
Lemma D_16554 : decode_any W_16554 = Some (OpImm ALU_ADD 12 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16558 : bv 32 := 0x00090513.
Lemma F_16558 : fetch_word Plain.M.loaded_segments (0x1665c : word) = Some W_16558.
Proof. vm_refl. Qed.
Lemma D_16558 : decode_any W_16558 = Some (OpImm ALU_ADD 10 18 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1655c : bv 32 := 0x00000693.
Lemma F_1655c : fetch_word Plain.M.loaded_segments (0x16660 : word) = Some W_1655c.
Proof. vm_refl. Qed.
Lemma D_1655c : decode_any W_1655c = Some (OpImm ALU_ADD 13 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16560 : bv 32 := 0xd1dfe0ef.
Lemma F_16560 : fetch_word Plain.M.loaded_segments (0x16664 : word) = Some W_16560.
Proof. vm_refl. Qed.
Lemma D_16560 : decode_any W_16560 = Some (Jal 1 2092316, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16564 : bv 32 := 0x00c12503.
Lemma F_16564 : fetch_word Plain.M.loaded_segments (0x16668 : word) = Some W_16564.
Proof. vm_refl. Qed.
Lemma D_16564 : decode_any W_16564 = Some (Load SZ4 true 10 2 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16568 : bv 32 := 0x029549bb.
Lemma F_16568 : fetch_word Plain.M.loaded_segments (0x1666c : word) = Some W_16568.
Proof. vm_refl. Qed.
Lemma D_16568 : decode_any W_16568 = Some (Mul32 M_DIV 19 10 9, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1656c : bv 32 := 0x00a00513.
Lemma F_1656c : fetch_word Plain.M.loaded_segments (0x16670 : word) = Some W_1656c.
Proof. vm_refl. Qed.
Lemma D_1656c : decode_any W_1656c = Some (OpImm ALU_ADD 10 0 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16570 : bv 32 := 0x10a9c263.
Lemma F_16570 : fetch_word Plain.M.loaded_segments (0x16674 : word) = Some W_16570.
Proof. vm_refl. Qed.
Lemma D_16570 : decode_any W_16570 = Some (Branch BC_LT 19 10 260, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16574 : bv 32 := 0x00812503.
Lemma F_16574 : fetch_word Plain.M.loaded_segments (0x16678 : word) = Some W_16574.
Proof. vm_refl. Qed.
Lemma D_16574 : decode_any W_16574 = Some (Load SZ4 true 10 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16578 : bv 32 := 0x02854abb.
Lemma F_16578 : fetch_word Plain.M.loaded_segments (0x1667c : word) = Some W_16578.
Proof. vm_refl. Qed.
Lemma D_16578 : decode_any W_16578 = Some (Mul32 M_DIV 21 10 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1657c : bv 32 := 0x00900513.
Lemma F_1657c : fetch_word Plain.M.loaded_segments (0x16680 : word) = Some W_1657c.
Proof. vm_refl. Qed.
Lemma D_1657c : decode_any W_1657c = Some (OpImm ALU_ADD 10 0 9, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16580 : bv 32 := 0x0f555a63.
Lemma F_16580 : fetch_word Plain.M.loaded_segments (0x16684 : word) = Some W_16580.
Proof. vm_refl. Qed.
Lemma D_16580 : decode_any W_16580 = Some (Branch BC_GE 10 21 244, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16584 : bv 32 := 0x02940a3b.
Lemma F_16584 : fetch_word Plain.M.loaded_segments (0x16688 : word) = Some W_16584.
Proof. vm_refl. Qed.
Lemma D_16584 : decode_any W_16584 = Some (Mul32 M_MUL 20 8 9, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16588 : bv 32 := 0x000a0513.
Lemma F_16588 : fetch_word Plain.M.loaded_segments (0x1668c : word) = Some W_16588.
Proof. vm_refl. Qed.
Lemma D_16588 : decode_any W_16588 = Some (OpImm ALU_ADD 10 20 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1658c : bv 32 := 0x974fe0ef.
Lemma F_1658c : fetch_word Plain.M.loaded_segments (0x16690 : word) = Some W_1658c.
Proof. vm_refl. Qed.
Lemma D_1658c : decode_any W_1658c = Some (Jal 1 2089332, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16590 : bv 32 := 0x00050b13.
Lemma F_16590 : fetch_word Plain.M.loaded_segments (0x16694 : word) = Some W_16590.
Proof. vm_refl. Qed.
Lemma D_16590 : decode_any W_16590 = Some (OpImm ALU_ADD 22 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16594 : bv 32 := 0x10805c63.
Lemma F_16594 : fetch_word Plain.M.loaded_segments (0x16698 : word) = Some W_16594.
Proof. vm_refl. Qed.
Lemma D_16594 : decode_any W_16594 = Some (Branch BC_GE 0 8 280, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16598 : bv 32 := 0x00000c93.
Lemma F_16598 : fetch_word Plain.M.loaded_segments (0x1669c : word) = Some W_16598.
Proof. vm_refl. Qed.
Lemma D_16598 : decode_any W_16598 = Some (OpImm ALU_ADD 25 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1659c : bv 32 := 0x00c0006f.
Lemma F_1659c : fetch_word Plain.M.loaded_segments (0x166a0 : word) = Some W_1659c.
Proof. vm_refl. Qed.
Lemma D_1659c : decode_any W_1659c = Some (Jal 0 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_165a0 : bv 32 := 0x001c8c9b.
Lemma F_165a0 : fetch_word Plain.M.loaded_segments (0x166a4 : word) = Some W_165a0.
Proof. vm_refl. Qed.
Lemma D_165a0 : decode_any W_165a0 = Some (OpImm32 25 25 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_165a4 : bv 32 := 0x108c8463.
Lemma F_165a4 : fetch_word Plain.M.loaded_segments (0x166a8 : word) = Some W_165a4.
Proof. vm_refl. Qed.
Lemma D_165a4 : decode_any W_165a4 = Some (Branch BC_EQ 25 8 264, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_165a8 : bv 32 := 0xfe905ce3.
Lemma F_165a8 : fetch_word Plain.M.loaded_segments (0x166ac : word) = Some W_165a8.
Proof. vm_refl. Qed.
Lemma D_165a8 : decode_any W_165a8 = Some (Branch BC_GE 0 9 8184, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_165ac : bv 32 := 0x00000b93.
Lemma F_165ac : fetch_word Plain.M.loaded_segments (0x166b0 : word) = Some W_165ac.
Proof. vm_refl. Qed.
Lemma D_165ac : decode_any W_165ac = Some (OpImm ALU_ADD 23 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_165b0 : bv 32 := 0x035c8c3b.
Lemma F_165b0 : fetch_word Plain.M.loaded_segments (0x166b4 : word) = Some W_165b0.
Proof. vm_refl. Qed.
Lemma D_165b0 : decode_any W_165b0 = Some (Mul32 M_MUL 24 25 21, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_165b4 : bv 32 := 0x00048d13.
Lemma F_165b4 : fetch_word Plain.M.loaded_segments (0x166b8 : word) = Some W_165b4.
Proof. vm_refl. Qed.
Lemma D_165b4 : decode_any W_165b4 = Some (OpImm ALU_ADD 26 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_165b8 : bv 32 := 0x000b8513.
Lemma F_165b8 : fetch_word Plain.M.loaded_segments (0x166bc : word) = Some W_165b8.
Proof. vm_refl. Qed.
Lemma D_165b8 : decode_any W_165b8 = Some (OpImm ALU_ADD 10 23 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_165bc : bv 32 := 0x000c0593.
Lemma F_165bc : fetch_word Plain.M.loaded_segments (0x166c0 : word) = Some W_165bc.
Proof. vm_refl. Qed.
Lemma D_165bc : decode_any W_165bc = Some (OpImm ALU_ADD 11 24 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_165c0 : bv 32 := 0x00098613.
Lemma F_165c0 : fetch_word Plain.M.loaded_segments (0x166c4 : word) = Some W_165c0.
Proof. vm_refl. Qed.
Lemma D_165c0 : decode_any W_165c0 = Some (OpImm ALU_ADD 12 19 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_165c4 : bv 32 := 0x000a8693.
Lemma F_165c4 : fetch_word Plain.M.loaded_segments (0x166c8 : word) = Some W_165c4.
Proof. vm_refl. Qed.
Lemma D_165c4 : decode_any W_165c4 = Some (OpImm ALU_ADD 13 21 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_165c8 : bv 32 := 0xfb9fd0ef.
Lemma F_165c8 : fetch_word Plain.M.loaded_segments (0x166cc : word) = Some W_165c8.
Proof. vm_refl. Qed.
Lemma D_165c8 : decode_any W_165c8 = Some (Jal 1 2088888, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_165cc : bv 32 := 0x00050593.
Lemma F_165cc : fetch_word Plain.M.loaded_segments (0x166d0 : word) = Some W_165cc.
Proof. vm_refl. Qed.
Lemma D_165cc : decode_any W_165cc = Some (OpImm ALU_ADD 11 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_165d0 : bv 32 := 0x000b0513.
Lemma F_165d0 : fetch_word Plain.M.loaded_segments (0x166d4 : word) = Some W_165d0.
Proof. vm_refl. Qed.
Lemma D_165d0 : decode_any W_165d0 = Some (OpImm ALU_ADD 10 22 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_165d4 : bv 32 := 0x00000613.
Lemma F_165d4 : fetch_word Plain.M.loaded_segments (0x166d8 : word) = Some W_165d4.
Proof. vm_refl. Qed.
Lemma D_165d4 : decode_any W_165d4 = Some (OpImm ALU_ADD 12 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_165d8 : bv 32 := 0xb84fe0ef.
Lemma F_165d8 : fetch_word Plain.M.loaded_segments (0x166dc : word) = Some W_165d8.
Proof. vm_refl. Qed.
Lemma D_165d8 : decode_any W_165d8 = Some (Jal 1 2089860, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_165dc : bv 32 := 0xfffd0d1b.
Lemma F_165dc : fetch_word Plain.M.loaded_segments (0x166e0 : word) = Some W_165dc.
Proof. vm_refl. Qed.
Lemma D_165dc : decode_any W_165dc = Some (OpImm32 26 26 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_165e0 : bv 32 := 0x013b8bbb.
Lemma F_165e0 : fetch_word Plain.M.loaded_segments (0x166e4 : word) = Some W_165e0.
Proof. vm_refl. Qed.
Lemma D_165e0 : decode_any W_165e0 = Some (Op32 ALU_ADD 23 23 19, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_165e4 : bv 32 := 0xfc0d1ae3.
Lemma F_165e4 : fetch_word Plain.M.loaded_segments (0x166e8 : word) = Some W_165e4.
Proof. vm_refl. Qed.
Lemma D_165e4 : decode_any W_165e4 = Some (Branch BC_NE 26 0 8148, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_165e8 : bv 32 := 0xfb9ff06f.
Lemma F_165e8 : fetch_word Plain.M.loaded_segments (0x166ec : word) = Some W_165e8.
Proof. vm_refl. Qed.
Lemma D_165e8 : decode_any W_165e8 = Some (Jal 0 2097080, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16614 : bv 32 := 0x0000a517.
Lemma F_16614 : fetch_word Plain.M.loaded_segments (0x16718 : word) = Some W_16614.
Proof. vm_refl. Qed.
Lemma D_16614 : decode_any W_16614 = Some (Auipc 10 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16618 : bv 32 := 0x88853503.
Lemma F_16618 : fetch_word Plain.M.loaded_segments (0x1671c : word) = Some W_16618.
Proof. vm_refl. Qed.
Lemma D_16618 : decode_any W_16618 = Some (Load SZ8 true 10 10 2184, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1661c : bv 32 := 0x00052503.
Lemma F_1661c : fetch_word Plain.M.loaded_segments (0x16720 : word) = Some W_1661c.
Proof. vm_refl. Qed.
Lemma D_1661c : decode_any W_1661c = Some (Load SZ4 true 10 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16620 : bv 32 := 0x00500593.
Lemma F_16620 : fetch_word Plain.M.loaded_segments (0x16724 : word) = Some W_16620.
Proof. vm_refl. Qed.
Lemma D_16620 : decode_any W_16620 = Some (OpImm ALU_ADD 11 0 5, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16624 : bv 32 := 0x08a5c063.
Lemma F_16624 : fetch_word Plain.M.loaded_segments (0x16728 : word) = Some W_16624.
Proof. vm_refl. Qed.
Lemma D_16624 : decode_any W_16624 = Some (Branch BC_LT 11 10 128, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16628 : bv 32 := 0xffffa517.
Lemma F_16628 : fetch_word Plain.M.loaded_segments (0x1672c : word) = Some W_16628.
Proof. vm_refl. Qed.
Lemma D_16628 : decode_any W_16628 = Some (Auipc 10 1048570, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1662c : bv 32 := 0xffffa597.
Lemma F_1662c : fetch_word Plain.M.loaded_segments (0x16730 : word) = Some W_1662c.
Proof. vm_refl. Qed.
Lemma D_1662c : decode_any W_1662c = Some (Auipc 11 1048570, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16630 : bv 32 := 0xe4450513.
Lemma F_16630 : fetch_word Plain.M.loaded_segments (0x16734 : word) = Some W_16630.
Proof. vm_refl. Qed.
Lemma D_16630 : decode_any W_16630 = Some (OpImm ALU_ADD 10 10 3652, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16634 : bv 32 := 0xd6258593.
Lemma F_16634 : fetch_word Plain.M.loaded_segments (0x16738 : word) = Some W_16634.
Proof. vm_refl. Qed.
Lemma D_16634 : decode_any W_16634 = Some (OpImm ALU_ADD 11 11 3426, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16638 : bv 32 := 0x00000613.
Lemma F_16638 : fetch_word Plain.M.loaded_segments (0x1673c : word) = Some W_16638.
Proof. vm_refl. Qed.
Lemma D_16638 : decode_any W_16638 = Some (OpImm ALU_ADD 12 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1663c : bv 32 := 0x06813083.
Lemma F_1663c : fetch_word Plain.M.loaded_segments (0x16740 : word) = Some W_1663c.
Proof. vm_refl. Qed.
Lemma D_1663c : decode_any W_1663c = Some (Load SZ8 true 1 2 104, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16640 : bv 32 := 0x06013403.
Lemma F_16640 : fetch_word Plain.M.loaded_segments (0x16744 : word) = Some W_16640.
Proof. vm_refl. Qed.
Lemma D_16640 : decode_any W_16640 = Some (Load SZ8 true 8 2 96, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16644 : bv 32 := 0x05813483.
Lemma F_16644 : fetch_word Plain.M.loaded_segments (0x16748 : word) = Some W_16644.
Proof. vm_refl. Qed.
Lemma D_16644 : decode_any W_16644 = Some (Load SZ8 true 9 2 88, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16648 : bv 32 := 0x05013903.
Lemma F_16648 : fetch_word Plain.M.loaded_segments (0x1674c : word) = Some W_16648.
Proof. vm_refl. Qed.
Lemma D_16648 : decode_any W_16648 = Some (Load SZ8 true 18 2 80, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1664c : bv 32 := 0x04813983.
Lemma F_1664c : fetch_word Plain.M.loaded_segments (0x16750 : word) = Some W_1664c.
Proof. vm_refl. Qed.
Lemma D_1664c : decode_any W_1664c = Some (Load SZ8 true 19 2 72, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16650 : bv 32 := 0x04013a03.
Lemma F_16650 : fetch_word Plain.M.loaded_segments (0x16754 : word) = Some W_16650.
Proof. vm_refl. Qed.
Lemma D_16650 : decode_any W_16650 = Some (Load SZ8 true 20 2 64, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16654 : bv 32 := 0x03813a83.
Lemma F_16654 : fetch_word Plain.M.loaded_segments (0x16758 : word) = Some W_16654.
Proof. vm_refl. Qed.
Lemma D_16654 : decode_any W_16654 = Some (Load SZ8 true 21 2 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16658 : bv 32 := 0x03013b03.
Lemma F_16658 : fetch_word Plain.M.loaded_segments (0x1675c : word) = Some W_16658.
Proof. vm_refl. Qed.
Lemma D_16658 : decode_any W_16658 = Some (Load SZ8 true 22 2 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1665c : bv 32 := 0x02813b83.
Lemma F_1665c : fetch_word Plain.M.loaded_segments (0x16760 : word) = Some W_1665c.
Proof. vm_refl. Qed.
Lemma D_1665c : decode_any W_1665c = Some (Load SZ8 true 23 2 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16660 : bv 32 := 0x02013c03.
Lemma F_16660 : fetch_word Plain.M.loaded_segments (0x16764 : word) = Some W_16660.
Proof. vm_refl. Qed.
Lemma D_16660 : decode_any W_16660 = Some (Load SZ8 true 24 2 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16664 : bv 32 := 0x01813c83.
Lemma F_16664 : fetch_word Plain.M.loaded_segments (0x16768 : word) = Some W_16664.
Proof. vm_refl. Qed.
Lemma D_16664 : decode_any W_16664 = Some (Load SZ8 true 25 2 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16668 : bv 32 := 0x01013d03.
Lemma F_16668 : fetch_word Plain.M.loaded_segments (0x1676c : word) = Some W_16668.
Proof. vm_refl. Qed.
Lemma D_16668 : decode_any W_16668 = Some (Load SZ8 true 26 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1666c : bv 32 := 0x07010113.
Lemma F_1666c : fetch_word Plain.M.loaded_segments (0x16770 : word) = Some W_1666c.
Proof. vm_refl. Qed.
Lemma D_1666c : decode_any W_1666c = Some (OpImm ALU_ADD 2 2 112, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16670 : bv 32 := 0xeacfd06f.
Lemma F_16670 : fetch_word Plain.M.loaded_segments (0x16774 : word) = Some W_16670.
Proof. vm_refl. Qed.
Lemma D_16670 : decode_any W_16670 = Some (Jal 0 2086572, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16674 : bv 32 := 0x0000a517.
Lemma F_16674 : fetch_word Plain.M.loaded_segments (0x16778 : word) = Some W_16674.
Proof. vm_refl. Qed.
Lemma D_16674 : decode_any W_16674 = Some (Auipc 10 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16678 : bv 32 := 0x82853503.
Lemma F_16678 : fetch_word Plain.M.loaded_segments (0x1677c : word) = Some W_16678.
Proof. vm_refl. Qed.
Lemma D_16678 : decode_any W_16678 = Some (Load SZ8 true 10 10 2088, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1667c : bv 32 := 0x00052503.
Lemma F_1667c : fetch_word Plain.M.loaded_segments (0x16780 : word) = Some W_1667c.
Proof. vm_refl. Qed.
Lemma D_1667c : decode_any W_1667c = Some (Load SZ4 true 10 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16680 : bv 32 := 0x00500593.
Lemma F_16680 : fetch_word Plain.M.loaded_segments (0x16784 : word) = Some W_16680.
Proof. vm_refl. Qed.
Lemma D_16680 : decode_any W_16680 = Some (OpImm ALU_ADD 11 0 5, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16684 : bv 32 := 0x02a5c063.
Lemma F_16684 : fetch_word Plain.M.loaded_segments (0x16788 : word) = Some W_16684.
Proof. vm_refl. Qed.
Lemma D_16684 : decode_any W_16684 = Some (Branch BC_LT 11 10 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16688 : bv 32 := 0xffffa517.
Lemma F_16688 : fetch_word Plain.M.loaded_segments (0x1678c : word) = Some W_16688.
Proof. vm_refl. Qed.
Lemma D_16688 : decode_any W_16688 = Some (Auipc 10 1048570, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1668c : bv 32 := 0xffffa597.
Lemma F_1668c : fetch_word Plain.M.loaded_segments (0x16790 : word) = Some W_1668c.
Proof. vm_refl. Qed.
Lemma D_1668c : decode_any W_1668c = Some (Auipc 11 1048570, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16690 : bv 32 := 0xc6850513.
Lemma F_16690 : fetch_word Plain.M.loaded_segments (0x16794 : word) = Some W_16690.
Proof. vm_refl. Qed.
Lemma D_16690 : decode_any W_16690 = Some (OpImm ALU_ADD 10 10 3176, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16694 : bv 32 := 0xd0258593.
Lemma F_16694 : fetch_word Plain.M.loaded_segments (0x16798 : word) = Some W_16694.
Proof. vm_refl. Qed.
Lemma D_16694 : decode_any W_16694 = Some (OpImm ALU_ADD 11 11 3330, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16698 : bv 32 := 0x00000613.
Lemma F_16698 : fetch_word Plain.M.loaded_segments (0x1679c : word) = Some W_16698.
Proof. vm_refl. Qed.
Lemma D_16698 : decode_any W_16698 = Some (OpImm ALU_ADD 12 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1669c : bv 32 := 0xe80fd0ef.
Lemma F_1669c : fetch_word Plain.M.loaded_segments (0x167a0 : word) = Some W_1669c.
Proof. vm_refl. Qed.
Lemma D_1669c : decode_any W_1669c = Some (Jal 1 2086528, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_166a0 : bv 32 := 0x0680006f.
Lemma F_166a0 : fetch_word Plain.M.loaded_segments (0x167a4 : word) = Some W_166a0.
Proof. vm_refl. Qed.
Lemma D_166a0 : decode_any W_166a0 = Some (Jal 0 104, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_166ac : bv 32 := 0x00100513.
Lemma F_166ac : fetch_word Plain.M.loaded_segments (0x167b0 : word) = Some W_166ac.
Proof. vm_refl. Qed.
Lemma D_166ac : decode_any W_166ac = Some (OpImm ALU_ADD 10 0 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_166b0 : bv 32 := 0x05800593.
Lemma F_166b0 : fetch_word Plain.M.loaded_segments (0x167b4 : word) = Some W_166b0.
Proof. vm_refl. Qed.
Lemma D_166b0 : decode_any W_166b0 = Some (OpImm ALU_ADD 11 0 88, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_166b4 : bv 32 := 0x365000ef.
Lemma F_166b4 : fetch_word Plain.M.loaded_segments (0x167b8 : word) = Some W_166b4.
Proof. vm_refl. Qed.
Lemma D_166b4 : decode_any W_166b4 = Some (Jal 1 2916, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_166b8 : bv 32 := 0x00050b93.
Lemma F_166b8 : fetch_word Plain.M.loaded_segments (0x167bc : word) = Some W_166b8.
Proof. vm_refl. Qed.
Lemma D_166b8 : decode_any W_166b8 = Some (OpImm ALU_ADD 23 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_166bc : bv 32 := 0x00090513.
Lemma F_166bc : fetch_word Plain.M.loaded_segments (0x167c0 : word) = Some W_166bc.
Proof. vm_refl. Qed.
Lemma D_166bc : decode_any W_166bc = Some (OpImm ALU_ADD 10 18 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_166c0 : bv 32 := 0xd21fe0ef.
Lemma F_166c0 : fetch_word Plain.M.loaded_segments (0x167c4 : word) = Some W_166c0.
Proof. vm_refl. Qed.
Lemma D_166c0 : decode_any W_166c0 = Some (Jal 1 2092320, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_166c4 : bv 32 := 0x00abb023.
Lemma F_166c4 : fetch_word Plain.M.loaded_segments (0x167c8 : word) = Some W_166c4.
Proof. vm_refl. Qed.
Lemma D_166c4 : decode_any W_166c4 = Some (Store SZ8 23 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_166c8 : bv 32 := 0x009ba823.
Lemma F_166c8 : fetch_word Plain.M.loaded_segments (0x167cc : word) = Some W_166c8.
Proof. vm_refl. Qed.
Lemma D_166c8 : decode_any W_166c8 = Some (Store SZ4 23 9 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_166cc : bv 32 := 0x008baa23.
Lemma F_166cc : fetch_word Plain.M.loaded_segments (0x167d0 : word) = Some W_166cc.
Proof. vm_refl. Qed.
Lemma D_166cc : decode_any W_166cc = Some (Store SZ4 23 8 20, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_166d0 : bv 32 := 0x013bac23.
Lemma F_166d0 : fetch_word Plain.M.loaded_segments (0x167d4 : word) = Some W_166d0.
Proof. vm_refl. Qed.
Lemma D_166d0 : decode_any W_166d0 = Some (Store SZ4 23 19 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_166d4 : bv 32 := 0x015bae23.
Lemma F_166d4 : fetch_word Plain.M.loaded_segments (0x167d8 : word) = Some W_166d4.
Proof. vm_refl. Qed.
Lemma D_166d4 : decode_any W_166d4 = Some (Store SZ4 23 21 28, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_166d8 : bv 32 := 0x036bb423.
Lemma F_166d8 : fetch_word Plain.M.loaded_segments (0x167dc : word) = Some W_166d8.
Proof. vm_refl. Qed.
Lemma D_166d8 : decode_any W_166d8 = Some (Store SZ8 23 22 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_166dc : bv 32 := 0x000a0513.
Lemma F_166dc : fetch_word Plain.M.loaded_segments (0x167e0 : word) = Some W_166dc.
Proof. vm_refl. Qed.
Lemma D_166dc : decode_any W_166dc = Some (OpImm ALU_ADD 10 20 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_166e0 : bv 32 := 0xa29fd0ef.
Lemma F_166e0 : fetch_word Plain.M.loaded_segments (0x167e4 : word) = Some W_166e0.
Proof. vm_refl. Qed.
Lemma D_166e0 : decode_any W_166e0 = Some (Jal 1 2087464, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_166e4 : bv 32 := 0x04abb023.
Lemma F_166e4 : fetch_word Plain.M.loaded_segments (0x167e8 : word) = Some W_166e4.
Proof. vm_refl. Qed.
Lemma D_166e4 : decode_any W_166e4 = Some (Store SZ8 23 10 64, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_166e8 : bv 32 := 0x000a0513.
Lemma F_166e8 : fetch_word Plain.M.loaded_segments (0x167ec : word) = Some W_166e8.
Proof. vm_refl. Qed.
Lemma D_166e8 : decode_any W_166e8 = Some (OpImm ALU_ADD 10 20 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_166ec : bv 32 := 0xfd0fd0ef.
Lemma F_166ec : fetch_word Plain.M.loaded_segments (0x167f0 : word) = Some W_166ec.
Proof. vm_refl. Qed.
Lemma D_166ec : decode_any W_166ec = Some (Jal 1 2086864, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_166f0 : bv 32 := 0x04abb423.
Lemma F_166f0 : fetch_word Plain.M.loaded_segments (0x167f4 : word) = Some W_166f0.
Proof. vm_refl. Qed.
Lemma D_166f0 : decode_any W_166f0 = Some (Store SZ8 23 10 72, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_166f4 : bv 32 := 0x00000513.
Lemma F_166f4 : fetch_word Plain.M.loaded_segments (0x167f8 : word) = Some W_166f4.
Proof. vm_refl. Qed.
Lemma D_166f4 : decode_any W_166f4 = Some (OpImm ALU_ADD 10 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_166f8 : bv 32 := 0xc5dfd0ef.
Lemma F_166f8 : fetch_word Plain.M.loaded_segments (0x167fc : word) = Some W_166f8.
Proof. vm_refl. Qed.
Lemma D_166f8 : decode_any W_166f8 = Some (Jal 1 2088028, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_166fc : bv 32 := 0x00050593.
Lemma F_166fc : fetch_word Plain.M.loaded_segments (0x16800 : word) = Some W_166fc.
Proof. vm_refl. Qed.
Lemma D_166fc : decode_any W_166fc = Some (OpImm ALU_ADD 11 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16700 : bv 32 := 0x000b8513.
Lemma F_16700 : fetch_word Plain.M.loaded_segments (0x16804 : word) = Some W_16700.
Proof. vm_refl. Qed.
Lemma D_16700 : decode_any W_16700 = Some (OpImm ALU_ADD 10 23 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16704 : bv 32 := 0x04bbb823.
Lemma F_16704 : fetch_word Plain.M.loaded_segments (0x16808 : word) = Some W_16704.
Proof. vm_refl. Qed.
Lemma D_16704 : decode_any W_16704 = Some (Store SZ8 23 11 80, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16708 : bv 32 := 0x06813083.
Lemma F_16708 : fetch_word Plain.M.loaded_segments (0x1680c : word) = Some W_16708.
Proof. vm_refl. Qed.
Lemma D_16708 : decode_any W_16708 = Some (Load SZ8 true 1 2 104, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1670c : bv 32 := 0x06013403.
Lemma F_1670c : fetch_word Plain.M.loaded_segments (0x16810 : word) = Some W_1670c.
Proof. vm_refl. Qed.
Lemma D_1670c : decode_any W_1670c = Some (Load SZ8 true 8 2 96, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16710 : bv 32 := 0x05813483.
Lemma F_16710 : fetch_word Plain.M.loaded_segments (0x16814 : word) = Some W_16710.
Proof. vm_refl. Qed.
Lemma D_16710 : decode_any W_16710 = Some (Load SZ8 true 9 2 88, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16714 : bv 32 := 0x05013903.
Lemma F_16714 : fetch_word Plain.M.loaded_segments (0x16818 : word) = Some W_16714.
Proof. vm_refl. Qed.
Lemma D_16714 : decode_any W_16714 = Some (Load SZ8 true 18 2 80, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16718 : bv 32 := 0x04813983.
Lemma F_16718 : fetch_word Plain.M.loaded_segments (0x1681c : word) = Some W_16718.
Proof. vm_refl. Qed.
Lemma D_16718 : decode_any W_16718 = Some (Load SZ8 true 19 2 72, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1671c : bv 32 := 0x04013a03.
Lemma F_1671c : fetch_word Plain.M.loaded_segments (0x16820 : word) = Some W_1671c.
Proof. vm_refl. Qed.
Lemma D_1671c : decode_any W_1671c = Some (Load SZ8 true 20 2 64, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16720 : bv 32 := 0x03813a83.
Lemma F_16720 : fetch_word Plain.M.loaded_segments (0x16824 : word) = Some W_16720.
Proof. vm_refl. Qed.
Lemma D_16720 : decode_any W_16720 = Some (Load SZ8 true 21 2 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16724 : bv 32 := 0x03013b03.
Lemma F_16724 : fetch_word Plain.M.loaded_segments (0x16828 : word) = Some W_16724.
Proof. vm_refl. Qed.
Lemma D_16724 : decode_any W_16724 = Some (Load SZ8 true 22 2 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16728 : bv 32 := 0x02813b83.
Lemma F_16728 : fetch_word Plain.M.loaded_segments (0x1682c : word) = Some W_16728.
Proof. vm_refl. Qed.
Lemma D_16728 : decode_any W_16728 = Some (Load SZ8 true 23 2 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1672c : bv 32 := 0x02013c03.
Lemma F_1672c : fetch_word Plain.M.loaded_segments (0x16830 : word) = Some W_1672c.
Proof. vm_refl. Qed.
Lemma D_1672c : decode_any W_1672c = Some (Load SZ8 true 24 2 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16730 : bv 32 := 0x01813c83.
Lemma F_16730 : fetch_word Plain.M.loaded_segments (0x16834 : word) = Some W_16730.
Proof. vm_refl. Qed.
Lemma D_16730 : decode_any W_16730 = Some (Load SZ8 true 25 2 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16734 : bv 32 := 0x01013d03.
Lemma F_16734 : fetch_word Plain.M.loaded_segments (0x16838 : word) = Some W_16734.
Proof. vm_refl. Qed.
Lemma D_16734 : decode_any W_16734 = Some (Load SZ8 true 26 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16738 : bv 32 := 0x07010113.
Lemma F_16738 : fetch_word Plain.M.loaded_segments (0x1683c : word) = Some W_16738.
Proof. vm_refl. Qed.
Lemma D_16738 : decode_any W_16738 = Some (OpImm ALU_ADD 2 2 112, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1673c : bv 32 := 0x00008067.
Lemma F_1673c : fetch_word Plain.M.loaded_segments (0x16840 : word) = Some W_1673c.
Proof. vm_refl. Qed.
Lemma D_1673c : decode_any W_1673c = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16740 : bv 32 := 0xfe010113.
Lemma F_16740 : fetch_word Plain.M.loaded_segments (0x16844 : word) = Some W_16740.
Proof. vm_refl. Qed.
Lemma D_16740 : decode_any W_16740 = Some (OpImm ALU_ADD 2 2 4064, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16744 : bv 32 := 0x00113c23.
Lemma F_16744 : fetch_word Plain.M.loaded_segments (0x16848 : word) = Some W_16744.
Proof. vm_refl. Qed.
Lemma D_16744 : decode_any W_16744 = Some (Store SZ8 2 1 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16748 : bv 32 := 0x00813823.
Lemma F_16748 : fetch_word Plain.M.loaded_segments (0x1684c : word) = Some W_16748.
Proof. vm_refl. Qed.
Lemma D_16748 : decode_any W_16748 = Some (Store SZ8 2 8 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1674c : bv 32 := 0x00913423.
Lemma F_1674c : fetch_word Plain.M.loaded_segments (0x16850 : word) = Some W_1674c.
Proof. vm_refl. Qed.
Lemma D_1674c : decode_any W_1674c = Some (Store SZ8 2 9 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16750 : bv 32 := 0x06050063.
Lemma F_16750 : fetch_word Plain.M.loaded_segments (0x16854 : word) = Some W_16750.
Proof. vm_refl. Qed.
Lemma D_16750 : decode_any W_16750 = Some (Branch BC_EQ 10 0 96, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16754 : bv 32 := 0x00050413.
Lemma F_16754 : fetch_word Plain.M.loaded_segments (0x16858 : word) = Some W_16754.
Proof. vm_refl. Qed.
Lemma D_16754 : decode_any W_16754 = Some (OpImm ALU_ADD 8 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16758 : bv 32 := 0x00053483.
Lemma F_16758 : fetch_word Plain.M.loaded_segments (0x1685c : word) = Some W_16758.
Proof. vm_refl. Qed.
Lemma D_16758 : decode_any W_16758 = Some (Load SZ8 true 9 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1675c : bv 32 := 0x08048663.
Lemma F_1675c : fetch_word Plain.M.loaded_segments (0x16860 : word) = Some W_1675c.
Proof. vm_refl. Qed.
Lemma D_1675c : decode_any W_1675c = Some (Branch BC_EQ 9 0 140, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16760 : bv 32 := 0x00048513.
Lemma F_16760 : fetch_word Plain.M.loaded_segments (0x16864 : word) = Some W_16760.
Proof. vm_refl. Qed.
Lemma D_16760 : decode_any W_16760 = Some (OpImm ALU_ADD 10 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16764 : bv 32 := 0xa4dfe0ef.
Lemma F_16764 : fetch_word Plain.M.loaded_segments (0x16868 : word) = Some W_16764.
Proof. vm_refl. Qed.
Lemma D_16764 : decode_any W_16764 = Some (Jal 1 2091596, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16768 : bv 32 := 0x00848513.
Lemma F_16768 : fetch_word Plain.M.loaded_segments (0x1686c : word) = Some W_16768.
Proof. vm_refl. Qed.
Lemma D_16768 : decode_any W_16768 = Some (OpImm ALU_ADD 10 9 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1676c : bv 32 := 0xa45fe0ef.
Lemma F_1676c : fetch_word Plain.M.loaded_segments (0x16870 : word) = Some W_1676c.
Proof. vm_refl. Qed.
Lemma D_1676c : decode_any W_1676c = Some (Jal 1 2091588, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16770 : bv 32 := 0x02848513.
Lemma F_16770 : fetch_word Plain.M.loaded_segments (0x16874 : word) = Some W_16770.
Proof. vm_refl. Qed.
Lemma D_16770 : decode_any W_16770 = Some (OpImm ALU_ADD 10 9 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16774 : bv 32 := 0x858fe0ef.
Lemma F_16774 : fetch_word Plain.M.loaded_segments (0x16878 : word) = Some W_16774.
Proof. vm_refl. Qed.
Lemma D_16774 : decode_any W_16774 = Some (Jal 1 2089048, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16778 : bv 32 := 0x03048513.
Lemma F_16778 : fetch_word Plain.M.loaded_segments (0x1687c : word) = Some W_16778.
Proof. vm_refl. Qed.
Lemma D_16778 : decode_any W_16778 = Some (OpImm ALU_ADD 10 9 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1677c : bv 32 := 0xd1dfd0ef.
Lemma F_1677c : fetch_word Plain.M.loaded_segments (0x16880 : word) = Some W_1677c.
Proof. vm_refl. Qed.
Lemma D_1677c : decode_any W_1677c = Some (Jal 1 2088220, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16780 : bv 32 := 0x03848513.
Lemma F_16780 : fetch_word Plain.M.loaded_segments (0x16884 : word) = Some W_16780.
Proof. vm_refl. Qed.
Lemma D_16780 : decode_any W_16780 = Some (OpImm ALU_ADD 10 9 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16784 : bv 32 := 0xd15fd0ef.
Lemma F_16784 : fetch_word Plain.M.loaded_segments (0x16888 : word) = Some W_16784.
Proof. vm_refl. Qed.
Lemma D_16784 : decode_any W_16784 = Some (Jal 1 2088212, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16788 : bv 32 := 0x04048513.
Lemma F_16788 : fetch_word Plain.M.loaded_segments (0x1688c : word) = Some W_16788.
Proof. vm_refl. Qed.
Lemma D_16788 : decode_any W_16788 = Some (OpImm ALU_ADD 10 9 64, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1678c : bv 32 := 0xa31fd0ef.
Lemma F_1678c : fetch_word Plain.M.loaded_segments (0x16890 : word) = Some W_1678c.
Proof. vm_refl. Qed.
Lemma D_1678c : decode_any W_1678c = Some (Jal 1 2087472, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16790 : bv 32 := 0x04848513.
Lemma F_16790 : fetch_word Plain.M.loaded_segments (0x16894 : word) = Some W_16790.
Proof. vm_refl. Qed.
Lemma D_16790 : decode_any W_16790 = Some (OpImm ALU_ADD 10 9 72, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16794 : bv 32 := 0xfdcfd0ef.
Lemma F_16794 : fetch_word Plain.M.loaded_segments (0x16898 : word) = Some W_16794.
Proof. vm_refl. Qed.
Lemma D_16794 : decode_any W_16794 = Some (Jal 1 2086876, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_16798 : bv 32 := 0x05048513.
Lemma F_16798 : fetch_word Plain.M.loaded_segments (0x1689c : word) = Some W_16798.
Proof. vm_refl. Qed.
Lemma D_16798 : decode_any W_16798 = Some (OpImm ALU_ADD 10 9 80, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1679c : bv 32 := 0xcfdfd0ef.
Lemma F_1679c : fetch_word Plain.M.loaded_segments (0x168a0 : word) = Some W_1679c.
Proof. vm_refl. Qed.
Lemma D_1679c : decode_any W_1679c = Some (Jal 1 2088188, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_167a0 : bv 32 := 0x00048513.
Lemma F_167a0 : fetch_word Plain.M.loaded_segments (0x168a4 : word) = Some W_167a0.
Proof. vm_refl. Qed.
Lemma D_167a0 : decode_any W_167a0 = Some (OpImm ALU_ADD 10 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_167a4 : bv 32 := 0x3ad000ef.
Lemma F_167a4 : fetch_word Plain.M.loaded_segments (0x168a8 : word) = Some W_167a4.
Proof. vm_refl. Qed.
Lemma D_167a4 : decode_any W_167a4 = Some (Jal 1 2988, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_167a8 : bv 32 := 0x00043023.
Lemma F_167a8 : fetch_word Plain.M.loaded_segments (0x168ac : word) = Some W_167a8.
Proof. vm_refl. Qed.
Lemma D_167a8 : decode_any W_167a8 = Some (Store SZ8 8 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_167ac : bv 32 := 0x03c0006f.
Lemma F_167ac : fetch_word Plain.M.loaded_segments (0x168b0 : word) = Some W_167ac.
Proof. vm_refl. Qed.
Lemma D_167ac : decode_any W_167ac = Some (Jal 0 60, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_167e8 : bv 32 := 0x01813083.
Lemma F_167e8 : fetch_word Plain.M.loaded_segments (0x168ec : word) = Some W_167e8.
Proof. vm_refl. Qed.
Lemma D_167e8 : decode_any W_167e8 = Some (Load SZ8 true 1 2 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_167ec : bv 32 := 0x01013403.
Lemma F_167ec : fetch_word Plain.M.loaded_segments (0x168f0 : word) = Some W_167ec.
Proof. vm_refl. Qed.
Lemma D_167ec : decode_any W_167ec = Some (Load SZ8 true 8 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_167f0 : bv 32 := 0x00813483.
Lemma F_167f0 : fetch_word Plain.M.loaded_segments (0x168f4 : word) = Some W_167f0.
Proof. vm_refl. Qed.
Lemma D_167f0 : decode_any W_167f0 = Some (Load SZ8 true 9 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_167f4 : bv 32 := 0x02010113.
Lemma F_167f4 : fetch_word Plain.M.loaded_segments (0x168f8 : word) = Some W_167f4.
Proof. vm_refl. Qed.
Lemma D_167f4 : decode_any W_167f4 = Some (OpImm ALU_ADD 2 2 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_167f8 : bv 32 := 0x00008067.
Lemma F_167f8 : fetch_word Plain.M.loaded_segments (0x168fc : word) = Some W_167f8.
Proof. vm_refl. Qed.
Lemma D_167f8 : decode_any W_167f8 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.
