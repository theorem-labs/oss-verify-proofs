(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib Require Import ImgP.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Abbreviation PSEGS := ImgP.M.loaded_segments.
Open Scope bv_scope.

(* [comment removed for export] *)
Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

(* [comment removed for export] *)
Definition W_a71b8 : bv 32 := 0x01013403.
Lemma F_a71b8 : fetch_word PSEGS (0xa71b8 : word) = Some W_a71b8.
Proof. vm_refl. Qed.
Lemma D_a71b8 : decode_any W_a71b8 = Some (Load SZ8 true 8 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a71bc : bv 32 := 0x00813483.
Lemma F_a71bc : fetch_word PSEGS (0xa71bc : word) = Some W_a71bc.
Proof. vm_refl. Qed.
Lemma D_a71bc : decode_any W_a71bc = Some (Load SZ8 true 9 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a71c0 : bv 32 := 0x02010113.
Lemma F_a71c0 : fetch_word PSEGS (0xa71c0 : word) = Some W_a71c0.
Proof. vm_refl. Qed.
Lemma D_a71c0 : decode_any W_a71c0 = Some (OpImm ALU_ADD 2 2 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a71c4 : bv 32 := 0x00008067.
Lemma F_a71c4 : fetch_word PSEGS (0xa71c4 : word) = Some W_a71c4.
Proof. vm_refl. Qed.
Lemma D_a71c4 : decode_any W_a71c4 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a71c8 : bv 32 := 0xff010113.
Lemma F_a71c8 : fetch_word PSEGS (0xa71c8 : word) = Some W_a71c8.
Proof. vm_refl. Qed.
Lemma D_a71c8 : decode_any W_a71c8 = Some (OpImm ALU_ADD 2 2 4080, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a71cc : bv 32 := 0x00113423.
Lemma F_a71cc : fetch_word PSEGS (0xa71cc : word) = Some W_a71cc.
Proof. vm_refl. Qed.
Lemma D_a71cc : decode_any W_a71cc = Some (Store SZ8 2 1 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a71d0 : bv 32 := 0x00813023.
Lemma F_a71d0 : fetch_word PSEGS (0xa71d0 : word) = Some W_a71d0.
Proof. vm_refl. Qed.
Lemma D_a71d0 : decode_any W_a71d0 = Some (Store SZ8 2 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a71d4 : bv 32 := 0x02058a63.
Lemma F_a71d4 : fetch_word PSEGS (0xa71d4 : word) = Some W_a71d4.
Proof. vm_refl. Qed.
Lemma D_a71d4 : decode_any W_a71d4 = Some (Branch BC_EQ 11 0 52, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a71d8 : bv 32 := 0xffc50513.
Lemma F_a71d8 : fetch_word PSEGS (0xa71d8 : word) = Some W_a71d8.
Proof. vm_refl. Qed.
Lemma D_a71d8 : decode_any W_a71d8 = Some (OpImm ALU_ADD 10 10 4092, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a71dc : bv 32 := 0x00452603.
Lemma F_a71dc : fetch_word PSEGS (0xa71dc : word) = Some W_a71dc.
Proof. vm_refl. Qed.
Lemma D_a71dc : decode_any W_a71dc = Some (Load SZ4 true 12 10 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a71e0 : bv 32 := 0x00450513.
Lemma F_a71e0 : fetch_word PSEGS (0xa71e0 : word) = Some W_a71e0.
Proof. vm_refl. Qed.
Lemma D_a71e0 : decode_any W_a71e0 = Some (OpImm ALU_ADD 10 10 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a71e4 : bv 32 := 0x00060463.
Lemma F_a71e4 : fetch_word PSEGS (0xa71e4 : word) = Some W_a71e4.
Proof. vm_refl. Qed.
Lemma D_a71e4 : decode_any W_a71e4 = Some (Branch BC_EQ 12 0 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a71e8 : bv 32 := 0xfeb61ae3.
Lemma F_a71e8 : fetch_word PSEGS (0xa71e8 : word) = Some W_a71e8.
Proof. vm_refl. Qed.
Lemma D_a71e8 : decode_any W_a71e8 = Some (Branch BC_NE 12 11 8180, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a71ec : bv 32 := 0x00163593.
Lemma F_a71ec : fetch_word PSEGS (0xa71ec : word) = Some W_a71ec.
Proof. vm_refl. Qed.
Lemma D_a71ec : decode_any W_a71ec = Some (OpImm ALU_SLTU 11 12 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a71f0 : bv 32 := 0xfff58593.
Lemma F_a71f0 : fetch_word PSEGS (0xa71f0 : word) = Some W_a71f0.
Proof. vm_refl. Qed.
Lemma D_a71f0 : decode_any W_a71f0 = Some (OpImm ALU_ADD 11 11 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a71f4 : bv 32 := 0x00a5f533.
Lemma F_a71f4 : fetch_word PSEGS (0xa71f4 : word) = Some W_a71f4.
Proof. vm_refl. Qed.
Lemma D_a71f4 : decode_any W_a71f4 = Some (Op ALU_AND 10 11 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a71f8 : bv 32 := 0x00813083.
Lemma F_a71f8 : fetch_word PSEGS (0xa71f8 : word) = Some W_a71f8.
Proof. vm_refl. Qed.
Lemma D_a71f8 : decode_any W_a71f8 = Some (Load SZ8 true 1 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a71fc : bv 32 := 0x00013403.
Lemma F_a71fc : fetch_word PSEGS (0xa71fc : word) = Some W_a71fc.
Proof. vm_refl. Qed.
Lemma D_a71fc : decode_any W_a71fc = Some (Load SZ8 true 8 2 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a7200 : bv 32 := 0x01010113.
Lemma F_a7200 : fetch_word PSEGS (0xa7200 : word) = Some W_a7200.
Proof. vm_refl. Qed.
Lemma D_a7200 : decode_any W_a7200 = Some (OpImm ALU_ADD 2 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a7204 : bv 32 := 0x00008067.
Lemma F_a7204 : fetch_word PSEGS (0xa7204 : word) = Some W_a7204.
Proof. vm_refl. Qed.
Lemma D_a7204 : decode_any W_a7204 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a7208 : bv 32 := 0x00050413.
Lemma F_a7208 : fetch_word PSEGS (0xa7208 : word) = Some W_a7208.
Proof. vm_refl. Qed.
Lemma D_a7208 : decode_any W_a7208 = Some (OpImm ALU_ADD 8 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a720c : bv 32 := 0x05c000ef.
Lemma F_a720c : fetch_word PSEGS (0xa720c : word) = Some W_a720c.
Proof. vm_refl. Qed.
Lemma D_a720c : decode_any W_a720c = Some (Jal 1 92, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a7210 : bv 32 := 0x00251513.
Lemma F_a7210 : fetch_word PSEGS (0xa7210 : word) = Some W_a7210.
Proof. vm_refl. Qed.
Lemma D_a7210 : decode_any W_a7210 = Some (ShiftImm ALU_SLL 10 10 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a7214 : bv 32 := 0x00a40533.
Lemma F_a7214 : fetch_word PSEGS (0xa7214 : word) = Some W_a7214.
Proof. vm_refl. Qed.
Lemma D_a7214 : decode_any W_a7214 = Some (Op ALU_ADD 10 8 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a7218 : bv 32 := 0x00813083.
Lemma F_a7218 : fetch_word PSEGS (0xa7218 : word) = Some W_a7218.
Proof. vm_refl. Qed.
Lemma D_a7218 : decode_any W_a7218 = Some (Load SZ8 true 1 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a721c : bv 32 := 0x00013403.
Lemma F_a721c : fetch_word PSEGS (0xa721c : word) = Some W_a721c.
Proof. vm_refl. Qed.
Lemma D_a721c : decode_any W_a721c = Some (Load SZ8 true 8 2 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a7220 : bv 32 := 0x01010113.
Lemma F_a7220 : fetch_word PSEGS (0xa7220 : word) = Some W_a7220.
Proof. vm_refl. Qed.
Lemma D_a7220 : decode_any W_a7220 = Some (OpImm ALU_ADD 2 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a7320 : bv 32 := 0x0003e597.
Lemma F_a7320 : fetch_word PSEGS (0xa7320 : word) = Some W_a7320.
Proof. vm_refl. Qed.
Lemma D_a7320 : decode_any W_a7320 = Some (Auipc 11 62, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a7324 : bv 32 := 0x88b58683.
Lemma F_a7324 : fetch_word PSEGS (0xa7324 : word) = Some W_a7324.
Proof. vm_refl. Qed.
Lemma D_a7324 : decode_any W_a7324 = Some (Load SZ1 true 13 11 2187, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a7328 : bv 32 := 0x1e068863.
Lemma F_a7328 : fetch_word PSEGS (0xa7328 : word) = Some W_a7328.
Proof. vm_refl. Qed.
Lemma D_a7328 : decode_any W_a7328 = Some (Branch BC_EQ 13 0 496, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a73a0 : bv 32 := 0x160526af.
Lemma F_a73a0 : fetch_word PSEGS (0xa73a0 : word) = Some W_a73a0.
Proof. vm_refl. Qed.
Lemma D_a73a0 : decode_any W_a73a0 = Some (Lr AW true true 13 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a73a4 : bv 32 := 0x00c69663.
Lemma F_a73a4 : fetch_word PSEGS (0xa73a4 : word) = Some W_a73a4.
Proof. vm_refl. Qed.
Lemma D_a73a4 : decode_any W_a73a4 = Some (Branch BC_NE 13 12 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a73a8 : bv 32 := 0x1eb5272f.
Lemma F_a73a8 : fetch_word PSEGS (0xa73a8 : word) = Some W_a73a8.
Proof. vm_refl. Qed.
Lemma D_a73a8 : decode_any W_a73a8 = Some (Sc AW true true 14 10 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a73ac : bv 32 := 0xfe071ae3.
Lemma F_a73ac : fetch_word PSEGS (0xa73ac : word) = Some W_a73ac.
Proof. vm_refl. Qed.
Lemma D_a73ac : decode_any W_a73ac = Some (Branch BC_NE 14 0 8180, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a73b0 : bv 32 := 0x0006859b.
Lemma F_a73b0 : fetch_word PSEGS (0xa73b0 : word) = Some W_a73b0.
Proof. vm_refl. Qed.
Lemma D_a73b0 : decode_any W_a73b0 = Some (OpImm32 11 13 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a73b4 : bv 32 := 0x16c58263.
Lemma F_a73b4 : fetch_word PSEGS (0xa73b4 : word) = Some W_a73b4.
Proof. vm_refl. Qed.
Lemma D_a73b4 : decode_any W_a73b4 = Some (Branch BC_EQ 11 12 356, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a73b8 : bv 32 := 0x01f5d613.
Lemma F_a73b8 : fetch_word PSEGS (0xa73b8 : word) = Some W_a73b8.
Proof. vm_refl. Qed.
Lemma D_a73b8 : decode_any W_a73b8 = Some (ShiftImm ALU_SRL 12 11 31, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a73bc : bv 32 := 0x00f67633.
Lemma F_a73bc : fetch_word PSEGS (0xa73bc : word) = Some W_a73bc.
Proof. vm_refl. Qed.
Lemma D_a73bc : decode_any W_a73bc = Some (Op ALU_AND 12 12 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a73c0 : bv 32 := 0x00c5863b.
Lemma F_a73c0 : fetch_word PSEGS (0xa73c0 : word) = Some W_a73c0.
Proof. vm_refl. Qed.
Lemma D_a73c0 : decode_any W_a73c0 = Some (Op32 ALU_ADD 12 11 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a73c4 : bv 32 := 0x00c785b3.
Lemma F_a73c4 : fetch_word PSEGS (0xa73c4 : word) = Some W_a73c4.
Proof. vm_refl. Qed.
Lemma D_a73c4 : decode_any W_a73c4 = Some (Op ALU_ADD 11 15 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a73c8 : bv 32 := 0x0025859b.
Lemma F_a73c8 : fetch_word PSEGS (0xa73c8 : word) = Some W_a73c8.
Proof. vm_refl. Qed.
Lemma D_a73c8 : decode_any W_a73c8 = Some (OpImm32 11 11 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a73cc : bv 32 := 0x160526af.
Lemma F_a73cc : fetch_word PSEGS (0xa73cc : word) = Some W_a73cc.
Proof. vm_refl. Qed.
Lemma D_a73cc : decode_any W_a73cc = Some (Lr AW true true 13 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a73d0 : bv 32 := 0x00c69663.
Lemma F_a73d0 : fetch_word PSEGS (0xa73d0 : word) = Some W_a73d0.
Proof. vm_refl. Qed.
Lemma D_a73d0 : decode_any W_a73d0 = Some (Branch BC_NE 13 12 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a73d4 : bv 32 := 0x1eb5272f.
Lemma F_a73d4 : fetch_word PSEGS (0xa73d4 : word) = Some W_a73d4.
Proof. vm_refl. Qed.
Lemma D_a73d4 : decode_any W_a73d4 = Some (Sc AW true true 14 10 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a73d8 : bv 32 := 0xfe071ae3.
Lemma F_a73d8 : fetch_word PSEGS (0xa73d8 : word) = Some W_a73d8.
Proof. vm_refl. Qed.
Lemma D_a73d8 : decode_any W_a73d8 = Some (Branch BC_NE 14 0 8180, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a73dc : bv 32 := 0x0006859b.
Lemma F_a73dc : fetch_word PSEGS (0xa73dc : word) = Some W_a73dc.
Proof. vm_refl. Qed.
Lemma D_a73dc : decode_any W_a73dc = Some (OpImm32 11 13 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a73e0 : bv 32 := 0x12c58c63.
Lemma F_a73e0 : fetch_word PSEGS (0xa73e0 : word) = Some W_a73e0.
Proof. vm_refl. Qed.
Lemma D_a73e0 : decode_any W_a73e0 = Some (Branch BC_EQ 11 12 312, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a73e4 : bv 32 := 0x01f5d613.
Lemma F_a73e4 : fetch_word PSEGS (0xa73e4 : word) = Some W_a73e4.
Proof. vm_refl. Qed.
Lemma D_a73e4 : decode_any W_a73e4 = Some (ShiftImm ALU_SRL 12 11 31, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a73e8 : bv 32 := 0x00f67633.
Lemma F_a73e8 : fetch_word PSEGS (0xa73e8 : word) = Some W_a73e8.
Proof. vm_refl. Qed.
Lemma D_a73e8 : decode_any W_a73e8 = Some (Op ALU_AND 12 12 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a73ec : bv 32 := 0x00c5863b.
Lemma F_a73ec : fetch_word PSEGS (0xa73ec : word) = Some W_a73ec.
Proof. vm_refl. Qed.
Lemma D_a73ec : decode_any W_a73ec = Some (Op32 ALU_ADD 12 11 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a73f0 : bv 32 := 0x00c785b3.
Lemma F_a73f0 : fetch_word PSEGS (0xa73f0 : word) = Some W_a73f0.
Proof. vm_refl. Qed.
Lemma D_a73f0 : decode_any W_a73f0 = Some (Op ALU_ADD 11 15 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a73f4 : bv 32 := 0x0025859b.
Lemma F_a73f4 : fetch_word PSEGS (0xa73f4 : word) = Some W_a73f4.
Proof. vm_refl. Qed.
Lemma D_a73f4 : decode_any W_a73f4 = Some (OpImm32 11 11 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a73f8 : bv 32 := 0x160526af.
Lemma F_a73f8 : fetch_word PSEGS (0xa73f8 : word) = Some W_a73f8.
Proof. vm_refl. Qed.
Lemma D_a73f8 : decode_any W_a73f8 = Some (Lr AW true true 13 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a73fc : bv 32 := 0x00c69663.
Lemma F_a73fc : fetch_word PSEGS (0xa73fc : word) = Some W_a73fc.
Proof. vm_refl. Qed.
Lemma D_a73fc : decode_any W_a73fc = Some (Branch BC_NE 13 12 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a7400 : bv 32 := 0x1eb5272f.
Lemma F_a7400 : fetch_word PSEGS (0xa7400 : word) = Some W_a7400.
Proof. vm_refl. Qed.
Lemma D_a7400 : decode_any W_a7400 = Some (Sc AW true true 14 10 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a7404 : bv 32 := 0xfe071ae3.
Lemma F_a7404 : fetch_word PSEGS (0xa7404 : word) = Some W_a7404.
Proof. vm_refl. Qed.
Lemma D_a7404 : decode_any W_a7404 = Some (Branch BC_NE 14 0 8180, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a7408 : bv 32 := 0x0006859b.
Lemma F_a7408 : fetch_word PSEGS (0xa7408 : word) = Some W_a7408.
Proof. vm_refl. Qed.
Lemma D_a7408 : decode_any W_a7408 = Some (OpImm32 11 13 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a740c : bv 32 := 0x10c58663.
Lemma F_a740c : fetch_word PSEGS (0xa740c : word) = Some W_a740c.
Proof. vm_refl. Qed.
Lemma D_a740c : decode_any W_a740c = Some (Branch BC_EQ 11 12 268, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a7410 : bv 32 := 0x01f5d613.
Lemma F_a7410 : fetch_word PSEGS (0xa7410 : word) = Some W_a7410.
Proof. vm_refl. Qed.
Lemma D_a7410 : decode_any W_a7410 = Some (ShiftImm ALU_SRL 12 11 31, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a7414 : bv 32 := 0x00f67633.
Lemma F_a7414 : fetch_word PSEGS (0xa7414 : word) = Some W_a7414.
Proof. vm_refl. Qed.
Lemma D_a7414 : decode_any W_a7414 = Some (Op ALU_AND 12 12 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a7418 : bv 32 := 0x00c5863b.
Lemma F_a7418 : fetch_word PSEGS (0xa7418 : word) = Some W_a7418.
Proof. vm_refl. Qed.
Lemma D_a7418 : decode_any W_a7418 = Some (Op32 ALU_ADD 12 11 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a741c : bv 32 := 0x00c785b3.
Lemma F_a741c : fetch_word PSEGS (0xa741c : word) = Some W_a741c.
Proof. vm_refl. Qed.
Lemma D_a741c : decode_any W_a741c = Some (Op ALU_ADD 11 15 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a7420 : bv 32 := 0x0025859b.
Lemma F_a7420 : fetch_word PSEGS (0xa7420 : word) = Some W_a7420.
Proof. vm_refl. Qed.
Lemma D_a7420 : decode_any W_a7420 = Some (OpImm32 11 11 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a7424 : bv 32 := 0x160526af.
Lemma F_a7424 : fetch_word PSEGS (0xa7424 : word) = Some W_a7424.
Proof. vm_refl. Qed.
Lemma D_a7424 : decode_any W_a7424 = Some (Lr AW true true 13 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a7428 : bv 32 := 0x00c69663.
Lemma F_a7428 : fetch_word PSEGS (0xa7428 : word) = Some W_a7428.
Proof. vm_refl. Qed.
Lemma D_a7428 : decode_any W_a7428 = Some (Branch BC_NE 13 12 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a742c : bv 32 := 0x1eb5272f.
Lemma F_a742c : fetch_word PSEGS (0xa742c : word) = Some W_a742c.
Proof. vm_refl. Qed.
Lemma D_a742c : decode_any W_a742c = Some (Sc AW true true 14 10 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a7430 : bv 32 := 0xfe071ae3.
Lemma F_a7430 : fetch_word PSEGS (0xa7430 : word) = Some W_a7430.
Proof. vm_refl. Qed.
Lemma D_a7430 : decode_any W_a7430 = Some (Branch BC_NE 14 0 8180, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a7434 : bv 32 := 0x0006859b.
Lemma F_a7434 : fetch_word PSEGS (0xa7434 : word) = Some W_a7434.
Proof. vm_refl. Qed.
Lemma D_a7434 : decode_any W_a7434 = Some (OpImm32 11 13 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a7438 : bv 32 := 0x0ec58063.
Lemma F_a7438 : fetch_word PSEGS (0xa7438 : word) = Some W_a7438.
Proof. vm_refl. Qed.
Lemma D_a7438 : decode_any W_a7438 = Some (Branch BC_EQ 11 12 224, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a743c : bv 32 := 0x01f5d613.
Lemma F_a743c : fetch_word PSEGS (0xa743c : word) = Some W_a743c.
Proof. vm_refl. Qed.
Lemma D_a743c : decode_any W_a743c = Some (ShiftImm ALU_SRL 12 11 31, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a7440 : bv 32 := 0x00f67633.
Lemma F_a7440 : fetch_word PSEGS (0xa7440 : word) = Some W_a7440.
Proof. vm_refl. Qed.
Lemma D_a7440 : decode_any W_a7440 = Some (Op ALU_AND 12 12 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a7444 : bv 32 := 0x00c5863b.
Lemma F_a7444 : fetch_word PSEGS (0xa7444 : word) = Some W_a7444.
Proof. vm_refl. Qed.
Lemma D_a7444 : decode_any W_a7444 = Some (Op32 ALU_ADD 12 11 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a7448 : bv 32 := 0x00c785b3.
Lemma F_a7448 : fetch_word PSEGS (0xa7448 : word) = Some W_a7448.
Proof. vm_refl. Qed.
Lemma D_a7448 : decode_any W_a7448 = Some (Op ALU_ADD 11 15 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a744c : bv 32 := 0x0025859b.
Lemma F_a744c : fetch_word PSEGS (0xa744c : word) = Some W_a744c.
Proof. vm_refl. Qed.
Lemma D_a744c : decode_any W_a744c = Some (OpImm32 11 11 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a7450 : bv 32 := 0x160526af.
Lemma F_a7450 : fetch_word PSEGS (0xa7450 : word) = Some W_a7450.
Proof. vm_refl. Qed.
Lemma D_a7450 : decode_any W_a7450 = Some (Lr AW true true 13 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a7454 : bv 32 := 0x00c69663.
Lemma F_a7454 : fetch_word PSEGS (0xa7454 : word) = Some W_a7454.
Proof. vm_refl. Qed.
Lemma D_a7454 : decode_any W_a7454 = Some (Branch BC_NE 13 12 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a7458 : bv 32 := 0x1eb5272f.
Lemma F_a7458 : fetch_word PSEGS (0xa7458 : word) = Some W_a7458.
Proof. vm_refl. Qed.
Lemma D_a7458 : decode_any W_a7458 = Some (Sc AW true true 14 10 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a745c : bv 32 := 0xfe071ae3.
Lemma F_a745c : fetch_word PSEGS (0xa745c : word) = Some W_a745c.
Proof. vm_refl. Qed.
Lemma D_a745c : decode_any W_a745c = Some (Branch BC_NE 14 0 8180, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a7460 : bv 32 := 0x0006859b.
Lemma F_a7460 : fetch_word PSEGS (0xa7460 : word) = Some W_a7460.
Proof. vm_refl. Qed.
Lemma D_a7460 : decode_any W_a7460 = Some (OpImm32 11 13 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a7464 : bv 32 := 0x0ac58a63.
Lemma F_a7464 : fetch_word PSEGS (0xa7464 : word) = Some W_a7464.
Proof. vm_refl. Qed.
Lemma D_a7464 : decode_any W_a7464 = Some (Branch BC_EQ 11 12 180, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a7468 : bv 32 := 0x01f5d613.
Lemma F_a7468 : fetch_word PSEGS (0xa7468 : word) = Some W_a7468.
Proof. vm_refl. Qed.
Lemma D_a7468 : decode_any W_a7468 = Some (ShiftImm ALU_SRL 12 11 31, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a746c : bv 32 := 0x00f67633.
Lemma F_a746c : fetch_word PSEGS (0xa746c : word) = Some W_a746c.
Proof. vm_refl. Qed.
Lemma D_a746c : decode_any W_a746c = Some (Op ALU_AND 12 12 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a7470 : bv 32 := 0x00c5863b.
Lemma F_a7470 : fetch_word PSEGS (0xa7470 : word) = Some W_a7470.
Proof. vm_refl. Qed.
Lemma D_a7470 : decode_any W_a7470 = Some (Op32 ALU_ADD 12 11 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a7474 : bv 32 := 0x00c785b3.
Lemma F_a7474 : fetch_word PSEGS (0xa7474 : word) = Some W_a7474.
Proof. vm_refl. Qed.
Lemma D_a7474 : decode_any W_a7474 = Some (Op ALU_ADD 11 15 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a7478 : bv 32 := 0x0025859b.
Lemma F_a7478 : fetch_word PSEGS (0xa7478 : word) = Some W_a7478.
Proof. vm_refl. Qed.
Lemma D_a7478 : decode_any W_a7478 = Some (OpImm32 11 11 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a747c : bv 32 := 0x160526af.
Lemma F_a747c : fetch_word PSEGS (0xa747c : word) = Some W_a747c.
Proof. vm_refl. Qed.
Lemma D_a747c : decode_any W_a747c = Some (Lr AW true true 13 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a7480 : bv 32 := 0x00c69663.
Lemma F_a7480 : fetch_word PSEGS (0xa7480 : word) = Some W_a7480.
Proof. vm_refl. Qed.
Lemma D_a7480 : decode_any W_a7480 = Some (Branch BC_NE 13 12 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a7484 : bv 32 := 0x1eb5272f.
Lemma F_a7484 : fetch_word PSEGS (0xa7484 : word) = Some W_a7484.
Proof. vm_refl. Qed.
Lemma D_a7484 : decode_any W_a7484 = Some (Sc AW true true 14 10 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a7488 : bv 32 := 0xfe071ae3.
Lemma F_a7488 : fetch_word PSEGS (0xa7488 : word) = Some W_a7488.
Proof. vm_refl. Qed.
Lemma D_a7488 : decode_any W_a7488 = Some (Branch BC_NE 14 0 8180, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a748c : bv 32 := 0x0006859b.
Lemma F_a748c : fetch_word PSEGS (0xa748c : word) = Some W_a748c.
Proof. vm_refl. Qed.
Lemma D_a748c : decode_any W_a748c = Some (OpImm32 11 13 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a7490 : bv 32 := 0x08c58463.
Lemma F_a7490 : fetch_word PSEGS (0xa7490 : word) = Some W_a7490.
Proof. vm_refl. Qed.
Lemma D_a7490 : decode_any W_a7490 = Some (Branch BC_EQ 11 12 136, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a7494 : bv 32 := 0x01f5d613.
Lemma F_a7494 : fetch_word PSEGS (0xa7494 : word) = Some W_a7494.
Proof. vm_refl. Qed.
Lemma D_a7494 : decode_any W_a7494 = Some (ShiftImm ALU_SRL 12 11 31, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a7518 : bv 32 := 0x00008067.
Lemma F_a7518 : fetch_word PSEGS (0xa7518 : word) = Some W_a7518.
Proof. vm_refl. Qed.
Lemma D_a7518 : decode_any W_a7518 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a75a8 : bv 32 := 0x00052583.
Lemma F_a75a8 : fetch_word PSEGS (0xa75a8 : word) = Some W_a75a8.
Proof. vm_refl. Qed.
Lemma D_a75a8 : decode_any W_a75a8 = Some (Load SZ4 true 11 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a75ac : bv 32 := 0x0005c463.
Lemma F_a75ac : fetch_word PSEGS (0xa75ac : word) = Some W_a75ac.
Proof. vm_refl. Qed.
Lemma D_a75ac : decode_any W_a75ac = Some (Branch BC_LT 11 0 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a75b0 : bv 32 := 0x00008067.
Lemma F_a75b0 : fetch_word PSEGS (0xa75b0 : word) = Some W_a75b0.
Proof. vm_refl. Qed.
Lemma D_a75b0 : decode_any W_a75b0 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a761c : bv 32 := 0x00050893.
Lemma F_a761c : fetch_word PSEGS (0xa761c : word) = Some W_a761c.
Proof. vm_refl. Qed.
Lemma D_a761c : decode_any W_a761c = Some (OpImm ALU_ADD 17 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a7620 : bv 32 := 0x00058513.
Lemma F_a7620 : fetch_word PSEGS (0xa7620 : word) = Some W_a7620.
Proof. vm_refl. Qed.
Lemma D_a7620 : decode_any W_a7620 = Some (OpImm ALU_ADD 10 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a7624 : bv 32 := 0x00060593.
Lemma F_a7624 : fetch_word PSEGS (0xa7624 : word) = Some W_a7624.
Proof. vm_refl. Qed.
Lemma D_a7624 : decode_any W_a7624 = Some (OpImm ALU_ADD 11 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a7628 : bv 32 := 0x00068613.
Lemma F_a7628 : fetch_word PSEGS (0xa7628 : word) = Some W_a7628.
Proof. vm_refl. Qed.
Lemma D_a7628 : decode_any W_a7628 = Some (OpImm ALU_ADD 12 13 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a762c : bv 32 := 0x00070693.
Lemma F_a762c : fetch_word PSEGS (0xa762c : word) = Some W_a762c.
Proof. vm_refl. Qed.
Lemma D_a762c : decode_any W_a762c = Some (OpImm ALU_ADD 13 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a7630 : bv 32 := 0x00078713.
Lemma F_a7630 : fetch_word PSEGS (0xa7630 : word) = Some W_a7630.
Proof. vm_refl. Qed.
Lemma D_a7630 : decode_any W_a7630 = Some (OpImm ALU_ADD 14 15 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a7634 : bv 32 := 0x00080793.
Lemma F_a7634 : fetch_word PSEGS (0xa7634 : word) = Some W_a7634.
Proof. vm_refl. Qed.
Lemma D_a7634 : decode_any W_a7634 = Some (OpImm ALU_ADD 15 16 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a7638 : bv 32 := 0x00000073.
Lemma F_a7638 : fetch_word PSEGS (0xa7638 : word) = Some W_a7638.
Proof. vm_refl. Qed.
Lemma D_a7638 : decode_any W_a7638 = Some (Ecall, 4%Z).
Proof. vm_refl. Qed.
Lemma E_a7638 : is_ecall W_a7638 = true.
Proof. reflexivity. Qed.

(* [comment removed for export] *)
Definition W_a763c : bv 32 := 0x00008067.
Lemma F_a763c : fetch_word PSEGS (0xa763c : word) = Some W_a763c.
Proof. vm_refl. Qed.
Lemma D_a763c : decode_any W_a763c = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a7640 : bv 32 := 0xfddff06f.
Lemma F_a7640 : fetch_word PSEGS (0xa7640 : word) = Some W_a7640.
Proof. vm_refl. Qed.
Lemma D_a7640 : decode_any W_a7640 = Some (Jal 0 2097116, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a787c : bv 32 := 0xfeb614e3.
Lemma F_a787c : fetch_word PSEGS (0xa787c : word) = Some W_a787c.
Proof. vm_refl. Qed.
Lemma D_a787c : decode_any W_a787c = Some (Branch BC_NE 12 11 8168, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a7880 : bv 32 := 0x00200a93.
Lemma F_a7880 : fetch_word PSEGS (0xa7880 : word) = Some W_a7880.
Proof. vm_refl. Qed.
Lemma D_a7880 : decode_any W_a7880 = Some (OpImm ALU_ADD 21 0 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a7884 : bv 32 := 0x03559a63.
Lemma F_a7884 : fetch_word PSEGS (0xa7884 : word) = Some W_a7884.
Proof. vm_refl. Qed.
Lemma D_a7884 : decode_any W_a7884 = Some (Branch BC_NE 11 21 52, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a7888 : bv 32 := 0x06200893.
Lemma F_a7888 : fetch_word PSEGS (0xa7888 : word) = Some W_a7888.
Proof. vm_refl. Qed.
Lemma D_a7888 : decode_any W_a7888 = Some (OpImm ALU_ADD 17 0 98, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a788c : bv 32 := 0x08100593.
Lemma F_a788c : fetch_word PSEGS (0xa788c : word) = Some W_a788c.
Proof. vm_refl. Qed.
Lemma D_a788c : decode_any W_a788c = Some (OpImm ALU_ADD 11 0 129, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a7890 : bv 32 := 0x00100613.
Lemma F_a7890 : fetch_word PSEGS (0xa7890 : word) = Some W_a7890.
Proof. vm_refl. Qed.
Lemma D_a7890 : decode_any W_a7890 = Some (OpImm ALU_ADD 12 0 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a7894 : bv 32 := 0xfda00693.
Lemma F_a7894 : fetch_word PSEGS (0xa7894 : word) = Some W_a7894.
Proof. vm_refl. Qed.
Lemma D_a7894 : decode_any W_a7894 = Some (OpImm ALU_ADD 13 0 4058, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a7898 : bv 32 := 0x000b8513.
Lemma F_a7898 : fetch_word PSEGS (0xa7898 : word) = Some W_a7898.
Proof. vm_refl. Qed.
Lemma D_a7898 : decode_any W_a7898 = Some (OpImm ALU_ADD 10 23 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a789c : bv 32 := 0x00000073.
Lemma F_a789c : fetch_word PSEGS (0xa789c : word) = Some W_a789c.
Proof. vm_refl. Qed.
Lemma D_a789c : decode_any W_a789c = Some (Ecall, 4%Z).
Proof. vm_refl. Qed.
Lemma E_a789c : is_ecall W_a789c = true.
Proof. reflexivity. Qed.

(* [comment removed for export] *)
Definition W_a78a0 : bv 32 := 0x00d51c63.
Lemma F_a78a0 : fetch_word PSEGS (0xa78a0 : word) = Some W_a78a0.
Proof. vm_refl. Qed.
Lemma D_a78a0 : decode_any W_a78a0 = Some (Branch BC_NE 10 13 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a78a4 : bv 32 := 0x06200893.
Lemma F_a78a4 : fetch_word PSEGS (0xa78a4 : word) = Some W_a78a4.
Proof. vm_refl. Qed.
Lemma D_a78a4 : decode_any W_a78a4 = Some (OpImm ALU_ADD 17 0 98, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a78a8 : bv 32 := 0x00100593.
Lemma F_a78a8 : fetch_word PSEGS (0xa78a8 : word) = Some W_a78a8.
Proof. vm_refl. Qed.
Lemma D_a78a8 : decode_any W_a78a8 = Some (OpImm ALU_ADD 11 0 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a78ac : bv 32 := 0x00100613.
Lemma F_a78ac : fetch_word PSEGS (0xa78ac : word) = Some W_a78ac.
Proof. vm_refl. Qed.
Lemma D_a78ac : decode_any W_a78ac = Some (OpImm ALU_ADD 12 0 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a78b0 : bv 32 := 0x000b8513.
Lemma F_a78b0 : fetch_word PSEGS (0xa78b0 : word) = Some W_a78b0.
Proof. vm_refl. Qed.
Lemma D_a78b0 : decode_any W_a78b0 = Some (OpImm ALU_ADD 10 23 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a78b4 : bv 32 := 0x00000073.
Lemma F_a78b4 : fetch_word PSEGS (0xa78b4 : word) = Some W_a78b4.
Proof. vm_refl. Qed.
Lemma D_a78b4 : decode_any W_a78b4 = Some (Ecall, 4%Z).
Proof. vm_refl. Qed.
Lemma E_a78b4 : is_ecall W_a78b4 = true.
Proof. reflexivity. Qed.

(* [comment removed for export] *)
Definition W_a78b8 : bv 32 := 0x00040513.
Lemma F_a78b8 : fetch_word PSEGS (0xa78b8 : word) = Some W_a78b8.
Proof. vm_refl. Qed.
Lemma D_a78b8 : decode_any W_a78b8 = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a78bc : bv 32 := 0x709000ef.
Lemma F_a78bc : fetch_word PSEGS (0xa78bc : word) = Some W_a78bc.
Proof. vm_refl. Qed.
Lemma D_a78bc : decode_any W_a78bc = Some (Jal 1 3848, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a7a18 : bv 32 := 0x1609252f.
Lemma F_a7a18 : fetch_word PSEGS (0xa7a18 : word) = Some W_a7a18.
Proof. vm_refl. Qed.
Lemma D_a7a18 : decode_any W_a7a18 = Some (Lr AW true true 10 18, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a7a1c : bv 32 := 0x01351663.
Lemma F_a7a1c : fetch_word PSEGS (0xa7a1c : word) = Some W_a7a1c.
Proof. vm_refl. Qed.
Lemma D_a7a1c : decode_any W_a7a1c = Some (Branch BC_NE 10 19 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a7a20 : bv 32 := 0x1f4925af.
Lemma F_a7a20 : fetch_word PSEGS (0xa7a20 : word) = Some W_a7a20.
Proof. vm_refl. Qed.
Lemma D_a7a20 : decode_any W_a7a20 = Some (Sc AW true true 11 18 20, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a7c10 : bv 32 := 0x00b50c63.
Lemma F_a7c10 : fetch_word PSEGS (0xa7c10 : word) = Some W_a7c10.
Proof. vm_refl. Qed.
Lemma D_a7c10 : decode_any W_a7c10 = Some (Branch BC_EQ 10 11 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a7ca0 : bv 32 := 0x1ec5272f.
Lemma F_a7ca0 : fetch_word PSEGS (0xa7ca0 : word) = Some W_a7ca0.
Proof. vm_refl. Qed.
Lemma D_a7ca0 : decode_any W_a7ca0 = Some (Sc AW true true 14 10 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a7ca4 : bv 32 := 0xfe071ae3.
Lemma F_a7ca4 : fetch_word PSEGS (0xa7ca4 : word) = Some W_a7ca4.
Proof. vm_refl. Qed.
Lemma D_a7ca4 : decode_any W_a7ca4 = Some (Branch BC_NE 14 0 8180, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a7ca8 : bv 32 := 0x0006869b.
Lemma F_a7ca8 : fetch_word PSEGS (0xa7ca8 : word) = Some W_a7ca8.
Proof. vm_refl. Qed.
Lemma D_a7ca8 : decode_any W_a7ca8 = Some (OpImm32 13 13 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a7d14 : bv 32 := 0x00100513.
Lemma F_a7d14 : fetch_word PSEGS (0xa7d14 : word) = Some W_a7d14.
Proof. vm_refl. Qed.
Lemma D_a7d14 : decode_any W_a7d14 = Some (OpImm ALU_ADD 10 0 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a7d18 : bv 32 := 0x00000593.
Lemma F_a7d18 : fetch_word PSEGS (0xa7d18 : word) = Some W_a7d18.
Proof. vm_refl. Qed.
Lemma D_a7d18 : decode_any W_a7d18 = Some (OpImm ALU_ADD 11 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a7d1c : bv 32 := 0x000010ef.
Lemma F_a7d1c : fetch_word PSEGS (0xa7d1c : word) = Some W_a7d1c.
Proof. vm_refl. Qed.
Lemma D_a7d1c : decode_any W_a7d1c = Some (Jal 1 4096, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a7d20 : bv 32 := 0x00040493.
Lemma F_a7d20 : fetch_word PSEGS (0xa7d20 : word) = Some W_a7d20.
Proof. vm_refl. Qed.
Lemma D_a7d20 : decode_any W_a7d20 = Some (OpImm ALU_ADD 9 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a7d24 : bv 32 := 0x000c3503.
Lemma F_a7d24 : fetch_word PSEGS (0xa7d24 : word) = Some W_a7d24.
Proof. vm_refl. Qed.
Lemma D_a7d24 : decode_any W_a7d24 = Some (Load SZ8 true 10 24 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a7d28 : bv 32 := 0x03013583.
Lemma F_a7d28 : fetch_word PSEGS (0xa7d28 : word) = Some W_a7d28.
Proof. vm_refl. Qed.
Lemma D_a7d28 : decode_any W_a7d28 = Some (Load SZ8 true 11 2 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a7d2c : bv 32 := 0x02b51e63.
Lemma F_a7d2c : fetch_word PSEGS (0xa7d2c : word) = Some W_a7d2c.
Proof. vm_refl. Qed.
Lemma D_a7d2c : decode_any W_a7d2c = Some (Branch BC_NE 10 11 60, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a7d30 : bv 32 := 0x00048513.
Lemma F_a7d30 : fetch_word PSEGS (0xa7d30 : word) = Some W_a7d30.
Proof. vm_refl. Qed.
Lemma D_a7d30 : decode_any W_a7d30 = Some (OpImm ALU_ADD 10 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a7d34 : bv 32 := 0x08813083.
Lemma F_a7d34 : fetch_word PSEGS (0xa7d34 : word) = Some W_a7d34.
Proof. vm_refl. Qed.
Lemma D_a7d34 : decode_any W_a7d34 = Some (Load SZ8 true 1 2 136, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a7d38 : bv 32 := 0x08013403.
Lemma F_a7d38 : fetch_word PSEGS (0xa7d38 : word) = Some W_a7d38.
Proof. vm_refl. Qed.
Lemma D_a7d38 : decode_any W_a7d38 = Some (Load SZ8 true 8 2 128, 4%Z).
Proof. vm_refl. Qed.

