(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib Require Import ImgU.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Abbreviation USEGS := ImgU.M.loaded_segments.
Open Scope bv_scope.

(* [comment removed for export] *)
Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

(* [comment removed for export] *)
Definition W_ab528 : bv 32 := 0x0246c703.
Lemma F_ab528 : fetch_word USEGS (0xab528 : word) = Some W_ab528.
Proof. vm_refl. Qed.
Lemma D_ab528 : decode_any W_ab528 = Some (Load SZ1 false 14 13 36, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ab52c : bv 32 := 0x0256c783.
Lemma F_ab52c : fetch_word USEGS (0xab52c : word) = Some W_ab52c.
Proof. vm_refl. Qed.
Lemma D_ab52c : decode_any W_ab52c = Some (Load SZ1 false 15 13 37, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ab530 : bv 32 := 0x0266c803.
Lemma F_ab530 : fetch_word USEGS (0xab530 : word) = Some W_ab530.
Proof. vm_refl. Qed.
Lemma D_ab530 : decode_any W_ab530 = Some (Load SZ1 false 16 13 38, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ab534 : bv 32 := 0x0276c883.
Lemma F_ab534 : fetch_word USEGS (0xab534 : word) = Some W_ab534.
Proof. vm_refl. Qed.
Lemma D_ab534 : decode_any W_ab534 = Some (Load SZ1 false 17 13 39, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ab538 : bv 32 := 0x01871713.
Lemma F_ab538 : fetch_word USEGS (0xab538 : word) = Some W_ab538.
Proof. vm_refl. Qed.
Lemma D_ab538 : decode_any W_ab538 = Some (ShiftImm ALU_SLL 14 14 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ab53c : bv 32 := 0x01079793.
Lemma F_ab53c : fetch_word USEGS (0xab53c : word) = Some W_ab53c.
Proof. vm_refl. Qed.
Lemma D_ab53c : decode_any W_ab53c = Some (ShiftImm ALU_SLL 15 15 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ab540 : bv 32 := 0x00881813.
Lemma F_ab540 : fetch_word USEGS (0xab540 : word) = Some W_ab540.
Proof. vm_refl. Qed.
Lemma D_ab540 : decode_any W_ab540 = Some (ShiftImm ALU_SLL 16 16 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ab544 : bv 32 := 0x00e7e733.
Lemma F_ab544 : fetch_word USEGS (0xab544 : word) = Some W_ab544.
Proof. vm_refl. Qed.
Lemma D_ab544 : decode_any W_ab544 = Some (Op ALU_OR 14 15 14, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ab548 : bv 32 := 0x011867b3.
Lemma F_ab548 : fetch_word USEGS (0xab548 : word) = Some W_ab548.
Proof. vm_refl. Qed.
Lemma D_ab548 : decode_any W_ab548 = Some (Op ALU_OR 15 16 17, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ab54c : bv 32 := 0x00f76733.
Lemma F_ab54c : fetch_word USEGS (0xab54c : word) = Some W_ab54c.
Proof. vm_refl. Qed.
Lemma D_ab54c : decode_any W_ab54c = Some (Op ALU_OR 14 14 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ab550 : bv 32 := 0x00171793.
Lemma F_ab550 : fetch_word USEGS (0xab550 : word) = Some W_ab550.
Proof. vm_refl. Qed.
Lemma D_ab550 : decode_any W_ab550 = Some (ShiftImm ALU_SLL 15 14 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ab554 : bv 32 := 0x00371713.
Lemma F_ab554 : fetch_word USEGS (0xab554 : word) = Some W_ab554.
Proof. vm_refl. Qed.
Lemma D_ab554 : decode_any W_ab554 = Some (ShiftImm ALU_SLL 14 14 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ab558 : bv 32 := 0x40f70733.
Lemma F_ab558 : fetch_word USEGS (0xab558 : word) = Some W_ab558.
Proof. vm_refl. Qed.
Lemma D_ab558 : decode_any W_ab558 = Some (Op ALU_SUB 14 14 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ab55c : bv 32 := 0x00a777b3.
Lemma F_ab55c : fetch_word USEGS (0xab55c : word) = Some W_ab55c.
Proof. vm_refl. Qed.
Lemma D_ab55c : decode_any W_ab55c = Some (Op ALU_AND 15 14 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ab560 : bv 32 := 0x00f60733.
Lemma F_ab560 : fetch_word USEGS (0xab560 : word) = Some W_ab560.
Proof. vm_refl. Qed.
Lemma D_ab560 : decode_any W_ab560 = Some (Op ALU_ADD 14 12 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ab564 : bv 32 := 0x02eb3423.
Lemma F_ab564 : fetch_word USEGS (0xab564 : word) = Some W_ab564.
Proof. vm_refl. Qed.
Lemma D_ab564 : decode_any W_ab564 = Some (Store SZ8 22 14 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ab568 : bv 32 := 0x0286c803.
Lemma F_ab568 : fetch_word USEGS (0xab568 : word) = Some W_ab568.
Proof. vm_refl. Qed.
Lemma D_ab568 : decode_any W_ab568 = Some (Load SZ1 false 16 13 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ab56c : bv 32 := 0x0296c883.
Lemma F_ab56c : fetch_word USEGS (0xab56c : word) = Some W_ab56c.
Proof. vm_refl. Qed.
Lemma D_ab56c : decode_any W_ab56c = Some (Load SZ1 false 17 13 41, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ab570 : bv 32 := 0x02a6c283.
Lemma F_ab570 : fetch_word USEGS (0xab570 : word) = Some W_ab570.
Proof. vm_refl. Qed.
Lemma D_ab570 : decode_any W_ab570 = Some (Load SZ1 false 5 13 42, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ab574 : bv 32 := 0x02b6c683.
Lemma F_ab574 : fetch_word USEGS (0xab574 : word) = Some W_ab574.
Proof. vm_refl. Qed.
Lemma D_ab574 : decode_any W_ab574 = Some (Load SZ1 false 13 13 43, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ab578 : bv 32 := 0x01881813.
Lemma F_ab578 : fetch_word USEGS (0xab578 : word) = Some W_ab578.
Proof. vm_refl. Qed.
Lemma D_ab578 : decode_any W_ab578 = Some (ShiftImm ALU_SLL 16 16 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ab588 : bv 32 := 0x00d2e6b3.
Lemma F_ab588 : fetch_word USEGS (0xab588 : word) = Some W_ab588.
Proof. vm_refl. Qed.
Lemma D_ab588 : decode_any W_ab588 = Some (Op ALU_OR 13 5 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ab58c : bv 32 := 0x038b3883.
Lemma F_ab58c : fetch_word USEGS (0xab58c : word) = Some W_ab58c.
Proof. vm_refl. Qed.
Lemma D_ab58c : decode_any W_ab58c = Some (Load SZ8 true 17 22 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ab590 : bv 32 := 0x00d866b3.
Lemma F_ab590 : fetch_word USEGS (0xab590 : word) = Some W_ab590.
Proof. vm_refl. Qed.
Lemma D_ab590 : decode_any W_ab590 = Some (Op ALU_OR 13 16 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ab594 : bv 32 := 0x00d706b3.
Lemma F_ab594 : fetch_word USEGS (0xab594 : word) = Some W_ab594.
Proof. vm_refl. Qed.
Lemma D_ab594 : decode_any W_ab594 = Some (Op ALU_ADD 13 14 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ab598 : bv 32 := 0x02db3823.
Lemma F_ab598 : fetch_word USEGS (0xab598 : word) = Some W_ab598.
Proof. vm_refl. Qed.
Lemma D_ab598 : decode_any W_ab598 = Some (Store SZ8 22 13 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ab59c : bv 32 := 0x01158833.
Lemma F_ab59c : fetch_word USEGS (0xab59c : word) = Some W_ab59c.
Proof. vm_refl. Qed.
Lemma D_ab59c : decode_any W_ab59c = Some (Op ALU_ADD 16 11 17, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ab5a0 : bv 32 := 0xfff84583.
Lemma F_ab5a0 : fetch_word USEGS (0xab5a0 : word) = Some W_ab5a0.
Proof. vm_refl. Qed.
Lemma D_ab5a0 : decode_any W_ab5a0 = Some (Load SZ1 false 11 16 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ab5a4 : bv 32 := 0x00a00693.
Lemma F_ab5a4 : fetch_word USEGS (0xab5a4 : word) = Some W_ab5a4.
Proof. vm_refl. Qed.
Lemma D_ab5a4 : decode_any W_ab5a4 = Some (OpImm ALU_ADD 13 0 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ab5a8 : bv 32 := 0x02d59263.
Lemma F_ab5a8 : fetch_word USEGS (0xab5a8 : word) = Some W_ab5a8.
Proof. vm_refl. Qed.
Lemma D_ab5a8 : decode_any W_ab5a8 = Some (Branch BC_NE 11 13 36, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ab5ac : bv 32 := 0xffe80513.
Lemma F_ab5ac : fetch_word USEGS (0xab5ac : word) = Some W_ab5ac.
Proof. vm_refl. Qed.
Lemma D_ab5ac : decode_any W_ab5ac = Some (OpImm ALU_ADD 10 16 4094, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ab5b0 : bv 32 := 0x00a13423.
Lemma F_ab5b0 : fetch_word USEGS (0xab5b0 : word) = Some W_ab5b0.
Proof. vm_refl. Qed.
Lemma D_ab5b0 : decode_any W_ab5b0 = Some (Store SZ8 2 10 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ab5b4 : bv 32 := 0x00054603.
Lemma F_ab5b4 : fetch_word USEGS (0xab5b4 : word) = Some W_ab5b4.
Proof. vm_refl. Qed.
Lemma D_ab5b4 : decode_any W_ab5b4 = Some (Load SZ1 false 12 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ab5b8 : bv 32 := 0xfff50513.
Lemma F_ab5b8 : fetch_word USEGS (0xab5b8 : word) = Some W_ab5b8.
Proof. vm_refl. Qed.
Lemma D_ab5b8 : decode_any W_ab5b8 = Some (OpImm ALU_ADD 10 10 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_abc2c : bv 32 := 0xff010113.
Lemma F_abc2c : fetch_word USEGS (0xabc2c : word) = Some W_abc2c.
Proof. vm_refl. Qed.
Lemma D_abc2c : decode_any W_abc2c = Some (OpImm ALU_ADD 2 2 4080, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_abc30 : bv 32 := 0x00113423.
Lemma F_abc30 : fetch_word USEGS (0xabc30 : word) = Some W_abc30.
Proof. vm_refl. Qed.
Lemma D_abc30 : decode_any W_abc30 = Some (Store SZ8 2 1 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_abc34 : bv 32 := 0xcc8f00ef.
Lemma F_abc34 : fetch_word USEGS (0xabc34 : word) = Some W_abc34.
Proof. vm_refl. Qed.
Lemma D_abc34 : decode_any W_abc34 = Some (Jal 1 2032840, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_abc38 : bv 32 := 0x00050593.
Lemma F_abc38 : fetch_word USEGS (0xabc38 : word) = Some W_abc38.
Proof. vm_refl. Qed.
Lemma D_abc38 : decode_any W_abc38 = Some (OpImm ALU_ADD 11 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_abc3c : bv 32 := 0x03900513.
Lemma F_abc3c : fetch_word USEGS (0xabc3c : word) = Some W_abc3c.
Proof. vm_refl. Qed.
Lemma D_abc3c : decode_any W_abc3c = Some (OpImm ALU_ADD 10 0 57, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_abc40 : bv 32 := 0x00000613.
Lemma F_abc40 : fetch_word USEGS (0xabc40 : word) = Some W_abc40.
Proof. vm_refl. Qed.
Lemma D_abc40 : decode_any W_abc40 = Some (OpImm ALU_ADD 12 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_abc44 : bv 32 := 0x00000693.
Lemma F_abc44 : fetch_word USEGS (0xabc44 : word) = Some W_abc44.
Proof. vm_refl. Qed.
Lemma D_abc44 : decode_any W_abc44 = Some (OpImm ALU_ADD 13 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_abc48 : bv 32 := 0x00000713.
Lemma F_abc48 : fetch_word USEGS (0xabc48 : word) = Some W_abc48.
Proof. vm_refl. Qed.
Lemma D_abc48 : decode_any W_abc48 = Some (OpImm ALU_ADD 14 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_abc4c : bv 32 := 0x00000793.
Lemma F_abc4c : fetch_word USEGS (0xabc4c : word) = Some W_abc4c.
Proof. vm_refl. Qed.
Lemma D_abc4c : decode_any W_abc4c = Some (OpImm ALU_ADD 15 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_abc50 : bv 32 := 0x00000813.
Lemma F_abc50 : fetch_word USEGS (0xabc50 : word) = Some W_abc50.
Proof. vm_refl. Qed.
Lemma D_abc50 : decode_any W_abc50 = Some (OpImm ALU_ADD 16 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_abc54 : bv 32 := 0x8e4fc0ef.
Lemma F_abc54 : fetch_word USEGS (0xabc54 : word) = Some W_abc54.
Proof. vm_refl. Qed.
Lemma D_abc54 : decode_any W_abc54 = Some (Jal 1 2080996, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_abc58 : bv 32 := 0x0005051b.
Lemma F_abc58 : fetch_word USEGS (0xabc58 : word) = Some W_abc58.
Proof. vm_refl. Qed.
Lemma D_abc58 : decode_any W_abc58 = Some (OpImm32 10 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_abc5c : bv 32 := 0x00450593.
Lemma F_abc5c : fetch_word USEGS (0xabc5c : word) = Some W_abc5c.
Proof. vm_refl. Qed.
Lemma D_abc5c : decode_any W_abc5c = Some (OpImm ALU_ADD 11 10 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_abc60 : bv 32 := 0x0015b593.
Lemma F_abc60 : fetch_word USEGS (0xabc60 : word) = Some W_abc60.
Proof. vm_refl. Qed.
Lemma D_abc60 : decode_any W_abc60 = Some (OpImm ALU_SLTU 11 11 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_abc64 : bv 32 := 0xfff58593.
Lemma F_abc64 : fetch_word USEGS (0xabc64 : word) = Some W_abc64.
Proof. vm_refl. Qed.
Lemma D_abc64 : decode_any W_abc64 = Some (OpImm ALU_ADD 11 11 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_abc68 : bv 32 := 0x00a5f533.
Lemma F_abc68 : fetch_word USEGS (0xabc68 : word) = Some W_abc68.
Proof. vm_refl. Qed.
Lemma D_abc68 : decode_any W_abc68 = Some (Op ALU_AND 10 11 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_abc6c : bv 32 := 0xce1ea0ef.
Lemma F_abc6c : fetch_word USEGS (0xabc6c : word) = Some W_abc6c.
Proof. vm_refl. Qed.
Lemma D_abc6c : decode_any W_abc6c = Some (Jal 1 2010336, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_abc70 : bv 32 := 0x0005051b.
Lemma F_abc70 : fetch_word USEGS (0xabc70 : word) = Some W_abc70.
Proof. vm_refl. Qed.
Lemma D_abc70 : decode_any W_abc70 = Some (OpImm32 10 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_abc74 : bv 32 := 0x00813083.
Lemma F_abc74 : fetch_word USEGS (0xabc74 : word) = Some W_abc74.
Proof. vm_refl. Qed.
Lemma D_abc74 : decode_any W_abc74 = Some (Load SZ8 true 1 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_abc78 : bv 32 := 0x01010113.
Lemma F_abc78 : fetch_word USEGS (0xabc78 : word) = Some W_abc78.
Proof. vm_refl. Qed.
Lemma D_abc78 : decode_any W_abc78 = Some (OpImm ALU_ADD 2 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_abc7c : bv 32 := 0x00008067.
Lemma F_abc7c : fetch_word USEGS (0xabc7c : word) = Some W_abc7c.
Proof. vm_refl. Qed.
Lemma D_abc7c : decode_any W_abc7c = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_abc8c : bv 32 := 0xff010113.
Lemma F_abc8c : fetch_word USEGS (0xabc8c : word) = Some W_abc8c.
Proof. vm_refl. Qed.
Lemma D_abc8c : decode_any W_abc8c = Some (OpImm ALU_ADD 2 2 4080, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_abc90 : bv 32 := 0x00113423.
Lemma F_abc90 : fetch_word USEGS (0xabc90 : word) = Some W_abc90.
Proof. vm_refl. Qed.
Lemma D_abc90 : decode_any W_abc90 = Some (Store SZ8 2 1 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_abc94 : bv 32 := 0x00060693.
Lemma F_abc94 : fetch_word USEGS (0xabc94 : word) = Some W_abc94.
Proof. vm_refl. Qed.
Lemma D_abc94 : decode_any W_abc94 = Some (OpImm ALU_ADD 13 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_abc98 : bv 32 := 0x00058613.
Lemma F_abc98 : fetch_word USEGS (0xabc98 : word) = Some W_abc98.
Proof. vm_refl. Qed.
Lemma D_abc98 : decode_any W_abc98 = Some (OpImm ALU_ADD 12 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_abc9c : bv 32 := 0x00050593.
Lemma F_abc9c : fetch_word USEGS (0xabc9c : word) = Some W_abc9c.
Proof. vm_refl. Qed.
Lemma D_abc9c : decode_any W_abc9c = Some (OpImm ALU_ADD 11 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_abca0 : bv 32 := 0x03f00513.
Lemma F_abca0 : fetch_word USEGS (0xabca0 : word) = Some W_abca0.
Proof. vm_refl. Qed.
Lemma D_abca0 : decode_any W_abca0 = Some (OpImm ALU_ADD 10 0 63, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_abca4 : bv 32 := 0x00000713.
Lemma F_abca4 : fetch_word USEGS (0xabca4 : word) = Some W_abca4.
Proof. vm_refl. Qed.
Lemma D_abca4 : decode_any W_abca4 = Some (OpImm ALU_ADD 14 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_abca8 : bv 32 := 0x00000793.
Lemma F_abca8 : fetch_word USEGS (0xabca8 : word) = Some W_abca8.
Proof. vm_refl. Qed.
Lemma D_abca8 : decode_any W_abca8 = Some (OpImm ALU_ADD 15 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_abcac : bv 32 := 0x00000813.
Lemma F_abcac : fetch_word USEGS (0xabcac : word) = Some W_abcac.
Proof. vm_refl. Qed.
Lemma D_abcac : decode_any W_abcac = Some (OpImm ALU_ADD 16 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_abcb0 : bv 32 := 0x888fc0ef.
Lemma F_abcb0 : fetch_word USEGS (0xabcb0 : word) = Some W_abcb0.
Proof. vm_refl. Qed.
Lemma D_abcb0 : decode_any W_abcb0 = Some (Jal 1 2080904, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_abcb4 : bv 32 := 0x00813083.
Lemma F_abcb4 : fetch_word USEGS (0xabcb4 : word) = Some W_abcb4.
Proof. vm_refl. Qed.
Lemma D_abcb4 : decode_any W_abcb4 = Some (Load SZ8 true 1 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_abcb8 : bv 32 := 0x01010113.
Lemma F_abcb8 : fetch_word USEGS (0xabcb8 : word) = Some W_abcb8.
Proof. vm_refl. Qed.
Lemma D_abcb8 : decode_any W_abcb8 = Some (OpImm ALU_ADD 2 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_abcbc : bv 32 := 0xc91ea06f.
Lemma F_abcbc : fetch_word USEGS (0xabcbc : word) = Some W_abcbc.
Proof. vm_refl. Qed.
Lemma D_abcbc : decode_any W_abcbc = Some (Jal 0 2010256, 4%Z).
Proof. vm_refl. Qed.

