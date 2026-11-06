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
Definition W_ab534 : bv 32 := 0xff010113.
Lemma F_ab534 : fetch_word PSEGS (0xab534 : word) = Some W_ab534.
Proof. vm_refl. Qed.
Lemma D_ab534 : decode_any W_ab534 = Some (OpImm ALU_ADD 2 2 4080, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ab538 : bv 32 := 0x00113423.
Lemma F_ab538 : fetch_word PSEGS (0xab538 : word) = Some W_ab538.
Proof. vm_refl. Qed.
Lemma D_ab538 : decode_any W_ab538 = Some (Store SZ8 2 1 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ab53c : bv 32 := 0xcc8f00ef.
Lemma F_ab53c : fetch_word PSEGS (0xab53c : word) = Some W_ab53c.
Proof. vm_refl. Qed.
Lemma D_ab53c : decode_any W_ab53c = Some (Jal 1 2032840, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ab540 : bv 32 := 0x00050593.
Lemma F_ab540 : fetch_word PSEGS (0xab540 : word) = Some W_ab540.
Proof. vm_refl. Qed.
Lemma D_ab540 : decode_any W_ab540 = Some (OpImm ALU_ADD 11 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ab544 : bv 32 := 0x03900513.
Lemma F_ab544 : fetch_word PSEGS (0xab544 : word) = Some W_ab544.
Proof. vm_refl. Qed.
Lemma D_ab544 : decode_any W_ab544 = Some (OpImm ALU_ADD 10 0 57, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ab548 : bv 32 := 0x00000613.
Lemma F_ab548 : fetch_word PSEGS (0xab548 : word) = Some W_ab548.
Proof. vm_refl. Qed.
Lemma D_ab548 : decode_any W_ab548 = Some (OpImm ALU_ADD 12 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ab54c : bv 32 := 0x00000693.
Lemma F_ab54c : fetch_word PSEGS (0xab54c : word) = Some W_ab54c.
Proof. vm_refl. Qed.
Lemma D_ab54c : decode_any W_ab54c = Some (OpImm ALU_ADD 13 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ab550 : bv 32 := 0x00000713.
Lemma F_ab550 : fetch_word PSEGS (0xab550 : word) = Some W_ab550.
Proof. vm_refl. Qed.
Lemma D_ab550 : decode_any W_ab550 = Some (OpImm ALU_ADD 14 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ab554 : bv 32 := 0x00000793.
Lemma F_ab554 : fetch_word PSEGS (0xab554 : word) = Some W_ab554.
Proof. vm_refl. Qed.
Lemma D_ab554 : decode_any W_ab554 = Some (OpImm ALU_ADD 15 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ab558 : bv 32 := 0x00000813.
Lemma F_ab558 : fetch_word PSEGS (0xab558 : word) = Some W_ab558.
Proof. vm_refl. Qed.
Lemma D_ab558 : decode_any W_ab558 = Some (OpImm ALU_ADD 16 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ab55c : bv 32 := 0x8e4fc0ef.
Lemma F_ab55c : fetch_word PSEGS (0xab55c : word) = Some W_ab55c.
Proof. vm_refl. Qed.
Lemma D_ab55c : decode_any W_ab55c = Some (Jal 1 2080996, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ab560 : bv 32 := 0x0005051b.
Lemma F_ab560 : fetch_word PSEGS (0xab560 : word) = Some W_ab560.
Proof. vm_refl. Qed.
Lemma D_ab560 : decode_any W_ab560 = Some (OpImm32 10 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ab564 : bv 32 := 0x00450593.
Lemma F_ab564 : fetch_word PSEGS (0xab564 : word) = Some W_ab564.
Proof. vm_refl. Qed.
Lemma D_ab564 : decode_any W_ab564 = Some (OpImm ALU_ADD 11 10 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ab568 : bv 32 := 0x0015b593.
Lemma F_ab568 : fetch_word PSEGS (0xab568 : word) = Some W_ab568.
Proof. vm_refl. Qed.
Lemma D_ab568 : decode_any W_ab568 = Some (OpImm ALU_SLTU 11 11 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ab56c : bv 32 := 0xfff58593.
Lemma F_ab56c : fetch_word PSEGS (0xab56c : word) = Some W_ab56c.
Proof. vm_refl. Qed.
Lemma D_ab56c : decode_any W_ab56c = Some (OpImm ALU_ADD 11 11 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ab570 : bv 32 := 0x00a5f533.
Lemma F_ab570 : fetch_word PSEGS (0xab570 : word) = Some W_ab570.
Proof. vm_refl. Qed.
Lemma D_ab570 : decode_any W_ab570 = Some (Op ALU_AND 10 11 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ab574 : bv 32 := 0xce1ea0ef.
Lemma F_ab574 : fetch_word PSEGS (0xab574 : word) = Some W_ab574.
Proof. vm_refl. Qed.
Lemma D_ab574 : decode_any W_ab574 = Some (Jal 1 2010336, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ab578 : bv 32 := 0x0005051b.
Lemma F_ab578 : fetch_word PSEGS (0xab578 : word) = Some W_ab578.
Proof. vm_refl. Qed.
Lemma D_ab578 : decode_any W_ab578 = Some (OpImm32 10 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ab57c : bv 32 := 0x00813083.
Lemma F_ab57c : fetch_word PSEGS (0xab57c : word) = Some W_ab57c.
Proof. vm_refl. Qed.
Lemma D_ab57c : decode_any W_ab57c = Some (Load SZ8 true 1 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ab580 : bv 32 := 0x01010113.
Lemma F_ab580 : fetch_word PSEGS (0xab580 : word) = Some W_ab580.
Proof. vm_refl. Qed.
Lemma D_ab580 : decode_any W_ab580 = Some (OpImm ALU_ADD 2 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ab584 : bv 32 := 0x00008067.
Lemma F_ab584 : fetch_word PSEGS (0xab584 : word) = Some W_ab584.
Proof. vm_refl. Qed.
Lemma D_ab584 : decode_any W_ab584 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ab594 : bv 32 := 0xff010113.
Lemma F_ab594 : fetch_word PSEGS (0xab594 : word) = Some W_ab594.
Proof. vm_refl. Qed.
Lemma D_ab594 : decode_any W_ab594 = Some (OpImm ALU_ADD 2 2 4080, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ab598 : bv 32 := 0x00113423.
Lemma F_ab598 : fetch_word PSEGS (0xab598 : word) = Some W_ab598.
Proof. vm_refl. Qed.
Lemma D_ab598 : decode_any W_ab598 = Some (Store SZ8 2 1 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ab59c : bv 32 := 0x00060693.
Lemma F_ab59c : fetch_word PSEGS (0xab59c : word) = Some W_ab59c.
Proof. vm_refl. Qed.
Lemma D_ab59c : decode_any W_ab59c = Some (OpImm ALU_ADD 13 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ab5a0 : bv 32 := 0x00058613.
Lemma F_ab5a0 : fetch_word PSEGS (0xab5a0 : word) = Some W_ab5a0.
Proof. vm_refl. Qed.
Lemma D_ab5a0 : decode_any W_ab5a0 = Some (OpImm ALU_ADD 12 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ab5a4 : bv 32 := 0x00050593.
Lemma F_ab5a4 : fetch_word PSEGS (0xab5a4 : word) = Some W_ab5a4.
Proof. vm_refl. Qed.
Lemma D_ab5a4 : decode_any W_ab5a4 = Some (OpImm ALU_ADD 11 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ab5a8 : bv 32 := 0x03f00513.
Lemma F_ab5a8 : fetch_word PSEGS (0xab5a8 : word) = Some W_ab5a8.
Proof. vm_refl. Qed.
Lemma D_ab5a8 : decode_any W_ab5a8 = Some (OpImm ALU_ADD 10 0 63, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ab5ac : bv 32 := 0x00000713.
Lemma F_ab5ac : fetch_word PSEGS (0xab5ac : word) = Some W_ab5ac.
Proof. vm_refl. Qed.
Lemma D_ab5ac : decode_any W_ab5ac = Some (OpImm ALU_ADD 14 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ab5b0 : bv 32 := 0x00000793.
Lemma F_ab5b0 : fetch_word PSEGS (0xab5b0 : word) = Some W_ab5b0.
Proof. vm_refl. Qed.
Lemma D_ab5b0 : decode_any W_ab5b0 = Some (OpImm ALU_ADD 15 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ab5b4 : bv 32 := 0x00000813.
Lemma F_ab5b4 : fetch_word PSEGS (0xab5b4 : word) = Some W_ab5b4.
Proof. vm_refl. Qed.
Lemma D_ab5b4 : decode_any W_ab5b4 = Some (OpImm ALU_ADD 16 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ab5b8 : bv 32 := 0x888fc0ef.
Lemma F_ab5b8 : fetch_word PSEGS (0xab5b8 : word) = Some W_ab5b8.
Proof. vm_refl. Qed.
Lemma D_ab5b8 : decode_any W_ab5b8 = Some (Jal 1 2080904, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ab5bc : bv 32 := 0x00813083.
Lemma F_ab5bc : fetch_word PSEGS (0xab5bc : word) = Some W_ab5bc.
Proof. vm_refl. Qed.
Lemma D_ab5bc : decode_any W_ab5bc = Some (Load SZ8 true 1 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ab5c0 : bv 32 := 0x01010113.
Lemma F_ab5c0 : fetch_word PSEGS (0xab5c0 : word) = Some W_ab5c0.
Proof. vm_refl. Qed.
Lemma D_ab5c0 : decode_any W_ab5c0 = Some (OpImm ALU_ADD 2 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_ab5c4 : bv 32 := 0xc91ea06f.
Lemma F_ab5c4 : fetch_word PSEGS (0xab5c4 : word) = Some W_ab5c4.
Proof. vm_refl. Qed.
Lemma D_ab5c4 : decode_any W_ab5c4 = Some (Jal 0 2010256, 4%Z).
Proof. vm_refl. Qed.

