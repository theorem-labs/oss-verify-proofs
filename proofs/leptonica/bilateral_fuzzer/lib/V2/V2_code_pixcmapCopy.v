(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
(* [comment removed for export] *)

From OssFuzzTheorems.Proofs.leptonica.bilateral_fuzzer.lib.H Require GcFlushS2.   (* [comment removed for export] *)
From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OssFuzzTheorems.leptonica.bilateral_fuzzer.images Require Import Ubsan.
Open Scope bv_scope.
#[local] Hint Extern 0 (BvWf _ _) => (lazymatch goal with |- BvWf ?n ?v => is_closed_term n; is_closed_term v end; exact I) : typeclass_instances.   (* [comment removed for export] *)

(* [comment removed for export] *)
Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

Definition W_1d61c : bv 32 := 0xfe010113.
Lemma F_1d61c : fetch_word Ubsan.M.loaded_segments (0x1d61c : word) = Some W_1d61c.
Proof. vm_refl. Qed.
Lemma D_1d61c : decode_any W_1d61c = Some (OpImm ALU_ADD 2 2 4064, 4%Z).
Proof. vm_refl. Qed.

Definition W_1d620 : bv 32 := 0x00113c23.
Lemma F_1d620 : fetch_word Ubsan.M.loaded_segments (0x1d620 : word) = Some W_1d620.
Proof. vm_refl. Qed.
Lemma D_1d620 : decode_any W_1d620 = Some (Store SZ8 2 1 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_1d624 : bv 32 := 0x00813823.
Lemma F_1d624 : fetch_word Ubsan.M.loaded_segments (0x1d624 : word) = Some W_1d624.
Proof. vm_refl. Qed.
Lemma D_1d624 : decode_any W_1d624 = Some (Store SZ8 2 8 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_1d628 : bv 32 := 0x00913423.
Lemma F_1d628 : fetch_word Ubsan.M.loaded_segments (0x1d628 : word) = Some W_1d628.
Proof. vm_refl. Qed.
Lemma D_1d628 : decode_any W_1d628 = Some (Store SZ8 2 9 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_1d62c : bv 32 := 0x06050c63.
Lemma F_1d62c : fetch_word Ubsan.M.loaded_segments (0x1d62c : word) = Some W_1d62c.
Proof. vm_refl. Qed.
Lemma D_1d62c : decode_any W_1d62c = Some (Branch BC_EQ 10 0 120, 4%Z).
Proof. vm_refl. Qed.

Definition W_1d630 : bv 32 := 0x00050413.
Lemma F_1d630 : fetch_word Ubsan.M.loaded_segments (0x1d630 : word) = Some W_1d630.
Proof. vm_refl. Qed.
Lemma D_1d630 : decode_any W_1d630 = Some (OpImm ALU_ADD 8 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_1d634 : bv 32 := 0x00410613.
Lemma F_1d634 : fetch_word Ubsan.M.loaded_segments (0x1d634 : word) = Some W_1d634.
Proof. vm_refl. Qed.
Lemma D_1d634 : decode_any W_1d634 = Some (OpImm ALU_ADD 12 2 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_1d638 : bv 32 := 0x00000593.
Lemma F_1d638 : fetch_word Ubsan.M.loaded_segments (0x1d638 : word) = Some W_1d638.
Proof. vm_refl. Qed.
Lemma D_1d638 : decode_any W_1d638 = Some (OpImm ALU_ADD 11 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_1d63c : bv 32 := 0x0f8000ef.
Lemma F_1d63c : fetch_word Ubsan.M.loaded_segments (0x1d63c : word) = Some W_1d63c.
Proof. vm_refl. Qed.
Lemma D_1d63c : decode_any W_1d63c = Some (Jal 1 248, 4%Z).
Proof. vm_refl. Qed.

Definition W_1d640 : bv 32 := 0x00412503.
Lemma F_1d640 : fetch_word Ubsan.M.loaded_segments (0x1d640 : word) = Some W_1d640.
Proof. vm_refl. Qed.
Lemma D_1d640 : decode_any W_1d640 = Some (Load SZ4 true 10 2 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_1d644 : bv 32 := 0x08050e63.
Lemma F_1d644 : fetch_word Ubsan.M.loaded_segments (0x1d644 : word) = Some W_1d644.
Proof. vm_refl. Qed.
Lemma D_1d644 : decode_any W_1d644 = Some (Branch BC_EQ 10 0 156, 4%Z).
Proof. vm_refl. Qed.

Definition W_1d648 : bv 32 := 0x00100513.
Lemma F_1d648 : fetch_word Ubsan.M.loaded_segments (0x1d648 : word) = Some W_1d648.
Proof. vm_refl. Qed.
Lemma D_1d648 : decode_any W_1d648 = Some (OpImm ALU_ADD 10 0 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_1d64c : bv 32 := 0x01800593.
Lemma F_1d64c : fetch_word Ubsan.M.loaded_segments (0x1d64c : word) = Some W_1d64c.
Proof. vm_refl. Qed.
Lemma D_1d64c : decode_any W_1d64c = Some (OpImm ALU_ADD 11 0 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_1d650 : bv 32 := 0x2a91e0ef.
Lemma F_1d650 : fetch_word Ubsan.M.loaded_segments (0x1d650 : word) = Some W_1d650.
Proof. vm_refl. Qed.
Lemma D_1d650 : decode_any W_1d650 = Some (Jal 1 125608, 4%Z).
Proof. vm_refl. Qed.

Definition W_1d654 : bv 32 := 0x00747593.
Lemma F_1d654 : fetch_word Ubsan.M.loaded_segments (0x1d654 : word) = Some W_1d654.
Proof. vm_refl. Qed.
Lemma D_1d654 : decode_any W_1d654 = Some (OpImm ALU_AND 11 8 7, 4%Z).
Proof. vm_refl. Qed.

Definition W_1d658 : bv 32 := 0x0c059c63.
Lemma F_1d658 : fetch_word Ubsan.M.loaded_segments (0x1d658 : word) = Some W_1d658.
Proof. vm_refl. Qed.
Lemma D_1d658 : decode_any W_1d658 = Some (Branch BC_NE 11 0 216, 4%Z).
Proof. vm_refl. Qed.

Definition W_1d65c : bv 32 := 0x00050493.
Lemma F_1d65c : fetch_word Ubsan.M.loaded_segments (0x1d65c : word) = Some W_1d65c.
Proof. vm_refl. Qed.
Lemma D_1d65c : decode_any W_1d65c = Some (OpImm ALU_ADD 9 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_1d660 : bv 32 := 0x00c42503.
Lemma F_1d660 : fetch_word Ubsan.M.loaded_segments (0x1d660 : word) = Some W_1d660.
Proof. vm_refl. Qed.
Lemma D_1d660 : decode_any W_1d660 = Some (Load SZ4 true 10 8 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_1d664 : bv 32 := 0x0025159b.
Lemma F_1d664 : fetch_word Ubsan.M.loaded_segments (0x1d664 : word) = Some W_1d664.
Proof. vm_refl. Qed.
Lemma D_1d664 : decode_any W_1d664 = Some (ShiftImm32 ALU_SLL 11 10 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_1d668 : bv 32 := 0x00100513.
Lemma F_1d668 : fetch_word Ubsan.M.loaded_segments (0x1d668 : word) = Some W_1d668.
Proof. vm_refl. Qed.
Lemma D_1d668 : decode_any W_1d668 = Some (OpImm ALU_ADD 10 0 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_1d66c : bv 32 := 0x28d1e0ef.
Lemma F_1d66c : fetch_word Ubsan.M.loaded_segments (0x1d66c : word) = Some W_1d66c.
Proof. vm_refl. Qed.
Lemma D_1d66c : decode_any W_1d66c = Some (Jal 1 125580, 4%Z).
Proof. vm_refl. Qed.

Definition W_1d670 : bv 32 := 0x0c048063.
Lemma F_1d670 : fetch_word Ubsan.M.loaded_segments (0x1d670 : word) = Some W_1d670.
Proof. vm_refl. Qed.
Lemma D_1d670 : decode_any W_1d670 = Some (Branch BC_EQ 9 0 192, 4%Z).
Proof. vm_refl. Qed.

Definition W_1d674 : bv 32 := 0x0074f593.
Lemma F_1d674 : fetch_word Ubsan.M.loaded_segments (0x1d674 : word) = Some W_1d674.
Proof. vm_refl. Qed.
Lemma D_1d674 : decode_any W_1d674 = Some (OpImm ALU_AND 11 9 7, 4%Z).
Proof. vm_refl. Qed.

Definition W_1d678 : bv 32 := 0x0a059c63.
Lemma F_1d678 : fetch_word Ubsan.M.loaded_segments (0x1d678 : word) = Some W_1d678.
Proof. vm_refl. Qed.
Lemma D_1d678 : decode_any W_1d678 = Some (Branch BC_NE 11 0 184, 4%Z).
Proof. vm_refl. Qed.

Definition W_1d67c : bv 32 := 0x00a4b023.
Lemma F_1d67c : fetch_word Ubsan.M.loaded_segments (0x1d67c : word) = Some W_1d67c.
Proof. vm_refl. Qed.
Lemma D_1d67c : decode_any W_1d67c = Some (Store SZ8 9 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_1d680 : bv 32 := 0x01042603.
Lemma F_1d680 : fetch_word Ubsan.M.loaded_segments (0x1d680 : word) = Some W_1d680.
Proof. vm_refl. Qed.
Lemma D_1d680 : decode_any W_1d680 = Some (Load SZ4 true 12 8 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_1d684 : bv 32 := 0x00043583.
Lemma F_1d684 : fetch_word Ubsan.M.loaded_segments (0x1d684 : word) = Some W_1d684.
Proof. vm_refl. Qed.
Lemma D_1d684 : decode_any W_1d684 = Some (Load SZ8 true 11 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_1d688 : bv 32 := 0x00261613.
Lemma F_1d688 : fetch_word Ubsan.M.loaded_segments (0x1d688 : word) = Some W_1d688.
Proof. vm_refl. Qed.
Lemma D_1d688 : decode_any W_1d688 = Some (ShiftImm ALU_SLL 12 12 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_1d68c : bv 32 := 0x5f1250ef.
Lemma F_1d68c : fetch_word Ubsan.M.loaded_segments (0x1d68c : word) = Some W_1d68c.
Proof. vm_refl. Qed.
Lemma D_1d68c : decode_any W_1d68c = Some (Jal 1 155120, 4%Z).
Proof. vm_refl. Qed.

Definition W_1d690 : bv 32 := 0x01042503.
Lemma F_1d690 : fetch_word Ubsan.M.loaded_segments (0x1d690 : word) = Some W_1d690.
Proof. vm_refl. Qed.
Lemma D_1d690 : decode_any W_1d690 = Some (Load SZ4 true 10 8 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_1d694 : bv 32 := 0x00a4a823.
Lemma F_1d694 : fetch_word Ubsan.M.loaded_segments (0x1d694 : word) = Some W_1d694.
Proof. vm_refl. Qed.
Lemma D_1d694 : decode_any W_1d694 = Some (Store SZ4 9 10 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_1d698 : bv 32 := 0x00843503.
Lemma F_1d698 : fetch_word Ubsan.M.loaded_segments (0x1d698 : word) = Some W_1d698.
Proof. vm_refl. Qed.
Lemma D_1d698 : decode_any W_1d698 = Some (Load SZ8 true 10 8 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_1d69c : bv 32 := 0x00a4b423.
Lemma F_1d69c : fetch_word Ubsan.M.loaded_segments (0x1d69c : word) = Some W_1d69c.
Proof. vm_refl. Qed.
Lemma D_1d69c : decode_any W_1d69c = Some (Store SZ8 9 10 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_1d6a0 : bv 32 := 0x0780006f.
Lemma F_1d6a0 : fetch_word Ubsan.M.loaded_segments (0x1d6a0 : word) = Some W_1d6a0.
Proof. vm_refl. Qed.
Lemma D_1d6a0 : decode_any W_1d6a0 = Some (Jal 0 120, 4%Z).
Proof. vm_refl. Qed.

Definition W_1d6a4 : bv 32 := 0x00027517.
Lemma F_1d6a4 : fetch_word Ubsan.M.loaded_segments (0x1d6a4 : word) = Some W_1d6a4.
Proof. vm_refl. Qed.
Lemma D_1d6a4 : decode_any W_1d6a4 = Some (Auipc 10 39, 4%Z).
Proof. vm_refl. Qed.

Definition W_1d6a8 : bv 32 := 0x7f453503.
Lemma F_1d6a8 : fetch_word Ubsan.M.loaded_segments (0x1d6a8 : word) = Some W_1d6a8.
Proof. vm_refl. Qed.
Lemma D_1d6a8 : decode_any W_1d6a8 = Some (Load SZ8 true 10 10 2036, 4%Z).
Proof. vm_refl. Qed.

Definition W_1d6ac : bv 32 := 0x00052503.
Lemma F_1d6ac : fetch_word Ubsan.M.loaded_segments (0x1d6ac : word) = Some W_1d6ac.
Proof. vm_refl. Qed.
Lemma D_1d6ac : decode_any W_1d6ac = Some (Load SZ4 true 10 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_1d6b0 : bv 32 := 0x00500593.
Lemma F_1d6b0 : fetch_word Ubsan.M.loaded_segments (0x1d6b0 : word) = Some W_1d6b0.
Proof. vm_refl. Qed.
Lemma D_1d6b0 : decode_any W_1d6b0 = Some (OpImm ALU_ADD 11 0 5, 4%Z).
Proof. vm_refl. Qed.

Definition W_1d6b4 : bv 32 := 0x06a5c063.
Lemma F_1d6b4 : fetch_word Ubsan.M.loaded_segments (0x1d6b4 : word) = Some W_1d6b4.
Proof. vm_refl. Qed.
Lemma D_1d6b4 : decode_any W_1d6b4 = Some (Branch BC_LT 11 10 96, 4%Z).
Proof. vm_refl. Qed.

Definition W_1d6b8 : bv 32 := 0xffff3517.
Lemma F_1d6b8 : fetch_word Ubsan.M.loaded_segments (0x1d6b8 : word) = Some W_1d6b8.
Proof. vm_refl. Qed.
Lemma D_1d6b8 : decode_any W_1d6b8 = Some (Auipc 10 1048563, 4%Z).
Proof. vm_refl. Qed.

Definition W_1d6bc : bv 32 := 0xffff3597.
Lemma F_1d6bc : fetch_word Ubsan.M.loaded_segments (0x1d6bc : word) = Some W_1d6bc.
Proof. vm_refl. Qed.
Lemma D_1d6bc : decode_any W_1d6bc = Some (Auipc 11 1048563, 4%Z).
Proof. vm_refl. Qed.

Definition W_1d6c0 : bv 32 := 0xec350513.
Lemma F_1d6c0 : fetch_word Ubsan.M.loaded_segments (0x1d6c0 : word) = Some W_1d6c0.
Proof. vm_refl. Qed.
Lemma D_1d6c0 : decode_any W_1d6c0 = Some (OpImm ALU_ADD 10 10 3779, 4%Z).
Proof. vm_refl. Qed.

Definition W_1d6c4 : bv 32 := 0x3c758593.
Lemma F_1d6c4 : fetch_word Ubsan.M.loaded_segments (0x1d6c4 : word) = Some W_1d6c4.
Proof. vm_refl. Qed.
Lemma D_1d6c4 : decode_any W_1d6c4 = Some (OpImm ALU_ADD 11 11 967, 4%Z).
Proof. vm_refl. Qed.

Definition W_1d6c8 : bv 32 := 0x00000613.
Lemma F_1d6c8 : fetch_word Ubsan.M.loaded_segments (0x1d6c8 : word) = Some W_1d6c8.
Proof. vm_refl. Qed.
Lemma D_1d6c8 : decode_any W_1d6c8 = Some (OpImm ALU_ADD 12 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_1d6cc : bv 32 := 0x01813083.
Lemma F_1d6cc : fetch_word Ubsan.M.loaded_segments (0x1d6cc : word) = Some W_1d6cc.
Proof. vm_refl. Qed.
Lemma D_1d6cc : decode_any W_1d6cc = Some (Load SZ8 true 1 2 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_1d6d0 : bv 32 := 0x01013403.
Lemma F_1d6d0 : fetch_word Ubsan.M.loaded_segments (0x1d6d0 : word) = Some W_1d6d0.
Proof. vm_refl. Qed.
Lemma D_1d6d0 : decode_any W_1d6d0 = Some (Load SZ8 true 8 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_1d6d4 : bv 32 := 0x00813483.
Lemma F_1d6d4 : fetch_word Ubsan.M.loaded_segments (0x1d6d4 : word) = Some W_1d6d4.
Proof. vm_refl. Qed.
Lemma D_1d6d4 : decode_any W_1d6d4 = Some (Load SZ8 true 9 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_1d6d8 : bv 32 := 0x02010113.
Lemma F_1d6d8 : fetch_word Ubsan.M.loaded_segments (0x1d6d8 : word) = Some W_1d6d8.
Proof. vm_refl. Qed.
Lemma D_1d6d8 : decode_any W_1d6d8 = Some (OpImm ALU_ADD 2 2 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_1d6dc : bv 32 := 0xfe8fa06f.
Lemma F_1d6dc : fetch_word Ubsan.M.loaded_segments (0x1d6dc : word) = Some W_1d6dc.
Proof. vm_refl. Qed.
Lemma D_1d6dc : decode_any W_1d6dc = Some (Jal 0 2074600, 4%Z).
Proof. vm_refl. Qed.

Definition W_1d6e0 : bv 32 := 0x00027517.
Lemma F_1d6e0 : fetch_word Ubsan.M.loaded_segments (0x1d6e0 : word) = Some W_1d6e0.
Proof. vm_refl. Qed.
Lemma D_1d6e0 : decode_any W_1d6e0 = Some (Auipc 10 39, 4%Z).
Proof. vm_refl. Qed.

Definition W_1d6e4 : bv 32 := 0x7b853503.
Lemma F_1d6e4 : fetch_word Ubsan.M.loaded_segments (0x1d6e4 : word) = Some W_1d6e4.
Proof. vm_refl. Qed.
Lemma D_1d6e4 : decode_any W_1d6e4 = Some (Load SZ8 true 10 10 1976, 4%Z).
Proof. vm_refl. Qed.

Definition W_1d6e8 : bv 32 := 0x00052503.
Lemma F_1d6e8 : fetch_word Ubsan.M.loaded_segments (0x1d6e8 : word) = Some W_1d6e8.
Proof. vm_refl. Qed.
Lemma D_1d6e8 : decode_any W_1d6e8 = Some (Load SZ4 true 10 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_1d6ec : bv 32 := 0x00500593.
Lemma F_1d6ec : fetch_word Ubsan.M.loaded_segments (0x1d6ec : word) = Some W_1d6ec.
Proof. vm_refl. Qed.
Lemma D_1d6ec : decode_any W_1d6ec = Some (OpImm ALU_ADD 11 0 5, 4%Z).
Proof. vm_refl. Qed.

Definition W_1d6f0 : bv 32 := 0x02a5c263.
Lemma F_1d6f0 : fetch_word Ubsan.M.loaded_segments (0x1d6f0 : word) = Some W_1d6f0.
Proof. vm_refl. Qed.
Lemma D_1d6f0 : decode_any W_1d6f0 = Some (Branch BC_LT 11 10 36, 4%Z).
Proof. vm_refl. Qed.

Definition W_1d6f4 : bv 32 := 0xffff5517.
Lemma F_1d6f4 : fetch_word Ubsan.M.loaded_segments (0x1d6f4 : word) = Some W_1d6f4.
Proof. vm_refl. Qed.
Lemma D_1d6f4 : decode_any W_1d6f4 = Some (Auipc 10 1048565, 4%Z).
Proof. vm_refl. Qed.

Definition W_1d6f8 : bv 32 := 0xffff3597.
Lemma F_1d6f8 : fetch_word Ubsan.M.loaded_segments (0x1d6f8 : word) = Some W_1d6f8.
Proof. vm_refl. Qed.
Lemma D_1d6f8 : decode_any W_1d6f8 = Some (Auipc 11 1048563, 4%Z).
Proof. vm_refl. Qed.

Definition W_1d6fc : bv 32 := 0x80f50513.
Lemma F_1d6fc : fetch_word Ubsan.M.loaded_segments (0x1d6fc : word) = Some W_1d6fc.
Proof. vm_refl. Qed.
Lemma D_1d6fc : decode_any W_1d6fc = Some (OpImm ALU_ADD 10 10 2063, 4%Z).
Proof. vm_refl. Qed.

Definition W_1d700 : bv 32 := 0x38b58593.
Lemma F_1d700 : fetch_word Ubsan.M.loaded_segments (0x1d700 : word) = Some W_1d700.
Proof. vm_refl. Qed.
Lemma D_1d700 : decode_any W_1d700 = Some (OpImm ALU_ADD 11 11 907, 4%Z).
Proof. vm_refl. Qed.

Definition W_1d704 : bv 32 := 0x00000613.
Lemma F_1d704 : fetch_word Ubsan.M.loaded_segments (0x1d704 : word) = Some W_1d704.
Proof. vm_refl. Qed.
Lemma D_1d704 : decode_any W_1d704 = Some (OpImm ALU_ADD 12 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_1d708 : bv 32 := 0xfbcfa0ef.
Lemma F_1d708 : fetch_word Ubsan.M.loaded_segments (0x1d708 : word) = Some W_1d708.
Proof. vm_refl. Qed.
Lemma D_1d708 : decode_any W_1d708 = Some (Jal 1 2074556, 4%Z).
Proof. vm_refl. Qed.

Definition W_1d70c : bv 32 := 0x00050493.
Lemma F_1d70c : fetch_word Ubsan.M.loaded_segments (0x1d70c : word) = Some W_1d70c.
Proof. vm_refl. Qed.
Lemma D_1d70c : decode_any W_1d70c = Some (OpImm ALU_ADD 9 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_1d710 : bv 32 := 0x0080006f.
Lemma F_1d710 : fetch_word Ubsan.M.loaded_segments (0x1d710 : word) = Some W_1d710.
Proof. vm_refl. Qed.
Lemma D_1d710 : decode_any W_1d710 = Some (Jal 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_1d714 : bv 32 := 0x00000493.
Lemma F_1d714 : fetch_word Ubsan.M.loaded_segments (0x1d714 : word) = Some W_1d714.
Proof. vm_refl. Qed.
Lemma D_1d714 : decode_any W_1d714 = Some (OpImm ALU_ADD 9 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_1d718 : bv 32 := 0x00048513.
Lemma F_1d718 : fetch_word Ubsan.M.loaded_segments (0x1d718 : word) = Some W_1d718.
Proof. vm_refl. Qed.
Lemma D_1d718 : decode_any W_1d718 = Some (OpImm ALU_ADD 10 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_1d71c : bv 32 := 0x01813083.
Lemma F_1d71c : fetch_word Ubsan.M.loaded_segments (0x1d71c : word) = Some W_1d71c.
Proof. vm_refl. Qed.
Lemma D_1d71c : decode_any W_1d71c = Some (Load SZ8 true 1 2 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_1d720 : bv 32 := 0x01013403.
Lemma F_1d720 : fetch_word Ubsan.M.loaded_segments (0x1d720 : word) = Some W_1d720.
Proof. vm_refl. Qed.
Lemma D_1d720 : decode_any W_1d720 = Some (Load SZ8 true 8 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_1d724 : bv 32 := 0x00813483.
Lemma F_1d724 : fetch_word Ubsan.M.loaded_segments (0x1d724 : word) = Some W_1d724.
Proof. vm_refl. Qed.
Lemma D_1d724 : decode_any W_1d724 = Some (Load SZ8 true 9 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_1d728 : bv 32 := 0x02010113.
Lemma F_1d728 : fetch_word Ubsan.M.loaded_segments (0x1d728 : word) = Some W_1d728.
Proof. vm_refl. Qed.
Lemma D_1d728 : decode_any W_1d728 = Some (OpImm ALU_ADD 2 2 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_1d72c : bv 32 := 0x00008067.
Lemma F_1d72c : fetch_word Ubsan.M.loaded_segments (0x1d72c : word) = Some W_1d72c.
Proof. vm_refl. Qed.
Lemma D_1d72c : decode_any W_1d72c = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_1d730 : bv 32 := 0xc0001073.
Lemma F_1d730 : fetch_word Ubsan.M.loaded_segments (0x1d730 : word) = Some W_1d730.
Proof. vm_refl. Qed.
Lemma D_1d730 : decode_any W_1d730 = Some (Csr CSR_RW 0 0 3072, 4%Z).
Proof. vm_refl. Qed.
