(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
(* [comment removed for export] *)

From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.H Require GcFlushS23.   (* [comment removed for export] *)
From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.leptonica.pix_orient_fuzzer.images Require Import Plain.
Open Scope bv_scope.

(* [comment removed for export] *)
Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

(* [comment removed for export] *)
Definition W_6d648 : bv 32 := 0xfb010113.
Lemma F_6d648 : fetch_word Plain.M.loaded_segments (0x6d6a0 : word) = Some W_6d648.
Proof. vm_refl. Qed.
Lemma D_6d648 : decode_any W_6d648 = Some (OpImm ALU_ADD 2 2 4016, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6d64c : bv 32 := 0x04113423.
Lemma F_6d64c : fetch_word Plain.M.loaded_segments (0x6d6a4 : word) = Some W_6d64c.
Proof. vm_refl. Qed.
Lemma D_6d64c : decode_any W_6d64c = Some (Store SZ8 2 1 72, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6d650 : bv 32 := 0x04813023.
Lemma F_6d650 : fetch_word Plain.M.loaded_segments (0x6d6a8 : word) = Some W_6d650.
Proof. vm_refl. Qed.
Lemma D_6d650 : decode_any W_6d650 = Some (Store SZ8 2 8 64, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6d654 : bv 32 := 0x02913c23.
Lemma F_6d654 : fetch_word Plain.M.loaded_segments (0x6d6ac : word) = Some W_6d654.
Proof. vm_refl. Qed.
Lemma D_6d654 : decode_any W_6d654 = Some (Store SZ8 2 9 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6d658 : bv 32 := 0x03213823.
Lemma F_6d658 : fetch_word Plain.M.loaded_segments (0x6d6b0 : word) = Some W_6d658.
Proof. vm_refl. Qed.
Lemma D_6d658 : decode_any W_6d658 = Some (Store SZ8 2 18 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6d65c : bv 32 := 0x03313423.
Lemma F_6d65c : fetch_word Plain.M.loaded_segments (0x6d6b4 : word) = Some W_6d65c.
Proof. vm_refl. Qed.
Lemma D_6d65c : decode_any W_6d65c = Some (Store SZ8 2 19 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6d660 : bv 32 := 0x03413023.
Lemma F_6d660 : fetch_word Plain.M.loaded_segments (0x6d6b8 : word) = Some W_6d660.
Proof. vm_refl. Qed.
Lemma D_6d660 : decode_any W_6d660 = Some (Store SZ8 2 20 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6d664 : bv 32 := 0x01513c23.
Lemma F_6d664 : fetch_word Plain.M.loaded_segments (0x6d6bc : word) = Some W_6d664.
Proof. vm_refl. Qed.
Lemma D_6d664 : decode_any W_6d664 = Some (Store SZ8 2 21 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6d668 : bv 32 := 0x01613823.
Lemma F_6d668 : fetch_word Plain.M.loaded_segments (0x6d6c0 : word) = Some W_6d668.
Proof. vm_refl. Qed.
Lemma D_6d668 : decode_any W_6d668 = Some (Store SZ8 2 22 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6d66c : bv 32 := 0x01713423.
Lemma F_6d66c : fetch_word Plain.M.loaded_segments (0x6d6c4 : word) = Some W_6d66c.
Proof. vm_refl. Qed.
Lemma D_6d66c : decode_any W_6d66c = Some (Store SZ8 2 23 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6d670 : bv 32 := 0x02058c63.
Lemma F_6d670 : fetch_word Plain.M.loaded_segments (0x6d6c8 : word) = Some W_6d670.
Proof. vm_refl. Qed.
Lemma D_6d670 : decode_any W_6d670 = Some (Branch BC_EQ 11 0 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6d674 : bv 32 := 0x04050e63.
Lemma F_6d674 : fetch_word Plain.M.loaded_segments (0x6d6cc : word) = Some W_6d674.
Proof. vm_refl. Qed.
Lemma D_6d674 : decode_any W_6d674 = Some (Branch BC_EQ 10 0 92, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6d678 : bv 32 := 0x02a58463.
Lemma F_6d678 : fetch_word Plain.M.loaded_segments (0x6d6d0 : word) = Some W_6d678.
Proof. vm_refl. Qed.
Lemma D_6d678 : decode_any W_6d678 = Some (Branch BC_EQ 11 10 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6d67c : bv 32 := 0x00052603.
Lemma F_6d67c : fetch_word Plain.M.loaded_segments (0x6d6d4 : word) = Some W_6d67c.
Proof. vm_refl. Qed.
Lemma D_6d67c : decode_any W_6d67c = Some (Load SZ4 true 12 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6d680 : bv 32 := 0x0005ab83.
Lemma F_6d680 : fetch_word Plain.M.loaded_segments (0x6d6d8 : word) = Some W_6d680.
Proof. vm_refl. Qed.
Lemma D_6d680 : decode_any W_6d680 = Some (Load SZ4 true 23 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6d684 : bv 32 := 0x0045ab03.
Lemma F_6d684 : fetch_word Plain.M.loaded_segments (0x6d6dc : word) = Some W_6d684.
Proof. vm_refl. Qed.
Lemma D_6d684 : decode_any W_6d684 = Some (Load SZ4 true 22 11 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6d688 : bv 32 := 0x06cb9863.
Lemma F_6d688 : fetch_word Plain.M.loaded_segments (0x6d6e0 : word) = Some W_6d688.
Proof. vm_refl. Qed.
Lemma D_6d688 : decode_any W_6d688 = Some (Branch BC_NE 23 12 112, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6d68c : bv 32 := 0x00452603.
Lemma F_6d68c : fetch_word Plain.M.loaded_segments (0x6d6e4 : word) = Some W_6d68c.
Proof. vm_refl. Qed.
Lemma D_6d68c : decode_any W_6d68c = Some (Load SZ4 true 12 10 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6d690 : bv 32 := 0x06cb1463.
Lemma F_6d690 : fetch_word Plain.M.loaded_segments (0x6d6e8 : word) = Some W_6d690.
Proof. vm_refl. Qed.
Lemma D_6d690 : decode_any W_6d690 = Some (Branch BC_NE 22 12 104, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6d694 : bv 32 := 0x0085a603.
Lemma F_6d694 : fetch_word Plain.M.loaded_segments (0x6d6ec : word) = Some W_6d694.
Proof. vm_refl. Qed.
Lemma D_6d694 : decode_any W_6d694 = Some (Load SZ4 true 12 11 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6d698 : bv 32 := 0x00852683.
Lemma F_6d698 : fetch_word Plain.M.loaded_segments (0x6d6f0 : word) = Some W_6d698.
Proof. vm_refl. Qed.
Lemma D_6d698 : decode_any W_6d698 = Some (Load SZ4 true 13 10 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6d69c : bv 32 := 0x04d61e63.
Lemma F_6d69c : fetch_word Plain.M.loaded_segments (0x6d6f4 : word) = Some W_6d69c.
Proof. vm_refl. Qed.
Lemma D_6d69c : decode_any W_6d69c = Some (Branch BC_NE 12 13 92, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6d6a0 : bv 32 := 0x00000513.
Lemma F_6d6a0 : fetch_word Plain.M.loaded_segments (0x6d6f8 : word) = Some W_6d6a0.
Proof. vm_refl. Qed.
Lemma D_6d6a0 : decode_any W_6d6a0 = Some (OpImm ALU_ADD 10 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6d6a4 : bv 32 := 0x1e40006f.
Lemma F_6d6a4 : fetch_word Plain.M.loaded_segments (0x6d6fc : word) = Some W_6d6a4.
Proof. vm_refl. Qed.
Lemma D_6d6a4 : decode_any W_6d6a4 = Some (Jal 0 484, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6d888 : bv 32 := 0x04813083.
Lemma F_6d888 : fetch_word Plain.M.loaded_segments (0x6d8e0 : word) = Some W_6d888.
Proof. vm_refl. Qed.
Lemma D_6d888 : decode_any W_6d888 = Some (Load SZ8 true 1 2 72, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6d88c : bv 32 := 0x04013403.
Lemma F_6d88c : fetch_word Plain.M.loaded_segments (0x6d8e4 : word) = Some W_6d88c.
Proof. vm_refl. Qed.
Lemma D_6d88c : decode_any W_6d88c = Some (Load SZ8 true 8 2 64, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6d890 : bv 32 := 0x03813483.
Lemma F_6d890 : fetch_word Plain.M.loaded_segments (0x6d8e8 : word) = Some W_6d890.
Proof. vm_refl. Qed.
Lemma D_6d890 : decode_any W_6d890 = Some (Load SZ8 true 9 2 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6d894 : bv 32 := 0x03013903.
Lemma F_6d894 : fetch_word Plain.M.loaded_segments (0x6d8ec : word) = Some W_6d894.
Proof. vm_refl. Qed.
Lemma D_6d894 : decode_any W_6d894 = Some (Load SZ8 true 18 2 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6d898 : bv 32 := 0x02813983.
Lemma F_6d898 : fetch_word Plain.M.loaded_segments (0x6d8f0 : word) = Some W_6d898.
Proof. vm_refl. Qed.
Lemma D_6d898 : decode_any W_6d898 = Some (Load SZ8 true 19 2 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6d89c : bv 32 := 0x02013a03.
Lemma F_6d89c : fetch_word Plain.M.loaded_segments (0x6d8f4 : word) = Some W_6d89c.
Proof. vm_refl. Qed.
Lemma D_6d89c : decode_any W_6d89c = Some (Load SZ8 true 20 2 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6d8a0 : bv 32 := 0x01813a83.
Lemma F_6d8a0 : fetch_word Plain.M.loaded_segments (0x6d8f8 : word) = Some W_6d8a0.
Proof. vm_refl. Qed.
Lemma D_6d8a0 : decode_any W_6d8a0 = Some (Load SZ8 true 21 2 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6d8a4 : bv 32 := 0x01013b03.
Lemma F_6d8a4 : fetch_word Plain.M.loaded_segments (0x6d8fc : word) = Some W_6d8a4.
Proof. vm_refl. Qed.
Lemma D_6d8a4 : decode_any W_6d8a4 = Some (Load SZ8 true 22 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6d8a8 : bv 32 := 0x00813b83.
Lemma F_6d8a8 : fetch_word Plain.M.loaded_segments (0x6d900 : word) = Some W_6d8a8.
Proof. vm_refl. Qed.
Lemma D_6d8a8 : decode_any W_6d8a8 = Some (Load SZ8 true 23 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6d8ac : bv 32 := 0x05010113.
Lemma F_6d8ac : fetch_word Plain.M.loaded_segments (0x6d904 : word) = Some W_6d8ac.
Proof. vm_refl. Qed.
Lemma D_6d8ac : decode_any W_6d8ac = Some (OpImm ALU_ADD 2 2 80, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6d8b0 : bv 32 := 0x00008067.
Lemma F_6d8b0 : fetch_word Plain.M.loaded_segments (0x6d908 : word) = Some W_6d8b0.
Proof. vm_refl. Qed.
Lemma D_6d8b0 : decode_any W_6d8b0 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.
(* [comment removed for export] *)
Definition W_6d928 : bv 32 := 0x00050663.
Lemma F_6d928 : fetch_word Plain.M.loaded_segments (0x6d980 : word) = Some W_6d928.
Proof. vm_refl. Qed.
Lemma D_6d928 : decode_any W_6d928 = Some (Branch BC_EQ 10 0 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6d92c : bv 32 := 0x00852503.
Lemma F_6d92c : fetch_word Plain.M.loaded_segments (0x6d984 : word) = Some W_6d92c.
Proof. vm_refl. Qed.
Lemma D_6d92c : decode_any W_6d92c = Some (Load SZ4 true 10 10 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6d930 : bv 32 := 0x00008067.
Lemma F_6d930 : fetch_word Plain.M.loaded_segments (0x6d988 : word) = Some W_6d930.
Proof. vm_refl. Qed.
Lemma D_6d930 : decode_any W_6d930 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8f67c : bv 32 := 0xfd010113.
Lemma F_8f67c : fetch_word Plain.M.loaded_segments (0x8f6d4 : word) = Some W_8f67c.
Proof. vm_refl. Qed.
Lemma D_8f67c : decode_any W_8f67c = Some (OpImm ALU_ADD 2 2 4048, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8f680 : bv 32 := 0x02113423.
Lemma F_8f680 : fetch_word Plain.M.loaded_segments (0x8f6d8 : word) = Some W_8f680.
Proof. vm_refl. Qed.
Lemma D_8f680 : decode_any W_8f680 = Some (Store SZ8 2 1 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8f684 : bv 32 := 0x02813023.
Lemma F_8f684 : fetch_word Plain.M.loaded_segments (0x8f6dc : word) = Some W_8f684.
Proof. vm_refl. Qed.
Lemma D_8f684 : decode_any W_8f684 = Some (Store SZ8 2 8 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8f688 : bv 32 := 0x00913c23.
Lemma F_8f688 : fetch_word Plain.M.loaded_segments (0x8f6e0 : word) = Some W_8f688.
Proof. vm_refl. Qed.
Lemma D_8f688 : decode_any W_8f688 = Some (Store SZ8 2 9 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8f68c : bv 32 := 0x01213823.
Lemma F_8f68c : fetch_word Plain.M.loaded_segments (0x8f6e4 : word) = Some W_8f68c.
Proof. vm_refl. Qed.
Lemma D_8f68c : decode_any W_8f68c = Some (Store SZ8 2 18 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8f690 : bv 32 := 0x01313423.
Lemma F_8f690 : fetch_word Plain.M.loaded_segments (0x8f6e8 : word) = Some W_8f690.
Proof. vm_refl. Qed.
Lemma D_8f690 : decode_any W_8f690 = Some (Store SZ8 2 19 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8f694 : bv 32 := 0x00050413.
Lemma F_8f694 : fetch_word Plain.M.loaded_segments (0x8f6ec : word) = Some W_8f694.
Proof. vm_refl. Qed.
Lemma D_8f694 : decode_any W_8f694 = Some (OpImm ALU_ADD 8 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8f698 : bv 32 := 0x0006b023.
Lemma F_8f698 : fetch_word Plain.M.loaded_segments (0x8f6f0 : word) = Some W_8f698.
Proof. vm_refl. Qed.
Lemma D_8f698 : decode_any W_8f698 = Some (Store SZ8 13 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8f69c : bv 32 := 0x08058e63.
Lemma F_8f69c : fetch_word Plain.M.loaded_segments (0x8f6f4 : word) = Some W_8f69c.
Proof. vm_refl. Qed.
Lemma D_8f69c : decode_any W_8f69c = Some (Branch BC_EQ 11 0 156, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8f6a0 : bv 32 := 0x0c060063.
Lemma F_8f6a0 : fetch_word Plain.M.loaded_segments (0x8f6f8 : word) = Some W_8f6a0.
Proof. vm_refl. Qed.
Lemma D_8f6a0 : decode_any W_8f6a0 = Some (Branch BC_EQ 12 0 192, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8f6a4 : bv 32 := 0x00060913.
Lemma F_8f6a4 : fetch_word Plain.M.loaded_segments (0x8f6fc : word) = Some W_8f6a4.
Proof. vm_refl. Qed.
Lemma D_8f6a4 : decode_any W_8f6a4 = Some (OpImm ALU_ADD 18 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8f6a8 : bv 32 := 0x00068993.
Lemma F_8f6a8 : fetch_word Plain.M.loaded_segments (0x8f700 : word) = Some W_8f6a8.
Proof. vm_refl. Qed.
Lemma D_8f6a8 : decode_any W_8f6a8 = Some (OpImm ALU_ADD 19 13 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8f6ac : bv 32 := 0x00058493.
Lemma F_8f6ac : fetch_word Plain.M.loaded_segments (0x8f704 : word) = Some W_8f6ac.
Proof. vm_refl. Qed.
Lemma D_8f6ac : decode_any W_8f6ac = Some (OpImm ALU_ADD 9 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8f6b0 : bv 32 := 0x00058513.
Lemma F_8f6b0 : fetch_word Plain.M.loaded_segments (0x8f708 : word) = Some W_8f6b0.
Proof. vm_refl. Qed.
Lemma D_8f6b0 : decode_any W_8f6b0 = Some (OpImm ALU_ADD 10 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8f6b4 : bv 32 := 0xa74de0ef.
Lemma F_8f6b4 : fetch_word Plain.M.loaded_segments (0x8f70c : word) = Some W_8f6b4.
Proof. vm_refl. Qed.
Lemma D_8f6b4 : decode_any W_8f6b4 = Some (Jal 1 1958516, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8f6b8 : bv 32 := 0x00100593.
Lemma F_8f6b8 : fetch_word Plain.M.loaded_segments (0x8f710 : word) = Some W_8f6b8.
Proof. vm_refl. Qed.
Lemma D_8f6b8 : decode_any W_8f6b8 = Some (OpImm ALU_ADD 11 0 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8f6bc : bv 32 := 0x0cb51663.
Lemma F_8f6bc : fetch_word Plain.M.loaded_segments (0x8f714 : word) = Some W_8f6bc.
Proof. vm_refl. Qed.
Lemma D_8f6bc : decode_any W_8f6bc = Some (Branch BC_NE 10 11 204, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8f6c0 : bv 32 := 0x00410593.
Lemma F_8f6c0 : fetch_word Plain.M.loaded_segments (0x8f718 : word) = Some W_8f6c0.
Proof. vm_refl. Qed.
Lemma D_8f6c0 : decode_any W_8f6c0 = Some (OpImm ALU_ADD 11 2 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8f6c4 : bv 32 := 0x00010613.
Lemma F_8f6c4 : fetch_word Plain.M.loaded_segments (0x8f71c : word) = Some W_8f6c4.
Proof. vm_refl. Qed.
Lemma D_8f6c4 : decode_any W_8f6c4 = Some (OpImm ALU_ADD 12 2 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8f6c8 : bv 32 := 0x00090513.
Lemma F_8f6c8 : fetch_word Plain.M.loaded_segments (0x8f720 : word) = Some W_8f6c8.
Proof. vm_refl. Qed.
Lemma D_8f6c8 : decode_any W_8f6c8 = Some (OpImm ALU_ADD 10 18 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8f6cc : bv 32 := 0x00000693.
Lemma F_8f6cc : fetch_word Plain.M.loaded_segments (0x8f724 : word) = Some W_8f6cc.
Proof. vm_refl. Qed.
Lemma D_8f6cc : decode_any W_8f6cc = Some (OpImm ALU_ADD 13 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8f6d0 : bv 32 := 0x00000713.
Lemma F_8f6d0 : fetch_word Plain.M.loaded_segments (0x8f728 : word) = Some W_8f6d0.
Proof. vm_refl. Qed.
Lemma D_8f6d0 : decode_any W_8f6d0 = Some (OpImm ALU_ADD 14 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8f6d4 : bv 32 := 0x71d020ef.
Lemma F_8f6d4 : fetch_word Plain.M.loaded_segments (0x8f72c : word) = Some W_8f6d4.
Proof. vm_refl. Qed.
Lemma D_8f6d4 : decode_any W_8f6d4 = Some (Jal 1 12060, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8f6d8 : bv 32 := 0x00412503.
Lemma F_8f6d8 : fetch_word Plain.M.loaded_segments (0x8f730 : word) = Some W_8f6d8.
Proof. vm_refl. Qed.
Lemma D_8f6d8 : decode_any W_8f6d8 = Some (Load SZ4 true 10 2 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8f6dc : bv 32 := 0x0e050863.
Lemma F_8f6dc : fetch_word Plain.M.loaded_segments (0x8f734 : word) = Some W_8f6dc.
Proof. vm_refl. Qed.
Lemma D_8f6dc : decode_any W_8f6dc = Some (Branch BC_EQ 10 0 240, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8f6e0 : bv 32 := 0x00012503.
Lemma F_8f6e0 : fetch_word Plain.M.loaded_segments (0x8f738 : word) = Some W_8f6e0.
Proof. vm_refl. Qed.
Lemma D_8f6e0 : decode_any W_8f6e0 = Some (Load SZ4 true 10 2 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8f6e4 : bv 32 := 0x0e050463.
Lemma F_8f6e4 : fetch_word Plain.M.loaded_segments (0x8f73c : word) = Some W_8f6e4.
Proof. vm_refl. Qed.
Lemma D_8f6e4 : decode_any W_8f6e4 = Some (Branch BC_EQ 10 0 232, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8f6e8 : bv 32 := 0x10040c63.
Lemma F_8f6e8 : fetch_word Plain.M.loaded_segments (0x8f740 : word) = Some W_8f6e8.
Proof. vm_refl. Qed.
Lemma D_8f6e8 : decode_any W_8f6e8 = Some (Branch BC_EQ 8 0 280, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8f6ec : bv 32 := 0x00040513.
Lemma F_8f6ec : fetch_word Plain.M.loaded_segments (0x8f744 : word) = Some W_8f6ec.
Proof. vm_refl. Qed.
Lemma D_8f6ec : decode_any W_8f6ec = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8f6f0 : bv 32 := 0x00048593.
Lemma F_8f6f0 : fetch_word Plain.M.loaded_segments (0x8f748 : word) = Some W_8f6f0.
Proof. vm_refl. Qed.
Lemma D_8f6f0 : decode_any W_8f6f0 = Some (OpImm ALU_ADD 11 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8f6f4 : bv 32 := 0xf55dd0ef.
Lemma F_8f6f4 : fetch_word Plain.M.loaded_segments (0x8f74c : word) = Some W_8f6f4.
Proof. vm_refl. Qed.
Lemma D_8f6f4 : decode_any W_8f6f4 = Some (Jal 1 1957716, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8f6f8 : bv 32 := 0x10941c63.
Lemma F_8f6f8 : fetch_word Plain.M.loaded_segments (0x8f750 : word) = Some W_8f6f8.
Proof. vm_refl. Qed.
Lemma D_8f6f8 : decode_any W_8f6f8 = Some (Branch BC_NE 8 9 280, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8f738 : bv 32 := 0x00083517.
Lemma F_8f738 : fetch_word Plain.M.loaded_segments (0x8f790 : word) = Some W_8f738.
Proof. vm_refl. Qed.
Lemma D_8f738 : decode_any W_8f738 = Some (Auipc 10 131, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8f73c : bv 32 := 0xe3853503.
Lemma F_8f73c : fetch_word Plain.M.loaded_segments (0x8f794 : word) = Some W_8f73c.
Proof. vm_refl. Qed.
Lemma D_8f73c : decode_any W_8f73c = Some (Load SZ8 true 10 10 3640, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8f740 : bv 32 := 0x00052503.
Lemma F_8f740 : fetch_word Plain.M.loaded_segments (0x8f798 : word) = Some W_8f740.
Proof. vm_refl. Qed.
Lemma D_8f740 : decode_any W_8f740 = Some (Load SZ4 true 10 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8f744 : bv 32 := 0x00500593.
Lemma F_8f744 : fetch_word Plain.M.loaded_segments (0x8f79c : word) = Some W_8f744.
Proof. vm_refl. Qed.
Lemma D_8f744 : decode_any W_8f744 = Some (OpImm ALU_ADD 11 0 5, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8f748 : bv 32 := 0x0ca5ca63.
Lemma F_8f748 : fetch_word Plain.M.loaded_segments (0x8f7a0 : word) = Some W_8f748.
Proof. vm_refl. Qed.
Lemma D_8f748 : decode_any W_8f748 = Some (Branch BC_LT 11 10 212, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8f74c : bv 32 := 0xfff81517.
Lemma F_8f74c : fetch_word Plain.M.loaded_segments (0x8f7a4 : word) = Some W_8f74c.
Proof. vm_refl. Qed.
Lemma D_8f74c : decode_any W_8f74c = Some (Auipc 10 1048449, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8f750 : bv 32 := 0xfff8c597.
Lemma F_8f750 : fetch_word Plain.M.loaded_segments (0x8f7a8 : word) = Some W_8f750.
Proof. vm_refl. Qed.
Lemma D_8f750 : decode_any W_8f750 = Some (Auipc 11 1048460, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8f754 : bv 32 := 0xbb150513.
Lemma F_8f754 : fetch_word Plain.M.loaded_segments (0x8f7ac : word) = Some W_8f754.
Proof. vm_refl. Qed.
Lemma D_8f754 : decode_any W_8f754 = Some (OpImm ALU_ADD 10 10 2993, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8f758 : bv 32 := 0xd6358593.
Lemma F_8f758 : fetch_word Plain.M.loaded_segments (0x8f7b0 : word) = Some W_8f758.
Proof. vm_refl. Qed.
Lemma D_8f758 : decode_any W_8f758 = Some (OpImm ALU_ADD 11 11 3427, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8f75c : bv 32 := 0x0500006f.
Lemma F_8f75c : fetch_word Plain.M.loaded_segments (0x8f7b4 : word) = Some W_8f75c.
Proof. vm_refl. Qed.
Lemma D_8f75c : decode_any W_8f75c = Some (Jal 0 80, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8f7ac : bv 32 := 0x00040613.
Lemma F_8f7ac : fetch_word Plain.M.loaded_segments (0x8f804 : word) = Some W_8f7ac.
Proof. vm_refl. Qed.
Lemma D_8f7ac : decode_any W_8f7ac = Some (OpImm ALU_ADD 12 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8f7b0 : bv 32 := 0x02813083.
Lemma F_8f7b0 : fetch_word Plain.M.loaded_segments (0x8f808 : word) = Some W_8f7b0.
Proof. vm_refl. Qed.
Lemma D_8f7b0 : decode_any W_8f7b0 = Some (Load SZ8 true 1 2 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8f7b4 : bv 32 := 0x02013403.
Lemma F_8f7b4 : fetch_word Plain.M.loaded_segments (0x8f80c : word) = Some W_8f7b4.
Proof. vm_refl. Qed.
Lemma D_8f7b4 : decode_any W_8f7b4 = Some (Load SZ8 true 8 2 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8f7b8 : bv 32 := 0x01813483.
Lemma F_8f7b8 : fetch_word Plain.M.loaded_segments (0x8f810 : word) = Some W_8f7b8.
Proof. vm_refl. Qed.
Lemma D_8f7b8 : decode_any W_8f7b8 = Some (Load SZ8 true 9 2 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8f7bc : bv 32 := 0x01013903.
Lemma F_8f7bc : fetch_word Plain.M.loaded_segments (0x8f814 : word) = Some W_8f7bc.
Proof. vm_refl. Qed.
Lemma D_8f7bc : decode_any W_8f7bc = Some (Load SZ8 true 18 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8f7c0 : bv 32 := 0x00813983.
Lemma F_8f7c0 : fetch_word Plain.M.loaded_segments (0x8f818 : word) = Some W_8f7c0.
Proof. vm_refl. Qed.
Lemma D_8f7c0 : decode_any W_8f7c0 = Some (Load SZ8 true 19 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8f7c4 : bv 32 := 0x03010113.
Lemma F_8f7c4 : fetch_word Plain.M.loaded_segments (0x8f81c : word) = Some W_8f7c4.
Proof. vm_refl. Qed.
Lemma D_8f7c4 : decode_any W_8f7c4 = Some (OpImm ALU_ADD 2 2 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8f7c8 : bv 32 := 0x8fdd306f.
Lemma F_8f7c8 : fetch_word Plain.M.loaded_segments (0x8f820 : word) = Some W_8f7c8.
Proof. vm_refl. Qed.
Lemma D_8f7c8 : decode_any W_8f7c8 = Some (Jal 0 1915132, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8f810 : bv 32 := 0x00048513.
Lemma F_8f810 : fetch_word Plain.M.loaded_segments (0x8f868 : word) = Some W_8f810.
Proof. vm_refl. Qed.
Lemma D_8f810 : decode_any W_8f810 = Some (OpImm ALU_ADD 10 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_8f814 : bv 32 := 0xbcddd0ef.
Lemma F_8f814 : fetch_word Plain.M.loaded_segments (0x8f86c : word) = Some W_8f814.
Proof. vm_refl. Qed.
Lemma D_8f814 : decode_any W_8f814 = Some (Jal 1 1956812, 4%Z).
Proof. vm_refl. Qed.

