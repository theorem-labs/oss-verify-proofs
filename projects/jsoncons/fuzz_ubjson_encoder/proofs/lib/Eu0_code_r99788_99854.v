(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
(* [comment removed for export] *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require BvWfKernel.

From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.jsoncons.fuzz_ubjson_encoder.images Require Import Ubsan.
Open Scope bv_scope.

Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

Definition W_9d67c : bv 32 := 0xfd010113.
Lemma F_9d67c : fetch_word Ubsan.M.loaded_segments (0x9d6c8 : word) = Some W_9d67c.
Proof. vm_refl. Qed.
Lemma D_9d67c : decode_any W_9d67c = Some (OpImm ALU_ADD 2 2 4048, 4%Z).
Proof. vm_refl. Qed.

Definition W_9d680 : bv 32 := 0x02113423.
Lemma F_9d680 : fetch_word Ubsan.M.loaded_segments (0x9d6cc : word) = Some W_9d680.
Proof. vm_refl. Qed.
Lemma D_9d680 : decode_any W_9d680 = Some (Store SZ8 2 1 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_9d684 : bv 32 := 0x02813023.
Lemma F_9d684 : fetch_word Ubsan.M.loaded_segments (0x9d6d0 : word) = Some W_9d684.
Proof. vm_refl. Qed.
Lemma D_9d684 : decode_any W_9d684 = Some (Store SZ8 2 8 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_9d688 : bv 32 := 0x00913c23.
Lemma F_9d688 : fetch_word Ubsan.M.loaded_segments (0x9d6d4 : word) = Some W_9d688.
Proof. vm_refl. Qed.
Lemma D_9d688 : decode_any W_9d688 = Some (Store SZ8 2 9 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_9d68c : bv 32 := 0x01213823.
Lemma F_9d68c : fetch_word Ubsan.M.loaded_segments (0x9d6d8 : word) = Some W_9d68c.
Proof. vm_refl. Qed.
Lemma D_9d68c : decode_any W_9d68c = Some (Store SZ8 2 18 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_9d690 : bv 32 := 0x01313423.
Lemma F_9d690 : fetch_word Ubsan.M.loaded_segments (0x9d6dc : word) = Some W_9d690.
Proof. vm_refl. Qed.
Lemma D_9d690 : decode_any W_9d690 = Some (Store SZ8 2 19 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_9d694 : bv 32 := 0x0004f517.
Lemma F_9d694 : fetch_word Ubsan.M.loaded_segments (0x9d6e0 : word) = Some W_9d694.
Proof. vm_refl. Qed.
Lemma D_9d694 : decode_any W_9d694 = Some (Auipc 10 79, 4%Z).
Proof. vm_refl. Qed.

Definition W_9d698 : bv 32 := 0x52850913.
Lemma F_9d698 : fetch_word Ubsan.M.loaded_segments (0x9d6e4 : word) = Some W_9d698.
Proof. vm_refl. Qed.
Lemma D_9d698 : decode_any W_9d698 = Some (OpImm ALU_ADD 18 10 1320, 4%Z).
Proof. vm_refl. Qed.

Definition W_9d69c : bv 32 := 0x00490413.
Lemma F_9d69c : fetch_word Ubsan.M.loaded_segments (0x9d6e8 : word) = Some W_9d69c.
Proof. vm_refl. Qed.
Lemma D_9d69c : decode_any W_9d69c = Some (OpImm ALU_ADD 8 18 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_9d6a0 : bv 32 := 0x00040513.
Lemma F_9d6a0 : fetch_word Ubsan.M.loaded_segments (0x9d6ec : word) = Some W_9d6a0.
Proof. vm_refl. Qed.
Lemma D_9d6a0 : decode_any W_9d6a0 = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_9d6a4 : bv 32 := 0x5a8110ef.
Lemma F_9d6a4 : fetch_word Ubsan.M.loaded_segments (0x9d6f0 : word) = Some W_9d6a4.
Proof. vm_refl. Qed.
Lemma D_9d6a4 : decode_any W_9d6a4 = Some (Jal 1 71080, 4%Z).
Proof. vm_refl. Qed.

Definition W_9d6a8 : bv 32 := 0x01093503.
Lemma F_9d6a8 : fetch_word Ubsan.M.loaded_segments (0x9d6f4 : word) = Some W_9d6a8.
Proof. vm_refl. Qed.
Lemma D_9d6a8 : decode_any W_9d6a8 = Some (Load SZ8 true 10 18 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_9d6ac : bv 32 := 0x06050863.
Lemma F_9d6ac : fetch_word Ubsan.M.loaded_segments (0x9d6f8 : word) = Some W_9d6ac.
Proof. vm_refl. Qed.
Lemma D_9d6ac : decode_any W_9d6ac = Some (Branch BC_EQ 10 0 112, 4%Z).
Proof. vm_refl. Qed.

Definition W_9d6b0 : bv 32 := 0x00892583.
Lemma F_9d6b0 : fetch_word Ubsan.M.loaded_segments (0x9d6fc : word) = Some W_9d6b0.
Proof. vm_refl. Qed.
Lemma D_9d6b0 : decode_any W_9d6b0 = Some (Load SZ4 true 11 18 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_9d6b4 : bv 32 := 0x0180006f.
Lemma F_9d6b4 : fetch_word Ubsan.M.loaded_segments (0x9d700 : word) = Some W_9d6b4.
Proof. vm_refl. Qed.
Lemma D_9d6b4 : decode_any W_9d6b4 = Some (Jal 0 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_9d6b8 : bv 32 := 0x00053503.
Lemma F_9d6b8 : fetch_word Ubsan.M.loaded_segments (0x9d704 : word) = Some W_9d6b8.
Proof. vm_refl. Qed.
Lemma D_9d6b8 : decode_any W_9d6b8 = Some (Load SZ8 true 10 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_9d6bc : bv 32 := 0x02000593.
Lemma F_9d6bc : fetch_word Ubsan.M.loaded_segments (0x9d708 : word) = Some W_9d6bc.
Proof. vm_refl. Qed.
Lemma D_9d6bc : decode_any W_9d6bc = Some (OpImm ALU_ADD 11 0 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_9d6c0 : bv 32 := 0x00b92423.
Lemma F_9d6c0 : fetch_word Ubsan.M.loaded_segments (0x9d70c : word) = Some W_9d6c0.
Proof. vm_refl. Qed.
Lemma D_9d6c0 : decode_any W_9d6c0 = Some (Store SZ4 18 11 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_9d6c4 : bv 32 := 0x00a93823.
Lemma F_9d6c4 : fetch_word Ubsan.M.loaded_segments (0x9d710 : word) = Some W_9d6c4.
Proof. vm_refl. Qed.
Lemma D_9d6c4 : decode_any W_9d6c4 = Some (Store SZ8 18 10 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_9d6c8 : bv 32 := 0x04050a63.
Lemma F_9d6c8 : fetch_word Ubsan.M.loaded_segments (0x9d714 : word) = Some W_9d6c8.
Proof. vm_refl. Qed.
Lemma D_9d6c8 : decode_any W_9d6c8 = Some (Branch BC_EQ 10 0 84, 4%Z).
Proof. vm_refl. Qed.

Definition W_9d6cc : bv 32 := 0xfff5861b.
Lemma F_9d6cc : fetch_word Ubsan.M.loaded_segments (0x9d718 : word) = Some W_9d6cc.
Proof. vm_refl. Qed.
Lemma D_9d6cc : decode_any W_9d6cc = Some (OpImm32 12 11 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_9d6d0 : bv 32 := 0x00c92423.
Lemma F_9d6d0 : fetch_word Ubsan.M.loaded_segments (0x9d71c : word) = Some W_9d6d0.
Proof. vm_refl. Qed.
Lemma D_9d6d0 : decode_any W_9d6d0 = Some (Store SZ4 18 12 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_9d6d4 : bv 32 := 0xfeb052e3.
Lemma F_9d6d4 : fetch_word Ubsan.M.loaded_segments (0x9d720 : word) = Some W_9d6d4.
Proof. vm_refl. Qed.
Lemma D_9d6d4 : decode_any W_9d6d4 = Some (Branch BC_GE 0 11 8164, 4%Z).
Proof. vm_refl. Qed.

Definition W_9d6d8 : bv 32 := 0x01093503.
Lemma F_9d6d8 : fetch_word Ubsan.M.loaded_segments (0x9d724 : word) = Some W_9d6d8.
Proof. vm_refl. Qed.
Lemma D_9d6d8 : decode_any W_9d6d8 = Some (Load SZ8 true 10 18 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_9d6dc : bv 32 := 0x00361613.
Lemma F_9d6dc : fetch_word Ubsan.M.loaded_segments (0x9d728 : word) = Some W_9d6dc.
Proof. vm_refl. Qed.
Lemma D_9d6dc : decode_any W_9d6dc = Some (ShiftImm ALU_SLL 12 12 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_9d6e0 : bv 32 := 0x00c50533.
Lemma F_9d6e0 : fetch_word Ubsan.M.loaded_segments (0x9d72c : word) = Some W_9d6e0.
Proof. vm_refl. Qed.
Lemma D_9d6e0 : decode_any W_9d6e0 = Some (Op ALU_ADD 10 10 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_9d6e4 : bv 32 := 0x00853983.
Lemma F_9d6e4 : fetch_word Ubsan.M.loaded_segments (0x9d730 : word) = Some W_9d6e4.
Proof. vm_refl. Qed.
Lemma D_9d6e4 : decode_any W_9d6e4 = Some (Load SZ8 true 19 10 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_9d6e8 : bv 32 := 0x10853483.
Lemma F_9d6e8 : fetch_word Ubsan.M.loaded_segments (0x9d734 : word) = Some W_9d6e8.
Proof. vm_refl. Qed.
Lemma D_9d6e8 : decode_any W_9d6e8 = Some (Load SZ8 true 9 10 264, 4%Z).
Proof. vm_refl. Qed.

Definition W_9d6ec : bv 32 := 0x00040513.
Lemma F_9d6ec : fetch_word Ubsan.M.loaded_segments (0x9d738 : word) = Some W_9d6ec.
Proof. vm_refl. Qed.
Lemma D_9d6ec : decode_any W_9d6ec = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_9d6f0 : bv 32 := 0x7e4110ef.
Lemma F_9d6f0 : fetch_word Ubsan.M.loaded_segments (0x9d73c : word) = Some W_9d6f0.
Proof. vm_refl. Qed.
Lemma D_9d6f0 : decode_any W_9d6f0 = Some (Jal 1 71652, 4%Z).
Proof. vm_refl. Qed.

Definition W_9d6f4 : bv 32 := 0x00048513.
Lemma F_9d6f4 : fetch_word Ubsan.M.loaded_segments (0x9d740 : word) = Some W_9d6f4.
Proof. vm_refl. Qed.
Lemma D_9d6f4 : decode_any W_9d6f4 = Some (OpImm ALU_ADD 10 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_9d6f8 : bv 32 := 0x000980e7.
Lemma F_9d6f8 : fetch_word Ubsan.M.loaded_segments (0x9d744 : word) = Some W_9d6f8.
Proof. vm_refl. Qed.
Lemma D_9d6f8 : decode_any W_9d6f8 = Some (Jalr 1 19 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_9d6fc : bv 32 := 0x00040513.
Lemma F_9d6fc : fetch_word Ubsan.M.loaded_segments (0x9d748 : word) = Some W_9d6fc.
Proof. vm_refl. Qed.
Lemma D_9d6fc : decode_any W_9d6fc = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_9d700 : bv 32 := 0x54c110ef.
Lemma F_9d700 : fetch_word Ubsan.M.loaded_segments (0x9d74c : word) = Some W_9d700.
Proof. vm_refl. Qed.
Lemma D_9d700 : decode_any W_9d700 = Some (Jal 1 70988, 4%Z).
Proof. vm_refl. Qed.

Definition W_9d704 : bv 32 := 0x00892503.
Lemma F_9d704 : fetch_word Ubsan.M.loaded_segments (0x9d750 : word) = Some W_9d704.
Proof. vm_refl. Qed.
Lemma D_9d704 : decode_any W_9d704 = Some (Load SZ4 true 10 18 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_9d708 : bv 32 := 0xfff5061b.
Lemma F_9d708 : fetch_word Ubsan.M.loaded_segments (0x9d754 : word) = Some W_9d708.
Proof. vm_refl. Qed.
Lemma D_9d708 : decode_any W_9d708 = Some (OpImm32 12 10 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_9d70c : bv 32 := 0x00c92423.
Lemma F_9d70c : fetch_word Ubsan.M.loaded_segments (0x9d758 : word) = Some W_9d70c.
Proof. vm_refl. Qed.
Lemma D_9d70c : decode_any W_9d70c = Some (Store SZ4 18 12 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_9d710 : bv 32 := 0xfca044e3.
Lemma F_9d710 : fetch_word Ubsan.M.loaded_segments (0x9d75c : word) = Some W_9d710.
Proof. vm_refl. Qed.
Lemma D_9d710 : decode_any W_9d710 = Some (Branch BC_LT 0 10 8136, 4%Z).
Proof. vm_refl. Qed.

Definition W_9d714 : bv 32 := 0x01093503.
Lemma F_9d714 : fetch_word Ubsan.M.loaded_segments (0x9d760 : word) = Some W_9d714.
Proof. vm_refl. Qed.
Lemma D_9d714 : decode_any W_9d714 = Some (Load SZ8 true 10 18 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_9d718 : bv 32 := 0xfa1ff06f.
Lemma F_9d718 : fetch_word Ubsan.M.loaded_segments (0x9d764 : word) = Some W_9d718.
Proof. vm_refl. Qed.
Lemma D_9d718 : decode_any W_9d718 = Some (Jal 0 2097056, 4%Z).
Proof. vm_refl. Qed.

Definition W_9d71c : bv 32 := 0x00100513.
Lemma F_9d71c : fetch_word Ubsan.M.loaded_segments (0x9d768 : word) = Some W_9d71c.
Proof. vm_refl. Qed.
Lemma D_9d71c : decode_any W_9d71c = Some (OpImm ALU_ADD 10 0 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_9d720 : bv 32 := 0x00a90023.
Lemma F_9d720 : fetch_word Ubsan.M.loaded_segments (0x9d76c : word) = Some W_9d720.
Proof. vm_refl. Qed.
Lemma D_9d720 : decode_any W_9d720 = Some (Store SZ1 18 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_9d724 : bv 32 := 0x00040513.
Lemma F_9d724 : fetch_word Ubsan.M.loaded_segments (0x9d770 : word) = Some W_9d724.
Proof. vm_refl. Qed.
Lemma D_9d724 : decode_any W_9d724 = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_9d728 : bv 32 := 0x02813083.
Lemma F_9d728 : fetch_word Ubsan.M.loaded_segments (0x9d774 : word) = Some W_9d728.
Proof. vm_refl. Qed.
Lemma D_9d728 : decode_any W_9d728 = Some (Load SZ8 true 1 2 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_9d72c : bv 32 := 0x02013403.
Lemma F_9d72c : fetch_word Ubsan.M.loaded_segments (0x9d778 : word) = Some W_9d72c.
Proof. vm_refl. Qed.
Lemma D_9d72c : decode_any W_9d72c = Some (Load SZ8 true 8 2 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_9d730 : bv 32 := 0x01813483.
Lemma F_9d730 : fetch_word Ubsan.M.loaded_segments (0x9d77c : word) = Some W_9d730.
Proof. vm_refl. Qed.
Lemma D_9d730 : decode_any W_9d730 = Some (Load SZ8 true 9 2 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_9d734 : bv 32 := 0x01013903.
Lemma F_9d734 : fetch_word Ubsan.M.loaded_segments (0x9d780 : word) = Some W_9d734.
Proof. vm_refl. Qed.
Lemma D_9d734 : decode_any W_9d734 = Some (Load SZ8 true 18 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_9d738 : bv 32 := 0x00813983.
Lemma F_9d738 : fetch_word Ubsan.M.loaded_segments (0x9d784 : word) = Some W_9d738.
Proof. vm_refl. Qed.
Lemma D_9d738 : decode_any W_9d738 = Some (Load SZ8 true 19 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_9d73c : bv 32 := 0x03010113.
Lemma F_9d73c : fetch_word Ubsan.M.loaded_segments (0x9d788 : word) = Some W_9d73c.
Proof. vm_refl. Qed.
Lemma D_9d73c : decode_any W_9d73c = Some (OpImm ALU_ADD 2 2 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_9d740 : bv 32 := 0x7941106f.
Lemma F_9d740 : fetch_word Ubsan.M.loaded_segments (0x9d78c : word) = Some W_9d740.
Proof. vm_refl. Qed.
Lemma D_9d740 : decode_any W_9d740 = Some (Jal 0 71572, 4%Z).
Proof. vm_refl. Qed.

Definition W_9d744 : bv 32 := 0x00008067.
Lemma F_9d744 : fetch_word Ubsan.M.loaded_segments (0x9d790 : word) = Some W_9d744.
Proof. vm_refl. Qed.
Lemma D_9d744 : decode_any W_9d744 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.
