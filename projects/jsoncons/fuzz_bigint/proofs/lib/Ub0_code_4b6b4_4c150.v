(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.jsoncons.fuzz_bigint.images Require Import Ubsan.
Open Scope bv_scope.

#[local] Hint Extern 0 (BvWf _ _) =>
  (lazymatch goal with |- BvWf ?n ?v => is_closed_term n; is_closed_term v end; exact I) : typeclass_instances.

Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

Definition W_4b6b4 : bv 32 := 0x00008067.
Lemma F_4b6b4 : fetch_word Ubsan.M.loaded_segments (0x4b6b4 : word) = Some W_4b6b4.
Proof. vm_refl. Qed.
Lemma D_4b6b4 : decode_any W_4b6b4 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_4b6b8 : bv 32 := 0xe8010113.
Lemma F_4b6b8 : fetch_word Ubsan.M.loaded_segments (0x4b6b8 : word) = Some W_4b6b8.
Proof. vm_refl. Qed.
Lemma D_4b6b8 : decode_any W_4b6b8 = Some (OpImm ALU_ADD 2 2 3712, 4%Z).
Proof. vm_refl. Qed.

Definition W_4b6bc : bv 32 := 0x16113c23.
Lemma F_4b6bc : fetch_word Ubsan.M.loaded_segments (0x4b6bc : word) = Some W_4b6bc.
Proof. vm_refl. Qed.
Lemma D_4b6bc : decode_any W_4b6bc = Some (Store SZ8 2 1 376, 4%Z).
Proof. vm_refl. Qed.

Definition W_4b6c0 : bv 32 := 0x16813823.
Lemma F_4b6c0 : fetch_word Ubsan.M.loaded_segments (0x4b6c0 : word) = Some W_4b6c0.
Proof. vm_refl. Qed.
Lemma D_4b6c0 : decode_any W_4b6c0 = Some (Store SZ8 2 8 368, 4%Z).
Proof. vm_refl. Qed.

Definition W_4b6c4 : bv 32 := 0x16913423.
Lemma F_4b6c4 : fetch_word Ubsan.M.loaded_segments (0x4b6c4 : word) = Some W_4b6c4.
Proof. vm_refl. Qed.
Lemma D_4b6c4 : decode_any W_4b6c4 = Some (Store SZ8 2 9 360, 4%Z).
Proof. vm_refl. Qed.

Definition W_4b6c8 : bv 32 := 0x17213023.
Lemma F_4b6c8 : fetch_word Ubsan.M.loaded_segments (0x4b6c8 : word) = Some W_4b6c8.
Proof. vm_refl. Qed.
Lemma D_4b6c8 : decode_any W_4b6c8 = Some (Store SZ8 2 18 352, 4%Z).
Proof. vm_refl. Qed.

Definition W_4b6cc : bv 32 := 0x00058413.
Lemma F_4b6cc : fetch_word Ubsan.M.loaded_segments (0x4b6cc : word) = Some W_4b6cc.
Proof. vm_refl. Qed.
Lemma D_4b6cc : decode_any W_4b6cc = Some (OpImm ALU_ADD 8 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_4b6d0 : bv 32 := 0x00050493.
Lemma F_4b6d0 : fetch_word Ubsan.M.loaded_segments (0x4b6d0 : word) = Some W_4b6d0.
Proof. vm_refl. Qed.
Lemma D_4b6d0 : decode_any W_4b6d0 = Some (OpImm ALU_ADD 9 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_4b6d4 : bv 32 := 0x03010513.
Lemma F_4b6d4 : fetch_word Ubsan.M.loaded_segments (0x4b6d4 : word) = Some W_4b6d4.
Proof. vm_refl. Qed.
Lemma D_4b6d4 : decode_any W_4b6d4 = Some (OpImm ALU_ADD 10 2 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_4b6d8 : bv 32 := 0x13000613.
Lemma F_4b6d8 : fetch_word Ubsan.M.loaded_segments (0x4b6d8 : word) = Some W_4b6d8.
Proof. vm_refl. Qed.
Lemma D_4b6d8 : decode_any W_4b6d8 = Some (OpImm ALU_ADD 12 0 304, 4%Z).
Proof. vm_refl. Qed.

Definition W_4b6dc : bv 32 := 0x00000593.
Lemma F_4b6dc : fetch_word Ubsan.M.loaded_segments (0x4b6dc : word) = Some W_4b6dc.
Proof. vm_refl. Qed.
Lemma D_4b6dc : decode_any W_4b6dc = Some (OpImm ALU_ADD 11 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_4b6e0 : bv 32 := 0x2c00e0ef.
Lemma F_4b6e0 : fetch_word Ubsan.M.loaded_segments (0x4b6e0 : word) = Some W_4b6e0.
Proof. vm_refl. Qed.
Lemma D_4b6e0 : decode_any W_4b6e0 = Some (Jal 1 58048, 4%Z).
Proof. vm_refl. Qed.

Definition W_4b6e4 : bv 32 := 0x00014517.
Lemma F_4b6e4 : fetch_word Ubsan.M.loaded_segments (0x4b6e4 : word) = Some W_4b6e4.
Proof. vm_refl. Qed.
Lemma D_4b6e4 : decode_any W_4b6e4 = Some (Auipc 10 20, 4%Z).
Proof. vm_refl. Qed.

Definition W_4b6e8 : bv 32 := 0x9dc53503.
Lemma F_4b6e8 : fetch_word Ubsan.M.loaded_segments (0x4b6e8 : word) = Some W_4b6e8.
Proof. vm_refl. Qed.
Lemma D_4b6e8 : decode_any W_4b6e8 = Some (Load SZ8 true 10 10 2524, 4%Z).
Proof. vm_refl. Qed.

Definition W_4b6ec : bv 32 := 0x00953023.
Lemma F_4b6ec : fetch_word Ubsan.M.loaded_segments (0x4b6ec : word) = Some W_4b6ec.
Proof. vm_refl. Qed.
Lemma D_4b6ec : decode_any W_4b6ec = Some (Store SZ8 10 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_4b6f0 : bv 32 := 0x0004b503.
Lemma F_4b6f0 : fetch_word Ubsan.M.loaded_segments (0x4b6f0 : word) = Some W_4b6f0.
Proof. vm_refl. Qed.
Lemma D_4b6f0 : decode_any W_4b6f0 = Some (Load SZ8 true 10 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_4b6f4 : bv 32 := 0x00848493.
Lemma F_4b6f4 : fetch_word Ubsan.M.loaded_segments (0x4b6f4 : word) = Some W_4b6f4.
Proof. vm_refl. Qed.
Lemma D_4b6f4 : decode_any W_4b6f4 = Some (OpImm ALU_ADD 9 9 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_4b6f8 : bv 32 := 0xfe051ce3.
Lemma F_4b6f8 : fetch_word Ubsan.M.loaded_segments (0x4b6f8 : word) = Some W_4b6f8.
Proof. vm_refl. Qed.
Lemma D_4b6f8 : decode_any W_4b6f8 = Some (Branch BC_NE 10 0 8184, 4%Z).
Proof. vm_refl. Qed.

Definition W_4b6fc : bv 32 := 0x00046517.
Lemma F_4b6fc : fetch_word Ubsan.M.loaded_segments (0x4b6fc : word) = Some W_4b6fc.
Proof. vm_refl. Qed.
Lemma D_4b6fc : decode_any W_4b6fc = Some (Auipc 10 70, 4%Z).
Proof. vm_refl. Qed.

Definition W_4b700 : bv 32 := 0xacc50913.
Lemma F_4b700 : fetch_word Ubsan.M.loaded_segments (0x4b700 : word) = Some W_4b700.
Proof. vm_refl. Qed.
Lemma D_4b700 : decode_any W_4b700 = Some (OpImm ALU_ADD 18 10 2764, 4%Z).
Proof. vm_refl. Qed.

Definition W_4b704 : bv 32 := 0x00993423.
Lemma F_4b704 : fetch_word Ubsan.M.loaded_segments (0x4b704 : word) = Some W_4b704.
Proof. vm_refl. Qed.
Lemma D_4b704 : decode_any W_4b704 = Some (Store SZ8 18 9 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_4b708 : bv 32 := 0x0004b583.
Lemma F_4b708 : fetch_word Ubsan.M.loaded_segments (0x4b708 : word) = Some W_4b708.
Proof. vm_refl. Qed.
Lemma D_4b708 : decode_any W_4b708 = Some (Load SZ8 true 11 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_4b70c : bv 32 := 0x04058c63.
Lemma F_4b70c : fetch_word Ubsan.M.loaded_segments (0x4b70c : word) = Some W_4b70c.
Proof. vm_refl. Qed.
Lemma D_4b70c : decode_any W_4b70c = Some (Branch BC_EQ 11 0 88, 4%Z).
Proof. vm_refl. Qed.

Definition W_4b710 : bv 32 := 0x01048493.
Lemma F_4b710 : fetch_word Ubsan.M.loaded_segments (0x4b710 : word) = Some W_4b710.
Proof. vm_refl. Qed.
Lemma D_4b710 : decode_any W_4b710 = Some (OpImm ALU_ADD 9 9 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_4b714 : bv 32 := 0x02500513.
Lemma F_4b714 : fetch_word Ubsan.M.loaded_segments (0x4b714 : word) = Some W_4b714.
Proof. vm_refl. Qed.
Lemma D_4b714 : decode_any W_4b714 = Some (OpImm ALU_ADD 10 0 37, 4%Z).
Proof. vm_refl. Qed.

Definition W_4b718 : bv 32 := 0x03010613.
Lemma F_4b718 : fetch_word Ubsan.M.loaded_segments (0x4b718 : word) = Some W_4b718.
Proof. vm_refl. Qed.
Lemma D_4b718 : decode_any W_4b718 = Some (OpImm ALU_ADD 12 2 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_4b71c : bv 32 := 0x0100006f.
Lemma F_4b71c : fetch_word Ubsan.M.loaded_segments (0x4b71c : word) = Some W_4b71c.
Proof. vm_refl. Qed.
Lemma D_4b71c : decode_any W_4b71c = Some (Jal 0 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_4b720 : bv 32 := 0x0004b583.
Lemma F_4b720 : fetch_word Ubsan.M.loaded_segments (0x4b720 : word) = Some W_4b720.
Proof. vm_refl. Qed.
Lemma D_4b720 : decode_any W_4b720 = Some (Load SZ8 true 11 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_4b724 : bv 32 := 0x01048493.
Lemma F_4b724 : fetch_word Ubsan.M.loaded_segments (0x4b724 : word) = Some W_4b724.
Proof. vm_refl. Qed.
Lemma D_4b724 : decode_any W_4b724 = Some (OpImm ALU_ADD 9 9 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_4b728 : bv 32 := 0x00058e63.
Lemma F_4b728 : fetch_word Ubsan.M.loaded_segments (0x4b728 : word) = Some W_4b728.
Proof. vm_refl. Qed.
Lemma D_4b728 : decode_any W_4b728 = Some (Branch BC_EQ 11 0 28, 4%Z).
Proof. vm_refl. Qed.

Definition W_4b72c : bv 32 := 0xfeb56ae3.
Lemma F_4b72c : fetch_word Ubsan.M.loaded_segments (0x4b72c : word) = Some W_4b72c.
Proof. vm_refl. Qed.
Lemma D_4b72c : decode_any W_4b72c = Some (Branch BC_LTU 10 11 8180, 4%Z).
Proof. vm_refl. Qed.

Definition W_4b730 : bv 32 := 0xff84b683.
Lemma F_4b730 : fetch_word Ubsan.M.loaded_segments (0x4b730 : word) = Some W_4b730.
Proof. vm_refl. Qed.
Lemma D_4b730 : decode_any W_4b730 = Some (Load SZ8 true 13 9 4088, 4%Z).
Proof. vm_refl. Qed.

Definition W_4b734 : bv 32 := 0x00359593.
Lemma F_4b734 : fetch_word Ubsan.M.loaded_segments (0x4b734 : word) = Some W_4b734.
Proof. vm_refl. Qed.
Lemma D_4b734 : decode_any W_4b734 = Some (ShiftImm ALU_SLL 11 11 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_4b738 : bv 32 := 0x00b605b3.
Lemma F_4b738 : fetch_word Ubsan.M.loaded_segments (0x4b738 : word) = Some W_4b738.
Proof. vm_refl. Qed.
Lemma D_4b738 : decode_any W_4b738 = Some (Op ALU_ADD 11 12 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_4b73c : bv 32 := 0x00d5b023.
Lemma F_4b73c : fetch_word Ubsan.M.loaded_segments (0x4b73c : word) = Some W_4b73c.
Proof. vm_refl. Qed.
Lemma D_4b73c : decode_any W_4b73c = Some (Store SZ8 11 13 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_4b740 : bv 32 := 0xfe1ff06f.
Lemma F_4b740 : fetch_word Ubsan.M.loaded_segments (0x4b740 : word) = Some W_4b740.
Proof. vm_refl. Qed.
Lemma D_4b740 : decode_any W_4b740 = Some (Jal 0 2097120, 4%Z).
Proof. vm_refl. Qed.

Definition W_4b744 : bv 32 := 0x0b013583.
Lemma F_4b744 : fetch_word Ubsan.M.loaded_segments (0x4b744 : word) = Some W_4b744.
Proof. vm_refl. Qed.
Lemma D_4b744 : decode_any W_4b744 = Some (Load SZ8 true 11 2 176, 4%Z).
Proof. vm_refl. Qed.

Definition W_4b748 : bv 32 := 0x13013503.
Lemma F_4b748 : fetch_word Ubsan.M.loaded_segments (0x4b748 : word) = Some W_4b748.
Proof. vm_refl. Qed.
Lemma D_4b748 : decode_any W_4b748 = Some (Load SZ8 true 10 2 304, 4%Z).
Proof. vm_refl. Qed.

Definition W_4b74c : bv 32 := 0x00046617.
Lemma F_4b74c : fetch_word Ubsan.M.loaded_segments (0x4b74c : word) = Some W_4b74c.
Proof. vm_refl. Qed.
Lemma D_4b74c : decode_any W_4b74c = Some (Auipc 12 70, 4%Z).
Proof. vm_refl. Qed.

Definition W_4b750 : bv 32 := 0xaeb63223.
Lemma F_4b750 : fetch_word Ubsan.M.loaded_segments (0x4b750 : word) = Some W_4b750.
Proof. vm_refl. Qed.
Lemma D_4b750 : decode_any W_4b750 = Some (Store SZ8 12 11 2788, 4%Z).
Proof. vm_refl. Qed.

Definition W_4b754 : bv 32 := 0x00050c63.
Lemma F_4b754 : fetch_word Ubsan.M.loaded_segments (0x4b754 : word) = Some W_4b754.
Proof. vm_refl. Qed.
Lemma D_4b754 : decode_any W_4b754 = Some (Branch BC_EQ 10 0 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_4b76c : bv 32 := 0x06013503.
Lemma F_4b76c : fetch_word Ubsan.M.loaded_segments (0x4b76c : word) = Some W_4b76c.
Proof. vm_refl. Qed.
Lemma D_4b76c : decode_any W_4b76c = Some (Load SZ8 true 10 2 96, 4%Z).
Proof. vm_refl. Qed.

Definition W_4b770 : bv 32 := 0x02a93823.
Lemma F_4b770 : fetch_word Ubsan.M.loaded_segments (0x4b770 : word) = Some W_4b770.
Proof. vm_refl. Qed.
Lemma D_4b770 : decode_any W_4b770 = Some (Store SZ8 18 10 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_4b774 : bv 32 := 0x00041463.
Lemma F_4b774 : fetch_word Ubsan.M.loaded_segments (0x4b774 : word) = Some W_4b774.
Proof. vm_refl. Qed.
Lemma D_4b774 : decode_any W_4b774 = Some (Branch BC_NE 8 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_4b77c : bv 32 := 0x00041663.
Lemma F_4b77c : fetch_word Ubsan.M.loaded_segments (0x4b77c : word) = Some W_4b77c.
Proof. vm_refl. Qed.
Lemma D_4b77c : decode_any W_4b77c = Some (Branch BC_NE 8 0 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_4b788 : bv 32 := 0x00014517.
Lemma F_4b788 : fetch_word Ubsan.M.loaded_segments (0x4b788 : word) = Some W_4b788.
Proof. vm_refl. Qed.
Lemma D_4b788 : decode_any W_4b788 = Some (Auipc 10 20, 4%Z).
Proof. vm_refl. Qed.

Definition W_4b78c : bv 32 := 0x94053583.
Lemma F_4b78c : fetch_word Ubsan.M.loaded_segments (0x4b78c : word) = Some W_4b78c.
Proof. vm_refl. Qed.
Lemma D_4b78c : decode_any W_4b78c = Some (Load SZ8 true 11 10 2368, 4%Z).
Proof. vm_refl. Qed.

Definition W_4b790 : bv 32 := 0x00014517.
Lemma F_4b790 : fetch_word Ubsan.M.loaded_segments (0x4b790 : word) = Some W_4b790.
Proof. vm_refl. Qed.
Lemma D_4b790 : decode_any W_4b790 = Some (Auipc 10 20, 4%Z).
Proof. vm_refl. Qed.

Definition W_4b794 : bv 32 := 0x94053503.
Lemma F_4b794 : fetch_word Ubsan.M.loaded_segments (0x4b794 : word) = Some W_4b794.
Proof. vm_refl. Qed.
Lemma D_4b794 : decode_any W_4b794 = Some (Load SZ8 true 10 10 2368, 4%Z).
Proof. vm_refl. Qed.

Definition W_4b798 : bv 32 := 0x0085b023.
Lemma F_4b798 : fetch_word Ubsan.M.loaded_segments (0x4b798 : word) = Some W_4b798.
Proof. vm_refl. Qed.
Lemma D_4b798 : decode_any W_4b798 = Some (Store SZ8 11 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_4b79c : bv 32 := 0x00140593.
Lemma F_4b79c : fetch_word Ubsan.M.loaded_segments (0x4b79c : word) = Some W_4b79c.
Proof. vm_refl. Qed.
Lemma D_4b79c : decode_any W_4b79c = Some (OpImm ALU_ADD 11 8 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_4b7a0 : bv 32 := 0x00853023.
Lemma F_4b7a0 : fetch_word Ubsan.M.loaded_segments (0x4b7a0 : word) = Some W_4b7a0.
Proof. vm_refl. Qed.
Lemma D_4b7a0 : decode_any W_4b7a0 = Some (Store SZ8 10 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_4b7a4 : bv 32 := 0x02f00613.
Lemma F_4b7a4 : fetch_word Ubsan.M.loaded_segments (0x4b7a4 : word) = Some W_4b7a4.
Proof. vm_refl. Qed.
Lemma D_4b7a4 : decode_any W_4b7a4 = Some (OpImm ALU_ADD 12 0 47, 4%Z).
Proof. vm_refl. Qed.

Definition W_4b7a8 : bv 32 := 0x00c0006f.
Lemma F_4b7a8 : fetch_word Ubsan.M.loaded_segments (0x4b7a8 : word) = Some W_4b7a8.
Proof. vm_refl. Qed.
Lemma D_4b7a8 : decode_any W_4b7a8 = Some (Jal 0 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_4b7ac : bv 32 := 0x00b53023.
Lemma F_4b7ac : fetch_word Ubsan.M.loaded_segments (0x4b7ac : word) = Some W_4b7ac.
Proof. vm_refl. Qed.
Lemma D_4b7ac : decode_any W_4b7ac = Some (Store SZ8 10 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_4b7b0 : bv 32 := 0x00158593.
Lemma F_4b7b0 : fetch_word Ubsan.M.loaded_segments (0x4b7b0 : word) = Some W_4b7b0.
Proof. vm_refl. Qed.
Lemma D_4b7b0 : decode_any W_4b7b0 = Some (OpImm ALU_ADD 11 11 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_4b7b4 : bv 32 := 0xfff5c683.
Lemma F_4b7b4 : fetch_word Ubsan.M.loaded_segments (0x4b7b4 : word) = Some W_4b7b4.
Proof. vm_refl. Qed.
Lemma D_4b7b4 : decode_any W_4b7b4 = Some (Load SZ1 false 13 11 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_4b7b8 : bv 32 := 0xfec68ae3.
Lemma F_4b7b8 : fetch_word Ubsan.M.loaded_segments (0x4b7b8 : word) = Some W_4b7b8.
Proof. vm_refl. Qed.
Lemma D_4b7b8 : decode_any W_4b7b8 = Some (Branch BC_EQ 13 12 8180, 4%Z).
Proof. vm_refl. Qed.

Definition W_4b7bc : bv 32 := 0xfe069ae3.
Lemma F_4b7bc : fetch_word Ubsan.M.loaded_segments (0x4b7bc : word) = Some W_4b7bc.
Proof. vm_refl. Qed.
Lemma D_4b7bc : decode_any W_4b7bc = Some (Branch BC_NE 13 0 8180, 4%Z).
Proof. vm_refl. Qed.

Definition W_4b7c0 : bv 32 := 0x03010513.
Lemma F_4b7c0 : fetch_word Ubsan.M.loaded_segments (0x4b7c0 : word) = Some W_4b7c0.
Proof. vm_refl. Qed.
Lemma D_4b7c0 : decode_any W_4b7c0 = Some (OpImm ALU_ADD 10 2 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_4b7c4 : bv 32 := 0x214000ef.
Lemma F_4b7c4 : fetch_word Ubsan.M.loaded_segments (0x4b7c4 : word) = Some W_4b7c4.
Proof. vm_refl. Qed.
Lemma D_4b7c4 : decode_any W_4b7c4 = Some (Jal 1 532, 4%Z).
Proof. vm_refl. Qed.

Definition W_4b7c8 : bv 32 := 0x0f813503.
Lemma F_4b7c8 : fetch_word Ubsan.M.loaded_segments (0x4b7c8 : word) = Some W_4b7c8.
Proof. vm_refl. Qed.
Lemma D_4b7c8 : decode_any W_4b7c8 = Some (Load SZ8 true 10 2 248, 4%Z).
Proof. vm_refl. Qed.

Definition W_4b7cc : bv 32 := 0x0e5000ef.
Lemma F_4b7cc : fetch_word Ubsan.M.loaded_segments (0x4b7cc : word) = Some W_4b7cc.
Proof. vm_refl. Qed.
Lemma D_4b7cc : decode_any W_4b7cc = Some (Jal 1 2276, 4%Z).
Proof. vm_refl. Qed.

Definition W_4b7d0 : bv 32 := 0x08813503.
Lemma F_4b7d0 : fetch_word Ubsan.M.loaded_segments (0x4b7d0 : word) = Some W_4b7d0.
Proof. vm_refl. Qed.
Lemma D_4b7d0 : decode_any W_4b7d0 = Some (Load SZ8 true 10 2 136, 4%Z).
Proof. vm_refl. Qed.

Definition W_4b7d4 : bv 32 := 0x09013583.
Lemma F_4b7d4 : fetch_word Ubsan.M.loaded_segments (0x4b7d4 : word) = Some W_4b7d4.
Proof. vm_refl. Qed.
Lemma D_4b7d4 : decode_any W_4b7d4 = Some (Load SZ8 true 11 2 144, 4%Z).
Proof. vm_refl. Qed.

Definition W_4b7d8 : bv 32 := 0x00b51c63.
Lemma F_4b7d8 : fetch_word Ubsan.M.loaded_segments (0x4b7d8 : word) = Some W_4b7d8.
Proof. vm_refl. Qed.
Lemma D_4b7d8 : decode_any W_4b7d8 = Some (Branch BC_NE 10 11 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_4b7dc : bv 32 := 0x09813503.
Lemma F_4b7dc : fetch_word Ubsan.M.loaded_segments (0x4b7dc : word) = Some W_4b7dc.
Proof. vm_refl. Qed.
Lemma D_4b7dc : decode_any W_4b7dc = Some (Load SZ8 true 10 2 152, 4%Z).
Proof. vm_refl. Qed.

Definition W_4b7e0 : bv 32 := 0x0a013583.
Lemma F_4b7e0 : fetch_word Ubsan.M.loaded_segments (0x4b7e0 : word) = Some W_4b7e0.
Proof. vm_refl. Qed.
Lemma D_4b7e0 : decode_any W_4b7e0 = Some (Load SZ8 true 11 2 160, 4%Z).
Proof. vm_refl. Qed.

Definition W_4b7e4 : bv 32 := 0x00b51663.
Lemma F_4b7e4 : fetch_word Ubsan.M.loaded_segments (0x4b7e4 : word) = Some W_4b7e4.
Proof. vm_refl. Qed.
Lemma D_4b7e4 : decode_any W_4b7e4 = Some (Branch BC_NE 10 11 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_4b7e8 : bv 32 := 0x0e813503.
Lemma F_4b7e8 : fetch_word Ubsan.M.loaded_segments (0x4b7e8 : word) = Some W_4b7e8.
Proof. vm_refl. Qed.
Lemma D_4b7e8 : decode_any W_4b7e8 = Some (Load SZ8 true 10 2 232, 4%Z).
Proof. vm_refl. Qed.

Definition W_4b7ec : bv 32 := 0x0e050063.
Lemma F_4b7ec : fetch_word Ubsan.M.loaded_segments (0x4b7ec : word) = Some W_4b7ec.
Proof. vm_refl. Qed.
Lemma D_4b7ec : decode_any W_4b7ec = Some (Branch BC_EQ 10 0 224, 4%Z).
Proof. vm_refl. Qed.

Definition W_4b8cc : bv 32 := 0x17813083.
Lemma F_4b8cc : fetch_word Ubsan.M.loaded_segments (0x4b8cc : word) = Some W_4b8cc.
Proof. vm_refl. Qed.
Lemma D_4b8cc : decode_any W_4b8cc = Some (Load SZ8 true 1 2 376, 4%Z).
Proof. vm_refl. Qed.

Definition W_4b8d0 : bv 32 := 0x17013403.
Lemma F_4b8d0 : fetch_word Ubsan.M.loaded_segments (0x4b8d0 : word) = Some W_4b8d0.
Proof. vm_refl. Qed.
Lemma D_4b8d0 : decode_any W_4b8d0 = Some (Load SZ8 true 8 2 368, 4%Z).
Proof. vm_refl. Qed.

Definition W_4b8d4 : bv 32 := 0x16813483.
Lemma F_4b8d4 : fetch_word Ubsan.M.loaded_segments (0x4b8d4 : word) = Some W_4b8d4.
Proof. vm_refl. Qed.
Lemma D_4b8d4 : decode_any W_4b8d4 = Some (Load SZ8 true 9 2 360, 4%Z).
Proof. vm_refl. Qed.

Definition W_4b8d8 : bv 32 := 0x16013903.
Lemma F_4b8d8 : fetch_word Ubsan.M.loaded_segments (0x4b8d8 : word) = Some W_4b8d8.
Proof. vm_refl. Qed.
Lemma D_4b8d8 : decode_any W_4b8d8 = Some (Load SZ8 true 18 2 352, 4%Z).
Proof. vm_refl. Qed.

Definition W_4b8dc : bv 32 := 0x18010113.
Lemma F_4b8dc : fetch_word Ubsan.M.loaded_segments (0x4b8dc : word) = Some W_4b8dc.
Proof. vm_refl. Qed.
Lemma D_4b8dc : decode_any W_4b8dc = Some (OpImm ALU_ADD 2 2 384, 4%Z).
Proof. vm_refl. Qed.

Definition W_4b8e0 : bv 32 := 0x00008067.
Lemma F_4b8e0 : fetch_word Ubsan.M.loaded_segments (0x4b8e0 : word) = Some W_4b8e0.
Proof. vm_refl. Qed.
Lemma D_4b8e0 : decode_any W_4b8e0 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_4b8e4 : bv 32 := 0xfe010113.
Lemma F_4b8e4 : fetch_word Ubsan.M.loaded_segments (0x4b8e4 : word) = Some W_4b8e4.
Proof. vm_refl. Qed.
Lemma D_4b8e4 : decode_any W_4b8e4 = Some (OpImm ALU_ADD 2 2 4064, 4%Z).
Proof. vm_refl. Qed.

Definition W_4b8e8 : bv 32 := 0x00113c23.
Lemma F_4b8e8 : fetch_word Ubsan.M.loaded_segments (0x4b8e8 : word) = Some W_4b8e8.
Proof. vm_refl. Qed.
Lemma D_4b8e8 : decode_any W_4b8e8 = Some (Store SZ8 2 1 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_4b8ec : bv 32 := 0x00813823.
Lemma F_4b8ec : fetch_word Ubsan.M.loaded_segments (0x4b8ec : word) = Some W_4b8ec.
Proof. vm_refl. Qed.
Lemma D_4b8ec : decode_any W_4b8ec = Some (Store SZ8 2 8 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_4b8f0 : bv 32 := 0x00913423.
Lemma F_4b8f0 : fetch_word Ubsan.M.loaded_segments (0x4b8f0 : word) = Some W_4b8f0.
Proof. vm_refl. Qed.
Lemma D_4b8f0 : decode_any W_4b8f0 = Some (Store SZ8 2 9 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_4b8f4 : bv 32 := 0xdc1ff0ef.
Lemma F_4b8f4 : fetch_word Ubsan.M.loaded_segments (0x4b8f4 : word) = Some W_4b8f4.
Proof. vm_refl. Qed.
Lemma D_4b8f4 : decode_any W_4b8f4 = Some (Jal 1 2096576, 4%Z).
Proof. vm_refl. Qed.

Definition W_4b8f8 : bv 32 := 0x00013517.
Lemma F_4b8f8 : fetch_word Ubsan.M.loaded_segments (0x4b8f8 : word) = Some W_4b8f8.
Proof. vm_refl. Qed.
Lemma D_4b8f8 : decode_any W_4b8f8 = Some (Auipc 10 19, 4%Z).
Proof. vm_refl. Qed.

Definition W_4b8fc : bv 32 := 0x00013597.
Lemma F_4b8fc : fetch_word Ubsan.M.loaded_segments (0x4b8fc : word) = Some W_4b8fc.
Proof. vm_refl. Qed.
Lemma D_4b8fc : decode_any W_4b8fc = Some (Auipc 11 19, 4%Z).
Proof. vm_refl. Qed.

Definition W_4b900 : bv 32 := 0x7e053403.
Lemma F_4b900 : fetch_word Ubsan.M.loaded_segments (0x4b900 : word) = Some W_4b900.
Proof. vm_refl. Qed.
Lemma D_4b900 : decode_any W_4b900 = Some (Load SZ8 true 8 10 2016, 4%Z).
Proof. vm_refl. Qed.

Definition W_4b904 : bv 32 := 0x7e45b483.
Lemma F_4b904 : fetch_word Ubsan.M.loaded_segments (0x4b904 : word) = Some W_4b904.
Proof. vm_refl. Qed.
Lemma D_4b904 : decode_any W_4b904 = Some (Load SZ8 true 9 11 2020, 4%Z).
Proof. vm_refl. Qed.

Definition W_4b908 : bv 32 := 0x0084fa63.
Lemma F_4b908 : fetch_word Ubsan.M.loaded_segments (0x4b908 : word) = Some W_4b908.
Proof. vm_refl. Qed.
Lemma D_4b908 : decode_any W_4b908 = Some (Branch BC_GEU 9 8 20, 4%Z).
Proof. vm_refl. Qed.

Definition W_4b90c : bv 32 := 0x0004b503.
Lemma F_4b90c : fetch_word Ubsan.M.loaded_segments (0x4b90c : word) = Some W_4b90c.
Proof. vm_refl. Qed.
Lemma D_4b90c : decode_any W_4b90c = Some (Load SZ8 true 10 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_4b910 : bv 32 := 0x000500e7.
Lemma F_4b910 : fetch_word Ubsan.M.loaded_segments (0x4b910 : word) = Some W_4b910.
Proof. vm_refl. Qed.
Lemma D_4b910 : decode_any W_4b910 = Some (Jalr 1 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_4b914 : bv 32 := 0x00848493.
Lemma F_4b914 : fetch_word Ubsan.M.loaded_segments (0x4b914 : word) = Some W_4b914.
Proof. vm_refl. Qed.
Lemma D_4b914 : decode_any W_4b914 = Some (OpImm ALU_ADD 9 9 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_4b918 : bv 32 := 0xfe84eae3.
Lemma F_4b918 : fetch_word Ubsan.M.loaded_segments (0x4b918 : word) = Some W_4b918.
Proof. vm_refl. Qed.
Lemma D_4b918 : decode_any W_4b918 = Some (Branch BC_LTU 9 8 8180, 4%Z).
Proof. vm_refl. Qed.

Definition W_4b91c : bv 32 := 0x01813083.
Lemma F_4b91c : fetch_word Ubsan.M.loaded_segments (0x4b91c : word) = Some W_4b91c.
Proof. vm_refl. Qed.
Lemma D_4b91c : decode_any W_4b91c = Some (Load SZ8 true 1 2 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_4b920 : bv 32 := 0x01013403.
Lemma F_4b920 : fetch_word Ubsan.M.loaded_segments (0x4b920 : word) = Some W_4b920.
Proof. vm_refl. Qed.
Lemma D_4b920 : decode_any W_4b920 = Some (Load SZ8 true 8 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_4b924 : bv 32 := 0x00813483.
Lemma F_4b924 : fetch_word Ubsan.M.loaded_segments (0x4b924 : word) = Some W_4b924.
Proof. vm_refl. Qed.
Lemma D_4b924 : decode_any W_4b924 = Some (Load SZ8 true 9 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_4b928 : bv 32 := 0x02010113.
Lemma F_4b928 : fetch_word Ubsan.M.loaded_segments (0x4b928 : word) = Some W_4b928.
Proof. vm_refl. Qed.
Lemma D_4b928 : decode_any W_4b928 = Some (OpImm ALU_ADD 2 2 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_4b92c : bv 32 := 0x00008067.
Lemma F_4b92c : fetch_word Ubsan.M.loaded_segments (0x4b92c : word) = Some W_4b92c.
Proof. vm_refl. Qed.
Lemma D_4b92c : decode_any W_4b92c = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_4b930 : bv 32 := 0xfe010113.
Lemma F_4b930 : fetch_word Ubsan.M.loaded_segments (0x4b930 : word) = Some W_4b930.
Proof. vm_refl. Qed.
Lemma D_4b930 : decode_any W_4b930 = Some (OpImm ALU_ADD 2 2 4064, 4%Z).
Proof. vm_refl. Qed.

Definition W_4b934 : bv 32 := 0x00113c23.
Lemma F_4b934 : fetch_word Ubsan.M.loaded_segments (0x4b934 : word) = Some W_4b934.
Proof. vm_refl. Qed.
Lemma D_4b934 : decode_any W_4b934 = Some (Store SZ8 2 1 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_4b938 : bv 32 := 0x00813823.
Lemma F_4b938 : fetch_word Ubsan.M.loaded_segments (0x4b938 : word) = Some W_4b938.
Proof. vm_refl. Qed.
Lemma D_4b938 : decode_any W_4b938 = Some (Store SZ8 2 8 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_4b93c : bv 32 := 0x00913423.
Lemma F_4b93c : fetch_word Ubsan.M.loaded_segments (0x4b93c : word) = Some W_4b93c.
Proof. vm_refl. Qed.
Lemma D_4b93c : decode_any W_4b93c = Some (Store SZ8 2 9 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_4b940 : bv 32 := 0x01213023.
Lemma F_4b940 : fetch_word Ubsan.M.loaded_segments (0x4b940 : word) = Some W_4b940.
Proof. vm_refl. Qed.
Lemma D_4b940 : decode_any W_4b940 = Some (Store SZ8 2 18 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_4b944 : bv 32 := 0x00060413.
Lemma F_4b944 : fetch_word Ubsan.M.loaded_segments (0x4b944 : word) = Some W_4b944.
Proof. vm_refl. Qed.
Lemma D_4b944 : decode_any W_4b944 = Some (OpImm ALU_ADD 8 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_4b948 : bv 32 := 0x00058493.
Lemma F_4b948 : fetch_word Ubsan.M.loaded_segments (0x4b948 : word) = Some W_4b948.
Proof. vm_refl. Qed.
Lemma D_4b948 : decode_any W_4b948 = Some (OpImm ALU_ADD 9 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_4b94c : bv 32 := 0x00050913.
Lemma F_4b94c : fetch_word Ubsan.M.loaded_segments (0x4b94c : word) = Some W_4b94c.
Proof. vm_refl. Qed.
Lemma D_4b94c : decode_any W_4b94c = Some (OpImm ALU_ADD 18 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_4b950 : bv 32 := 0x00063583.
Lemma F_4b950 : fetch_word Ubsan.M.loaded_segments (0x4b950 : word) = Some W_4b950.
Proof. vm_refl. Qed.
Lemma D_4b950 : decode_any W_4b950 = Some (Load SZ8 true 11 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_4b954 : bv 32 := 0x00349513.
Lemma F_4b954 : fetch_word Ubsan.M.loaded_segments (0x4b954 : word) = Some W_4b954.
Proof. vm_refl. Qed.
Lemma D_4b954 : decode_any W_4b954 = Some (ShiftImm ALU_SLL 10 9 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_4b958 : bv 32 := 0x00a60533.
Lemma F_4b958 : fetch_word Ubsan.M.loaded_segments (0x4b958 : word) = Some W_4b958.
Proof. vm_refl. Qed.
Lemma D_4b958 : decode_any W_4b958 = Some (Op ALU_ADD 10 12 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_4b95c : bv 32 := 0x00850513.
Lemma F_4b95c : fetch_word Ubsan.M.loaded_segments (0x4b95c : word) = Some W_4b95c.
Proof. vm_refl. Qed.
Lemma D_4b95c : decode_any W_4b95c = Some (OpImm ALU_ADD 10 10 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_4b960 : bv 32 := 0xd59ff0ef.
Lemma F_4b960 : fetch_word Ubsan.M.loaded_segments (0x4b960 : word) = Some W_4b960.
Proof. vm_refl. Qed.
Lemma D_4b960 : decode_any W_4b960 = Some (Jal 1 2096472, 4%Z).
Proof. vm_refl. Qed.

Definition W_4b964 : bv 32 := 0x00000517.
Lemma F_4b964 : fetch_word Ubsan.M.loaded_segments (0x4b964 : word) = Some W_4b964.
Proof. vm_refl. Qed.
Lemma D_4b964 : decode_any W_4b964 = Some (Auipc 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_4b968 : bv 32 := 0x02c50313.
Lemma F_4b968 : fetch_word Ubsan.M.loaded_segments (0x4b968 : word) = Some W_4b968.
Proof. vm_refl. Qed.
Lemma D_4b968 : decode_any W_4b968 = Some (OpImm ALU_ADD 6 10 44, 4%Z).
Proof. vm_refl. Qed.

Definition W_4b96c : bv 32 := 0x00090513.
Lemma F_4b96c : fetch_word Ubsan.M.loaded_segments (0x4b96c : word) = Some W_4b96c.
Proof. vm_refl. Qed.
Lemma D_4b96c : decode_any W_4b96c = Some (OpImm ALU_ADD 10 18 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_4b970 : bv 32 := 0x00048593.
Lemma F_4b970 : fetch_word Ubsan.M.loaded_segments (0x4b970 : word) = Some W_4b970.
Proof. vm_refl. Qed.
Lemma D_4b970 : decode_any W_4b970 = Some (OpImm ALU_ADD 11 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_4b974 : bv 32 := 0x00040613.
Lemma F_4b974 : fetch_word Ubsan.M.loaded_segments (0x4b974 : word) = Some W_4b974.
Proof. vm_refl. Qed.
Lemma D_4b974 : decode_any W_4b974 = Some (OpImm ALU_ADD 12 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_4b978 : bv 32 := 0x01813083.
Lemma F_4b978 : fetch_word Ubsan.M.loaded_segments (0x4b978 : word) = Some W_4b978.
Proof. vm_refl. Qed.
Lemma D_4b978 : decode_any W_4b978 = Some (Load SZ8 true 1 2 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_4b97c : bv 32 := 0x01013403.
Lemma F_4b97c : fetch_word Ubsan.M.loaded_segments (0x4b97c : word) = Some W_4b97c.
Proof. vm_refl. Qed.
Lemma D_4b97c : decode_any W_4b97c = Some (Load SZ8 true 8 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_4b980 : bv 32 := 0x00813483.
Lemma F_4b980 : fetch_word Ubsan.M.loaded_segments (0x4b980 : word) = Some W_4b980.
Proof. vm_refl. Qed.
Lemma D_4b980 : decode_any W_4b980 = Some (Load SZ8 true 9 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_4b984 : bv 32 := 0x00013903.
Lemma F_4b984 : fetch_word Ubsan.M.loaded_segments (0x4b984 : word) = Some W_4b984.
Proof. vm_refl. Qed.
Lemma D_4b984 : decode_any W_4b984 = Some (Load SZ8 true 18 2 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_4b988 : bv 32 := 0x02010113.
Lemma F_4b988 : fetch_word Ubsan.M.loaded_segments (0x4b988 : word) = Some W_4b988.
Proof. vm_refl. Qed.
Lemma D_4b988 : decode_any W_4b988 = Some (OpImm ALU_ADD 2 2 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_4b98c : bv 32 := 0x00030067.
Lemma F_4b98c : fetch_word Ubsan.M.loaded_segments (0x4b98c : word) = Some W_4b98c.
Proof. vm_refl. Qed.
Lemma D_4b98c : decode_any W_4b98c = Some (Jalr 0 6 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_4b990 : bv 32 := 0xfd010113.
Lemma F_4b990 : fetch_word Ubsan.M.loaded_segments (0x4b990 : word) = Some W_4b990.
Proof. vm_refl. Qed.
Lemma D_4b990 : decode_any W_4b990 = Some (OpImm ALU_ADD 2 2 4048, 4%Z).
Proof. vm_refl. Qed.

Definition W_4b994 : bv 32 := 0x02113423.
Lemma F_4b994 : fetch_word Ubsan.M.loaded_segments (0x4b994 : word) = Some W_4b994.
Proof. vm_refl. Qed.
Lemma D_4b994 : decode_any W_4b994 = Some (Store SZ8 2 1 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_4b998 : bv 32 := 0x02813023.
Lemma F_4b998 : fetch_word Ubsan.M.loaded_segments (0x4b998 : word) = Some W_4b998.
Proof. vm_refl. Qed.
Lemma D_4b998 : decode_any W_4b998 = Some (Store SZ8 2 8 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_4b99c : bv 32 := 0x00913c23.
Lemma F_4b99c : fetch_word Ubsan.M.loaded_segments (0x4b99c : word) = Some W_4b99c.
Proof. vm_refl. Qed.
Lemma D_4b99c : decode_any W_4b99c = Some (Store SZ8 2 9 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_4b9a0 : bv 32 := 0x01213823.
Lemma F_4b9a0 : fetch_word Ubsan.M.loaded_segments (0x4b9a0 : word) = Some W_4b9a0.
Proof. vm_refl. Qed.
Lemma D_4b9a0 : decode_any W_4b9a0 = Some (Store SZ8 2 18 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_4b9a4 : bv 32 := 0x01313423.
Lemma F_4b9a4 : fetch_word Ubsan.M.loaded_segments (0x4b9a4 : word) = Some W_4b9a4.
Proof. vm_refl. Qed.
Lemma D_4b9a4 : decode_any W_4b9a4 = Some (Store SZ8 2 19 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_4b9a8 : bv 32 := 0x00060413.
Lemma F_4b9a8 : fetch_word Ubsan.M.loaded_segments (0x4b9a8 : word) = Some W_4b9a8.
Proof. vm_refl. Qed.
Lemma D_4b9a8 : decode_any W_4b9a8 = Some (OpImm ALU_ADD 8 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_4b9ac : bv 32 := 0x00058493.
Lemma F_4b9ac : fetch_word Ubsan.M.loaded_segments (0x4b9ac : word) = Some W_4b9ac.
Proof. vm_refl. Qed.
Lemma D_4b9ac : decode_any W_4b9ac = Some (OpImm ALU_ADD 9 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_4b9b0 : bv 32 := 0x00050913.
Lemma F_4b9b0 : fetch_word Ubsan.M.loaded_segments (0x4b9b0 : word) = Some W_4b9b0.
Proof. vm_refl. Qed.
Lemma D_4b9b0 : decode_any W_4b9b0 = Some (OpImm ALU_ADD 18 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_4b9b4 : bv 32 := 0x00359513.
Lemma F_4b9b4 : fetch_word Ubsan.M.loaded_segments (0x4b9b4 : word) = Some W_4b9b4.
Proof. vm_refl. Qed.
Lemma D_4b9b4 : decode_any W_4b9b4 = Some (ShiftImm ALU_SLL 10 11 3, 4%Z).
Proof. vm_refl. Qed.

Definition W_4b9b8 : bv 32 := 0x00a60533.
Lemma F_4b9b8 : fetch_word Ubsan.M.loaded_segments (0x4b9b8 : word) = Some W_4b9b8.
Proof. vm_refl. Qed.
Lemma D_4b9b8 : decode_any W_4b9b8 = Some (Op ALU_ADD 10 12 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_4b9bc : bv 32 := 0x00850993.
Lemma F_4b9bc : fetch_word Ubsan.M.loaded_segments (0x4b9bc : word) = Some W_4b9bc.
Proof. vm_refl. Qed.
Lemma D_4b9bc : decode_any W_4b9bc = Some (OpImm ALU_ADD 19 10 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_4b9c0 : bv 32 := 0xf25ff0ef.
Lemma F_4b9c0 : fetch_word Ubsan.M.loaded_segments (0x4b9c0 : word) = Some W_4b9c0.
Proof. vm_refl. Qed.
Lemma D_4b9c0 : decode_any W_4b9c0 = Some (Jal 1 2096932, 4%Z).
Proof. vm_refl. Qed.

Definition W_4b9c4 : bv 32 := 0x00048513.
Lemma F_4b9c4 : fetch_word Ubsan.M.loaded_segments (0x4b9c4 : word) = Some W_4b9c4.
Proof. vm_refl. Qed.
Lemma D_4b9c4 : decode_any W_4b9c4 = Some (OpImm ALU_ADD 10 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_4b9c8 : bv 32 := 0x00040593.
Lemma F_4b9c8 : fetch_word Ubsan.M.loaded_segments (0x4b9c8 : word) = Some W_4b9c8.
Proof. vm_refl. Qed.
Lemma D_4b9c8 : decode_any W_4b9c8 = Some (OpImm ALU_ADD 11 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_4b9cc : bv 32 := 0x00098613.
Lemma F_4b9cc : fetch_word Ubsan.M.loaded_segments (0x4b9cc : word) = Some W_4b9cc.
Proof. vm_refl. Qed.
Lemma D_4b9cc : decode_any W_4b9cc = Some (OpImm ALU_ADD 12 19 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_4b9d0 : bv 32 := 0x000900e7.
Lemma F_4b9d0 : fetch_word Ubsan.M.loaded_segments (0x4b9d0 : word) = Some W_4b9d0.
Proof. vm_refl. Qed.
Lemma D_4b9d0 : decode_any W_4b9d0 = Some (Jalr 1 18 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_4b9d8 : bv 32 := 0xfc010113.
Lemma F_4b9d8 : fetch_word Ubsan.M.loaded_segments (0x4b9d8 : word) = Some W_4b9d8.
Proof. vm_refl. Qed.
Lemma D_4b9d8 : decode_any W_4b9d8 = Some (OpImm ALU_ADD 2 2 4032, 4%Z).
Proof. vm_refl. Qed.

Definition W_4b9dc : bv 32 := 0x02113c23.
Lemma F_4b9dc : fetch_word Ubsan.M.loaded_segments (0x4b9dc : word) = Some W_4b9dc.
Proof. vm_refl. Qed.
Lemma D_4b9dc : decode_any W_4b9dc = Some (Store SZ8 2 1 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_4b9e0 : bv 32 := 0x02813823.
Lemma F_4b9e0 : fetch_word Ubsan.M.loaded_segments (0x4b9e0 : word) = Some W_4b9e0.
Proof. vm_refl. Qed.
Lemma D_4b9e0 : decode_any W_4b9e0 = Some (Store SZ8 2 8 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_4b9e4 : bv 32 := 0x02913423.
Lemma F_4b9e4 : fetch_word Ubsan.M.loaded_segments (0x4b9e4 : word) = Some W_4b9e4.
Proof. vm_refl. Qed.
Lemma D_4b9e4 : decode_any W_4b9e4 = Some (Store SZ8 2 9 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_4b9e8 : bv 32 := 0x03213023.
Lemma F_4b9e8 : fetch_word Ubsan.M.loaded_segments (0x4b9e8 : word) = Some W_4b9e8.
Proof. vm_refl. Qed.
Lemma D_4b9e8 : decode_any W_4b9e8 = Some (Store SZ8 2 18 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_4b9ec : bv 32 := 0x01313c23.
Lemma F_4b9ec : fetch_word Ubsan.M.loaded_segments (0x4b9ec : word) = Some W_4b9ec.
Proof. vm_refl. Qed.
Lemma D_4b9ec : decode_any W_4b9ec = Some (Store SZ8 2 19 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_4b9f0 : bv 32 := 0x01413823.
Lemma F_4b9f0 : fetch_word Ubsan.M.loaded_segments (0x4b9f0 : word) = Some W_4b9f0.
Proof. vm_refl. Qed.
Lemma D_4b9f0 : decode_any W_4b9f0 = Some (Store SZ8 2 20 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_4b9f4 : bv 32 := 0x01513423.
Lemma F_4b9f4 : fetch_word Ubsan.M.loaded_segments (0x4b9f4 : word) = Some W_4b9f4.
Proof. vm_refl. Qed.
Lemma D_4b9f4 : decode_any W_4b9f4 = Some (Store SZ8 2 21 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_4b9f8 : bv 32 := 0x02853683.
Lemma F_4b9f8 : fetch_word Ubsan.M.loaded_segments (0x4b9f8 : word) = Some W_4b9f8.
Proof. vm_refl. Qed.
Lemma D_4b9f8 : decode_any W_4b9f8 = Some (Load SZ8 true 13 10 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_4b9fc : bv 32 := 0x00045597.
Lemma F_4b9fc : fetch_word Ubsan.M.loaded_segments (0x4b9fc : word) = Some W_4b9fc.
Proof. vm_refl. Qed.
Lemma D_4b9fc : decode_any W_4b9fc = Some (Auipc 11 69, 4%Z).
Proof. vm_refl. Qed.

Definition W_4ba0c : bv 32 := 0x0c068e63.
Lemma F_4ba0c : fetch_word Ubsan.M.loaded_segments (0x4ba0c : word) = Some W_4ba0c.
Proof. vm_refl. Qed.
Lemma D_4ba0c : decode_any W_4ba0c = Some (Branch BC_EQ 13 0 220, 4%Z).
Proof. vm_refl. Qed.

Definition W_4ba14 : bv 32 := 0x00000893.
Lemma F_4ba14 : fetch_word Ubsan.M.loaded_segments (0x4ba14 : word) = Some W_4ba14.
Proof. vm_refl. Qed.
Lemma D_4ba14 : decode_any W_4ba14 = Some (OpImm ALU_ADD 17 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_4ba18 : bv 32 := 0x00015717.
Lemma F_4ba18 : fetch_word Ubsan.M.loaded_segments (0x4ba18 : word) = Some W_4ba18.
Proof. vm_refl. Qed.
Lemma D_4ba18 : decode_any W_4ba18 = Some (Auipc 14 21, 4%Z).
Proof. vm_refl. Qed.

Definition W_4ba1c : bv 32 := 0x01853783.
Lemma F_4ba1c : fetch_word Ubsan.M.loaded_segments (0x4ba1c : word) = Some W_4ba1c.
Proof. vm_refl. Qed.
Lemma D_4ba1c : decode_any W_4ba1c = Some (Load SZ8 true 15 10 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_4ba20 : bv 32 := 0x02053503.
Lemma F_4ba20 : fetch_word Ubsan.M.loaded_segments (0x4ba20 : word) = Some W_4ba20.
Proof. vm_refl. Qed.
Lemma D_4ba20 : decode_any W_4ba20 = Some (Load SZ8 true 10 10 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_4ba24 : bv 32 := 0x00600813.
Lemma F_4ba24 : fetch_word Ubsan.M.loaded_segments (0x4ba24 : word) = Some W_4ba24.
Proof. vm_refl. Qed.
Lemma D_4ba24 : decode_any W_4ba24 = Some (OpImm ALU_ADD 16 0 6, 4%Z).
Proof. vm_refl. Qed.

Definition W_4ba28 : bv 32 := 0x00013297.
Lemma F_4ba28 : fetch_word Ubsan.M.loaded_segments (0x4ba28 : word) = Some W_4ba28.
Proof. vm_refl. Qed.
Lemma D_4ba28 : decode_any W_4ba28 = Some (Auipc 5 19, 4%Z).
Proof. vm_refl. Qed.

Definition W_4ba2c : bv 32 := 0x94076f03.
Lemma F_4ba2c : fetch_word Ubsan.M.loaded_segments (0x4ba2c : word) = Some W_4ba2c.
Proof. vm_refl. Qed.
Lemma D_4ba2c : decode_any W_4ba2c = Some (Load SZ4 false 30 14 2368, 4%Z).
Proof. vm_refl. Qed.

Definition W_4ba30 : bv 32 := 0x5702b283.
Lemma F_4ba30 : fetch_word Ubsan.M.loaded_segments (0x4ba30 : word) = Some W_4ba30.
Proof. vm_refl. Qed.
Lemma D_4ba30 : decode_any W_4ba30 = Some (Load SZ8 true 5 5 1392, 4%Z).
Proof. vm_refl. Qed.

Definition W_4ba34 : bv 32 := 0x00200313.
Lemma F_4ba34 : fetch_word Ubsan.M.loaded_segments (0x4ba34 : word) = Some W_4ba34.
Proof. vm_refl. Qed.
Lemma D_4ba34 : decode_any W_4ba34 = Some (OpImm ALU_ADD 6 0 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_4ba38 : bv 32 := 0x00700393.
Lemma F_4ba38 : fetch_word Ubsan.M.loaded_segments (0x4ba38 : word) = Some W_4ba38.
Proof. vm_refl. Qed.
Lemma D_4ba38 : decode_any W_4ba38 = Some (OpImm ALU_ADD 7 0 7, 4%Z).
Proof. vm_refl. Qed.

Definition W_4ba3c : bv 32 := 0x6474ee37.
Lemma F_4ba3c : fetch_word Ubsan.M.loaded_segments (0x4ba3c : word) = Some W_4ba3c.
Proof. vm_refl. Qed.
Lemma D_4ba3c : decode_any W_4ba3c = Some (Lui 28 411470, 4%Z).
Proof. vm_refl. Qed.

Definition W_4ba40 : bv 32 := 0x551e0e1b.
Lemma F_4ba40 : fetch_word Ubsan.M.loaded_segments (0x4ba40 : word) = Some W_4ba40.
Proof. vm_refl. Qed.
Lemma D_4ba40 : decode_any W_4ba40 = Some (OpImm32 28 28 1361, 4%Z).
Proof. vm_refl. Qed.

Definition W_4ba44 : bv 32 := 0x00078e93.
Lemma F_4ba44 : fetch_word Ubsan.M.loaded_segments (0x4ba44 : word) = Some W_4ba44.
Proof. vm_refl. Qed.
Lemma D_4ba44 : decode_any W_4ba44 = Some (OpImm ALU_ADD 29 15 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_4ba48 : bv 32 := 0x0180006f.
Lemma F_4ba48 : fetch_word Ubsan.M.loaded_segments (0x4ba48 : word) = Some W_4ba48.
Proof. vm_refl. Qed.
Lemma D_4ba48 : decode_any W_4ba48 = Some (Jal 0 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_4ba54 : bv 32 := 0xfff68693.
Lemma F_4ba54 : fetch_word Ubsan.M.loaded_segments (0x4ba54 : word) = Some W_4ba54.
Proof. vm_refl. Qed.
Lemma D_4ba54 : decode_any W_4ba54 = Some (OpImm ALU_ADD 13 13 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_4ba58 : bv 32 := 0x00ae8eb3.
Lemma F_4ba58 : fetch_word Ubsan.M.loaded_segments (0x4ba58 : word) = Some W_4ba58.
Proof. vm_refl. Qed.
Lemma D_4ba58 : decode_any W_4ba58 = Some (Op ALU_ADD 29 29 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_4ba5c : bv 32 := 0x04068a63.
Lemma F_4ba5c : fetch_word Ubsan.M.loaded_segments (0x4ba5c : word) = Some W_4ba5c.
Proof. vm_refl. Qed.
Lemma D_4ba5c : decode_any W_4ba5c = Some (Branch BC_EQ 13 0 84, 4%Z).
Proof. vm_refl. Qed.

Definition W_4ba60 : bv 32 := 0x000ea403.
Lemma F_4ba60 : fetch_word Ubsan.M.loaded_segments (0x4ba60 : word) = Some W_4ba60.
Proof. vm_refl. Qed.
Lemma D_4ba60 : decode_any W_4ba60 = Some (Load SZ4 true 8 29 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_4ba64 : bv 32 := 0xff0404e3.
Lemma F_4ba64 : fetch_word Ubsan.M.loaded_segments (0x4ba64 : word) = Some W_4ba64.
Proof. vm_refl. Qed.
Lemma D_4ba64 : decode_any W_4ba64 = Some (Branch BC_EQ 8 16 8168, 4%Z).
Proof. vm_refl. Qed.

Definition W_4ba68 : bv 32 := 0x00028a63.
Lemma F_4ba68 : fetch_word Ubsan.M.loaded_segments (0x4ba68 : word) = Some W_4ba68.
Proof. vm_refl. Qed.
Lemma D_4ba68 : decode_any W_4ba68 = Some (Branch BC_EQ 5 0 20, 4%Z).
Proof. vm_refl. Qed.

Definition W_4ba7c : bv 32 := 0x000e8f93.
Lemma F_4ba7c : fetch_word Ubsan.M.loaded_segments (0x4ba7c : word) = Some W_4ba7c.
Proof. vm_refl. Qed.
Lemma D_4ba7c : decode_any W_4ba7c = Some (OpImm ALU_ADD 31 29 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_4ba80 : bv 32 := 0x00740463.
Lemma F_4ba80 : fetch_word Ubsan.M.loaded_segments (0x4ba80 : word) = Some W_4ba80.
Proof. vm_refl. Qed.
Lemma D_4ba80 : decode_any W_4ba80 = Some (Branch BC_EQ 8 7 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_4ba84 : bv 32 := 0x00088f93.
Lemma F_4ba84 : fetch_word Ubsan.M.loaded_segments (0x4ba84 : word) = Some W_4ba84.
Proof. vm_refl. Qed.
Lemma D_4ba84 : decode_any W_4ba84 = Some (OpImm ALU_ADD 31 17 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_4ba88 : bv 32 := 0x03c41063.
Lemma F_4ba88 : fetch_word Ubsan.M.loaded_segments (0x4ba88 : word) = Some W_4ba88.
Proof. vm_refl. Qed.
Lemma D_4ba88 : decode_any W_4ba88 = Some (Branch BC_NE 8 28 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_4ba8c : bv 32 := 0x028eb883.
Lemma F_4ba8c : fetch_word Ubsan.M.loaded_segments (0x4ba8c : word) = Some W_4ba8c.
Proof. vm_refl. Qed.
Lemma D_4ba8c : decode_any W_4ba8c = Some (Load SZ8 true 17 29 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_4ba90 : bv 32 := 0x011f7c63.
Lemma F_4ba90 : fetch_word Ubsan.M.loaded_segments (0x4ba90 : word) = Some W_4ba90.
Proof. vm_refl. Qed.
Lemma D_4ba90 : decode_any W_4ba90 = Some (Branch BC_GEU 30 17 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_4baa8 : bv 32 := 0x000f8893.
Lemma F_4baa8 : fetch_word Ubsan.M.loaded_segments (0x4baa8 : word) = Some W_4baa8.
Proof. vm_refl. Qed.
Lemma D_4baa8 : decode_any W_4baa8 = Some (OpImm ALU_ADD 17 31 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_4baac : bv 32 := 0xfa9ff06f.
Lemma F_4baac : fetch_word Ubsan.M.loaded_segments (0x4baac : word) = Some W_4baac.
Proof. vm_refl. Qed.
Lemma D_4baac : decode_any W_4baac = Some (Jal 0 2097064, 4%Z).
Proof. vm_refl. Qed.

Definition W_4bab0 : bv 32 := 0x02088c63.
Lemma F_4bab0 : fetch_word Ubsan.M.loaded_segments (0x4bab0 : word) = Some W_4bab0.
Proof. vm_refl. Qed.
Lemma D_4bab0 : decode_any W_4bab0 = Some (Branch BC_EQ 17 0 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_4baf8 : bv 32 := 0xfff50793.
Lemma F_4baf8 : fetch_word Ubsan.M.loaded_segments (0x4baf8 : word) = Some W_4baf8.
Proof. vm_refl. Qed.
Lemma D_4baf8 : decode_any W_4baf8 = Some (OpImm ALU_ADD 15 10 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_4bafc : bv 32 := 0x40e00733.
Lemma F_4bafc : fetch_word Ubsan.M.loaded_segments (0x4bafc : word) = Some W_4bafc.
Proof. vm_refl. Qed.
Lemma D_4bafc : decode_any W_4bafc = Some (Op ALU_SUB 14 0 14, 4%Z).
Proof. vm_refl. Qed.

Definition W_4bb04 : bv 32 := 0x00e7f733.
Lemma F_4bb04 : fetch_word Ubsan.M.loaded_segments (0x4bb04 : word) = Some W_4bb04.
Proof. vm_refl. Qed.
Lemma D_4bb04 : decode_any W_4bb04 = Some (Op ALU_AND 14 15 14, 4%Z).
Proof. vm_refl. Qed.

Definition W_4bb08 : bv 32 := 0x00700793.
Lemma F_4bb08 : fetch_word Ubsan.M.loaded_segments (0x4bb08 : word) = Some W_4bb08.
Proof. vm_refl. Qed.
Lemma D_4bb08 : decode_any W_4bb08 = Some (OpImm ALU_ADD 15 0 7, 4%Z).
Proof. vm_refl. Qed.

Definition W_4bb0c : bv 32 := 0x00d706b3.
Lemma F_4bb0c : fetch_word Ubsan.M.loaded_segments (0x4bb0c : word) = Some W_4bb0c.
Proof. vm_refl. Qed.
Lemma D_4bb0c : decode_any W_4bb0c = Some (Op ALU_ADD 13 14 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_4bb18 : bv 32 := 0x00a7e663.
Lemma F_4bb18 : fetch_word Ubsan.M.loaded_segments (0x4bb18 : word) = Some W_4bb18.
Proof. vm_refl. Qed.
Lemma D_4bb18 : decode_any W_4bb18 = Some (Branch BC_LTU 15 10 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_4bb1c : bv 32 := 0x00800513.
Lemma F_4bb1c : fetch_word Ubsan.M.loaded_segments (0x4bb1c : word) = Some W_4bb1c.
Proof. vm_refl. Qed.
Lemma D_4bb1c : decode_any W_4bb1c = Some (OpImm ALU_ADD 10 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_4bb38 : bv 32 := 0xff85f593.
Lemma F_4bb38 : fetch_word Ubsan.M.loaded_segments (0x4bb38 : word) = Some W_4bb38.
Proof. vm_refl. Qed.
Lemma D_4bb38 : decode_any W_4bb38 = Some (OpImm ALU_AND 11 11 4088, 4%Z).
Proof. vm_refl. Qed.

Definition W_4bb3c : bv 32 := 0x00b4bc23.
Lemma F_4bb3c : fetch_word Ubsan.M.loaded_segments (0x4bb3c : word) = Some W_4bb3c.
Proof. vm_refl. Qed.
Lemma D_4bb3c : decode_any W_4bb3c = Some (Store SZ8 9 11 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_4bb40 : bv 32 := 0x02a4b023.
Lemma F_4bb40 : fetch_word Ubsan.M.loaded_segments (0x4bb40 : word) = Some W_4bb40.
Proof. vm_refl. Qed.
Lemma D_4bb40 : decode_any W_4bb40 = Some (Store SZ8 9 10 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_4bb44 : bv 32 := 0x02d5ea63.
Lemma F_4bb44 : fetch_word Ubsan.M.loaded_segments (0x4bb44 : word) = Some W_4bb44.
Proof. vm_refl. Qed.
Lemma D_4bb44 : decode_any W_4bb44 = Some (Branch BC_LTU 11 13 52, 4%Z).
Proof. vm_refl. Qed.

Definition W_4bb80 : bv 32 := 0x0284b603.
Lemma F_4bb80 : fetch_word Ubsan.M.loaded_segments (0x4bb80 : word) = Some W_4bb80.
Proof. vm_refl. Qed.
Lemma D_4bb80 : decode_any W_4bb80 = Some (Load SZ8 true 12 9 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_4bbac : bv 32 := 0x0c890413.
Lemma F_4bbac : fetch_word Ubsan.M.loaded_segments (0x4bbac : word) = Some W_4bbac.
Proof. vm_refl. Qed.
Lemma D_4bbac : decode_any W_4bbac = Some (OpImm ALU_ADD 8 18 200, 4%Z).
Proof. vm_refl. Qed.

Definition W_4bc00 : bv 32 := 0x01293023.
Lemma F_4bc00 : fetch_word Ubsan.M.loaded_segments (0x4bc00 : word) = Some W_4bc00.
Proof. vm_refl. Qed.
Lemma D_4bc00 : decode_any W_4bc00 = Some (Store SZ8 18 18 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_4bc04 : bv 32 := 0x00040513.
Lemma F_4bc04 : fetch_word Ubsan.M.loaded_segments (0x4bc04 : word) = Some W_4bc04.
Proof. vm_refl. Qed.
Lemma D_4bc04 : decode_any W_4bc04 = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_4bc08 : bv 32 := 0x23d0e0ef.
Lemma F_4bc08 : fetch_word Ubsan.M.loaded_segments (0x4bc08 : word) = Some W_4bc08.
Proof. vm_refl. Qed.
Lemma D_4bc08 : decode_any W_4bc08 = Some (Jal 1 59964, 4%Z).
Proof. vm_refl. Qed.

Definition W_4bc0c : bv 32 := 0x04054a63.
Lemma F_4bc0c : fetch_word Ubsan.M.loaded_segments (0x4bc0c : word) = Some W_4bc0c.
Proof. vm_refl. Qed.
Lemma D_4bc0c : decode_any W_4bc0c = Some (Branch BC_LT 10 0 84, 4%Z).
Proof. vm_refl. Qed.

Definition W_4bc10 : bv 32 := 0x00051663.
Lemma F_4bc10 : fetch_word Ubsan.M.loaded_segments (0x4bc10 : word) = Some W_4bc10.
Proof. vm_refl. Qed.
Lemma D_4bc10 : decode_any W_4bc10 = Some (Branch BC_NE 10 0 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_4bc14 : bv 32 := 0x00100513.
Lemma F_4bc14 : fetch_word Ubsan.M.loaded_segments (0x4bc14 : word) = Some W_4bc14.
Proof. vm_refl. Qed.
Lemma D_4bc14 : decode_any W_4bc14 = Some (OpImm ALU_ADD 10 0 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_4bc18 : bv 32 := 0x00a48023.
Lemma F_4bc18 : fetch_word Ubsan.M.loaded_segments (0x4bc18 : word) = Some W_4bc18.
Proof. vm_refl. Qed.
Lemma D_4bc18 : decode_any W_4bc18 = Some (Store SZ1 9 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_4bc1c : bv 32 := 0x00200513.
Lemma F_4bc1c : fetch_word Ubsan.M.loaded_segments (0x4bc1c : word) = Some W_4bc1c.
Proof. vm_refl. Qed.
Lemma D_4bc1c : decode_any W_4bc1c = Some (OpImm ALU_ADD 10 0 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_4bc20 : bv 32 := 0x00045597.
Lemma F_4bc20 : fetch_word Ubsan.M.loaded_segments (0x4bc20 : word) = Some W_4bc20.
Proof. vm_refl. Qed.
Lemma D_4bc20 : decode_any W_4bc20 = Some (Auipc 11 69, 4%Z).
Proof. vm_refl. Qed.

Definition W_4bc24 : bv 32 := 0x02a92423.
Lemma F_4bc24 : fetch_word Ubsan.M.loaded_segments (0x4bc24 : word) = Some W_4bc24.
Proof. vm_refl. Qed.
Lemma D_4bc24 : decode_any W_4bc24 = Some (Store SZ4 18 10 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_4bc28 : bv 32 := 0x06000893.
Lemma F_4bc28 : fetch_word Ubsan.M.loaded_segments (0x4bc28 : word) = Some W_4bc28.
Proof. vm_refl. Qed.
Lemma D_4bc28 : decode_any W_4bc28 = Some (OpImm ALU_ADD 17 0 96, 4%Z).
Proof. vm_refl. Qed.

Definition W_4bc2c : bv 32 := 0x32058513.
Lemma F_4bc2c : fetch_word Ubsan.M.loaded_segments (0x4bc2c : word) = Some W_4bc2c.
Proof. vm_refl. Qed.
Lemma D_4bc2c : decode_any W_4bc2c = Some (OpImm ALU_ADD 10 11 800, 4%Z).
Proof. vm_refl. Qed.

Definition W_4bc30 : bv 32 := 0x03848593.
Lemma F_4bc30 : fetch_word Ubsan.M.loaded_segments (0x4bc30 : word) = Some W_4bc30.
Proof. vm_refl. Qed.
Lemma D_4bc30 : decode_any W_4bc30 = Some (OpImm ALU_ADD 11 9 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_4bc34 : bv 32 := 0x00000073.
Lemma F_4bc34 : fetch_word Ubsan.M.loaded_segments (0x4bc34 : word) = Some W_4bc34.
Proof. vm_refl. Qed.
Lemma D_4bc34 : decode_any W_4bc34 = Some (Ecall, 4%Z).
Proof. vm_refl. Qed.
Lemma E_4bc34 : is_ecall W_4bc34 = true.
Proof. reflexivity. Qed.

Definition W_4bc38 : bv 32 := 0x07890613.
Lemma F_4bc38 : fetch_word Ubsan.M.loaded_segments (0x4bc38 : word) = Some W_4bc38.
Proof. vm_refl. Qed.
Lemma D_4bc38 : decode_any W_4bc38 = Some (OpImm ALU_ADD 12 18 120, 4%Z).
Proof. vm_refl. Qed.

Definition W_4bc3c : bv 32 := 0x02a92023.
Lemma F_4bc3c : fetch_word Ubsan.M.loaded_segments (0x4bc3c : word) = Some W_4bc3c.
Proof. vm_refl. Qed.
Lemma D_4bc3c : decode_any W_4bc3c = Some (Store SZ4 18 10 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_4bc40 : bv 32 := 0x08b93c23.
Lemma F_4bc40 : fetch_word Ubsan.M.loaded_segments (0x4bc40 : word) = Some W_4bc40.
Proof. vm_refl. Qed.
Lemma D_4bc40 : decode_any W_4bc40 = Some (Store SZ8 18 11 152, 4%Z).
Proof. vm_refl. Qed.

Definition W_4bc44 : bv 32 := 0x06c93c23.
Lemma F_4bc44 : fetch_word Ubsan.M.loaded_segments (0x4bc44 : word) = Some W_4bc44.
Proof. vm_refl. Qed.
Lemma D_4bc44 : decode_any W_4bc44 = Some (Store SZ8 18 12 120, 4%Z).
Proof. vm_refl. Qed.

Definition W_4bc48 : bv 32 := 0x00045517.
Lemma F_4bc48 : fetch_word Ubsan.M.loaded_segments (0x4bc48 : word) = Some W_4bc48.
Proof. vm_refl. Qed.
Lemma D_4bc48 : decode_any W_4bc48 = Some (Auipc 10 69, 4%Z).
Proof. vm_refl. Qed.

Definition W_4bc4c : bv 32 := 0x56853503.
Lemma F_4bc4c : fetch_word Ubsan.M.loaded_segments (0x4bc4c : word) = Some W_4bc4c.
Proof. vm_refl. Qed.
Lemma D_4bc4c : decode_any W_4bc4c = Some (Load SZ8 true 10 10 1384, 4%Z).
Proof. vm_refl. Qed.

Definition W_4bc50 : bv 32 := 0x01293423.
Lemma F_4bc50 : fetch_word Ubsan.M.loaded_segments (0x4bc50 : word) = Some W_4bc50.
Proof. vm_refl. Qed.
Lemma D_4bc50 : decode_any W_4bc50 = Some (Store SZ8 18 18 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_4bc54 : bv 32 := 0x01293823.
Lemma F_4bc54 : fetch_word Ubsan.M.loaded_segments (0x4bc54 : word) = Some W_4bc54.
Proof. vm_refl. Qed.
Lemma D_4bc54 : decode_any W_4bc54 = Some (Store SZ8 18 18 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_4bc58 : bv 32 := 0x00a93c23.
Lemma F_4bc58 : fetch_word Ubsan.M.loaded_segments (0x4bc58 : word) = Some W_4bc58.
Proof. vm_refl. Qed.
Lemma D_4bc58 : decode_any W_4bc58 = Some (Store SZ8 18 10 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_4bc5c : bv 32 := 0x0080006f.
Lemma F_4bc5c : fetch_word Ubsan.M.loaded_segments (0x4bc5c : word) = Some W_4bc5c.
Proof. vm_refl. Qed.
Lemma D_4bc5c : decode_any W_4bc5c = Some (Jal 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_4bc64 : bv 32 := 0x03813083.
Lemma F_4bc64 : fetch_word Ubsan.M.loaded_segments (0x4bc64 : word) = Some W_4bc64.
Proof. vm_refl. Qed.
Lemma D_4bc64 : decode_any W_4bc64 = Some (Load SZ8 true 1 2 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_4bc68 : bv 32 := 0x03013403.
Lemma F_4bc68 : fetch_word Ubsan.M.loaded_segments (0x4bc68 : word) = Some W_4bc68.
Proof. vm_refl. Qed.
Lemma D_4bc68 : decode_any W_4bc68 = Some (Load SZ8 true 8 2 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_4bc6c : bv 32 := 0x02813483.
Lemma F_4bc6c : fetch_word Ubsan.M.loaded_segments (0x4bc6c : word) = Some W_4bc6c.
Proof. vm_refl. Qed.
Lemma D_4bc6c : decode_any W_4bc6c = Some (Load SZ8 true 9 2 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_4bc70 : bv 32 := 0x02013903.
Lemma F_4bc70 : fetch_word Ubsan.M.loaded_segments (0x4bc70 : word) = Some W_4bc70.
Proof. vm_refl. Qed.
Lemma D_4bc70 : decode_any W_4bc70 = Some (Load SZ8 true 18 2 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_4bc74 : bv 32 := 0x01813983.
Lemma F_4bc74 : fetch_word Ubsan.M.loaded_segments (0x4bc74 : word) = Some W_4bc74.
Proof. vm_refl. Qed.
Lemma D_4bc74 : decode_any W_4bc74 = Some (Load SZ8 true 19 2 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_4bc78 : bv 32 := 0x01013a03.
Lemma F_4bc78 : fetch_word Ubsan.M.loaded_segments (0x4bc78 : word) = Some W_4bc78.
Proof. vm_refl. Qed.
Lemma D_4bc78 : decode_any W_4bc78 = Some (Load SZ8 true 20 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_4bc7c : bv 32 := 0x00813a83.
Lemma F_4bc7c : fetch_word Ubsan.M.loaded_segments (0x4bc7c : word) = Some W_4bc7c.
Proof. vm_refl. Qed.
Lemma D_4bc7c : decode_any W_4bc7c = Some (Load SZ8 true 21 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_4bc80 : bv 32 := 0x04010113.
Lemma F_4bc80 : fetch_word Ubsan.M.loaded_segments (0x4bc80 : word) = Some W_4bc80.
Proof. vm_refl. Qed.
Lemma D_4bc80 : decode_any W_4bc80 = Some (OpImm ALU_ADD 2 2 64, 4%Z).
Proof. vm_refl. Qed.

Definition W_4bc84 : bv 32 := 0x00008067.
Lemma F_4bc84 : fetch_word Ubsan.M.loaded_segments (0x4bc84 : word) = Some W_4bc84.
Proof. vm_refl. Qed.
Lemma D_4bc84 : decode_any W_4bc84 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_4bd28 : bv 32 := 0x00050593.
Lemma F_4bd28 : fetch_word Ubsan.M.loaded_segments (0x4bd28 : word) = Some W_4bd28.
Proof. vm_refl. Qed.
Lemma D_4bd28 : decode_any W_4bd28 = Some (OpImm ALU_ADD 11 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_4bd2c : bv 32 := 0x05e00893.
Lemma F_4bd2c : fetch_word Ubsan.M.loaded_segments (0x4bd2c : word) = Some W_4bd2c.
Proof. vm_refl. Qed.
Lemma D_4bd2c : decode_any W_4bd2c = Some (OpImm ALU_ADD 17 0 94, 4%Z).
Proof. vm_refl. Qed.

Definition W_4bd30 : bv 32 := 0x00000073.
Lemma F_4bd30 : fetch_word Ubsan.M.loaded_segments (0x4bd30 : word) = Some W_4bd30.
Proof. vm_refl. Qed.
Lemma D_4bd30 : decode_any W_4bd30 = Some (Ecall, 4%Z).
Proof. vm_refl. Qed.
Lemma E_4bd30 : is_ecall W_4bd30 = true.
Proof. reflexivity. Qed.

Definition W_4bf08 : bv 32 := 0x00008067.
Lemma F_4bf08 : fetch_word Ubsan.M.loaded_segments (0x4bf08 : word) = Some W_4bf08.
Proof. vm_refl. Qed.
Lemma D_4bf08 : decode_any W_4bf08 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_4bf0c : bv 32 := 0xfe010113.
Lemma F_4bf0c : fetch_word Ubsan.M.loaded_segments (0x4bf0c : word) = Some W_4bf0c.
Proof. vm_refl. Qed.
Lemma D_4bf0c : decode_any W_4bf0c = Some (OpImm ALU_ADD 2 2 4064, 4%Z).
Proof. vm_refl. Qed.

Definition W_4bf10 : bv 32 := 0x00113c23.
Lemma F_4bf10 : fetch_word Ubsan.M.loaded_segments (0x4bf10 : word) = Some W_4bf10.
Proof. vm_refl. Qed.
Lemma D_4bf10 : decode_any W_4bf10 = Some (Store SZ8 2 1 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_4bf14 : bv 32 := 0x00813823.
Lemma F_4bf14 : fetch_word Ubsan.M.loaded_segments (0x4bf14 : word) = Some W_4bf14.
Proof. vm_refl. Qed.
Lemma D_4bf14 : decode_any W_4bf14 = Some (Store SZ8 2 8 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_4bf18 : bv 32 := 0x00913423.
Lemma F_4bf18 : fetch_word Ubsan.M.loaded_segments (0x4bf18 : word) = Some W_4bf18.
Proof. vm_refl. Qed.
Lemma D_4bf18 : decode_any W_4bf18 = Some (Store SZ8 2 9 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_4bf1c : bv 32 := 0x00013517.
Lemma F_4bf1c : fetch_word Ubsan.M.loaded_segments (0x4bf1c : word) = Some W_4bf1c.
Proof. vm_refl. Qed.
Lemma D_4bf1c : decode_any W_4bf1c = Some (Auipc 10 19, 4%Z).
Proof. vm_refl. Qed.

Definition W_4bf20 : bv 32 := 0x00013597.
Lemma F_4bf20 : fetch_word Ubsan.M.loaded_segments (0x4bf20 : word) = Some W_4bf20.
Proof. vm_refl. Qed.
Lemma D_4bf20 : decode_any W_4bf20 = Some (Auipc 11 19, 4%Z).
Proof. vm_refl. Qed.

Definition W_4bf24 : bv 32 := 0x1d453503.
Lemma F_4bf24 : fetch_word Ubsan.M.loaded_segments (0x4bf24 : word) = Some W_4bf24.
Proof. vm_refl. Qed.
Lemma D_4bf24 : decode_any W_4bf24 = Some (Load SZ8 true 10 10 468, 4%Z).
Proof. vm_refl. Qed.

Definition W_4bf28 : bv 32 := 0x1d85b403.
Lemma F_4bf28 : fetch_word Ubsan.M.loaded_segments (0x4bf28 : word) = Some W_4bf28.
Proof. vm_refl. Qed.
Lemma D_4bf28 : decode_any W_4bf28 = Some (Load SZ8 true 8 11 472, 4%Z).
Proof. vm_refl. Qed.

Definition W_4bf2c : bv 32 := 0x00a47c63.
Lemma F_4bf2c : fetch_word Ubsan.M.loaded_segments (0x4bf2c : word) = Some W_4bf2c.
Proof. vm_refl. Qed.
Lemma D_4bf2c : decode_any W_4bf2c = Some (Branch BC_GEU 8 10 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_4bf30 : bv 32 := 0xff853583.
Lemma F_4bf30 : fetch_word Ubsan.M.loaded_segments (0x4bf30 : word) = Some W_4bf30.
Proof. vm_refl. Qed.
Lemma D_4bf30 : decode_any W_4bf30 = Some (Load SZ8 true 11 10 4088, 4%Z).
Proof. vm_refl. Qed.

Definition W_4bf34 : bv 32 := 0xff850493.
Lemma F_4bf34 : fetch_word Ubsan.M.loaded_segments (0x4bf34 : word) = Some W_4bf34.
Proof. vm_refl. Qed.
Lemma D_4bf34 : decode_any W_4bf34 = Some (OpImm ALU_ADD 9 10 4088, 4%Z).
Proof. vm_refl. Qed.

Definition W_4bf38 : bv 32 := 0x000580e7.
Lemma F_4bf38 : fetch_word Ubsan.M.loaded_segments (0x4bf38 : word) = Some W_4bf38.
Proof. vm_refl. Qed.
Lemma D_4bf38 : decode_any W_4bf38 = Some (Jalr 1 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_4bf3c : bv 32 := 0x00048513.
Lemma F_4bf3c : fetch_word Ubsan.M.loaded_segments (0x4bf3c : word) = Some W_4bf3c.
Proof. vm_refl. Qed.
Lemma D_4bf3c : decode_any W_4bf3c = Some (OpImm ALU_ADD 10 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_4bf40 : bv 32 := 0xfe9468e3.
Lemma F_4bf40 : fetch_word Ubsan.M.loaded_segments (0x4bf40 : word) = Some W_4bf40.
Proof. vm_refl. Qed.
Lemma D_4bf40 : decode_any W_4bf40 = Some (Branch BC_LTU 8 9 8176, 4%Z).
Proof. vm_refl. Qed.

Definition W_4bf44 : bv 32 := 0x01813083.
Lemma F_4bf44 : fetch_word Ubsan.M.loaded_segments (0x4bf44 : word) = Some W_4bf44.
Proof. vm_refl. Qed.
Lemma D_4bf44 : decode_any W_4bf44 = Some (Load SZ8 true 1 2 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_4bf48 : bv 32 := 0x01013403.
Lemma F_4bf48 : fetch_word Ubsan.M.loaded_segments (0x4bf48 : word) = Some W_4bf48.
Proof. vm_refl. Qed.
Lemma D_4bf48 : decode_any W_4bf48 = Some (Load SZ8 true 8 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_4bf4c : bv 32 := 0x00813483.
Lemma F_4bf4c : fetch_word Ubsan.M.loaded_segments (0x4bf4c : word) = Some W_4bf4c.
Proof. vm_refl. Qed.
Lemma D_4bf4c : decode_any W_4bf4c = Some (Load SZ8 true 9 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_4bf50 : bv 32 := 0x02010113.
Lemma F_4bf50 : fetch_word Ubsan.M.loaded_segments (0x4bf50 : word) = Some W_4bf50.
Proof. vm_refl. Qed.
Lemma D_4bf50 : decode_any W_4bf50 = Some (OpImm ALU_ADD 2 2 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_4bf54 : bv 32 := 0xfb5ff06f.
Lemma F_4bf54 : fetch_word Ubsan.M.loaded_segments (0x4bf54 : word) = Some W_4bf54.
Proof. vm_refl. Qed.
Lemma D_4bf54 : decode_any W_4bf54 = Some (Jal 0 2097076, 4%Z).
Proof. vm_refl. Qed.

Definition W_4bf58 : bv 32 := 0xff010113.
Lemma F_4bf58 : fetch_word Ubsan.M.loaded_segments (0x4bf58 : word) = Some W_4bf58.
Proof. vm_refl. Qed.
Lemma D_4bf58 : decode_any W_4bf58 = Some (OpImm ALU_ADD 2 2 4080, 4%Z).
Proof. vm_refl. Qed.

Definition W_4bf5c : bv 32 := 0x00113423.
Lemma F_4bf5c : fetch_word Ubsan.M.loaded_segments (0x4bf5c : word) = Some W_4bf5c.
Proof. vm_refl. Qed.
Lemma D_4bf5c : decode_any W_4bf5c = Some (Store SZ8 2 1 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_4bf60 : bv 32 := 0x00813023.
Lemma F_4bf60 : fetch_word Ubsan.M.loaded_segments (0x4bf60 : word) = Some W_4bf60.
Proof. vm_refl. Qed.
Lemma D_4bf60 : decode_any W_4bf60 = Some (Store SZ8 2 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_4bf64 : bv 32 := 0x00000593.
Lemma F_4bf64 : fetch_word Ubsan.M.loaded_segments (0x4bf64 : word) = Some W_4bf64.
Proof. vm_refl. Qed.
Lemma D_4bf64 : decode_any W_4bf64 = Some (OpImm ALU_ADD 11 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_4bf68 : bv 32 := 0x00020613.
Lemma F_4bf68 : fetch_word Ubsan.M.loaded_segments (0x4bf68 : word) = Some W_4bf68.
Proof. vm_refl. Qed.
Lemma D_4bf68 : decode_any W_4bf68 = Some (OpImm ALU_ADD 12 4 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_4bf6c : bv 32 := 0xf5862603.
Lemma F_4bf6c : fetch_word Ubsan.M.loaded_segments (0x4bf6c : word) = Some W_4bf6c.
Proof. vm_refl. Qed.
Lemma D_4bf6c : decode_any W_4bf6c = Some (Load SZ4 true 12 12 3928, 4%Z).
Proof. vm_refl. Qed.

Definition W_4bf70 : bv 32 := 0x00045697.
Lemma F_4bf70 : fetch_word Ubsan.M.loaded_segments (0x4bf70 : word) = Some W_4bf70.
Proof. vm_refl. Qed.
Lemma D_4bf70 : decode_any W_4bf70 = Some (Auipc 13 69, 4%Z).
Proof. vm_refl. Qed.

Definition W_4bf74 : bv 32 := 0x23068693.
Lemma F_4bf74 : fetch_word Ubsan.M.loaded_segments (0x4bf74 : word) = Some W_4bf74.
Proof. vm_refl. Qed.
Lemma D_4bf74 : decode_any W_4bf74 = Some (OpImm ALU_ADD 13 13 560, 4%Z).
Proof. vm_refl. Qed.

Definition W_4bf78 : bv 32 := 0x1606a72f.
Lemma F_4bf78 : fetch_word Ubsan.M.loaded_segments (0x4bf78 : word) = Some W_4bf78.
Proof. vm_refl. Qed.
Lemma D_4bf78 : decode_any W_4bf78 = Some (Lr AW true true 14 13, 4%Z).
Proof. vm_refl. Qed.

Definition W_4bf7c : bv 32 := 0x00b71663.
Lemma F_4bf7c : fetch_word Ubsan.M.loaded_segments (0x4bf7c : word) = Some W_4bf7c.
Proof. vm_refl. Qed.
Lemma D_4bf7c : decode_any W_4bf7c = Some (Branch BC_NE 14 11 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_4bf80 : bv 32 := 0x1ec6a7af.
Lemma F_4bf80 : fetch_word Ubsan.M.loaded_segments (0x4bf80 : word) = Some W_4bf80.
Proof. vm_refl. Qed.
Lemma D_4bf80 : decode_any W_4bf80 = Some (Sc AW true true 15 13 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_4bf84 : bv 32 := 0xfe079ae3.
Lemma F_4bf84 : fetch_word Ubsan.M.loaded_segments (0x4bf84 : word) = Some W_4bf84.
Proof. vm_refl. Qed.
Lemma D_4bf84 : decode_any W_4bf84 = Some (Branch BC_NE 15 0 8180, 4%Z).
Proof. vm_refl. Qed.

Definition W_4bf88 : bv 32 := 0x0007059b.
Lemma F_4bf88 : fetch_word Ubsan.M.loaded_segments (0x4bf88 : word) = Some W_4bf88.
Proof. vm_refl. Qed.
Lemma D_4bf88 : decode_any W_4bf88 = Some (OpImm32 11 14 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_4bf8c : bv 32 := 0x02c58263.
Lemma F_4bf8c : fetch_word Ubsan.M.loaded_segments (0x4bf8c : word) = Some W_4bf8c.
Proof. vm_refl. Qed.
Lemma D_4bf8c : decode_any W_4bf8c = Some (Branch BC_EQ 11 12 36, 4%Z).
Proof. vm_refl. Qed.

Definition W_4bf90 : bv 32 := 0x02058263.
Lemma F_4bf90 : fetch_word Ubsan.M.loaded_segments (0x4bf90 : word) = Some W_4bf90.
Proof. vm_refl. Qed.
Lemma D_4bf90 : decode_any W_4bf90 = Some (Branch BC_EQ 11 0 36, 4%Z).
Proof. vm_refl. Qed.

Definition W_4bfb4 : bv 32 := 0x00050413.
Lemma F_4bfb4 : fetch_word Ubsan.M.loaded_segments (0x4bfb4 : word) = Some W_4bfb4.
Proof. vm_refl. Qed.
Lemma D_4bfb4 : decode_any W_4bfb4 = Some (OpImm ALU_ADD 8 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_4bfb8 : bv 32 := 0xdbdff0ef.
Lemma F_4bfb8 : fetch_word Ubsan.M.loaded_segments (0x4bfb8 : word) = Some W_4bfb8.
Proof. vm_refl. Qed.
Lemma D_4bfb8 : decode_any W_4bfb8 = Some (Jal 1 2096572, 4%Z).
Proof. vm_refl. Qed.

Definition W_4bfbc : bv 32 := 0xf51ff0ef.
Lemma F_4bfbc : fetch_word Ubsan.M.loaded_segments (0x4bfbc : word) = Some W_4bfbc.
Proof. vm_refl. Qed.
Lemma D_4bfbc : decode_any W_4bfbc = Some (Jal 1 2096976, 4%Z).
Proof. vm_refl. Qed.

Definition W_4bfc0 : bv 32 := 0x561020ef.
Lemma F_4bfc0 : fetch_word Ubsan.M.loaded_segments (0x4bfc0 : word) = Some W_4bfc0.
Proof. vm_refl. Qed.
Lemma D_4bfc0 : decode_any W_4bfc0 = Some (Jal 1 11616, 4%Z).
Proof. vm_refl. Qed.

Definition W_4bfc4 : bv 32 := 0x00040513.
Lemma F_4bfc4 : fetch_word Ubsan.M.loaded_segments (0x4bfc4 : word) = Some W_4bfc4.
Proof. vm_refl. Qed.
Lemma D_4bfc4 : decode_any W_4bfc4 = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_4bfc8 : bv 32 := 0xd61ff0ef.
Lemma F_4bfc8 : fetch_word Ubsan.M.loaded_segments (0x4bfc8 : word) = Some W_4bfc8.
Proof. vm_refl. Qed.
Lemma D_4bfc8 : decode_any W_4bfc8 = Some (Jal 1 2096480, 4%Z).
Proof. vm_refl. Qed.

Definition W_4c0b0 : bv 32 := 0xff010113.
Lemma F_4c0b0 : fetch_word Ubsan.M.loaded_segments (0x4c0b0 : word) = Some W_4c0b0.
Proof. vm_refl. Qed.
Lemma D_4c0b0 : decode_any W_4c0b0 = Some (OpImm ALU_ADD 2 2 4080, 4%Z).
Proof. vm_refl. Qed.

Definition W_4c0b4 : bv 32 := 0x00113423.
Lemma F_4c0b4 : fetch_word Ubsan.M.loaded_segments (0x4c0b4 : word) = Some W_4c0b4.
Proof. vm_refl. Qed.
Lemma D_4c0b4 : decode_any W_4c0b4 = Some (Store SZ8 2 1 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_4c0b8 : bv 32 := 0x00050e63.
Lemma F_4c0b8 : fetch_word Ubsan.M.loaded_segments (0x4c0b8 : word) = Some W_4c0b8.
Proof. vm_refl. Qed.
Lemma D_4c0b8 : decode_any W_4c0b8 = Some (Branch BC_EQ 10 0 28, 4%Z).
Proof. vm_refl. Qed.

Definition W_4c0bc : bv 32 := 0x00050593.
Lemma F_4c0bc : fetch_word Ubsan.M.loaded_segments (0x4c0bc : word) = Some W_4c0bc.
Proof. vm_refl. Qed.
Lemma D_4c0bc : decode_any W_4c0bc = Some (OpImm ALU_ADD 11 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_4c0c0 : bv 32 := 0x00013517.
Lemma F_4c0c0 : fetch_word Ubsan.M.loaded_segments (0x4c0c0 : word) = Some W_4c0c0.
Proof. vm_refl. Qed.
Lemma D_4c0c0 : decode_any W_4c0c0 = Some (Auipc 10 19, 4%Z).
Proof. vm_refl. Qed.

Definition W_4c0c4 : bv 32 := 0x02853503.
Lemma F_4c0c4 : fetch_word Ubsan.M.loaded_segments (0x4c0c4 : word) = Some W_4c0c4.
Proof. vm_refl. Qed.
Lemma D_4c0c4 : decode_any W_4c0c4 = Some (Load SZ8 true 10 10 40, 4%Z).
Proof. vm_refl. Qed.

Definition W_4c0c8 : bv 32 := 0x00800613.
Lemma F_4c0c8 : fetch_word Ubsan.M.loaded_segments (0x4c0c8 : word) = Some W_4c0c8.
Proof. vm_refl. Qed.
Lemma D_4c0c8 : decode_any W_4c0c8 = Some (OpImm ALU_ADD 12 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_4c0cc : bv 32 := 0x3540d0ef.
Lemma F_4c0cc : fetch_word Ubsan.M.loaded_segments (0x4c0cc : word) = Some W_4c0cc.
Proof. vm_refl. Qed.
Lemma D_4c0cc : decode_any W_4c0cc = Some (Jal 1 54100, 4%Z).
Proof. vm_refl. Qed.

Definition W_4c0d0 : bv 32 := 0x01c0006f.
Lemma F_4c0d0 : fetch_word Ubsan.M.loaded_segments (0x4c0d0 : word) = Some W_4c0d0.
Proof. vm_refl. Qed.
Lemma D_4c0d0 : decode_any W_4c0d0 = Some (Jal 0 28, 4%Z).
Proof. vm_refl. Qed.

Definition W_4c0ec : bv 32 := 0x00013517.
Lemma F_4c0ec : fetch_word Ubsan.M.loaded_segments (0x4c0ec : word) = Some W_4c0ec.
Proof. vm_refl. Qed.
Lemma D_4c0ec : decode_any W_4c0ec = Some (Auipc 10 19, 4%Z).
Proof. vm_refl. Qed.

Definition W_4c0f0 : bv 32 := 0xffc53503.
Lemma F_4c0f0 : fetch_word Ubsan.M.loaded_segments (0x4c0f0 : word) = Some W_4c0f0.
Proof. vm_refl. Qed.
Lemma D_4c0f0 : decode_any W_4c0f0 = Some (Load SZ8 true 10 10 4092, 4%Z).
Proof. vm_refl. Qed.

Definition W_4c0f4 : bv 32 := 0x000500a3.
Lemma F_4c0f4 : fetch_word Ubsan.M.loaded_segments (0x4c0f4 : word) = Some W_4c0f4.
Proof. vm_refl. Qed.
Lemma D_4c0f4 : decode_any W_4c0f4 = Some (Store SZ1 10 0 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_4c0f8 : bv 32 := 0x00053503.
Lemma F_4c0f8 : fetch_word Ubsan.M.loaded_segments (0x4c0f8 : word) = Some W_4c0f8.
Proof. vm_refl. Qed.
Lemma D_4c0f8 : decode_any W_4c0f8 = Some (Load SZ8 true 10 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_4c0fc : bv 32 := 0x00020593.
Lemma F_4c0fc : fetch_word Ubsan.M.loaded_segments (0x4c0fc : word) = Some W_4c0fc.
Proof. vm_refl. Qed.
Lemma D_4c0fc : decode_any W_4c0fc = Some (OpImm ALU_ADD 11 4 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_4c100 : bv 32 := 0xfea5b823.
Lemma F_4c100 : fetch_word Ubsan.M.loaded_segments (0x4c100 : word) = Some W_4c100.
Proof. vm_refl. Qed.
Lemma D_4c100 : decode_any W_4c100 = Some (Store SZ8 11 10 4080, 4%Z).
Proof. vm_refl. Qed.

Definition W_4c104 : bv 32 := 0x00813083.
Lemma F_4c104 : fetch_word Ubsan.M.loaded_segments (0x4c104 : word) = Some W_4c104.
Proof. vm_refl. Qed.
Lemma D_4c104 : decode_any W_4c104 = Some (Load SZ8 true 1 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_4c108 : bv 32 := 0x01010113.
Lemma F_4c108 : fetch_word Ubsan.M.loaded_segments (0x4c108 : word) = Some W_4c108.
Proof. vm_refl. Qed.
Lemma D_4c108 : decode_any W_4c108 = Some (OpImm ALU_ADD 2 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_4c10c : bv 32 := 0x00008067.
Lemma F_4c10c : fetch_word Ubsan.M.loaded_segments (0x4c10c : word) = Some W_4c10c.
Proof. vm_refl. Qed.
Lemma D_4c10c : decode_any W_4c10c = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_4c118 : bv 32 := 0xfffff5b7.
Lemma F_4c118 : fetch_word Ubsan.M.loaded_segments (0x4c118 : word) = Some W_4c118.
Proof. vm_refl. Qed.
Lemma D_4c118 : decode_any W_4c118 = Some (Lui 11 1048575, 4%Z).
Proof. vm_refl. Qed.

Definition W_4c11c : bv 32 := 0x0015859b.
Lemma F_4c11c : fetch_word Ubsan.M.loaded_segments (0x4c11c : word) = Some W_4c11c.
Proof. vm_refl. Qed.
Lemma D_4c11c : decode_any W_4c11c = Some (OpImm32 11 11 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_4c120 : bv 32 := 0x02b56663.
Lemma F_4c120 : fetch_word Ubsan.M.loaded_segments (0x4c120 : word) = Some W_4c120.
Proof. vm_refl. Qed.
Lemma D_4c120 : decode_any W_4c120 = Some (Branch BC_LTU 10 11 44, 4%Z).
Proof. vm_refl. Qed.

Definition W_4c14c : bv 32 := 0x00008067.
Lemma F_4c14c : fetch_word Ubsan.M.loaded_segments (0x4c14c : word) = Some W_4c14c.
Proof. vm_refl. Qed.
Lemma D_4c14c : decode_any W_4c14c = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.
