(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
(* [comment removed for export] *)

From OSSVerify.Proofs.leptonica.edge_fuzzer.lib.H Require GcFlushS9.   (* [comment removed for export] *)
From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.leptonica.edge_fuzzer.images Require Import Plain.
Open Scope bv_scope.
#[local] Hint Extern 0 (BvWf _ _) => (lazymatch goal with |- BvWf ?n ?v => is_closed_term n; is_closed_term v end; exact I) : typeclass_instances.   (* [comment removed for export] *)

(* [comment removed for export] *)
Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

(* [comment removed for export] *)
Definition W_5c7a0 : bv 32 := 0xffff3517.
Lemma F_5c7a0 : fetch_word Plain.M.loaded_segments (0x5c7f8 : word) = Some W_5c7a0.
Proof. vm_refl. Qed.
Lemma D_5c7a0 : decode_any W_5c7a0 = Some (Auipc 10 1048563, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5c7a4 : bv 32 := 0x68050513.
Lemma F_5c7a4 : fetch_word Plain.M.loaded_segments (0x5c7fc : word) = Some W_5c7a4.
Proof. vm_refl. Qed.
Lemma D_5c7a4 : decode_any W_5c7a4 = Some (OpImm ALU_ADD 10 10 1664, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5c7a8 : bv 32 := 0x00093597.
Lemma F_5c7a8 : fetch_word Plain.M.loaded_segments (0x5c800 : word) = Some W_5c7a8.
Proof. vm_refl. Qed.
Lemma D_5c7a8 : decode_any W_5c7a8 = Some (Auipc 11 147, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5c7ac : bv 32 := 0x1a858593.
Lemma F_5c7ac : fetch_word Plain.M.loaded_segments (0x5c804 : word) = Some W_5c7ac.
Proof. vm_refl. Qed.
Lemma D_5c7ac : decode_any W_5c7ac = Some (OpImm ALU_ADD 11 11 424, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5c7b0 : bv 32 := 0x000000ef.
Lemma F_5c7b0 : fetch_word Plain.M.loaded_segments (0x5c808 : word) = Some W_5c7b0.
Proof. vm_refl. Qed.
Lemma D_5c7b0 : decode_any W_5c7b0 = Some (Jal 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5c7b4 : bv 32 := 0x0040006f.
Lemma F_5c7b4 : fetch_word Plain.M.loaded_segments (0x5c80c : word) = Some W_5c7b4.
Proof. vm_refl. Qed.
Lemma D_5c7b4 : decode_any W_5c7b4 = Some (Jal 0 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5c7b8 : bv 32 := 0x00813083.
Lemma F_5c7b8 : fetch_word Plain.M.loaded_segments (0x5c810 : word) = Some W_5c7b8.
Proof. vm_refl. Qed.
Lemma D_5c7b8 : decode_any W_5c7b8 = Some (Load SZ8 true 1 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5c7bc : bv 32 := 0x00013403.
Lemma F_5c7bc : fetch_word Plain.M.loaded_segments (0x5c814 : word) = Some W_5c7bc.
Proof. vm_refl. Qed.
Lemma D_5c7bc : decode_any W_5c7bc = Some (Load SZ8 true 8 2 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5c7c0 : bv 32 := 0x01010113.
Lemma F_5c7c0 : fetch_word Plain.M.loaded_segments (0x5c818 : word) = Some W_5c7c0.
Proof. vm_refl. Qed.
Lemma D_5c7c0 : decode_any W_5c7c0 = Some (OpImm ALU_ADD 2 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5c7c4 : bv 32 := 0x00008067.
Lemma F_5c7c4 : fetch_word Plain.M.loaded_segments (0x5c81c : word) = Some W_5c7c4.
Proof. vm_refl. Qed.
Lemma D_5c7c4 : decode_any W_5c7c4 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5c7c8 : bv 32 := 0xff010113.
Lemma F_5c7c8 : fetch_word Plain.M.loaded_segments (0x5c820 : word) = Some W_5c7c8.
Proof. vm_refl. Qed.
Lemma D_5c7c8 : decode_any W_5c7c8 = Some (OpImm ALU_ADD 2 2 4080, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5c7cc : bv 32 := 0x00113423.
Lemma F_5c7cc : fetch_word Plain.M.loaded_segments (0x5c824 : word) = Some W_5c7cc.
Proof. vm_refl. Qed.
Lemma D_5c7cc : decode_any W_5c7cc = Some (Store SZ8 2 1 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5c7d0 : bv 32 := 0x00813023.
Lemma F_5c7d0 : fetch_word Plain.M.loaded_segments (0x5c828 : word) = Some W_5c7d0.
Proof. vm_refl. Qed.
Lemma D_5c7d0 : decode_any W_5c7d0 = Some (Store SZ8 2 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5c7d4 : bv 32 := 0x01010413.
Lemma F_5c7d4 : fetch_word Plain.M.loaded_segments (0x5c82c : word) = Some W_5c7d4.
Proof. vm_refl. Qed.
Lemma D_5c7d4 : decode_any W_5c7d4 = Some (OpImm ALU_ADD 8 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5c7d8 : bv 32 := 0x00093517.
Lemma F_5c7d8 : fetch_word Plain.M.loaded_segments (0x5c830 : word) = Some W_5c7d8.
Proof. vm_refl. Qed.
Lemma D_5c7d8 : decode_any W_5c7d8 = Some (Auipc 10 147, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5c7dc : bv 32 := 0x1b850513.
Lemma F_5c7dc : fetch_word Plain.M.loaded_segments (0x5c834 : word) = Some W_5c7dc.
Proof. vm_refl. Qed.
Lemma D_5c7dc : decode_any W_5c7dc = Some (OpImm ALU_ADD 10 10 440, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5c7e0 : bv 32 := 0x00054503.
Lemma F_5c7e0 : fetch_word Plain.M.loaded_segments (0x5c838 : word) = Some W_5c7e0.
Proof. vm_refl. Qed.
Lemma D_5c7e0 : decode_any W_5c7e0 = Some (Load SZ1 false 10 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5c7e4 : bv 32 := 0x00157513.
Lemma F_5c7e4 : fetch_word Plain.M.loaded_segments (0x5c83c : word) = Some W_5c7e4.
Proof. vm_refl. Qed.
Lemma D_5c7e4 : decode_any W_5c7e4 = Some (OpImm ALU_AND 10 10 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5c7e8 : bv 32 := 0x00050663.
Lemma F_5c7e8 : fetch_word Plain.M.loaded_segments (0x5c840 : word) = Some W_5c7e8.
Proof. vm_refl. Qed.
Lemma D_5c7e8 : decode_any W_5c7e8 = Some (Branch BC_EQ 10 0 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5c7ec : bv 32 := 0x0040006f.
Lemma F_5c7ec : fetch_word Plain.M.loaded_segments (0x5c844 : word) = Some W_5c7ec.
Proof. vm_refl. Qed.
Lemma D_5c7ec : decode_any W_5c7ec = Some (Jal 0 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5c7f0 : bv 32 := 0x0580006f.
Lemma F_5c7f0 : fetch_word Plain.M.loaded_segments (0x5c848 : word) = Some W_5c7f0.
Proof. vm_refl. Qed.
Lemma D_5c7f0 : decode_any W_5c7f0 = Some (Jal 0 88, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5c7f4 : bv 32 := 0x00093517.
Lemma F_5c7f4 : fetch_word Plain.M.loaded_segments (0x5c84c : word) = Some W_5c7f4.
Proof. vm_refl. Qed.
Lemma D_5c7f4 : decode_any W_5c7f4 = Some (Auipc 10 147, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5c7f8 : bv 32 := 0x19c50593.
Lemma F_5c7f8 : fetch_word Plain.M.loaded_segments (0x5c850 : word) = Some W_5c7f8.
Proof. vm_refl. Qed.
Lemma D_5c7f8 : decode_any W_5c7f8 = Some (OpImm ALU_ADD 11 10 412, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5c7fc : bv 32 := 0x00100513.
Lemma F_5c7fc : fetch_word Plain.M.loaded_segments (0x5c854 : word) = Some W_5c7fc.
Proof. vm_refl. Qed.
Lemma D_5c7fc : decode_any W_5c7fc = Some (OpImm ALU_ADD 10 0 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5c800 : bv 32 := 0x00a58023.
Lemma F_5c800 : fetch_word Plain.M.loaded_segments (0x5c858 : word) = Some W_5c800.
Proof. vm_refl. Qed.
Lemma D_5c800 : decode_any W_5c800 = Some (Store SZ1 11 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5c804 : bv 32 := 0x00092517.
Lemma F_5c804 : fetch_word Plain.M.loaded_segments (0x5c85c : word) = Some W_5c804.
Proof. vm_refl. Qed.
Lemma D_5c804 : decode_any W_5c804 = Some (Auipc 10 146, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5c808 : bv 32 := 0xce453503.
Lemma F_5c808 : fetch_word Plain.M.loaded_segments (0x5c860 : word) = Some W_5c808.
Proof. vm_refl. Qed.
Lemma D_5c808 : decode_any W_5c808 = Some (Load SZ8 true 10 10 3300, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5c80c : bv 32 := 0x00050e63.
Lemma F_5c80c : fetch_word Plain.M.loaded_segments (0x5c864 : word) = Some W_5c80c.
Proof. vm_refl. Qed.
Lemma D_5c80c : decode_any W_5c80c = Some (Branch BC_EQ 10 0 28, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5c810 : bv 32 := 0x0040006f.
Lemma F_5c810 : fetch_word Plain.M.loaded_segments (0x5c868 : word) = Some W_5c810.
Proof. vm_refl. Qed.
Lemma D_5c810 : decode_any W_5c810 = Some (Jal 0 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5c814 : bv 32 := 0x00093517.
Lemma F_5c814 : fetch_word Plain.M.loaded_segments (0x5c86c : word) = Some W_5c814.
Proof. vm_refl. Qed.
Lemma D_5c814 : decode_any W_5c814 = Some (Auipc 10 147, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5c818 : bv 32 := 0xebc50513.
Lemma F_5c818 : fetch_word Plain.M.loaded_segments (0x5c870 : word) = Some W_5c818.
Proof. vm_refl. Qed.
Lemma D_5c818 : decode_any W_5c818 = Some (OpImm ALU_ADD 10 10 3772, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5c81c : bv 32 := 0x00053503.
Lemma F_5c81c : fetch_word Plain.M.loaded_segments (0x5c874 : word) = Some W_5c81c.
Proof. vm_refl. Qed.
Lemma D_5c81c : decode_any W_5c81c = Some (Load SZ8 true 10 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5c820 : bv 32 := 0x5397a0ef.
Lemma F_5c820 : fetch_word Plain.M.loaded_segments (0x5c878 : word) = Some W_5c820.
Proof. vm_refl. Qed.
Lemma D_5c820 : decode_any W_5c820 = Some (Jal 1 503096, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5c824 : bv 32 := 0x0040006f.
Lemma F_5c824 : fetch_word Plain.M.loaded_segments (0x5c87c : word) = Some W_5c824.
Proof. vm_refl. Qed.
Lemma D_5c824 : decode_any W_5c824 = Some (Jal 0 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5c828 : bv 32 := 0x00092517.
Lemma F_5c828 : fetch_word Plain.M.loaded_segments (0x5c880 : word) = Some W_5c828.
Proof. vm_refl. Qed.
Lemma D_5c828 : decode_any W_5c828 = Some (Auipc 10 146, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5c82c : bv 32 := 0xcc853503.
Lemma F_5c82c : fetch_word Plain.M.loaded_segments (0x5c884 : word) = Some W_5c82c.
Proof. vm_refl. Qed.
Lemma D_5c82c : decode_any W_5c82c = Some (Load SZ8 true 10 10 3272, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5c830 : bv 32 := 0x00050c63.
Lemma F_5c830 : fetch_word Plain.M.loaded_segments (0x5c888 : word) = Some W_5c830.
Proof. vm_refl. Qed.
Lemma D_5c830 : decode_any W_5c830 = Some (Branch BC_EQ 10 0 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5c834 : bv 32 := 0x0040006f.
Lemma F_5c834 : fetch_word Plain.M.loaded_segments (0x5c88c : word) = Some W_5c834.
Proof. vm_refl. Qed.
Lemma D_5c834 : decode_any W_5c834 = Some (Jal 0 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5c838 : bv 32 := 0xffff3517.
Lemma F_5c838 : fetch_word Plain.M.loaded_segments (0x5c890 : word) = Some W_5c838.
Proof. vm_refl. Qed.
Lemma D_5c838 : decode_any W_5c838 = Some (Auipc 10 1048563, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5c83c : bv 32 := 0x5e850513.
Lemma F_5c83c : fetch_word Plain.M.loaded_segments (0x5c894 : word) = Some W_5c83c.
Proof. vm_refl. Qed.
Lemma D_5c83c : decode_any W_5c83c = Some (OpImm ALU_ADD 10 10 1512, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5c840 : bv 32 := 0x000000ef.
Lemma F_5c840 : fetch_word Plain.M.loaded_segments (0x5c898 : word) = Some W_5c840.
Proof. vm_refl. Qed.
Lemma D_5c840 : decode_any W_5c840 = Some (Jal 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5c844 : bv 32 := 0x0040006f.
Lemma F_5c844 : fetch_word Plain.M.loaded_segments (0x5c89c : word) = Some W_5c844.
Proof. vm_refl. Qed.
Lemma D_5c844 : decode_any W_5c844 = Some (Jal 0 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5c848 : bv 32 := 0x00813083.
Lemma F_5c848 : fetch_word Plain.M.loaded_segments (0x5c8a0 : word) = Some W_5c848.
Proof. vm_refl. Qed.
Lemma D_5c848 : decode_any W_5c848 = Some (Load SZ8 true 1 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5c84c : bv 32 := 0x00013403.
Lemma F_5c84c : fetch_word Plain.M.loaded_segments (0x5c8a4 : word) = Some W_5c84c.
Proof. vm_refl. Qed.
Lemma D_5c84c : decode_any W_5c84c = Some (Load SZ8 true 8 2 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5c850 : bv 32 := 0x01010113.
Lemma F_5c850 : fetch_word Plain.M.loaded_segments (0x5c8a8 : word) = Some W_5c850.
Proof. vm_refl. Qed.
Lemma D_5c850 : decode_any W_5c850 = Some (OpImm ALU_ADD 2 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5c854 : bv 32 := 0x00008067.
Lemma F_5c854 : fetch_word Plain.M.loaded_segments (0x5c8ac : word) = Some W_5c854.
Proof. vm_refl. Qed.
Lemma D_5c854 : decode_any W_5c854 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5cc80 : bv 32 := 0x000a3517.
Lemma F_5cc80 : fetch_word Plain.M.loaded_segments (0x5ccd8 : word) = Some W_5cc80.
Proof. vm_refl. Qed.
Lemma D_5cc80 : decode_any W_5cc80 = Some (Auipc 10 163, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5cc84 : bv 32 := 0xd1c54503.
Lemma F_5cc84 : fetch_word Plain.M.loaded_segments (0x5ccdc : word) = Some W_5cc84.
Proof. vm_refl. Qed.
Lemma D_5cc84 : decode_any W_5cc84 = Some (Load SZ1 false 10 10 3356, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5cc88 : bv 32 := 0x00051463.
Lemma F_5cc88 : fetch_word Plain.M.loaded_segments (0x5cce0 : word) = Some W_5cc88.
Proof. vm_refl. Qed.
Lemma D_5cc88 : decode_any W_5cc88 = Some (Branch BC_NE 10 0 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5cc8c : bv 32 := 0x00008067.
Lemma F_5cc8c : fetch_word Plain.M.loaded_segments (0x5cce4 : word) = Some W_5cc8c.
Proof. vm_refl. Qed.
Lemma D_5cc8c : decode_any W_5cc8c = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5cc90 : bv 32 := 0xff010113.
Lemma F_5cc90 : fetch_word Plain.M.loaded_segments (0x5cce8 : word) = Some W_5cc90.
Proof. vm_refl. Qed.
Lemma D_5cc90 : decode_any W_5cc90 = Some (OpImm ALU_ADD 2 2 4080, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5cc94 : bv 32 := 0x00113423.
Lemma F_5cc94 : fetch_word Plain.M.loaded_segments (0x5ccec : word) = Some W_5cc94.
Proof. vm_refl. Qed.
Lemma D_5cc94 : decode_any W_5cc94 = Some (Store SZ8 2 1 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5cc98 : bv 32 := 0x00092517.
Lemma F_5cc98 : fetch_word Plain.M.loaded_segments (0x5ccf0 : word) = Some W_5cc98.
Proof. vm_refl. Qed.
Lemma D_5cc98 : decode_any W_5cc98 = Some (Auipc 10 146, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5cc9c : bv 32 := 0x87853503.
Lemma F_5cc9c : fetch_word Plain.M.loaded_segments (0x5ccf4 : word) = Some W_5cc9c.
Proof. vm_refl. Qed.
Lemma D_5cc9c : decode_any W_5cc9c = Some (Load SZ8 true 10 10 2168, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5cca0 : bv 32 := 0x00053503.
Lemma F_5cca0 : fetch_word Plain.M.loaded_segments (0x5ccf8 : word) = Some W_5cca0.
Proof. vm_refl. Qed.
Lemma D_5cca0 : decode_any W_5cca0 = Some (Load SZ8 true 10 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5cca4 : bv 32 := 0x4807e0ef.
Lemma F_5cca4 : fetch_word Plain.M.loaded_segments (0x5ccfc : word) = Some W_5cca4.
Proof. vm_refl. Qed.
Lemma D_5cca4 : decode_any W_5cca4 = Some (Jal 1 517248, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5cca8 : bv 32 := 0x04d00513.
Lemma F_5cca8 : fetch_word Plain.M.loaded_segments (0x5cd00 : word) = Some W_5cca8.
Proof. vm_refl. Qed.
Lemma D_5cca8 : decode_any W_5cca8 = Some (OpImm ALU_ADD 10 0 77, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5ccac : bv 32 := 0x2b48d0ef.
Lemma F_5ccac : fetch_word Plain.M.loaded_segments (0x5cd04 : word) = Some W_5ccac.
Proof. vm_refl. Qed.
Lemma D_5ccac : decode_any W_5ccac = Some (Jal 1 578228, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d74a0 : bv 32 := 0xfd010113.
Lemma F_d74a0 : fetch_word Plain.M.loaded_segments (0xd74e8 : word) = Some W_d74a0.
Proof. vm_refl. Qed.
Lemma D_d74a0 : decode_any W_d74a0 = Some (OpImm ALU_ADD 2 2 4048, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d74a4 : bv 32 := 0x02113423.
Lemma F_d74a4 : fetch_word Plain.M.loaded_segments (0xd74ec : word) = Some W_d74a4.
Proof. vm_refl. Qed.
Lemma D_d74a4 : decode_any W_d74a4 = Some (Store SZ8 2 1 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d74a8 : bv 32 := 0x02813023.
Lemma F_d74a8 : fetch_word Plain.M.loaded_segments (0xd74f0 : word) = Some W_d74a8.
Proof. vm_refl. Qed.
Lemma D_d74a8 : decode_any W_d74a8 = Some (Store SZ8 2 8 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d74ac : bv 32 := 0x00913c23.
Lemma F_d74ac : fetch_word Plain.M.loaded_segments (0xd74f4 : word) = Some W_d74ac.
Proof. vm_refl. Qed.
Lemma D_d74ac : decode_any W_d74ac = Some (Store SZ8 2 9 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d74b0 : bv 32 := 0x01213823.
Lemma F_d74b0 : fetch_word Plain.M.loaded_segments (0xd74f8 : word) = Some W_d74b0.
Proof. vm_refl. Qed.
Lemma D_d74b0 : decode_any W_d74b0 = Some (Store SZ8 2 18 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d74b4 : bv 32 := 0x01313423.
Lemma F_d74b4 : fetch_word Plain.M.loaded_segments (0xd74fc : word) = Some W_d74b4.
Proof. vm_refl. Qed.
Lemma D_d74b4 : decode_any W_d74b4 = Some (Store SZ8 2 19 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d74b8 : bv 32 := 0x00048517.
Lemma F_d74b8 : fetch_word Plain.M.loaded_segments (0xd7500 : word) = Some W_d74b8.
Proof. vm_refl. Qed.
Lemma D_d74b8 : decode_any W_d74b8 = Some (Auipc 10 72, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d74bc : bv 32 := 0x7f050913.
Lemma F_d74bc : fetch_word Plain.M.loaded_segments (0xd7504 : word) = Some W_d74bc.
Proof. vm_refl. Qed.
Lemma D_d74bc : decode_any W_d74bc = Some (OpImm ALU_ADD 18 10 2032, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d74c0 : bv 32 := 0x00490413.
Lemma F_d74c0 : fetch_word Plain.M.loaded_segments (0xd7508 : word) = Some W_d74c0.
Proof. vm_refl. Qed.
Lemma D_d74c0 : decode_any W_d74c0 = Some (OpImm ALU_ADD 8 18 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d74c4 : bv 32 := 0x00040513.
Lemma F_d74c4 : fetch_word Plain.M.loaded_segments (0xd750c : word) = Some W_d74c4.
Proof. vm_refl. Qed.
Lemma D_d74c4 : decode_any W_d74c4 = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d74c8 : bv 32 := 0x5480f0ef.
Lemma F_d74c8 : fetch_word Plain.M.loaded_segments (0xd7510 : word) = Some W_d74c8.
Proof. vm_refl. Qed.
Lemma D_d74c8 : decode_any W_d74c8 = Some (Jal 1 62792, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d74cc : bv 32 := 0x01093503.
Lemma F_d74cc : fetch_word Plain.M.loaded_segments (0xd7514 : word) = Some W_d74cc.
Proof. vm_refl. Qed.
Lemma D_d74cc : decode_any W_d74cc = Some (Load SZ8 true 10 18 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d74d0 : bv 32 := 0x06050863.
Lemma F_d74d0 : fetch_word Plain.M.loaded_segments (0xd7518 : word) = Some W_d74d0.
Proof. vm_refl. Qed.
Lemma D_d74d0 : decode_any W_d74d0 = Some (Branch BC_EQ 10 0 112, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d74d4 : bv 32 := 0x00892583.
Lemma F_d74d4 : fetch_word Plain.M.loaded_segments (0xd751c : word) = Some W_d74d4.
Proof. vm_refl. Qed.
Lemma D_d74d4 : decode_any W_d74d4 = Some (Load SZ4 true 11 18 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d74d8 : bv 32 := 0x0180006f.
Lemma F_d74d8 : fetch_word Plain.M.loaded_segments (0xd7520 : word) = Some W_d74d8.
Proof. vm_refl. Qed.
Lemma D_d74d8 : decode_any W_d74d8 = Some (Jal 0 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d74dc : bv 32 := 0x00053503.
Lemma F_d74dc : fetch_word Plain.M.loaded_segments (0xd7524 : word) = Some W_d74dc.
Proof. vm_refl. Qed.
Lemma D_d74dc : decode_any W_d74dc = Some (Load SZ8 true 10 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d74e0 : bv 32 := 0x02000593.
Lemma F_d74e0 : fetch_word Plain.M.loaded_segments (0xd7528 : word) = Some W_d74e0.
Proof. vm_refl. Qed.
Lemma D_d74e0 : decode_any W_d74e0 = Some (OpImm ALU_ADD 11 0 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d74e4 : bv 32 := 0x00b92423.
Lemma F_d74e4 : fetch_word Plain.M.loaded_segments (0xd752c : word) = Some W_d74e4.
Proof. vm_refl. Qed.
Lemma D_d74e4 : decode_any W_d74e4 = Some (Store SZ4 18 11 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d74e8 : bv 32 := 0x00a93823.
Lemma F_d74e8 : fetch_word Plain.M.loaded_segments (0xd7530 : word) = Some W_d74e8.
Proof. vm_refl. Qed.
Lemma D_d74e8 : decode_any W_d74e8 = Some (Store SZ8 18 10 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d74ec : bv 32 := 0x04050a63.
Lemma F_d74ec : fetch_word Plain.M.loaded_segments (0xd7534 : word) = Some W_d74ec.
Proof. vm_refl. Qed.
Lemma D_d74ec : decode_any W_d74ec = Some (Branch BC_EQ 10 0 84, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d74f0 : bv 32 := 0xfff5861b.
Lemma F_d74f0 : fetch_word Plain.M.loaded_segments (0xd7538 : word) = Some W_d74f0.
Proof. vm_refl. Qed.
Lemma D_d74f0 : decode_any W_d74f0 = Some (OpImm32 12 11 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d74f4 : bv 32 := 0x00c92423.
Lemma F_d74f4 : fetch_word Plain.M.loaded_segments (0xd753c : word) = Some W_d74f4.
Proof. vm_refl. Qed.
Lemma D_d74f4 : decode_any W_d74f4 = Some (Store SZ4 18 12 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d74f8 : bv 32 := 0xfeb052e3.
Lemma F_d74f8 : fetch_word Plain.M.loaded_segments (0xd7540 : word) = Some W_d74f8.
Proof. vm_refl. Qed.
Lemma D_d74f8 : decode_any W_d74f8 = Some (Branch BC_GE 0 11 8164, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d74fc : bv 32 := 0x01093503.
Lemma F_d74fc : fetch_word Plain.M.loaded_segments (0xd7544 : word) = Some W_d74fc.
Proof. vm_refl. Qed.
Lemma D_d74fc : decode_any W_d74fc = Some (Load SZ8 true 10 18 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d7500 : bv 32 := 0x00361613.
Lemma F_d7500 : fetch_word Plain.M.loaded_segments (0xd7548 : word) = Some W_d7500.
Proof. vm_refl. Qed.
Lemma D_d7500 : decode_any W_d7500 = Some (ShiftImm ALU_SLL 12 12 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d7504 : bv 32 := 0x00c50533.
Lemma F_d7504 : fetch_word Plain.M.loaded_segments (0xd754c : word) = Some W_d7504.
Proof. vm_refl. Qed.
Lemma D_d7504 : decode_any W_d7504 = Some (Op ALU_ADD 10 10 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d7508 : bv 32 := 0x00853983.
Lemma F_d7508 : fetch_word Plain.M.loaded_segments (0xd7550 : word) = Some W_d7508.
Proof. vm_refl. Qed.
Lemma D_d7508 : decode_any W_d7508 = Some (Load SZ8 true 19 10 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d750c : bv 32 := 0x10853483.
Lemma F_d750c : fetch_word Plain.M.loaded_segments (0xd7554 : word) = Some W_d750c.
Proof. vm_refl. Qed.
Lemma D_d750c : decode_any W_d750c = Some (Load SZ8 true 9 10 264, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d7510 : bv 32 := 0x00040513.
Lemma F_d7510 : fetch_word Plain.M.loaded_segments (0xd7558 : word) = Some W_d7510.
Proof. vm_refl. Qed.
Lemma D_d7510 : decode_any W_d7510 = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d7514 : bv 32 := 0x7840f0ef.
Lemma F_d7514 : fetch_word Plain.M.loaded_segments (0xd755c : word) = Some W_d7514.
Proof. vm_refl. Qed.
Lemma D_d7514 : decode_any W_d7514 = Some (Jal 1 63364, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d7518 : bv 32 := 0x00048513.
Lemma F_d7518 : fetch_word Plain.M.loaded_segments (0xd7560 : word) = Some W_d7518.
Proof. vm_refl. Qed.
Lemma D_d7518 : decode_any W_d7518 = Some (OpImm ALU_ADD 10 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d751c : bv 32 := 0x000980e7.
Lemma F_d751c : fetch_word Plain.M.loaded_segments (0xd7564 : word) = Some W_d751c.
Proof. vm_refl. Qed.
Lemma D_d751c : decode_any W_d751c = Some (Jalr 1 19 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d7520 : bv 32 := 0x00040513.
Lemma F_d7520 : fetch_word Plain.M.loaded_segments (0xd7568 : word) = Some W_d7520.
Proof. vm_refl. Qed.
Lemma D_d7520 : decode_any W_d7520 = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d7524 : bv 32 := 0x4ec0f0ef.
Lemma F_d7524 : fetch_word Plain.M.loaded_segments (0xd756c : word) = Some W_d7524.
Proof. vm_refl. Qed.
Lemma D_d7524 : decode_any W_d7524 = Some (Jal 1 62700, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d7528 : bv 32 := 0x00892503.
Lemma F_d7528 : fetch_word Plain.M.loaded_segments (0xd7570 : word) = Some W_d7528.
Proof. vm_refl. Qed.
Lemma D_d7528 : decode_any W_d7528 = Some (Load SZ4 true 10 18 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d752c : bv 32 := 0xfff5061b.
Lemma F_d752c : fetch_word Plain.M.loaded_segments (0xd7574 : word) = Some W_d752c.
Proof. vm_refl. Qed.
Lemma D_d752c : decode_any W_d752c = Some (OpImm32 12 10 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d7530 : bv 32 := 0x00c92423.
Lemma F_d7530 : fetch_word Plain.M.loaded_segments (0xd7578 : word) = Some W_d7530.
Proof. vm_refl. Qed.
Lemma D_d7530 : decode_any W_d7530 = Some (Store SZ4 18 12 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d7534 : bv 32 := 0xfca044e3.
Lemma F_d7534 : fetch_word Plain.M.loaded_segments (0xd757c : word) = Some W_d7534.
Proof. vm_refl. Qed.
Lemma D_d7534 : decode_any W_d7534 = Some (Branch BC_LT 0 10 8136, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d7538 : bv 32 := 0x01093503.
Lemma F_d7538 : fetch_word Plain.M.loaded_segments (0xd7580 : word) = Some W_d7538.
Proof. vm_refl. Qed.
Lemma D_d7538 : decode_any W_d7538 = Some (Load SZ8 true 10 18 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d753c : bv 32 := 0xfa1ff06f.
Lemma F_d753c : fetch_word Plain.M.loaded_segments (0xd7584 : word) = Some W_d753c.
Proof. vm_refl. Qed.
Lemma D_d753c : decode_any W_d753c = Some (Jal 0 2097056, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d7540 : bv 32 := 0x00100513.
Lemma F_d7540 : fetch_word Plain.M.loaded_segments (0xd7588 : word) = Some W_d7540.
Proof. vm_refl. Qed.
Lemma D_d7540 : decode_any W_d7540 = Some (OpImm ALU_ADD 10 0 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d7544 : bv 32 := 0x00a90023.
Lemma F_d7544 : fetch_word Plain.M.loaded_segments (0xd758c : word) = Some W_d7544.
Proof. vm_refl. Qed.
Lemma D_d7544 : decode_any W_d7544 = Some (Store SZ1 18 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d7548 : bv 32 := 0x00040513.
Lemma F_d7548 : fetch_word Plain.M.loaded_segments (0xd7590 : word) = Some W_d7548.
Proof. vm_refl. Qed.
Lemma D_d7548 : decode_any W_d7548 = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d754c : bv 32 := 0x02813083.
Lemma F_d754c : fetch_word Plain.M.loaded_segments (0xd7594 : word) = Some W_d754c.
Proof. vm_refl. Qed.
Lemma D_d754c : decode_any W_d754c = Some (Load SZ8 true 1 2 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d7550 : bv 32 := 0x02013403.
Lemma F_d7550 : fetch_word Plain.M.loaded_segments (0xd7598 : word) = Some W_d7550.
Proof. vm_refl. Qed.
Lemma D_d7550 : decode_any W_d7550 = Some (Load SZ8 true 8 2 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d7554 : bv 32 := 0x01813483.
Lemma F_d7554 : fetch_word Plain.M.loaded_segments (0xd759c : word) = Some W_d7554.
Proof. vm_refl. Qed.
Lemma D_d7554 : decode_any W_d7554 = Some (Load SZ8 true 9 2 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d7558 : bv 32 := 0x01013903.
Lemma F_d7558 : fetch_word Plain.M.loaded_segments (0xd75a0 : word) = Some W_d7558.
Proof. vm_refl. Qed.
Lemma D_d7558 : decode_any W_d7558 = Some (Load SZ8 true 18 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d755c : bv 32 := 0x00813983.
Lemma F_d755c : fetch_word Plain.M.loaded_segments (0xd75a4 : word) = Some W_d755c.
Proof. vm_refl. Qed.
Lemma D_d755c : decode_any W_d755c = Some (Load SZ8 true 19 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d7560 : bv 32 := 0x03010113.
Lemma F_d7560 : fetch_word Plain.M.loaded_segments (0xd75a8 : word) = Some W_d7560.
Proof. vm_refl. Qed.
Lemma D_d7560 : decode_any W_d7560 = Some (OpImm ALU_ADD 2 2 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d7564 : bv 32 := 0x7340f06f.
Lemma F_d7564 : fetch_word Plain.M.loaded_segments (0xd75ac : word) = Some W_d7564.
Proof. vm_refl. Qed.
Lemma D_d7564 : decode_any W_d7564 = Some (Jal 0 63284, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d7568 : bv 32 := 0x00008067.
Lemma F_d7568 : fetch_word Plain.M.loaded_segments (0xd75b0 : word) = Some W_d7568.
Proof. vm_refl. Qed.
Lemma D_d7568 : decode_any W_d7568 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d756c : bv 32 := 0xfd010113.
Lemma F_d756c : fetch_word Plain.M.loaded_segments (0xd75b4 : word) = Some W_d756c.
Proof. vm_refl. Qed.
Lemma D_d756c : decode_any W_d756c = Some (OpImm ALU_ADD 2 2 4048, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d7570 : bv 32 := 0x02113423.
Lemma F_d7570 : fetch_word Plain.M.loaded_segments (0xd75b8 : word) = Some W_d7570.
Proof. vm_refl. Qed.
Lemma D_d7570 : decode_any W_d7570 = Some (Store SZ8 2 1 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d7574 : bv 32 := 0x02813023.
Lemma F_d7574 : fetch_word Plain.M.loaded_segments (0xd75bc : word) = Some W_d7574.
Proof. vm_refl. Qed.
Lemma D_d7574 : decode_any W_d7574 = Some (Store SZ8 2 8 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d7578 : bv 32 := 0x00913c23.
Lemma F_d7578 : fetch_word Plain.M.loaded_segments (0xd75c0 : word) = Some W_d7578.
Proof. vm_refl. Qed.
Lemma D_d7578 : decode_any W_d7578 = Some (Store SZ8 2 9 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d757c : bv 32 := 0x01213823.
Lemma F_d757c : fetch_word Plain.M.loaded_segments (0xd75c4 : word) = Some W_d757c.
Proof. vm_refl. Qed.
Lemma D_d757c : decode_any W_d757c = Some (Store SZ8 2 18 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d7580 : bv 32 := 0x01313423.
Lemma F_d7580 : fetch_word Plain.M.loaded_segments (0xd75c8 : word) = Some W_d7580.
Proof. vm_refl. Qed.
Lemma D_d7580 : decode_any W_d7580 = Some (Store SZ8 2 19 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d7584 : bv 32 := 0x00050493.
Lemma F_d7584 : fetch_word Plain.M.loaded_segments (0xd75cc : word) = Some W_d7584.
Proof. vm_refl. Qed.
Lemma D_d7584 : decode_any W_d7584 = Some (OpImm ALU_ADD 9 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d7588 : bv 32 := 0x00048517.
Lemma F_d7588 : fetch_word Plain.M.loaded_segments (0xd75d0 : word) = Some W_d7588.
Proof. vm_refl. Qed.
Lemma D_d7588 : decode_any W_d7588 = Some (Auipc 10 72, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d758c : bv 32 := 0x72050993.
Lemma F_d758c : fetch_word Plain.M.loaded_segments (0xd75d4 : word) = Some W_d758c.
Proof. vm_refl. Qed.
Lemma D_d758c : decode_any W_d758c = Some (OpImm ALU_ADD 19 10 1824, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d7590 : bv 32 := 0x00498413.
Lemma F_d7590 : fetch_word Plain.M.loaded_segments (0xd75d8 : word) = Some W_d7590.
Proof. vm_refl. Qed.
Lemma D_d7590 : decode_any W_d7590 = Some (OpImm ALU_ADD 8 19 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d7594 : bv 32 := 0x00040513.
Lemma F_d7594 : fetch_word Plain.M.loaded_segments (0xd75dc : word) = Some W_d7594.
Proof. vm_refl. Qed.
Lemma D_d7594 : decode_any W_d7594 = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d7598 : bv 32 := 0x4780f0ef.
Lemma F_d7598 : fetch_word Plain.M.loaded_segments (0xd75e0 : word) = Some W_d7598.
Proof. vm_refl. Qed.
Lemma D_d7598 : decode_any W_d7598 = Some (Jal 1 62584, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d759c : bv 32 := 0x0009c503.
Lemma F_d759c : fetch_word Plain.M.loaded_segments (0xd75e4 : word) = Some W_d759c.
Proof. vm_refl. Qed.
Lemma D_d759c : decode_any W_d759c = Some (Load SZ1 false 10 19 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d75a0 : bv 32 := 0xfff00913.
Lemma F_d75a0 : fetch_word Plain.M.loaded_segments (0xd75e8 : word) = Some W_d75a0.
Proof. vm_refl. Qed.
Lemma D_d75a0 : decode_any W_d75a0 = Some (OpImm ALU_ADD 18 0 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d75a4 : bv 32 := 0x06051263.
Lemma F_d75a4 : fetch_word Plain.M.loaded_segments (0xd75ec : word) = Some W_d75a4.
Proof. vm_refl. Qed.
Lemma D_d75a4 : decode_any W_d75a4 = Some (Branch BC_NE 10 0 100, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d75a8 : bv 32 := 0x0109b503.
Lemma F_d75a8 : fetch_word Plain.M.loaded_segments (0xd75f0 : word) = Some W_d75a8.
Proof. vm_refl. Qed.
Lemma D_d75a8 : decode_any W_d75a8 = Some (Load SZ8 true 10 19 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d75ac : bv 32 := 0x00051663.
Lemma F_d75ac : fetch_word Plain.M.loaded_segments (0xd75f4 : word) = Some W_d75ac.
Proof. vm_refl. Qed.
Lemma D_d75ac : decode_any W_d75ac = Some (Branch BC_NE 10 0 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d75b0 : bv 32 := 0x01898513.
Lemma F_d75b0 : fetch_word Plain.M.loaded_segments (0xd75f8 : word) = Some W_d75b0.
Proof. vm_refl. Qed.
Lemma D_d75b0 : decode_any W_d75b0 = Some (OpImm ALU_ADD 10 19 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d75b4 : bv 32 := 0x00a9b823.
Lemma F_d75b4 : fetch_word Plain.M.loaded_segments (0xd75fc : word) = Some W_d75b4.
Proof. vm_refl. Qed.
Lemma D_d75b4 : decode_any W_d75b4 = Some (Store SZ8 19 10 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d75b8 : bv 32 := 0x0089a583.
Lemma F_d75b8 : fetch_word Plain.M.loaded_segments (0xd7600 : word) = Some W_d75b8.
Proof. vm_refl. Qed.
Lemma D_d75b8 : decode_any W_d75b8 = Some (Load SZ4 true 11 19 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d75bc : bv 32 := 0x02000613.
Lemma F_d75bc : fetch_word Plain.M.loaded_segments (0xd7604 : word) = Some W_d75bc.
Proof. vm_refl. Qed.
Lemma D_d75bc : decode_any W_d75bc = Some (OpImm ALU_ADD 12 0 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d75c0 : bv 32 := 0x02c59263.
Lemma F_d75c0 : fetch_word Plain.M.loaded_segments (0xd7608 : word) = Some W_d75c0.
Proof. vm_refl. Qed.
Lemma D_d75c0 : decode_any W_d75c0 = Some (Branch BC_NE 11 12 36, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d75c4 : bv 32 := 0x20800513.
Lemma F_d75c4 : fetch_word Plain.M.loaded_segments (0xd760c : word) = Some W_d75c4.
Proof. vm_refl. Qed.
Lemma D_d75c4 : decode_any W_d75c4 = Some (OpImm ALU_ADD 10 0 520, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d75c8 : bv 32 := 0x00100593.
Lemma F_d75c8 : fetch_word Plain.M.loaded_segments (0xd7610 : word) = Some W_d75c8.
Proof. vm_refl. Qed.
Lemma D_d75c8 : decode_any W_d75c8 = Some (OpImm ALU_ADD 11 0 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d75cc : bv 32 := 0x3f4000ef.
Lemma F_d75cc : fetch_word Plain.M.loaded_segments (0xd7614 : word) = Some W_d75cc.
Proof. vm_refl. Qed.
Lemma D_d75cc : decode_any W_d75cc = Some (Jal 1 1012, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d75d0 : bv 32 := 0x02050c63.
Lemma F_d75d0 : fetch_word Plain.M.loaded_segments (0xd7618 : word) = Some W_d75d0.
Proof. vm_refl. Qed.
Lemma D_d75d0 : decode_any W_d75d0 = Some (Branch BC_EQ 10 0 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d75d4 : bv 32 := 0x00000593.
Lemma F_d75d4 : fetch_word Plain.M.loaded_segments (0xd761c : word) = Some W_d75d4.
Proof. vm_refl. Qed.
Lemma D_d75d4 : decode_any W_d75d4 = Some (OpImm ALU_ADD 11 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d75d8 : bv 32 := 0x0109b603.
Lemma F_d75d8 : fetch_word Plain.M.loaded_segments (0xd7620 : word) = Some W_d75d8.
Proof. vm_refl. Qed.
Lemma D_d75d8 : decode_any W_d75d8 = Some (Load SZ8 true 12 19 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d75dc : bv 32 := 0x00c53023.
Lemma F_d75dc : fetch_word Plain.M.loaded_segments (0xd7624 : word) = Some W_d75dc.
Proof. vm_refl. Qed.
Lemma D_d75dc : decode_any W_d75dc = Some (Store SZ8 10 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d75e0 : bv 32 := 0x00a9b823.
Lemma F_d75e0 : fetch_word Plain.M.loaded_segments (0xd7628 : word) = Some W_d75e0.
Proof. vm_refl. Qed.
Lemma D_d75e0 : decode_any W_d75e0 = Some (Store SZ8 19 10 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d75e4 : bv 32 := 0x00000913.
Lemma F_d75e4 : fetch_word Plain.M.loaded_segments (0xd762c : word) = Some W_d75e4.
Proof. vm_refl. Qed.
Lemma D_d75e4 : decode_any W_d75e4 = Some (OpImm ALU_ADD 18 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d75e8 : bv 32 := 0x00359613.
Lemma F_d75e8 : fetch_word Plain.M.loaded_segments (0xd7630 : word) = Some W_d75e8.
Proof. vm_refl. Qed.
Lemma D_d75e8 : decode_any W_d75e8 = Some (ShiftImm ALU_SLL 12 11 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d75ec : bv 32 := 0x00c50533.
Lemma F_d75ec : fetch_word Plain.M.loaded_segments (0xd7634 : word) = Some W_d75ec.
Proof. vm_refl. Qed.
Lemma D_d75ec : decode_any W_d75ec = Some (Op ALU_ADD 10 10 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d75f0 : bv 32 := 0x00000617.
Lemma F_d75f0 : fetch_word Plain.M.loaded_segments (0xd7638 : word) = Some W_d75f0.
Proof. vm_refl. Qed.
Lemma D_d75f0 : decode_any W_d75f0 = Some (Auipc 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d75f4 : bv 32 := 0x00158593.
Lemma F_d75f4 : fetch_word Plain.M.loaded_segments (0xd763c : word) = Some W_d75f4.
Proof. vm_refl. Qed.
Lemma D_d75f4 : decode_any W_d75f4 = Some (OpImm ALU_ADD 11 11 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d75f8 : bv 32 := 0x04060613.
Lemma F_d75f8 : fetch_word Plain.M.loaded_segments (0xd7640 : word) = Some W_d75f8.
Proof. vm_refl. Qed.
Lemma D_d75f8 : decode_any W_d75f8 = Some (OpImm ALU_ADD 12 12 64, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d75fc : bv 32 := 0x00c53423.
Lemma F_d75fc : fetch_word Plain.M.loaded_segments (0xd7644 : word) = Some W_d75fc.
Proof. vm_refl. Qed.
Lemma D_d75fc : decode_any W_d75fc = Some (Store SZ8 10 12 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d7600 : bv 32 := 0x10953423.
Lemma F_d7600 : fetch_word Plain.M.loaded_segments (0xd7648 : word) = Some W_d7600.
Proof. vm_refl. Qed.
Lemma D_d7600 : decode_any W_d7600 = Some (Store SZ8 10 9 264, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d7604 : bv 32 := 0x00b9a423.
Lemma F_d7604 : fetch_word Plain.M.loaded_segments (0xd764c : word) = Some W_d7604.
Proof. vm_refl. Qed.
Lemma D_d7604 : decode_any W_d7604 = Some (Store SZ4 19 11 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d7608 : bv 32 := 0x00040513.
Lemma F_d7608 : fetch_word Plain.M.loaded_segments (0xd7650 : word) = Some W_d7608.
Proof. vm_refl. Qed.
Lemma D_d7608 : decode_any W_d7608 = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d760c : bv 32 := 0x68c0f0ef.
Lemma F_d760c : fetch_word Plain.M.loaded_segments (0xd7654 : word) = Some W_d760c.
Proof. vm_refl. Qed.
Lemma D_d760c : decode_any W_d760c = Some (Jal 1 63116, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d7610 : bv 32 := 0x00090513.
Lemma F_d7610 : fetch_word Plain.M.loaded_segments (0xd7658 : word) = Some W_d7610.
Proof. vm_refl. Qed.
Lemma D_d7610 : decode_any W_d7610 = Some (OpImm ALU_ADD 10 18 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d7614 : bv 32 := 0x02813083.
Lemma F_d7614 : fetch_word Plain.M.loaded_segments (0xd765c : word) = Some W_d7614.
Proof. vm_refl. Qed.
Lemma D_d7614 : decode_any W_d7614 = Some (Load SZ8 true 1 2 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d7618 : bv 32 := 0x02013403.
Lemma F_d7618 : fetch_word Plain.M.loaded_segments (0xd7660 : word) = Some W_d7618.
Proof. vm_refl. Qed.
Lemma D_d7618 : decode_any W_d7618 = Some (Load SZ8 true 8 2 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d761c : bv 32 := 0x01813483.
Lemma F_d761c : fetch_word Plain.M.loaded_segments (0xd7664 : word) = Some W_d761c.
Proof. vm_refl. Qed.
Lemma D_d761c : decode_any W_d761c = Some (Load SZ8 true 9 2 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d7620 : bv 32 := 0x01013903.
Lemma F_d7620 : fetch_word Plain.M.loaded_segments (0xd7668 : word) = Some W_d7620.
Proof. vm_refl. Qed.
Lemma D_d7620 : decode_any W_d7620 = Some (Load SZ8 true 18 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d7624 : bv 32 := 0x00813983.
Lemma F_d7624 : fetch_word Plain.M.loaded_segments (0xd766c : word) = Some W_d7624.
Proof. vm_refl. Qed.
Lemma D_d7624 : decode_any W_d7624 = Some (Load SZ8 true 19 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d7628 : bv 32 := 0x03010113.
Lemma F_d7628 : fetch_word Plain.M.loaded_segments (0xd7670 : word) = Some W_d7628.
Proof. vm_refl. Qed.
Lemma D_d7628 : decode_any W_d7628 = Some (OpImm ALU_ADD 2 2 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d762c : bv 32 := 0x00008067.
Lemma F_d762c : fetch_word Plain.M.loaded_segments (0xd7674 : word) = Some W_d762c.
Proof. vm_refl. Qed.
Lemma D_d762c : decode_any W_d762c = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d7630 : bv 32 := 0x00050067.
Lemma F_d7630 : fetch_word Plain.M.loaded_segments (0xd7678 : word) = Some W_d7630.
Proof. vm_refl. Qed.
Lemma D_d7630 : decode_any W_d7630 = Some (Jalr 0 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d7634 : bv 32 := 0x00008067.
Lemma F_d7634 : fetch_word Plain.M.loaded_segments (0xd767c : word) = Some W_d7634.
Proof. vm_refl. Qed.
Lemma D_d7634 : decode_any W_d7634 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d7638 : bv 32 := 0xfe010113.
Lemma F_d7638 : fetch_word Plain.M.loaded_segments (0xd7680 : word) = Some W_d7638.
Proof. vm_refl. Qed.
Lemma D_d7638 : decode_any W_d7638 = Some (OpImm ALU_ADD 2 2 4064, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d763c : bv 32 := 0x00113c23.
Lemma F_d763c : fetch_word Plain.M.loaded_segments (0xd7684 : word) = Some W_d763c.
Proof. vm_refl. Qed.
Lemma D_d763c : decode_any W_d763c = Some (Store SZ8 2 1 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d7640 : bv 32 := 0x00813823.
Lemma F_d7640 : fetch_word Plain.M.loaded_segments (0xd7688 : word) = Some W_d7640.
Proof. vm_refl. Qed.
Lemma D_d7640 : decode_any W_d7640 = Some (Store SZ8 2 8 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d7644 : bv 32 := 0x00913423.
Lemma F_d7644 : fetch_word Plain.M.loaded_segments (0xd768c : word) = Some W_d7644.
Proof. vm_refl. Qed.
Lemma D_d7644 : decode_any W_d7644 = Some (Store SZ8 2 9 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d7648 : bv 32 := 0x00017517.
Lemma F_d7648 : fetch_word Plain.M.loaded_segments (0xd7690 : word) = Some W_d7648.
Proof. vm_refl. Qed.
Lemma D_d7648 : decode_any W_d7648 = Some (Auipc 10 23, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d764c : bv 32 := 0x00017597.
Lemma F_d764c : fetch_word Plain.M.loaded_segments (0xd7694 : word) = Some W_d764c.
Proof. vm_refl. Qed.
Lemma D_d764c : decode_any W_d764c = Some (Auipc 11 23, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d7650 : bv 32 := 0x07053503.
Lemma F_d7650 : fetch_word Plain.M.loaded_segments (0xd7698 : word) = Some W_d7650.
Proof. vm_refl. Qed.
Lemma D_d7650 : decode_any W_d7650 = Some (Load SZ8 true 10 10 112, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d7654 : bv 32 := 0x0745b403.
Lemma F_d7654 : fetch_word Plain.M.loaded_segments (0xd769c : word) = Some W_d7654.
Proof. vm_refl. Qed.
Lemma D_d7654 : decode_any W_d7654 = Some (Load SZ8 true 8 11 116, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d7658 : bv 32 := 0x00a47c63.
Lemma F_d7658 : fetch_word Plain.M.loaded_segments (0xd76a0 : word) = Some W_d7658.
Proof. vm_refl. Qed.
Lemma D_d7658 : decode_any W_d7658 = Some (Branch BC_GEU 8 10 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d765c : bv 32 := 0xff853583.
Lemma F_d765c : fetch_word Plain.M.loaded_segments (0xd76a4 : word) = Some W_d765c.
Proof. vm_refl. Qed.
Lemma D_d765c : decode_any W_d765c = Some (Load SZ8 true 11 10 4088, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d7660 : bv 32 := 0xff850493.
Lemma F_d7660 : fetch_word Plain.M.loaded_segments (0xd76a8 : word) = Some W_d7660.
Proof. vm_refl. Qed.
Lemma D_d7660 : decode_any W_d7660 = Some (OpImm ALU_ADD 9 10 4088, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d7664 : bv 32 := 0x000580e7.
Lemma F_d7664 : fetch_word Plain.M.loaded_segments (0xd76ac : word) = Some W_d7664.
Proof. vm_refl. Qed.
Lemma D_d7664 : decode_any W_d7664 = Some (Jalr 1 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d7668 : bv 32 := 0x00048513.
Lemma F_d7668 : fetch_word Plain.M.loaded_segments (0xd76b0 : word) = Some W_d7668.
Proof. vm_refl. Qed.
Lemma D_d7668 : decode_any W_d7668 = Some (OpImm ALU_ADD 10 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d766c : bv 32 := 0xfe9468e3.
Lemma F_d766c : fetch_word Plain.M.loaded_segments (0xd76b4 : word) = Some W_d766c.
Proof. vm_refl. Qed.
Lemma D_d766c : decode_any W_d766c = Some (Branch BC_LTU 8 9 8176, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d7670 : bv 32 := 0x01813083.
Lemma F_d7670 : fetch_word Plain.M.loaded_segments (0xd76b8 : word) = Some W_d7670.
Proof. vm_refl. Qed.
Lemma D_d7670 : decode_any W_d7670 = Some (Load SZ8 true 1 2 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d7674 : bv 32 := 0x01013403.
Lemma F_d7674 : fetch_word Plain.M.loaded_segments (0xd76bc : word) = Some W_d7674.
Proof. vm_refl. Qed.
Lemma D_d7674 : decode_any W_d7674 = Some (Load SZ8 true 8 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d7678 : bv 32 := 0x00813483.
Lemma F_d7678 : fetch_word Plain.M.loaded_segments (0xd76c0 : word) = Some W_d7678.
Proof. vm_refl. Qed.
Lemma D_d7678 : decode_any W_d7678 = Some (Load SZ8 true 9 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d767c : bv 32 := 0x02010113.
Lemma F_d767c : fetch_word Plain.M.loaded_segments (0xd76c4 : word) = Some W_d767c.
Proof. vm_refl. Qed.
Lemma D_d767c : decode_any W_d767c = Some (OpImm ALU_ADD 2 2 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d7680 : bv 32 := 0xfb5ff06f.
Lemma F_d7680 : fetch_word Plain.M.loaded_segments (0xd76c8 : word) = Some W_d7680.
Proof. vm_refl. Qed.
Lemma D_d7680 : decode_any W_d7680 = Some (Jal 0 2097076, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d7684 : bv 32 := 0xff010113.
Lemma F_d7684 : fetch_word Plain.M.loaded_segments (0xd76cc : word) = Some W_d7684.
Proof. vm_refl. Qed.
Lemma D_d7684 : decode_any W_d7684 = Some (OpImm ALU_ADD 2 2 4080, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d7688 : bv 32 := 0x00113423.
Lemma F_d7688 : fetch_word Plain.M.loaded_segments (0xd76d0 : word) = Some W_d7688.
Proof. vm_refl. Qed.
Lemma D_d7688 : decode_any W_d7688 = Some (Store SZ8 2 1 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d768c : bv 32 := 0x00813023.
Lemma F_d768c : fetch_word Plain.M.loaded_segments (0xd76d4 : word) = Some W_d768c.
Proof. vm_refl. Qed.
Lemma D_d768c : decode_any W_d768c = Some (Store SZ8 2 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d7690 : bv 32 := 0x00000593.
Lemma F_d7690 : fetch_word Plain.M.loaded_segments (0xd76d8 : word) = Some W_d7690.
Proof. vm_refl. Qed.
Lemma D_d7690 : decode_any W_d7690 = Some (OpImm ALU_ADD 11 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d7694 : bv 32 := 0x00020613.
Lemma F_d7694 : fetch_word Plain.M.loaded_segments (0xd76dc : word) = Some W_d7694.
Proof. vm_refl. Qed.
Lemma D_d7694 : decode_any W_d7694 = Some (OpImm ALU_ADD 12 4 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d7698 : bv 32 := 0xf5862603.
Lemma F_d7698 : fetch_word Plain.M.loaded_segments (0xd76e0 : word) = Some W_d7698.
Proof. vm_refl. Qed.
Lemma D_d7698 : decode_any W_d7698 = Some (Load SZ4 true 12 12 3928, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d769c : bv 32 := 0x00049697.
Lemma F_d769c : fetch_word Plain.M.loaded_segments (0xd76e4 : word) = Some W_d769c.
Proof. vm_refl. Qed.
Lemma D_d769c : decode_any W_d769c = Some (Auipc 13 73, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d76a0 : bv 32 := 0x82c68693.
Lemma F_d76a0 : fetch_word Plain.M.loaded_segments (0xd76e8 : word) = Some W_d76a0.
Proof. vm_refl. Qed.
Lemma D_d76a0 : decode_any W_d76a0 = Some (OpImm ALU_ADD 13 13 2092, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d76a4 : bv 32 := 0x1606a72f.
Lemma F_d76a4 : fetch_word Plain.M.loaded_segments (0xd76ec : word) = Some W_d76a4.
Proof. vm_refl. Qed.
Lemma D_d76a4 : decode_any W_d76a4 = Some (Lr AW true true 14 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d76a8 : bv 32 := 0x00b71663.
Lemma F_d76a8 : fetch_word Plain.M.loaded_segments (0xd76f0 : word) = Some W_d76a8.
Proof. vm_refl. Qed.
Lemma D_d76a8 : decode_any W_d76a8 = Some (Branch BC_NE 14 11 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d76ac : bv 32 := 0x1ec6a7af.
Lemma F_d76ac : fetch_word Plain.M.loaded_segments (0xd76f4 : word) = Some W_d76ac.
Proof. vm_refl. Qed.
Lemma D_d76ac : decode_any W_d76ac = Some (Sc AW true true 15 13 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d76b0 : bv 32 := 0xfe079ae3.
Lemma F_d76b0 : fetch_word Plain.M.loaded_segments (0xd76f8 : word) = Some W_d76b0.
Proof. vm_refl. Qed.
Lemma D_d76b0 : decode_any W_d76b0 = Some (Branch BC_NE 15 0 8180, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d76b4 : bv 32 := 0x0007059b.
Lemma F_d76b4 : fetch_word Plain.M.loaded_segments (0xd76fc : word) = Some W_d76b4.
Proof. vm_refl. Qed.
Lemma D_d76b4 : decode_any W_d76b4 = Some (OpImm32 11 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d76b8 : bv 32 := 0x02c58263.
Lemma F_d76b8 : fetch_word Plain.M.loaded_segments (0xd7700 : word) = Some W_d76b8.
Proof. vm_refl. Qed.
Lemma D_d76b8 : decode_any W_d76b8 = Some (Branch BC_EQ 11 12 36, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d76bc : bv 32 := 0x02058263.
Lemma F_d76bc : fetch_word Plain.M.loaded_segments (0xd7704 : word) = Some W_d76bc.
Proof. vm_refl. Qed.
Lemma D_d76bc : decode_any W_d76bc = Some (Branch BC_EQ 11 0 36, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d76c0 : bv 32 := 0x04900893.
Lemma F_d76c0 : fetch_word Plain.M.loaded_segments (0xd7708 : word) = Some W_d76c0.
Proof. vm_refl. Qed.
Lemma D_d76c0 : decode_any W_d76c0 = Some (OpImm ALU_ADD 17 0 73, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d76c4 : bv 32 := 0x00000593.
Lemma F_d76c4 : fetch_word Plain.M.loaded_segments (0xd770c : word) = Some W_d76c4.
Proof. vm_refl. Qed.
Lemma D_d76c4 : decode_any W_d76c4 = Some (OpImm ALU_ADD 11 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d76c8 : bv 32 := 0x00000613.
Lemma F_d76c8 : fetch_word Plain.M.loaded_segments (0xd7710 : word) = Some W_d76c8.
Proof. vm_refl. Qed.
Lemma D_d76c8 : decode_any W_d76c8 = Some (OpImm ALU_ADD 12 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d76cc : bv 32 := 0x00000693.
Lemma F_d76cc : fetch_word Plain.M.loaded_segments (0xd7714 : word) = Some W_d76cc.
Proof. vm_refl. Qed.
Lemma D_d76cc : decode_any W_d76cc = Some (OpImm ALU_ADD 13 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d76d0 : bv 32 := 0x00000513.
Lemma F_d76d0 : fetch_word Plain.M.loaded_segments (0xd7718 : word) = Some W_d76d0.
Proof. vm_refl. Qed.
Lemma D_d76d0 : decode_any W_d76d0 = Some (OpImm ALU_ADD 10 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d76d4 : bv 32 := 0x00000073.
Lemma F_d76d4 : fetch_word Plain.M.loaded_segments (0xd771c : word) = Some W_d76d4.
Proof. vm_refl. Qed.
Lemma E_d76d4 : is_ecall W_d76d4 = true.
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d76d8 : bv 32 := 0xff9ff06f.
Lemma F_d76d8 : fetch_word Plain.M.loaded_segments (0xd7720 : word) = Some W_d76d8.
Proof. vm_refl. Qed.
Lemma D_d76d8 : decode_any W_d76d8 = Some (Jal 0 2097144, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d76dc : bv 32 := 0x00000023.
Lemma F_d76dc : fetch_word Plain.M.loaded_segments (0xd7724 : word) = Some W_d76dc.
Proof. vm_refl. Qed.
Lemma D_d76dc : decode_any W_d76dc = Some (Store SZ1 0 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d76e0 : bv 32 := 0x00050413.
Lemma F_d76e0 : fetch_word Plain.M.loaded_segments (0xd7728 : word) = Some W_d76e0.
Proof. vm_refl. Qed.
Lemma D_d76e0 : decode_any W_d76e0 = Some (OpImm ALU_ADD 8 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d76e4 : bv 32 := 0xdbdff0ef.
Lemma F_d76e4 : fetch_word Plain.M.loaded_segments (0xd772c : word) = Some W_d76e4.
Proof. vm_refl. Qed.
Lemma D_d76e4 : decode_any W_d76e4 = Some (Jal 1 2096572, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d76e8 : bv 32 := 0xf51ff0ef.
Lemma F_d76e8 : fetch_word Plain.M.loaded_segments (0xd7730 : word) = Some W_d76e8.
Proof. vm_refl. Qed.
Lemma D_d76e8 : decode_any W_d76e8 = Some (Jal 1 2096976, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d76ec : bv 32 := 0x4d9030ef.
Lemma F_d76ec : fetch_word Plain.M.loaded_segments (0xd7734 : word) = Some W_d76ec.
Proof. vm_refl. Qed.
Lemma D_d76ec : decode_any W_d76ec = Some (Jal 1 15576, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d76f0 : bv 32 := 0x00040513.
Lemma F_d76f0 : fetch_word Plain.M.loaded_segments (0xd7738 : word) = Some W_d76f0.
Proof. vm_refl. Qed.
Lemma D_d76f0 : decode_any W_d76f0 = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_d76f4 : bv 32 := 0xd61ff0ef.
Lemma F_d76f4 : fetch_word Plain.M.loaded_segments (0xd773c : word) = Some W_d76f4.
Proof. vm_refl. Qed.
Lemma D_d76f4 : decode_any W_d76f4 = Some (Jal 1 2096480, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_e6a10 : bv 32 := 0x00039597.
Lemma F_e6a10 : fetch_word Plain.M.loaded_segments (0xe6a58 : word) = Some W_e6a10.
Proof. vm_refl. Qed.
Lemma D_e6a10 : decode_any W_e6a10 = Some (Auipc 11 57, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_e6a14 : bv 32 := 0x4e358683.
Lemma F_e6a14 : fetch_word Plain.M.loaded_segments (0xe6a5c : word) = Some W_e6a14.
Proof. vm_refl. Qed.
Lemma D_e6a14 : decode_any W_e6a14 = Some (Load SZ1 true 13 11 1251, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_e6a18 : bv 32 := 0x1e068863.
Lemma F_e6a18 : fetch_word Plain.M.loaded_segments (0xe6a60 : word) = Some W_e6a18.
Proof. vm_refl. Qed.
Lemma D_e6a18 : decode_any W_e6a18 = Some (Branch BC_EQ 13 0 496, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_e6c08 : bv 32 := 0x00008067.
Lemma F_e6c08 : fetch_word Plain.M.loaded_segments (0xe6c50 : word) = Some W_e6c08.
Proof. vm_refl. Qed.
Lemma D_e6c08 : decode_any W_e6c08 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_e6c98 : bv 32 := 0x00052583.
Lemma F_e6c98 : fetch_word Plain.M.loaded_segments (0xe6ce0 : word) = Some W_e6c98.
Proof. vm_refl. Qed.
Lemma D_e6c98 : decode_any W_e6c98 = Some (Load SZ4 true 11 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_e6c9c : bv 32 := 0x0005c463.
Lemma F_e6c9c : fetch_word Plain.M.loaded_segments (0xe6ce4 : word) = Some W_e6c9c.
Proof. vm_refl. Qed.
Lemma D_e6c9c : decode_any W_e6c9c = Some (Branch BC_LT 11 0 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_e6ca0 : bv 32 := 0x00008067.
Lemma F_e6ca0 : fetch_word Plain.M.loaded_segments (0xe6ce8 : word) = Some W_e6ca0.
Proof. vm_refl. Qed.
Lemma D_e6ca0 : decode_any W_e6ca0 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

