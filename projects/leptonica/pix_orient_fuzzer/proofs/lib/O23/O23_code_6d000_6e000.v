(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
(* [comment removed for export] *)

From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.H Require GcFlushS23.   (* [comment removed for export] *)
From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.leptonica.pix_orient_fuzzer.images Require Import Plain.
Open Scope bv_scope.
#[local] Hint Extern 0 (BvWf _ _) => (lazymatch goal with |- BvWf ?n ?v => is_closed_term n; is_closed_term v end; exact I) : typeclass_instances.   (* [comment removed for export] *)

(* [comment removed for export] *)
Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

(* [comment removed for export] *)




(* [comment removed for export] *)
Definition W_6d000 : bv 32 := 0x00c13823.
Lemma F_6d000 : fetch_word Plain.M.loaded_segments (0x6d058 : word) = Some W_6d000.
Proof. vm_refl. Qed.
Lemma D_6d000 : decode_any W_6d000 = Some (Store SZ8 2 12 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6d004 : bv 32 := 0x00060c63.
Lemma F_6d004 : fetch_word Plain.M.loaded_segments (0x6d05c : word) = Some W_6d004.
Proof. vm_refl. Qed.
Lemma D_6d004 : decode_any W_6d004 = Some (Branch BC_EQ 12 0 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6d01c : bv 32 := 0x02a5b823.
Lemma F_6d01c : fetch_word Plain.M.loaded_segments (0x6d074 : word) = Some W_6d01c.
Proof. vm_refl. Qed.
Lemma D_6d01c : decode_any W_6d01c = Some (Store SZ8 11 10 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6d020 : bv 32 := 0x01010613.
Lemma F_6d020 : fetch_word Plain.M.loaded_segments (0x6d078 : word) = Some W_6d020.
Proof. vm_refl. Qed.
Lemma D_6d020 : decode_any W_6d020 = Some (OpImm ALU_ADD 12 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6d024 : bv 32 := 0x00000593.
Lemma F_6d024 : fetch_word Plain.M.loaded_segments (0x6d07c : word) = Some W_6d024.
Proof. vm_refl. Qed.
Lemma D_6d024 : decode_any W_6d024 = Some (OpImm ALU_ADD 11 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6d028 : bv 32 := 0x661030ef.
Lemma F_6d028 : fetch_word Plain.M.loaded_segments (0x6d080 : word) = Some W_6d028.
Proof. vm_refl. Qed.
Lemma D_6d028 : decode_any W_6d028 = Some (Jal 1 15968, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6d02c : bv 32 := 0x01012503.
Lemma F_6d02c : fetch_word Plain.M.loaded_segments (0x6d084 : word) = Some W_6d02c.
Proof. vm_refl. Qed.
Lemma D_6d02c : decode_any W_6d02c = Some (Load SZ4 true 10 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6d030 : bv 32 := 0x02051863.
Lemma F_6d030 : fetch_word Plain.M.loaded_segments (0x6d088 : word) = Some W_6d030.
Proof. vm_refl. Qed.
Lemma D_6d030 : decode_any W_6d030 = Some (Branch BC_NE 10 0 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6d060 : bv 32 := 0x00000513.
Lemma F_6d060 : fetch_word Plain.M.loaded_segments (0x6d0b8 : word) = Some W_6d060.
Proof. vm_refl. Qed.
Lemma D_6d060 : decode_any W_6d060 = Some (OpImm ALU_ADD 10 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6d064 : bv 32 := 0x0ec0006f.
Lemma F_6d064 : fetch_word Plain.M.loaded_segments (0x6d0bc : word) = Some W_6d064.
Proof. vm_refl. Qed.
Lemma D_6d064 : decode_any W_6d064 = Some (Jal 0 236, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6d11c : bv 32 := 0x000a5517.
Lemma F_6d11c : fetch_word Plain.M.loaded_segments (0x6d174 : word) = Some W_6d11c.
Proof. vm_refl. Qed.
Lemma D_6d11c : decode_any W_6d11c = Some (Auipc 10 165, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6d120 : bv 32 := 0x45453503.
Lemma F_6d120 : fetch_word Plain.M.loaded_segments (0x6d178 : word) = Some W_6d120.
Proof. vm_refl. Qed.
Lemma D_6d120 : decode_any W_6d120 = Some (Load SZ8 true 10 10 1108, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6d124 : bv 32 := 0x00052503.
Lemma F_6d124 : fetch_word Plain.M.loaded_segments (0x6d17c : word) = Some W_6d124.
Proof. vm_refl. Qed.
Lemma D_6d124 : decode_any W_6d124 = Some (Load SZ4 true 10 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6d128 : bv 32 := 0x00500593.
Lemma F_6d128 : fetch_word Plain.M.loaded_segments (0x6d180 : word) = Some W_6d128.
Proof. vm_refl. Qed.
Lemma D_6d128 : decode_any W_6d128 = Some (OpImm ALU_ADD 11 0 5, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6d12c : bv 32 := 0x02a5c063.
Lemma F_6d12c : fetch_word Plain.M.loaded_segments (0x6d184 : word) = Some W_6d12c.
Proof. vm_refl. Qed.
Lemma D_6d12c : decode_any W_6d12c = Some (Branch BC_LT 11 10 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6d130 : bv 32 := 0xfffa5517.
Lemma F_6d130 : fetch_word Plain.M.loaded_segments (0x6d188 : word) = Some W_6d130.
Proof. vm_refl. Qed.
Lemma D_6d130 : decode_any W_6d130 = Some (Auipc 10 1048485, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6d134 : bv 32 := 0xfffa6597.
Lemma F_6d134 : fetch_word Plain.M.loaded_segments (0x6d18c : word) = Some W_6d134.
Proof. vm_refl. Qed.
Lemma D_6d134 : decode_any W_6d134 = Some (Auipc 11 1048486, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6d138 : bv 32 := 0x56050513.
Lemma F_6d138 : fetch_word Plain.M.loaded_segments (0x6d190 : word) = Some W_6d138.
Proof. vm_refl. Qed.
Lemma D_6d138 : decode_any W_6d138 = Some (OpImm ALU_ADD 10 10 1376, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6d13c : bv 32 := 0xc6758593.
Lemma F_6d13c : fetch_word Plain.M.loaded_segments (0x6d194 : word) = Some W_6d13c.
Proof. vm_refl. Qed.
Lemma D_6d13c : decode_any W_6d13c = Some (OpImm ALU_ADD 11 11 3175, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6d140 : bv 32 := 0x00100613.
Lemma F_6d140 : fetch_word Plain.M.loaded_segments (0x6d198 : word) = Some W_6d140.
Proof. vm_refl. Qed.
Lemma D_6d140 : decode_any W_6d140 = Some (OpImm ALU_ADD 12 0 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6d144 : bv 32 := 0xeb1f50ef.
Lemma F_6d144 : fetch_word Plain.M.loaded_segments (0x6d19c : word) = Some W_6d144.
Proof. vm_refl. Qed.
Lemma D_6d144 : decode_any W_6d144 = Some (Jal 1 2055856, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6d148 : bv 32 := 0x0080006f.
Lemma F_6d148 : fetch_word Plain.M.loaded_segments (0x6d1a0 : word) = Some W_6d148.
Proof. vm_refl. Qed.
Lemma D_6d148 : decode_any W_6d148 = Some (Jal 0 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6d150 : bv 32 := 0x02813083.
Lemma F_6d150 : fetch_word Plain.M.loaded_segments (0x6d1a8 : word) = Some W_6d150.
Proof. vm_refl. Qed.
Lemma D_6d150 : decode_any W_6d150 = Some (Load SZ8 true 1 2 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6d154 : bv 32 := 0x02013403.
Lemma F_6d154 : fetch_word Plain.M.loaded_segments (0x6d1ac : word) = Some W_6d154.
Proof. vm_refl. Qed.
Lemma D_6d154 : decode_any W_6d154 = Some (Load SZ8 true 8 2 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6d158 : bv 32 := 0x01813483.
Lemma F_6d158 : fetch_word Plain.M.loaded_segments (0x6d1b0 : word) = Some W_6d158.
Proof. vm_refl. Qed.
Lemma D_6d158 : decode_any W_6d158 = Some (Load SZ8 true 9 2 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6d15c : bv 32 := 0x03010113.
Lemma F_6d15c : fetch_word Plain.M.loaded_segments (0x6d1b4 : word) = Some W_6d15c.
Proof. vm_refl. Qed.
Lemma D_6d15c : decode_any W_6d15c = Some (OpImm ALU_ADD 2 2 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6d160 : bv 32 := 0x00008067.
Lemma F_6d160 : fetch_word Plain.M.loaded_segments (0x6d1b8 : word) = Some W_6d160.
Proof. vm_refl. Qed.
Lemma D_6d160 : decode_any W_6d160 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6d428 : bv 32 := 0xfd010113.
Lemma F_6d428 : fetch_word Plain.M.loaded_segments (0x6d480 : word) = Some W_6d428.
Proof. vm_refl. Qed.
Lemma D_6d428 : decode_any W_6d428 = Some (OpImm ALU_ADD 2 2 4048, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6d42c : bv 32 := 0x02113423.
Lemma F_6d42c : fetch_word Plain.M.loaded_segments (0x6d484 : word) = Some W_6d42c.
Proof. vm_refl. Qed.
Lemma D_6d42c : decode_any W_6d42c = Some (Store SZ8 2 1 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6d430 : bv 32 := 0x02813023.
Lemma F_6d430 : fetch_word Plain.M.loaded_segments (0x6d488 : word) = Some W_6d430.
Proof. vm_refl. Qed.
Lemma D_6d430 : decode_any W_6d430 = Some (Store SZ8 2 8 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6d434 : bv 32 := 0x00913c23.
Lemma F_6d434 : fetch_word Plain.M.loaded_segments (0x6d48c : word) = Some W_6d434.
Proof. vm_refl. Qed.
Lemma D_6d434 : decode_any W_6d434 = Some (Store SZ8 2 9 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6d438 : bv 32 := 0x01213823.
Lemma F_6d438 : fetch_word Plain.M.loaded_segments (0x6d490 : word) = Some W_6d438.
Proof. vm_refl. Qed.
Lemma D_6d438 : decode_any W_6d438 = Some (Store SZ8 2 18 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6d43c : bv 32 := 0x01313423.
Lemma F_6d43c : fetch_word Plain.M.loaded_segments (0x6d494 : word) = Some W_6d43c.
Proof. vm_refl. Qed.
Lemma D_6d43c : decode_any W_6d43c = Some (Store SZ8 2 19 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6d440 : bv 32 := 0x00050413.
Lemma F_6d440 : fetch_word Plain.M.loaded_segments (0x6d498 : word) = Some W_6d440.
Proof. vm_refl. Qed.
Lemma D_6d440 : decode_any W_6d440 = Some (OpImm ALU_ADD 8 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6d444 : bv 32 := 0x06058063.
Lemma F_6d444 : fetch_word Plain.M.loaded_segments (0x6d49c : word) = Some W_6d444.
Proof. vm_refl. Qed.
Lemma D_6d444 : decode_any W_6d444 = Some (Branch BC_EQ 11 0 96, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6d448 : bv 32 := 0x00058493.
Lemma F_6d448 : fetch_word Plain.M.loaded_segments (0x6d4a0 : word) = Some W_6d448.
Proof. vm_refl. Qed.
Lemma D_6d448 : decode_any W_6d448 = Some (OpImm ALU_ADD 9 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6d44c : bv 32 := 0x18858e63.
Lemma F_6d44c : fetch_word Plain.M.loaded_segments (0x6d4a4 : word) = Some W_6d44c.
Proof. vm_refl. Qed.
Lemma D_6d44c : decode_any W_6d44c = Some (Branch BC_EQ 11 8 412, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6d450 : bv 32 := 0x0044a503.
Lemma F_6d450 : fetch_word Plain.M.loaded_segments (0x6d4a8 : word) = Some W_6d450.
Proof. vm_refl. Qed.
Lemma D_6d450 : decode_any W_6d450 = Some (Load SZ4 true 10 9 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6d454 : bv 32 := 0x0104a583.
Lemma F_6d454 : fetch_word Plain.M.loaded_segments (0x6d4ac : word) = Some W_6d454.
Proof. vm_refl. Qed.
Lemma D_6d454 : decode_any W_6d454 = Some (Load SZ4 true 11 9 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6d458 : bv 32 := 0x02a58533.
Lemma F_6d458 : fetch_word Plain.M.loaded_segments (0x6d4b0 : word) = Some W_6d458.
Proof. vm_refl. Qed.
Lemma D_6d458 : decode_any W_6d458 = Some (Mul M_MUL 10 11 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6d45c : bv 32 := 0x0025191b.
Lemma F_6d45c : fetch_word Plain.M.loaded_segments (0x6d4b4 : word) = Some W_6d45c.
Proof. vm_refl. Qed.
Lemma D_6d45c : decode_any W_6d45c = Some (ShiftImm32 ALU_SLL 18 10 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6d460 : bv 32 := 0x08040463.
Lemma F_6d460 : fetch_word Plain.M.loaded_segments (0x6d4b8 : word) = Some W_6d460.
Proof. vm_refl. Qed.
Lemma D_6d460 : decode_any W_6d460 = Some (Branch BC_EQ 8 0 136, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6d49c : bv 32 := 0x00000613.
Lemma F_6d49c : fetch_word Plain.M.loaded_segments (0x6d4f4 : word) = Some W_6d49c.
Proof. vm_refl. Qed.
Lemma D_6d49c : decode_any W_6d49c = Some (OpImm ALU_ADD 12 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6d4a0 : bv 32 := 0x02c0006f.
Lemma F_6d4a0 : fetch_word Plain.M.loaded_segments (0x6d4f8 : word) = Some W_6d4a0.
Proof. vm_refl. Qed.
Lemma D_6d4a0 : decode_any W_6d4a0 = Some (Jal 0 44, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6d4cc : bv 32 := 0x02813083.
Lemma F_6d4cc : fetch_word Plain.M.loaded_segments (0x6d524 : word) = Some W_6d4cc.
Proof. vm_refl. Qed.
Lemma D_6d4cc : decode_any W_6d4cc = Some (Load SZ8 true 1 2 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6d4d0 : bv 32 := 0x02013403.
Lemma F_6d4d0 : fetch_word Plain.M.loaded_segments (0x6d528 : word) = Some W_6d4d0.
Proof. vm_refl. Qed.
Lemma D_6d4d0 : decode_any W_6d4d0 = Some (Load SZ8 true 8 2 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6d4d4 : bv 32 := 0x01813483.
Lemma F_6d4d4 : fetch_word Plain.M.loaded_segments (0x6d52c : word) = Some W_6d4d4.
Proof. vm_refl. Qed.
Lemma D_6d4d4 : decode_any W_6d4d4 = Some (Load SZ8 true 9 2 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6d4d8 : bv 32 := 0x01013903.
Lemma F_6d4d8 : fetch_word Plain.M.loaded_segments (0x6d530 : word) = Some W_6d4d8.
Proof. vm_refl. Qed.
Lemma D_6d4d8 : decode_any W_6d4d8 = Some (Load SZ8 true 18 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6d4dc : bv 32 := 0x00813983.
Lemma F_6d4dc : fetch_word Plain.M.loaded_segments (0x6d534 : word) = Some W_6d4dc.
Proof. vm_refl. Qed.
Lemma D_6d4dc : decode_any W_6d4dc = Some (Load SZ8 true 19 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6d4e0 : bv 32 := 0x03010113.
Lemma F_6d4e0 : fetch_word Plain.M.loaded_segments (0x6d538 : word) = Some W_6d4e0.
Proof. vm_refl. Qed.
Lemma D_6d4e0 : decode_any W_6d4e0 = Some (OpImm ALU_ADD 2 2 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6d4e4 : bv 32 := 0xbe1f506f.
Lemma F_6d4e4 : fetch_word Plain.M.loaded_segments (0x6d53c : word) = Some W_6d4e4.
Proof. vm_refl. Qed.
Lemma D_6d4e4 : decode_any W_6d4e4 = Some (Jal 0 2055136, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6d4e8 : bv 32 := 0x00048513.
Lemma F_6d4e8 : fetch_word Plain.M.loaded_segments (0x6d540 : word) = Some W_6d4e8.
Proof. vm_refl. Qed.
Lemma D_6d4e8 : decode_any W_6d4e8 = Some (OpImm ALU_ADD 10 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6d4ec : bv 32 := 0xf7cff0ef.
Lemma F_6d4ec : fetch_word Plain.M.loaded_segments (0x6d544 : word) = Some W_6d4ec.
Proof. vm_refl. Qed.
Lemma D_6d4ec : decode_any W_6d4ec = Some (Jal 1 2094972, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6d4f0 : bv 32 := 0x04050263.
Lemma F_6d4f0 : fetch_word Plain.M.loaded_segments (0x6d548 : word) = Some W_6d4f0.
Proof. vm_refl. Qed.
Lemma D_6d4f0 : decode_any W_6d4f0 = Some (Branch BC_EQ 10 0 68, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6d4f4 : bv 32 := 0x00050413.
Lemma F_6d4f4 : fetch_word Plain.M.loaded_segments (0x6d54c : word) = Some W_6d4f4.
Proof. vm_refl. Qed.
Lemma D_6d4f4 : decode_any W_6d4f4 = Some (OpImm ALU_ADD 8 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6d4f8 : bv 32 := 0x00456583.
Lemma F_6d4f8 : fetch_word Plain.M.loaded_segments (0x6d550 : word) = Some W_6d4f8.
Proof. vm_refl. Qed.
Lemma D_6d4f8 : decode_any W_6d4f8 = Some (Load SZ4 false 11 10 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6d4fc : bv 32 := 0x01056603.
Lemma F_6d4fc : fetch_word Plain.M.loaded_segments (0x6d554 : word) = Some W_6d4fc.
Proof. vm_refl. Qed.
Lemma D_6d4fc : decode_any W_6d4fc = Some (Load SZ4 false 12 10 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6d500 : bv 32 := 0x03853503.
Lemma F_6d500 : fetch_word Plain.M.loaded_segments (0x6d558 : word) = Some W_6d500.
Proof. vm_refl. Qed.
Lemma D_6d500 : decode_any W_6d500 = Some (Load SZ8 true 10 10 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6d504 : bv 32 := 0x02b60633.
Lemma F_6d504 : fetch_word Plain.M.loaded_segments (0x6d55c : word) = Some W_6d504.
Proof. vm_refl. Qed.
Lemma D_6d504 : decode_any W_6d504 = Some (Mul M_MUL 12 12 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6d508 : bv 32 := 0x00261613.
Lemma F_6d508 : fetch_word Plain.M.loaded_segments (0x6d560 : word) = Some W_6d508.
Proof. vm_refl. Qed.
Lemma D_6d508 : decode_any W_6d508 = Some (ShiftImm ALU_SLL 12 12 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6d50c : bv 32 := 0x00000593.
Lemma F_6d50c : fetch_word Plain.M.loaded_segments (0x6d564 : word) = Some W_6d50c.
Proof. vm_refl. Qed.
Lemma D_6d50c : decode_any W_6d50c = Some (OpImm ALU_ADD 11 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6d510 : bv 32 := 0x4c99c0ef.
Lemma F_6d510 : fetch_word Plain.M.loaded_segments (0x6d568 : word) = Some W_6d510.
Proof. vm_refl. Qed.
Lemma D_6d510 : decode_any W_6d510 = Some (Jal 1 642248, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6d514 : bv 32 := 0x0c40006f.
Lemma F_6d514 : fetch_word Plain.M.loaded_segments (0x6d56c : word) = Some W_6d514.
Proof. vm_refl. Qed.
Lemma D_6d514 : decode_any W_6d514 = Some (Jal 0 196, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6d534 : bv 32 := 0x000a5517.
Lemma F_6d534 : fetch_word Plain.M.loaded_segments (0x6d58c : word) = Some W_6d534.
Proof. vm_refl. Qed.
Lemma D_6d534 : decode_any W_6d534 = Some (Auipc 10 165, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6d538 : bv 32 := 0x03c53983.
Lemma F_6d538 : fetch_word Plain.M.loaded_segments (0x6d590 : word) = Some W_6d538.
Proof. vm_refl. Qed.
Lemma D_6d538 : decode_any W_6d538 = Some (Load SZ8 true 19 10 60, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6d53c : bv 32 := 0x0009a503.
Lemma F_6d53c : fetch_word Plain.M.loaded_segments (0x6d594 : word) = Some W_6d53c.
Proof. vm_refl. Qed.
Lemma D_6d53c : decode_any W_6d53c = Some (Load SZ4 true 10 19 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6d540 : bv 32 := 0x00600593.
Lemma F_6d540 : fetch_word Plain.M.loaded_segments (0x6d598 : word) = Some W_6d540.
Proof. vm_refl. Qed.
Lemma D_6d540 : decode_any W_6d540 = Some (OpImm ALU_ADD 11 0 6, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6d544 : bv 32 := 0x04b55263.
Lemma F_6d544 : fetch_word Plain.M.loaded_segments (0x6d59c : word) = Some W_6d544.
Proof. vm_refl. Qed.
Lemma D_6d544 : decode_any W_6d544 = Some (Branch BC_GE 10 11 68, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6d548 : bv 32 := 0xfffa5517.
Lemma F_6d548 : fetch_word Plain.M.loaded_segments (0x6d5a0 : word) = Some W_6d548.
Proof. vm_refl. Qed.
Lemma D_6d548 : decode_any W_6d548 = Some (Auipc 10 1048485, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6d54c : bv 32 := 0xfffac597.
Lemma F_6d54c : fetch_word Plain.M.loaded_segments (0x6d5a4 : word) = Some W_6d54c.
Proof. vm_refl. Qed.
Lemma D_6d54c : decode_any W_6d54c = Some (Auipc 11 1048492, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6d550 : bv 32 := 0x13a50513.
Lemma F_6d550 : fetch_word Plain.M.loaded_segments (0x6d5a8 : word) = Some W_6d550.
Proof. vm_refl. Qed.
Lemma D_6d550 : decode_any W_6d550 = Some (OpImm ALU_ADD 10 10 314, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6d554 : bv 32 := 0xcd358593.
Lemma F_6d554 : fetch_word Plain.M.loaded_segments (0x6d5ac : word) = Some W_6d554.
Proof. vm_refl. Qed.
Lemma D_6d554 : decode_any W_6d554 = Some (OpImm ALU_ADD 11 11 3283, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6d558 : bv 32 := 0x00000613.
Lemma F_6d558 : fetch_word Plain.M.loaded_segments (0x6d5b0 : word) = Some W_6d558.
Proof. vm_refl. Qed.
Lemma D_6d558 : decode_any W_6d558 = Some (OpImm ALU_ADD 12 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6d55c : bv 32 := 0xb69f50ef.
Lemma F_6d55c : fetch_word Plain.M.loaded_segments (0x6d5b4 : word) = Some W_6d55c.
Proof. vm_refl. Qed.
Lemma D_6d55c : decode_any W_6d55c = Some (Jal 1 2055016, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6d560 : bv 32 := 0x00050413.
Lemma F_6d560 : fetch_word Plain.M.loaded_segments (0x6d5b8 : word) = Some W_6d560.
Proof. vm_refl. Qed.
Lemma D_6d560 : decode_any W_6d560 = Some (OpImm ALU_ADD 8 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6d564 : bv 32 := 0x06051a63.
Lemma F_6d564 : fetch_word Plain.M.loaded_segments (0x6d5bc : word) = Some W_6d564.
Proof. vm_refl. Qed.
Lemma D_6d564 : decode_any W_6d564 = Some (Branch BC_NE 10 0 116, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6d568 : bv 32 := 0x0009a503.
Lemma F_6d568 : fetch_word Plain.M.loaded_segments (0x6d5c0 : word) = Some W_6d568.
Proof. vm_refl. Qed.
Lemma D_6d568 : decode_any W_6d568 = Some (Load SZ4 true 10 19 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6d56c : bv 32 := 0x00500593.
Lemma F_6d56c : fetch_word Plain.M.loaded_segments (0x6d5c4 : word) = Some W_6d56c.
Proof. vm_refl. Qed.
Lemma D_6d56c : decode_any W_6d56c = Some (OpImm ALU_ADD 11 0 5, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6d570 : bv 32 := 0x00a5cc63.
Lemma F_6d570 : fetch_word Plain.M.loaded_segments (0x6d5c8 : word) = Some W_6d570.
Proof. vm_refl. Qed.
Lemma D_6d570 : decode_any W_6d570 = Some (Branch BC_LT 11 10 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6d574 : bv 32 := 0xfffa5517.
Lemma F_6d574 : fetch_word Plain.M.loaded_segments (0x6d5cc : word) = Some W_6d574.
Proof. vm_refl. Qed.
Lemma D_6d574 : decode_any W_6d574 = Some (Auipc 10 1048485, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6d578 : bv 32 := 0xfffab597.
Lemma F_6d578 : fetch_word Plain.M.loaded_segments (0x6d5d0 : word) = Some W_6d578.
Proof. vm_refl. Qed.
Lemma D_6d578 : decode_any W_6d578 = Some (Auipc 11 1048491, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6d57c : bv 32 := 0x10e50513.
Lemma F_6d57c : fetch_word Plain.M.loaded_segments (0x6d5d4 : word) = Some W_6d57c.
Proof. vm_refl. Qed.
Lemma D_6d57c : decode_any W_6d57c = Some (OpImm ALU_ADD 10 10 270, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6d580 : bv 32 := 0x5c358593.
Lemma F_6d580 : fetch_word Plain.M.loaded_segments (0x6d5d8 : word) = Some W_6d580.
Proof. vm_refl. Qed.
Lemma D_6d580 : decode_any W_6d580 = Some (OpImm ALU_ADD 11 11 1475, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6d584 : bv 32 := 0xf19ff06f.
Lemma F_6d584 : fetch_word Plain.M.loaded_segments (0x6d5dc : word) = Some W_6d584.
Proof. vm_refl. Qed.
Lemma D_6d584 : decode_any W_6d584 = Some (Jal 0 2096920, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6d5d8 : bv 32 := 0x03843503.
Lemma F_6d5d8 : fetch_word Plain.M.loaded_segments (0x6d630 : word) = Some W_6d5d8.
Proof. vm_refl. Qed.
Lemma D_6d5d8 : decode_any W_6d5d8 = Some (Load SZ8 true 10 8 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6d5dc : bv 32 := 0x0384b583.
Lemma F_6d5dc : fetch_word Plain.M.loaded_segments (0x6d634 : word) = Some W_6d5dc.
Proof. vm_refl. Qed.
Lemma D_6d5dc : decode_any W_6d5dc = Some (Load SZ8 true 11 9 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6d5e0 : bv 32 := 0x00090613.
Lemma F_6d5e0 : fetch_word Plain.M.loaded_segments (0x6d638 : word) = Some W_6d5e0.
Proof. vm_refl. Qed.
Lemma D_6d5e0 : decode_any W_6d5e0 = Some (OpImm ALU_ADD 12 18 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6d5e4 : bv 32 := 0x6749c0ef.
Lemma F_6d5e4 : fetch_word Plain.M.loaded_segments (0x6d63c : word) = Some W_6d5e4.
Proof. vm_refl. Qed.
Lemma D_6d5e4 : decode_any W_6d5e4 = Some (Jal 1 640628, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6d5e8 : bv 32 := 0x00040513.
Lemma F_6d5e8 : fetch_word Plain.M.loaded_segments (0x6d640 : word) = Some W_6d5e8.
Proof. vm_refl. Qed.
Lemma D_6d5e8 : decode_any W_6d5e8 = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6d5ec : bv 32 := 0x02813083.
Lemma F_6d5ec : fetch_word Plain.M.loaded_segments (0x6d644 : word) = Some W_6d5ec.
Proof. vm_refl. Qed.
Lemma D_6d5ec : decode_any W_6d5ec = Some (Load SZ8 true 1 2 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6d5f0 : bv 32 := 0x02013403.
Lemma F_6d5f0 : fetch_word Plain.M.loaded_segments (0x6d648 : word) = Some W_6d5f0.
Proof. vm_refl. Qed.
Lemma D_6d5f0 : decode_any W_6d5f0 = Some (Load SZ8 true 8 2 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6d5f4 : bv 32 := 0x01813483.
Lemma F_6d5f4 : fetch_word Plain.M.loaded_segments (0x6d64c : word) = Some W_6d5f4.
Proof. vm_refl. Qed.
Lemma D_6d5f4 : decode_any W_6d5f4 = Some (Load SZ8 true 9 2 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6d5f8 : bv 32 := 0x01013903.
Lemma F_6d5f8 : fetch_word Plain.M.loaded_segments (0x6d650 : word) = Some W_6d5f8.
Proof. vm_refl. Qed.
Lemma D_6d5f8 : decode_any W_6d5f8 = Some (Load SZ8 true 18 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6d5fc : bv 32 := 0x00813983.
Lemma F_6d5fc : fetch_word Plain.M.loaded_segments (0x6d654 : word) = Some W_6d5fc.
Proof. vm_refl. Qed.
Lemma D_6d5fc : decode_any W_6d5fc = Some (Load SZ8 true 19 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6d600 : bv 32 := 0x03010113.
Lemma F_6d600 : fetch_word Plain.M.loaded_segments (0x6d658 : word) = Some W_6d600.
Proof. vm_refl. Qed.
Lemma D_6d600 : decode_any W_6d600 = Some (OpImm ALU_ADD 2 2 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6d604 : bv 32 := 0x00008067.
Lemma F_6d604 : fetch_word Plain.M.loaded_segments (0x6d65c : word) = Some W_6d604.
Proof. vm_refl. Qed.
Lemma D_6d604 : decode_any W_6d604 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6d9e8 : bv 32 := 0x00050663.
Lemma F_6d9e8 : fetch_word Plain.M.loaded_segments (0x6da40 : word) = Some W_6d9e8.
Proof. vm_refl. Qed.
Lemma D_6d9e8 : decode_any W_6d9e8 = Some (Branch BC_EQ 10 0 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6d9ec : bv 32 := 0x03853503.
Lemma F_6d9ec : fetch_word Plain.M.loaded_segments (0x6da44 : word) = Some W_6d9ec.
Proof. vm_refl. Qed.
Lemma D_6d9ec : decode_any W_6d9ec = Some (Load SZ8 true 10 10 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6d9f0 : bv 32 := 0x00008067.
Lemma F_6d9f0 : fetch_word Plain.M.loaded_segments (0x6da48 : word) = Some W_6d9f0.
Proof. vm_refl. Qed.
Lemma D_6d9f0 : decode_any W_6d9f0 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6da28 : bv 32 := 0x00050663.
Lemma F_6da28 : fetch_word Plain.M.loaded_segments (0x6da80 : word) = Some W_6da28.
Proof. vm_refl. Qed.
Lemma D_6da28 : decode_any W_6da28 = Some (Branch BC_EQ 10 0 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6da2c : bv 32 := 0x03053503.
Lemma F_6da2c : fetch_word Plain.M.loaded_segments (0x6da84 : word) = Some W_6da2c.
Proof. vm_refl. Qed.
Lemma D_6da2c : decode_any W_6da2c = Some (Load SZ8 true 10 10 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6da30 : bv 32 := 0x00008067.
Lemma F_6da30 : fetch_word Plain.M.loaded_segments (0x6da88 : word) = Some W_6da30.
Proof. vm_refl. Qed.
Lemma D_6da30 : decode_any W_6da30 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.
