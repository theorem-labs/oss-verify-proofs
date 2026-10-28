(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
(* [comment removed for export] *)

From OssFuzzTheorems.Proofs.leptonica.fhmtgen_fuzzer.lib.H Require GcFlushU10.   (* [comment removed for export] *)
From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OssFuzzTheorems.leptonica.fhmtgen_fuzzer.images Require Import Ubsan.
Open Scope bv_scope.
#[local] Hint Extern 0 (BvWf _ _) => (lazymatch goal with |- BvWf ?n ?v => is_closed_term n; is_closed_term v end; exact I) : typeclass_instances.   (* [comment removed for export] *)

(* [comment removed for export] *)
Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

(* [comment removed for export] *)
Definition W_15154 : bv 32 := 0xffffe517.
Lemma F_15154 : fetch_word Ubsan.M.loaded_segments (0x15154 : word) = Some W_15154.
Proof. vm_refl. Qed.
Lemma D_15154 : decode_any W_15154 = Some (Auipc 10 1048574, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15158 : bv 32 := 0x94450513.
Lemma F_15158 : fetch_word Ubsan.M.loaded_segments (0x15158 : word) = Some W_15158.
Proof. vm_refl. Qed.
Lemma D_15158 : decode_any W_15158 = Some (OpImm ALU_ADD 10 10 2372, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1515c : bv 32 := 0x00020597.
Lemma F_1515c : fetch_word Ubsan.M.loaded_segments (0x1515c : word) = Some W_1515c.
Proof. vm_refl. Qed.
Lemma D_1515c : decode_any W_1515c = Some (Auipc 11 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15160 : bv 32 := 0x1dc58593.
Lemma F_15160 : fetch_word Ubsan.M.loaded_segments (0x15160 : word) = Some W_15160.
Proof. vm_refl. Qed.
Lemma D_15160 : decode_any W_15160 = Some (OpImm ALU_ADD 11 11 476, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15164 : bv 32 := 0x000000ef.
Lemma F_15164 : fetch_word Ubsan.M.loaded_segments (0x15164 : word) = Some W_15164.
Proof. vm_refl. Qed.
Lemma D_15164 : decode_any W_15164 = Some (Jal 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15168 : bv 32 := 0x0040006f.
Lemma F_15168 : fetch_word Ubsan.M.loaded_segments (0x15168 : word) = Some W_15168.
Proof. vm_refl. Qed.
Lemma D_15168 : decode_any W_15168 = Some (Jal 0 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1516c : bv 32 := 0x00813083.
Lemma F_1516c : fetch_word Ubsan.M.loaded_segments (0x1516c : word) = Some W_1516c.
Proof. vm_refl. Qed.
Lemma D_1516c : decode_any W_1516c = Some (Load SZ8 true 1 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15170 : bv 32 := 0x00013403.
Lemma F_15170 : fetch_word Ubsan.M.loaded_segments (0x15170 : word) = Some W_15170.
Proof. vm_refl. Qed.
Lemma D_15170 : decode_any W_15170 = Some (Load SZ8 true 8 2 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15174 : bv 32 := 0x01010113.
Lemma F_15174 : fetch_word Ubsan.M.loaded_segments (0x15174 : word) = Some W_15174.
Proof. vm_refl. Qed.
Lemma D_15174 : decode_any W_15174 = Some (OpImm ALU_ADD 2 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15178 : bv 32 := 0x00008067.
Lemma F_15178 : fetch_word Ubsan.M.loaded_segments (0x15178 : word) = Some W_15178.
Proof. vm_refl. Qed.
Lemma D_15178 : decode_any W_15178 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1517c : bv 32 := 0xff010113.
Lemma F_1517c : fetch_word Ubsan.M.loaded_segments (0x1517c : word) = Some W_1517c.
Proof. vm_refl. Qed.
Lemma D_1517c : decode_any W_1517c = Some (OpImm ALU_ADD 2 2 4080, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15180 : bv 32 := 0x00113423.
Lemma F_15180 : fetch_word Ubsan.M.loaded_segments (0x15180 : word) = Some W_15180.
Proof. vm_refl. Qed.
Lemma D_15180 : decode_any W_15180 = Some (Store SZ8 2 1 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15184 : bv 32 := 0x00813023.
Lemma F_15184 : fetch_word Ubsan.M.loaded_segments (0x15184 : word) = Some W_15184.
Proof. vm_refl. Qed.
Lemma D_15184 : decode_any W_15184 = Some (Store SZ8 2 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15188 : bv 32 := 0x01010413.
Lemma F_15188 : fetch_word Ubsan.M.loaded_segments (0x15188 : word) = Some W_15188.
Proof. vm_refl. Qed.
Lemma D_15188 : decode_any W_15188 = Some (OpImm ALU_ADD 8 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1518c : bv 32 := 0x00020517.
Lemma F_1518c : fetch_word Ubsan.M.loaded_segments (0x1518c : word) = Some W_1518c.
Proof. vm_refl. Qed.
Lemma D_1518c : decode_any W_1518c = Some (Auipc 10 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15190 : bv 32 := 0x1ec50513.
Lemma F_15190 : fetch_word Ubsan.M.loaded_segments (0x15190 : word) = Some W_15190.
Proof. vm_refl. Qed.
Lemma D_15190 : decode_any W_15190 = Some (OpImm ALU_ADD 10 10 492, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15194 : bv 32 := 0x00054503.
Lemma F_15194 : fetch_word Ubsan.M.loaded_segments (0x15194 : word) = Some W_15194.
Proof. vm_refl. Qed.
Lemma D_15194 : decode_any W_15194 = Some (Load SZ1 false 10 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15198 : bv 32 := 0x00157513.
Lemma F_15198 : fetch_word Ubsan.M.loaded_segments (0x15198 : word) = Some W_15198.
Proof. vm_refl. Qed.
Lemma D_15198 : decode_any W_15198 = Some (OpImm ALU_AND 10 10 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1519c : bv 32 := 0x00050663.
Lemma F_1519c : fetch_word Ubsan.M.loaded_segments (0x1519c : word) = Some W_1519c.
Proof. vm_refl. Qed.
Lemma D_1519c : decode_any W_1519c = Some (Branch BC_EQ 10 0 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_151a0 : bv 32 := 0x0040006f.
Lemma F_151a0 : fetch_word Ubsan.M.loaded_segments (0x151a0 : word) = Some W_151a0.
Proof. vm_refl. Qed.
Lemma D_151a0 : decode_any W_151a0 = Some (Jal 0 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_151a4 : bv 32 := 0x0580006f.
Lemma F_151a4 : fetch_word Ubsan.M.loaded_segments (0x151a4 : word) = Some W_151a4.
Proof. vm_refl. Qed.
Lemma D_151a4 : decode_any W_151a4 = Some (Jal 0 88, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_151a8 : bv 32 := 0x00020517.
Lemma F_151a8 : fetch_word Ubsan.M.loaded_segments (0x151a8 : word) = Some W_151a8.
Proof. vm_refl. Qed.
Lemma D_151a8 : decode_any W_151a8 = Some (Auipc 10 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_151ac : bv 32 := 0x1d050593.
Lemma F_151ac : fetch_word Ubsan.M.loaded_segments (0x151ac : word) = Some W_151ac.
Proof. vm_refl. Qed.
Lemma D_151ac : decode_any W_151ac = Some (OpImm ALU_ADD 11 10 464, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_151b0 : bv 32 := 0x00100513.
Lemma F_151b0 : fetch_word Ubsan.M.loaded_segments (0x151b0 : word) = Some W_151b0.
Proof. vm_refl. Qed.
Lemma D_151b0 : decode_any W_151b0 = Some (OpImm ALU_ADD 10 0 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_151b4 : bv 32 := 0x00a58023.
Lemma F_151b4 : fetch_word Ubsan.M.loaded_segments (0x151b4 : word) = Some W_151b4.
Proof. vm_refl. Qed.
Lemma D_151b4 : decode_any W_151b4 = Some (Store SZ1 11 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_151b8 : bv 32 := 0x0001f517.
Lemma F_151b8 : fetch_word Ubsan.M.loaded_segments (0x151b8 : word) = Some W_151b8.
Proof. vm_refl. Qed.
Lemma D_151b8 : decode_any W_151b8 = Some (Auipc 10 31, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_151bc : bv 32 := 0xbb053503.
Lemma F_151bc : fetch_word Ubsan.M.loaded_segments (0x151bc : word) = Some W_151bc.
Proof. vm_refl. Qed.
Lemma D_151bc : decode_any W_151bc = Some (Load SZ8 true 10 10 2992, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_151c0 : bv 32 := 0x00050e63.
Lemma F_151c0 : fetch_word Ubsan.M.loaded_segments (0x151c0 : word) = Some W_151c0.
Proof. vm_refl. Qed.
Lemma D_151c0 : decode_any W_151c0 = Some (Branch BC_EQ 10 0 28, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_151c4 : bv 32 := 0x0040006f.
Lemma F_151c4 : fetch_word Ubsan.M.loaded_segments (0x151c4 : word) = Some W_151c4.
Proof. vm_refl. Qed.
Lemma D_151c4 : decode_any W_151c4 = Some (Jal 0 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_151c8 : bv 32 := 0x00020517.
Lemma F_151c8 : fetch_word Ubsan.M.loaded_segments (0x151c8 : word) = Some W_151c8.
Proof. vm_refl. Qed.
Lemma D_151c8 : decode_any W_151c8 = Some (Auipc 10 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_151cc : bv 32 := 0xc1050513.
Lemma F_151cc : fetch_word Ubsan.M.loaded_segments (0x151cc : word) = Some W_151cc.
Proof. vm_refl. Qed.
Lemma D_151cc : decode_any W_151cc = Some (OpImm ALU_ADD 10 10 3088, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_151d0 : bv 32 := 0x00053503.
Lemma F_151d0 : fetch_word Ubsan.M.loaded_segments (0x151d0 : word) = Some W_151d0.
Proof. vm_refl. Qed.
Lemma D_151d0 : decode_any W_151d0 = Some (Load SZ8 true 10 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_151d4 : bv 32 := 0x3e1150ef.
Lemma F_151d4 : fetch_word Ubsan.M.loaded_segments (0x151d4 : word) = Some W_151d4.
Proof. vm_refl. Qed.
Lemma D_151d4 : decode_any W_151d4 = Some (Jal 1 89056, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_151d8 : bv 32 := 0x0040006f.
Lemma F_151d8 : fetch_word Ubsan.M.loaded_segments (0x151d8 : word) = Some W_151d8.
Proof. vm_refl. Qed.
Lemma D_151d8 : decode_any W_151d8 = Some (Jal 0 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_151dc : bv 32 := 0x0001f517.
Lemma F_151dc : fetch_word Ubsan.M.loaded_segments (0x151dc : word) = Some W_151dc.
Proof. vm_refl. Qed.
Lemma D_151dc : decode_any W_151dc = Some (Auipc 10 31, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_151e0 : bv 32 := 0xb9453503.
Lemma F_151e0 : fetch_word Ubsan.M.loaded_segments (0x151e0 : word) = Some W_151e0.
Proof. vm_refl. Qed.
Lemma D_151e0 : decode_any W_151e0 = Some (Load SZ8 true 10 10 2964, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_151e4 : bv 32 := 0x00050c63.
Lemma F_151e4 : fetch_word Ubsan.M.loaded_segments (0x151e4 : word) = Some W_151e4.
Proof. vm_refl. Qed.
Lemma D_151e4 : decode_any W_151e4 = Some (Branch BC_EQ 10 0 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_151e8 : bv 32 := 0x0040006f.
Lemma F_151e8 : fetch_word Ubsan.M.loaded_segments (0x151e8 : word) = Some W_151e8.
Proof. vm_refl. Qed.
Lemma D_151e8 : decode_any W_151e8 = Some (Jal 0 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_151ec : bv 32 := 0xffffe517.
Lemma F_151ec : fetch_word Ubsan.M.loaded_segments (0x151ec : word) = Some W_151ec.
Proof. vm_refl. Qed.
Lemma D_151ec : decode_any W_151ec = Some (Auipc 10 1048574, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_151f0 : bv 32 := 0x8ac50513.
Lemma F_151f0 : fetch_word Ubsan.M.loaded_segments (0x151f0 : word) = Some W_151f0.
Proof. vm_refl. Qed.
Lemma D_151f0 : decode_any W_151f0 = Some (OpImm ALU_ADD 10 10 2220, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_151f4 : bv 32 := 0x000000ef.
Lemma F_151f4 : fetch_word Ubsan.M.loaded_segments (0x151f4 : word) = Some W_151f4.
Proof. vm_refl. Qed.
Lemma D_151f4 : decode_any W_151f4 = Some (Jal 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_151f8 : bv 32 := 0x0040006f.
Lemma F_151f8 : fetch_word Ubsan.M.loaded_segments (0x151f8 : word) = Some W_151f8.
Proof. vm_refl. Qed.
Lemma D_151f8 : decode_any W_151f8 = Some (Jal 0 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_151fc : bv 32 := 0x00813083.
Lemma F_151fc : fetch_word Ubsan.M.loaded_segments (0x151fc : word) = Some W_151fc.
Proof. vm_refl. Qed.
Lemma D_151fc : decode_any W_151fc = Some (Load SZ8 true 1 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15200 : bv 32 := 0x00013403.
Lemma F_15200 : fetch_word Ubsan.M.loaded_segments (0x15200 : word) = Some W_15200.
Proof. vm_refl. Qed.
Lemma D_15200 : decode_any W_15200 = Some (Load SZ8 true 8 2 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15204 : bv 32 := 0x01010113.
Lemma F_15204 : fetch_word Ubsan.M.loaded_segments (0x15204 : word) = Some W_15204.
Proof. vm_refl. Qed.
Lemma D_15204 : decode_any W_15204 = Some (OpImm ALU_ADD 2 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15208 : bv 32 := 0x00008067.
Lemma F_15208 : fetch_word Ubsan.M.loaded_segments (0x15208 : word) = Some W_15208.
Proof. vm_refl. Qed.
Lemma D_15208 : decode_any W_15208 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15634 : bv 32 := 0x00030517.
Lemma F_15634 : fetch_word Ubsan.M.loaded_segments (0x15634 : word) = Some W_15634.
Proof. vm_refl. Qed.
Lemma D_15634 : decode_any W_15634 = Some (Auipc 10 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15638 : bv 32 := 0xd5054503.
Lemma F_15638 : fetch_word Ubsan.M.loaded_segments (0x15638 : word) = Some W_15638.
Proof. vm_refl. Qed.
Lemma D_15638 : decode_any W_15638 = Some (Load SZ1 false 10 10 3408, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1563c : bv 32 := 0x00051463.
Lemma F_1563c : fetch_word Ubsan.M.loaded_segments (0x1563c : word) = Some W_1563c.
Proof. vm_refl. Qed.
Lemma D_1563c : decode_any W_1563c = Some (Branch BC_NE 10 0 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15640 : bv 32 := 0x00008067.
Lemma F_15640 : fetch_word Ubsan.M.loaded_segments (0x15640 : word) = Some W_15640.
Proof. vm_refl. Qed.
Lemma D_15640 : decode_any W_15640 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15644 : bv 32 := 0xff010113.
Lemma F_15644 : fetch_word Ubsan.M.loaded_segments (0x15644 : word) = Some W_15644.
Proof. vm_refl. Qed.
Lemma D_15644 : decode_any W_15644 = Some (OpImm ALU_ADD 2 2 4080, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15648 : bv 32 := 0x00113423.
Lemma F_15648 : fetch_word Ubsan.M.loaded_segments (0x15648 : word) = Some W_15648.
Proof. vm_refl. Qed.
Lemma D_15648 : decode_any W_15648 = Some (Store SZ8 2 1 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1564c : bv 32 := 0x0001e517.
Lemma F_1564c : fetch_word Ubsan.M.loaded_segments (0x1564c : word) = Some W_1564c.
Proof. vm_refl. Qed.
Lemma D_1564c : decode_any W_1564c = Some (Auipc 10 30, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15650 : bv 32 := 0x73c53503.
Lemma F_15650 : fetch_word Ubsan.M.loaded_segments (0x15650 : word) = Some W_15650.
Proof. vm_refl. Qed.
Lemma D_15650 : decode_any W_15650 = Some (Load SZ8 true 10 10 1852, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15654 : bv 32 := 0x00053503.
Lemma F_15654 : fetch_word Ubsan.M.loaded_segments (0x15654 : word) = Some W_15654.
Proof. vm_refl. Qed.
Lemma D_15654 : decode_any W_15654 = Some (Load SZ8 true 10 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15658 : bv 32 := 0x0d1170ef.
Lemma F_15658 : fetch_word Ubsan.M.loaded_segments (0x15658 : word) = Some W_15658.
Proof. vm_refl. Qed.
Lemma D_15658 : decode_any W_15658 = Some (Jal 1 96464, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1565c : bv 32 := 0x04d00513.
Lemma F_1565c : fetch_word Ubsan.M.loaded_segments (0x1565c : word) = Some W_1565c.
Proof. vm_refl. Qed.
Lemma D_1565c : decode_any W_1565c = Some (OpImm ALU_ADD 10 0 77, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_15660 : bv 32 := 0x6141d0ef.
Lemma F_15660 : fetch_word Ubsan.M.loaded_segments (0x15660 : word) = Some W_15660.
Proof. vm_refl. Qed.
Lemma D_15660 : decode_any W_15660 = Some (Jal 1 120340, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2acec : bv 32 := 0xfd010113.
Lemma F_2acec : fetch_word Ubsan.M.loaded_segments (0x2acec : word) = Some W_2acec.
Proof. vm_refl. Qed.
Lemma D_2acec : decode_any W_2acec = Some (OpImm ALU_ADD 2 2 4048, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2acf0 : bv 32 := 0x02113423.
Lemma F_2acf0 : fetch_word Ubsan.M.loaded_segments (0x2acf0 : word) = Some W_2acf0.
Proof. vm_refl. Qed.
Lemma D_2acf0 : decode_any W_2acf0 = Some (Store SZ8 2 1 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2acf4 : bv 32 := 0x02813023.
Lemma F_2acf4 : fetch_word Ubsan.M.loaded_segments (0x2acf4 : word) = Some W_2acf4.
Proof. vm_refl. Qed.
Lemma D_2acf4 : decode_any W_2acf4 = Some (Store SZ8 2 8 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2acf8 : bv 32 := 0x00913c23.
Lemma F_2acf8 : fetch_word Ubsan.M.loaded_segments (0x2acf8 : word) = Some W_2acf8.
Proof. vm_refl. Qed.
Lemma D_2acf8 : decode_any W_2acf8 = Some (Store SZ8 2 9 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2acfc : bv 32 := 0x01213823.
Lemma F_2acfc : fetch_word Ubsan.M.loaded_segments (0x2acfc : word) = Some W_2acfc.
Proof. vm_refl. Qed.
Lemma D_2acfc : decode_any W_2acfc = Some (Store SZ8 2 18 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2ad00 : bv 32 := 0x01313423.
Lemma F_2ad00 : fetch_word Ubsan.M.loaded_segments (0x2ad00 : word) = Some W_2ad00.
Proof. vm_refl. Qed.
Lemma D_2ad00 : decode_any W_2ad00 = Some (Store SZ8 2 19 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2ad04 : bv 32 := 0x0003a517.
Lemma F_2ad04 : fetch_word Ubsan.M.loaded_segments (0x2ad04 : word) = Some W_2ad04.
Proof. vm_refl. Qed.
Lemma D_2ad04 : decode_any W_2ad04 = Some (Auipc 10 58, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2ad08 : bv 32 := 0x7bc50913.
Lemma F_2ad08 : fetch_word Ubsan.M.loaded_segments (0x2ad08 : word) = Some W_2ad08.
Proof. vm_refl. Qed.
Lemma D_2ad08 : decode_any W_2ad08 = Some (OpImm ALU_ADD 18 10 1980, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2ad0c : bv 32 := 0x00490413.
Lemma F_2ad0c : fetch_word Ubsan.M.loaded_segments (0x2ad0c : word) = Some W_2ad0c.
Proof. vm_refl. Qed.
Lemma D_2ad0c : decode_any W_2ad0c = Some (OpImm ALU_ADD 8 18 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2ad10 : bv 32 := 0x00040513.
Lemma F_2ad10 : fetch_word Ubsan.M.loaded_segments (0x2ad10 : word) = Some W_2ad10.
Proof. vm_refl. Qed.
Lemma D_2ad10 : decode_any W_2ad10 = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2ad14 : bv 32 := 0x431070ef.
Lemma F_2ad14 : fetch_word Ubsan.M.loaded_segments (0x2ad14 : word) = Some W_2ad14.
Proof. vm_refl. Qed.
Lemma D_2ad14 : decode_any W_2ad14 = Some (Jal 1 31792, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2ad18 : bv 32 := 0x01093503.
Lemma F_2ad18 : fetch_word Ubsan.M.loaded_segments (0x2ad18 : word) = Some W_2ad18.
Proof. vm_refl. Qed.
Lemma D_2ad18 : decode_any W_2ad18 = Some (Load SZ8 true 10 18 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2ad1c : bv 32 := 0x06050863.
Lemma F_2ad1c : fetch_word Ubsan.M.loaded_segments (0x2ad1c : word) = Some W_2ad1c.
Proof. vm_refl. Qed.
Lemma D_2ad1c : decode_any W_2ad1c = Some (Branch BC_EQ 10 0 112, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2ad20 : bv 32 := 0x00892583.
Lemma F_2ad20 : fetch_word Ubsan.M.loaded_segments (0x2ad20 : word) = Some W_2ad20.
Proof. vm_refl. Qed.
Lemma D_2ad20 : decode_any W_2ad20 = Some (Load SZ4 true 11 18 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2ad24 : bv 32 := 0x0180006f.
Lemma F_2ad24 : fetch_word Ubsan.M.loaded_segments (0x2ad24 : word) = Some W_2ad24.
Proof. vm_refl. Qed.
Lemma D_2ad24 : decode_any W_2ad24 = Some (Jal 0 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2ad28 : bv 32 := 0x00053503.
Lemma F_2ad28 : fetch_word Ubsan.M.loaded_segments (0x2ad28 : word) = Some W_2ad28.
Proof. vm_refl. Qed.
Lemma D_2ad28 : decode_any W_2ad28 = Some (Load SZ8 true 10 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2ad2c : bv 32 := 0x02000593.
Lemma F_2ad2c : fetch_word Ubsan.M.loaded_segments (0x2ad2c : word) = Some W_2ad2c.
Proof. vm_refl. Qed.
Lemma D_2ad2c : decode_any W_2ad2c = Some (OpImm ALU_ADD 11 0 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2ad30 : bv 32 := 0x00b92423.
Lemma F_2ad30 : fetch_word Ubsan.M.loaded_segments (0x2ad30 : word) = Some W_2ad30.
Proof. vm_refl. Qed.
Lemma D_2ad30 : decode_any W_2ad30 = Some (Store SZ4 18 11 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2ad34 : bv 32 := 0x00a93823.
Lemma F_2ad34 : fetch_word Ubsan.M.loaded_segments (0x2ad34 : word) = Some W_2ad34.
Proof. vm_refl. Qed.
Lemma D_2ad34 : decode_any W_2ad34 = Some (Store SZ8 18 10 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2ad38 : bv 32 := 0x04050a63.
Lemma F_2ad38 : fetch_word Ubsan.M.loaded_segments (0x2ad38 : word) = Some W_2ad38.
Proof. vm_refl. Qed.
Lemma D_2ad38 : decode_any W_2ad38 = Some (Branch BC_EQ 10 0 84, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2ad3c : bv 32 := 0xfff5861b.
Lemma F_2ad3c : fetch_word Ubsan.M.loaded_segments (0x2ad3c : word) = Some W_2ad3c.
Proof. vm_refl. Qed.
Lemma D_2ad3c : decode_any W_2ad3c = Some (OpImm32 12 11 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2ad40 : bv 32 := 0x00c92423.
Lemma F_2ad40 : fetch_word Ubsan.M.loaded_segments (0x2ad40 : word) = Some W_2ad40.
Proof. vm_refl. Qed.
Lemma D_2ad40 : decode_any W_2ad40 = Some (Store SZ4 18 12 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2ad44 : bv 32 := 0xfeb052e3.
Lemma F_2ad44 : fetch_word Ubsan.M.loaded_segments (0x2ad44 : word) = Some W_2ad44.
Proof. vm_refl. Qed.
Lemma D_2ad44 : decode_any W_2ad44 = Some (Branch BC_GE 0 11 8164, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2ad48 : bv 32 := 0x01093503.
Lemma F_2ad48 : fetch_word Ubsan.M.loaded_segments (0x2ad48 : word) = Some W_2ad48.
Proof. vm_refl. Qed.
Lemma D_2ad48 : decode_any W_2ad48 = Some (Load SZ8 true 10 18 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2ad4c : bv 32 := 0x00361613.
Lemma F_2ad4c : fetch_word Ubsan.M.loaded_segments (0x2ad4c : word) = Some W_2ad4c.
Proof. vm_refl. Qed.
Lemma D_2ad4c : decode_any W_2ad4c = Some (ShiftImm ALU_SLL 12 12 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2ad50 : bv 32 := 0x00c50533.
Lemma F_2ad50 : fetch_word Ubsan.M.loaded_segments (0x2ad50 : word) = Some W_2ad50.
Proof. vm_refl. Qed.
Lemma D_2ad50 : decode_any W_2ad50 = Some (Op ALU_ADD 10 10 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2ad54 : bv 32 := 0x00853983.
Lemma F_2ad54 : fetch_word Ubsan.M.loaded_segments (0x2ad54 : word) = Some W_2ad54.
Proof. vm_refl. Qed.
Lemma D_2ad54 : decode_any W_2ad54 = Some (Load SZ8 true 19 10 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2ad58 : bv 32 := 0x10853483.
Lemma F_2ad58 : fetch_word Ubsan.M.loaded_segments (0x2ad58 : word) = Some W_2ad58.
Proof. vm_refl. Qed.
Lemma D_2ad58 : decode_any W_2ad58 = Some (Load SZ8 true 9 10 264, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2ad5c : bv 32 := 0x00040513.
Lemma F_2ad5c : fetch_word Ubsan.M.loaded_segments (0x2ad5c : word) = Some W_2ad5c.
Proof. vm_refl. Qed.
Lemma D_2ad5c : decode_any W_2ad5c = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2ad60 : bv 32 := 0x66d070ef.
Lemma F_2ad60 : fetch_word Ubsan.M.loaded_segments (0x2ad60 : word) = Some W_2ad60.
Proof. vm_refl. Qed.
Lemma D_2ad60 : decode_any W_2ad60 = Some (Jal 1 32364, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2ad64 : bv 32 := 0x00048513.
Lemma F_2ad64 : fetch_word Ubsan.M.loaded_segments (0x2ad64 : word) = Some W_2ad64.
Proof. vm_refl. Qed.
Lemma D_2ad64 : decode_any W_2ad64 = Some (OpImm ALU_ADD 10 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2ad68 : bv 32 := 0x000980e7.
Lemma F_2ad68 : fetch_word Ubsan.M.loaded_segments (0x2ad68 : word) = Some W_2ad68.
Proof. vm_refl. Qed.
Lemma D_2ad68 : decode_any W_2ad68 = Some (Jalr 1 19 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2ad6c : bv 32 := 0x00040513.
Lemma F_2ad6c : fetch_word Ubsan.M.loaded_segments (0x2ad6c : word) = Some W_2ad6c.
Proof. vm_refl. Qed.
Lemma D_2ad6c : decode_any W_2ad6c = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2ad70 : bv 32 := 0x3d5070ef.
Lemma F_2ad70 : fetch_word Ubsan.M.loaded_segments (0x2ad70 : word) = Some W_2ad70.
Proof. vm_refl. Qed.
Lemma D_2ad70 : decode_any W_2ad70 = Some (Jal 1 31700, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2ad74 : bv 32 := 0x00892503.
Lemma F_2ad74 : fetch_word Ubsan.M.loaded_segments (0x2ad74 : word) = Some W_2ad74.
Proof. vm_refl. Qed.
Lemma D_2ad74 : decode_any W_2ad74 = Some (Load SZ4 true 10 18 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2ad78 : bv 32 := 0xfff5061b.
Lemma F_2ad78 : fetch_word Ubsan.M.loaded_segments (0x2ad78 : word) = Some W_2ad78.
Proof. vm_refl. Qed.
Lemma D_2ad78 : decode_any W_2ad78 = Some (OpImm32 12 10 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2ad7c : bv 32 := 0x00c92423.
Lemma F_2ad7c : fetch_word Ubsan.M.loaded_segments (0x2ad7c : word) = Some W_2ad7c.
Proof. vm_refl. Qed.
Lemma D_2ad7c : decode_any W_2ad7c = Some (Store SZ4 18 12 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2ad80 : bv 32 := 0xfca044e3.
Lemma F_2ad80 : fetch_word Ubsan.M.loaded_segments (0x2ad80 : word) = Some W_2ad80.
Proof. vm_refl. Qed.
Lemma D_2ad80 : decode_any W_2ad80 = Some (Branch BC_LT 0 10 8136, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2ad84 : bv 32 := 0x01093503.
Lemma F_2ad84 : fetch_word Ubsan.M.loaded_segments (0x2ad84 : word) = Some W_2ad84.
Proof. vm_refl. Qed.
Lemma D_2ad84 : decode_any W_2ad84 = Some (Load SZ8 true 10 18 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2ad88 : bv 32 := 0xfa1ff06f.
Lemma F_2ad88 : fetch_word Ubsan.M.loaded_segments (0x2ad88 : word) = Some W_2ad88.
Proof. vm_refl. Qed.
Lemma D_2ad88 : decode_any W_2ad88 = Some (Jal 0 2097056, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2ad8c : bv 32 := 0x00100513.
Lemma F_2ad8c : fetch_word Ubsan.M.loaded_segments (0x2ad8c : word) = Some W_2ad8c.
Proof. vm_refl. Qed.
Lemma D_2ad8c : decode_any W_2ad8c = Some (OpImm ALU_ADD 10 0 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2ad90 : bv 32 := 0x00a90023.
Lemma F_2ad90 : fetch_word Ubsan.M.loaded_segments (0x2ad90 : word) = Some W_2ad90.
Proof. vm_refl. Qed.
Lemma D_2ad90 : decode_any W_2ad90 = Some (Store SZ1 18 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2ad94 : bv 32 := 0x00040513.
Lemma F_2ad94 : fetch_word Ubsan.M.loaded_segments (0x2ad94 : word) = Some W_2ad94.
Proof. vm_refl. Qed.
Lemma D_2ad94 : decode_any W_2ad94 = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2ad98 : bv 32 := 0x02813083.
Lemma F_2ad98 : fetch_word Ubsan.M.loaded_segments (0x2ad98 : word) = Some W_2ad98.
Proof. vm_refl. Qed.
Lemma D_2ad98 : decode_any W_2ad98 = Some (Load SZ8 true 1 2 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2ad9c : bv 32 := 0x02013403.
Lemma F_2ad9c : fetch_word Ubsan.M.loaded_segments (0x2ad9c : word) = Some W_2ad9c.
Proof. vm_refl. Qed.
Lemma D_2ad9c : decode_any W_2ad9c = Some (Load SZ8 true 8 2 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2ada0 : bv 32 := 0x01813483.
Lemma F_2ada0 : fetch_word Ubsan.M.loaded_segments (0x2ada0 : word) = Some W_2ada0.
Proof. vm_refl. Qed.
Lemma D_2ada0 : decode_any W_2ada0 = Some (Load SZ8 true 9 2 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2ada4 : bv 32 := 0x01013903.
Lemma F_2ada4 : fetch_word Ubsan.M.loaded_segments (0x2ada4 : word) = Some W_2ada4.
Proof. vm_refl. Qed.
Lemma D_2ada4 : decode_any W_2ada4 = Some (Load SZ8 true 18 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2ada8 : bv 32 := 0x00813983.
Lemma F_2ada8 : fetch_word Ubsan.M.loaded_segments (0x2ada8 : word) = Some W_2ada8.
Proof. vm_refl. Qed.
Lemma D_2ada8 : decode_any W_2ada8 = Some (Load SZ8 true 19 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2adac : bv 32 := 0x03010113.
Lemma F_2adac : fetch_word Ubsan.M.loaded_segments (0x2adac : word) = Some W_2adac.
Proof. vm_refl. Qed.
Lemma D_2adac : decode_any W_2adac = Some (OpImm ALU_ADD 2 2 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2adb0 : bv 32 := 0x61d0706f.
Lemma F_2adb0 : fetch_word Ubsan.M.loaded_segments (0x2adb0 : word) = Some W_2adb0.
Proof. vm_refl. Qed.
Lemma D_2adb0 : decode_any W_2adb0 = Some (Jal 0 32284, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2adb4 : bv 32 := 0x00008067.
Lemma F_2adb4 : fetch_word Ubsan.M.loaded_segments (0x2adb4 : word) = Some W_2adb4.
Proof. vm_refl. Qed.
Lemma D_2adb4 : decode_any W_2adb4 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2adb8 : bv 32 := 0xfd010113.
Lemma F_2adb8 : fetch_word Ubsan.M.loaded_segments (0x2adb8 : word) = Some W_2adb8.
Proof. vm_refl. Qed.
Lemma D_2adb8 : decode_any W_2adb8 = Some (OpImm ALU_ADD 2 2 4048, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2adbc : bv 32 := 0x02113423.
Lemma F_2adbc : fetch_word Ubsan.M.loaded_segments (0x2adbc : word) = Some W_2adbc.
Proof. vm_refl. Qed.
Lemma D_2adbc : decode_any W_2adbc = Some (Store SZ8 2 1 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2adc0 : bv 32 := 0x02813023.
Lemma F_2adc0 : fetch_word Ubsan.M.loaded_segments (0x2adc0 : word) = Some W_2adc0.
Proof. vm_refl. Qed.
Lemma D_2adc0 : decode_any W_2adc0 = Some (Store SZ8 2 8 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2adc4 : bv 32 := 0x00913c23.
Lemma F_2adc4 : fetch_word Ubsan.M.loaded_segments (0x2adc4 : word) = Some W_2adc4.
Proof. vm_refl. Qed.
Lemma D_2adc4 : decode_any W_2adc4 = Some (Store SZ8 2 9 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2adc8 : bv 32 := 0x01213823.
Lemma F_2adc8 : fetch_word Ubsan.M.loaded_segments (0x2adc8 : word) = Some W_2adc8.
Proof. vm_refl. Qed.
Lemma D_2adc8 : decode_any W_2adc8 = Some (Store SZ8 2 18 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2adcc : bv 32 := 0x01313423.
Lemma F_2adcc : fetch_word Ubsan.M.loaded_segments (0x2adcc : word) = Some W_2adcc.
Proof. vm_refl. Qed.
Lemma D_2adcc : decode_any W_2adcc = Some (Store SZ8 2 19 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2add0 : bv 32 := 0x00050493.
Lemma F_2add0 : fetch_word Ubsan.M.loaded_segments (0x2add0 : word) = Some W_2add0.
Proof. vm_refl. Qed.
Lemma D_2add0 : decode_any W_2add0 = Some (OpImm ALU_ADD 9 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2add4 : bv 32 := 0x0003a517.
Lemma F_2add4 : fetch_word Ubsan.M.loaded_segments (0x2add4 : word) = Some W_2add4.
Proof. vm_refl. Qed.
Lemma D_2add4 : decode_any W_2add4 = Some (Auipc 10 58, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2add8 : bv 32 := 0x6ec50993.
Lemma F_2add8 : fetch_word Ubsan.M.loaded_segments (0x2add8 : word) = Some W_2add8.
Proof. vm_refl. Qed.
Lemma D_2add8 : decode_any W_2add8 = Some (OpImm ALU_ADD 19 10 1772, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2addc : bv 32 := 0x00498413.
Lemma F_2addc : fetch_word Ubsan.M.loaded_segments (0x2addc : word) = Some W_2addc.
Proof. vm_refl. Qed.
Lemma D_2addc : decode_any W_2addc = Some (OpImm ALU_ADD 8 19 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2ade0 : bv 32 := 0x00040513.
Lemma F_2ade0 : fetch_word Ubsan.M.loaded_segments (0x2ade0 : word) = Some W_2ade0.
Proof. vm_refl. Qed.
Lemma D_2ade0 : decode_any W_2ade0 = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2ade4 : bv 32 := 0x361070ef.
Lemma F_2ade4 : fetch_word Ubsan.M.loaded_segments (0x2ade4 : word) = Some W_2ade4.
Proof. vm_refl. Qed.
Lemma D_2ade4 : decode_any W_2ade4 = Some (Jal 1 31584, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2ade8 : bv 32 := 0x0009c503.
Lemma F_2ade8 : fetch_word Ubsan.M.loaded_segments (0x2ade8 : word) = Some W_2ade8.
Proof. vm_refl. Qed.
Lemma D_2ade8 : decode_any W_2ade8 = Some (Load SZ1 false 10 19 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2adec : bv 32 := 0xfff00913.
Lemma F_2adec : fetch_word Ubsan.M.loaded_segments (0x2adec : word) = Some W_2adec.
Proof. vm_refl. Qed.
Lemma D_2adec : decode_any W_2adec = Some (OpImm ALU_ADD 18 0 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2adf0 : bv 32 := 0x06051263.
Lemma F_2adf0 : fetch_word Ubsan.M.loaded_segments (0x2adf0 : word) = Some W_2adf0.
Proof. vm_refl. Qed.
Lemma D_2adf0 : decode_any W_2adf0 = Some (Branch BC_NE 10 0 100, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2adf4 : bv 32 := 0x0109b503.
Lemma F_2adf4 : fetch_word Ubsan.M.loaded_segments (0x2adf4 : word) = Some W_2adf4.
Proof. vm_refl. Qed.
Lemma D_2adf4 : decode_any W_2adf4 = Some (Load SZ8 true 10 19 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2adf8 : bv 32 := 0x00051663.
Lemma F_2adf8 : fetch_word Ubsan.M.loaded_segments (0x2adf8 : word) = Some W_2adf8.
Proof. vm_refl. Qed.
Lemma D_2adf8 : decode_any W_2adf8 = Some (Branch BC_NE 10 0 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2adfc : bv 32 := 0x01898513.
Lemma F_2adfc : fetch_word Ubsan.M.loaded_segments (0x2adfc : word) = Some W_2adfc.
Proof. vm_refl. Qed.
Lemma D_2adfc : decode_any W_2adfc = Some (OpImm ALU_ADD 10 19 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2ae00 : bv 32 := 0x00a9b823.
Lemma F_2ae00 : fetch_word Ubsan.M.loaded_segments (0x2ae00 : word) = Some W_2ae00.
Proof. vm_refl. Qed.
Lemma D_2ae00 : decode_any W_2ae00 = Some (Store SZ8 19 10 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2ae04 : bv 32 := 0x0089a583.
Lemma F_2ae04 : fetch_word Ubsan.M.loaded_segments (0x2ae04 : word) = Some W_2ae04.
Proof. vm_refl. Qed.
Lemma D_2ae04 : decode_any W_2ae04 = Some (Load SZ4 true 11 19 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2ae08 : bv 32 := 0x02000613.
Lemma F_2ae08 : fetch_word Ubsan.M.loaded_segments (0x2ae08 : word) = Some W_2ae08.
Proof. vm_refl. Qed.
Lemma D_2ae08 : decode_any W_2ae08 = Some (OpImm ALU_ADD 12 0 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2ae0c : bv 32 := 0x02c59263.
Lemma F_2ae0c : fetch_word Ubsan.M.loaded_segments (0x2ae0c : word) = Some W_2ae0c.
Proof. vm_refl. Qed.
Lemma D_2ae0c : decode_any W_2ae0c = Some (Branch BC_NE 11 12 36, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2ae10 : bv 32 := 0x20800513.
Lemma F_2ae10 : fetch_word Ubsan.M.loaded_segments (0x2ae10 : word) = Some W_2ae10.
Proof. vm_refl. Qed.
Lemma D_2ae10 : decode_any W_2ae10 = Some (OpImm ALU_ADD 10 0 520, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2ae14 : bv 32 := 0x00100593.
Lemma F_2ae14 : fetch_word Ubsan.M.loaded_segments (0x2ae14 : word) = Some W_2ae14.
Proof. vm_refl. Qed.
Lemma D_2ae14 : decode_any W_2ae14 = Some (OpImm ALU_ADD 11 0 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2ae18 : bv 32 := 0x3f4000ef.
Lemma F_2ae18 : fetch_word Ubsan.M.loaded_segments (0x2ae18 : word) = Some W_2ae18.
Proof. vm_refl. Qed.
Lemma D_2ae18 : decode_any W_2ae18 = Some (Jal 1 1012, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2ae1c : bv 32 := 0x02050c63.
Lemma F_2ae1c : fetch_word Ubsan.M.loaded_segments (0x2ae1c : word) = Some W_2ae1c.
Proof. vm_refl. Qed.
Lemma D_2ae1c : decode_any W_2ae1c = Some (Branch BC_EQ 10 0 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2ae20 : bv 32 := 0x00000593.
Lemma F_2ae20 : fetch_word Ubsan.M.loaded_segments (0x2ae20 : word) = Some W_2ae20.
Proof. vm_refl. Qed.
Lemma D_2ae20 : decode_any W_2ae20 = Some (OpImm ALU_ADD 11 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2ae24 : bv 32 := 0x0109b603.
Lemma F_2ae24 : fetch_word Ubsan.M.loaded_segments (0x2ae24 : word) = Some W_2ae24.
Proof. vm_refl. Qed.
Lemma D_2ae24 : decode_any W_2ae24 = Some (Load SZ8 true 12 19 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2ae28 : bv 32 := 0x00c53023.
Lemma F_2ae28 : fetch_word Ubsan.M.loaded_segments (0x2ae28 : word) = Some W_2ae28.
Proof. vm_refl. Qed.
Lemma D_2ae28 : decode_any W_2ae28 = Some (Store SZ8 10 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2ae2c : bv 32 := 0x00a9b823.
Lemma F_2ae2c : fetch_word Ubsan.M.loaded_segments (0x2ae2c : word) = Some W_2ae2c.
Proof. vm_refl. Qed.
Lemma D_2ae2c : decode_any W_2ae2c = Some (Store SZ8 19 10 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2ae30 : bv 32 := 0x00000913.
Lemma F_2ae30 : fetch_word Ubsan.M.loaded_segments (0x2ae30 : word) = Some W_2ae30.
Proof. vm_refl. Qed.
Lemma D_2ae30 : decode_any W_2ae30 = Some (OpImm ALU_ADD 18 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2ae34 : bv 32 := 0x00359613.
Lemma F_2ae34 : fetch_word Ubsan.M.loaded_segments (0x2ae34 : word) = Some W_2ae34.
Proof. vm_refl. Qed.
Lemma D_2ae34 : decode_any W_2ae34 = Some (ShiftImm ALU_SLL 12 11 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2ae38 : bv 32 := 0x00c50533.
Lemma F_2ae38 : fetch_word Ubsan.M.loaded_segments (0x2ae38 : word) = Some W_2ae38.
Proof. vm_refl. Qed.
Lemma D_2ae38 : decode_any W_2ae38 = Some (Op ALU_ADD 10 10 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2ae3c : bv 32 := 0x00000617.
Lemma F_2ae3c : fetch_word Ubsan.M.loaded_segments (0x2ae3c : word) = Some W_2ae3c.
Proof. vm_refl. Qed.
Lemma D_2ae3c : decode_any W_2ae3c = Some (Auipc 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2ae40 : bv 32 := 0x00158593.
Lemma F_2ae40 : fetch_word Ubsan.M.loaded_segments (0x2ae40 : word) = Some W_2ae40.
Proof. vm_refl. Qed.
Lemma D_2ae40 : decode_any W_2ae40 = Some (OpImm ALU_ADD 11 11 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2ae44 : bv 32 := 0x04060613.
Lemma F_2ae44 : fetch_word Ubsan.M.loaded_segments (0x2ae44 : word) = Some W_2ae44.
Proof. vm_refl. Qed.
Lemma D_2ae44 : decode_any W_2ae44 = Some (OpImm ALU_ADD 12 12 64, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2ae48 : bv 32 := 0x00c53423.
Lemma F_2ae48 : fetch_word Ubsan.M.loaded_segments (0x2ae48 : word) = Some W_2ae48.
Proof. vm_refl. Qed.
Lemma D_2ae48 : decode_any W_2ae48 = Some (Store SZ8 10 12 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2ae4c : bv 32 := 0x10953423.
Lemma F_2ae4c : fetch_word Ubsan.M.loaded_segments (0x2ae4c : word) = Some W_2ae4c.
Proof. vm_refl. Qed.
Lemma D_2ae4c : decode_any W_2ae4c = Some (Store SZ8 10 9 264, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2ae50 : bv 32 := 0x00b9a423.
Lemma F_2ae50 : fetch_word Ubsan.M.loaded_segments (0x2ae50 : word) = Some W_2ae50.
Proof. vm_refl. Qed.
Lemma D_2ae50 : decode_any W_2ae50 = Some (Store SZ4 19 11 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2ae54 : bv 32 := 0x00040513.
Lemma F_2ae54 : fetch_word Ubsan.M.loaded_segments (0x2ae54 : word) = Some W_2ae54.
Proof. vm_refl. Qed.
Lemma D_2ae54 : decode_any W_2ae54 = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2ae58 : bv 32 := 0x575070ef.
Lemma F_2ae58 : fetch_word Ubsan.M.loaded_segments (0x2ae58 : word) = Some W_2ae58.
Proof. vm_refl. Qed.
Lemma D_2ae58 : decode_any W_2ae58 = Some (Jal 1 32116, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2ae5c : bv 32 := 0x00090513.
Lemma F_2ae5c : fetch_word Ubsan.M.loaded_segments (0x2ae5c : word) = Some W_2ae5c.
Proof. vm_refl. Qed.
Lemma D_2ae5c : decode_any W_2ae5c = Some (OpImm ALU_ADD 10 18 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2ae60 : bv 32 := 0x02813083.
Lemma F_2ae60 : fetch_word Ubsan.M.loaded_segments (0x2ae60 : word) = Some W_2ae60.
Proof. vm_refl. Qed.
Lemma D_2ae60 : decode_any W_2ae60 = Some (Load SZ8 true 1 2 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2ae64 : bv 32 := 0x02013403.
Lemma F_2ae64 : fetch_word Ubsan.M.loaded_segments (0x2ae64 : word) = Some W_2ae64.
Proof. vm_refl. Qed.
Lemma D_2ae64 : decode_any W_2ae64 = Some (Load SZ8 true 8 2 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2ae68 : bv 32 := 0x01813483.
Lemma F_2ae68 : fetch_word Ubsan.M.loaded_segments (0x2ae68 : word) = Some W_2ae68.
Proof. vm_refl. Qed.
Lemma D_2ae68 : decode_any W_2ae68 = Some (Load SZ8 true 9 2 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2ae6c : bv 32 := 0x01013903.
Lemma F_2ae6c : fetch_word Ubsan.M.loaded_segments (0x2ae6c : word) = Some W_2ae6c.
Proof. vm_refl. Qed.
Lemma D_2ae6c : decode_any W_2ae6c = Some (Load SZ8 true 18 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2ae70 : bv 32 := 0x00813983.
Lemma F_2ae70 : fetch_word Ubsan.M.loaded_segments (0x2ae70 : word) = Some W_2ae70.
Proof. vm_refl. Qed.
Lemma D_2ae70 : decode_any W_2ae70 = Some (Load SZ8 true 19 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2ae74 : bv 32 := 0x03010113.
Lemma F_2ae74 : fetch_word Ubsan.M.loaded_segments (0x2ae74 : word) = Some W_2ae74.
Proof. vm_refl. Qed.
Lemma D_2ae74 : decode_any W_2ae74 = Some (OpImm ALU_ADD 2 2 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2ae78 : bv 32 := 0x00008067.
Lemma F_2ae78 : fetch_word Ubsan.M.loaded_segments (0x2ae78 : word) = Some W_2ae78.
Proof. vm_refl. Qed.
Lemma D_2ae78 : decode_any W_2ae78 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2ae7c : bv 32 := 0x00050067.
Lemma F_2ae7c : fetch_word Ubsan.M.loaded_segments (0x2ae7c : word) = Some W_2ae7c.
Proof. vm_refl. Qed.
Lemma D_2ae7c : decode_any W_2ae7c = Some (Jalr 0 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2ae80 : bv 32 := 0x00008067.
Lemma F_2ae80 : fetch_word Ubsan.M.loaded_segments (0x2ae80 : word) = Some W_2ae80.
Proof. vm_refl. Qed.
Lemma D_2ae80 : decode_any W_2ae80 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2ae84 : bv 32 := 0xfe010113.
Lemma F_2ae84 : fetch_word Ubsan.M.loaded_segments (0x2ae84 : word) = Some W_2ae84.
Proof. vm_refl. Qed.
Lemma D_2ae84 : decode_any W_2ae84 = Some (OpImm ALU_ADD 2 2 4064, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2ae88 : bv 32 := 0x00113c23.
Lemma F_2ae88 : fetch_word Ubsan.M.loaded_segments (0x2ae88 : word) = Some W_2ae88.
Proof. vm_refl. Qed.
Lemma D_2ae88 : decode_any W_2ae88 = Some (Store SZ8 2 1 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2ae8c : bv 32 := 0x00813823.
Lemma F_2ae8c : fetch_word Ubsan.M.loaded_segments (0x2ae8c : word) = Some W_2ae8c.
Proof. vm_refl. Qed.
Lemma D_2ae8c : decode_any W_2ae8c = Some (Store SZ8 2 8 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2ae90 : bv 32 := 0x00913423.
Lemma F_2ae90 : fetch_word Ubsan.M.loaded_segments (0x2ae90 : word) = Some W_2ae90.
Proof. vm_refl. Qed.
Lemma D_2ae90 : decode_any W_2ae90 = Some (Store SZ8 2 9 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2ae94 : bv 32 := 0x00009517.
Lemma F_2ae94 : fetch_word Ubsan.M.loaded_segments (0x2ae94 : word) = Some W_2ae94.
Proof. vm_refl. Qed.
Lemma D_2ae94 : decode_any W_2ae94 = Some (Auipc 10 9, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2ae98 : bv 32 := 0x00009597.
Lemma F_2ae98 : fetch_word Ubsan.M.loaded_segments (0x2ae98 : word) = Some W_2ae98.
Proof. vm_refl. Qed.
Lemma D_2ae98 : decode_any W_2ae98 = Some (Auipc 11 9, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2ae9c : bv 32 := 0xf3453503.
Lemma F_2ae9c : fetch_word Ubsan.M.loaded_segments (0x2ae9c : word) = Some W_2ae9c.
Proof. vm_refl. Qed.
Lemma D_2ae9c : decode_any W_2ae9c = Some (Load SZ8 true 10 10 3892, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2aea0 : bv 32 := 0xf385b403.
Lemma F_2aea0 : fetch_word Ubsan.M.loaded_segments (0x2aea0 : word) = Some W_2aea0.
Proof. vm_refl. Qed.
Lemma D_2aea0 : decode_any W_2aea0 = Some (Load SZ8 true 8 11 3896, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2aea4 : bv 32 := 0x00a47c63.
Lemma F_2aea4 : fetch_word Ubsan.M.loaded_segments (0x2aea4 : word) = Some W_2aea4.
Proof. vm_refl. Qed.
Lemma D_2aea4 : decode_any W_2aea4 = Some (Branch BC_GEU 8 10 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2aea8 : bv 32 := 0xff853583.
Lemma F_2aea8 : fetch_word Ubsan.M.loaded_segments (0x2aea8 : word) = Some W_2aea8.
Proof. vm_refl. Qed.
Lemma D_2aea8 : decode_any W_2aea8 = Some (Load SZ8 true 11 10 4088, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2aeac : bv 32 := 0xff850493.
Lemma F_2aeac : fetch_word Ubsan.M.loaded_segments (0x2aeac : word) = Some W_2aeac.
Proof. vm_refl. Qed.
Lemma D_2aeac : decode_any W_2aeac = Some (OpImm ALU_ADD 9 10 4088, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2aeb0 : bv 32 := 0x000580e7.
Lemma F_2aeb0 : fetch_word Ubsan.M.loaded_segments (0x2aeb0 : word) = Some W_2aeb0.
Proof. vm_refl. Qed.
Lemma D_2aeb0 : decode_any W_2aeb0 = Some (Jalr 1 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2aeb4 : bv 32 := 0x00048513.
Lemma F_2aeb4 : fetch_word Ubsan.M.loaded_segments (0x2aeb4 : word) = Some W_2aeb4.
Proof. vm_refl. Qed.
Lemma D_2aeb4 : decode_any W_2aeb4 = Some (OpImm ALU_ADD 10 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2aeb8 : bv 32 := 0xfe9468e3.
Lemma F_2aeb8 : fetch_word Ubsan.M.loaded_segments (0x2aeb8 : word) = Some W_2aeb8.
Proof. vm_refl. Qed.
Lemma D_2aeb8 : decode_any W_2aeb8 = Some (Branch BC_LTU 8 9 8176, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2aebc : bv 32 := 0x01813083.
Lemma F_2aebc : fetch_word Ubsan.M.loaded_segments (0x2aebc : word) = Some W_2aebc.
Proof. vm_refl. Qed.
Lemma D_2aebc : decode_any W_2aebc = Some (Load SZ8 true 1 2 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2aec0 : bv 32 := 0x01013403.
Lemma F_2aec0 : fetch_word Ubsan.M.loaded_segments (0x2aec0 : word) = Some W_2aec0.
Proof. vm_refl. Qed.
Lemma D_2aec0 : decode_any W_2aec0 = Some (Load SZ8 true 8 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2aec4 : bv 32 := 0x00813483.
Lemma F_2aec4 : fetch_word Ubsan.M.loaded_segments (0x2aec4 : word) = Some W_2aec4.
Proof. vm_refl. Qed.
Lemma D_2aec4 : decode_any W_2aec4 = Some (Load SZ8 true 9 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2aec8 : bv 32 := 0x02010113.
Lemma F_2aec8 : fetch_word Ubsan.M.loaded_segments (0x2aec8 : word) = Some W_2aec8.
Proof. vm_refl. Qed.
Lemma D_2aec8 : decode_any W_2aec8 = Some (OpImm ALU_ADD 2 2 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2aecc : bv 32 := 0xfb5ff06f.
Lemma F_2aecc : fetch_word Ubsan.M.loaded_segments (0x2aecc : word) = Some W_2aecc.
Proof. vm_refl. Qed.
Lemma D_2aecc : decode_any W_2aecc = Some (Jal 0 2097076, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2aed0 : bv 32 := 0xff010113.
Lemma F_2aed0 : fetch_word Ubsan.M.loaded_segments (0x2aed0 : word) = Some W_2aed0.
Proof. vm_refl. Qed.
Lemma D_2aed0 : decode_any W_2aed0 = Some (OpImm ALU_ADD 2 2 4080, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2aed4 : bv 32 := 0x00113423.
Lemma F_2aed4 : fetch_word Ubsan.M.loaded_segments (0x2aed4 : word) = Some W_2aed4.
Proof. vm_refl. Qed.
Lemma D_2aed4 : decode_any W_2aed4 = Some (Store SZ8 2 1 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2aed8 : bv 32 := 0x00813023.
Lemma F_2aed8 : fetch_word Ubsan.M.loaded_segments (0x2aed8 : word) = Some W_2aed8.
Proof. vm_refl. Qed.
Lemma D_2aed8 : decode_any W_2aed8 = Some (Store SZ8 2 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2aedc : bv 32 := 0x00000593.
Lemma F_2aedc : fetch_word Ubsan.M.loaded_segments (0x2aedc : word) = Some W_2aedc.
Proof. vm_refl. Qed.
Lemma D_2aedc : decode_any W_2aedc = Some (OpImm ALU_ADD 11 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2aee0 : bv 32 := 0x00020613.
Lemma F_2aee0 : fetch_word Ubsan.M.loaded_segments (0x2aee0 : word) = Some W_2aee0.
Proof. vm_refl. Qed.
Lemma D_2aee0 : decode_any W_2aee0 = Some (OpImm ALU_ADD 12 4 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2aee4 : bv 32 := 0xf5862603.
Lemma F_2aee4 : fetch_word Ubsan.M.loaded_segments (0x2aee4 : word) = Some W_2aee4.
Proof. vm_refl. Qed.
Lemma D_2aee4 : decode_any W_2aee4 = Some (Load SZ4 true 12 12 3928, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2aee8 : bv 32 := 0x0003a697.
Lemma F_2aee8 : fetch_word Ubsan.M.loaded_segments (0x2aee8 : word) = Some W_2aee8.
Proof. vm_refl. Qed.
Lemma D_2aee8 : decode_any W_2aee8 = Some (Auipc 13 58, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2aeec : bv 32 := 0x7f868693.
Lemma F_2aeec : fetch_word Ubsan.M.loaded_segments (0x2aeec : word) = Some W_2aeec.
Proof. vm_refl. Qed.
Lemma D_2aeec : decode_any W_2aeec = Some (OpImm ALU_ADD 13 13 2040, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2aef0 : bv 32 := 0x1606a72f.
Lemma F_2aef0 : fetch_word Ubsan.M.loaded_segments (0x2aef0 : word) = Some W_2aef0.
Proof. vm_refl. Qed.
Lemma D_2aef0 : decode_any W_2aef0 = Some (Lr AW true true 14 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2aef4 : bv 32 := 0x00b71663.
Lemma F_2aef4 : fetch_word Ubsan.M.loaded_segments (0x2aef4 : word) = Some W_2aef4.
Proof. vm_refl. Qed.
Lemma D_2aef4 : decode_any W_2aef4 = Some (Branch BC_NE 14 11 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2aef8 : bv 32 := 0x1ec6a7af.
Lemma F_2aef8 : fetch_word Ubsan.M.loaded_segments (0x2aef8 : word) = Some W_2aef8.
Proof. vm_refl. Qed.
Lemma D_2aef8 : decode_any W_2aef8 = Some (Sc AW true true 15 13 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2aefc : bv 32 := 0xfe079ae3.
Lemma F_2aefc : fetch_word Ubsan.M.loaded_segments (0x2aefc : word) = Some W_2aefc.
Proof. vm_refl. Qed.
Lemma D_2aefc : decode_any W_2aefc = Some (Branch BC_NE 15 0 8180, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2af00 : bv 32 := 0x0007059b.
Lemma F_2af00 : fetch_word Ubsan.M.loaded_segments (0x2af00 : word) = Some W_2af00.
Proof. vm_refl. Qed.
Lemma D_2af00 : decode_any W_2af00 = Some (OpImm32 11 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2af04 : bv 32 := 0x02c58263.
Lemma F_2af04 : fetch_word Ubsan.M.loaded_segments (0x2af04 : word) = Some W_2af04.
Proof. vm_refl. Qed.
Lemma D_2af04 : decode_any W_2af04 = Some (Branch BC_EQ 11 12 36, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2af08 : bv 32 := 0x02058263.
Lemma F_2af08 : fetch_word Ubsan.M.loaded_segments (0x2af08 : word) = Some W_2af08.
Proof. vm_refl. Qed.
Lemma D_2af08 : decode_any W_2af08 = Some (Branch BC_EQ 11 0 36, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2af0c : bv 32 := 0x04900893.
Lemma F_2af0c : fetch_word Ubsan.M.loaded_segments (0x2af0c : word) = Some W_2af0c.
Proof. vm_refl. Qed.
Lemma D_2af0c : decode_any W_2af0c = Some (OpImm ALU_ADD 17 0 73, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2af10 : bv 32 := 0x00000593.
Lemma F_2af10 : fetch_word Ubsan.M.loaded_segments (0x2af10 : word) = Some W_2af10.
Proof. vm_refl. Qed.
Lemma D_2af10 : decode_any W_2af10 = Some (OpImm ALU_ADD 11 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2af14 : bv 32 := 0x00000613.
Lemma F_2af14 : fetch_word Ubsan.M.loaded_segments (0x2af14 : word) = Some W_2af14.
Proof. vm_refl. Qed.
Lemma D_2af14 : decode_any W_2af14 = Some (OpImm ALU_ADD 12 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2af18 : bv 32 := 0x00000693.
Lemma F_2af18 : fetch_word Ubsan.M.loaded_segments (0x2af18 : word) = Some W_2af18.
Proof. vm_refl. Qed.
Lemma D_2af18 : decode_any W_2af18 = Some (OpImm ALU_ADD 13 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2af1c : bv 32 := 0x00000513.
Lemma F_2af1c : fetch_word Ubsan.M.loaded_segments (0x2af1c : word) = Some W_2af1c.
Proof. vm_refl. Qed.
Lemma D_2af1c : decode_any W_2af1c = Some (OpImm ALU_ADD 10 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2af20 : bv 32 := 0x00000073.
Lemma F_2af20 : fetch_word Ubsan.M.loaded_segments (0x2af20 : word) = Some W_2af20.
Proof. vm_refl. Qed.
Lemma E_2af20 : is_ecall W_2af20 = true.
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2af24 : bv 32 := 0xff9ff06f.
Lemma F_2af24 : fetch_word Ubsan.M.loaded_segments (0x2af24 : word) = Some W_2af24.
Proof. vm_refl. Qed.
Lemma D_2af24 : decode_any W_2af24 = Some (Jal 0 2097144, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2af28 : bv 32 := 0x00000023.
Lemma F_2af28 : fetch_word Ubsan.M.loaded_segments (0x2af28 : word) = Some W_2af28.
Proof. vm_refl. Qed.
Lemma D_2af28 : decode_any W_2af28 = Some (Store SZ1 0 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2af2c : bv 32 := 0x00050413.
Lemma F_2af2c : fetch_word Ubsan.M.loaded_segments (0x2af2c : word) = Some W_2af2c.
Proof. vm_refl. Qed.
Lemma D_2af2c : decode_any W_2af2c = Some (OpImm ALU_ADD 8 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2af30 : bv 32 := 0xdbdff0ef.
Lemma F_2af30 : fetch_word Ubsan.M.loaded_segments (0x2af30 : word) = Some W_2af30.
Proof. vm_refl. Qed.
Lemma D_2af30 : decode_any W_2af30 = Some (Jal 1 2096572, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2af34 : bv 32 := 0xf51ff0ef.
Lemma F_2af34 : fetch_word Ubsan.M.loaded_segments (0x2af34 : word) = Some W_2af34.
Proof. vm_refl. Qed.
Lemma D_2af34 : decode_any W_2af34 = Some (Jal 1 2096976, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2af38 : bv 32 := 0x160020ef.
Lemma F_2af38 : fetch_word Ubsan.M.loaded_segments (0x2af38 : word) = Some W_2af38.
Proof. vm_refl. Qed.
Lemma D_2af38 : decode_any W_2af38 = Some (Jal 1 8544, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2af3c : bv 32 := 0x00040513.
Lemma F_2af3c : fetch_word Ubsan.M.loaded_segments (0x2af3c : word) = Some W_2af3c.
Proof. vm_refl. Qed.
Lemma D_2af3c : decode_any W_2af3c = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2af40 : bv 32 := 0xd91ff0ef.
Lemma F_2af40 : fetch_word Ubsan.M.loaded_segments (0x2af40 : word) = Some W_2af40.
Proof. vm_refl. Qed.
Lemma D_2af40 : decode_any W_2af40 = Some (Jal 1 2096528, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_32944 : bv 32 := 0x00033597.
Lemma F_32944 : fetch_word Ubsan.M.loaded_segments (0x32944 : word) = Some W_32944.
Proof. vm_refl. Qed.
Lemma D_32944 : decode_any W_32944 = Some (Auipc 11 51, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_32948 : bv 32 := 0xdc758683.
Lemma F_32948 : fetch_word Ubsan.M.loaded_segments (0x32948 : word) = Some W_32948.
Proof. vm_refl. Qed.
Lemma D_32948 : decode_any W_32948 = Some (Load SZ1 true 13 11 3527, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_3294c : bv 32 := 0x1e068863.
Lemma F_3294c : fetch_word Ubsan.M.loaded_segments (0x3294c : word) = Some W_3294c.
Proof. vm_refl. Qed.
Lemma D_3294c : decode_any W_3294c = Some (Branch BC_EQ 13 0 496, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_32b3c : bv 32 := 0x00008067.
Lemma F_32b3c : fetch_word Ubsan.M.loaded_segments (0x32b3c : word) = Some W_32b3c.
Proof. vm_refl. Qed.
Lemma D_32b3c : decode_any W_32b3c = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_32bcc : bv 32 := 0x00052583.
Lemma F_32bcc : fetch_word Ubsan.M.loaded_segments (0x32bcc : word) = Some W_32bcc.
Proof. vm_refl. Qed.
Lemma D_32bcc : decode_any W_32bcc = Some (Load SZ4 true 11 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_32bd0 : bv 32 := 0x0005c463.
Lemma F_32bd0 : fetch_word Ubsan.M.loaded_segments (0x32bd0 : word) = Some W_32bd0.
Proof. vm_refl. Qed.
Lemma D_32bd0 : decode_any W_32bd0 = Some (Branch BC_LT 11 0 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_32bd4 : bv 32 := 0x00008067.
Lemma F_32bd4 : fetch_word Ubsan.M.loaded_segments (0x32bd4 : word) = Some W_32bd4.
Proof. vm_refl. Qed.
Lemma D_32bd4 : decode_any W_32bd4 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

