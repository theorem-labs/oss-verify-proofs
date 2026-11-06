(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
(* [comment removed for export] *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require BvWfKernel.

From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.jsoncons.fuzz_ubjson_encoder.images Require Import Asan.
Open Scope bv_scope.

Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

Definition W_57184 : bv 32 := 0x000e7517.
Lemma F_57184 : fetch_word Asan.M.loaded_segments (0x571d4 : word) = Some W_57184.
Proof. vm_refl. Qed.
Lemma D_57184 : decode_any W_57184 = Some (Auipc 10 231, 4%Z).
Proof. vm_refl. Qed.

Definition W_57188 : bv 32 := 0x1e453503.
Lemma F_57188 : fetch_word Asan.M.loaded_segments (0x571d8 : word) = Some W_57188.
Proof. vm_refl. Qed.
Lemma D_57188 : decode_any W_57188 = Some (Load SZ8 true 10 10 484, 4%Z).
Proof. vm_refl. Qed.

Definition W_5718c : bv 32 := 0x06a76463.
Lemma F_5718c : fetch_word Asan.M.loaded_segments (0x571dc : word) = Some W_5718c.
Proof. vm_refl. Qed.
Lemma D_5718c : decode_any W_5718c = Some (Branch BC_LTU 14 10 104, 4%Z).
Proof. vm_refl. Qed.

Definition W_57190 : bv 32 := 0x00100593.
Lemma F_57190 : fetch_word Asan.M.loaded_segments (0x571e0 : word) = Some W_57190.
Proof. vm_refl. Qed.
Lemma D_57190 : decode_any W_57190 = Some (OpImm ALU_ADD 11 0 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_57194 : bv 32 := 0x02559593.
Lemma F_57194 : fetch_word Asan.M.loaded_segments (0x571e4 : word) = Some W_57194.
Proof. vm_refl. Qed.
Lemma D_57194 : decode_any W_57194 = Some (ShiftImm ALU_SLL 11 11 37, 4%Z).
Proof. vm_refl. Qed.

Definition W_57198 : bv 32 := 0x00b50533.
Lemma F_57198 : fetch_word Asan.M.loaded_segments (0x571e8 : word) = Some W_57198.
Proof. vm_refl. Qed.
Lemma D_57198 : decode_any W_57198 = Some (Op ALU_ADD 10 10 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_5719c : bv 32 := 0x04a77c63.
Lemma F_5719c : fetch_word Asan.M.loaded_segments (0x571ec : word) = Some W_5719c.
Proof. vm_refl. Qed.
Lemma D_5719c : decode_any W_5719c = Some (Branch BC_GEU 14 10 88, 4%Z).
Proof. vm_refl. Qed.

Definition W_571a0 : bv 32 := 0x000e2517.
Lemma F_571a0 : fetch_word Asan.M.loaded_segments (0x571f0 : word) = Some W_571a0.
Proof. vm_refl. Qed.
Lemma D_571a0 : decode_any W_571a0 = Some (Auipc 10 226, 4%Z).
Proof. vm_refl. Qed.

Definition W_571a4 : bv 32 := 0xfc053583.
Lemma F_571a4 : fetch_word Asan.M.loaded_segments (0x571f4 : word) = Some W_571a4.
Proof. vm_refl. Qed.
Lemma D_571a4 : decode_any W_571a4 = Some (Load SZ8 true 11 10 4032, 4%Z).
Proof. vm_refl. Qed.

Definition W_571a8 : bv 32 := 0x0305a683.
Lemma F_571a8 : fetch_word Asan.M.loaded_segments (0x571f8 : word) = Some W_571a8.
Proof. vm_refl. Qed.
Lemma D_571a8 : decode_any W_571a8 = Some (Load SZ4 true 13 11 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_571ac : bv 32 := 0x04d05463.
Lemma F_571ac : fetch_word Asan.M.loaded_segments (0x571fc : word) = Some W_571ac.
Proof. vm_refl. Qed.
Lemma D_571ac : decode_any W_571ac = Some (Branch BC_GE 0 13 72, 4%Z).
Proof. vm_refl. Qed.

Definition W_571b0 : bv 32 := 0x00275503.
Lemma F_571b0 : fetch_word Asan.M.loaded_segments (0x57200 : word) = Some W_571b0.
Proof. vm_refl. Qed.
Lemma D_571b0 : decode_any W_571b0 = Some (Load SZ2 false 10 14 2, 4%Z).
Proof. vm_refl. Qed.

Definition W_571b4 : bv 32 := 0x00476603.
Lemma F_571b4 : fetch_word Asan.M.loaded_segments (0x57204 : word) = Some W_571b4.
Proof. vm_refl. Qed.
Lemma D_571b4 : decode_any W_571b4 = Some (Load SZ4 false 12 14 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_571b8 : bv 32 := 0x02051513.
Lemma F_571b8 : fetch_word Asan.M.loaded_segments (0x57208 : word) = Some W_571b8.
Proof. vm_refl. Qed.
Lemma D_571b8 : decode_any W_571b8 = Some (ShiftImm ALU_SLL 10 10 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_571bc : bv 32 := 0x00c56633.
Lemma F_571bc : fetch_word Asan.M.loaded_segments (0x5720c : word) = Some W_571bc.
Proof. vm_refl. Qed.
Lemma D_571bc : decode_any W_571bc = Some (Op ALU_OR 12 10 12, 4%Z).
Proof. vm_refl. Qed.

Definition W_571c0 : bv 32 := 0x00800513.
Lemma F_571c0 : fetch_word Asan.M.loaded_segments (0x57210 : word) = Some W_571c0.
Proof. vm_refl. Qed.
Lemma D_571c0 : decode_any W_571c0 = Some (OpImm ALU_ADD 10 0 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_571c4 : bv 32 := 0x02a66863.
Lemma F_571c4 : fetch_word Asan.M.loaded_segments (0x57214 : word) = Some W_571c4.
Proof. vm_refl. Qed.
Lemma D_571c4 : decode_any W_571c4 = Some (Branch BC_LTU 12 10 48, 4%Z).
Proof. vm_refl. Qed.

Definition W_571c8 : bv 32 := 0xff860613.
Lemma F_571c8 : fetch_word Asan.M.loaded_segments (0x57218 : word) = Some W_571c8.
Proof. vm_refl. Qed.
Lemma D_571c8 : decode_any W_571c8 = Some (OpImm ALU_ADD 12 12 4088, 4%Z).
Proof. vm_refl. Qed.

Definition W_571cc : bv 32 := 0x00070913.
Lemma F_571cc : fetch_word Asan.M.loaded_segments (0x5721c : word) = Some W_571cc.
Proof. vm_refl. Qed.
Lemma D_571cc : decode_any W_571cc = Some (OpImm ALU_ADD 18 14 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_571d0 : bv 32 := 0x01870513.
Lemma F_571d0 : fetch_word Asan.M.loaded_segments (0x57220 : word) = Some W_571d0.
Proof. vm_refl. Qed.
Lemma D_571d0 : decode_any W_571d0 = Some (OpImm ALU_ADD 10 14 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_571d4 : bv 32 := 0x00d66463.
Lemma F_571d4 : fetch_word Asan.M.loaded_segments (0x57224 : word) = Some W_571d4.
Proof. vm_refl. Qed.
Lemma D_571d4 : decode_any W_571d4 = Some (Branch BC_LTU 12 13 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_571d8 : bv 32 := 0x00068613.
Lemma F_571d8 : fetch_word Asan.M.loaded_segments (0x57228 : word) = Some W_571d8.
Proof. vm_refl. Qed.
Lemma D_571d8 : decode_any W_571d8 = Some (OpImm ALU_ADD 12 13 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_571dc : bv 32 := 0x000e2697.
Lemma F_571dc : fetch_word Asan.M.loaded_segments (0x5722c : word) = Some W_571dc.
Proof. vm_refl. Qed.
Lemma D_571dc : decode_any W_571dc = Some (Auipc 13 226, 4%Z).
Proof. vm_refl. Qed.

Definition W_571e0 : bv 32 := 0xfac6b683.
Lemma F_571e0 : fetch_word Asan.M.loaded_segments (0x57230 : word) = Some W_571e0.
Proof. vm_refl. Qed.
Lemma D_571e0 : decode_any W_571e0 = Some (Load SZ8 true 13 13 4012, 4%Z).
Proof. vm_refl. Qed.

Definition W_571e4 : bv 32 := 0x0006b683.
Lemma F_571e4 : fetch_word Asan.M.loaded_segments (0x57234 : word) = Some W_571e4.
Proof. vm_refl. Qed.
Lemma D_571e4 : decode_any W_571e4 = Some (Load SZ8 true 13 13 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_571e8 : bv 32 := 0x0385a583.
Lemma F_571e8 : fetch_word Asan.M.loaded_segments (0x57238 : word) = Some W_571e8.
Proof. vm_refl. Qed.
Lemma D_571e8 : decode_any W_571e8 = Some (Load SZ4 true 11 11 56, 4%Z).
Proof. vm_refl. Qed.

Definition W_571ec : bv 32 := 0x000680e7.
Lemma F_571ec : fetch_word Asan.M.loaded_segments (0x5723c : word) = Some W_571ec.
Proof. vm_refl. Qed.
Lemma D_571ec : decode_any W_571ec = Some (Jalr 1 13 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_571f0 : bv 32 := 0x00090713.
Lemma F_571f0 : fetch_word Asan.M.loaded_segments (0x57240 : word) = Some W_571f0.
Proof. vm_refl. Qed.
Lemma D_571f0 : decode_any W_571f0 = Some (OpImm ALU_ADD 14 18 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_571f4 : bv 32 := 0x00010513.
Lemma F_571f4 : fetch_word Asan.M.loaded_segments (0x57244 : word) = Some W_571f4.
Proof. vm_refl. Qed.
Lemma D_571f4 : decode_any W_571f4 = Some (OpImm ALU_ADD 10 2 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_571f8 : bv 32 := 0x00070593.
Lemma F_571f8 : fetch_word Asan.M.loaded_segments (0x57248 : word) = Some W_571f8.
Proof. vm_refl. Qed.
Lemma D_571f8 : decode_any W_571f8 = Some (OpImm ALU_ADD 11 14 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_571fc : bv 32 := 0xe91fd0ef.
Lemma F_571fc : fetch_word Asan.M.loaded_segments (0x5724c : word) = Some W_571fc.
Proof. vm_refl. Qed.
Lemma D_571fc : decode_any W_571fc = Some (Jal 1 2088592, 4%Z).
Proof. vm_refl. Qed.

Definition W_57200 : bv 32 := 0x0184b503.
Lemma F_57200 : fetch_word Asan.M.loaded_segments (0x57250 : word) = Some W_57200.
Proof. vm_refl. Qed.
Lemma D_57200 : decode_any W_57200 = Some (Load SZ8 true 10 9 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_57204 : bv 32 := 0x00ab7c63.
Lemma F_57204 : fetch_word Asan.M.loaded_segments (0x57254 : word) = Some W_57204.
Proof. vm_refl. Qed.
Lemma D_57204 : decode_any W_57204 = Some (Branch BC_GEU 22 10 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_57208 : bv 32 := 0x00013603.
Lemma F_57208 : fetch_word Asan.M.loaded_segments (0x57258 : word) = Some W_57208.
Proof. vm_refl. Qed.
Lemma D_57208 : decode_any W_57208 = Some (Load SZ8 true 12 2 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_5720c : bv 32 := 0x00813683.
Lemma F_5720c : fetch_word Asan.M.loaded_segments (0x5725c : word) = Some W_5720c.
Proof. vm_refl. Qed.
Lemma D_5720c : decode_any W_5720c = Some (Load SZ8 true 13 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_57210 : bv 32 := 0x00040513.
Lemma F_57210 : fetch_word Asan.M.loaded_segments (0x57260 : word) = Some W_57210.
Proof. vm_refl. Qed.
Lemma D_57210 : decode_any W_57210 = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_57214 : bv 32 := 0x00048593.
Lemma F_57214 : fetch_word Asan.M.loaded_segments (0x57264 : word) = Some W_57214.
Proof. vm_refl. Qed.
Lemma D_57214 : decode_any W_57214 = Some (OpImm ALU_ADD 11 9 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_57218 : bv 32 := 0x831fd0ef.
Lemma F_57218 : fetch_word Asan.M.loaded_segments (0x57268 : word) = Some W_57218.
Proof. vm_refl. Qed.
Lemma D_57218 : decode_any W_57218 = Some (Jal 1 2086960, 4%Z).
Proof. vm_refl. Qed.
