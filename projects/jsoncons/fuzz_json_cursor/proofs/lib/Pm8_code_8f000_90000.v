(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.jsoncons.fuzz_json_cursor.images Require Import Asan.
Open Scope bv_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Hint Extern 0 (BvWf _ _) =>
  (lazymatch goal with |- BvWf ?n ?v => is_closed_term n; is_closed_term v end; exact I) : typeclass_instances.
Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

Definition W_8f248 : bv 32 := 0xfe010113.
Lemma F_8f248 : fetch_word Asan.M.loaded_segments (0x8f298 : word) = Some W_8f248.
Proof. vm_refl. Qed.
Lemma D_8f248 : decode_any W_8f248 = Some (OpImm ALU_ADD 2 2 4064, 4%Z).
Proof. vm_refl. Qed.

Definition W_8f24c : bv 32 := 0x00113c23.
Lemma F_8f24c : fetch_word Asan.M.loaded_segments (0x8f29c : word) = Some W_8f24c.
Proof. vm_refl. Qed.
Lemma D_8f24c : decode_any W_8f24c = Some (Store SZ8 2 1 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_8f250 : bv 32 := 0x00813823.
Lemma F_8f250 : fetch_word Asan.M.loaded_segments (0x8f2a0 : word) = Some W_8f250.
Proof. vm_refl. Qed.
Lemma D_8f250 : decode_any W_8f250 = Some (Store SZ8 2 8 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_8f254 : bv 32 := 0x00913423.
Lemma F_8f254 : fetch_word Asan.M.loaded_segments (0x8f2a4 : word) = Some W_8f254.
Proof. vm_refl. Qed.
Lemma D_8f254 : decode_any W_8f254 = Some (Store SZ8 2 9 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_8f258 : bv 32 := 0x01213023.
Lemma F_8f258 : fetch_word Asan.M.loaded_segments (0x8f2a8 : word) = Some W_8f258.
Proof. vm_refl. Qed.
Lemma D_8f258 : decode_any W_8f258 = Some (Store SZ8 2 18 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_8f25c : bv 32 := 0x00058413.
Lemma F_8f25c : fetch_word Asan.M.loaded_segments (0x8f2ac : word) = Some W_8f25c.
Proof. vm_refl. Qed.
Lemma D_8f25c : decode_any W_8f25c = Some (OpImm ALU_ADD 8 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_8f260 : bv 32 := 0x00050493.
Lemma F_8f260 : fetch_word Asan.M.loaded_segments (0x8f2b0 : word) = Some W_8f260.
Proof. vm_refl. Qed.
Lemma D_8f260 : decode_any W_8f260 = Some (OpImm ALU_ADD 9 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_8f264 : bv 32 := 0x09c000ef.
Lemma F_8f264 : fetch_word Asan.M.loaded_segments (0x8f2b4 : word) = Some W_8f264.
Proof. vm_refl. Qed.
Lemma D_8f264 : decode_any W_8f264 = Some (Jal 1 156, 4%Z).
Proof. vm_refl. Qed.

Definition W_8f268 : bv 32 := 0x0015f517.
Lemma F_8f268 : fetch_word Asan.M.loaded_segments (0x8f2b8 : word) = Some W_8f268.
Proof. vm_refl. Qed.
Lemma D_8f268 : decode_any W_8f268 = Some (Auipc 10 351, 4%Z).
Proof. vm_refl. Qed.

Definition W_8f26c : bv 32 := 0x1c850913.
Lemma F_8f26c : fetch_word Asan.M.loaded_segments (0x8f2bc : word) = Some W_8f26c.
Proof. vm_refl. Qed.
Lemma D_8f26c : decode_any W_8f26c = Some (OpImm ALU_ADD 18 10 456, 4%Z).
Proof. vm_refl. Qed.

Definition W_8f270 : bv 32 := 0x00093603.
Lemma F_8f270 : fetch_word Asan.M.loaded_segments (0x8f2c0 : word) = Some W_8f270.
Proof. vm_refl. Qed.
Lemma D_8f270 : decode_any W_8f270 = Some (Load SZ8 true 12 18 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_8f274 : bv 32 := 0x06060a63.
Lemma F_8f274 : fetch_word Asan.M.loaded_segments (0x8f2c4 : word) = Some W_8f274.
Proof. vm_refl. Qed.
Lemma D_8f274 : decode_any W_8f274 = Some (Branch BC_EQ 12 0 116, 4%Z).
Proof. vm_refl. Qed.

Definition W_8f2e8 : bv 32 := 0x01813083.
Lemma F_8f2e8 : fetch_word Asan.M.loaded_segments (0x8f338 : word) = Some W_8f2e8.
Proof. vm_refl. Qed.
Lemma D_8f2e8 : decode_any W_8f2e8 = Some (Load SZ8 true 1 2 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_8f2ec : bv 32 := 0x01013403.
Lemma F_8f2ec : fetch_word Asan.M.loaded_segments (0x8f33c : word) = Some W_8f2ec.
Proof. vm_refl. Qed.
Lemma D_8f2ec : decode_any W_8f2ec = Some (Load SZ8 true 8 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_8f2f0 : bv 32 := 0x00813483.
Lemma F_8f2f0 : fetch_word Asan.M.loaded_segments (0x8f340 : word) = Some W_8f2f0.
Proof. vm_refl. Qed.
Lemma D_8f2f0 : decode_any W_8f2f0 = Some (Load SZ8 true 9 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_8f2f4 : bv 32 := 0x00013903.
Lemma F_8f2f4 : fetch_word Asan.M.loaded_segments (0x8f344 : word) = Some W_8f2f4.
Proof. vm_refl. Qed.
Lemma D_8f2f4 : decode_any W_8f2f4 = Some (Load SZ8 true 18 2 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_8f2f8 : bv 32 := 0x02010113.
Lemma F_8f2f8 : fetch_word Asan.M.loaded_segments (0x8f348 : word) = Some W_8f2f8.
Proof. vm_refl. Qed.
Lemma D_8f2f8 : decode_any W_8f2f8 = Some (OpImm ALU_ADD 2 2 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_8f2fc : bv 32 := 0x00008067.
Lemma F_8f2fc : fetch_word Asan.M.loaded_segments (0x8f34c : word) = Some W_8f2fc.
Proof. vm_refl. Qed.
Lemma D_8f2fc : decode_any W_8f2fc = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_8f300 : bv 32 := 0x00008067.
Lemma F_8f300 : fetch_word Asan.M.loaded_segments (0x8f350 : word) = Some W_8f300.
Proof. vm_refl. Qed.
Lemma D_8f300 : decode_any W_8f300 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_8f304 : bv 32 := 0xfe010113.
Lemma F_8f304 : fetch_word Asan.M.loaded_segments (0x8f354 : word) = Some W_8f304.
Proof. vm_refl. Qed.
Lemma D_8f304 : decode_any W_8f304 = Some (OpImm ALU_ADD 2 2 4064, 4%Z).
Proof. vm_refl. Qed.

Definition W_8f308 : bv 32 := 0x00113c23.
Lemma F_8f308 : fetch_word Asan.M.loaded_segments (0x8f358 : word) = Some W_8f308.
Proof. vm_refl. Qed.
Lemma D_8f308 : decode_any W_8f308 = Some (Store SZ8 2 1 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_8f30c : bv 32 := 0x00813823.
Lemma F_8f30c : fetch_word Asan.M.loaded_segments (0x8f35c : word) = Some W_8f30c.
Proof. vm_refl. Qed.
Lemma D_8f30c : decode_any W_8f30c = Some (Store SZ8 2 8 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_8f310 : bv 32 := 0x00913423.
Lemma F_8f310 : fetch_word Asan.M.loaded_segments (0x8f360 : word) = Some W_8f310.
Proof. vm_refl. Qed.
Lemma D_8f310 : decode_any W_8f310 = Some (Store SZ8 2 9 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_8f314 : bv 32 := 0x00050413.
Lemma F_8f314 : fetch_word Asan.M.loaded_segments (0x8f364 : word) = Some W_8f314.
Proof. vm_refl. Qed.
Lemma D_8f314 : decode_any W_8f314 = Some (OpImm ALU_ADD 8 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_8f318 : bv 32 := 0x098000ef.
Lemma F_8f318 : fetch_word Asan.M.loaded_segments (0x8f368 : word) = Some W_8f318.
Proof. vm_refl. Qed.
Lemma D_8f318 : decode_any W_8f318 = Some (Jal 1 152, 4%Z).
Proof. vm_refl. Qed.

Definition W_8f31c : bv 32 := 0x00050e63.
Lemma F_8f31c : fetch_word Asan.M.loaded_segments (0x8f36c : word) = Some W_8f31c.
Proof. vm_refl. Qed.
Lemma D_8f31c : decode_any W_8f31c = Some (Branch BC_EQ 10 0 28, 4%Z).
Proof. vm_refl. Qed.

Definition W_8f338 : bv 32 := 0x00040513.
Lemma F_8f338 : fetch_word Asan.M.loaded_segments (0x8f388 : word) = Some W_8f338.
Proof. vm_refl. Qed.
Lemma D_8f338 : decode_any W_8f338 = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_8f33c : bv 32 := 0x07c000ef.
Lemma F_8f33c : fetch_word Asan.M.loaded_segments (0x8f38c : word) = Some W_8f33c.
Proof. vm_refl. Qed.
Lemma D_8f33c : decode_any W_8f33c = Some (Jal 1 124, 4%Z).
Proof. vm_refl. Qed.

Definition W_8f340 : bv 32 := 0x0015f517.
Lemma F_8f340 : fetch_word Asan.M.loaded_segments (0x8f390 : word) = Some W_8f340.
Proof. vm_refl. Qed.
Lemma D_8f340 : decode_any W_8f340 = Some (Auipc 10 351, 4%Z).
Proof. vm_refl. Qed.

Definition W_8f344 : bv 32 := 0x0f050493.
Lemma F_8f344 : fetch_word Asan.M.loaded_segments (0x8f394 : word) = Some W_8f344.
Proof. vm_refl. Qed.
Lemma D_8f344 : decode_any W_8f344 = Some (OpImm ALU_ADD 9 10 240, 4%Z).
Proof. vm_refl. Qed.

Definition W_8f348 : bv 32 := 0x0084b583.
Lemma F_8f348 : fetch_word Asan.M.loaded_segments (0x8f398 : word) = Some W_8f348.
Proof. vm_refl. Qed.
Lemma D_8f348 : decode_any W_8f348 = Some (Load SZ8 true 11 9 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_8f34c : bv 32 := 0x04058663.
Lemma F_8f34c : fetch_word Asan.M.loaded_segments (0x8f39c : word) = Some W_8f34c.
Proof. vm_refl. Qed.
Lemma D_8f34c : decode_any W_8f34c = Some (Branch BC_EQ 11 0 76, 4%Z).
Proof. vm_refl. Qed.

Definition W_8f398 : bv 32 := 0x00000513.
Lemma F_8f398 : fetch_word Asan.M.loaded_segments (0x8f3e8 : word) = Some W_8f398.
Proof. vm_refl. Qed.
Lemma D_8f398 : decode_any W_8f398 = Some (OpImm ALU_ADD 10 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_8f39c : bv 32 := 0x01813083.
Lemma F_8f39c : fetch_word Asan.M.loaded_segments (0x8f3ec : word) = Some W_8f39c.
Proof. vm_refl. Qed.
Lemma D_8f39c : decode_any W_8f39c = Some (Load SZ8 true 1 2 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_8f3a0 : bv 32 := 0x01013403.
Lemma F_8f3a0 : fetch_word Asan.M.loaded_segments (0x8f3f0 : word) = Some W_8f3a0.
Proof. vm_refl. Qed.
Lemma D_8f3a0 : decode_any W_8f3a0 = Some (Load SZ8 true 8 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_8f3a4 : bv 32 := 0x00813483.
Lemma F_8f3a4 : fetch_word Asan.M.loaded_segments (0x8f3f4 : word) = Some W_8f3a4.
Proof. vm_refl. Qed.
Lemma D_8f3a4 : decode_any W_8f3a4 = Some (Load SZ8 true 9 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_8f3a8 : bv 32 := 0x02010113.
Lemma F_8f3a8 : fetch_word Asan.M.loaded_segments (0x8f3f8 : word) = Some W_8f3a8.
Proof. vm_refl. Qed.
Lemma D_8f3a8 : decode_any W_8f3a8 = Some (OpImm ALU_ADD 2 2 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_8f3ac : bv 32 := 0x00008067.
Lemma F_8f3ac : fetch_word Asan.M.loaded_segments (0x8f3fc : word) = Some W_8f3ac.
Proof. vm_refl. Qed.
Lemma D_8f3ac : decode_any W_8f3ac = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_8f3b0 : bv 32 := 0x00000513.
Lemma F_8f3b0 : fetch_word Asan.M.loaded_segments (0x8f400 : word) = Some W_8f3b0.
Proof. vm_refl. Qed.
Lemma D_8f3b0 : decode_any W_8f3b0 = Some (OpImm ALU_ADD 10 0 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_8f3b4 : bv 32 := 0x00008067.
Lemma F_8f3b4 : fetch_word Asan.M.loaded_segments (0x8f404 : word) = Some W_8f3b4.
Proof. vm_refl. Qed.
Lemma D_8f3b4 : decode_any W_8f3b4 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_8f3b8 : bv 32 := 0x00008067.
Lemma F_8f3b8 : fetch_word Asan.M.loaded_segments (0x8f408 : word) = Some W_8f3b8.
Proof. vm_refl. Qed.
Lemma D_8f3b8 : decode_any W_8f3b8 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

