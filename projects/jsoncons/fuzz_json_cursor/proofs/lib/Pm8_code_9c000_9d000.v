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

Definition W_9c20c : bv 32 := 0xfe010113.
Lemma F_9c20c : fetch_word Asan.M.loaded_segments (0x9c25c : word) = Some W_9c20c.
Proof. vm_refl. Qed.
Lemma D_9c20c : decode_any W_9c20c = Some (OpImm ALU_ADD 2 2 4064, 4%Z).
Proof. vm_refl. Qed.

Definition W_9c210 : bv 32 := 0x00113c23.
Lemma F_9c210 : fetch_word Asan.M.loaded_segments (0x9c260 : word) = Some W_9c210.
Proof. vm_refl. Qed.
Lemma D_9c210 : decode_any W_9c210 = Some (Store SZ8 2 1 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_9c214 : bv 32 := 0x00813823.
Lemma F_9c214 : fetch_word Asan.M.loaded_segments (0x9c264 : word) = Some W_9c214.
Proof. vm_refl. Qed.
Lemma D_9c214 : decode_any W_9c214 = Some (Store SZ8 2 8 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_9c218 : bv 32 := 0x00913423.
Lemma F_9c218 : fetch_word Asan.M.loaded_segments (0x9c268 : word) = Some W_9c218.
Proof. vm_refl. Qed.
Lemma D_9c218 : decode_any W_9c218 = Some (Store SZ8 2 9 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_9c21c : bv 32 := 0x01213023.
Lemma F_9c21c : fetch_word Asan.M.loaded_segments (0x9c26c : word) = Some W_9c21c.
Proof. vm_refl. Qed.
Lemma D_9c21c : decode_any W_9c21c = Some (Store SZ8 2 18 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_9c220 : bv 32 := 0x00058413.
Lemma F_9c220 : fetch_word Asan.M.loaded_segments (0x9c270 : word) = Some W_9c220.
Proof. vm_refl. Qed.
Lemma D_9c220 : decode_any W_9c220 = Some (OpImm ALU_ADD 8 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_9c224 : bv 32 := 0x000b7597.
Lemma F_9c224 : fetch_word Asan.M.loaded_segments (0x9c274 : word) = Some W_9c224.
Proof. vm_refl. Qed.
Lemma D_9c224 : decode_any W_9c224 = Some (Auipc 11 183, 4%Z).
Proof. vm_refl. Qed.

Definition W_9c228 : bv 32 := 0xea45b903.
Lemma F_9c228 : fetch_word Asan.M.loaded_segments (0x9c278 : word) = Some W_9c228.
Proof. vm_refl. Qed.
Lemma D_9c228 : decode_any W_9c228 = Some (Load SZ8 true 18 11 3748, 4%Z).
Proof. vm_refl. Qed.

Definition W_9c22c : bv 32 := 0x00093583.
Lemma F_9c22c : fetch_word Asan.M.loaded_segments (0x9c27c : word) = Some W_9c22c.
Proof. vm_refl. Qed.
Lemma D_9c22c : decode_any W_9c22c = Some (Load SZ8 true 11 18 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_9c230 : bv 32 := 0x00050493.
Lemma F_9c230 : fetch_word Asan.M.loaded_segments (0x9c280 : word) = Some W_9c230.
Proof. vm_refl. Qed.
Lemma D_9c230 : decode_any W_9c230 = Some (OpImm ALU_ADD 9 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_9c234 : bv 32 := 0x00059863.
Lemma F_9c234 : fetch_word Asan.M.loaded_segments (0x9c284 : word) = Some W_9c234.
Proof. vm_refl. Qed.
Lemma D_9c234 : decode_any W_9c234 = Some (Branch BC_NE 11 0 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_9c244 : bv 32 := 0xfff58513.
Lemma F_9c244 : fetch_word Asan.M.loaded_segments (0x9c294 : word) = Some W_9c244.
Proof. vm_refl. Qed.
Lemma D_9c244 : decode_any W_9c244 = Some (OpImm ALU_ADD 10 11 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_9c248 : bv 32 := 0x00a5f533.
Lemma F_9c248 : fetch_word Asan.M.loaded_segments (0x9c298 : word) = Some W_9c248.
Proof. vm_refl. Qed.
Lemma D_9c248 : decode_any W_9c248 = Some (Op ALU_AND 10 11 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_9c24c : bv 32 := 0x04051a63.
Lemma F_9c24c : fetch_word Asan.M.loaded_segments (0x9c29c : word) = Some W_9c24c.
Proof. vm_refl. Qed.
Lemma D_9c24c : decode_any W_9c24c = Some (Branch BC_NE 10 0 84, 4%Z).
Proof. vm_refl. Qed.

Definition W_9c250 : bv 32 := 0x00b484b3.
Lemma F_9c250 : fetch_word Asan.M.loaded_segments (0x9c2a0 : word) = Some W_9c250.
Proof. vm_refl. Qed.
Lemma D_9c250 : decode_any W_9c250 = Some (Op ALU_ADD 9 9 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_9c254 : bv 32 := 0x40b005b3.
Lemma F_9c254 : fetch_word Asan.M.loaded_segments (0x9c2a4 : word) = Some W_9c254.
Proof. vm_refl. Qed.
Lemma D_9c254 : decode_any W_9c254 = Some (Op ALU_SUB 11 0 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_9c258 : bv 32 := 0xfff48513.
Lemma F_9c258 : fetch_word Asan.M.loaded_segments (0x9c2a8 : word) = Some W_9c258.
Proof. vm_refl. Qed.
Lemma D_9c258 : decode_any W_9c258 = Some (OpImm ALU_ADD 10 9 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_9c25c : bv 32 := 0x00b57533.
Lemma F_9c25c : fetch_word Asan.M.loaded_segments (0x9c2ac : word) = Some W_9c25c.
Proof. vm_refl. Qed.
Lemma D_9c25c : decode_any W_9c25c = Some (Op ALU_AND 10 10 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_9c260 : bv 32 := 0x00b475b3.
Lemma F_9c260 : fetch_word Asan.M.loaded_segments (0x9c2b0 : word) = Some W_9c260.
Proof. vm_refl. Qed.
Lemma D_9c260 : decode_any W_9c260 = Some (Op ALU_AND 11 8 11, 4%Z).
Proof. vm_refl. Qed.

Definition W_9c264 : bv 32 := 0x02b57263.
Lemma F_9c264 : fetch_word Asan.M.loaded_segments (0x9c2b4 : word) = Some W_9c264.
Proof. vm_refl. Qed.
Lemma D_9c264 : decode_any W_9c264 = Some (Branch BC_GEU 10 11 36, 4%Z).
Proof. vm_refl. Qed.

Definition W_9c268 : bv 32 := 0x40a585b3.
Lemma F_9c268 : fetch_word Asan.M.loaded_segments (0x9c2b8 : word) = Some W_9c268.
Proof. vm_refl. Qed.
Lemma D_9c268 : decode_any W_9c268 = Some (Op ALU_SUB 11 11 10, 4%Z).
Proof. vm_refl. Qed.

Definition W_9c26c : bv 32 := 0x00400613.
Lemma F_9c26c : fetch_word Asan.M.loaded_segments (0x9c2bc : word) = Some W_9c26c.
Proof. vm_refl. Qed.
Lemma D_9c26c : decode_any W_9c26c = Some (OpImm ALU_ADD 12 0 4, 4%Z).
Proof. vm_refl. Qed.

Definition W_9c270 : bv 32 := 0x01813083.
Lemma F_9c270 : fetch_word Asan.M.loaded_segments (0x9c2c0 : word) = Some W_9c270.
Proof. vm_refl. Qed.
Lemma D_9c270 : decode_any W_9c270 = Some (Load SZ8 true 1 2 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_9c274 : bv 32 := 0x01013403.
Lemma F_9c274 : fetch_word Asan.M.loaded_segments (0x9c2c4 : word) = Some W_9c274.
Proof. vm_refl. Qed.
Lemma D_9c274 : decode_any W_9c274 = Some (Load SZ8 true 8 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_9c278 : bv 32 := 0x00813483.
Lemma F_9c278 : fetch_word Asan.M.loaded_segments (0x9c2c8 : word) = Some W_9c278.
Proof. vm_refl. Qed.
Lemma D_9c278 : decode_any W_9c278 = Some (Load SZ8 true 9 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_9c27c : bv 32 := 0x00013903.
Lemma F_9c27c : fetch_word Asan.M.loaded_segments (0x9c2cc : word) = Some W_9c27c.
Proof. vm_refl. Qed.
Lemma D_9c27c : decode_any W_9c27c = Some (Load SZ8 true 18 2 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_9c280 : bv 32 := 0x02010113.
Lemma F_9c280 : fetch_word Asan.M.loaded_segments (0x9c2d0 : word) = Some W_9c280.
Proof. vm_refl. Qed.
Lemma D_9c280 : decode_any W_9c280 = Some (OpImm ALU_ADD 2 2 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_9c284 : bv 32 := 0xbb1f606f.
Lemma F_9c284 : fetch_word Asan.M.loaded_segments (0x9c2d4 : word) = Some W_9c284.
Proof. vm_refl. Qed.
Lemma D_9c284 : decode_any W_9c284 = Some (Jal 0 2059184, 4%Z).
Proof. vm_refl. Qed.

Definition W_9c288 : bv 32 := 0x01813083.
Lemma F_9c288 : fetch_word Asan.M.loaded_segments (0x9c2d8 : word) = Some W_9c288.
Proof. vm_refl. Qed.
Lemma D_9c288 : decode_any W_9c288 = Some (Load SZ8 true 1 2 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_9c28c : bv 32 := 0x01013403.
Lemma F_9c28c : fetch_word Asan.M.loaded_segments (0x9c2dc : word) = Some W_9c28c.
Proof. vm_refl. Qed.
Lemma D_9c28c : decode_any W_9c28c = Some (Load SZ8 true 8 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_9c290 : bv 32 := 0x00813483.
Lemma F_9c290 : fetch_word Asan.M.loaded_segments (0x9c2e0 : word) = Some W_9c290.
Proof. vm_refl. Qed.
Lemma D_9c290 : decode_any W_9c290 = Some (Load SZ8 true 9 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_9c294 : bv 32 := 0x00013903.
Lemma F_9c294 : fetch_word Asan.M.loaded_segments (0x9c2e4 : word) = Some W_9c294.
Proof. vm_refl. Qed.
Lemma D_9c294 : decode_any W_9c294 = Some (Load SZ8 true 18 2 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_9c298 : bv 32 := 0x02010113.
Lemma F_9c298 : fetch_word Asan.M.loaded_segments (0x9c2e8 : word) = Some W_9c298.
Proof. vm_refl. Qed.
Lemma D_9c298 : decode_any W_9c298 = Some (OpImm ALU_ADD 2 2 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_9c29c : bv 32 := 0x00008067.
Lemma F_9c29c : fetch_word Asan.M.loaded_segments (0x9c2ec : word) = Some W_9c29c.
Proof. vm_refl. Qed.
Lemma D_9c29c : decode_any W_9c29c = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_9cd5c : bv 32 := 0xfe010113.
Lemma F_9cd5c : fetch_word Asan.M.loaded_segments (0x9cdac : word) = Some W_9cd5c.
Proof. vm_refl. Qed.
Lemma D_9cd5c : decode_any W_9cd5c = Some (OpImm ALU_ADD 2 2 4064, 4%Z).
Proof. vm_refl. Qed.

Definition W_9cd60 : bv 32 := 0x00113c23.
Lemma F_9cd60 : fetch_word Asan.M.loaded_segments (0x9cdb0 : word) = Some W_9cd60.
Proof. vm_refl. Qed.
Lemma D_9cd60 : decode_any W_9cd60 = Some (Store SZ8 2 1 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_9cd64 : bv 32 := 0x00813823.
Lemma F_9cd64 : fetch_word Asan.M.loaded_segments (0x9cdb4 : word) = Some W_9cd64.
Proof. vm_refl. Qed.
Lemma D_9cd64 : decode_any W_9cd64 = Some (Store SZ8 2 8 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_9cd68 : bv 32 := 0x00913423.
Lemma F_9cd68 : fetch_word Asan.M.loaded_segments (0x9cdb8 : word) = Some W_9cd68.
Proof. vm_refl. Qed.
Lemma D_9cd68 : decode_any W_9cd68 = Some (Store SZ8 2 9 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_9cd6c : bv 32 := 0x01213023.
Lemma F_9cd6c : fetch_word Asan.M.loaded_segments (0x9cdbc : word) = Some W_9cd6c.
Proof. vm_refl. Qed.
Lemma D_9cd6c : decode_any W_9cd6c = Some (Store SZ8 2 18 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_9cd70 : bv 32 := 0x00060413.
Lemma F_9cd70 : fetch_word Asan.M.loaded_segments (0x9cdc0 : word) = Some W_9cd70.
Proof. vm_refl. Qed.
Lemma D_9cd70 : decode_any W_9cd70 = Some (OpImm ALU_ADD 8 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_9cd74 : bv 32 := 0x00058493.
Lemma F_9cd74 : fetch_word Asan.M.loaded_segments (0x9cdc4 : word) = Some W_9cd74.
Proof. vm_refl. Qed.
Lemma D_9cd74 : decode_any W_9cd74 = Some (OpImm ALU_ADD 9 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_9cd78 : bv 32 := 0x00058513.
Lemma F_9cd78 : fetch_word Asan.M.loaded_segments (0x9cdc8 : word) = Some W_9cd78.
Proof. vm_refl. Qed.
Lemma D_9cd78 : decode_any W_9cd78 = Some (OpImm ALU_ADD 10 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_9cd7c : bv 32 := 0x00060593.
Lemma F_9cd7c : fetch_word Asan.M.loaded_segments (0x9cdcc : word) = Some W_9cd7c.
Proof. vm_refl. Qed.
Lemma D_9cd7c : decode_any W_9cd7c = Some (OpImm ALU_ADD 11 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_9cd80 : bv 32 := 0x00068613.
Lemma F_9cd80 : fetch_word Asan.M.loaded_segments (0x9cdd0 : word) = Some W_9cd80.
Proof. vm_refl. Qed.
Lemma D_9cd80 : decode_any W_9cd80 = Some (OpImm ALU_ADD 12 13 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_9cd84 : bv 32 := 0xf19f70ef.
Lemma F_9cd84 : fetch_word Asan.M.loaded_segments (0x9cdd4 : word) = Some W_9cd84.
Proof. vm_refl. Qed.
Lemma D_9cd84 : decode_any W_9cd84 = Some (Jal 1 2064152, 4%Z).
Proof. vm_refl. Qed.

Definition W_9cd88 : bv 32 := 0x00050e63.
Lemma F_9cd88 : fetch_word Asan.M.loaded_segments (0x9cdd8 : word) = Some W_9cd88.
Proof. vm_refl. Qed.
Lemma D_9cd88 : decode_any W_9cd88 = Some (Branch BC_EQ 10 0 28, 4%Z).
Proof. vm_refl. Qed.

Definition W_9cd8c : bv 32 := 0x01813083.
Lemma F_9cd8c : fetch_word Asan.M.loaded_segments (0x9cddc : word) = Some W_9cd8c.
Proof. vm_refl. Qed.
Lemma D_9cd8c : decode_any W_9cd8c = Some (Load SZ8 true 1 2 24, 4%Z).
Proof. vm_refl. Qed.

Definition W_9cd90 : bv 32 := 0x01013403.
Lemma F_9cd90 : fetch_word Asan.M.loaded_segments (0x9cde0 : word) = Some W_9cd90.
Proof. vm_refl. Qed.
Lemma D_9cd90 : decode_any W_9cd90 = Some (Load SZ8 true 8 2 16, 4%Z).
Proof. vm_refl. Qed.

Definition W_9cd94 : bv 32 := 0x00813483.
Lemma F_9cd94 : fetch_word Asan.M.loaded_segments (0x9cde4 : word) = Some W_9cd94.
Proof. vm_refl. Qed.
Lemma D_9cd94 : decode_any W_9cd94 = Some (Load SZ8 true 9 2 8, 4%Z).
Proof. vm_refl. Qed.

Definition W_9cd98 : bv 32 := 0x00013903.
Lemma F_9cd98 : fetch_word Asan.M.loaded_segments (0x9cde8 : word) = Some W_9cd98.
Proof. vm_refl. Qed.
Lemma D_9cd98 : decode_any W_9cd98 = Some (Load SZ8 true 18 2 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_9cd9c : bv 32 := 0x02010113.
Lemma F_9cd9c : fetch_word Asan.M.loaded_segments (0x9cdec : word) = Some W_9cd9c.
Proof. vm_refl. Qed.
Lemma D_9cd9c : decode_any W_9cd9c = Some (OpImm ALU_ADD 2 2 32, 4%Z).
Proof. vm_refl. Qed.

Definition W_9cda0 : bv 32 := 0x00008067.
Lemma F_9cda0 : fetch_word Asan.M.loaded_segments (0x9cdf0 : word) = Some W_9cda0.
Proof. vm_refl. Qed.
Lemma D_9cda0 : decode_any W_9cda0 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_9cea8 : bv 32 := 0x00058513.
Lemma F_9cea8 : fetch_word Asan.M.loaded_segments (0x9cef8 : word) = Some W_9cea8.
Proof. vm_refl. Qed.
Lemma D_9cea8 : decode_any W_9cea8 = Some (OpImm ALU_ADD 10 11 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_9ceac : bv 32 := 0x00060593.
Lemma F_9ceac : fetch_word Asan.M.loaded_segments (0x9cefc : word) = Some W_9ceac.
Proof. vm_refl. Qed.
Lemma D_9ceac : decode_any W_9ceac = Some (OpImm ALU_ADD 11 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_9ceb0 : bv 32 := 0x00068613.
Lemma F_9ceb0 : fetch_word Asan.M.loaded_segments (0x9cf00 : word) = Some W_9ceb0.
Proof. vm_refl. Qed.
Lemma D_9ceb0 : decode_any W_9ceb0 = Some (OpImm ALU_ADD 12 13 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_9ceb4 : bv 32 := 0xc65f706f.
Lemma F_9ceb4 : fetch_word Asan.M.loaded_segments (0x9cf04 : word) = Some W_9ceb4.
Proof. vm_refl. Qed.
Lemma D_9ceb4 : decode_any W_9ceb4 = Some (Jal 0 2063460, 4%Z).
Proof. vm_refl. Qed.

