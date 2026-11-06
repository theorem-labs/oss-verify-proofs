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

Definition W_951b8 : bv 32 := 0xef010113.
Lemma F_951b8 : fetch_word Asan.M.loaded_segments (0x95208 : word) = Some W_951b8.
Proof. vm_refl. Qed.
Lemma D_951b8 : decode_any W_951b8 = Some (OpImm ALU_ADD 2 2 3824, 4%Z).
Proof. vm_refl. Qed.

Definition W_951bc : bv 32 := 0x10113423.
Lemma F_951bc : fetch_word Asan.M.loaded_segments (0x9520c : word) = Some W_951bc.
Proof. vm_refl. Qed.
Lemma D_951bc : decode_any W_951bc = Some (Store SZ8 2 1 264, 4%Z).
Proof. vm_refl. Qed.

Definition W_951c0 : bv 32 := 0x10813023.
Lemma F_951c0 : fetch_word Asan.M.loaded_segments (0x95210 : word) = Some W_951c0.
Proof. vm_refl. Qed.
Lemma D_951c0 : decode_any W_951c0 = Some (Store SZ8 2 8 256, 4%Z).
Proof. vm_refl. Qed.

Definition W_951c4 : bv 32 := 0x0e913c23.
Lemma F_951c4 : fetch_word Asan.M.loaded_segments (0x95214 : word) = Some W_951c4.
Proof. vm_refl. Qed.
Lemma D_951c4 : decode_any W_951c4 = Some (Store SZ8 2 9 248, 4%Z).
Proof. vm_refl. Qed.

Definition W_951c8 : bv 32 := 0x0f213823.
Lemma F_951c8 : fetch_word Asan.M.loaded_segments (0x95218 : word) = Some W_951c8.
Proof. vm_refl. Qed.
Lemma D_951c8 : decode_any W_951c8 = Some (Store SZ8 2 18 240, 4%Z).
Proof. vm_refl. Qed.

Definition W_951cc : bv 32 := 0x0f313423.
Lemma F_951cc : fetch_word Asan.M.loaded_segments (0x9521c : word) = Some W_951cc.
Proof. vm_refl. Qed.
Lemma D_951cc : decode_any W_951cc = Some (Store SZ8 2 19 232, 4%Z).
Proof. vm_refl. Qed.

Definition W_951d0 : bv 32 := 0x0f413023.
Lemma F_951d0 : fetch_word Asan.M.loaded_segments (0x95220 : word) = Some W_951d0.
Proof. vm_refl. Qed.
Lemma D_951d0 : decode_any W_951d0 = Some (Store SZ8 2 20 224, 4%Z).
Proof. vm_refl. Qed.

Definition W_951d4 : bv 32 := 0x0d513c23.
Lemma F_951d4 : fetch_word Asan.M.loaded_segments (0x95224 : word) = Some W_951d4.
Proof. vm_refl. Qed.
Lemma D_951d4 : decode_any W_951d4 = Some (Store SZ8 2 21 216, 4%Z).
Proof. vm_refl. Qed.

Definition W_951d8 : bv 32 := 0x00050913.
Lemma F_951d8 : fetch_word Asan.M.loaded_segments (0x95228 : word) = Some W_951d8.
Proof. vm_refl. Qed.
Lemma D_951d8 : decode_any W_951d8 = Some (OpImm ALU_ADD 18 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_951dc : bv 32 := 0xfff00513.
Lemma F_951dc : fetch_word Asan.M.loaded_segments (0x9522c : word) = Some W_951dc.
Proof. vm_refl. Qed.
Lemma D_951dc : decode_any W_951dc = Some (OpImm ALU_ADD 10 0 4095, 4%Z).
Proof. vm_refl. Qed.

Definition W_951e0 : bv 32 := 0x12090463.
Lemma F_951e0 : fetch_word Asan.M.loaded_segments (0x95230 : word) = Some W_951e0.
Proof. vm_refl. Qed.
Lemma D_951e0 : decode_any W_951e0 = Some (Branch BC_EQ 18 0 296, 4%Z).
Proof. vm_refl. Qed.

Definition W_951e4 : bv 32 := 0x00060413.
Lemma F_951e4 : fetch_word Asan.M.loaded_segments (0x95234 : word) = Some W_951e4.
Proof. vm_refl. Qed.
Lemma D_951e4 : decode_any W_951e4 = Some (OpImm ALU_ADD 8 12 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_951e8 : bv 32 := 0x000be617.
Lemma F_951e8 : fetch_word Asan.M.loaded_segments (0x95238 : word) = Some W_951e8.
Proof. vm_refl. Qed.
Lemma D_951e8 : decode_any W_951e8 = Some (Auipc 12 190, 4%Z).
Proof. vm_refl. Qed.

Definition W_951ec : bv 32 := 0xef063603.
Lemma F_951ec : fetch_word Asan.M.loaded_segments (0x9523c : word) = Some W_951ec.
Proof. vm_refl. Qed.
Lemma D_951ec : decode_any W_951ec = Some (Load SZ8 true 12 12 3824, 4%Z).
Proof. vm_refl. Qed.

Definition W_951f0 : bv 32 := 0x10464603.
Lemma F_951f0 : fetch_word Asan.M.loaded_segments (0x95240 : word) = Some W_951f0.
Proof. vm_refl. Qed.
Lemma D_951f0 : decode_any W_951f0 = Some (Load SZ1 false 12 12 260, 4%Z).
Proof. vm_refl. Qed.

Definition W_951f4 : bv 32 := 0x00167613.
Lemma F_951f4 : fetch_word Asan.M.loaded_segments (0x95244 : word) = Some W_951f4.
Proof. vm_refl. Qed.
Lemma D_951f4 : decode_any W_951f4 = Some (OpImm ALU_AND 12 12 1, 4%Z).
Proof. vm_refl. Qed.

Definition W_951f8 : bv 32 := 0x10060863.
Lemma F_951f8 : fetch_word Asan.M.loaded_segments (0x95248 : word) = Some W_951f8.
Proof. vm_refl. Qed.
Lemma D_951f8 : decode_any W_951f8 = Some (Branch BC_EQ 12 0 272, 4%Z).
Proof. vm_refl. Qed.

Definition W_95308 : bv 32 := 0x0005051b.
Lemma F_95308 : fetch_word Asan.M.loaded_segments (0x95358 : word) = Some W_95308.
Proof. vm_refl. Qed.
Lemma D_95308 : decode_any W_95308 = Some (OpImm32 10 10 0, 4%Z).
Proof. vm_refl. Qed.

Definition W_9530c : bv 32 := 0x10813083.
Lemma F_9530c : fetch_word Asan.M.loaded_segments (0x9535c : word) = Some W_9530c.
Proof. vm_refl. Qed.
Lemma D_9530c : decode_any W_9530c = Some (Load SZ8 true 1 2 264, 4%Z).
Proof. vm_refl. Qed.

Definition W_95310 : bv 32 := 0x10013403.
Lemma F_95310 : fetch_word Asan.M.loaded_segments (0x95360 : word) = Some W_95310.
Proof. vm_refl. Qed.
Lemma D_95310 : decode_any W_95310 = Some (Load SZ8 true 8 2 256, 4%Z).
Proof. vm_refl. Qed.

Definition W_95314 : bv 32 := 0x0f813483.
Lemma F_95314 : fetch_word Asan.M.loaded_segments (0x95364 : word) = Some W_95314.
Proof. vm_refl. Qed.
Lemma D_95314 : decode_any W_95314 = Some (Load SZ8 true 9 2 248, 4%Z).
Proof. vm_refl. Qed.

Definition W_95318 : bv 32 := 0x0f013903.
Lemma F_95318 : fetch_word Asan.M.loaded_segments (0x95368 : word) = Some W_95318.
Proof. vm_refl. Qed.
Lemma D_95318 : decode_any W_95318 = Some (Load SZ8 true 18 2 240, 4%Z).
Proof. vm_refl. Qed.

Definition W_9531c : bv 32 := 0x0e813983.
Lemma F_9531c : fetch_word Asan.M.loaded_segments (0x9536c : word) = Some W_9531c.
Proof. vm_refl. Qed.
Lemma D_9531c : decode_any W_9531c = Some (Load SZ8 true 19 2 232, 4%Z).
Proof. vm_refl. Qed.

Definition W_95320 : bv 32 := 0x0e013a03.
Lemma F_95320 : fetch_word Asan.M.loaded_segments (0x95370 : word) = Some W_95320.
Proof. vm_refl. Qed.
Lemma D_95320 : decode_any W_95320 = Some (Load SZ8 true 20 2 224, 4%Z).
Proof. vm_refl. Qed.

Definition W_95324 : bv 32 := 0x0d813a83.
Lemma F_95324 : fetch_word Asan.M.loaded_segments (0x95374 : word) = Some W_95324.
Proof. vm_refl. Qed.
Lemma D_95324 : decode_any W_95324 = Some (Load SZ8 true 21 2 216, 4%Z).
Proof. vm_refl. Qed.

Definition W_95328 : bv 32 := 0x11010113.
Lemma F_95328 : fetch_word Asan.M.loaded_segments (0x95378 : word) = Some W_95328.
Proof. vm_refl. Qed.
Lemma D_95328 : decode_any W_95328 = Some (OpImm ALU_ADD 2 2 272, 4%Z).
Proof. vm_refl. Qed.

Definition W_9532c : bv 32 := 0x00008067.
Lemma F_9532c : fetch_word Asan.M.loaded_segments (0x9537c : word) = Some W_9532c.
Proof. vm_refl. Qed.
Lemma D_9532c : decode_any W_9532c = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

