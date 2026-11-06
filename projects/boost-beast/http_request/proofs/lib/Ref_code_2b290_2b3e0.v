(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.boost_beast.http_request.images Require Import Plain.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.

(* [comment removed for export] *)
Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

(* [comment removed for export] *)
Definition W_2b290 : bv 32 := 0x00066517.
Lemma F_2b290 : fetch_word Plain.M.loaded_segments (0x2b290 : word) = Some W_2b290.
Proof. vm_refl. Qed.
Lemma D_2b290 : decode_any W_2b290 = Some (Auipc 10 102, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2b294 : bv 32 := 0xa1850503.
Lemma F_2b294 : fetch_word Plain.M.loaded_segments (0x2b294 : word) = Some W_2b294.
Proof. vm_refl. Qed.
Lemma D_2b294 : decode_any W_2b294 = Some (Load SZ1 true 10 10 2584, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2b298 : bv 32 := 0x0230000f.
Lemma F_2b298 : fetch_word Plain.M.loaded_segments (0x2b298 : word) = Some W_2b298.
Proof. vm_refl. Qed.
Lemma D_2b298 : decode_any W_2b298 = Some (Fence 0 2 3 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2b29c : bv 32 := 0x00050463.
Lemma F_2b29c : fetch_word Plain.M.loaded_segments (0x2b29c : word) = Some W_2b29c.
Proof. vm_refl. Qed.
Lemma D_2b29c : decode_any W_2b29c = Some (Branch BC_EQ 10 0 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2b2a0 : bv 32 := 0x00008067.
Lemma F_2b2a0 : fetch_word Plain.M.loaded_segments (0x2b2a0 : word) = Some W_2b2a0.
Proof. vm_refl. Qed.
Lemma D_2b2a0 : decode_any W_2b2a0 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2b2a4 : bv 32 := 0xff010113.
Lemma F_2b2a4 : fetch_word Plain.M.loaded_segments (0x2b2a4 : word) = Some W_2b2a4.
Proof. vm_refl. Qed.
Lemma D_2b2a4 : decode_any W_2b2a4 = Some (OpImm ALU_ADD 2 2 4080, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2b2a8 : bv 32 := 0x00113423.
Lemma F_2b2a8 : fetch_word Plain.M.loaded_segments (0x2b2a8 : word) = Some W_2b2a8.
Proof. vm_refl. Qed.
Lemma D_2b2a8 : decode_any W_2b2a8 = Some (Store SZ8 2 1 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2b2ac : bv 32 := 0x00066517.
Lemma F_2b2ac : fetch_word Plain.M.loaded_segments (0x2b2ac : word) = Some W_2b2ac.
Proof. vm_refl. Qed.
Lemma D_2b2ac : decode_any W_2b2ac = Some (Auipc 10 102, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2b2b0 : bv 32 := 0x9fc50513.
Lemma F_2b2b0 : fetch_word Plain.M.loaded_segments (0x2b2b0 : word) = Some W_2b2b0.
Proof. vm_refl. Qed.
Lemma D_2b2b0 : decode_any W_2b2b0 = Some (OpImm ALU_ADD 10 10 2556, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2b2b4 : bv 32 := 0x3f4110ef.
Lemma F_2b2b4 : fetch_word Plain.M.loaded_segments (0x2b2b4 : word) = Some W_2b2b4.
Proof. vm_refl. Qed.
Lemma D_2b2b4 : decode_any W_2b2b4 = Some (Jal 1 70644, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2b2b8 : bv 32 := 0x0005051b.
Lemma F_2b2b8 : fetch_word Plain.M.loaded_segments (0x2b2b8 : word) = Some W_2b2b8.
Proof. vm_refl. Qed.
Lemma D_2b2b8 : decode_any W_2b2b8 = Some (OpImm32 10 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2b2bc : bv 32 := 0x00813083.
Lemma F_2b2bc : fetch_word Plain.M.loaded_segments (0x2b2bc : word) = Some W_2b2bc.
Proof. vm_refl. Qed.
Lemma D_2b2bc : decode_any W_2b2bc = Some (Load SZ8 true 1 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2b2c0 : bv 32 := 0x01010113.
Lemma F_2b2c0 : fetch_word Plain.M.loaded_segments (0x2b2c0 : word) = Some W_2b2c0.
Proof. vm_refl. Qed.
Lemma D_2b2c0 : decode_any W_2b2c0 = Some (OpImm ALU_ADD 2 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2b2c4 : bv 32 := 0xfc050ee3.
Lemma F_2b2c4 : fetch_word Plain.M.loaded_segments (0x2b2c4 : word) = Some W_2b2c4.
Proof. vm_refl. Qed.
Lemma D_2b2c4 : decode_any W_2b2c4 = Some (Branch BC_EQ 10 0 8156, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2b2c8 : bv 32 := 0x00066597.
Lemma F_2b2c8 : fetch_word Plain.M.loaded_segments (0x2b2c8 : word) = Some W_2b2c8.
Proof. vm_refl. Qed.
Lemma D_2b2c8 : decode_any W_2b2c8 = Some (Auipc 11 102, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2b2cc : bv 32 := 0x00055517.
Lemma F_2b2cc : fetch_word Plain.M.loaded_segments (0x2b2cc : word) = Some W_2b2cc.
Proof. vm_refl. Qed.
Lemma D_2b2cc : decode_any W_2b2cc = Some (Auipc 10 85, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2b2d0 : bv 32 := 0x00066617.
Lemma F_2b2d0 : fetch_word Plain.M.loaded_segments (0x2b2d0 : word) = Some W_2b2d0.
Proof. vm_refl. Qed.
Lemma D_2b2d0 : decode_any W_2b2d0 = Some (Auipc 12 102, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2b2d4 : bv 32 := 0x5a450693.
Lemma F_2b2d4 : fetch_word Plain.M.loaded_segments (0x2b2d4 : word) = Some W_2b2d4.
Proof. vm_refl. Qed.
Lemma D_2b2d4 : decode_any W_2b2d4 = Some (OpImm ALU_ADD 13 10 1444, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2b2d8 : bv 32 := 0x9d860513.
Lemma F_2b2d8 : fetch_word Plain.M.loaded_segments (0x2b2d8 : word) = Some W_2b2d8.
Proof. vm_refl. Qed.
Lemma D_2b2d8 : decode_any W_2b2d8 = Some (OpImm ALU_ADD 10 12 2520, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2b2dc : bv 32 := 0x9cd5bc23.
Lemma F_2b2dc : fetch_word Plain.M.loaded_segments (0x2b2dc : word) = Some W_2b2dc.
Proof. vm_refl. Qed.
Lemma D_2b2dc : decode_any W_2b2dc = Some (Store SZ8 11 13 2520, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2b2e0 : bv 32 := 0x4181106f.
Lemma F_2b2e0 : fetch_word Plain.M.loaded_segments (0x2b2e0 : word) = Some W_2b2e0.
Proof. vm_refl. Qed.
Lemma D_2b2e0 : decode_any W_2b2e0 = Some (Jal 0 70680, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2b2e4 : bv 32 := 0x00066517.
Lemma F_2b2e4 : fetch_word Plain.M.loaded_segments (0x2b2e4 : word) = Some W_2b2e4.
Proof. vm_refl. Qed.
Lemma D_2b2e4 : decode_any W_2b2e4 = Some (Auipc 10 102, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2b2e8 : bv 32 := 0x9d450503.
Lemma F_2b2e8 : fetch_word Plain.M.loaded_segments (0x2b2e8 : word) = Some W_2b2e8.
Proof. vm_refl. Qed.
Lemma D_2b2e8 : decode_any W_2b2e8 = Some (Load SZ1 true 10 10 2516, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2b2ec : bv 32 := 0x0230000f.
Lemma F_2b2ec : fetch_word Plain.M.loaded_segments (0x2b2ec : word) = Some W_2b2ec.
Proof. vm_refl. Qed.
Lemma D_2b2ec : decode_any W_2b2ec = Some (Fence 0 2 3 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2b2f0 : bv 32 := 0x00050463.
Lemma F_2b2f0 : fetch_word Plain.M.loaded_segments (0x2b2f0 : word) = Some W_2b2f0.
Proof. vm_refl. Qed.
Lemma D_2b2f0 : decode_any W_2b2f0 = Some (Branch BC_EQ 10 0 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2b2f4 : bv 32 := 0x00008067.
Lemma F_2b2f4 : fetch_word Plain.M.loaded_segments (0x2b2f4 : word) = Some W_2b2f4.
Proof. vm_refl. Qed.
Lemma D_2b2f4 : decode_any W_2b2f4 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2b2f8 : bv 32 := 0xff010113.
Lemma F_2b2f8 : fetch_word Plain.M.loaded_segments (0x2b2f8 : word) = Some W_2b2f8.
Proof. vm_refl. Qed.
Lemma D_2b2f8 : decode_any W_2b2f8 = Some (OpImm ALU_ADD 2 2 4080, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2b2fc : bv 32 := 0x00113423.
Lemma F_2b2fc : fetch_word Plain.M.loaded_segments (0x2b2fc : word) = Some W_2b2fc.
Proof. vm_refl. Qed.
Lemma D_2b2fc : decode_any W_2b2fc = Some (Store SZ8 2 1 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2b300 : bv 32 := 0x00066517.
Lemma F_2b300 : fetch_word Plain.M.loaded_segments (0x2b300 : word) = Some W_2b300.
Proof. vm_refl. Qed.
Lemma D_2b300 : decode_any W_2b300 = Some (Auipc 10 102, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2b304 : bv 32 := 0x9b850513.
Lemma F_2b304 : fetch_word Plain.M.loaded_segments (0x2b304 : word) = Some W_2b304.
Proof. vm_refl. Qed.
Lemma D_2b304 : decode_any W_2b304 = Some (OpImm ALU_ADD 10 10 2488, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2b308 : bv 32 := 0x3a0110ef.
Lemma F_2b308 : fetch_word Plain.M.loaded_segments (0x2b308 : word) = Some W_2b308.
Proof. vm_refl. Qed.
Lemma D_2b308 : decode_any W_2b308 = Some (Jal 1 70560, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2b30c : bv 32 := 0x0005051b.
Lemma F_2b30c : fetch_word Plain.M.loaded_segments (0x2b30c : word) = Some W_2b30c.
Proof. vm_refl. Qed.
Lemma D_2b30c : decode_any W_2b30c = Some (OpImm32 10 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2b310 : bv 32 := 0x00813083.
Lemma F_2b310 : fetch_word Plain.M.loaded_segments (0x2b310 : word) = Some W_2b310.
Proof. vm_refl. Qed.
Lemma D_2b310 : decode_any W_2b310 = Some (Load SZ8 true 1 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2b314 : bv 32 := 0x01010113.
Lemma F_2b314 : fetch_word Plain.M.loaded_segments (0x2b314 : word) = Some W_2b314.
Proof. vm_refl. Qed.
Lemma D_2b314 : decode_any W_2b314 = Some (OpImm ALU_ADD 2 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2b318 : bv 32 := 0xfc050ee3.
Lemma F_2b318 : fetch_word Plain.M.loaded_segments (0x2b318 : word) = Some W_2b318.
Proof. vm_refl. Qed.
Lemma D_2b318 : decode_any W_2b318 = Some (Branch BC_EQ 10 0 8156, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2b31c : bv 32 := 0x00066597.
Lemma F_2b31c : fetch_word Plain.M.loaded_segments (0x2b31c : word) = Some W_2b31c.
Proof. vm_refl. Qed.
Lemma D_2b31c : decode_any W_2b31c = Some (Auipc 11 102, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2b320 : bv 32 := 0x00055517.
Lemma F_2b320 : fetch_word Plain.M.loaded_segments (0x2b320 : word) = Some W_2b320.
Proof. vm_refl. Qed.
Lemma D_2b320 : decode_any W_2b320 = Some (Auipc 10 85, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2b324 : bv 32 := 0x00066617.
Lemma F_2b324 : fetch_word Plain.M.loaded_segments (0x2b324 : word) = Some W_2b324.
Proof. vm_refl. Qed.
Lemma D_2b324 : decode_any W_2b324 = Some (Auipc 12 102, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2b328 : bv 32 := 0x58850693.
Lemma F_2b328 : fetch_word Plain.M.loaded_segments (0x2b328 : word) = Some W_2b328.
Proof. vm_refl. Qed.
Lemma D_2b328 : decode_any W_2b328 = Some (OpImm ALU_ADD 13 10 1416, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2b32c : bv 32 := 0x99460513.
Lemma F_2b32c : fetch_word Plain.M.loaded_segments (0x2b32c : word) = Some W_2b32c.
Proof. vm_refl. Qed.
Lemma D_2b32c : decode_any W_2b32c = Some (OpImm ALU_ADD 10 12 2452, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2b330 : bv 32 := 0x98d5ba23.
Lemma F_2b330 : fetch_word Plain.M.loaded_segments (0x2b330 : word) = Some W_2b330.
Proof. vm_refl. Qed.
Lemma D_2b330 : decode_any W_2b330 = Some (Store SZ8 11 13 2452, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2b334 : bv 32 := 0x3c41106f.
Lemma F_2b334 : fetch_word Plain.M.loaded_segments (0x2b334 : word) = Some W_2b334.
Proof. vm_refl. Qed.
Lemma D_2b334 : decode_any W_2b334 = Some (Jal 0 70596, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2b338 : bv 32 := 0x00066517.
Lemma F_2b338 : fetch_word Plain.M.loaded_segments (0x2b338 : word) = Some W_2b338.
Proof. vm_refl. Qed.
Lemma D_2b338 : decode_any W_2b338 = Some (Auipc 10 102, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2b33c : bv 32 := 0x99050503.
Lemma F_2b33c : fetch_word Plain.M.loaded_segments (0x2b33c : word) = Some W_2b33c.
Proof. vm_refl. Qed.
Lemma D_2b33c : decode_any W_2b33c = Some (Load SZ1 true 10 10 2448, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2b340 : bv 32 := 0x0230000f.
Lemma F_2b340 : fetch_word Plain.M.loaded_segments (0x2b340 : word) = Some W_2b340.
Proof. vm_refl. Qed.
Lemma D_2b340 : decode_any W_2b340 = Some (Fence 0 2 3 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2b344 : bv 32 := 0x00050463.
Lemma F_2b344 : fetch_word Plain.M.loaded_segments (0x2b344 : word) = Some W_2b344.
Proof. vm_refl. Qed.
Lemma D_2b344 : decode_any W_2b344 = Some (Branch BC_EQ 10 0 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2b348 : bv 32 := 0x00008067.
Lemma F_2b348 : fetch_word Plain.M.loaded_segments (0x2b348 : word) = Some W_2b348.
Proof. vm_refl. Qed.
Lemma D_2b348 : decode_any W_2b348 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2b34c : bv 32 := 0xff010113.
Lemma F_2b34c : fetch_word Plain.M.loaded_segments (0x2b34c : word) = Some W_2b34c.
Proof. vm_refl. Qed.
Lemma D_2b34c : decode_any W_2b34c = Some (OpImm ALU_ADD 2 2 4080, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2b350 : bv 32 := 0x00113423.
Lemma F_2b350 : fetch_word Plain.M.loaded_segments (0x2b350 : word) = Some W_2b350.
Proof. vm_refl. Qed.
Lemma D_2b350 : decode_any W_2b350 = Some (Store SZ8 2 1 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2b354 : bv 32 := 0x00066517.
Lemma F_2b354 : fetch_word Plain.M.loaded_segments (0x2b354 : word) = Some W_2b354.
Proof. vm_refl. Qed.
Lemma D_2b354 : decode_any W_2b354 = Some (Auipc 10 102, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2b358 : bv 32 := 0x97450513.
Lemma F_2b358 : fetch_word Plain.M.loaded_segments (0x2b358 : word) = Some W_2b358.
Proof. vm_refl. Qed.
Lemma D_2b358 : decode_any W_2b358 = Some (OpImm ALU_ADD 10 10 2420, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2b35c : bv 32 := 0x34c110ef.
Lemma F_2b35c : fetch_word Plain.M.loaded_segments (0x2b35c : word) = Some W_2b35c.
Proof. vm_refl. Qed.
Lemma D_2b35c : decode_any W_2b35c = Some (Jal 1 70476, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2b360 : bv 32 := 0x0005051b.
Lemma F_2b360 : fetch_word Plain.M.loaded_segments (0x2b360 : word) = Some W_2b360.
Proof. vm_refl. Qed.
Lemma D_2b360 : decode_any W_2b360 = Some (OpImm32 10 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2b364 : bv 32 := 0x00813083.
Lemma F_2b364 : fetch_word Plain.M.loaded_segments (0x2b364 : word) = Some W_2b364.
Proof. vm_refl. Qed.
Lemma D_2b364 : decode_any W_2b364 = Some (Load SZ8 true 1 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2b368 : bv 32 := 0x01010113.
Lemma F_2b368 : fetch_word Plain.M.loaded_segments (0x2b368 : word) = Some W_2b368.
Proof. vm_refl. Qed.
Lemma D_2b368 : decode_any W_2b368 = Some (OpImm ALU_ADD 2 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2b36c : bv 32 := 0xfc050ee3.
Lemma F_2b36c : fetch_word Plain.M.loaded_segments (0x2b36c : word) = Some W_2b36c.
Proof. vm_refl. Qed.
Lemma D_2b36c : decode_any W_2b36c = Some (Branch BC_EQ 10 0 8156, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2b370 : bv 32 := 0x00066597.
Lemma F_2b370 : fetch_word Plain.M.loaded_segments (0x2b370 : word) = Some W_2b370.
Proof. vm_refl. Qed.
Lemma D_2b370 : decode_any W_2b370 = Some (Auipc 11 102, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2b374 : bv 32 := 0x00055517.
Lemma F_2b374 : fetch_word Plain.M.loaded_segments (0x2b374 : word) = Some W_2b374.
Proof. vm_refl. Qed.
Lemma D_2b374 : decode_any W_2b374 = Some (Auipc 10 85, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2b378 : bv 32 := 0x00066617.
Lemma F_2b378 : fetch_word Plain.M.loaded_segments (0x2b378 : word) = Some W_2b378.
Proof. vm_refl. Qed.
Lemma D_2b378 : decode_any W_2b378 = Some (Auipc 12 102, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2b37c : bv 32 := 0x56c50693.
Lemma F_2b37c : fetch_word Plain.M.loaded_segments (0x2b37c : word) = Some W_2b37c.
Proof. vm_refl. Qed.
Lemma D_2b37c : decode_any W_2b37c = Some (OpImm ALU_ADD 13 10 1388, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2b380 : bv 32 := 0x95060513.
Lemma F_2b380 : fetch_word Plain.M.loaded_segments (0x2b380 : word) = Some W_2b380.
Proof. vm_refl. Qed.
Lemma D_2b380 : decode_any W_2b380 = Some (OpImm ALU_ADD 10 12 2384, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2b384 : bv 32 := 0x94d5b823.
Lemma F_2b384 : fetch_word Plain.M.loaded_segments (0x2b384 : word) = Some W_2b384.
Proof. vm_refl. Qed.
Lemma D_2b384 : decode_any W_2b384 = Some (Store SZ8 11 13 2384, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2b388 : bv 32 := 0x3701106f.
Lemma F_2b388 : fetch_word Plain.M.loaded_segments (0x2b388 : word) = Some W_2b388.
Proof. vm_refl. Qed.
Lemma D_2b388 : decode_any W_2b388 = Some (Jal 0 70512, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2b38c : bv 32 := 0x00066517.
Lemma F_2b38c : fetch_word Plain.M.loaded_segments (0x2b38c : word) = Some W_2b38c.
Proof. vm_refl. Qed.
Lemma D_2b38c : decode_any W_2b38c = Some (Auipc 10 102, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2b390 : bv 32 := 0x94c50503.
Lemma F_2b390 : fetch_word Plain.M.loaded_segments (0x2b390 : word) = Some W_2b390.
Proof. vm_refl. Qed.
Lemma D_2b390 : decode_any W_2b390 = Some (Load SZ1 true 10 10 2380, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2b394 : bv 32 := 0x0230000f.
Lemma F_2b394 : fetch_word Plain.M.loaded_segments (0x2b394 : word) = Some W_2b394.
Proof. vm_refl. Qed.
Lemma D_2b394 : decode_any W_2b394 = Some (Fence 0 2 3 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2b398 : bv 32 := 0x00050463.
Lemma F_2b398 : fetch_word Plain.M.loaded_segments (0x2b398 : word) = Some W_2b398.
Proof. vm_refl. Qed.
Lemma D_2b398 : decode_any W_2b398 = Some (Branch BC_EQ 10 0 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2b39c : bv 32 := 0x00008067.
Lemma F_2b39c : fetch_word Plain.M.loaded_segments (0x2b39c : word) = Some W_2b39c.
Proof. vm_refl. Qed.
Lemma D_2b39c : decode_any W_2b39c = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2b3a0 : bv 32 := 0xff010113.
Lemma F_2b3a0 : fetch_word Plain.M.loaded_segments (0x2b3a0 : word) = Some W_2b3a0.
Proof. vm_refl. Qed.
Lemma D_2b3a0 : decode_any W_2b3a0 = Some (OpImm ALU_ADD 2 2 4080, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2b3a4 : bv 32 := 0x00113423.
Lemma F_2b3a4 : fetch_word Plain.M.loaded_segments (0x2b3a4 : word) = Some W_2b3a4.
Proof. vm_refl. Qed.
Lemma D_2b3a4 : decode_any W_2b3a4 = Some (Store SZ8 2 1 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2b3a8 : bv 32 := 0x00066517.
Lemma F_2b3a8 : fetch_word Plain.M.loaded_segments (0x2b3a8 : word) = Some W_2b3a8.
Proof. vm_refl. Qed.
Lemma D_2b3a8 : decode_any W_2b3a8 = Some (Auipc 10 102, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2b3ac : bv 32 := 0x93050513.
Lemma F_2b3ac : fetch_word Plain.M.loaded_segments (0x2b3ac : word) = Some W_2b3ac.
Proof. vm_refl. Qed.
Lemma D_2b3ac : decode_any W_2b3ac = Some (OpImm ALU_ADD 10 10 2352, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2b3b0 : bv 32 := 0x2f8110ef.
Lemma F_2b3b0 : fetch_word Plain.M.loaded_segments (0x2b3b0 : word) = Some W_2b3b0.
Proof. vm_refl. Qed.
Lemma D_2b3b0 : decode_any W_2b3b0 = Some (Jal 1 70392, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2b3b4 : bv 32 := 0x0005051b.
Lemma F_2b3b4 : fetch_word Plain.M.loaded_segments (0x2b3b4 : word) = Some W_2b3b4.
Proof. vm_refl. Qed.
Lemma D_2b3b4 : decode_any W_2b3b4 = Some (OpImm32 10 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2b3b8 : bv 32 := 0x00813083.
Lemma F_2b3b8 : fetch_word Plain.M.loaded_segments (0x2b3b8 : word) = Some W_2b3b8.
Proof. vm_refl. Qed.
Lemma D_2b3b8 : decode_any W_2b3b8 = Some (Load SZ8 true 1 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2b3bc : bv 32 := 0x01010113.
Lemma F_2b3bc : fetch_word Plain.M.loaded_segments (0x2b3bc : word) = Some W_2b3bc.
Proof. vm_refl. Qed.
Lemma D_2b3bc : decode_any W_2b3bc = Some (OpImm ALU_ADD 2 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2b3c0 : bv 32 := 0xfc050ee3.
Lemma F_2b3c0 : fetch_word Plain.M.loaded_segments (0x2b3c0 : word) = Some W_2b3c0.
Proof. vm_refl. Qed.
Lemma D_2b3c0 : decode_any W_2b3c0 = Some (Branch BC_EQ 10 0 8156, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2b3c4 : bv 32 := 0x00066597.
Lemma F_2b3c4 : fetch_word Plain.M.loaded_segments (0x2b3c4 : word) = Some W_2b3c4.
Proof. vm_refl. Qed.
Lemma D_2b3c4 : decode_any W_2b3c4 = Some (Auipc 11 102, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2b3c8 : bv 32 := 0x00055517.
Lemma F_2b3c8 : fetch_word Plain.M.loaded_segments (0x2b3c8 : word) = Some W_2b3c8.
Proof. vm_refl. Qed.
Lemma D_2b3c8 : decode_any W_2b3c8 = Some (Auipc 10 85, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2b3cc : bv 32 := 0x00066617.
Lemma F_2b3cc : fetch_word Plain.M.loaded_segments (0x2b3cc : word) = Some W_2b3cc.
Proof. vm_refl. Qed.
Lemma D_2b3cc : decode_any W_2b3cc = Some (Auipc 12 102, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2b3d0 : bv 32 := 0x55050693.
Lemma F_2b3d0 : fetch_word Plain.M.loaded_segments (0x2b3d0 : word) = Some W_2b3d0.
Proof. vm_refl. Qed.
Lemma D_2b3d0 : decode_any W_2b3d0 = Some (OpImm ALU_ADD 13 10 1360, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2b3d4 : bv 32 := 0x90c60513.
Lemma F_2b3d4 : fetch_word Plain.M.loaded_segments (0x2b3d4 : word) = Some W_2b3d4.
Proof. vm_refl. Qed.
Lemma D_2b3d4 : decode_any W_2b3d4 = Some (OpImm ALU_ADD 10 12 2316, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2b3d8 : bv 32 := 0x90d5b623.
Lemma F_2b3d8 : fetch_word Plain.M.loaded_segments (0x2b3d8 : word) = Some W_2b3d8.
Proof. vm_refl. Qed.
Lemma D_2b3d8 : decode_any W_2b3d8 = Some (Store SZ8 11 13 2316, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_2b3dc : bv 32 := 0x31c1106f.
Lemma F_2b3dc : fetch_word Plain.M.loaded_segments (0x2b3dc : word) = Some W_2b3dc.
Proof. vm_refl. Qed.
Lemma D_2b3dc : decode_any W_2b3dc = Some (Jal 0 70428, 4%Z).
Proof. vm_refl. Qed.
