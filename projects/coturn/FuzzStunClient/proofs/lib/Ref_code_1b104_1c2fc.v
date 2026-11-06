(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)

From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.coturn.FuzzStunClient.images Require Import Plain.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.

(* [comment removed for export] *)
Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.


(* [comment removed for export] *)
Definition W_1b260 : bv 32 := 0xfbf5059b.
Lemma F_1b260 : fetch_word Plain.M.loaded_segments (0x1b260 : word) = Some W_1b260.
Proof. vm_refl. Qed.
Lemma D_1b260 : decode_any W_1b260 = Some (OpImm32 11 10 4031, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1b264 : bv 32 := 0x01a5b593.
Lemma F_1b264 : fetch_word Plain.M.loaded_segments (0x1b264 : word) = Some W_1b264.
Proof. vm_refl. Qed.
Lemma D_1b264 : decode_any W_1b264 = Some (OpImm ALU_SLTU 11 11 26, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1b268 : bv 32 := 0x00559593.
Lemma F_1b268 : fetch_word Plain.M.loaded_segments (0x1b268 : word) = Some W_1b268.
Proof. vm_refl. Qed.
Lemma D_1b268 : decode_any W_1b268 = Some (ShiftImm ALU_SLL 11 11 5, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1b26c : bv 32 := 0x00b56533.
Lemma F_1b26c : fetch_word Plain.M.loaded_segments (0x1b26c : word) = Some W_1b26c.
Proof. vm_refl. Qed.
Lemma D_1b26c : decode_any W_1b26c = Some (Op ALU_OR 10 10 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1b270 : bv 32 := 0x00008067.
Lemma F_1b270 : fetch_word Plain.M.loaded_segments (0x1b270 : word) = Some W_1b270.
Proof. vm_refl. Qed.
Lemma D_1b270 : decode_any W_1b270 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1b274 : bv 32 := 0x00008067.
Lemma F_1b274 : fetch_word Plain.M.loaded_segments (0x1b274 : word) = Some W_1b274.
Proof. vm_refl. Qed.
Lemma D_1b274 : decode_any W_1b274 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1b278 : bv 32 := 0xe8010113.
Lemma F_1b278 : fetch_word Plain.M.loaded_segments (0x1b278 : word) = Some W_1b278.
Proof. vm_refl. Qed.
Lemma D_1b278 : decode_any W_1b278 = Some (OpImm ALU_ADD 2 2 3712, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1b27c : bv 32 := 0x16113c23.
Lemma F_1b27c : fetch_word Plain.M.loaded_segments (0x1b27c : word) = Some W_1b27c.
Proof. vm_refl. Qed.
Lemma D_1b27c : decode_any W_1b27c = Some (Store SZ8 2 1 376, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1b280 : bv 32 := 0x16813823.
Lemma F_1b280 : fetch_word Plain.M.loaded_segments (0x1b280 : word) = Some W_1b280.
Proof. vm_refl. Qed.
Lemma D_1b280 : decode_any W_1b280 = Some (Store SZ8 2 8 368, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1b284 : bv 32 := 0x16913423.
Lemma F_1b284 : fetch_word Plain.M.loaded_segments (0x1b284 : word) = Some W_1b284.
Proof. vm_refl. Qed.
Lemma D_1b284 : decode_any W_1b284 = Some (Store SZ8 2 9 360, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1b288 : bv 32 := 0x17213023.
Lemma F_1b288 : fetch_word Plain.M.loaded_segments (0x1b288 : word) = Some W_1b288.
Proof. vm_refl. Qed.
Lemma D_1b288 : decode_any W_1b288 = Some (Store SZ8 2 18 352, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1b28c : bv 32 := 0x00058413.
Lemma F_1b28c : fetch_word Plain.M.loaded_segments (0x1b28c : word) = Some W_1b28c.
Proof. vm_refl. Qed.
Lemma D_1b28c : decode_any W_1b28c = Some (OpImm ALU_ADD 8 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1b290 : bv 32 := 0x00050493.
Lemma F_1b290 : fetch_word Plain.M.loaded_segments (0x1b290 : word) = Some W_1b290.
Proof. vm_refl. Qed.
Lemma D_1b290 : decode_any W_1b290 = Some (OpImm ALU_ADD 9 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1b294 : bv 32 := 0x03010513.
Lemma F_1b294 : fetch_word Plain.M.loaded_segments (0x1b294 : word) = Some W_1b294.
Proof. vm_refl. Qed.
Lemma D_1b294 : decode_any W_1b294 = Some (OpImm ALU_ADD 10 2 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1b298 : bv 32 := 0x13000613.
Lemma F_1b298 : fetch_word Plain.M.loaded_segments (0x1b298 : word) = Some W_1b298.
Proof. vm_refl. Qed.
Lemma D_1b298 : decode_any W_1b298 = Some (OpImm ALU_ADD 12 0 304, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1b29c : bv 32 := 0x00000593.
Lemma F_1b29c : fetch_word Plain.M.loaded_segments (0x1b29c : word) = Some W_1b29c.
Proof. vm_refl. Qed.
Lemma D_1b29c : decode_any W_1b29c = Some (OpImm ALU_ADD 11 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1b2a0 : bv 32 := 0x7a4080ef.
Lemma F_1b2a0 : fetch_word Plain.M.loaded_segments (0x1b2a0 : word) = Some W_1b2a0.
Proof. vm_refl. Qed.
Lemma D_1b2a0 : decode_any W_1b2a0 = Some (Jal 1 34724, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1b2a4 : bv 32 := 0x0000a517.
Lemma F_1b2a4 : fetch_word Plain.M.loaded_segments (0x1b2a4 : word) = Some W_1b2a4.
Proof. vm_refl. Qed.
Lemma D_1b2a4 : decode_any W_1b2a4 = Some (Auipc 10 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1b2a8 : bv 32 := 0x05c53503.
Lemma F_1b2a8 : fetch_word Plain.M.loaded_segments (0x1b2a8 : word) = Some W_1b2a8.
Proof. vm_refl. Qed.
Lemma D_1b2a8 : decode_any W_1b2a8 = Some (Load SZ8 true 10 10 92, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1b2ac : bv 32 := 0x00953023.
Lemma F_1b2ac : fetch_word Plain.M.loaded_segments (0x1b2ac : word) = Some W_1b2ac.
Proof. vm_refl. Qed.
Lemma D_1b2ac : decode_any W_1b2ac = Some (Store SZ8 10 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1b2b0 : bv 32 := 0x0004b503.
Lemma F_1b2b0 : fetch_word Plain.M.loaded_segments (0x1b2b0 : word) = Some W_1b2b0.
Proof. vm_refl. Qed.
Lemma D_1b2b0 : decode_any W_1b2b0 = Some (Load SZ8 true 10 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1b2b4 : bv 32 := 0x00848493.
Lemma F_1b2b4 : fetch_word Plain.M.loaded_segments (0x1b2b4 : word) = Some W_1b2b4.
Proof. vm_refl. Qed.
Lemma D_1b2b4 : decode_any W_1b2b4 = Some (OpImm ALU_ADD 9 9 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1b2b8 : bv 32 := 0xfe051ce3.
Lemma F_1b2b8 : fetch_word Plain.M.loaded_segments (0x1b2b8 : word) = Some W_1b2b8.
Proof. vm_refl. Qed.
Lemma D_1b2b8 : decode_any W_1b2b8 = Some (Branch BC_NE 10 0 8184, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1b2bc : bv 32 := 0x0003b517.
Lemma F_1b2bc : fetch_word Plain.M.loaded_segments (0x1b2bc : word) = Some W_1b2bc.
Proof. vm_refl. Qed.
Lemma D_1b2bc : decode_any W_1b2bc = Some (Auipc 10 59, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1b2c0 : bv 32 := 0x77c50913.
Lemma F_1b2c0 : fetch_word Plain.M.loaded_segments (0x1b2c0 : word) = Some W_1b2c0.
Proof. vm_refl. Qed.
Lemma D_1b2c0 : decode_any W_1b2c0 = Some (OpImm ALU_ADD 18 10 1916, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1b2c4 : bv 32 := 0x00993423.
Lemma F_1b2c4 : fetch_word Plain.M.loaded_segments (0x1b2c4 : word) = Some W_1b2c4.
Proof. vm_refl. Qed.
Lemma D_1b2c4 : decode_any W_1b2c4 = Some (Store SZ8 18 9 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1b2c8 : bv 32 := 0x0004b583.
Lemma F_1b2c8 : fetch_word Plain.M.loaded_segments (0x1b2c8 : word) = Some W_1b2c8.
Proof. vm_refl. Qed.
Lemma D_1b2c8 : decode_any W_1b2c8 = Some (Load SZ8 true 11 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1b2cc : bv 32 := 0x04058c63.
Lemma F_1b2cc : fetch_word Plain.M.loaded_segments (0x1b2cc : word) = Some W_1b2cc.
Proof. vm_refl. Qed.
Lemma D_1b2cc : decode_any W_1b2cc = Some (Branch BC_EQ 11 0 88, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1b2d0 : bv 32 := 0x01048493.
Lemma F_1b2d0 : fetch_word Plain.M.loaded_segments (0x1b2d0 : word) = Some W_1b2d0.
Proof. vm_refl. Qed.
Lemma D_1b2d0 : decode_any W_1b2d0 = Some (OpImm ALU_ADD 9 9 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1b2d4 : bv 32 := 0x02500513.
Lemma F_1b2d4 : fetch_word Plain.M.loaded_segments (0x1b2d4 : word) = Some W_1b2d4.
Proof. vm_refl. Qed.
Lemma D_1b2d4 : decode_any W_1b2d4 = Some (OpImm ALU_ADD 10 0 37, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1b2d8 : bv 32 := 0x03010613.
Lemma F_1b2d8 : fetch_word Plain.M.loaded_segments (0x1b2d8 : word) = Some W_1b2d8.
Proof. vm_refl. Qed.
Lemma D_1b2d8 : decode_any W_1b2d8 = Some (OpImm ALU_ADD 12 2 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1b2dc : bv 32 := 0x0100006f.
Lemma F_1b2dc : fetch_word Plain.M.loaded_segments (0x1b2dc : word) = Some W_1b2dc.
Proof. vm_refl. Qed.
Lemma D_1b2dc : decode_any W_1b2dc = Some (Jal 0 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1b2e0 : bv 32 := 0x0004b583.
Lemma F_1b2e0 : fetch_word Plain.M.loaded_segments (0x1b2e0 : word) = Some W_1b2e0.
Proof. vm_refl. Qed.
Lemma D_1b2e0 : decode_any W_1b2e0 = Some (Load SZ8 true 11 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1b2e4 : bv 32 := 0x01048493.
Lemma F_1b2e4 : fetch_word Plain.M.loaded_segments (0x1b2e4 : word) = Some W_1b2e4.
Proof. vm_refl. Qed.
Lemma D_1b2e4 : decode_any W_1b2e4 = Some (OpImm ALU_ADD 9 9 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1b2e8 : bv 32 := 0x00058e63.
Lemma F_1b2e8 : fetch_word Plain.M.loaded_segments (0x1b2e8 : word) = Some W_1b2e8.
Proof. vm_refl. Qed.
Lemma D_1b2e8 : decode_any W_1b2e8 = Some (Branch BC_EQ 11 0 28, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1b2ec : bv 32 := 0xfeb56ae3.
Lemma F_1b2ec : fetch_word Plain.M.loaded_segments (0x1b2ec : word) = Some W_1b2ec.
Proof. vm_refl. Qed.
Lemma D_1b2ec : decode_any W_1b2ec = Some (Branch BC_LTU 10 11 8180, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1b2f0 : bv 32 := 0xff84b683.
Lemma F_1b2f0 : fetch_word Plain.M.loaded_segments (0x1b2f0 : word) = Some W_1b2f0.
Proof. vm_refl. Qed.
Lemma D_1b2f0 : decode_any W_1b2f0 = Some (Load SZ8 true 13 9 4088, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1b2f4 : bv 32 := 0x00359593.
Lemma F_1b2f4 : fetch_word Plain.M.loaded_segments (0x1b2f4 : word) = Some W_1b2f4.
Proof. vm_refl. Qed.
Lemma D_1b2f4 : decode_any W_1b2f4 = Some (ShiftImm ALU_SLL 11 11 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1b2f8 : bv 32 := 0x00b605b3.
Lemma F_1b2f8 : fetch_word Plain.M.loaded_segments (0x1b2f8 : word) = Some W_1b2f8.
Proof. vm_refl. Qed.
Lemma D_1b2f8 : decode_any W_1b2f8 = Some (Op ALU_ADD 11 12 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1b2fc : bv 32 := 0x00d5b023.
Lemma F_1b2fc : fetch_word Plain.M.loaded_segments (0x1b2fc : word) = Some W_1b2fc.
Proof. vm_refl. Qed.
Lemma D_1b2fc : decode_any W_1b2fc = Some (Store SZ8 11 13 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1b300 : bv 32 := 0xfe1ff06f.
Lemma F_1b300 : fetch_word Plain.M.loaded_segments (0x1b300 : word) = Some W_1b300.
Proof. vm_refl. Qed.
Lemma D_1b300 : decode_any W_1b300 = Some (Jal 0 2097120, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1b304 : bv 32 := 0x0b013583.
Lemma F_1b304 : fetch_word Plain.M.loaded_segments (0x1b304 : word) = Some W_1b304.
Proof. vm_refl. Qed.
Lemma D_1b304 : decode_any W_1b304 = Some (Load SZ8 true 11 2 176, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1b308 : bv 32 := 0x13013503.
Lemma F_1b308 : fetch_word Plain.M.loaded_segments (0x1b308 : word) = Some W_1b308.
Proof. vm_refl. Qed.
Lemma D_1b308 : decode_any W_1b308 = Some (Load SZ8 true 10 2 304, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1b30c : bv 32 := 0x0003b617.
Lemma F_1b30c : fetch_word Plain.M.loaded_segments (0x1b30c : word) = Some W_1b30c.
Proof. vm_refl. Qed.
Lemma D_1b30c : decode_any W_1b30c = Some (Auipc 12 59, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1b310 : bv 32 := 0x78b63a23.
Lemma F_1b310 : fetch_word Plain.M.loaded_segments (0x1b310 : word) = Some W_1b310.
Proof. vm_refl. Qed.
Lemma D_1b310 : decode_any W_1b310 = Some (Store SZ8 12 11 1940, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1b314 : bv 32 := 0x00050c63.
Lemma F_1b314 : fetch_word Plain.M.loaded_segments (0x1b314 : word) = Some W_1b314.
Proof. vm_refl. Qed.
Lemma D_1b314 : decode_any W_1b314 = Some (Branch BC_EQ 10 0 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1b32c : bv 32 := 0x06013503.
Lemma F_1b32c : fetch_word Plain.M.loaded_segments (0x1b32c : word) = Some W_1b32c.
Proof. vm_refl. Qed.
Lemma D_1b32c : decode_any W_1b32c = Some (Load SZ8 true 10 2 96, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1b330 : bv 32 := 0x02a93823.
Lemma F_1b330 : fetch_word Plain.M.loaded_segments (0x1b330 : word) = Some W_1b330.
Proof. vm_refl. Qed.
Lemma D_1b330 : decode_any W_1b330 = Some (Store SZ8 18 10 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1b334 : bv 32 := 0x00041463.
Lemma F_1b334 : fetch_word Plain.M.loaded_segments (0x1b334 : word) = Some W_1b334.
Proof. vm_refl. Qed.
Lemma D_1b334 : decode_any W_1b334 = Some (Branch BC_NE 8 0 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1b33c : bv 32 := 0x00041663.
Lemma F_1b33c : fetch_word Plain.M.loaded_segments (0x1b33c : word) = Some W_1b33c.
Proof. vm_refl. Qed.
Lemma D_1b33c : decode_any W_1b33c = Some (Branch BC_NE 8 0 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1b348 : bv 32 := 0x0000a517.
Lemma F_1b348 : fetch_word Plain.M.loaded_segments (0x1b348 : word) = Some W_1b348.
Proof. vm_refl. Qed.
Lemma D_1b348 : decode_any W_1b348 = Some (Auipc 10 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1b34c : bv 32 := 0xfc053583.
Lemma F_1b34c : fetch_word Plain.M.loaded_segments (0x1b34c : word) = Some W_1b34c.
Proof. vm_refl. Qed.
Lemma D_1b34c : decode_any W_1b34c = Some (Load SZ8 true 11 10 4032, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1b350 : bv 32 := 0x0000a517.
Lemma F_1b350 : fetch_word Plain.M.loaded_segments (0x1b350 : word) = Some W_1b350.
Proof. vm_refl. Qed.
Lemma D_1b350 : decode_any W_1b350 = Some (Auipc 10 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1b354 : bv 32 := 0xfc053503.
Lemma F_1b354 : fetch_word Plain.M.loaded_segments (0x1b354 : word) = Some W_1b354.
Proof. vm_refl. Qed.
Lemma D_1b354 : decode_any W_1b354 = Some (Load SZ8 true 10 10 4032, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1b358 : bv 32 := 0x0085b023.
Lemma F_1b358 : fetch_word Plain.M.loaded_segments (0x1b358 : word) = Some W_1b358.
Proof. vm_refl. Qed.
Lemma D_1b358 : decode_any W_1b358 = Some (Store SZ8 11 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1b35c : bv 32 := 0x00140593.
Lemma F_1b35c : fetch_word Plain.M.loaded_segments (0x1b35c : word) = Some W_1b35c.
Proof. vm_refl. Qed.
Lemma D_1b35c : decode_any W_1b35c = Some (OpImm ALU_ADD 11 8 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1b360 : bv 32 := 0x00853023.
Lemma F_1b360 : fetch_word Plain.M.loaded_segments (0x1b360 : word) = Some W_1b360.
Proof. vm_refl. Qed.
Lemma D_1b360 : decode_any W_1b360 = Some (Store SZ8 10 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1b364 : bv 32 := 0x02f00613.
Lemma F_1b364 : fetch_word Plain.M.loaded_segments (0x1b364 : word) = Some W_1b364.
Proof. vm_refl. Qed.
Lemma D_1b364 : decode_any W_1b364 = Some (OpImm ALU_ADD 12 0 47, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1b368 : bv 32 := 0x00c0006f.
Lemma F_1b368 : fetch_word Plain.M.loaded_segments (0x1b368 : word) = Some W_1b368.
Proof. vm_refl. Qed.
Lemma D_1b368 : decode_any W_1b368 = Some (Jal 0 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1b36c : bv 32 := 0x00b53023.
Lemma F_1b36c : fetch_word Plain.M.loaded_segments (0x1b36c : word) = Some W_1b36c.
Proof. vm_refl. Qed.
Lemma D_1b36c : decode_any W_1b36c = Some (Store SZ8 10 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1b370 : bv 32 := 0x00158593.
Lemma F_1b370 : fetch_word Plain.M.loaded_segments (0x1b370 : word) = Some W_1b370.
Proof. vm_refl. Qed.
Lemma D_1b370 : decode_any W_1b370 = Some (OpImm ALU_ADD 11 11 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1b374 : bv 32 := 0xfff5c683.
Lemma F_1b374 : fetch_word Plain.M.loaded_segments (0x1b374 : word) = Some W_1b374.
Proof. vm_refl. Qed.
Lemma D_1b374 : decode_any W_1b374 = Some (Load SZ1 false 13 11 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1b378 : bv 32 := 0xfec68ae3.
Lemma F_1b378 : fetch_word Plain.M.loaded_segments (0x1b378 : word) = Some W_1b378.
Proof. vm_refl. Qed.
Lemma D_1b378 : decode_any W_1b378 = Some (Branch BC_EQ 13 12 8180, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1b37c : bv 32 := 0xfe069ae3.
Lemma F_1b37c : fetch_word Plain.M.loaded_segments (0x1b37c : word) = Some W_1b37c.
Proof. vm_refl. Qed.
Lemma D_1b37c : decode_any W_1b37c = Some (Branch BC_NE 13 0 8180, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1b380 : bv 32 := 0x03010513.
Lemma F_1b380 : fetch_word Plain.M.loaded_segments (0x1b380 : word) = Some W_1b380.
Proof. vm_refl. Qed.
Lemma D_1b380 : decode_any W_1b380 = Some (OpImm ALU_ADD 10 2 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1b384 : bv 32 := 0x214000ef.
Lemma F_1b384 : fetch_word Plain.M.loaded_segments (0x1b384 : word) = Some W_1b384.
Proof. vm_refl. Qed.
Lemma D_1b384 : decode_any W_1b384 = Some (Jal 1 532, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1b388 : bv 32 := 0x0f813503.
Lemma F_1b388 : fetch_word Plain.M.loaded_segments (0x1b388 : word) = Some W_1b388.
Proof. vm_refl. Qed.
Lemma D_1b388 : decode_any W_1b388 = Some (Load SZ8 true 10 2 248, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1b38c : bv 32 := 0x4bc000ef.
Lemma F_1b38c : fetch_word Plain.M.loaded_segments (0x1b38c : word) = Some W_1b38c.
Proof. vm_refl. Qed.
Lemma D_1b38c : decode_any W_1b38c = Some (Jal 1 1212, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1b390 : bv 32 := 0x08813503.
Lemma F_1b390 : fetch_word Plain.M.loaded_segments (0x1b390 : word) = Some W_1b390.
Proof. vm_refl. Qed.
Lemma D_1b390 : decode_any W_1b390 = Some (Load SZ8 true 10 2 136, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1b394 : bv 32 := 0x09013583.
Lemma F_1b394 : fetch_word Plain.M.loaded_segments (0x1b394 : word) = Some W_1b394.
Proof. vm_refl. Qed.
Lemma D_1b394 : decode_any W_1b394 = Some (Load SZ8 true 11 2 144, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1b398 : bv 32 := 0x00b51c63.
Lemma F_1b398 : fetch_word Plain.M.loaded_segments (0x1b398 : word) = Some W_1b398.
Proof. vm_refl. Qed.
Lemma D_1b398 : decode_any W_1b398 = Some (Branch BC_NE 10 11 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1b39c : bv 32 := 0x09813503.
Lemma F_1b39c : fetch_word Plain.M.loaded_segments (0x1b39c : word) = Some W_1b39c.
Proof. vm_refl. Qed.
Lemma D_1b39c : decode_any W_1b39c = Some (Load SZ8 true 10 2 152, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1b3a0 : bv 32 := 0x0a013583.
Lemma F_1b3a0 : fetch_word Plain.M.loaded_segments (0x1b3a0 : word) = Some W_1b3a0.
Proof. vm_refl. Qed.
Lemma D_1b3a0 : decode_any W_1b3a0 = Some (Load SZ8 true 11 2 160, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1b3a4 : bv 32 := 0x00b51663.
Lemma F_1b3a4 : fetch_word Plain.M.loaded_segments (0x1b3a4 : word) = Some W_1b3a4.
Proof. vm_refl. Qed.
Lemma D_1b3a4 : decode_any W_1b3a4 = Some (Branch BC_NE 10 11 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1b3a8 : bv 32 := 0x0e813503.
Lemma F_1b3a8 : fetch_word Plain.M.loaded_segments (0x1b3a8 : word) = Some W_1b3a8.
Proof. vm_refl. Qed.
Lemma D_1b3a8 : decode_any W_1b3a8 = Some (Load SZ8 true 10 2 232, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1b3ac : bv 32 := 0x0e050063.
Lemma F_1b3ac : fetch_word Plain.M.loaded_segments (0x1b3ac : word) = Some W_1b3ac.
Proof. vm_refl. Qed.
Lemma D_1b3ac : decode_any W_1b3ac = Some (Branch BC_EQ 10 0 224, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1b48c : bv 32 := 0x17813083.
Lemma F_1b48c : fetch_word Plain.M.loaded_segments (0x1b48c : word) = Some W_1b48c.
Proof. vm_refl. Qed.
Lemma D_1b48c : decode_any W_1b48c = Some (Load SZ8 true 1 2 376, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1b490 : bv 32 := 0x17013403.
Lemma F_1b490 : fetch_word Plain.M.loaded_segments (0x1b490 : word) = Some W_1b490.
Proof. vm_refl. Qed.
Lemma D_1b490 : decode_any W_1b490 = Some (Load SZ8 true 8 2 368, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1b494 : bv 32 := 0x16813483.
Lemma F_1b494 : fetch_word Plain.M.loaded_segments (0x1b494 : word) = Some W_1b494.
Proof. vm_refl. Qed.
Lemma D_1b494 : decode_any W_1b494 = Some (Load SZ8 true 9 2 360, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1b498 : bv 32 := 0x16013903.
Lemma F_1b498 : fetch_word Plain.M.loaded_segments (0x1b498 : word) = Some W_1b498.
Proof. vm_refl. Qed.
Lemma D_1b498 : decode_any W_1b498 = Some (Load SZ8 true 18 2 352, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1b49c : bv 32 := 0x18010113.
Lemma F_1b49c : fetch_word Plain.M.loaded_segments (0x1b49c : word) = Some W_1b49c.
Proof. vm_refl. Qed.
Lemma D_1b49c : decode_any W_1b49c = Some (OpImm ALU_ADD 2 2 384, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1b4a0 : bv 32 := 0x00008067.
Lemma F_1b4a0 : fetch_word Plain.M.loaded_segments (0x1b4a0 : word) = Some W_1b4a0.
Proof. vm_refl. Qed.
Lemma D_1b4a0 : decode_any W_1b4a0 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1b4a4 : bv 32 := 0xfe010113.
Lemma F_1b4a4 : fetch_word Plain.M.loaded_segments (0x1b4a4 : word) = Some W_1b4a4.
Proof. vm_refl. Qed.
Lemma D_1b4a4 : decode_any W_1b4a4 = Some (OpImm ALU_ADD 2 2 4064, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1b4a8 : bv 32 := 0x00113c23.
Lemma F_1b4a8 : fetch_word Plain.M.loaded_segments (0x1b4a8 : word) = Some W_1b4a8.
Proof. vm_refl. Qed.
Lemma D_1b4a8 : decode_any W_1b4a8 = Some (Store SZ8 2 1 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1b4ac : bv 32 := 0x00813823.
Lemma F_1b4ac : fetch_word Plain.M.loaded_segments (0x1b4ac : word) = Some W_1b4ac.
Proof. vm_refl. Qed.
Lemma D_1b4ac : decode_any W_1b4ac = Some (Store SZ8 2 8 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1b4b0 : bv 32 := 0x00913423.
Lemma F_1b4b0 : fetch_word Plain.M.loaded_segments (0x1b4b0 : word) = Some W_1b4b0.
Proof. vm_refl. Qed.
Lemma D_1b4b0 : decode_any W_1b4b0 = Some (Store SZ8 2 9 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1b4b4 : bv 32 := 0xdc1ff0ef.
Lemma F_1b4b4 : fetch_word Plain.M.loaded_segments (0x1b4b4 : word) = Some W_1b4b4.
Proof. vm_refl. Qed.
Lemma D_1b4b4 : decode_any W_1b4b4 = Some (Jal 1 2096576, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1b4b8 : bv 32 := 0x0000a517.
Lemma F_1b4b8 : fetch_word Plain.M.loaded_segments (0x1b4b8 : word) = Some W_1b4b8.
Proof. vm_refl. Qed.
Lemma D_1b4b8 : decode_any W_1b4b8 = Some (Auipc 10 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1b4bc : bv 32 := 0x0000a597.
Lemma F_1b4bc : fetch_word Plain.M.loaded_segments (0x1b4bc : word) = Some W_1b4bc.
Proof. vm_refl. Qed.
Lemma D_1b4bc : decode_any W_1b4bc = Some (Auipc 11 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1b4c0 : bv 32 := 0xe6053403.
Lemma F_1b4c0 : fetch_word Plain.M.loaded_segments (0x1b4c0 : word) = Some W_1b4c0.
Proof. vm_refl. Qed.
Lemma D_1b4c0 : decode_any W_1b4c0 = Some (Load SZ8 true 8 10 3680, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1b4c4 : bv 32 := 0xe645b483.
Lemma F_1b4c4 : fetch_word Plain.M.loaded_segments (0x1b4c4 : word) = Some W_1b4c4.
Proof. vm_refl. Qed.
Lemma D_1b4c4 : decode_any W_1b4c4 = Some (Load SZ8 true 9 11 3684, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1b4c8 : bv 32 := 0x0084fa63.
Lemma F_1b4c8 : fetch_word Plain.M.loaded_segments (0x1b4c8 : word) = Some W_1b4c8.
Proof. vm_refl. Qed.
Lemma D_1b4c8 : decode_any W_1b4c8 = Some (Branch BC_GEU 9 8 20, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1b4cc : bv 32 := 0x0004b503.
Lemma F_1b4cc : fetch_word Plain.M.loaded_segments (0x1b4cc : word) = Some W_1b4cc.
Proof. vm_refl. Qed.
Lemma D_1b4cc : decode_any W_1b4cc = Some (Load SZ8 true 10 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1b4d0 : bv 32 := 0x000500e7.
Lemma F_1b4d0 : fetch_word Plain.M.loaded_segments (0x1b4d0 : word) = Some W_1b4d0.
Proof. vm_refl. Qed.
Lemma D_1b4d0 : decode_any W_1b4d0 = Some (Jalr 1 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1b4d4 : bv 32 := 0x00848493.
Lemma F_1b4d4 : fetch_word Plain.M.loaded_segments (0x1b4d4 : word) = Some W_1b4d4.
Proof. vm_refl. Qed.
Lemma D_1b4d4 : decode_any W_1b4d4 = Some (OpImm ALU_ADD 9 9 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1b4d8 : bv 32 := 0xfe84eae3.
Lemma F_1b4d8 : fetch_word Plain.M.loaded_segments (0x1b4d8 : word) = Some W_1b4d8.
Proof. vm_refl. Qed.
Lemma D_1b4d8 : decode_any W_1b4d8 = Some (Branch BC_LTU 9 8 8180, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1b4dc : bv 32 := 0x01813083.
Lemma F_1b4dc : fetch_word Plain.M.loaded_segments (0x1b4dc : word) = Some W_1b4dc.
Proof. vm_refl. Qed.
Lemma D_1b4dc : decode_any W_1b4dc = Some (Load SZ8 true 1 2 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1b4e0 : bv 32 := 0x01013403.
Lemma F_1b4e0 : fetch_word Plain.M.loaded_segments (0x1b4e0 : word) = Some W_1b4e0.
Proof. vm_refl. Qed.
Lemma D_1b4e0 : decode_any W_1b4e0 = Some (Load SZ8 true 8 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1b4e4 : bv 32 := 0x00813483.
Lemma F_1b4e4 : fetch_word Plain.M.loaded_segments (0x1b4e4 : word) = Some W_1b4e4.
Proof. vm_refl. Qed.
Lemma D_1b4e4 : decode_any W_1b4e4 = Some (Load SZ8 true 9 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1b4e8 : bv 32 := 0x02010113.
Lemma F_1b4e8 : fetch_word Plain.M.loaded_segments (0x1b4e8 : word) = Some W_1b4e8.
Proof. vm_refl. Qed.
Lemma D_1b4e8 : decode_any W_1b4e8 = Some (OpImm ALU_ADD 2 2 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1b4ec : bv 32 := 0x00008067.
Lemma F_1b4ec : fetch_word Plain.M.loaded_segments (0x1b4ec : word) = Some W_1b4ec.
Proof. vm_refl. Qed.
Lemma D_1b4ec : decode_any W_1b4ec = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1b4f0 : bv 32 := 0xfe010113.
Lemma F_1b4f0 : fetch_word Plain.M.loaded_segments (0x1b4f0 : word) = Some W_1b4f0.
Proof. vm_refl. Qed.
Lemma D_1b4f0 : decode_any W_1b4f0 = Some (OpImm ALU_ADD 2 2 4064, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1b4f4 : bv 32 := 0x00113c23.
Lemma F_1b4f4 : fetch_word Plain.M.loaded_segments (0x1b4f4 : word) = Some W_1b4f4.
Proof. vm_refl. Qed.
Lemma D_1b4f4 : decode_any W_1b4f4 = Some (Store SZ8 2 1 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1b4f8 : bv 32 := 0x00813823.
Lemma F_1b4f8 : fetch_word Plain.M.loaded_segments (0x1b4f8 : word) = Some W_1b4f8.
Proof. vm_refl. Qed.
Lemma D_1b4f8 : decode_any W_1b4f8 = Some (Store SZ8 2 8 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1b4fc : bv 32 := 0x00913423.
Lemma F_1b4fc : fetch_word Plain.M.loaded_segments (0x1b4fc : word) = Some W_1b4fc.
Proof. vm_refl. Qed.
Lemma D_1b4fc : decode_any W_1b4fc = Some (Store SZ8 2 9 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1b500 : bv 32 := 0x01213023.
Lemma F_1b500 : fetch_word Plain.M.loaded_segments (0x1b500 : word) = Some W_1b500.
Proof. vm_refl. Qed.
Lemma D_1b500 : decode_any W_1b500 = Some (Store SZ8 2 18 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1b504 : bv 32 := 0x00060413.
Lemma F_1b504 : fetch_word Plain.M.loaded_segments (0x1b504 : word) = Some W_1b504.
Proof. vm_refl. Qed.
Lemma D_1b504 : decode_any W_1b504 = Some (OpImm ALU_ADD 8 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1b508 : bv 32 := 0x00058493.
Lemma F_1b508 : fetch_word Plain.M.loaded_segments (0x1b508 : word) = Some W_1b508.
Proof. vm_refl. Qed.
Lemma D_1b508 : decode_any W_1b508 = Some (OpImm ALU_ADD 9 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1b50c : bv 32 := 0x00050913.
Lemma F_1b50c : fetch_word Plain.M.loaded_segments (0x1b50c : word) = Some W_1b50c.
Proof. vm_refl. Qed.
Lemma D_1b50c : decode_any W_1b50c = Some (OpImm ALU_ADD 18 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1b510 : bv 32 := 0x00063583.
Lemma F_1b510 : fetch_word Plain.M.loaded_segments (0x1b510 : word) = Some W_1b510.
Proof. vm_refl. Qed.
Lemma D_1b510 : decode_any W_1b510 = Some (Load SZ8 true 11 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1b514 : bv 32 := 0x00349513.
Lemma F_1b514 : fetch_word Plain.M.loaded_segments (0x1b514 : word) = Some W_1b514.
Proof. vm_refl. Qed.
Lemma D_1b514 : decode_any W_1b514 = Some (ShiftImm ALU_SLL 10 9 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1b518 : bv 32 := 0x00a60533.
Lemma F_1b518 : fetch_word Plain.M.loaded_segments (0x1b518 : word) = Some W_1b518.
Proof. vm_refl. Qed.
Lemma D_1b518 : decode_any W_1b518 = Some (Op ALU_ADD 10 12 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1b51c : bv 32 := 0x00850513.
Lemma F_1b51c : fetch_word Plain.M.loaded_segments (0x1b51c : word) = Some W_1b51c.
Proof. vm_refl. Qed.
Lemma D_1b51c : decode_any W_1b51c = Some (OpImm ALU_ADD 10 10 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1b520 : bv 32 := 0xd59ff0ef.
Lemma F_1b520 : fetch_word Plain.M.loaded_segments (0x1b520 : word) = Some W_1b520.
Proof. vm_refl. Qed.
Lemma D_1b520 : decode_any W_1b520 = Some (Jal 1 2096472, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1b524 : bv 32 := 0x00000517.
Lemma F_1b524 : fetch_word Plain.M.loaded_segments (0x1b524 : word) = Some W_1b524.
Proof. vm_refl. Qed.
Lemma D_1b524 : decode_any W_1b524 = Some (Auipc 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1b528 : bv 32 := 0x02c50313.
Lemma F_1b528 : fetch_word Plain.M.loaded_segments (0x1b528 : word) = Some W_1b528.
Proof. vm_refl. Qed.
Lemma D_1b528 : decode_any W_1b528 = Some (OpImm ALU_ADD 6 10 44, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1b52c : bv 32 := 0x00090513.
Lemma F_1b52c : fetch_word Plain.M.loaded_segments (0x1b52c : word) = Some W_1b52c.
Proof. vm_refl. Qed.
Lemma D_1b52c : decode_any W_1b52c = Some (OpImm ALU_ADD 10 18 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1b530 : bv 32 := 0x00048593.
Lemma F_1b530 : fetch_word Plain.M.loaded_segments (0x1b530 : word) = Some W_1b530.
Proof. vm_refl. Qed.
Lemma D_1b530 : decode_any W_1b530 = Some (OpImm ALU_ADD 11 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1b534 : bv 32 := 0x00040613.
Lemma F_1b534 : fetch_word Plain.M.loaded_segments (0x1b534 : word) = Some W_1b534.
Proof. vm_refl. Qed.
Lemma D_1b534 : decode_any W_1b534 = Some (OpImm ALU_ADD 12 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1b538 : bv 32 := 0x01813083.
Lemma F_1b538 : fetch_word Plain.M.loaded_segments (0x1b538 : word) = Some W_1b538.
Proof. vm_refl. Qed.
Lemma D_1b538 : decode_any W_1b538 = Some (Load SZ8 true 1 2 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1b53c : bv 32 := 0x01013403.
Lemma F_1b53c : fetch_word Plain.M.loaded_segments (0x1b53c : word) = Some W_1b53c.
Proof. vm_refl. Qed.
Lemma D_1b53c : decode_any W_1b53c = Some (Load SZ8 true 8 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1b540 : bv 32 := 0x00813483.
Lemma F_1b540 : fetch_word Plain.M.loaded_segments (0x1b540 : word) = Some W_1b540.
Proof. vm_refl. Qed.
Lemma D_1b540 : decode_any W_1b540 = Some (Load SZ8 true 9 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1b544 : bv 32 := 0x00013903.
Lemma F_1b544 : fetch_word Plain.M.loaded_segments (0x1b544 : word) = Some W_1b544.
Proof. vm_refl. Qed.
Lemma D_1b544 : decode_any W_1b544 = Some (Load SZ8 true 18 2 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1b548 : bv 32 := 0x02010113.
Lemma F_1b548 : fetch_word Plain.M.loaded_segments (0x1b548 : word) = Some W_1b548.
Proof. vm_refl. Qed.
Lemma D_1b548 : decode_any W_1b548 = Some (OpImm ALU_ADD 2 2 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1b54c : bv 32 := 0x00030067.
Lemma F_1b54c : fetch_word Plain.M.loaded_segments (0x1b54c : word) = Some W_1b54c.
Proof. vm_refl. Qed.
Lemma D_1b54c : decode_any W_1b54c = Some (Jalr 0 6 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1b550 : bv 32 := 0xfd010113.
Lemma F_1b550 : fetch_word Plain.M.loaded_segments (0x1b550 : word) = Some W_1b550.
Proof. vm_refl. Qed.
Lemma D_1b550 : decode_any W_1b550 = Some (OpImm ALU_ADD 2 2 4048, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1b554 : bv 32 := 0x02113423.
Lemma F_1b554 : fetch_word Plain.M.loaded_segments (0x1b554 : word) = Some W_1b554.
Proof. vm_refl. Qed.
Lemma D_1b554 : decode_any W_1b554 = Some (Store SZ8 2 1 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1b558 : bv 32 := 0x02813023.
Lemma F_1b558 : fetch_word Plain.M.loaded_segments (0x1b558 : word) = Some W_1b558.
Proof. vm_refl. Qed.
Lemma D_1b558 : decode_any W_1b558 = Some (Store SZ8 2 8 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1b55c : bv 32 := 0x00913c23.
Lemma F_1b55c : fetch_word Plain.M.loaded_segments (0x1b55c : word) = Some W_1b55c.
Proof. vm_refl. Qed.
Lemma D_1b55c : decode_any W_1b55c = Some (Store SZ8 2 9 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1b560 : bv 32 := 0x01213823.
Lemma F_1b560 : fetch_word Plain.M.loaded_segments (0x1b560 : word) = Some W_1b560.
Proof. vm_refl. Qed.
Lemma D_1b560 : decode_any W_1b560 = Some (Store SZ8 2 18 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1b564 : bv 32 := 0x01313423.
Lemma F_1b564 : fetch_word Plain.M.loaded_segments (0x1b564 : word) = Some W_1b564.
Proof. vm_refl. Qed.
Lemma D_1b564 : decode_any W_1b564 = Some (Store SZ8 2 19 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1b568 : bv 32 := 0x00060413.
Lemma F_1b568 : fetch_word Plain.M.loaded_segments (0x1b568 : word) = Some W_1b568.
Proof. vm_refl. Qed.
Lemma D_1b568 : decode_any W_1b568 = Some (OpImm ALU_ADD 8 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1b56c : bv 32 := 0x00058493.
Lemma F_1b56c : fetch_word Plain.M.loaded_segments (0x1b56c : word) = Some W_1b56c.
Proof. vm_refl. Qed.
Lemma D_1b56c : decode_any W_1b56c = Some (OpImm ALU_ADD 9 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1b570 : bv 32 := 0x00050913.
Lemma F_1b570 : fetch_word Plain.M.loaded_segments (0x1b570 : word) = Some W_1b570.
Proof. vm_refl. Qed.
Lemma D_1b570 : decode_any W_1b570 = Some (OpImm ALU_ADD 18 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1b574 : bv 32 := 0x00359513.
Lemma F_1b574 : fetch_word Plain.M.loaded_segments (0x1b574 : word) = Some W_1b574.
Proof. vm_refl. Qed.
Lemma D_1b574 : decode_any W_1b574 = Some (ShiftImm ALU_SLL 10 11 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1b578 : bv 32 := 0x00a60533.
Lemma F_1b578 : fetch_word Plain.M.loaded_segments (0x1b578 : word) = Some W_1b578.
Proof. vm_refl. Qed.
Lemma D_1b578 : decode_any W_1b578 = Some (Op ALU_ADD 10 12 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1b57c : bv 32 := 0x00850993.
Lemma F_1b57c : fetch_word Plain.M.loaded_segments (0x1b57c : word) = Some W_1b57c.
Proof. vm_refl. Qed.
Lemma D_1b57c : decode_any W_1b57c = Some (OpImm ALU_ADD 19 10 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1b580 : bv 32 := 0xf25ff0ef.
Lemma F_1b580 : fetch_word Plain.M.loaded_segments (0x1b580 : word) = Some W_1b580.
Proof. vm_refl. Qed.
Lemma D_1b580 : decode_any W_1b580 = Some (Jal 1 2096932, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1b584 : bv 32 := 0x00048513.
Lemma F_1b584 : fetch_word Plain.M.loaded_segments (0x1b584 : word) = Some W_1b584.
Proof. vm_refl. Qed.
Lemma D_1b584 : decode_any W_1b584 = Some (OpImm ALU_ADD 10 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1b588 : bv 32 := 0x00040593.
Lemma F_1b588 : fetch_word Plain.M.loaded_segments (0x1b588 : word) = Some W_1b588.
Proof. vm_refl. Qed.
Lemma D_1b588 : decode_any W_1b588 = Some (OpImm ALU_ADD 11 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1b58c : bv 32 := 0x00098613.
Lemma F_1b58c : fetch_word Plain.M.loaded_segments (0x1b58c : word) = Some W_1b58c.
Proof. vm_refl. Qed.
Lemma D_1b58c : decode_any W_1b58c = Some (OpImm ALU_ADD 12 19 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1b590 : bv 32 := 0x000900e7.
Lemma F_1b590 : fetch_word Plain.M.loaded_segments (0x1b590 : word) = Some W_1b590.
Proof. vm_refl. Qed.
Lemma D_1b590 : decode_any W_1b590 = Some (Jalr 1 18 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1b848 : bv 32 := 0xff010113.
Lemma F_1b848 : fetch_word Plain.M.loaded_segments (0x1b848 : word) = Some W_1b848.
Proof. vm_refl. Qed.
Lemma D_1b848 : decode_any W_1b848 = Some (OpImm ALU_ADD 2 2 4080, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1b84c : bv 32 := 0x00113423.
Lemma F_1b84c : fetch_word Plain.M.loaded_segments (0x1b84c : word) = Some W_1b84c.
Proof. vm_refl. Qed.
Lemma D_1b84c : decode_any W_1b84c = Some (Store SZ8 2 1 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1b850 : bv 32 := 0x00050e63.
Lemma F_1b850 : fetch_word Plain.M.loaded_segments (0x1b850 : word) = Some W_1b850.
Proof. vm_refl. Qed.
Lemma D_1b850 : decode_any W_1b850 = Some (Branch BC_EQ 10 0 28, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1b854 : bv 32 := 0x00050593.
Lemma F_1b854 : fetch_word Plain.M.loaded_segments (0x1b854 : word) = Some W_1b854.
Proof. vm_refl. Qed.
Lemma D_1b854 : decode_any W_1b854 = Some (OpImm ALU_ADD 11 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1b858 : bv 32 := 0x0000a517.
Lemma F_1b858 : fetch_word Plain.M.loaded_segments (0x1b858 : word) = Some W_1b858.
Proof. vm_refl. Qed.
Lemma D_1b858 : decode_any W_1b858 = Some (Auipc 10 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1b85c : bv 32 := 0xaa053503.
Lemma F_1b85c : fetch_word Plain.M.loaded_segments (0x1b85c : word) = Some W_1b85c.
Proof. vm_refl. Qed.
Lemma D_1b85c : decode_any W_1b85c = Some (Load SZ8 true 10 10 2720, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1b860 : bv 32 := 0x00800613.
Lemma F_1b860 : fetch_word Plain.M.loaded_segments (0x1b860 : word) = Some W_1b860.
Proof. vm_refl. Qed.
Lemma D_1b860 : decode_any W_1b860 = Some (OpImm ALU_ADD 12 0 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1b864 : bv 32 := 0x5dd070ef.
Lemma F_1b864 : fetch_word Plain.M.loaded_segments (0x1b864 : word) = Some W_1b864.
Proof. vm_refl. Qed.
Lemma D_1b864 : decode_any W_1b864 = Some (Jal 1 32220, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1b868 : bv 32 := 0x01c0006f.
Lemma F_1b868 : fetch_word Plain.M.loaded_segments (0x1b868 : word) = Some W_1b868.
Proof. vm_refl. Qed.
Lemma D_1b868 : decode_any W_1b868 = Some (Jal 0 28, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1b884 : bv 32 := 0x0000a517.
Lemma F_1b884 : fetch_word Plain.M.loaded_segments (0x1b884 : word) = Some W_1b884.
Proof. vm_refl. Qed.
Lemma D_1b884 : decode_any W_1b884 = Some (Auipc 10 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1b888 : bv 32 := 0xa7453503.
Lemma F_1b888 : fetch_word Plain.M.loaded_segments (0x1b888 : word) = Some W_1b888.
Proof. vm_refl. Qed.
Lemma D_1b888 : decode_any W_1b888 = Some (Load SZ8 true 10 10 2676, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1b88c : bv 32 := 0x000500a3.
Lemma F_1b88c : fetch_word Plain.M.loaded_segments (0x1b88c : word) = Some W_1b88c.
Proof. vm_refl. Qed.
Lemma D_1b88c : decode_any W_1b88c = Some (Store SZ1 10 0 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1b890 : bv 32 := 0x00053503.
Lemma F_1b890 : fetch_word Plain.M.loaded_segments (0x1b890 : word) = Some W_1b890.
Proof. vm_refl. Qed.
Lemma D_1b890 : decode_any W_1b890 = Some (Load SZ8 true 10 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1b894 : bv 32 := 0x00020593.
Lemma F_1b894 : fetch_word Plain.M.loaded_segments (0x1b894 : word) = Some W_1b894.
Proof. vm_refl. Qed.
Lemma D_1b894 : decode_any W_1b894 = Some (OpImm ALU_ADD 11 4 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1b898 : bv 32 := 0xfea5b823.
Lemma F_1b898 : fetch_word Plain.M.loaded_segments (0x1b898 : word) = Some W_1b898.
Proof. vm_refl. Qed.
Lemma D_1b898 : decode_any W_1b898 = Some (Store SZ8 11 10 4080, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1b89c : bv 32 := 0x00813083.
Lemma F_1b89c : fetch_word Plain.M.loaded_segments (0x1b89c : word) = Some W_1b89c.
Proof. vm_refl. Qed.
Lemma D_1b89c : decode_any W_1b89c = Some (Load SZ8 true 1 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1b8a0 : bv 32 := 0x01010113.
Lemma F_1b8a0 : fetch_word Plain.M.loaded_segments (0x1b8a0 : word) = Some W_1b8a0.
Proof. vm_refl. Qed.
Lemma D_1b8a0 : decode_any W_1b8a0 = Some (OpImm ALU_ADD 2 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1b8a4 : bv 32 := 0x00008067.
Lemma F_1b8a4 : fetch_word Plain.M.loaded_segments (0x1b8a4 : word) = Some W_1b8a4.
Proof. vm_refl. Qed.
Lemma D_1b8a4 : decode_any W_1b8a4 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1b8b0 : bv 32 := 0x00020513.
Lemma F_1b8b0 : fetch_word Plain.M.loaded_segments (0x1b8b0 : word) = Some W_1b8b0.
Proof. vm_refl. Qed.
Lemma D_1b8b0 : decode_any W_1b8b0 = Some (OpImm ALU_ADD 10 4 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1b8b4 : bv 32 := 0xf5c50513.
Lemma F_1b8b4 : fetch_word Plain.M.loaded_segments (0x1b8b4 : word) = Some W_1b8b4.
Proof. vm_refl. Qed.
Lemma D_1b8b4 : decode_any W_1b8b4 = Some (OpImm ALU_ADD 10 10 3932, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1b8b8 : bv 32 := 0x00008067.
Lemma F_1b8b8 : fetch_word Plain.M.loaded_segments (0x1b8b8 : word) = Some W_1b8b8.
Proof. vm_refl. Qed.
Lemma D_1b8b8 : decode_any W_1b8b8 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1b8f8 : bv 32 := 0x00050593.
Lemma F_1b8f8 : fetch_word Plain.M.loaded_segments (0x1b8f8 : word) = Some W_1b8f8.
Proof. vm_refl. Qed.
Lemma D_1b8f8 : decode_any W_1b8f8 = Some (OpImm ALU_ADD 11 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1b8fc : bv 32 := 0x05e00893.
Lemma F_1b8fc : fetch_word Plain.M.loaded_segments (0x1b8fc : word) = Some W_1b8fc.
Proof. vm_refl. Qed.
Lemma D_1b8fc : decode_any W_1b8fc = Some (OpImm ALU_ADD 17 0 94, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1b900 : bv 32 := 0x00000073.
Lemma F_1b900 : fetch_word Plain.M.loaded_segments (0x1b900 : word) = Some W_1b900.
Proof. vm_refl. Qed.
Lemma D_1b900 : decode_any W_1b900 = Some (Ecall, 4%Z).
Proof. vm_refl. Qed.
Lemma E_1b900 : is_ecall W_1b900 = true.
Proof. reflexivity. Qed.

(* [comment removed for export] *)
Definition W_1b914 : bv 32 := 0xfd010113.
Lemma F_1b914 : fetch_word Plain.M.loaded_segments (0x1b914 : word) = Some W_1b914.
Proof. vm_refl. Qed.
Lemma D_1b914 : decode_any W_1b914 = Some (OpImm ALU_ADD 2 2 4048, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1b918 : bv 32 := 0x02113423.
Lemma F_1b918 : fetch_word Plain.M.loaded_segments (0x1b918 : word) = Some W_1b918.
Proof. vm_refl. Qed.
Lemma D_1b918 : decode_any W_1b918 = Some (Store SZ8 2 1 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1b91c : bv 32 := 0x02813023.
Lemma F_1b91c : fetch_word Plain.M.loaded_segments (0x1b91c : word) = Some W_1b91c.
Proof. vm_refl. Qed.
Lemma D_1b91c : decode_any W_1b91c = Some (Store SZ8 2 8 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1b920 : bv 32 := 0x00913c23.
Lemma F_1b920 : fetch_word Plain.M.loaded_segments (0x1b920 : word) = Some W_1b920.
Proof. vm_refl. Qed.
Lemma D_1b920 : decode_any W_1b920 = Some (Store SZ8 2 9 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1b924 : bv 32 := 0x01213823.
Lemma F_1b924 : fetch_word Plain.M.loaded_segments (0x1b924 : word) = Some W_1b924.
Proof. vm_refl. Qed.
Lemma D_1b924 : decode_any W_1b924 = Some (Store SZ8 2 18 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1b928 : bv 32 := 0x01313423.
Lemma F_1b928 : fetch_word Plain.M.loaded_segments (0x1b928 : word) = Some W_1b928.
Proof. vm_refl. Qed.
Lemma D_1b928 : decode_any W_1b928 = Some (Store SZ8 2 19 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1b92c : bv 32 := 0x0003b517.
Lemma F_1b92c : fetch_word Plain.M.loaded_segments (0x1b92c : word) = Some W_1b92c.
Proof. vm_refl. Qed.
Lemma D_1b92c : decode_any W_1b92c = Some (Auipc 10 59, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1b930 : bv 32 := 0xecc50913.
Lemma F_1b930 : fetch_word Plain.M.loaded_segments (0x1b930 : word) = Some W_1b930.
Proof. vm_refl. Qed.
Lemma D_1b930 : decode_any W_1b930 = Some (OpImm ALU_ADD 18 10 3788, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1b934 : bv 32 := 0x00490413.
Lemma F_1b934 : fetch_word Plain.M.loaded_segments (0x1b934 : word) = Some W_1b934.
Proof. vm_refl. Qed.
Lemma D_1b934 : decode_any W_1b934 = Some (OpImm ALU_ADD 8 18 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1b938 : bv 32 := 0x00040513.
Lemma F_1b938 : fetch_word Plain.M.loaded_segments (0x1b938 : word) = Some W_1b938.
Proof. vm_refl. Qed.
Lemma D_1b938 : decode_any W_1b938 = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1b93c : bv 32 := 0x444080ef.
Lemma F_1b93c : fetch_word Plain.M.loaded_segments (0x1b93c : word) = Some W_1b93c.
Proof. vm_refl. Qed.
Lemma D_1b93c : decode_any W_1b93c = Some (Jal 1 33860, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1b940 : bv 32 := 0x01093503.
Lemma F_1b940 : fetch_word Plain.M.loaded_segments (0x1b940 : word) = Some W_1b940.
Proof. vm_refl. Qed.
Lemma D_1b940 : decode_any W_1b940 = Some (Load SZ8 true 10 18 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1b944 : bv 32 := 0x06050863.
Lemma F_1b944 : fetch_word Plain.M.loaded_segments (0x1b944 : word) = Some W_1b944.
Proof. vm_refl. Qed.
Lemma D_1b944 : decode_any W_1b944 = Some (Branch BC_EQ 10 0 112, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1b9b4 : bv 32 := 0x00100513.
Lemma F_1b9b4 : fetch_word Plain.M.loaded_segments (0x1b9b4 : word) = Some W_1b9b4.
Proof. vm_refl. Qed.
Lemma D_1b9b4 : decode_any W_1b9b4 = Some (OpImm ALU_ADD 10 0 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1b9b8 : bv 32 := 0x00a90023.
Lemma F_1b9b8 : fetch_word Plain.M.loaded_segments (0x1b9b8 : word) = Some W_1b9b8.
Proof. vm_refl. Qed.
Lemma D_1b9b8 : decode_any W_1b9b8 = Some (Store SZ1 18 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1b9bc : bv 32 := 0x00040513.
Lemma F_1b9bc : fetch_word Plain.M.loaded_segments (0x1b9bc : word) = Some W_1b9bc.
Proof. vm_refl. Qed.
Lemma D_1b9bc : decode_any W_1b9bc = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1b9c0 : bv 32 := 0x02813083.
Lemma F_1b9c0 : fetch_word Plain.M.loaded_segments (0x1b9c0 : word) = Some W_1b9c0.
Proof. vm_refl. Qed.
Lemma D_1b9c0 : decode_any W_1b9c0 = Some (Load SZ8 true 1 2 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1b9c4 : bv 32 := 0x02013403.
Lemma F_1b9c4 : fetch_word Plain.M.loaded_segments (0x1b9c4 : word) = Some W_1b9c4.
Proof. vm_refl. Qed.
Lemma D_1b9c4 : decode_any W_1b9c4 = Some (Load SZ8 true 8 2 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1b9c8 : bv 32 := 0x01813483.
Lemma F_1b9c8 : fetch_word Plain.M.loaded_segments (0x1b9c8 : word) = Some W_1b9c8.
Proof. vm_refl. Qed.
Lemma D_1b9c8 : decode_any W_1b9c8 = Some (Load SZ8 true 9 2 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1b9cc : bv 32 := 0x01013903.
Lemma F_1b9cc : fetch_word Plain.M.loaded_segments (0x1b9cc : word) = Some W_1b9cc.
Proof. vm_refl. Qed.
Lemma D_1b9cc : decode_any W_1b9cc = Some (Load SZ8 true 18 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1b9d0 : bv 32 := 0x00813983.
Lemma F_1b9d0 : fetch_word Plain.M.loaded_segments (0x1b9d0 : word) = Some W_1b9d0.
Proof. vm_refl. Qed.
Lemma D_1b9d0 : decode_any W_1b9d0 = Some (Load SZ8 true 19 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1b9d4 : bv 32 := 0x03010113.
Lemma F_1b9d4 : fetch_word Plain.M.loaded_segments (0x1b9d4 : word) = Some W_1b9d4.
Proof. vm_refl. Qed.
Lemma D_1b9d4 : decode_any W_1b9d4 = Some (OpImm ALU_ADD 2 2 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1b9d8 : bv 32 := 0x6300806f.
Lemma F_1b9d8 : fetch_word Plain.M.loaded_segments (0x1b9d8 : word) = Some W_1b9d8.
Proof. vm_refl. Qed.
Lemma D_1b9d8 : decode_any W_1b9d8 = Some (Jal 0 34352, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1b9dc : bv 32 := 0x00008067.
Lemma F_1b9dc : fetch_word Plain.M.loaded_segments (0x1b9dc : word) = Some W_1b9dc.
Proof. vm_refl. Qed.
Lemma D_1b9dc : decode_any W_1b9dc = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1baa8 : bv 32 := 0x00008067.
Lemma F_1baa8 : fetch_word Plain.M.loaded_segments (0x1baa8 : word) = Some W_1baa8.
Proof. vm_refl. Qed.
Lemma D_1baa8 : decode_any W_1baa8 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1baac : bv 32 := 0xfe010113.
Lemma F_1baac : fetch_word Plain.M.loaded_segments (0x1baac : word) = Some W_1baac.
Proof. vm_refl. Qed.
Lemma D_1baac : decode_any W_1baac = Some (OpImm ALU_ADD 2 2 4064, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1bab0 : bv 32 := 0x00113c23.
Lemma F_1bab0 : fetch_word Plain.M.loaded_segments (0x1bab0 : word) = Some W_1bab0.
Proof. vm_refl. Qed.
Lemma D_1bab0 : decode_any W_1bab0 = Some (Store SZ8 2 1 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1bab4 : bv 32 := 0x00813823.
Lemma F_1bab4 : fetch_word Plain.M.loaded_segments (0x1bab4 : word) = Some W_1bab4.
Proof. vm_refl. Qed.
Lemma D_1bab4 : decode_any W_1bab4 = Some (Store SZ8 2 8 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1bab8 : bv 32 := 0x00913423.
Lemma F_1bab8 : fetch_word Plain.M.loaded_segments (0x1bab8 : word) = Some W_1bab8.
Proof. vm_refl. Qed.
Lemma D_1bab8 : decode_any W_1bab8 = Some (Store SZ8 2 9 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1babc : bv 32 := 0x0000a517.
Lemma F_1babc : fetch_word Plain.M.loaded_segments (0x1babc : word) = Some W_1babc.
Proof. vm_refl. Qed.
Lemma D_1babc : decode_any W_1babc = Some (Auipc 10 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1bac0 : bv 32 := 0x0000a597.
Lemma F_1bac0 : fetch_word Plain.M.loaded_segments (0x1bac0 : word) = Some W_1bac0.
Proof. vm_refl. Qed.
Lemma D_1bac0 : decode_any W_1bac0 = Some (Auipc 11 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1bac4 : bv 32 := 0x86c53503.
Lemma F_1bac4 : fetch_word Plain.M.loaded_segments (0x1bac4 : word) = Some W_1bac4.
Proof. vm_refl. Qed.
Lemma D_1bac4 : decode_any W_1bac4 = Some (Load SZ8 true 10 10 2156, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1bac8 : bv 32 := 0x8705b403.
Lemma F_1bac8 : fetch_word Plain.M.loaded_segments (0x1bac8 : word) = Some W_1bac8.
Proof. vm_refl. Qed.
Lemma D_1bac8 : decode_any W_1bac8 = Some (Load SZ8 true 8 11 2160, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1bacc : bv 32 := 0x00a47c63.
Lemma F_1bacc : fetch_word Plain.M.loaded_segments (0x1bacc : word) = Some W_1bacc.
Proof. vm_refl. Qed.
Lemma D_1bacc : decode_any W_1bacc = Some (Branch BC_GEU 8 10 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1bad0 : bv 32 := 0xff853583.
Lemma F_1bad0 : fetch_word Plain.M.loaded_segments (0x1bad0 : word) = Some W_1bad0.
Proof. vm_refl. Qed.
Lemma D_1bad0 : decode_any W_1bad0 = Some (Load SZ8 true 11 10 4088, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1bad4 : bv 32 := 0xff850493.
Lemma F_1bad4 : fetch_word Plain.M.loaded_segments (0x1bad4 : word) = Some W_1bad4.
Proof. vm_refl. Qed.
Lemma D_1bad4 : decode_any W_1bad4 = Some (OpImm ALU_ADD 9 10 4088, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1bad8 : bv 32 := 0x000580e7.
Lemma F_1bad8 : fetch_word Plain.M.loaded_segments (0x1bad8 : word) = Some W_1bad8.
Proof. vm_refl. Qed.
Lemma D_1bad8 : decode_any W_1bad8 = Some (Jalr 1 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1badc : bv 32 := 0x00048513.
Lemma F_1badc : fetch_word Plain.M.loaded_segments (0x1badc : word) = Some W_1badc.
Proof. vm_refl. Qed.
Lemma D_1badc : decode_any W_1badc = Some (OpImm ALU_ADD 10 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1bae0 : bv 32 := 0xfe9468e3.
Lemma F_1bae0 : fetch_word Plain.M.loaded_segments (0x1bae0 : word) = Some W_1bae0.
Proof. vm_refl. Qed.
Lemma D_1bae0 : decode_any W_1bae0 = Some (Branch BC_LTU 8 9 8176, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1bae4 : bv 32 := 0x01813083.
Lemma F_1bae4 : fetch_word Plain.M.loaded_segments (0x1bae4 : word) = Some W_1bae4.
Proof. vm_refl. Qed.
Lemma D_1bae4 : decode_any W_1bae4 = Some (Load SZ8 true 1 2 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1bae8 : bv 32 := 0x01013403.
Lemma F_1bae8 : fetch_word Plain.M.loaded_segments (0x1bae8 : word) = Some W_1bae8.
Proof. vm_refl. Qed.
Lemma D_1bae8 : decode_any W_1bae8 = Some (Load SZ8 true 8 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1baec : bv 32 := 0x00813483.
Lemma F_1baec : fetch_word Plain.M.loaded_segments (0x1baec : word) = Some W_1baec.
Proof. vm_refl. Qed.
Lemma D_1baec : decode_any W_1baec = Some (Load SZ8 true 9 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1baf0 : bv 32 := 0x02010113.
Lemma F_1baf0 : fetch_word Plain.M.loaded_segments (0x1baf0 : word) = Some W_1baf0.
Proof. vm_refl. Qed.
Lemma D_1baf0 : decode_any W_1baf0 = Some (OpImm ALU_ADD 2 2 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1baf4 : bv 32 := 0xfb5ff06f.
Lemma F_1baf4 : fetch_word Plain.M.loaded_segments (0x1baf4 : word) = Some W_1baf4.
Proof. vm_refl. Qed.
Lemma D_1baf4 : decode_any W_1baf4 = Some (Jal 0 2097076, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1baf8 : bv 32 := 0xff010113.
Lemma F_1baf8 : fetch_word Plain.M.loaded_segments (0x1baf8 : word) = Some W_1baf8.
Proof. vm_refl. Qed.
Lemma D_1baf8 : decode_any W_1baf8 = Some (OpImm ALU_ADD 2 2 4080, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1bafc : bv 32 := 0x00113423.
Lemma F_1bafc : fetch_word Plain.M.loaded_segments (0x1bafc : word) = Some W_1bafc.
Proof. vm_refl. Qed.
Lemma D_1bafc : decode_any W_1bafc = Some (Store SZ8 2 1 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1bb00 : bv 32 := 0x00813023.
Lemma F_1bb00 : fetch_word Plain.M.loaded_segments (0x1bb00 : word) = Some W_1bb00.
Proof. vm_refl. Qed.
Lemma D_1bb00 : decode_any W_1bb00 = Some (Store SZ8 2 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1bb04 : bv 32 := 0x00000593.
Lemma F_1bb04 : fetch_word Plain.M.loaded_segments (0x1bb04 : word) = Some W_1bb04.
Proof. vm_refl. Qed.
Lemma D_1bb04 : decode_any W_1bb04 = Some (OpImm ALU_ADD 11 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1bb08 : bv 32 := 0x00020613.
Lemma F_1bb08 : fetch_word Plain.M.loaded_segments (0x1bb08 : word) = Some W_1bb08.
Proof. vm_refl. Qed.
Lemma D_1bb08 : decode_any W_1bb08 = Some (OpImm ALU_ADD 12 4 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1bb0c : bv 32 := 0xf5862603.
Lemma F_1bb0c : fetch_word Plain.M.loaded_segments (0x1bb0c : word) = Some W_1bb0c.
Proof. vm_refl. Qed.
Lemma D_1bb0c : decode_any W_1bb0c = Some (Load SZ4 true 12 12 3928, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1bb10 : bv 32 := 0x0003b697.
Lemma F_1bb10 : fetch_word Plain.M.loaded_segments (0x1bb10 : word) = Some W_1bb10.
Proof. vm_refl. Qed.
Lemma D_1bb10 : decode_any W_1bb10 = Some (Auipc 13 59, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1bb14 : bv 32 := 0xf0868693.
Lemma F_1bb14 : fetch_word Plain.M.loaded_segments (0x1bb14 : word) = Some W_1bb14.
Proof. vm_refl. Qed.
Lemma D_1bb14 : decode_any W_1bb14 = Some (OpImm ALU_ADD 13 13 3848, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1bb18 : bv 32 := 0x1606a72f.
Lemma F_1bb18 : fetch_word Plain.M.loaded_segments (0x1bb18 : word) = Some W_1bb18.
Proof. vm_refl. Qed.
Lemma D_1bb18 : decode_any W_1bb18 = Some (Lr AW true true 14 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1bb1c : bv 32 := 0x00b71663.
Lemma F_1bb1c : fetch_word Plain.M.loaded_segments (0x1bb1c : word) = Some W_1bb1c.
Proof. vm_refl. Qed.
Lemma D_1bb1c : decode_any W_1bb1c = Some (Branch BC_NE 14 11 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1bb20 : bv 32 := 0x1ec6a7af.
Lemma F_1bb20 : fetch_word Plain.M.loaded_segments (0x1bb20 : word) = Some W_1bb20.
Proof. vm_refl. Qed.
Lemma D_1bb20 : decode_any W_1bb20 = Some (Sc AW true true 15 13 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1bb24 : bv 32 := 0xfe079ae3.
Lemma F_1bb24 : fetch_word Plain.M.loaded_segments (0x1bb24 : word) = Some W_1bb24.
Proof. vm_refl. Qed.
Lemma D_1bb24 : decode_any W_1bb24 = Some (Branch BC_NE 15 0 8180, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1bb28 : bv 32 := 0x0007059b.
Lemma F_1bb28 : fetch_word Plain.M.loaded_segments (0x1bb28 : word) = Some W_1bb28.
Proof. vm_refl. Qed.
Lemma D_1bb28 : decode_any W_1bb28 = Some (OpImm32 11 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1bb2c : bv 32 := 0x02c58263.
Lemma F_1bb2c : fetch_word Plain.M.loaded_segments (0x1bb2c : word) = Some W_1bb2c.
Proof. vm_refl. Qed.
Lemma D_1bb2c : decode_any W_1bb2c = Some (Branch BC_EQ 11 12 36, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1bb30 : bv 32 := 0x02058263.
Lemma F_1bb30 : fetch_word Plain.M.loaded_segments (0x1bb30 : word) = Some W_1bb30.
Proof. vm_refl. Qed.
Lemma D_1bb30 : decode_any W_1bb30 = Some (Branch BC_EQ 11 0 36, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1bb54 : bv 32 := 0x00050413.
Lemma F_1bb54 : fetch_word Plain.M.loaded_segments (0x1bb54 : word) = Some W_1bb54.
Proof. vm_refl. Qed.
Lemma D_1bb54 : decode_any W_1bb54 = Some (OpImm ALU_ADD 8 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1bb58 : bv 32 := 0xdbdff0ef.
Lemma F_1bb58 : fetch_word Plain.M.loaded_segments (0x1bb58 : word) = Some W_1bb58.
Proof. vm_refl. Qed.
Lemma D_1bb58 : decode_any W_1bb58 = Some (Jal 1 2096572, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1bb5c : bv 32 := 0xf51ff0ef.
Lemma F_1bb5c : fetch_word Plain.M.loaded_segments (0x1bb5c : word) = Some W_1bb5c.
Proof. vm_refl. Qed.
Lemma D_1bb5c : decode_any W_1bb5c = Some (Jal 1 2096976, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1bb60 : bv 32 := 0x224020ef.
Lemma F_1bb60 : fetch_word Plain.M.loaded_segments (0x1bb60 : word) = Some W_1bb60.
Proof. vm_refl. Qed.
Lemma D_1bb60 : decode_any W_1bb60 = Some (Jal 1 8740, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1bb64 : bv 32 := 0x00040513.
Lemma F_1bb64 : fetch_word Plain.M.loaded_segments (0x1bb64 : word) = Some W_1bb64.
Proof. vm_refl. Qed.
Lemma D_1bb64 : decode_any W_1bb64 = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1bb68 : bv 32 := 0xd91ff0ef.
Lemma F_1bb68 : fetch_word Plain.M.loaded_segments (0x1bb68 : word) = Some W_1bb68.
Proof. vm_refl. Qed.
Lemma D_1bb68 : decode_any W_1bb68 = Some (Jal 1 2096528, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1bc50 : bv 32 := 0xfffff5b7.
Lemma F_1bc50 : fetch_word Plain.M.loaded_segments (0x1bc50 : word) = Some W_1bc50.
Proof. vm_refl. Qed.
Lemma D_1bc50 : decode_any W_1bc50 = Some (Lui 11 1048575, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1bc54 : bv 32 := 0x0015859b.
Lemma F_1bc54 : fetch_word Plain.M.loaded_segments (0x1bc54 : word) = Some W_1bc54.
Proof. vm_refl. Qed.
Lemma D_1bc54 : decode_any W_1bc54 = Some (OpImm32 11 11 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1bc58 : bv 32 := 0x02b56663.
Lemma F_1bc58 : fetch_word Plain.M.loaded_segments (0x1bc58 : word) = Some W_1bc58.
Proof. vm_refl. Qed.
Lemma D_1bc58 : decode_any W_1bc58 = Some (Branch BC_LTU 10 11 44, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1bc84 : bv 32 := 0x00008067.
Lemma F_1bc84 : fetch_word Plain.M.loaded_segments (0x1bc84 : word) = Some W_1bc84.
Proof. vm_refl. Qed.
Lemma D_1bc84 : decode_any W_1bc84 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1bdd4 : bv 32 := 0x1c050463.
Lemma F_1bdd4 : fetch_word Plain.M.loaded_segments (0x1bdd4 : word) = Some W_1bdd4.
Proof. vm_refl. Qed.
Lemma D_1bdd4 : decode_any W_1bdd4 = Some (Branch BC_EQ 10 0 456, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1bdd8 : bv 32 := 0xfd010113.
Lemma F_1bdd8 : fetch_word Plain.M.loaded_segments (0x1bdd8 : word) = Some W_1bdd8.
Proof. vm_refl. Qed.
Lemma D_1bdd8 : decode_any W_1bdd8 = Some (OpImm ALU_ADD 2 2 4048, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1bddc : bv 32 := 0x02113423.
Lemma F_1bddc : fetch_word Plain.M.loaded_segments (0x1bddc : word) = Some W_1bddc.
Proof. vm_refl. Qed.
Lemma D_1bddc : decode_any W_1bddc = Some (Store SZ8 2 1 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1bde0 : bv 32 := 0x02813023.
Lemma F_1bde0 : fetch_word Plain.M.loaded_segments (0x1bde0 : word) = Some W_1bde0.
Proof. vm_refl. Qed.
Lemma D_1bde0 : decode_any W_1bde0 = Some (Store SZ8 2 8 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1bde4 : bv 32 := 0x00913c23.
Lemma F_1bde4 : fetch_word Plain.M.loaded_segments (0x1bde4 : word) = Some W_1bde4.
Proof. vm_refl. Qed.
Lemma D_1bde4 : decode_any W_1bde4 = Some (Store SZ8 2 9 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1bde8 : bv 32 := 0x01213823.
Lemma F_1bde8 : fetch_word Plain.M.loaded_segments (0x1bde8 : word) = Some W_1bde8.
Proof. vm_refl. Qed.
Lemma D_1bde8 : decode_any W_1bde8 = Some (Store SZ8 2 18 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1bdec : bv 32 := 0x01313423.
Lemma F_1bdec : fetch_word Plain.M.loaded_segments (0x1bdec : word) = Some W_1bdec.
Proof. vm_refl. Qed.
Lemma D_1bdec : decode_any W_1bdec = Some (Store SZ8 2 19 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1bdf0 : bv 32 := 0x00050493.
Lemma F_1bdf0 : fetch_word Plain.M.loaded_segments (0x1bdf0 : word) = Some W_1bdf0.
Proof. vm_refl. Qed.
Lemma D_1bdf0 : decode_any W_1bdf0 = Some (OpImm ALU_ADD 9 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1bdf4 : bv 32 := 0x1ac000ef.
Lemma F_1bdf4 : fetch_word Plain.M.loaded_segments (0x1bdf4 : word) = Some W_1bdf4.
Proof. vm_refl. Qed.
Lemma D_1bdf4 : decode_any W_1bdf4 = Some (Jal 1 428, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1bdf8 : bv 32 := 0x02053583.
Lemma F_1bdf8 : fetch_word Plain.M.loaded_segments (0x1bdf8 : word) = Some W_1bdf8.
Proof. vm_refl. Qed.
Lemma D_1bdf8 : decode_any W_1bdf8 = Some (Load SZ8 true 11 10 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1bdfc : bv 32 := 0xffd4c683.
Lemma F_1bdfc : fetch_word Plain.M.loaded_segments (0x1bdfc : word) = Some W_1bdfc.
Proof. vm_refl. Qed.
Lemma D_1bdfc : decode_any W_1bdfc = Some (Load SZ1 false 13 9 4093, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1be00 : bv 32 := 0x00c5d613.
Lemma F_1be00 : fetch_word Plain.M.loaded_segments (0x1be00 : word) = Some W_1be00.
Proof. vm_refl. Qed.
Lemma D_1be00 : decode_any W_1be00 = Some (ShiftImm ALU_SRL 12 11 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1be04 : bv 32 := 0x01f6f413.
Lemma F_1be04 : fetch_word Plain.M.loaded_segments (0x1be04 : word) = Some W_1be04.
Proof. vm_refl. Qed.
Lemma D_1be04 : decode_any W_1be04 = Some (OpImm ALU_AND 8 13 31, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1be08 : bv 32 := 0x00060e63.
Lemma F_1be08 : fetch_word Plain.M.loaded_segments (0x1be08 : word) = Some W_1be08.
Proof. vm_refl. Qed.
Lemma D_1be08 : decode_any W_1be08 = Some (Branch BC_EQ 12 0 28, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1be0c : bv 32 := 0x01f5f613.
Lemma F_1be0c : fetch_word Plain.M.loaded_segments (0x1be0c : word) = Some W_1be0c.
Proof. vm_refl. Qed.
Lemma D_1be0c : decode_any W_1be0c = Some (OpImm ALU_AND 12 11 31, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1be10 : bv 32 := 0x00061a63.
Lemma F_1be10 : fetch_word Plain.M.loaded_segments (0x1be10 : word) = Some W_1be10.
Proof. vm_refl. Qed.
Lemma D_1be10 : decode_any W_1be10 = Some (Branch BC_NE 12 0 20, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1be14 : bv 32 := 0xfffff637.
Lemma F_1be14 : fetch_word Plain.M.loaded_segments (0x1be14 : word) = Some W_1be14.
Proof. vm_refl. Qed.
Lemma D_1be14 : decode_any W_1be14 = Some (Lui 12 1048575, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1be18 : bv 32 := 0x00c5f633.
Lemma F_1be18 : fetch_word Plain.M.loaded_segments (0x1be18 : word) = Some W_1be18.
Proof. vm_refl. Qed.
Lemma D_1be18 : decode_any W_1be18 = Some (Op ALU_AND 12 11 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1be1c : bv 32 := 0xff060613.
Lemma F_1be1c : fetch_word Plain.M.loaded_segments (0x1be1c : word) = Some W_1be1c.
Proof. vm_refl. Qed.
Lemma D_1be1c : decode_any W_1be1c = Some (OpImm ALU_ADD 12 12 4080, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1be20 : bv 32 := 0x0200006f.
Lemma F_1be20 : fetch_word Plain.M.loaded_segments (0x1be20 : word) = Some W_1be20.
Proof. vm_refl. Qed.
Lemma D_1be20 : decode_any W_1be20 = Some (Jal 0 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1be24 : bv 32 := 0x0055d613.
Lemma F_1be24 : fetch_word Plain.M.loaded_segments (0x1be24 : word) = Some W_1be24.
Proof. vm_refl. Qed.
Lemma D_1be24 : decode_any W_1be24 = Some (ShiftImm ALU_SRL 12 11 5, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1be28 : bv 32 := 0xffff5717.
Lemma F_1be28 : fetch_word Plain.M.loaded_segments (0x1be28 : word) = Some W_1be28.
Proof. vm_refl. Qed.
Lemma D_1be28 : decode_any W_1be28 = Some (Auipc 14 1048565, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1be2c : bv 32 := 0x07e67613.
Lemma F_1be2c : fetch_word Plain.M.loaded_segments (0x1be2c : word) = Some W_1be2c.
Proof. vm_refl. Qed.
Lemma D_1be2c : decode_any W_1be2c = Some (OpImm ALU_AND 12 12 126, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1be30 : bv 32 := 0x29870713.
Lemma F_1be30 : fetch_word Plain.M.loaded_segments (0x1be30 : word) = Some W_1be30.
Proof. vm_refl. Qed.
Lemma D_1be30 : decode_any W_1be30 = Some (OpImm ALU_ADD 14 14 664, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1be34 : bv 32 := 0x00c70633.
Lemma F_1be34 : fetch_word Plain.M.loaded_segments (0x1be34 : word) = Some W_1be34.
Proof. vm_refl. Qed.
Lemma D_1be34 : decode_any W_1be34 = Some (Op ALU_ADD 12 14 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1be38 : bv 32 := 0x00065603.
Lemma F_1be38 : fetch_word Plain.M.loaded_segments (0x1be38 : word) = Some W_1be38.
Proof. vm_refl. Qed.
Lemma D_1be38 : decode_any W_1be38 = Some (Load SZ2 false 12 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1be3c : bv 32 := 0x00461613.
Lemma F_1be3c : fetch_word Plain.M.loaded_segments (0x1be3c : word) = Some W_1be3c.
Proof. vm_refl. Qed.
Lemma D_1be3c : decode_any W_1be3c = Some (ShiftImm ALU_SLL 12 12 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1be40 : bv 32 := 0x01053703.
Lemma F_1be40 : fetch_word Plain.M.loaded_segments (0x1be40 : word) = Some W_1be40.
Proof. vm_refl. Qed.
Lemma D_1be40 : decode_any W_1be40 = Some (Load SZ8 true 14 10 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1be44 : bv 32 := 0x028607b3.
Lemma F_1be44 : fetch_word Plain.M.loaded_segments (0x1be44 : word) = Some W_1be44.
Proof. vm_refl. Qed.
Lemma D_1be44 : decode_any W_1be44 = Some (Mul M_MUL 15 12 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1be48 : bv 32 := 0x0a000813.
Lemma F_1be48 : fetch_word Plain.M.loaded_segments (0x1be48 : word) = Some W_1be48.
Proof. vm_refl. Qed.
Lemma D_1be48 : decode_any W_1be48 = Some (OpImm ALU_ADD 16 0 160, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1be4c : bv 32 := 0x00c70633.
Lemma F_1be4c : fetch_word Plain.M.loaded_segments (0x1be4c : word) = Some W_1be4c.
Proof. vm_refl. Qed.
Lemma D_1be4c : decode_any W_1be4c = Some (Op ALU_ADD 12 14 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1be50 : bv 32 := 0x00f607b3.
Lemma F_1be50 : fetch_word Plain.M.loaded_segments (0x1be50 : word) = Some W_1be50.
Proof. vm_refl. Qed.
Lemma D_1be50 : decode_any W_1be50 = Some (Op ALU_ADD 15 12 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1be54 : bv 32 := 0x00c78613.
Lemma F_1be54 : fetch_word Plain.M.loaded_segments (0x1be54 : word) = Some W_1be54.
Proof. vm_refl. Qed.
Lemma D_1be54 : decode_any W_1be54 = Some (OpImm ALU_ADD 12 15 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1be58 : bv 32 := 0x0056d713.
Lemma F_1be58 : fetch_word Plain.M.loaded_segments (0x1be58 : word) = Some W_1be58.
Proof. vm_refl. Qed.
Lemma D_1be58 : decode_any W_1be58 = Some (ShiftImm ALU_SRL 14 13 5, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1be5c : bv 32 := 0x0306e663.
Lemma F_1be5c : fetch_word Plain.M.loaded_segments (0x1be5c : word) = Some W_1be5c.
Proof. vm_refl. Qed.
Lemma D_1be5c : decode_any W_1be5c = Some (Branch BC_LTU 13 16 44, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1be60 : bv 32 := 0x00500693.
Lemma F_1be60 : fetch_word Plain.M.loaded_segments (0x1be60 : word) = Some W_1be60.
Proof. vm_refl. Qed.
Lemma D_1be60 : decode_any W_1be60 = Some (OpImm ALU_ADD 13 0 5, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1be64 : bv 32 := 0x00d70463.
Lemma F_1be64 : fetch_word Plain.M.loaded_segments (0x1be64 : word) = Some W_1be64.
Proof. vm_refl. Qed.
Lemma D_1be64 : decode_any W_1be64 = Some (Branch BC_EQ 14 13 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1be6c : bv 32 := 0x0087e703.
Lemma F_1be6c : fetch_word Plain.M.loaded_segments (0x1be6c : word) = Some W_1be6c.
Proof. vm_refl. Qed.
Lemma D_1be6c : decode_any W_1be6c = Some (Load SZ4 false 14 15 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1be70 : bv 32 := 0x00400693.
Lemma F_1be70 : fetch_word Plain.M.loaded_segments (0x1be70 : word) = Some W_1be70.
Proof. vm_refl. Qed.
Lemma D_1be70 : decode_any W_1be70 = Some (OpImm ALU_ADD 13 0 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1be74 : bv 32 := 0x00e6e463.
Lemma F_1be74 : fetch_word Plain.M.loaded_segments (0x1be74 : word) = Some W_1be74.
Proof. vm_refl. Qed.
Lemma D_1be74 : decode_any W_1be74 = Some (Branch BC_LTU 13 14 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1be7c : bv 32 := 0x0077c683.
Lemma F_1be7c : fetch_word Plain.M.loaded_segments (0x1be7c : word) = Some W_1be7c.
Proof. vm_refl. Qed.
Lemma D_1be7c : decode_any W_1be7c = Some (Load SZ1 false 13 15 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1be80 : bv 32 := 0x00068463.
Lemma F_1be80 : fetch_word Plain.M.loaded_segments (0x1be80 : word) = Some W_1be80.
Proof. vm_refl. Qed.
Lemma D_1be80 : decode_any W_1be80 = Some (Branch BC_EQ 13 0 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1be88 : bv 32 := 0x409606b3.
Lemma F_1be88 : fetch_word Plain.M.loaded_segments (0x1be88 : word) = Some W_1be88.
Proof. vm_refl. Qed.
Lemma D_1be88 : decode_any W_1be88 = Some (Op ALU_SUB 13 12 9, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1be8c : bv 32 := 0x00e6f463.
Lemma F_1be8c : fetch_word Plain.M.loaded_segments (0x1be8c : word) = Some W_1be8c.
Proof. vm_refl. Qed.
Lemma D_1be8c : decode_any W_1be8c = Some (Branch BC_GEU 13 14 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1be94 : bv 32 := 0x40e606b3.
Lemma F_1be94 : fetch_word Plain.M.loaded_segments (0x1be94 : word) = Some W_1be94.
Proof. vm_refl. Qed.
Lemma D_1be94 : decode_any W_1be94 = Some (Op ALU_SUB 13 12 14, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1be98 : bv 32 := 0x0006c683.
Lemma F_1be98 : fetch_word Plain.M.loaded_segments (0x1be98 : word) = Some W_1be98.
Proof. vm_refl. Qed.
Lemma D_1be98 : decode_any W_1be98 = Some (Load SZ1 false 13 13 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1be9c : bv 32 := 0x00068463.
Lemma F_1be9c : fetch_word Plain.M.loaded_segments (0x1be9c : word) = Some W_1be9c.
Proof. vm_refl. Qed.
Lemma D_1be9c : decode_any W_1be9c = Some (Branch BC_EQ 13 0 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1bea4 : bv 32 := 0x00064603.
Lemma F_1bea4 : fetch_word Plain.M.loaded_segments (0x1bea4 : word) = Some W_1bea4.
Proof. vm_refl. Qed.
Lemma D_1bea4 : decode_any W_1bea4 = Some (Load SZ1 false 12 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1bea8 : bv 32 := 0x00060463.
Lemma F_1bea8 : fetch_word Plain.M.loaded_segments (0x1bea8 : word) = Some W_1bea8.
Proof. vm_refl. Qed.
Lemma D_1bea8 : decode_any W_1bea8 = Some (Branch BC_EQ 12 0 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1bfa0 : bv 32 := 0x00f57593.
Lemma F_1bfa0 : fetch_word Plain.M.loaded_segments (0x1bfa0 : word) = Some W_1bfa0.
Proof. vm_refl. Qed.
Lemma D_1bfa0 : decode_any W_1bfa0 = Some (OpImm ALU_AND 11 10 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1bfa4 : bv 32 := 0x00058463.
Lemma F_1bfa4 : fetch_word Plain.M.loaded_segments (0x1bfa4 : word) = Some W_1bfa4.
Proof. vm_refl. Qed.
Lemma D_1bfa4 : decode_any W_1bfa4 = Some (Branch BC_EQ 11 0 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1bfac : bv 32 := 0xffc54603.
Lemma F_1bfac : fetch_word Plain.M.loaded_segments (0x1bfac : word) = Some W_1bfac.
Proof. vm_refl. Qed.
Lemma D_1bfac : decode_any W_1bfac = Some (Load SZ1 false 12 10 4092, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1bfb0 : bv 32 := 0xffd54683.
Lemma F_1bfb0 : fetch_word Plain.M.loaded_segments (0x1bfb0 : word) = Some W_1bfb0.
Proof. vm_refl. Qed.
Lemma D_1bfb0 : decode_any W_1bfb0 = Some (Load SZ1 false 13 10 4093, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1bfb4 : bv 32 := 0xffe55583.
Lemma F_1bfb4 : fetch_word Plain.M.loaded_segments (0x1bfb4 : word) = Some W_1bfb4.
Proof. vm_refl. Qed.
Lemma D_1bfb4 : decode_any W_1bfb4 = Some (Load SZ2 false 11 10 4094, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1bfb8 : bv 32 := 0x00060e63.
Lemma F_1bfb8 : fetch_word Plain.M.loaded_segments (0x1bfb8 : word) = Some W_1bfb8.
Proof. vm_refl. Qed.
Lemma D_1bfb8 : decode_any W_1bfb8 = Some (Branch BC_EQ 12 0 28, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1bfd4 : bv 32 := 0x00459613.
Lemma F_1bfd4 : fetch_word Plain.M.loaded_segments (0x1bfd4 : word) = Some W_1bfd4.
Proof. vm_refl. Qed.
Lemma D_1bfd4 : decode_any W_1bfd4 = Some (ShiftImm ALU_SLL 12 11 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1bfd8 : bv 32 := 0x40c50633.
Lemma F_1bfd8 : fetch_word Plain.M.loaded_segments (0x1bfd8 : word) = Some W_1bfd8.
Proof. vm_refl. Qed.
Lemma D_1bfd8 : decode_any W_1bfd8 = Some (Op ALU_SUB 12 10 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1bfdc : bv 32 := 0xff063503.
Lemma F_1bfdc : fetch_word Plain.M.loaded_segments (0x1bfdc : word) = Some W_1bfdc.
Proof. vm_refl. Qed.
Lemma D_1bfdc : decode_any W_1bfdc = Some (Load SZ8 true 10 12 4080, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1bfe0 : bv 32 := 0x01053703.
Lemma F_1bfe0 : fetch_word Plain.M.loaded_segments (0x1bfe0 : word) = Some W_1bfe0.
Proof. vm_refl. Qed.
Lemma D_1bfe0 : decode_any W_1bfe0 = Some (Load SZ8 true 14 10 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1bfe4 : bv 32 := 0xff060613.
Lemma F_1bfe4 : fetch_word Plain.M.loaded_segments (0x1bfe4 : word) = Some W_1bfe4.
Proof. vm_refl. Qed.
Lemma D_1bfe4 : decode_any W_1bfe4 = Some (OpImm ALU_ADD 12 12 4080, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1bfe8 : bv 32 := 0x01f6f693.
Lemma F_1bfe8 : fetch_word Plain.M.loaded_segments (0x1bfe8 : word) = Some W_1bfe8.
Proof. vm_refl. Qed.
Lemma D_1bfe8 : decode_any W_1bfe8 = Some (OpImm ALU_AND 13 13 31, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1bfec : bv 32 := 0x00c70463.
Lemma F_1bfec : fetch_word Plain.M.loaded_segments (0x1bfec : word) = Some W_1bfec.
Proof. vm_refl. Qed.
Lemma D_1bfec : decode_any W_1bfec = Some (Branch BC_EQ 14 12 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1bff4 : bv 32 := 0x02053603.
Lemma F_1bff4 : fetch_word Plain.M.loaded_segments (0x1bff4 : word) = Some W_1bff4.
Proof. vm_refl. Qed.
Lemma D_1bff4 : decode_any W_1bff4 = Some (Load SZ8 true 12 10 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1bff8 : bv 32 := 0x01f67713.
Lemma F_1bff8 : fetch_word Plain.M.loaded_segments (0x1bff8 : word) = Some W_1bff8.
Proof. vm_refl. Qed.
Lemma D_1bff8 : decode_any W_1bff8 = Some (OpImm ALU_AND 14 12 31, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1bffc : bv 32 := 0x00d77463.
Lemma F_1bffc : fetch_word Plain.M.loaded_segments (0x1bffc : word) = Some W_1bffc.
Proof. vm_refl. Qed.
Lemma D_1bffc : decode_any W_1bffc = Some (Branch BC_GEU 14 13 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1c004 : bv 32 := 0x01852783.
Lemma F_1c004 : fetch_word Plain.M.loaded_segments (0x1c004 : word) = Some W_1c004.
Proof. vm_refl. Qed.
Lemma D_1c004 : decode_any W_1c004 = Some (Load SZ4 true 15 10 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1c008 : bv 32 := 0x00100713.
Lemma F_1c008 : fetch_word Plain.M.loaded_segments (0x1c008 : word) = Some W_1c008.
Proof. vm_refl. Qed.
Lemma D_1c008 : decode_any W_1c008 = Some (OpImm ALU_ADD 14 0 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1c00c : bv 32 := 0x00d7173b.
Lemma F_1c00c : fetch_word Plain.M.loaded_segments (0x1c00c : word) = Some W_1c00c.
Proof. vm_refl. Qed.
Lemma D_1c00c : decode_any W_1c00c = Some (Op32 ALU_SLL 14 14 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1c010 : bv 32 := 0x00e7f7b3.
Lemma F_1c010 : fetch_word Plain.M.loaded_segments (0x1c010 : word) = Some W_1c010.
Proof. vm_refl. Qed.
Lemma D_1c010 : decode_any W_1c010 = Some (Op ALU_AND 15 15 14, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1c014 : bv 32 := 0x00078463.
Lemma F_1c014 : fetch_word Plain.M.loaded_segments (0x1c014 : word) = Some W_1c014.
Proof. vm_refl. Qed.
Lemma D_1c014 : decode_any W_1c014 = Some (Branch BC_EQ 15 0 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1c01c : bv 32 := 0x01c52783.
Lemma F_1c01c : fetch_word Plain.M.loaded_segments (0x1c01c : word) = Some W_1c01c.
Proof. vm_refl. Qed.
Lemma D_1c01c : decode_any W_1c01c = Some (Load SZ4 true 15 10 28, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1c020 : bv 32 := 0x00e7f733.
Lemma F_1c020 : fetch_word Plain.M.loaded_segments (0x1c020 : word) = Some W_1c020.
Proof. vm_refl. Qed.
Lemma D_1c020 : decode_any W_1c020 = Some (Op ALU_AND 14 15 14, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1c024 : bv 32 := 0x00070463.
Lemma F_1c024 : fetch_word Plain.M.loaded_segments (0x1c024 : word) = Some W_1c024.
Proof. vm_refl. Qed.
Lemma D_1c024 : decode_any W_1c024 = Some (Branch BC_EQ 14 0 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1c02c : bv 32 := 0xfffff737.
Lemma F_1c02c : fetch_word Plain.M.loaded_segments (0x1c02c : word) = Some W_1c02c.
Proof. vm_refl. Qed.
Lemma D_1c02c : decode_any W_1c02c = Some (Lui 14 1048575, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1c030 : bv 32 := 0x0003b797.
Lemma F_1c030 : fetch_word Plain.M.loaded_segments (0x1c030 : word) = Some W_1c030.
Proof. vm_refl. Qed.
Lemma D_1c030 : decode_any W_1c030 = Some (Auipc 15 59, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1c034 : bv 32 := 0x00e57733.
Lemma F_1c034 : fetch_word Plain.M.loaded_segments (0x1c034 : word) = Some W_1c034.
Proof. vm_refl. Qed.
Lemma D_1c034 : decode_any W_1c034 = Some (Op ALU_AND 14 10 14, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1c038 : bv 32 := 0x00073703.
Lemma F_1c038 : fetch_word Plain.M.loaded_segments (0x1c038 : word) = Some W_1c038.
Proof. vm_refl. Qed.
Lemma D_1c038 : decode_any W_1c038 = Some (Load SZ8 true 14 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1c03c : bv 32 := 0xa807b783.
Lemma F_1c03c : fetch_word Plain.M.loaded_segments (0x1c03c : word) = Some W_1c03c.
Proof. vm_refl. Qed.
Lemma D_1c03c : decode_any W_1c03c = Some (Load SZ8 true 15 15 2688, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1c040 : bv 32 := 0x00f70463.
Lemma F_1c040 : fetch_word Plain.M.loaded_segments (0x1c040 : word) = Some W_1c040.
Proof. vm_refl. Qed.
Lemma D_1c040 : decode_any W_1c040 = Some (Branch BC_EQ 14 15 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1c048 : bv 32 := 0x03461713.
Lemma F_1c048 : fetch_word Plain.M.loaded_segments (0x1c048 : word) = Some W_1c048.
Proof. vm_refl. Qed.
Lemma D_1c048 : decode_any W_1c048 = Some (ShiftImm ALU_SLL 14 12 52, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1c04c : bv 32 := 0x03a75713.
Lemma F_1c04c : fetch_word Plain.M.loaded_segments (0x1c04c : word) = Some W_1c04c.
Proof. vm_refl. Qed.
Lemma D_1c04c : decode_any W_1c04c = Some (ShiftImm ALU_SRL 14 14 58, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1c050 : bv 32 := 0x02f00793.
Lemma F_1c050 : fetch_word Plain.M.loaded_segments (0x1c050 : word) = Some W_1c050.
Proof. vm_refl. Qed.
Lemma D_1c050 : decode_any W_1c050 = Some (OpImm ALU_ADD 15 0 47, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1c054 : bv 32 := 0x02e7ea63.
Lemma F_1c054 : fetch_word Plain.M.loaded_segments (0x1c054 : word) = Some W_1c054.
Proof. vm_refl. Qed.
Lemma D_1c054 : decode_any W_1c054 = Some (Branch BC_LTU 15 14 52, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1c058 : bv 32 := 0x00171713.
Lemma F_1c058 : fetch_word Plain.M.loaded_segments (0x1c058 : word) = Some W_1c058.
Proof. vm_refl. Qed.
Lemma D_1c058 : decode_any W_1c058 = Some (ShiftImm ALU_SLL 14 14 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1c05c : bv 32 := 0xffff5797.
Lemma F_1c05c : fetch_word Plain.M.loaded_segments (0x1c05c : word) = Some W_1c05c.
Proof. vm_refl. Qed.
Lemma D_1c05c : decode_any W_1c05c = Some (Auipc 15 1048565, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1c060 : bv 32 := 0x06478793.
Lemma F_1c060 : fetch_word Plain.M.loaded_segments (0x1c060 : word) = Some W_1c060.
Proof. vm_refl. Qed.
Lemma D_1c060 : decode_any W_1c060 = Some (OpImm ALU_ADD 15 15 100, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1c064 : bv 32 := 0x00e78733.
Lemma F_1c064 : fetch_word Plain.M.loaded_segments (0x1c064 : word) = Some W_1c064.
Proof. vm_refl. Qed.
Lemma D_1c064 : decode_any W_1c064 = Some (Op ALU_ADD 14 15 14, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1c068 : bv 32 := 0x00075703.
Lemma F_1c068 : fetch_word Plain.M.loaded_segments (0x1c068 : word) = Some W_1c068.
Proof. vm_refl. Qed.
Lemma D_1c068 : decode_any W_1c068 = Some (Load SZ2 false 14 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1c06c : bv 32 := 0x02d707b3.
Lemma F_1c06c : fetch_word Plain.M.loaded_segments (0x1c06c : word) = Some W_1c06c.
Proof. vm_refl. Qed.
Lemma D_1c06c : decode_any W_1c06c = Some (Mul M_MUL 15 14 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1c070 : bv 32 := 0x00f5f463.
Lemma F_1c070 : fetch_word Plain.M.loaded_segments (0x1c070 : word) = Some W_1c070.
Proof. vm_refl. Qed.
Lemma D_1c070 : decode_any W_1c070 = Some (Branch BC_GEU 11 15 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1c078 : bv 32 := 0x00168693.
Lemma F_1c078 : fetch_word Plain.M.loaded_segments (0x1c078 : word) = Some W_1c078.
Proof. vm_refl. Qed.
Lemma D_1c078 : decode_any W_1c078 = Some (OpImm ALU_ADD 13 13 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1c07c : bv 32 := 0x02e686b3.
Lemma F_1c07c : fetch_word Plain.M.loaded_segments (0x1c07c : word) = Some W_1c07c.
Proof. vm_refl. Qed.
Lemma D_1c07c : decode_any W_1c07c = Some (Mul M_MUL 13 13 14, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1c080 : bv 32 := 0x00d5f863.
Lemma F_1c080 : fetch_word Plain.M.loaded_segments (0x1c080 : word) = Some W_1c080.
Proof. vm_refl. Qed.
Lemma D_1c080 : decode_any W_1c080 = Some (Branch BC_GEU 11 13 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1c084 : bv 32 := 0x0100006f.
Lemma F_1c084 : fetch_word Plain.M.loaded_segments (0x1c084 : word) = Some W_1c084.
Proof. vm_refl. Qed.
Lemma D_1c084 : decode_any W_1c084 = Some (Jal 0 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1c088 : bv 32 := 0x03f00693.
Lemma F_1c088 : fetch_word Plain.M.loaded_segments (0x1c088 : word) = Some W_1c088.
Proof. vm_refl. Qed.
Lemma D_1c088 : decode_any W_1c088 = Some (OpImm ALU_ADD 13 0 63, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1c08c : bv 32 := 0x00d70463.
Lemma F_1c08c : fetch_word Plain.M.loaded_segments (0x1c08c : word) = Some W_1c08c.
Proof. vm_refl. Qed.
Lemma D_1c08c : decode_any W_1c08c = Some (Branch BC_EQ 14 13 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1c094 : bv 32 := 0x00c65613.
Lemma F_1c094 : fetch_word Plain.M.loaded_segments (0x1c094 : word) = Some W_1c094.
Proof. vm_refl. Qed.
Lemma D_1c094 : decode_any W_1c094 = Some (ShiftImm ALU_SRL 12 12 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1c098 : bv 32 := 0x00060a63.
Lemma F_1c098 : fetch_word Plain.M.loaded_segments (0x1c098 : word) = Some W_1c098.
Proof. vm_refl. Qed.
Lemma D_1c098 : decode_any W_1c098 = Some (Branch BC_EQ 12 0 20, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1c09c : bv 32 := 0x00861613.
Lemma F_1c09c : fetch_word Plain.M.loaded_segments (0x1c09c : word) = Some W_1c09c.
Proof. vm_refl. Qed.
Lemma D_1c09c : decode_any W_1c09c = Some (ShiftImm ALU_SLL 12 12 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1c0a0 : bv 32 := 0xfff60613.
Lemma F_1c0a0 : fetch_word Plain.M.loaded_segments (0x1c0a0 : word) = Some W_1c0a0.
Proof. vm_refl. Qed.
Lemma D_1c0a0 : decode_any W_1c0a0 = Some (OpImm ALU_ADD 12 12 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1c0a4 : bv 32 := 0x00b67463.
Lemma F_1c0a4 : fetch_word Plain.M.loaded_segments (0x1c0a4 : word) = Some W_1c0a4.
Proof. vm_refl. Qed.
Lemma D_1c0a4 : decode_any W_1c0a4 = Some (Branch BC_GEU 12 11 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1c0ac : bv 32 := 0x00008067.
Lemma F_1c0ac : fetch_word Plain.M.loaded_segments (0x1c0ac : word) = Some W_1c0ac.
Proof. vm_refl. Qed.
Lemma D_1c0ac : decode_any W_1c0ac = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.
