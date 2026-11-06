(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
(* [comment removed for export] *)

From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.H Require GcFlushS23.   (* [comment removed for export] *)
From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.leptonica.pix_orient_fuzzer.images Require Import Plain.
Open Scope bv_scope.

(* [comment removed for export] *)
Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

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
Definition W_6d4a4 : bv 32 := 0x000a5517.
Lemma F_6d4a4 : fetch_word Plain.M.loaded_segments (0x6d4fc : word) = Some W_6d4a4.
Proof. vm_refl. Qed.
Lemma D_6d4a4 : decode_any W_6d4a4 = Some (Auipc 10 165, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6d4a8 : bv 32 := 0x0cc53503.
Lemma F_6d4a8 : fetch_word Plain.M.loaded_segments (0x6d500 : word) = Some W_6d4a8.
Proof. vm_refl. Qed.
Lemma D_6d4a8 : decode_any W_6d4a8 = Some (Load SZ8 true 10 10 204, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6d4ac : bv 32 := 0x00052503.
Lemma F_6d4ac : fetch_word Plain.M.loaded_segments (0x6d504 : word) = Some W_6d4ac.
Proof. vm_refl. Qed.
Lemma D_6d4ac : decode_any W_6d4ac = Some (Load SZ4 true 10 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6d4b0 : bv 32 := 0x00500593.
Lemma F_6d4b0 : fetch_word Plain.M.loaded_segments (0x6d508 : word) = Some W_6d4b0.
Proof. vm_refl. Qed.
Lemma D_6d4b0 : decode_any W_6d4b0 = Some (OpImm ALU_ADD 11 0 5, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6d4b4 : bv 32 := 0x12a5ca63.
Lemma F_6d4b4 : fetch_word Plain.M.loaded_segments (0x6d50c : word) = Some W_6d4b4.
Proof. vm_refl. Qed.
Lemma D_6d4b4 : decode_any W_6d4b4 = Some (Branch BC_LT 11 10 308, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6d4b8 : bv 32 := 0xfffa3517.
Lemma F_6d4b8 : fetch_word Plain.M.loaded_segments (0x6d510 : word) = Some W_6d4b8.
Proof. vm_refl. Qed.
Lemma D_6d4b8 : decode_any W_6d4b8 = Some (Auipc 10 1048483, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6d4bc : bv 32 := 0xfffab597.
Lemma F_6d4bc : fetch_word Plain.M.loaded_segments (0x6d514 : word) = Some W_6d4bc.
Proof. vm_refl. Qed.
Lemma D_6d4bc : decode_any W_6d4bc = Some (Auipc 11 1048491, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6d4c0 : bv 32 := 0xe4550513.
Lemma F_6d4c0 : fetch_word Plain.M.loaded_segments (0x6d518 : word) = Some W_6d4c0.
Proof. vm_refl. Qed.
Lemma D_6d4c0 : decode_any W_6d4c0 = Some (OpImm ALU_ADD 10 10 3653, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6d4c4 : bv 32 := 0x67f58593.
Lemma F_6d4c4 : fetch_word Plain.M.loaded_segments (0x6d51c : word) = Some W_6d4c4.
Proof. vm_refl. Qed.
Lemma D_6d4c4 : decode_any W_6d4c4 = Some (OpImm ALU_ADD 11 11 1663, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6d4c8 : bv 32 := 0x00040613.
Lemma F_6d4c8 : fetch_word Plain.M.loaded_segments (0x6d520 : word) = Some W_6d4c8.
Proof. vm_refl. Qed.
Lemma D_6d4c8 : decode_any W_6d4c8 = Some (OpImm ALU_ADD 12 8 0, 4%Z).
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
Definition W_6f374 : bv 32 := 0x00050c63.
Lemma F_6f374 : fetch_word Plain.M.loaded_segments (0x6f3cc : word) = Some W_6f374.
Proof. vm_refl. Qed.
Lemma D_6f374 : decode_any W_6f374 = Some (Branch BC_EQ 10 0 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6f38c : bv 32 := 0x000a3517.
Lemma F_6f38c : fetch_word Plain.M.loaded_segments (0x6f3e4 : word) = Some W_6f38c.
Proof. vm_refl. Qed.
Lemma D_6f38c : decode_any W_6f38c = Some (Auipc 10 163, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6f390 : bv 32 := 0x1e453503.
Lemma F_6f390 : fetch_word Plain.M.loaded_segments (0x6f3e8 : word) = Some W_6f390.
Proof. vm_refl. Qed.
Lemma D_6f390 : decode_any W_6f390 = Some (Load SZ8 true 10 10 484, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6f394 : bv 32 := 0x00052503.
Lemma F_6f394 : fetch_word Plain.M.loaded_segments (0x6f3ec : word) = Some W_6f394.
Proof. vm_refl. Qed.
Lemma D_6f394 : decode_any W_6f394 = Some (Load SZ4 true 10 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6f398 : bv 32 := 0x00500593.
Lemma F_6f398 : fetch_word Plain.M.loaded_segments (0x6f3f0 : word) = Some W_6f398.
Proof. vm_refl. Qed.
Lemma D_6f398 : decode_any W_6f398 = Some (OpImm ALU_ADD 11 0 5, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6f39c : bv 32 := 0x02a5c063.
Lemma F_6f39c : fetch_word Plain.M.loaded_segments (0x6f3f4 : word) = Some W_6f39c.
Proof. vm_refl. Qed.
Lemma D_6f39c : decode_any W_6f39c = Some (Branch BC_LT 11 10 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6f3a0 : bv 32 := 0xfffa1517.
Lemma F_6f3a0 : fetch_word Plain.M.loaded_segments (0x6f3f8 : word) = Some W_6f3a0.
Proof. vm_refl. Qed.
Lemma D_6f3a0 : decode_any W_6f3a0 = Some (Auipc 10 1048481, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6f3a4 : bv 32 := 0xfffa8597.
Lemma F_6f3a4 : fetch_word Plain.M.loaded_segments (0x6f3fc : word) = Some W_6f3a4.
Proof. vm_refl. Qed.
Lemma D_6f3a4 : decode_any W_6f3a4 = Some (Auipc 11 1048488, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6f3a8 : bv 32 := 0xf5d50513.
Lemma F_6f3a8 : fetch_word Plain.M.loaded_segments (0x6f400 : word) = Some W_6f3a8.
Proof. vm_refl. Qed.
Lemma D_6f3a8 : decode_any W_6f3a8 = Some (OpImm ALU_ADD 10 10 3933, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6f3ac : bv 32 := 0xd1258593.
Lemma F_6f3ac : fetch_word Plain.M.loaded_segments (0x6f404 : word) = Some W_6f3ac.
Proof. vm_refl. Qed.
Lemma D_6f3ac : decode_any W_6f3ac = Some (OpImm ALU_ADD 11 11 3346, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6f3b0 : bv 32 := 0x00000613.
Lemma F_6f3b0 : fetch_word Plain.M.loaded_segments (0x6f408 : word) = Some W_6f3b0.
Proof. vm_refl. Qed.
Lemma D_6f3b0 : decode_any W_6f3b0 = Some (OpImm ALU_ADD 12 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_6f3b4 : bv 32 := 0xd11f306f.
Lemma F_6f3b4 : fetch_word Plain.M.loaded_segments (0x6f40c : word) = Some W_6f3b4.
Proof. vm_refl. Qed.
Lemma D_6f3b4 : decode_any W_6f3b4 = Some (Jal 0 2047248, 4%Z).
Proof. vm_refl. Qed.

