(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.coturn.FuzzStunClient.images Require Import Asan.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.

(* [comment removed for export] *)
Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

(* [comment removed for export] *)
Definition W_9a5f0 : bv 32 := 0x00000023.
Lemma F_9a5f0 : fetch_word Asan.M.loaded_segments (0x9a5f0 : word) = Some W_9a5f0.
Proof. vm_refl. Qed.
Lemma D_9a5f0 : decode_any W_9a5f0 = Some (Store SZ1 0 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9a5f4 : bv 32 := 0x00008067.
Lemma F_9a5f4 : fetch_word Asan.M.loaded_segments (0x9a5f4 : word) = Some W_9a5f4.
Proof. vm_refl. Qed.
Lemma D_9a5f4 : decode_any W_9a5f4 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9a5f8 : bv 32 := 0x00020513.
Lemma F_9a5f8 : fetch_word Asan.M.loaded_segments (0x9a5f8 : word) = Some W_9a5f8.
Proof. vm_refl. Qed.
Lemma D_9a5f8 : decode_any W_9a5f8 = Some (OpImm ALU_ADD 10 4 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9a5fc : bv 32 := 0xf5c50513.
Lemma F_9a5fc : fetch_word Asan.M.loaded_segments (0x9a5fc : word) = Some W_9a5fc.
Proof. vm_refl. Qed.
Lemma D_9a5fc : decode_any W_9a5fc = Some (OpImm ALU_ADD 10 10 3932, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9a600 : bv 32 := 0x00008067.
Lemma F_9a600 : fetch_word Asan.M.loaded_segments (0x9a600 : word) = Some W_9a600.
Proof. vm_refl. Qed.
Lemma D_9a600 : decode_any W_9a600 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.
(* [comment removed for export] *)
Definition W_a3420 : bv 32 := 0x00853683.
Lemma F_a3420 : fetch_word Asan.M.loaded_segments (0xa3420 : word) = Some W_a3420.
Proof. vm_refl. Qed.
Lemma D_a3420 : decode_any W_a3420 = Some (Load SZ8 true 13 10 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a3424 : bv 32 := 0x01053603.
Lemma F_a3424 : fetch_word Asan.M.loaded_segments (0xa3424 : word) = Some W_a3424.
Proof. vm_refl. Qed.
Lemma D_a3424 : decode_any W_a3424 = Some (Load SZ8 true 12 10 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a3428 : bv 32 := 0x05853703.
Lemma F_a3428 : fetch_word Asan.M.loaded_segments (0xa3428 : word) = Some W_a3428.
Proof. vm_refl. Qed.
Lemma D_a3428 : decode_any W_a3428 = Some (Load SZ8 true 14 10 88, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a342c : bv 32 := 0x00b037b3.
Lemma F_a342c : fetch_word Asan.M.loaded_segments (0xa342c : word) = Some W_a342c.
Proof. vm_refl. Qed.
Lemma D_a342c : decode_any W_a342c = Some (Op ALU_SLTU 15 0 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a3430 : bv 32 := 0x40d60833.
Lemma F_a3430 : fetch_word Asan.M.loaded_segments (0xa3430 : word) = Some W_a3430.
Proof. vm_refl. Qed.
Lemma D_a3430 : decode_any W_a3430 = Some (Op ALU_SUB 16 12 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a3434 : bv 32 := 0x0105a833.
Lemma F_a3434 : fetch_word Asan.M.loaded_segments (0xa3434 : word) = Some W_a3434.
Proof. vm_refl. Qed.
Lemma D_a3434 : decode_any W_a3434 = Some (Op ALU_SLT 16 11 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a3438 : bv 32 := 0x0107f7b3.
Lemma F_a3438 : fetch_word Asan.M.loaded_segments (0xa3438 : word) = Some W_a3438.
Proof. vm_refl. Qed.
Lemma D_a3438 : decode_any W_a3438 = Some (Op ALU_AND 15 15 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a343c : bv 32 := 0x40d70733.
Lemma F_a343c : fetch_word Asan.M.loaded_segments (0xa343c : word) = Some W_a343c.
Proof. vm_refl. Qed.
Lemma D_a343c : decode_any W_a343c = Some (Op ALU_SUB 14 14 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a3440 : bv 32 := 0x0cb53023.
Lemma F_a3440 : fetch_word Asan.M.loaded_segments (0xa3440 : word) = Some W_a3440.
Proof. vm_refl. Qed.
Lemma D_a3440 : decode_any W_a3440 = Some (Store SZ8 10 11 192, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a3444 : bv 32 := 0x0ce53423.
Lemma F_a3444 : fetch_word Asan.M.loaded_segments (0xa3444 : word) = Some W_a3444.
Proof. vm_refl. Qed.
Lemma D_a3444 : decode_any W_a3444 = Some (Store SZ8 10 14 200, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a3448 : bv 32 := 0x00078463.
Lemma F_a3448 : fetch_word Asan.M.loaded_segments (0xa3448 : word) = Some W_a3448.
Proof. vm_refl. Qed.
Lemma D_a3448 : decode_any W_a3448 = Some (Branch BC_EQ 15 0 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a344c : bv 32 := 0x00b68633.
Lemma F_a344c : fetch_word Asan.M.loaded_segments (0xa344c : word) = Some W_a344c.
Proof. vm_refl. Qed.
Lemma D_a344c : decode_any W_a344c = Some (Op ALU_ADD 12 13 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a3450 : bv 32 := 0x0ac53c23.
Lemma F_a3450 : fetch_word Asan.M.loaded_segments (0xa3450 : word) = Some W_a3450.
Proof. vm_refl. Qed.
Lemma D_a3450 : decode_any W_a3450 = Some (Store SZ8 10 12 184, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a3454 : bv 32 := 0x00008067.
Lemma F_a3454 : fetch_word Asan.M.loaded_segments (0xa3454 : word) = Some W_a3454.
Proof. vm_refl. Qed.
Lemma D_a3454 : decode_any W_a3454 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a3458 : bv 32 := 0xfe010113.
Lemma F_a3458 : fetch_word Asan.M.loaded_segments (0xa3458 : word) = Some W_a3458.
Proof. vm_refl. Qed.
Lemma D_a3458 : decode_any W_a3458 = Some (OpImm ALU_ADD 2 2 4064, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a345c : bv 32 := 0x00113c23.
Lemma F_a345c : fetch_word Asan.M.loaded_segments (0xa345c : word) = Some W_a345c.
Proof. vm_refl. Qed.
Lemma D_a345c : decode_any W_a345c = Some (Store SZ8 2 1 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a3460 : bv 32 := 0x00813823.
Lemma F_a3460 : fetch_word Asan.M.loaded_segments (0xa3460 : word) = Some W_a3460.
Proof. vm_refl. Qed.
Lemma D_a3460 : decode_any W_a3460 = Some (Store SZ8 2 8 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a3464 : bv 32 := 0x00913423.
Lemma F_a3464 : fetch_word Asan.M.loaded_segments (0xa3464 : word) = Some W_a3464.
Proof. vm_refl. Qed.
Lemma D_a3464 : decode_any W_a3464 = Some (Store SZ8 2 9 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a3468 : bv 32 := 0x00050413.
Lemma F_a3468 : fetch_word Asan.M.loaded_segments (0xa3468 : word) = Some W_a3468.
Proof. vm_refl. Qed.
Lemma D_a3468 : decode_any W_a3468 = Some (OpImm ALU_ADD 8 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a346c : bv 32 := 0x00853583.
Lemma F_a346c : fetch_word Asan.M.loaded_segments (0xa346c : word) = Some W_a346c.
Proof. vm_refl. Qed.
Lemma D_a346c : decode_any W_a346c = Some (Load SZ8 true 11 10 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a3470 : bv 32 := 0x05853503.
Lemma F_a3470 : fetch_word Asan.M.loaded_segments (0xa3470 : word) = Some W_a3470.
Proof. vm_refl. Qed.
Lemma D_a3470 : decode_any W_a3470 = Some (Load SZ8 true 10 10 88, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a3474 : bv 32 := 0x0c043603.
Lemma F_a3474 : fetch_word Asan.M.loaded_segments (0xa3474 : word) = Some W_a3474.
Proof. vm_refl. Qed.
Lemma D_a3474 : decode_any W_a3474 = Some (Load SZ8 true 12 8 192, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a3478 : bv 32 := 0x0c843483.
Lemma F_a3478 : fetch_word Asan.M.loaded_segments (0xa3478 : word) = Some W_a3478.
Proof. vm_refl. Qed.
Lemma D_a3478 : decode_any W_a3478 = Some (Load SZ8 true 9 8 200, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a347c : bv 32 := 0x40a586b3.
Lemma F_a347c : fetch_word Asan.M.loaded_segments (0xa347c : word) = Some W_a347c.
Proof. vm_refl. Qed.
Lemma D_a347c : decode_any W_a347c = Some (Op ALU_SUB 13 11 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a3480 : bv 32 := 0x009684b3.
Lemma F_a3480 : fetch_word Asan.M.loaded_segments (0xa3480 : word) = Some W_a3480.
Proof. vm_refl. Qed.
Lemma D_a3480 : decode_any W_a3480 = Some (Op ALU_ADD 9 13 9, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a3484 : bv 32 := 0x00060463.
Lemma F_a3484 : fetch_word Asan.M.loaded_segments (0xa3484 : word) = Some W_a3484.
Proof. vm_refl. Qed.
Lemma D_a3484 : decode_any W_a3484 = Some (Branch BC_EQ 12 0 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a3488 : bv 32 := 0x06c4d663.
Lemma F_a3488 : fetch_word Asan.M.loaded_segments (0xa3488 : word) = Some W_a3488.
Proof. vm_refl. Qed.
Lemma D_a3488 : decode_any W_a3488 = Some (Branch BC_GE 9 12 108, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a348c : bv 32 := 0x00040513.
Lemma F_a348c : fetch_word Asan.M.loaded_segments (0xa348c : word) = Some W_a348c.
Proof. vm_refl. Qed.
Lemma D_a348c : decode_any W_a348c = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a3490 : bv 32 := 0xed5fc0ef.
Lemma F_a3490 : fetch_word Asan.M.loaded_segments (0xa3490 : word) = Some W_a3490.
Proof. vm_refl. Qed.
Lemma D_a3490 : decode_any W_a3490 = Some (Jal 1 2084564, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a3494 : bv 32 := 0x04054c63.
Lemma F_a3494 : fetch_word Asan.M.loaded_segments (0xa3494 : word) = Some W_a3494.
Proof. vm_refl. Qed.
Lemma D_a3494 : decode_any W_a3494 = Some (Branch BC_LT 10 0 88, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a3498 : bv 32 := 0x0c043683.
Lemma F_a3498 : fetch_word Asan.M.loaded_segments (0xa3498 : word) = Some W_a3498.
Proof. vm_refl. Qed.
Lemma D_a3498 : decode_any W_a3498 = Some (Load SZ8 true 13 8 192, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a349c : bv 32 := 0x00843583.
Lemma F_a349c : fetch_word Asan.M.loaded_segments (0xa349c : word) = Some W_a349c.
Proof. vm_refl. Qed.
Lemma D_a349c : decode_any W_a349c = Some (Load SZ8 true 11 8 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a34a0 : bv 32 := 0x01043603.
Lemma F_a34a0 : fetch_word Asan.M.loaded_segments (0xa34a0 : word) = Some W_a34a0.
Proof. vm_refl. Qed.
Lemma D_a34a0 : decode_any W_a34a0 = Some (Load SZ8 true 12 8 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a34a4 : bv 32 := 0x00148493.
Lemma F_a34a4 : fetch_word Asan.M.loaded_segments (0xa34a4 : word) = Some W_a34a4.
Proof. vm_refl. Qed.
Lemma D_a34a4 : decode_any W_a34a4 = Some (OpImm ALU_ADD 9 9 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a34a8 : bv 32 := 0x00068a63.
Lemma F_a34a8 : fetch_word Asan.M.loaded_segments (0xa34a8 : word) = Some W_a34a8.
Proof. vm_refl. Qed.
Lemma D_a34a8 : decode_any W_a34a8 = Some (Branch BC_EQ 13 0 20, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a34ac : bv 32 := 0x40b60733.
Lemma F_a34ac : fetch_word Asan.M.loaded_segments (0xa34ac : word) = Some W_a34ac.
Proof. vm_refl. Qed.
Lemma D_a34ac : decode_any W_a34ac = Some (Op ALU_SUB 14 12 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a34b0 : bv 32 := 0x409686b3.
Lemma F_a34b0 : fetch_word Asan.M.loaded_segments (0xa34b0 : word) = Some W_a34b0.
Proof. vm_refl. Qed.
Lemma D_a34b0 : decode_any W_a34b0 = Some (Op ALU_SUB 13 13 9, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a34b4 : bv 32 := 0x00e6d463.
Lemma F_a34b4 : fetch_word Asan.M.loaded_segments (0xa34b4 : word) = Some W_a34b4.
Proof. vm_refl. Qed.
Lemma D_a34b4 : decode_any W_a34b4 = Some (Branch BC_GE 13 14 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a34b8 : bv 32 := 0x00d58633.
Lemma F_a34b8 : fetch_word Asan.M.loaded_segments (0xa34b8 : word) = Some W_a34b8.
Proof. vm_refl. Qed.
Lemma D_a34b8 : decode_any W_a34b8 = Some (Op ALU_ADD 12 11 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a34bc : bv 32 := 0x05843683.
Lemma F_a34bc : fetch_word Asan.M.loaded_segments (0xa34bc : word) = Some W_a34bc.
Proof. vm_refl. Qed.
Lemma D_a34bc : decode_any W_a34bc = Some (Load SZ8 true 13 8 88, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a34c0 : bv 32 := 0x40b68733.
Lemma F_a34c0 : fetch_word Asan.M.loaded_segments (0xa34c0 : word) = Some W_a34c0.
Proof. vm_refl. Qed.
Lemma D_a34c0 : decode_any W_a34c0 = Some (Op ALU_SUB 14 13 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a34c4 : bv 32 := 0x00e48733.
Lemma F_a34c4 : fetch_word Asan.M.loaded_segments (0xa34c4 : word) = Some W_a34c4.
Proof. vm_refl. Qed.
Lemma D_a34c4 : decode_any W_a34c4 = Some (Op ALU_ADD 14 9 14, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a34c8 : bv 32 := 0x0ac43c23.
Lemma F_a34c8 : fetch_word Asan.M.loaded_segments (0xa34c8 : word) = Some W_a34c8.
Proof. vm_refl. Qed.
Lemma D_a34c8 : decode_any W_a34c8 = Some (Store SZ8 8 12 184, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a34cc : bv 32 := 0x0ce43423.
Lemma F_a34cc : fetch_word Asan.M.loaded_segments (0xa34cc : word) = Some W_a34cc.
Proof. vm_refl. Qed.
Lemma D_a34cc : decode_any W_a34cc = Some (Store SZ8 8 14 200, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a34d0 : bv 32 := 0x00b6e463.
Lemma F_a34d0 : fetch_word Asan.M.loaded_segments (0xa34d0 : word) = Some W_a34d0.
Proof. vm_refl. Qed.
Lemma D_a34d0 : decode_any W_a34d0 = Some (Branch BC_LTU 13 11 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a34d4 : bv 32 := 0xfea58fa3.
Lemma F_a34d4 : fetch_word Asan.M.loaded_segments (0xa34d4 : word) = Some W_a34d4.
Proof. vm_refl. Qed.
Lemma D_a34d4 : decode_any W_a34d4 = Some (Store SZ1 11 10 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a34d8 : bv 32 := 0x01813083.
Lemma F_a34d8 : fetch_word Asan.M.loaded_segments (0xa34d8 : word) = Some W_a34d8.
Proof. vm_refl. Qed.
Lemma D_a34d8 : decode_any W_a34d8 = Some (Load SZ8 true 1 2 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a34dc : bv 32 := 0x01013403.
Lemma F_a34dc : fetch_word Asan.M.loaded_segments (0xa34dc : word) = Some W_a34dc.
Proof. vm_refl. Qed.
Lemma D_a34dc : decode_any W_a34dc = Some (Load SZ8 true 8 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a34e0 : bv 32 := 0x00813483.
Lemma F_a34e0 : fetch_word Asan.M.loaded_segments (0xa34e0 : word) = Some W_a34e0.
Proof. vm_refl. Qed.
Lemma D_a34e0 : decode_any W_a34e0 = Some (Load SZ8 true 9 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a34e4 : bv 32 := 0x02010113.
Lemma F_a34e4 : fetch_word Asan.M.loaded_segments (0xa34e4 : word) = Some W_a34e4.
Proof. vm_refl. Qed.
Lemma D_a34e4 : decode_any W_a34e4 = Some (OpImm ALU_ADD 2 2 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a34e8 : bv 32 := 0x00008067.
Lemma F_a34e8 : fetch_word Asan.M.loaded_segments (0xa34e8 : word) = Some W_a34e8.
Proof. vm_refl. Qed.
Lemma D_a34e8 : decode_any W_a34e8 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a34ec : bv 32 := 0x05843503.
Lemma F_a34ec : fetch_word Asan.M.loaded_segments (0xa34ec : word) = Some W_a34ec.
Proof. vm_refl. Qed.
Lemma D_a34ec : decode_any W_a34ec = Some (Load SZ8 true 10 8 88, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a34f0 : bv 32 := 0x00843583.
Lemma F_a34f0 : fetch_word Asan.M.loaded_segments (0xa34f0 : word) = Some W_a34f0.
Proof. vm_refl. Qed.
Lemma D_a34f0 : decode_any W_a34f0 = Some (Load SZ8 true 11 8 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a34f4 : bv 32 := 0x40b50533.
Lemma F_a34f4 : fetch_word Asan.M.loaded_segments (0xa34f4 : word) = Some W_a34f4.
Proof. vm_refl. Qed.
Lemma D_a34f4 : decode_any W_a34f4 = Some (Op ALU_SUB 10 10 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a34f8 : bv 32 := 0x00a484b3.
Lemma F_a34f8 : fetch_word Asan.M.loaded_segments (0xa34f8 : word) = Some W_a34f8.
Proof. vm_refl. Qed.
Lemma D_a34f8 : decode_any W_a34f8 = Some (Op ALU_ADD 9 9 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a34fc : bv 32 := 0xfff00513.
Lemma F_a34fc : fetch_word Asan.M.loaded_segments (0xa34fc : word) = Some W_a34fc.
Proof. vm_refl. Qed.
Lemma D_a34fc : decode_any W_a34fc = Some (OpImm ALU_ADD 10 0 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a3500 : bv 32 := 0x0ab43c23.
Lemma F_a3500 : fetch_word Asan.M.loaded_segments (0xa3500 : word) = Some W_a3500.
Proof. vm_refl. Qed.
Lemma D_a3500 : decode_any W_a3500 = Some (Store SZ8 8 11 184, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a3504 : bv 32 := 0x0ca43023.
Lemma F_a3504 : fetch_word Asan.M.loaded_segments (0xa3504 : word) = Some W_a3504.
Proof. vm_refl. Qed.
Lemma D_a3504 : decode_any W_a3504 = Some (Store SZ8 8 10 192, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a3508 : bv 32 := 0x0c943423.
Lemma F_a3508 : fetch_word Asan.M.loaded_segments (0xa3508 : word) = Some W_a3508.
Proof. vm_refl. Qed.
Lemma D_a3508 : decode_any W_a3508 = Some (Store SZ8 8 9 200, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a350c : bv 32 := 0x01813083.
Lemma F_a350c : fetch_word Asan.M.loaded_segments (0xa350c : word) = Some W_a350c.
Proof. vm_refl. Qed.
Lemma D_a350c : decode_any W_a350c = Some (Load SZ8 true 1 2 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a3510 : bv 32 := 0x01013403.
Lemma F_a3510 : fetch_word Asan.M.loaded_segments (0xa3510 : word) = Some W_a3510.
Proof. vm_refl. Qed.
Lemma D_a3510 : decode_any W_a3510 = Some (Load SZ8 true 8 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a3514 : bv 32 := 0x00813483.
Lemma F_a3514 : fetch_word Asan.M.loaded_segments (0xa3514 : word) = Some W_a3514.
Proof. vm_refl. Qed.
Lemma D_a3514 : decode_any W_a3514 = Some (Load SZ8 true 9 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a3518 : bv 32 := 0x02010113.
Lemma F_a3518 : fetch_word Asan.M.loaded_segments (0xa3518 : word) = Some W_a3518.
Proof. vm_refl. Qed.
Lemma D_a3518 : decode_any W_a3518 = Some (OpImm ALU_ADD 2 2 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a351c : bv 32 := 0x00008067.
Lemma F_a351c : fetch_word Asan.M.loaded_segments (0xa351c : word) = Some W_a351c.
Proof. vm_refl. Qed.
Lemma D_a351c : decode_any W_a351c = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a3520 : bv 32 := 0xfb010113.
Lemma F_a3520 : fetch_word Asan.M.loaded_segments (0xa3520 : word) = Some W_a3520.
Proof. vm_refl. Qed.
Lemma D_a3520 : decode_any W_a3520 = Some (OpImm ALU_ADD 2 2 4016, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a3524 : bv 32 := 0x04113423.
Lemma F_a3524 : fetch_word Asan.M.loaded_segments (0xa3524 : word) = Some W_a3524.
Proof. vm_refl. Qed.
Lemma D_a3524 : decode_any W_a3524 = Some (Store SZ8 2 1 72, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a3528 : bv 32 := 0x04813023.
Lemma F_a3528 : fetch_word Asan.M.loaded_segments (0xa3528 : word) = Some W_a3528.
Proof. vm_refl. Qed.
Lemma D_a3528 : decode_any W_a3528 = Some (Store SZ8 2 8 64, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a352c : bv 32 := 0x02913c23.
Lemma F_a352c : fetch_word Asan.M.loaded_segments (0xa352c : word) = Some W_a352c.
Proof. vm_refl. Qed.
Lemma D_a352c : decode_any W_a352c = Some (Store SZ8 2 9 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a3530 : bv 32 := 0x03213823.
Lemma F_a3530 : fetch_word Asan.M.loaded_segments (0xa3530 : word) = Some W_a3530.
Proof. vm_refl. Qed.
Lemma D_a3530 : decode_any W_a3530 = Some (Store SZ8 2 18 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a3534 : bv 32 := 0x03313423.
Lemma F_a3534 : fetch_word Asan.M.loaded_segments (0xa3534 : word) = Some W_a3534.
Proof. vm_refl. Qed.
Lemma D_a3534 : decode_any W_a3534 = Some (Store SZ8 2 19 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a3538 : bv 32 := 0x03413023.
Lemma F_a3538 : fetch_word Asan.M.loaded_segments (0xa3538 : word) = Some W_a3538.
Proof. vm_refl. Qed.
Lemma D_a3538 : decode_any W_a3538 = Some (Store SZ8 2 20 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a353c : bv 32 := 0x01513c23.
Lemma F_a353c : fetch_word Asan.M.loaded_segments (0xa353c : word) = Some W_a353c.
Proof. vm_refl. Qed.
Lemma D_a353c : decode_any W_a353c = Some (Store SZ8 2 21 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a3540 : bv 32 := 0x01613823.
Lemma F_a3540 : fetch_word Asan.M.loaded_segments (0xa3540 : word) = Some W_a3540.
Proof. vm_refl. Qed.
Lemma D_a3540 : decode_any W_a3540 = Some (Store SZ8 2 22 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a3544 : bv 32 := 0x01713423.
Lemma F_a3544 : fetch_word Asan.M.loaded_segments (0xa3544 : word) = Some W_a3544.
Proof. vm_refl. Qed.
Lemma D_a3544 : decode_any W_a3544 = Some (Store SZ8 2 23 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a3548 : bv 32 := 0x01813023.
Lemma F_a3548 : fetch_word Asan.M.loaded_segments (0xa3548 : word) = Some W_a3548.
Proof. vm_refl. Qed.
Lemma D_a3548 : decode_any W_a3548 = Some (Store SZ8 2 24 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a354c : bv 32 := 0x00058913.
Lemma F_a354c : fetch_word Asan.M.loaded_segments (0xa354c : word) = Some W_a354c.
Proof. vm_refl. Qed.
Lemma D_a354c : decode_any W_a354c = Some (OpImm ALU_ADD 18 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a3550 : bv 32 := 0x02400593.
Lemma F_a3550 : fetch_word Asan.M.loaded_segments (0xa3550 : word) = Some W_a3550.
Proof. vm_refl. Qed.
Lemma D_a3550 : decode_any W_a3550 = Some (OpImm ALU_ADD 11 0 36, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a3554 : bv 32 := 0x1325ee63.
Lemma F_a3554 : fetch_word Asan.M.loaded_segments (0xa3554 : word) = Some W_a3554.
Proof. vm_refl. Qed.
Lemma D_a3554 : decode_any W_a3554 = Some (Branch BC_LTU 11 18 316, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a3558 : bv 32 := 0x00050493.
Lemma F_a3558 : fetch_word Asan.M.loaded_segments (0xa3558 : word) = Some W_a3558.
Proof. vm_refl. Qed.
Lemma D_a3558 : decode_any W_a3558 = Some (OpImm ALU_ADD 9 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a355c : bv 32 := 0x00100513.
Lemma F_a355c : fetch_word Asan.M.loaded_segments (0xa355c : word) = Some W_a355c.
Proof. vm_refl. Qed.
Lemma D_a355c : decode_any W_a355c = Some (OpImm ALU_ADD 10 0 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a3560 : bv 32 := 0x12a90863.
Lemma F_a3560 : fetch_word Asan.M.loaded_segments (0xa3560 : word) = Some W_a3560.
Proof. vm_refl. Qed.
Lemma D_a3560 : decode_any W_a3560 = Some (Branch BC_EQ 18 10 304, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a3564 : bv 32 := 0x00068413.
Lemma F_a3564 : fetch_word Asan.M.loaded_segments (0xa3564 : word) = Some W_a3564.
Proof. vm_refl. Qed.
Lemma D_a3564 : decode_any W_a3564 = Some (OpImm ALU_ADD 8 13 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a3568 : bv 32 := 0x00060993.
Lemma F_a3568 : fetch_word Asan.M.loaded_segments (0xa3568 : word) = Some W_a3568.
Proof. vm_refl. Qed.
Lemma D_a3568 : decode_any W_a3568 = Some (OpImm ALU_ADD 19 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a356c : bv 32 := 0x00500a13.
Lemma F_a356c : fetch_word Asan.M.loaded_segments (0xa356c : word) = Some W_a356c.
Proof. vm_refl. Qed.
Lemma D_a356c : decode_any W_a356c = Some (OpImm ALU_ADD 20 0 5, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a3570 : bv 32 := 0x02000a93.
Lemma F_a3570 : fetch_word Asan.M.loaded_segments (0xa3570 : word) = Some W_a3570.
Proof. vm_refl. Qed.
Lemma D_a3570 : decode_any W_a3570 = Some (OpImm ALU_ADD 21 0 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a3574 : bv 32 := 0x0140006f.
Lemma F_a3574 : fetch_word Asan.M.loaded_segments (0xa3574 : word) = Some W_a3574.
Proof. vm_refl. Qed.
Lemma D_a3574 : decode_any W_a3574 = Some (Jal 0 20, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a3578 : bv 32 := 0x00048513.
Lemma F_a3578 : fetch_word Asan.M.loaded_segments (0xa3578 : word) = Some W_a3578.
Proof. vm_refl. Qed.
Lemma D_a3578 : decode_any W_a3578 = Some (OpImm ALU_ADD 10 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a357c : bv 32 := 0xeddff0ef.
Lemma F_a357c : fetch_word Asan.M.loaded_segments (0xa357c : word) = Some W_a357c.
Proof. vm_refl. Qed.
Lemma D_a357c : decode_any W_a357c = Some (Jal 1 2096860, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a3580 : bv 32 := 0xff750593.
Lemma F_a3580 : fetch_word Asan.M.loaded_segments (0xa3580 : word) = Some W_a3580.
Proof. vm_refl. Qed.
Lemma D_a3580 : decode_any W_a3580 = Some (OpImm ALU_ADD 11 10 4087, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a3584 : bv 32 := 0x0345f263.
Lemma F_a3584 : fetch_word Asan.M.loaded_segments (0xa3584 : word) = Some W_a3584.
Proof. vm_refl. Qed.
Lemma D_a3584 : decode_any W_a3584 = Some (Branch BC_GEU 11 20 36, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a3588 : bv 32 := 0x0084b503.
Lemma F_a3588 : fetch_word Asan.M.loaded_segments (0xa3588 : word) = Some W_a3588.
Proof. vm_refl. Qed.
Lemma D_a3588 : decode_any W_a3588 = Some (Load SZ8 true 10 9 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a358c : bv 32 := 0x0b84b583.
Lemma F_a358c : fetch_word Asan.M.loaded_segments (0xa358c : word) = Some W_a358c.
Proof. vm_refl. Qed.
Lemma D_a358c : decode_any W_a358c = Some (Load SZ8 true 11 9 184, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a3590 : bv 32 := 0xfeb504e3.
Lemma F_a3590 : fetch_word Asan.M.loaded_segments (0xa3590 : word) = Some W_a3590.
Proof. vm_refl. Qed.
Lemma D_a3590 : decode_any W_a3590 = Some (Branch BC_EQ 10 11 8168, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a3594 : bv 32 := 0x00150593.
Lemma F_a3594 : fetch_word Asan.M.loaded_segments (0xa3594 : word) = Some W_a3594.
Proof. vm_refl. Qed.
Lemma D_a3594 : decode_any W_a3594 = Some (OpImm ALU_ADD 11 10 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a3598 : bv 32 := 0x00b4b423.
Lemma F_a3598 : fetch_word Asan.M.loaded_segments (0xa3598 : word) = Some W_a3598.
Proof. vm_refl. Qed.
Lemma D_a3598 : decode_any W_a3598 = Some (Store SZ8 9 11 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a359c : bv 32 := 0x00054503.
Lemma F_a359c : fetch_word Asan.M.loaded_segments (0xa359c : word) = Some W_a359c.
Proof. vm_refl. Qed.
Lemma D_a359c : decode_any W_a359c = Some (Load SZ1 false 10 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a35a0 : bv 32 := 0xff750593.
Lemma F_a35a0 : fetch_word Asan.M.loaded_segments (0xa35a0 : word) = Some W_a35a0.
Proof. vm_refl. Qed.
Lemma D_a35a0 : decode_any W_a35a0 = Some (OpImm ALU_ADD 11 10 4087, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a35a4 : bv 32 := 0xff45e2e3.
Lemma F_a35a4 : fetch_word Asan.M.loaded_segments (0xa35a4 : word) = Some W_a35a4.
Proof. vm_refl. Qed.
Lemma D_a35a4 : decode_any W_a35a4 = Some (Branch BC_LTU 11 20 8164, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a35a8 : bv 32 := 0xff5500e3.
Lemma F_a35a8 : fetch_word Asan.M.loaded_segments (0xa35a8 : word) = Some W_a35a8.
Proof. vm_refl. Qed.
Lemma D_a35a8 : decode_any W_a35a8 = Some (Branch BC_EQ 10 21 8160, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a35ac : bv 32 := 0x02d00593.
Lemma F_a35ac : fetch_word Asan.M.loaded_segments (0xa35ac : word) = Some W_a35ac.
Proof. vm_refl. Qed.
Lemma D_a35ac : decode_any W_a35ac = Some (OpImm ALU_ADD 11 0 45, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a35b0 : bv 32 := 0x00b50663.
Lemma F_a35b0 : fetch_word Asan.M.loaded_segments (0xa35b0 : word) = Some W_a35b0.
Proof. vm_refl. Qed.
Lemma D_a35b0 : decode_any W_a35b0 = Some (Branch BC_EQ 10 11 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a35b4 : bv 32 := 0x02b00593.
Lemma F_a35b4 : fetch_word Asan.M.loaded_segments (0xa35b4 : word) = Some W_a35b4.
Proof. vm_refl. Qed.
Lemma D_a35b4 : decode_any W_a35b4 = Some (OpImm ALU_ADD 11 0 43, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a35b8 : bv 32 := 0x02b51a63.
Lemma F_a35b8 : fetch_word Asan.M.loaded_segments (0xa35b8 : word) = Some W_a35b8.
Proof. vm_refl. Qed.
Lemma D_a35b8 : decode_any W_a35b8 = Some (Branch BC_NE 10 11 52, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a35bc : bv 32 := 0x0084b583.
Lemma F_a35bc : fetch_word Asan.M.loaded_segments (0xa35bc : word) = Some W_a35bc.
Proof. vm_refl. Qed.
Lemma D_a35bc : decode_any W_a35bc = Some (Load SZ8 true 11 9 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a35c0 : bv 32 := 0x0b84b603.
Lemma F_a35c0 : fetch_word Asan.M.loaded_segments (0xa35c0 : word) = Some W_a35c0.
Proof. vm_refl. Qed.
Lemma D_a35c0 : decode_any W_a35c0 = Some (Load SZ8 true 12 9 184, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a35c4 : bv 32 := 0xfd350513.
Lemma F_a35c4 : fetch_word Asan.M.loaded_segments (0xa35c4 : word) = Some W_a35c4.
Proof. vm_refl. Qed.
Lemma D_a35c4 : decode_any W_a35c4 = Some (OpImm ALU_ADD 10 10 4051, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a35c8 : bv 32 := 0x00a03a33.
Lemma F_a35c8 : fetch_word Asan.M.loaded_segments (0xa35c8 : word) = Some W_a35c8.
Proof. vm_refl. Qed.
Lemma D_a35c8 : decode_any W_a35c8 = Some (Op ALU_SLTU 20 0 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a35cc : bv 32 := 0xfffa0a1b.
Lemma F_a35cc : fetch_word Asan.M.loaded_segments (0xa35cc : word) = Some W_a35cc.
Proof. vm_refl. Qed.
Lemma D_a35cc : decode_any W_a35cc = Some (OpImm32 20 20 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a35d0 : bv 32 := 0x02c58663.
Lemma F_a35d0 : fetch_word Asan.M.loaded_segments (0xa35d0 : word) = Some W_a35d0.
Proof. vm_refl. Qed.
Lemma D_a35d0 : decode_any W_a35d0 = Some (Branch BC_EQ 11 12 44, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a35d4 : bv 32 := 0x00158513.
Lemma F_a35d4 : fetch_word Asan.M.loaded_segments (0xa35d4 : word) = Some W_a35d4.
Proof. vm_refl. Qed.
Lemma D_a35d4 : decode_any W_a35d4 = Some (OpImm ALU_ADD 10 11 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a35d8 : bv 32 := 0x00a4b423.
Lemma F_a35d8 : fetch_word Asan.M.loaded_segments (0xa35d8 : word) = Some W_a35d8.
Proof. vm_refl. Qed.
Lemma D_a35d8 : decode_any W_a35d8 = Some (Store SZ8 9 10 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a35dc : bv 32 := 0x0005c503.
Lemma F_a35dc : fetch_word Asan.M.loaded_segments (0xa35dc : word) = Some W_a35dc.
Proof. vm_refl. Qed.
Lemma D_a35dc : decode_any W_a35dc = Some (Load SZ1 false 10 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a35e0 : bv 32 := 0xfef97593.
Lemma F_a35e0 : fetch_word Asan.M.loaded_segments (0xa35e0 : word) = Some W_a35e0.
Proof. vm_refl. Qed.
Lemma D_a35e0 : decode_any W_a35e0 = Some (OpImm ALU_AND 11 18 4079, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a35e4 : bv 32 := 0x02058463.
Lemma F_a35e4 : fetch_word Asan.M.loaded_segments (0xa35e4 : word) = Some W_a35e4.
Proof. vm_refl. Qed.
Lemma D_a35e4 : decode_any W_a35e4 = Some (Branch BC_EQ 11 0 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a35e8 : bv 32 := 0x06c0006f.
Lemma F_a35e8 : fetch_word Asan.M.loaded_segments (0xa35e8 : word) = Some W_a35e8.
Proof. vm_refl. Qed.
Lemma D_a35e8 : decode_any W_a35e8 = Some (Jal 0 108, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a35ec : bv 32 := 0x00000a13.
Lemma F_a35ec : fetch_word Asan.M.loaded_segments (0xa35ec : word) = Some W_a35ec.
Proof. vm_refl. Qed.
Lemma D_a35ec : decode_any W_a35ec = Some (OpImm ALU_ADD 20 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a35f0 : bv 32 := 0xfef97593.
Lemma F_a35f0 : fetch_word Asan.M.loaded_segments (0xa35f0 : word) = Some W_a35f0.
Proof. vm_refl. Qed.
Lemma D_a35f0 : decode_any W_a35f0 = Some (OpImm ALU_AND 11 18 4079, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a35f4 : bv 32 := 0x00058c63.
Lemma F_a35f4 : fetch_word Asan.M.loaded_segments (0xa35f4 : word) = Some W_a35f4.
Proof. vm_refl. Qed.
Lemma D_a35f4 : decode_any W_a35f4 = Some (Branch BC_EQ 11 0 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a35f8 : bv 32 := 0x05c0006f.
Lemma F_a35f8 : fetch_word Asan.M.loaded_segments (0xa35f8 : word) = Some W_a35f8.
Proof. vm_refl. Qed.
Lemma D_a35f8 : decode_any W_a35f8 = Some (Jal 0 92, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a35fc : bv 32 := 0x00048513.
Lemma F_a35fc : fetch_word Asan.M.loaded_segments (0xa35fc : word) = Some W_a35fc.
Proof. vm_refl. Qed.
Lemma D_a35fc : decode_any W_a35fc = Some (OpImm ALU_ADD 10 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a3600 : bv 32 := 0xe59ff0ef.
Lemma F_a3600 : fetch_word Asan.M.loaded_segments (0xa3600 : word) = Some W_a3600.
Proof. vm_refl. Qed.
Lemma D_a3600 : decode_any W_a3600 = Some (Jal 1 2096728, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a3604 : bv 32 := 0xfef97593.
Lemma F_a3604 : fetch_word Asan.M.loaded_segments (0xa3604 : word) = Some W_a3604.
Proof. vm_refl. Qed.
Lemma D_a3604 : decode_any W_a3604 = Some (OpImm ALU_AND 11 18 4079, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a3608 : bv 32 := 0x04059663.
Lemma F_a3608 : fetch_word Asan.M.loaded_segments (0xa3608 : word) = Some W_a3608.
Proof. vm_refl. Qed.
Lemma D_a3608 : decode_any W_a3608 = Some (Branch BC_NE 11 0 76, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a360c : bv 32 := 0x03000593.
Lemma F_a360c : fetch_word Asan.M.loaded_segments (0xa360c : word) = Some W_a360c.
Proof. vm_refl. Qed.
Lemma D_a360c : decode_any W_a360c = Some (OpImm ALU_ADD 11 0 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a3610 : bv 32 := 0x04b51263.
Lemma F_a3610 : fetch_word Asan.M.loaded_segments (0xa3610 : word) = Some W_a3610.
Proof. vm_refl. Qed.
Lemma D_a3610 : decode_any W_a3610 = Some (Branch BC_NE 10 11 68, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a3614 : bv 32 := 0x0084b503.
Lemma F_a3614 : fetch_word Asan.M.loaded_segments (0xa3614 : word) = Some W_a3614.
Proof. vm_refl. Qed.
Lemma D_a3614 : decode_any W_a3614 = Some (Load SZ8 true 10 9 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a3618 : bv 32 := 0x0b84b583.
Lemma F_a3618 : fetch_word Asan.M.loaded_segments (0xa3618 : word) = Some W_a3618.
Proof. vm_refl. Qed.
Lemma D_a3618 : decode_any W_a3618 = Some (Load SZ8 true 11 9 184, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a361c : bv 32 := 0x08b50463.
Lemma F_a361c : fetch_word Asan.M.loaded_segments (0xa361c : word) = Some W_a361c.
Proof. vm_refl. Qed.
Lemma D_a361c : decode_any W_a361c = Some (Branch BC_EQ 10 11 136, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a3620 : bv 32 := 0x00150593.
Lemma F_a3620 : fetch_word Asan.M.loaded_segments (0xa3620 : word) = Some W_a3620.
Proof. vm_refl. Qed.
Lemma D_a3620 : decode_any W_a3620 = Some (OpImm ALU_ADD 11 10 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a3624 : bv 32 := 0x00b4b423.
Lemma F_a3624 : fetch_word Asan.M.loaded_segments (0xa3624 : word) = Some W_a3624.
Proof. vm_refl. Qed.
Lemma D_a3624 : decode_any W_a3624 = Some (Store SZ8 9 11 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a3628 : bv 32 := 0x00054503.
Lemma F_a3628 : fetch_word Asan.M.loaded_segments (0xa3628 : word) = Some W_a3628.
Proof. vm_refl. Qed.
Lemma D_a3628 : decode_any W_a3628 = Some (Load SZ1 false 10 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a362c : bv 32 := 0xfdf57593.
Lemma F_a362c : fetch_word Asan.M.loaded_segments (0xa362c : word) = Some W_a362c.
Proof. vm_refl. Qed.
Lemma D_a362c : decode_any W_a362c = Some (OpImm ALU_AND 11 10 4063, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a3630 : bv 32 := 0x05800613.
Lemma F_a3630 : fetch_word Asan.M.loaded_segments (0xa3630 : word) = Some W_a3630.
Proof. vm_refl. Qed.
Lemma D_a3630 : decode_any W_a3630 = Some (OpImm ALU_ADD 12 0 88, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a3634 : bv 32 := 0x08c59263.
Lemma F_a3634 : fetch_word Asan.M.loaded_segments (0xa3634 : word) = Some W_a3634.
Proof. vm_refl. Qed.
Lemma D_a3634 : decode_any W_a3634 = Some (Branch BC_NE 11 12 132, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a3638 : bv 32 := 0x0084b503.
Lemma F_a3638 : fetch_word Asan.M.loaded_segments (0xa3638 : word) = Some W_a3638.
Proof. vm_refl. Qed.
Lemma D_a3638 : decode_any W_a3638 = Some (Load SZ8 true 10 9 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a363c : bv 32 := 0x0b84b583.
Lemma F_a363c : fetch_word Asan.M.loaded_segments (0xa363c : word) = Some W_a363c.
Proof. vm_refl. Qed.
Lemma D_a363c : decode_any W_a363c = Some (Load SZ8 true 11 9 184, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a3640 : bv 32 := 0x14b50e63.
Lemma F_a3640 : fetch_word Asan.M.loaded_segments (0xa3640 : word) = Some W_a3640.
Proof. vm_refl. Qed.
Lemma D_a3640 : decode_any W_a3640 = Some (Branch BC_EQ 10 11 348, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a3644 : bv 32 := 0x00150593.
Lemma F_a3644 : fetch_word Asan.M.loaded_segments (0xa3644 : word) = Some W_a3644.
Proof. vm_refl. Qed.
Lemma D_a3644 : decode_any W_a3644 = Some (OpImm ALU_ADD 11 10 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a3648 : bv 32 := 0x00b4b423.
Lemma F_a3648 : fetch_word Asan.M.loaded_segments (0xa3648 : word) = Some W_a3648.
Proof. vm_refl. Qed.
Lemma D_a3648 : decode_any W_a3648 = Some (Store SZ8 9 11 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a364c : bv 32 := 0x00054503.
Lemma F_a364c : fetch_word Asan.M.loaded_segments (0xa364c : word) = Some W_a364c.
Proof. vm_refl. Qed.
Lemma D_a364c : decode_any W_a364c = Some (Load SZ1 false 10 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a3650 : bv 32 := 0x1540006f.
Lemma F_a3650 : fetch_word Asan.M.loaded_segments (0xa3650 : word) = Some W_a3650.
Proof. vm_refl. Qed.
Lemma D_a3650 : decode_any W_a3650 = Some (Jal 0 340, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a3654 : bv 32 := 0x00091463.
Lemma F_a3654 : fetch_word Asan.M.loaded_segments (0xa3654 : word) = Some W_a3654.
Proof. vm_refl. Qed.
Lemma D_a3654 : decode_any W_a3654 = Some (Branch BC_NE 18 0 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a3658 : bv 32 := 0x00a00913.
Lemma F_a3658 : fetch_word Asan.M.loaded_segments (0xa3658 : word) = Some W_a3658.
Proof. vm_refl. Qed.
Lemma D_a3658 : decode_any W_a3658 = Some (OpImm ALU_ADD 18 0 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a365c : bv 32 := 0xfff80597.
Lemma F_a365c : fetch_word Asan.M.loaded_segments (0xa365c : word) = Some W_a365c.
Proof. vm_refl. Qed.
Lemma D_a365c : decode_any W_a365c = Some (Auipc 11 1048448, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a3660 : bv 32 := 0x16458593.
Lemma F_a3660 : fetch_word Asan.M.loaded_segments (0xa3660 : word) = Some W_a3660.
Proof. vm_refl. Qed.
Lemma D_a3660 : decode_any W_a3660 = Some (OpImm ALU_ADD 11 11 356, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a3664 : bv 32 := 0x00a585b3.
Lemma F_a3664 : fetch_word Asan.M.loaded_segments (0xa3664 : word) = Some W_a3664.
Proof. vm_refl. Qed.
Lemma D_a3664 : decode_any W_a3664 = Some (Op ALU_ADD 11 11 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a3668 : bv 32 := 0x0015c583.
Lemma F_a3668 : fetch_word Asan.M.loaded_segments (0xa3668 : word) = Some W_a3668.
Proof. vm_refl. Qed.
Lemma D_a3668 : decode_any W_a3668 = Some (Load SZ1 false 11 11 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a366c : bv 32 := 0x0525e863.
Lemma F_a366c : fetch_word Asan.M.loaded_segments (0xa366c : word) = Some W_a366c.
Proof. vm_refl. Qed.
Lemma D_a366c : decode_any W_a366c = Some (Branch BC_LTU 11 18 80, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a3670 : bv 32 := 0x0c04b503.
Lemma F_a3670 : fetch_word Asan.M.loaded_segments (0xa3670 : word) = Some W_a3670.
Proof. vm_refl. Qed.
Lemma D_a3670 : decode_any W_a3670 = Some (Load SZ8 true 10 9 192, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a3674 : bv 32 := 0x00054863.
Lemma F_a3674 : fetch_word Asan.M.loaded_segments (0xa3674 : word) = Some W_a3674.
Proof. vm_refl. Qed.
Lemma D_a3674 : decode_any W_a3674 = Some (Branch BC_LT 10 0 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a3678 : bv 32 := 0x0084b503.
Lemma F_a3678 : fetch_word Asan.M.loaded_segments (0xa3678 : word) = Some W_a3678.
Proof. vm_refl. Qed.
Lemma D_a3678 : decode_any W_a3678 = Some (Load SZ8 true 10 9 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a367c : bv 32 := 0xfff50513.
Lemma F_a367c : fetch_word Asan.M.loaded_segments (0xa367c : word) = Some W_a367c.
Proof. vm_refl. Qed.
Lemma D_a367c : decode_any W_a367c = Some (OpImm ALU_ADD 10 10 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a3680 : bv 32 := 0x00a4b423.
Lemma F_a3680 : fetch_word Asan.M.loaded_segments (0xa3680 : word) = Some W_a3680.
Proof. vm_refl. Qed.
Lemma D_a3680 : decode_any W_a3680 = Some (Store SZ8 9 10 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a3684 : bv 32 := 0x00048513.
Lemma F_a3684 : fetch_word Asan.M.loaded_segments (0xa3684 : word) = Some W_a3684.
Proof. vm_refl. Qed.
Lemma D_a3684 : decode_any W_a3684 = Some (OpImm ALU_ADD 10 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a3688 : bv 32 := 0x00000593.
Lemma F_a3688 : fetch_word Asan.M.loaded_segments (0xa3688 : word) = Some W_a3688.
Proof. vm_refl. Qed.
Lemma D_a3688 : decode_any W_a3688 = Some (OpImm ALU_ADD 11 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a368c : bv 32 := 0xd95ff0ef.
Lemma F_a368c : fetch_word Asan.M.loaded_segments (0xa368c : word) = Some W_a368c.
Proof. vm_refl. Qed.
Lemma D_a368c : decode_any W_a368c = Some (Jal 1 2096532, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a3690 : bv 32 := 0xf69f60ef.
Lemma F_a3690 : fetch_word Asan.M.loaded_segments (0xa3690 : word) = Some W_a3690.
Proof. vm_refl. Qed.
Lemma D_a3690 : decode_any W_a3690 = Some (Jal 1 2060136, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a3694 : bv 32 := 0x00000413.
Lemma F_a3694 : fetch_word Asan.M.loaded_segments (0xa3694 : word) = Some W_a3694.
Proof. vm_refl. Qed.
Lemma D_a3694 : decode_any W_a3694 = Some (OpImm ALU_ADD 8 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a3698 : bv 32 := 0x01600593.
Lemma F_a3698 : fetch_word Asan.M.loaded_segments (0xa3698 : word) = Some W_a3698.
Proof. vm_refl. Qed.
Lemma D_a3698 : decode_any W_a3698 = Some (OpImm ALU_ADD 11 0 22, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a369c : bv 32 := 0x00b52023.
Lemma F_a369c : fetch_word Asan.M.loaded_segments (0xa369c : word) = Some W_a369c.
Proof. vm_refl. Qed.
Lemma D_a369c : decode_any W_a369c = Some (Store SZ4 10 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a36a0 : bv 32 := 0x4240006f.
Lemma F_a36a0 : fetch_word Asan.M.loaded_segments (0xa36a0 : word) = Some W_a36a0.
Proof. vm_refl. Qed.
Lemma D_a36a0 : decode_any W_a36a0 = Some (Jal 0 1060, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a36a4 : bv 32 := 0x00048513.
Lemma F_a36a4 : fetch_word Asan.M.loaded_segments (0xa36a4 : word) = Some W_a36a4.
Proof. vm_refl. Qed.
Lemma D_a36a4 : decode_any W_a36a4 = Some (OpImm ALU_ADD 10 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a36a8 : bv 32 := 0xdb1ff0ef.
Lemma F_a36a8 : fetch_word Asan.M.loaded_segments (0xa36a8 : word) = Some W_a36a8.
Proof. vm_refl. Qed.
Lemma D_a36a8 : decode_any W_a36a8 = Some (Jal 1 2096560, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a36ac : bv 32 := 0xfdf57593.
Lemma F_a36ac : fetch_word Asan.M.loaded_segments (0xa36ac : word) = Some W_a36ac.
Proof. vm_refl. Qed.
Lemma D_a36ac : decode_any W_a36ac = Some (OpImm ALU_AND 11 10 4063, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a36b0 : bv 32 := 0x05800613.
Lemma F_a36b0 : fetch_word Asan.M.loaded_segments (0xa36b0 : word) = Some W_a36b0.
Proof. vm_refl. Qed.
Lemma D_a36b0 : decode_any W_a36b0 = Some (OpImm ALU_ADD 12 0 88, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a36b4 : bv 32 := 0xf8c582e3.
Lemma F_a36b4 : fetch_word Asan.M.loaded_segments (0xa36b4 : word) = Some W_a36b4.
Proof. vm_refl. Qed.
Lemma D_a36b4 : decode_any W_a36b4 = Some (Branch BC_EQ 11 12 8068, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a36b8 : bv 32 := 0x12090663.
Lemma F_a36b8 : fetch_word Asan.M.loaded_segments (0xa36b8 : word) = Some W_a36b8.
Proof. vm_refl. Qed.
Lemma D_a36b8 : decode_any W_a36b8 = Some (Branch BC_EQ 18 0 300, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a36bc : bv 32 := 0x00a00593.
Lemma F_a36bc : fetch_word Asan.M.loaded_segments (0xa36bc : word) = Some W_a36bc.
Proof. vm_refl. Qed.
Lemma D_a36bc : decode_any W_a36bc = Some (OpImm ALU_ADD 11 0 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a36c0 : bv 32 := 0x12b91463.
Lemma F_a36c0 : fetch_word Asan.M.loaded_segments (0xa36c0 : word) = Some W_a36c0.
Proof. vm_refl. Qed.
Lemma D_a36c0 : decode_any W_a36c0 = Some (Branch BC_NE 18 11 296, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a36c4 : bv 32 := 0xfd050a9b.
Lemma F_a36c4 : fetch_word Asan.M.loaded_segments (0xa36c4 : word) = Some W_a36c4.
Proof. vm_refl. Qed.
Lemma D_a36c4 : decode_any W_a36c4 = Some (OpImm32 21 10 4048, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a36c8 : bv 32 := 0x00000993.
Lemma F_a36c8 : fetch_word Asan.M.loaded_segments (0xa36c8 : word) = Some W_a36c8.
Proof. vm_refl. Qed.
Lemma D_a36c8 : decode_any W_a36c8 = Some (OpImm ALU_ADD 19 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a36cc : bv 32 := 0x00900913.
Lemma F_a36cc : fetch_word Asan.M.loaded_segments (0xa36cc : word) = Some W_a36cc.
Proof. vm_refl. Qed.
Lemma D_a36cc : decode_any W_a36cc = Some (OpImm ALU_ADD 18 0 9, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a36d0 : bv 32 := 0x07596063.
Lemma F_a36d0 : fetch_word Asan.M.loaded_segments (0xa36d0 : word) = Some W_a36d0.
Proof. vm_refl. Qed.
Lemma D_a36d0 : decode_any W_a36d0 = Some (Branch BC_LTU 18 21 96, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a36d4 : bv 32 := 0x00a00b13.
Lemma F_a36d4 : fetch_word Asan.M.loaded_segments (0xa36d4 : word) = Some W_a36d4.
Proof. vm_refl. Qed.
Lemma D_a36d4 : decode_any W_a36d4 = Some (OpImm ALU_ADD 22 0 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a36d8 : bv 32 := 0x1999a537.
Lemma F_a36d8 : fetch_word Asan.M.loaded_segments (0xa36d8 : word) = Some W_a36d8.
Proof. vm_refl. Qed.
Lemma D_a36d8 : decode_any W_a36d8 = Some (Lui 10 104858, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a36dc : bv 32 := 0x99950b9b.
Lemma F_a36dc : fetch_word Asan.M.loaded_segments (0xa36dc : word) = Some W_a36dc.
Proof. vm_refl. Qed.
Lemma D_a36dc : decode_any W_a36dc = Some (OpImm32 23 10 2457, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a36e0 : bv 32 := 0x0200006f.
Lemma F_a36e0 : fetch_word Asan.M.loaded_segments (0xa36e0 : word) = Some W_a36e0.
Proof. vm_refl. Qed.
Lemma D_a36e0 : decode_any W_a36e0 = Some (Jal 0 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a36e4 : bv 32 := 0x00048513.
Lemma F_a36e4 : fetch_word Asan.M.loaded_segments (0xa36e4 : word) = Some W_a36e4.
Proof. vm_refl. Qed.
Lemma D_a36e4 : decode_any W_a36e4 = Some (OpImm ALU_ADD 10 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a36e8 : bv 32 := 0xd71ff0ef.
Lemma F_a36e8 : fetch_word Asan.M.loaded_segments (0xa36e8 : word) = Some W_a36e8.
Proof. vm_refl. Qed.
Lemma D_a36e8 : decode_any W_a36e8 = Some (Jal 1 2096496, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a36ec : bv 32 := 0x036985b3.
Lemma F_a36ec : fetch_word Asan.M.loaded_segments (0xa36ec : word) = Some W_a36ec.
Proof. vm_refl. Qed.
Lemma D_a36ec : decode_any W_a36ec = Some (Mul M_MUL 11 19 22, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a36f0 : bv 32 := 0x015589bb.
Lemma F_a36f0 : fetch_word Asan.M.loaded_segments (0xa36f0 : word) = Some W_a36f0.
Proof. vm_refl. Qed.
Lemma D_a36f0 : decode_any W_a36f0 = Some (Op32 ALU_ADD 19 11 21, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a36f4 : bv 32 := 0xfd050a9b.
Lemma F_a36f4 : fetch_word Asan.M.loaded_segments (0xa36f4 : word) = Some W_a36f4.
Proof. vm_refl. Qed.
Lemma D_a36f4 : decode_any W_a36f4 = Some (OpImm32 21 10 4048, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a36f8 : bv 32 := 0x03596863.
Lemma F_a36f8 : fetch_word Asan.M.loaded_segments (0xa36f8 : word) = Some W_a36f8.
Proof. vm_refl. Qed.
Lemma D_a36f8 : decode_any W_a36f8 = Some (Branch BC_LTU 18 21 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a36fc : bv 32 := 0x0379f663.
Lemma F_a36fc : fetch_word Asan.M.loaded_segments (0xa36fc : word) = Some W_a36fc.
Proof. vm_refl. Qed.
Lemma D_a36fc : decode_any W_a36fc = Some (Branch BC_GEU 19 23 44, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a3700 : bv 32 := 0x0084b503.
Lemma F_a3700 : fetch_word Asan.M.loaded_segments (0xa3700 : word) = Some W_a3700.
Proof. vm_refl. Qed.
Lemma D_a3700 : decode_any W_a3700 = Some (Load SZ8 true 10 9 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a3704 : bv 32 := 0x0b84b583.
Lemma F_a3704 : fetch_word Asan.M.loaded_segments (0xa3704 : word) = Some W_a3704.
Proof. vm_refl. Qed.
Lemma D_a3704 : decode_any W_a3704 = Some (Load SZ8 true 11 9 184, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a3708 : bv 32 := 0xfcb50ee3.
Lemma F_a3708 : fetch_word Asan.M.loaded_segments (0xa3708 : word) = Some W_a3708.
Proof. vm_refl. Qed.
Lemma D_a3708 : decode_any W_a3708 = Some (Branch BC_EQ 10 11 8156, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a370c : bv 32 := 0x00150593.
Lemma F_a370c : fetch_word Asan.M.loaded_segments (0xa370c : word) = Some W_a370c.
Proof. vm_refl. Qed.
Lemma D_a370c : decode_any W_a370c = Some (OpImm ALU_ADD 11 10 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a3710 : bv 32 := 0x00b4b423.
Lemma F_a3710 : fetch_word Asan.M.loaded_segments (0xa3710 : word) = Some W_a3710.
Proof. vm_refl. Qed.
Lemma D_a3710 : decode_any W_a3710 = Some (Store SZ8 9 11 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a3714 : bv 32 := 0x00054503.
Lemma F_a3714 : fetch_word Asan.M.loaded_segments (0xa3714 : word) = Some W_a3714.
Proof. vm_refl. Qed.
Lemma D_a3714 : decode_any W_a3714 = Some (Load SZ1 false 10 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a3718 : bv 32 := 0x036985b3.
Lemma F_a3718 : fetch_word Asan.M.loaded_segments (0xa3718 : word) = Some W_a3718.
Proof. vm_refl. Qed.
Lemma D_a3718 : decode_any W_a3718 = Some (Mul M_MUL 11 19 22, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a371c : bv 32 := 0x015589bb.
Lemma F_a371c : fetch_word Asan.M.loaded_segments (0xa371c : word) = Some W_a371c.
Proof. vm_refl. Qed.
Lemma D_a371c : decode_any W_a371c = Some (Op32 ALU_ADD 19 11 21, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a3720 : bv 32 := 0xfd050a9b.
Lemma F_a3720 : fetch_word Asan.M.loaded_segments (0xa3720 : word) = Some W_a3720.
Proof. vm_refl. Qed.
Lemma D_a3720 : decode_any W_a3720 = Some (OpImm32 21 10 4048, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a3724 : bv 32 := 0xfd597ce3.
Lemma F_a3724 : fetch_word Asan.M.loaded_segments (0xa3724 : word) = Some W_a3724.
Proof. vm_refl. Qed.
Lemma D_a3724 : decode_any W_a3724 = Some (Branch BC_GEU 18 21 8152, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a3728 : bv 32 := 0x02099993.
Lemma F_a3728 : fetch_word Asan.M.loaded_segments (0xa3728 : word) = Some W_a3728.
Proof. vm_refl. Qed.
Lemma D_a3728 : decode_any W_a3728 = Some (ShiftImm ALU_SLL 19 19 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a372c : bv 32 := 0x0209d993.
Lemma F_a372c : fetch_word Asan.M.loaded_segments (0xa372c : word) = Some W_a372c.
Proof. vm_refl. Qed.
Lemma D_a372c : decode_any W_a372c = Some (ShiftImm ALU_SRL 19 19 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a3730 : bv 32 := 0x2d596463.
Lemma F_a3730 : fetch_word Asan.M.loaded_segments (0xa3730 : word) = Some W_a3730.
Proof. vm_refl. Qed.
Lemma D_a3730 : decode_any W_a3730 = Some (Branch BC_LTU 18 21 712, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a3734 : bv 32 := 0xfff6d517.
Lemma F_a3734 : fetch_word Asan.M.loaded_segments (0xa3734 : word) = Some W_a3734.
Proof. vm_refl. Qed.
Lemma D_a3734 : decode_any W_a3734 = Some (Auipc 10 1048429, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a3738 : bv 32 := 0xbfc53b03.
Lemma F_a3738 : fetch_word Asan.M.loaded_segments (0xa3738 : word) = Some W_a3738.
Proof. vm_refl. Qed.
Lemma D_a3738 : decode_any W_a3738 = Some (Load SZ8 true 22 10 3068, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a373c : bv 32 := 0x00a00513.
Lemma F_a373c : fetch_word Asan.M.loaded_segments (0xa373c : word) = Some W_a373c.
Proof. vm_refl. Qed.
Lemma D_a373c : decode_any W_a373c = Some (OpImm ALU_ADD 10 0 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a3740 : bv 32 := 0x02a98c33.
Lemma F_a3740 : fetch_word Asan.M.loaded_segments (0xa3740 : word) = Some W_a3740.
Proof. vm_refl. Qed.
Lemma D_a3740 : decode_any W_a3740 = Some (Mul M_MUL 24 19 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a3744 : bv 32 := 0x00900b93.
Lemma F_a3744 : fetch_word Asan.M.loaded_segments (0xa3744 : word) = Some W_a3744.
Proof. vm_refl. Qed.
Lemma D_a3744 : decode_any W_a3744 = Some (OpImm ALU_ADD 23 0 9, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a3748 : bv 32 := 0x0084b503.
Lemma F_a3748 : fetch_word Asan.M.loaded_segments (0xa3748 : word) = Some W_a3748.
Proof. vm_refl. Qed.
Lemma D_a3748 : decode_any W_a3748 = Some (Load SZ8 true 10 9 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a374c : bv 32 := 0x0b84b583.
Lemma F_a374c : fetch_word Asan.M.loaded_segments (0xa374c : word) = Some W_a374c.
Proof. vm_refl. Qed.
Lemma D_a374c : decode_any W_a374c = Some (Load SZ8 true 11 9 184, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a3750 : bv 32 := 0x02b50063.
Lemma F_a3750 : fetch_word Asan.M.loaded_segments (0xa3750 : word) = Some W_a3750.
Proof. vm_refl. Qed.
Lemma D_a3750 : decode_any W_a3750 = Some (Branch BC_EQ 10 11 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a3754 : bv 32 := 0x00150593.
Lemma F_a3754 : fetch_word Asan.M.loaded_segments (0xa3754 : word) = Some W_a3754.
Proof. vm_refl. Qed.
Lemma D_a3754 : decode_any W_a3754 = Some (OpImm ALU_ADD 11 10 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a3758 : bv 32 := 0x00b4b423.
Lemma F_a3758 : fetch_word Asan.M.loaded_segments (0xa3758 : word) = Some W_a3758.
Proof. vm_refl. Qed.
Lemma D_a3758 : decode_any W_a3758 = Some (Store SZ8 9 11 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a375c : bv 32 := 0x00054503.
Lemma F_a375c : fetch_word Asan.M.loaded_segments (0xa375c : word) = Some W_a375c.
Proof. vm_refl. Qed.
Lemma D_a375c : decode_any W_a375c = Some (Load SZ1 false 10 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a3760 : bv 32 := 0x015c09b3.
Lemma F_a3760 : fetch_word Asan.M.loaded_segments (0xa3760 : word) = Some W_a3760.
Proof. vm_refl. Qed.
Lemma D_a3760 : decode_any W_a3760 = Some (Op ALU_ADD 19 24 21, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a3764 : bv 32 := 0xfd050a9b.
Lemma F_a3764 : fetch_word Asan.M.loaded_segments (0xa3764 : word) = Some W_a3764.
Proof. vm_refl. Qed.
Lemma D_a3764 : decode_any W_a3764 = Some (OpImm32 21 10 4048, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a3768 : bv 32 := 0x015bfe63.
Lemma F_a3768 : fetch_word Asan.M.loaded_segments (0xa3768 : word) = Some W_a3768.
Proof. vm_refl. Qed.
Lemma D_a3768 : decode_any W_a3768 = Some (Branch BC_GEU 23 21 28, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a376c : bv 32 := 0x26c0006f.
Lemma F_a376c : fetch_word Asan.M.loaded_segments (0xa376c : word) = Some W_a376c.
Proof. vm_refl. Qed.
Lemma D_a376c : decode_any W_a376c = Some (Jal 0 620, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a3770 : bv 32 := 0x00048513.
Lemma F_a3770 : fetch_word Asan.M.loaded_segments (0xa3770 : word) = Some W_a3770.
Proof. vm_refl. Qed.
Lemma D_a3770 : decode_any W_a3770 = Some (OpImm ALU_ADD 10 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a3774 : bv 32 := 0xce5ff0ef.
Lemma F_a3774 : fetch_word Asan.M.loaded_segments (0xa3774 : word) = Some W_a3774.
Proof. vm_refl. Qed.
Lemma D_a3774 : decode_any W_a3774 = Some (Jal 1 2096356, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a3778 : bv 32 := 0x015c09b3.
Lemma F_a3778 : fetch_word Asan.M.loaded_segments (0xa3778 : word) = Some W_a3778.
Proof. vm_refl. Qed.
Lemma D_a3778 : decode_any W_a3778 = Some (Op ALU_ADD 19 24 21, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a377c : bv 32 := 0xfd050a9b.
Lemma F_a377c : fetch_word Asan.M.loaded_segments (0xa377c : word) = Some W_a377c.
Proof. vm_refl. Qed.
Lemma D_a377c : decode_any W_a377c = Some (OpImm32 21 10 4048, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a3780 : bv 32 := 0x255bec63.
Lemma F_a3780 : fetch_word Asan.M.loaded_segments (0xa3780 : word) = Some W_a3780.
Proof. vm_refl. Qed.
Lemma D_a3780 : decode_any W_a3780 = Some (Branch BC_LTU 23 21 600, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a3784 : bv 32 := 0x2569fa63.
Lemma F_a3784 : fetch_word Asan.M.loaded_segments (0xa3784 : word) = Some W_a3784.
Proof. vm_refl. Qed.
Lemma D_a3784 : decode_any W_a3784 = Some (Branch BC_GEU 19 22 596, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a3788 : bv 32 := 0x00a00913.
Lemma F_a3788 : fetch_word Asan.M.loaded_segments (0xa3788 : word) = Some W_a3788.
Proof. vm_refl. Qed.
Lemma D_a3788 : decode_any W_a3788 = Some (OpImm ALU_ADD 18 0 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a378c : bv 32 := 0x03298c33.
Lemma F_a378c : fetch_word Asan.M.loaded_segments (0xa378c : word) = Some W_a378c.
Proof. vm_refl. Qed.
Lemma D_a378c : decode_any W_a378c = Some (Mul M_MUL 24 19 18, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a3790 : bv 32 := 0xfffac593.
Lemma F_a3790 : fetch_word Asan.M.loaded_segments (0xa3790 : word) = Some W_a3790.
Proof. vm_refl. Qed.
Lemma D_a3790 : decode_any W_a3790 = Some (OpImm ALU_XOR 11 21 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a3794 : bv 32 := 0xfb85fae3.
Lemma F_a3794 : fetch_word Asan.M.loaded_segments (0xa3794 : word) = Some W_a3794.
Proof. vm_refl. Qed.
Lemma D_a3794 : decode_any W_a3794 = Some (Branch BC_GEU 11 24 8116, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a3798 : bv 32 := 0x24c0006f.
Lemma F_a3798 : fetch_word Asan.M.loaded_segments (0xa3798 : word) = Some W_a3798.
Proof. vm_refl. Qed.
Lemma D_a3798 : decode_any W_a3798 = Some (Jal 0 588, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a379c : bv 32 := 0x00048513.
Lemma F_a379c : fetch_word Asan.M.loaded_segments (0xa379c : word) = Some W_a379c.
Proof. vm_refl. Qed.
Lemma D_a379c : decode_any W_a379c = Some (OpImm ALU_ADD 10 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a37a0 : bv 32 := 0xcb9ff0ef.
Lemma F_a37a0 : fetch_word Asan.M.loaded_segments (0xa37a0 : word) = Some W_a37a0.
Proof. vm_refl. Qed.
Lemma D_a37a0 : decode_any W_a37a0 = Some (Jal 1 2096312, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a37a4 : bv 32 := 0xfff80597.
Lemma F_a37a4 : fetch_word Asan.M.loaded_segments (0xa37a4 : word) = Some W_a37a4.
Proof. vm_refl. Qed.
Lemma D_a37a4 : decode_any W_a37a4 = Some (Auipc 11 1048448, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a37a8 : bv 32 := 0x01c58593.
Lemma F_a37a8 : fetch_word Asan.M.loaded_segments (0xa37a8 : word) = Some W_a37a8.
Proof. vm_refl. Qed.
Lemma D_a37a8 : decode_any W_a37a8 = Some (OpImm ALU_ADD 11 11 28, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a37ac : bv 32 := 0x00a585b3.
Lemma F_a37ac : fetch_word Asan.M.loaded_segments (0xa37ac : word) = Some W_a37ac.
Proof. vm_refl. Qed.
Lemma D_a37ac : decode_any W_a37ac = Some (Op ALU_ADD 11 11 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a37b0 : bv 32 := 0x0015c583.
Lemma F_a37b0 : fetch_word Asan.M.loaded_segments (0xa37b0 : word) = Some W_a37b0.
Proof. vm_refl. Qed.
Lemma D_a37b0 : decode_any W_a37b0 = Some (Load SZ1 false 11 11 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a37b4 : bv 32 := 0x01000913.
Lemma F_a37b4 : fetch_word Asan.M.loaded_segments (0xa37b4 : word) = Some W_a37b4.
Proof. vm_refl. Qed.
Lemma D_a37b4 : decode_any W_a37b4 = Some (OpImm ALU_ADD 18 0 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a37b8 : bv 32 := 0x0325e863.
Lemma F_a37b8 : fetch_word Asan.M.loaded_segments (0xa37b8 : word) = Some W_a37b8.
Proof. vm_refl. Qed.
Lemma D_a37b8 : decode_any W_a37b8 = Some (Branch BC_LTU 11 18 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a37bc : bv 32 := 0x0c04b503.
Lemma F_a37bc : fetch_word Asan.M.loaded_segments (0xa37bc : word) = Some W_a37bc.
Proof. vm_refl. Qed.
Lemma D_a37bc : decode_any W_a37bc = Some (Load SZ8 true 10 9 192, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a37c0 : bv 32 := 0x2e054863.
Lemma F_a37c0 : fetch_word Asan.M.loaded_segments (0xa37c0 : word) = Some W_a37c0.
Proof. vm_refl. Qed.
Lemma D_a37c0 : decode_any W_a37c0 = Some (Branch BC_LT 10 0 752, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a37c4 : bv 32 := 0x0084b503.
Lemma F_a37c4 : fetch_word Asan.M.loaded_segments (0xa37c4 : word) = Some W_a37c4.
Proof. vm_refl. Qed.
Lemma D_a37c4 : decode_any W_a37c4 = Some (Load SZ8 true 10 9 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a37c8 : bv 32 := 0xfff50593.
Lemma F_a37c8 : fetch_word Asan.M.loaded_segments (0xa37c8 : word) = Some W_a37c8.
Proof. vm_refl. Qed.
Lemma D_a37c8 : decode_any W_a37c8 = Some (OpImm ALU_ADD 11 10 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a37cc : bv 32 := 0x00b4b423.
Lemma F_a37cc : fetch_word Asan.M.loaded_segments (0xa37cc : word) = Some W_a37cc.
Proof. vm_refl. Qed.
Lemma D_a37cc : decode_any W_a37cc = Some (Store SZ8 9 11 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a37d0 : bv 32 := 0x2e098263.
Lemma F_a37d0 : fetch_word Asan.M.loaded_segments (0xa37d0 : word) = Some W_a37d0.
Proof. vm_refl. Qed.
Lemma D_a37d0 : decode_any W_a37d0 = Some (Branch BC_EQ 19 0 740, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a37d4 : bv 32 := 0x00000413.
Lemma F_a37d4 : fetch_word Asan.M.loaded_segments (0xa37d4 : word) = Some W_a37d4.
Proof. vm_refl. Qed.
Lemma D_a37d4 : decode_any W_a37d4 = Some (OpImm ALU_ADD 8 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a37d8 : bv 32 := 0xffe50513.
Lemma F_a37d8 : fetch_word Asan.M.loaded_segments (0xa37d8 : word) = Some W_a37d8.
Proof. vm_refl. Qed.
Lemma D_a37d8 : decode_any W_a37d8 = Some (OpImm ALU_ADD 10 10 4094, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a37dc : bv 32 := 0x00a4b423.
Lemma F_a37dc : fetch_word Asan.M.loaded_segments (0xa37dc : word) = Some W_a37dc.
Proof. vm_refl. Qed.
Lemma D_a37dc : decode_any W_a37dc = Some (Store SZ8 9 10 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a37e0 : bv 32 := 0x2e40006f.
Lemma F_a37e0 : fetch_word Asan.M.loaded_segments (0xa37e0 : word) = Some W_a37e0.
Proof. vm_refl. Qed.
Lemma D_a37e0 : decode_any W_a37e0 = Some (Jal 0 740, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a37e4 : bv 32 := 0x00800913.
Lemma F_a37e4 : fetch_word Asan.M.loaded_segments (0xa37e4 : word) = Some W_a37e4.
Proof. vm_refl. Qed.
Lemma D_a37e4 : decode_any W_a37e4 = Some (OpImm ALU_ADD 18 0 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a37e8 : bv 32 := 0xfff9059b.
Lemma F_a37e8 : fetch_word Asan.M.loaded_segments (0xa37e8 : word) = Some W_a37e8.
Proof. vm_refl. Qed.
Lemma D_a37e8 : decode_any W_a37e8 = Some (OpImm32 11 18 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a37ec : bv 32 := 0x00b975b3.
Lemma F_a37ec : fetch_word Asan.M.loaded_segments (0xa37ec : word) = Some W_a37ec.
Proof. vm_refl. Qed.
Lemma D_a37ec : decode_any W_a37ec = Some (Op ALU_AND 11 18 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a37f0 : bv 32 := 0x0e059e63.
Lemma F_a37f0 : fetch_word Asan.M.loaded_segments (0xa37f0 : word) = Some W_a37f0.
Proof. vm_refl. Qed.
Lemma D_a37f0 : decode_any W_a37f0 = Some (Branch BC_NE 11 0 252, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a37f4 : bv 32 := 0x01700593.
Lemma F_a37f4 : fetch_word Asan.M.loaded_segments (0xa37f4 : word) = Some W_a37f4.
Proof. vm_refl. Qed.
Lemma D_a37f4 : decode_any W_a37f4 = Some (OpImm ALU_ADD 11 0 23, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a37f8 : bv 32 := 0xfff80617.
Lemma F_a37f8 : fetch_word Asan.M.loaded_segments (0xa37f8 : word) = Some W_a37f8.
Proof. vm_refl. Qed.
Lemma D_a37f8 : decode_any W_a37f8 = Some (Auipc 12 1048448, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a37fc : bv 32 := 0xfff80697.
Lemma F_a37fc : fetch_word Asan.M.loaded_segments (0xa37fc : word) = Some W_a37fc.
Proof. vm_refl. Qed.
Lemma D_a37fc : decode_any W_a37fc = Some (Auipc 13 1048448, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a3800 : bv 32 := 0x02b905b3.
Lemma F_a3800 : fetch_word Asan.M.loaded_segments (0xa3800 : word) = Some W_a3800.
Proof. vm_refl. Qed.
Lemma D_a3800 : decode_any W_a3800 = Some (Mul M_MUL 11 18 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a3804 : bv 32 := 0x0c960613.
Lemma F_a3804 : fetch_word Asan.M.loaded_segments (0xa3804 : word) = Some W_a3804.
Proof. vm_refl. Qed.
Lemma D_a3804 : decode_any W_a3804 = Some (OpImm ALU_ADD 12 12 201, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a3808 : bv 32 := 0xfc468a93.
Lemma F_a3808 : fetch_word Asan.M.loaded_segments (0xa3808 : word) = Some W_a3808.
Proof. vm_refl. Qed.
Lemma D_a3808 : decode_any W_a3808 = Some (OpImm ALU_ADD 21 13 4036, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a380c : bv 32 := 0x03859593.
Lemma F_a380c : fetch_word Asan.M.loaded_segments (0xa380c : word) = Some W_a380c.
Proof. vm_refl. Qed.
Lemma D_a380c : decode_any W_a380c = Some (ShiftImm ALU_SLL 11 11 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a3810 : bv 32 := 0x03d5d593.
Lemma F_a3810 : fetch_word Asan.M.loaded_segments (0xa3810 : word) = Some W_a3810.
Proof. vm_refl. Qed.
Lemma D_a3810 : decode_any W_a3810 = Some (ShiftImm ALU_SRL 11 11 61, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a3814 : bv 32 := 0x00b605b3.
Lemma F_a3814 : fetch_word Asan.M.loaded_segments (0xa3814 : word) = Some W_a3814.
Proof. vm_refl. Qed.
Lemma D_a3814 : decode_any W_a3814 = Some (Op ALU_ADD 11 12 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a3818 : bv 32 := 0x00aa8633.
Lemma F_a3818 : fetch_word Asan.M.loaded_segments (0xa3818 : word) = Some W_a3818.
Proof. vm_refl. Qed.
Lemma D_a3818 : decode_any W_a3818 = Some (Op ALU_ADD 12 21 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a381c : bv 32 := 0x00164b83.
Lemma F_a381c : fetch_word Asan.M.loaded_segments (0xa381c : word) = Some W_a381c.
Proof. vm_refl. Qed.
Lemma D_a381c : decode_any W_a381c = Some (Load SZ1 false 23 12 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a3820 : bv 32 := 0x0005cb03.
Lemma F_a3820 : fetch_word Asan.M.loaded_segments (0xa3820 : word) = Some W_a3820.
Proof. vm_refl. Qed.
Lemma D_a3820 : decode_any W_a3820 = Some (Load SZ1 false 22 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a3824 : bv 32 := 0x00000993.
Lemma F_a3824 : fetch_word Asan.M.loaded_segments (0xa3824 : word) = Some W_a3824.
Proof. vm_refl. Qed.
Lemma D_a3824 : decode_any W_a3824 = Some (OpImm ALU_ADD 19 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a3828 : bv 32 := 0x072bf063.
Lemma F_a3828 : fetch_word Asan.M.loaded_segments (0xa3828 : word) = Some W_a3828.
Proof. vm_refl. Qed.
Lemma D_a3828 : decode_any W_a3828 = Some (Branch BC_GEU 23 18 96, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a382c : bv 32 := 0x0280006f.
Lemma F_a382c : fetch_word Asan.M.loaded_segments (0xa382c : word) = Some W_a382c.
Proof. vm_refl. Qed.
Lemma D_a382c : decode_any W_a382c = Some (Jal 0 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a3830 : bv 32 := 0x00048513.
Lemma F_a3830 : fetch_word Asan.M.loaded_segments (0xa3830 : word) = Some W_a3830.
Proof. vm_refl. Qed.
Lemma D_a3830 : decode_any W_a3830 = Some (OpImm ALU_ADD 10 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a3834 : bv 32 := 0xc25ff0ef.
Lemma F_a3834 : fetch_word Asan.M.loaded_segments (0xa3834 : word) = Some W_a3834.
Proof. vm_refl. Qed.
Lemma D_a3834 : decode_any W_a3834 = Some (Jal 1 2096164, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a3838 : bv 32 := 0x016995bb.
Lemma F_a3838 : fetch_word Asan.M.loaded_segments (0xa3838 : word) = Some W_a3838.
Proof. vm_refl. Qed.
Lemma D_a3838 : decode_any W_a3838 = Some (Op32 ALU_SLL 11 19 22, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a383c : bv 32 := 0x00aa8633.
Lemma F_a383c : fetch_word Asan.M.loaded_segments (0xa383c : word) = Some W_a383c.
Proof. vm_refl. Qed.
Lemma D_a383c : decode_any W_a383c = Some (Op ALU_ADD 12 21 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a3840 : bv 32 := 0x00bbe9b3.
Lemma F_a3840 : fetch_word Asan.M.loaded_segments (0xa3840 : word) = Some W_a3840.
Proof. vm_refl. Qed.
Lemma D_a3840 : decode_any W_a3840 = Some (Op ALU_OR 19 23 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a3844 : bv 32 := 0x00164b83.
Lemma F_a3844 : fetch_word Asan.M.loaded_segments (0xa3844 : word) = Some W_a3844.
Proof. vm_refl. Qed.
Lemma D_a3844 : decode_any W_a3844 = Some (Load SZ1 false 23 12 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a3848 : bv 32 := 0x032bfc63.
Lemma F_a3848 : fetch_word Asan.M.loaded_segments (0xa3848 : word) = Some W_a3848.
Proof. vm_refl. Qed.
Lemma D_a3848 : decode_any W_a3848 = Some (Branch BC_GEU 23 18 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a384c : bv 32 := 0x01b5d59b.
Lemma F_a384c : fetch_word Asan.M.loaded_segments (0xa384c : word) = Some W_a384c.
Proof. vm_refl. Qed.
Lemma D_a384c : decode_any W_a384c = Some (ShiftImm32 ALU_SRL 11 11 27, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a3850 : bv 32 := 0x02059863.
Lemma F_a3850 : fetch_word Asan.M.loaded_segments (0xa3850 : word) = Some W_a3850.
Proof. vm_refl. Qed.
Lemma D_a3850 : decode_any W_a3850 = Some (Branch BC_NE 11 0 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a3854 : bv 32 := 0x0084b503.
Lemma F_a3854 : fetch_word Asan.M.loaded_segments (0xa3854 : word) = Some W_a3854.
Proof. vm_refl. Qed.
Lemma D_a3854 : decode_any W_a3854 = Some (Load SZ8 true 10 9 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a3858 : bv 32 := 0x0b84b583.
Lemma F_a3858 : fetch_word Asan.M.loaded_segments (0xa3858 : word) = Some W_a3858.
Proof. vm_refl. Qed.
Lemma D_a3858 : decode_any W_a3858 = Some (Load SZ8 true 11 9 184, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a385c : bv 32 := 0xfcb50ae3.
Lemma F_a385c : fetch_word Asan.M.loaded_segments (0xa385c : word) = Some W_a385c.
Proof. vm_refl. Qed.
Lemma D_a385c : decode_any W_a385c = Some (Branch BC_EQ 10 11 8148, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a3860 : bv 32 := 0x00150593.
Lemma F_a3860 : fetch_word Asan.M.loaded_segments (0xa3860 : word) = Some W_a3860.
Proof. vm_refl. Qed.
Lemma D_a3860 : decode_any W_a3860 = Some (OpImm ALU_ADD 11 10 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a3864 : bv 32 := 0x00b4b423.
Lemma F_a3864 : fetch_word Asan.M.loaded_segments (0xa3864 : word) = Some W_a3864.
Proof. vm_refl. Qed.
Lemma D_a3864 : decode_any W_a3864 = Some (Store SZ8 9 11 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a3868 : bv 32 := 0x00054503.
Lemma F_a3868 : fetch_word Asan.M.loaded_segments (0xa3868 : word) = Some W_a3868.
Proof. vm_refl. Qed.
Lemma D_a3868 : decode_any W_a3868 = Some (Load SZ1 false 10 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a386c : bv 32 := 0x016995bb.
Lemma F_a386c : fetch_word Asan.M.loaded_segments (0xa386c : word) = Some W_a386c.
Proof. vm_refl. Qed.
Lemma D_a386c : decode_any W_a386c = Some (Op32 ALU_SLL 11 19 22, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a3870 : bv 32 := 0x00aa8633.
Lemma F_a3870 : fetch_word Asan.M.loaded_segments (0xa3870 : word) = Some W_a3870.
Proof. vm_refl. Qed.
Lemma D_a3870 : decode_any W_a3870 = Some (Op ALU_ADD 12 21 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a3874 : bv 32 := 0x00bbe9b3.
Lemma F_a3874 : fetch_word Asan.M.loaded_segments (0xa3874 : word) = Some W_a3874.
Proof. vm_refl. Qed.
Lemma D_a3874 : decode_any W_a3874 = Some (Op ALU_OR 19 23 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a3878 : bv 32 := 0x00164b83.
Lemma F_a3878 : fetch_word Asan.M.loaded_segments (0xa3878 : word) = Some W_a3878.
Proof. vm_refl. Qed.
Lemma D_a3878 : decode_any W_a3878 = Some (Load SZ1 false 23 12 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a387c : bv 32 := 0xfd2be8e3.
Lemma F_a387c : fetch_word Asan.M.loaded_segments (0xa387c : word) = Some W_a387c.
Proof. vm_refl. Qed.
Lemma D_a387c : decode_any W_a387c = Some (Branch BC_LTU 23 18 8144, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a3880 : bv 32 := 0x02099993.
Lemma F_a3880 : fetch_word Asan.M.loaded_segments (0xa3880 : word) = Some W_a3880.
Proof. vm_refl. Qed.
Lemma D_a3880 : decode_any W_a3880 = Some (ShiftImm ALU_SLL 19 19 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a3884 : bv 32 := 0x0209d993.
Lemma F_a3884 : fetch_word Asan.M.loaded_segments (0xa3884 : word) = Some W_a3884.
Proof. vm_refl. Qed.
Lemma D_a3884 : decode_any W_a3884 = Some (ShiftImm ALU_SRL 19 19 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a3888 : bv 32 := 0x152bfe63.
Lemma F_a3888 : fetch_word Asan.M.loaded_segments (0xa3888 : word) = Some W_a3888.
Proof. vm_refl. Qed.
Lemma D_a3888 : decode_any W_a3888 = Some (Branch BC_GEU 23 18 348, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a388c : bv 32 := 0xfff00593.
Lemma F_a388c : fetch_word Asan.M.loaded_segments (0xa388c : word) = Some W_a388c.
Proof. vm_refl. Qed.
Lemma D_a388c : decode_any W_a388c = Some (OpImm ALU_ADD 11 0 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a3890 : bv 32 := 0x0165dc33.
Lemma F_a3890 : fetch_word Asan.M.loaded_segments (0xa3890 : word) = Some W_a3890.
Proof. vm_refl. Qed.
Lemma D_a3890 : decode_any W_a3890 = Some (Op ALU_SRL 24 11 22, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a3894 : bv 32 := 0x033c7463.
Lemma F_a3894 : fetch_word Asan.M.loaded_segments (0xa3894 : word) = Some W_a3894.
Proof. vm_refl. Qed.
Lemma D_a3894 : decode_any W_a3894 = Some (Branch BC_GEU 24 19 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a3898 : bv 32 := 0x14c0006f.
Lemma F_a3898 : fetch_word Asan.M.loaded_segments (0xa3898 : word) = Some W_a3898.
Proof. vm_refl. Qed.
Lemma D_a3898 : decode_any W_a3898 = Some (Jal 0 332, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a389c : bv 32 := 0x00048513.
Lemma F_a389c : fetch_word Asan.M.loaded_segments (0xa389c : word) = Some W_a389c.
Proof. vm_refl. Qed.
Lemma D_a389c : decode_any W_a389c = Some (OpImm ALU_ADD 10 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a38a0 : bv 32 := 0xbb9ff0ef.
Lemma F_a38a0 : fetch_word Asan.M.loaded_segments (0xa38a0 : word) = Some W_a38a0.
Proof. vm_refl. Qed.
Lemma D_a38a0 : decode_any W_a38a0 = Some (Jal 1 2096056, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a38a4 : bv 32 := 0x016995b3.
Lemma F_a38a4 : fetch_word Asan.M.loaded_segments (0xa38a4 : word) = Some W_a38a4.
Proof. vm_refl. Qed.
Lemma D_a38a4 : decode_any W_a38a4 = Some (Op ALU_SLL 11 19 22, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a38a8 : bv 32 := 0x0175e9b3.
Lemma F_a38a8 : fetch_word Asan.M.loaded_segments (0xa38a8 : word) = Some W_a38a8.
Proof. vm_refl. Qed.
Lemma D_a38a8 : decode_any W_a38a8 = Some (Op ALU_OR 19 11 23, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a38ac : bv 32 := 0x00aa85b3.
Lemma F_a38ac : fetch_word Asan.M.loaded_segments (0xa38ac : word) = Some W_a38ac.
Proof. vm_refl. Qed.
Lemma D_a38ac : decode_any W_a38ac = Some (Op ALU_ADD 11 21 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a38b0 : bv 32 := 0x0015cb83.
Lemma F_a38b0 : fetch_word Asan.M.loaded_segments (0xa38b0 : word) = Some W_a38b0.
Proof. vm_refl. Qed.
Lemma D_a38b0 : decode_any W_a38b0 = Some (Load SZ1 false 23 11 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a38b4 : bv 32 := 0x132bf863.
Lemma F_a38b4 : fetch_word Asan.M.loaded_segments (0xa38b4 : word) = Some W_a38b4.
Proof. vm_refl. Qed.
Lemma D_a38b4 : decode_any W_a38b4 = Some (Branch BC_GEU 23 18 304, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a38b8 : bv 32 := 0x133c6663.
Lemma F_a38b8 : fetch_word Asan.M.loaded_segments (0xa38b8 : word) = Some W_a38b8.
Proof. vm_refl. Qed.
Lemma D_a38b8 : decode_any W_a38b8 = Some (Branch BC_LTU 24 19 300, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a38bc : bv 32 := 0x0084b503.
Lemma F_a38bc : fetch_word Asan.M.loaded_segments (0xa38bc : word) = Some W_a38bc.
Proof. vm_refl. Qed.
Lemma D_a38bc : decode_any W_a38bc = Some (Load SZ8 true 10 9 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a38c0 : bv 32 := 0x0b84b583.
Lemma F_a38c0 : fetch_word Asan.M.loaded_segments (0xa38c0 : word) = Some W_a38c0.
Proof. vm_refl. Qed.
Lemma D_a38c0 : decode_any W_a38c0 = Some (Load SZ8 true 11 9 184, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a38c4 : bv 32 := 0xfcb50ce3.
Lemma F_a38c4 : fetch_word Asan.M.loaded_segments (0xa38c4 : word) = Some W_a38c4.
Proof. vm_refl. Qed.
Lemma D_a38c4 : decode_any W_a38c4 = Some (Branch BC_EQ 10 11 8152, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a38c8 : bv 32 := 0x00150593.
Lemma F_a38c8 : fetch_word Asan.M.loaded_segments (0xa38c8 : word) = Some W_a38c8.
Proof. vm_refl. Qed.
Lemma D_a38c8 : decode_any W_a38c8 = Some (OpImm ALU_ADD 11 10 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a38cc : bv 32 := 0x00b4b423.
Lemma F_a38cc : fetch_word Asan.M.loaded_segments (0xa38cc : word) = Some W_a38cc.
Proof. vm_refl. Qed.
Lemma D_a38cc : decode_any W_a38cc = Some (Store SZ8 9 11 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a38d0 : bv 32 := 0x00054503.
Lemma F_a38d0 : fetch_word Asan.M.loaded_segments (0xa38d0 : word) = Some W_a38d0.
Proof. vm_refl. Qed.
Lemma D_a38d0 : decode_any W_a38d0 = Some (Load SZ1 false 10 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a38d4 : bv 32 := 0x016995b3.
Lemma F_a38d4 : fetch_word Asan.M.loaded_segments (0xa38d4 : word) = Some W_a38d4.
Proof. vm_refl. Qed.
Lemma D_a38d4 : decode_any W_a38d4 = Some (Op ALU_SLL 11 19 22, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a38d8 : bv 32 := 0x0175e9b3.
Lemma F_a38d8 : fetch_word Asan.M.loaded_segments (0xa38d8 : word) = Some W_a38d8.
Proof. vm_refl. Qed.
Lemma D_a38d8 : decode_any W_a38d8 = Some (Op ALU_OR 19 11 23, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a38dc : bv 32 := 0x00aa85b3.
Lemma F_a38dc : fetch_word Asan.M.loaded_segments (0xa38dc : word) = Some W_a38dc.
Proof. vm_refl. Qed.
Lemma D_a38dc : decode_any W_a38dc = Some (Op ALU_ADD 11 21 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a38e0 : bv 32 := 0x0015cb83.
Lemma F_a38e0 : fetch_word Asan.M.loaded_segments (0xa38e0 : word) = Some W_a38e0.
Proof. vm_refl. Qed.
Lemma D_a38e0 : decode_any W_a38e0 = Some (Load SZ1 false 23 11 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a38e4 : bv 32 := 0xfd2beae3.
Lemma F_a38e4 : fetch_word Asan.M.loaded_segments (0xa38e4 : word) = Some W_a38e4.
Proof. vm_refl. Qed.
Lemma D_a38e4 : decode_any W_a38e4 = Some (Branch BC_LTU 23 18 8148, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a38e8 : bv 32 := 0x0fc0006f.
Lemma F_a38e8 : fetch_word Asan.M.loaded_segments (0xa38e8 : word) = Some W_a38e8.
Proof. vm_refl. Qed.
Lemma D_a38e8 : decode_any W_a38e8 = Some (Jal 0 252, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a38ec : bv 32 := 0xfff80597.
Lemma F_a38ec : fetch_word Asan.M.loaded_segments (0xa38ec : word) = Some W_a38ec.
Proof. vm_refl. Qed.
Lemma D_a38ec : decode_any W_a38ec = Some (Auipc 11 1048448, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a38f0 : bv 32 := 0xed458a93.
Lemma F_a38f0 : fetch_word Asan.M.loaded_segments (0xa38f0 : word) = Some W_a38f0.
Proof. vm_refl. Qed.
Lemma D_a38f0 : decode_any W_a38f0 = Some (OpImm ALU_ADD 21 11 3796, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a38f4 : bv 32 := 0x00aa85b3.
Lemma F_a38f4 : fetch_word Asan.M.loaded_segments (0xa38f4 : word) = Some W_a38f4.
Proof. vm_refl. Qed.
Lemma D_a38f4 : decode_any W_a38f4 = Some (Op ALU_ADD 11 21 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a38f8 : bv 32 := 0x0015cb03.
Lemma F_a38f8 : fetch_word Asan.M.loaded_segments (0xa38f8 : word) = Some W_a38f8.
Proof. vm_refl. Qed.
Lemma D_a38f8 : decode_any W_a38f8 = Some (Load SZ1 false 22 11 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a38fc : bv 32 := 0x072b7863.
Lemma F_a38fc : fetch_word Asan.M.loaded_segments (0xa38fc : word) = Some W_a38fc.
Proof. vm_refl. Qed.
Lemma D_a38fc : decode_any W_a38fc = Some (Branch BC_GEU 22 18 112, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a3900 : bv 32 := 0x00000993.
Lemma F_a3900 : fetch_word Asan.M.loaded_segments (0xa3900 : word) = Some W_a3900.
Proof. vm_refl. Qed.
Lemma D_a3900 : decode_any W_a3900 = Some (OpImm ALU_ADD 19 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a3904 : bv 32 := 0x071c7537.
Lemma F_a3904 : fetch_word Asan.M.loaded_segments (0xa3904 : word) = Some W_a3904.
Proof. vm_refl. Qed.
Lemma D_a3904 : decode_any W_a3904 = Some (Lui 10 29127, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a3908 : bv 32 := 0x1c750b9b.
Lemma F_a3908 : fetch_word Asan.M.loaded_segments (0xa3908 : word) = Some W_a3908.
Proof. vm_refl. Qed.
Lemma D_a3908 : decode_any W_a3908 = Some (OpImm32 23 10 455, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a390c : bv 32 := 0x0240006f.
Lemma F_a390c : fetch_word Asan.M.loaded_segments (0xa390c : word) = Some W_a390c.
Proof. vm_refl. Qed.
Lemma D_a390c : decode_any W_a390c = Some (Jal 0 36, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a3910 : bv 32 := 0x00048513.
Lemma F_a3910 : fetch_word Asan.M.loaded_segments (0xa3910 : word) = Some W_a3910.
Proof. vm_refl. Qed.
Lemma D_a3910 : decode_any W_a3910 = Some (OpImm ALU_ADD 10 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a3914 : bv 32 := 0xb45ff0ef.
Lemma F_a3914 : fetch_word Asan.M.loaded_segments (0xa3914 : word) = Some W_a3914.
Proof. vm_refl. Qed.
Lemma D_a3914 : decode_any W_a3914 = Some (Jal 1 2095940, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a3918 : bv 32 := 0x032985b3.
Lemma F_a3918 : fetch_word Asan.M.loaded_segments (0xa3918 : word) = Some W_a3918.
Proof. vm_refl. Qed.
Lemma D_a3918 : decode_any W_a3918 = Some (Mul M_MUL 11 19 18, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a391c : bv 32 := 0x00bb09bb.
Lemma F_a391c : fetch_word Asan.M.loaded_segments (0xa391c : word) = Some W_a391c.
Proof. vm_refl. Qed.
Lemma D_a391c : decode_any W_a391c = Some (Op32 ALU_ADD 19 22 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a3920 : bv 32 := 0x00aa85b3.
Lemma F_a3920 : fetch_word Asan.M.loaded_segments (0xa3920 : word) = Some W_a3920.
Proof. vm_refl. Qed.
Lemma D_a3920 : decode_any W_a3920 = Some (Op ALU_ADD 11 21 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a3924 : bv 32 := 0x0015cb03.
Lemma F_a3924 : fetch_word Asan.M.loaded_segments (0xa3924 : word) = Some W_a3924.
Proof. vm_refl. Qed.
Lemma D_a3924 : decode_any W_a3924 = Some (Load SZ1 false 22 11 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a3928 : bv 32 := 0x032b7a63.
Lemma F_a3928 : fetch_word Asan.M.loaded_segments (0xa3928 : word) = Some W_a3928.
Proof. vm_refl. Qed.
Lemma D_a3928 : decode_any W_a3928 = Some (Branch BC_GEU 22 18 52, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a392c : bv 32 := 0x0379f863.
Lemma F_a392c : fetch_word Asan.M.loaded_segments (0xa392c : word) = Some W_a392c.
Proof. vm_refl. Qed.
Lemma D_a392c : decode_any W_a392c = Some (Branch BC_GEU 19 23 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a3930 : bv 32 := 0x0084b503.
Lemma F_a3930 : fetch_word Asan.M.loaded_segments (0xa3930 : word) = Some W_a3930.
Proof. vm_refl. Qed.
Lemma D_a3930 : decode_any W_a3930 = Some (Load SZ8 true 10 9 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a3934 : bv 32 := 0x0b84b583.
Lemma F_a3934 : fetch_word Asan.M.loaded_segments (0xa3934 : word) = Some W_a3934.
Proof. vm_refl. Qed.
Lemma D_a3934 : decode_any W_a3934 = Some (Load SZ8 true 11 9 184, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a3938 : bv 32 := 0xfcb50ce3.
Lemma F_a3938 : fetch_word Asan.M.loaded_segments (0xa3938 : word) = Some W_a3938.
Proof. vm_refl. Qed.
Lemma D_a3938 : decode_any W_a3938 = Some (Branch BC_EQ 10 11 8152, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a393c : bv 32 := 0x00150593.
Lemma F_a393c : fetch_word Asan.M.loaded_segments (0xa393c : word) = Some W_a393c.
Proof. vm_refl. Qed.
Lemma D_a393c : decode_any W_a393c = Some (OpImm ALU_ADD 11 10 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a3940 : bv 32 := 0x00b4b423.
Lemma F_a3940 : fetch_word Asan.M.loaded_segments (0xa3940 : word) = Some W_a3940.
Proof. vm_refl. Qed.
Lemma D_a3940 : decode_any W_a3940 = Some (Store SZ8 9 11 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a3944 : bv 32 := 0x00054503.
Lemma F_a3944 : fetch_word Asan.M.loaded_segments (0xa3944 : word) = Some W_a3944.
Proof. vm_refl. Qed.
Lemma D_a3944 : decode_any W_a3944 = Some (Load SZ1 false 10 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a3948 : bv 32 := 0x032985b3.
Lemma F_a3948 : fetch_word Asan.M.loaded_segments (0xa3948 : word) = Some W_a3948.
Proof. vm_refl. Qed.
Lemma D_a3948 : decode_any W_a3948 = Some (Mul M_MUL 11 19 18, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a394c : bv 32 := 0x00bb09bb.
Lemma F_a394c : fetch_word Asan.M.loaded_segments (0xa394c : word) = Some W_a394c.
Proof. vm_refl. Qed.
Lemma D_a394c : decode_any W_a394c = Some (Op32 ALU_ADD 19 22 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a3950 : bv 32 := 0x00aa85b3.
Lemma F_a3950 : fetch_word Asan.M.loaded_segments (0xa3950 : word) = Some W_a3950.
Proof. vm_refl. Qed.
Lemma D_a3950 : decode_any W_a3950 = Some (Op ALU_ADD 11 21 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a3954 : bv 32 := 0x0015cb03.
Lemma F_a3954 : fetch_word Asan.M.loaded_segments (0xa3954 : word) = Some W_a3954.
Proof. vm_refl. Qed.
Lemma D_a3954 : decode_any W_a3954 = Some (Load SZ1 false 22 11 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a3958 : bv 32 := 0xfd2b6ae3.
Lemma F_a3958 : fetch_word Asan.M.loaded_segments (0xa3958 : word) = Some W_a3958.
Proof. vm_refl. Qed.
Lemma D_a3958 : decode_any W_a3958 = Some (Branch BC_LTU 22 18 8148, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a395c : bv 32 := 0x02099993.
Lemma F_a395c : fetch_word Asan.M.loaded_segments (0xa395c : word) = Some W_a395c.
Proof. vm_refl. Qed.
Lemma D_a395c : decode_any W_a395c = Some (ShiftImm ALU_SLL 19 19 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a3960 : bv 32 := 0x0209d993.
Lemma F_a3960 : fetch_word Asan.M.loaded_segments (0xa3960 : word) = Some W_a3960.
Proof. vm_refl. Qed.
Lemma D_a3960 : decode_any W_a3960 = Some (ShiftImm ALU_SRL 19 19 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a3964 : bv 32 := 0x012b6863.
Lemma F_a3964 : fetch_word Asan.M.loaded_segments (0xa3964 : word) = Some W_a3964.
Proof. vm_refl. Qed.
Lemma D_a3964 : decode_any W_a3964 = Some (Branch BC_LTU 22 18 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a3968 : bv 32 := 0x07c0006f.
Lemma F_a3968 : fetch_word Asan.M.loaded_segments (0xa3968 : word) = Some W_a3968.
Proof. vm_refl. Qed.
Lemma D_a3968 : decode_any W_a3968 = Some (Jal 0 124, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a396c : bv 32 := 0x00000993.
Lemma F_a396c : fetch_word Asan.M.loaded_segments (0xa396c : word) = Some W_a396c.
Proof. vm_refl. Qed.
Lemma D_a396c : decode_any W_a396c = Some (OpImm ALU_ADD 19 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a3970 : bv 32 := 0x072b7a63.
Lemma F_a3970 : fetch_word Asan.M.loaded_segments (0xa3970 : word) = Some W_a3970.
Proof. vm_refl. Qed.
Lemma D_a3970 : decode_any W_a3970 = Some (Branch BC_GEU 22 18 116, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a3974 : bv 32 := 0x02091593.
Lemma F_a3974 : fetch_word Asan.M.loaded_segments (0xa3974 : word) = Some W_a3974.
Proof. vm_refl. Qed.
Lemma D_a3974 : decode_any W_a3974 = Some (ShiftImm ALU_SLL 11 18 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a3978 : bv 32 := 0x0205db93.
Lemma F_a3978 : fetch_word Asan.M.loaded_segments (0xa3978 : word) = Some W_a3978.
Proof. vm_refl. Qed.
Lemma D_a3978 : decode_any W_a3978 = Some (ShiftImm ALU_SRL 23 11 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a397c : bv 32 := 0x0240006f.
Lemma F_a397c : fetch_word Asan.M.loaded_segments (0xa397c : word) = Some W_a397c.
Proof. vm_refl. Qed.
Lemma D_a397c : decode_any W_a397c = Some (Jal 0 36, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a3980 : bv 32 := 0x00048513.
Lemma F_a3980 : fetch_word Asan.M.loaded_segments (0xa3980 : word) = Some W_a3980.
Proof. vm_refl. Qed.
Lemma D_a3980 : decode_any W_a3980 = Some (OpImm ALU_ADD 10 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a3984 : bv 32 := 0xad5ff0ef.
Lemma F_a3984 : fetch_word Asan.M.loaded_segments (0xa3984 : word) = Some W_a3984.
Proof. vm_refl. Qed.
Lemma D_a3984 : decode_any W_a3984 = Some (Jal 1 2095828, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a3988 : bv 32 := 0x016c09b3.
Lemma F_a3988 : fetch_word Asan.M.loaded_segments (0xa3988 : word) = Some W_a3988.
Proof. vm_refl. Qed.
Lemma D_a3988 : decode_any W_a3988 = Some (Op ALU_ADD 19 24 22, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a398c : bv 32 := 0x00aa85b3.
Lemma F_a398c : fetch_word Asan.M.loaded_segments (0xa398c : word) = Some W_a398c.
Proof. vm_refl. Qed.
Lemma D_a398c : decode_any W_a398c = Some (Op ALU_ADD 11 21 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a3990 : bv 32 := 0x0015cb03.
Lemma F_a3990 : fetch_word Asan.M.loaded_segments (0xa3990 : word) = Some W_a3990.
Proof. vm_refl. Qed.
Lemma D_a3990 : decode_any W_a3990 = Some (Load SZ1 false 22 11 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a3994 : bv 32 := 0x052b7863.
Lemma F_a3994 : fetch_word Asan.M.loaded_segments (0xa3994 : word) = Some W_a3994.
Proof. vm_refl. Qed.
Lemma D_a3994 : decode_any W_a3994 = Some (Branch BC_GEU 22 18 80, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a3998 : bv 32 := 0x033bb5b3.
Lemma F_a3998 : fetch_word Asan.M.loaded_segments (0xa3998 : word) = Some W_a3998.
Proof. vm_refl. Qed.
Lemma D_a3998 : decode_any W_a3998 = Some (Mul M_MULHU 11 23 19, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a399c : bv 32 := 0x04059463.
Lemma F_a399c : fetch_word Asan.M.loaded_segments (0xa399c : word) = Some W_a399c.
Proof. vm_refl. Qed.
Lemma D_a399c : decode_any W_a399c = Some (Branch BC_NE 11 0 72, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a39a0 : bv 32 := 0x03798c33.
Lemma F_a39a0 : fetch_word Asan.M.loaded_segments (0xa39a0 : word) = Some W_a39a0.
Proof. vm_refl. Qed.
Lemma D_a39a0 : decode_any W_a39a0 = Some (Mul M_MUL 24 19 23, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a39a4 : bv 32 := 0xfffb4593.
Lemma F_a39a4 : fetch_word Asan.M.loaded_segments (0xa39a4 : word) = Some W_a39a4.
Proof. vm_refl. Qed.
Lemma D_a39a4 : decode_any W_a39a4 = Some (OpImm ALU_XOR 11 22 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a39a8 : bv 32 := 0x0385ee63.
Lemma F_a39a8 : fetch_word Asan.M.loaded_segments (0xa39a8 : word) = Some W_a39a8.
Proof. vm_refl. Qed.
Lemma D_a39a8 : decode_any W_a39a8 = Some (Branch BC_LTU 11 24 60, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a39ac : bv 32 := 0x0084b503.
Lemma F_a39ac : fetch_word Asan.M.loaded_segments (0xa39ac : word) = Some W_a39ac.
Proof. vm_refl. Qed.
Lemma D_a39ac : decode_any W_a39ac = Some (Load SZ8 true 10 9 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a39b0 : bv 32 := 0x0b84b583.
Lemma F_a39b0 : fetch_word Asan.M.loaded_segments (0xa39b0 : word) = Some W_a39b0.
Proof. vm_refl. Qed.
Lemma D_a39b0 : decode_any W_a39b0 = Some (Load SZ8 true 11 9 184, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a39b4 : bv 32 := 0xfcb506e3.
Lemma F_a39b4 : fetch_word Asan.M.loaded_segments (0xa39b4 : word) = Some W_a39b4.
Proof. vm_refl. Qed.
Lemma D_a39b4 : decode_any W_a39b4 = Some (Branch BC_EQ 10 11 8140, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a39b8 : bv 32 := 0x00150593.
Lemma F_a39b8 : fetch_word Asan.M.loaded_segments (0xa39b8 : word) = Some W_a39b8.
Proof. vm_refl. Qed.
Lemma D_a39b8 : decode_any W_a39b8 = Some (OpImm ALU_ADD 11 10 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a39bc : bv 32 := 0x00b4b423.
Lemma F_a39bc : fetch_word Asan.M.loaded_segments (0xa39bc : word) = Some W_a39bc.
Proof. vm_refl. Qed.
Lemma D_a39bc : decode_any W_a39bc = Some (Store SZ8 9 11 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a39c0 : bv 32 := 0x00054503.
Lemma F_a39c0 : fetch_word Asan.M.loaded_segments (0xa39c0 : word) = Some W_a39c0.
Proof. vm_refl. Qed.
Lemma D_a39c0 : decode_any W_a39c0 = Some (Load SZ1 false 10 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a39c4 : bv 32 := 0x016c09b3.
Lemma F_a39c4 : fetch_word Asan.M.loaded_segments (0xa39c4 : word) = Some W_a39c4.
Proof. vm_refl. Qed.
Lemma D_a39c4 : decode_any W_a39c4 = Some (Op ALU_ADD 19 24 22, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a39c8 : bv 32 := 0x00aa85b3.
Lemma F_a39c8 : fetch_word Asan.M.loaded_segments (0xa39c8 : word) = Some W_a39c8.
Proof. vm_refl. Qed.
Lemma D_a39c8 : decode_any W_a39c8 = Some (Op ALU_ADD 11 21 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a39cc : bv 32 := 0x0015cb03.
Lemma F_a39cc : fetch_word Asan.M.loaded_segments (0xa39cc : word) = Some W_a39cc.
Proof. vm_refl. Qed.
Lemma D_a39cc : decode_any W_a39cc = Some (Load SZ1 false 22 11 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a39d0 : bv 32 := 0xfd2b64e3.
Lemma F_a39d0 : fetch_word Asan.M.loaded_segments (0xa39d0 : word) = Some W_a39d0.
Proof. vm_refl. Qed.
Lemma D_a39d0 : decode_any W_a39d0 = Some (Branch BC_LTU 22 18 8136, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a39d4 : bv 32 := 0x0100006f.
Lemma F_a39d4 : fetch_word Asan.M.loaded_segments (0xa39d4 : word) = Some W_a39d4.
Proof. vm_refl. Qed.
Lemma D_a39d4 : decode_any W_a39d4 = Some (Jal 0 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a39d8 : bv 32 := 0x00900593.
Lemma F_a39d8 : fetch_word Asan.M.loaded_segments (0xa39d8 : word) = Some W_a39d8.
Proof. vm_refl. Qed.
Lemma D_a39d8 : decode_any W_a39d8 = Some (OpImm ALU_ADD 11 0 9, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a39dc : bv 32 := 0x0155ee63.
Lemma F_a39dc : fetch_word Asan.M.loaded_segments (0xa39dc : word) = Some W_a39dc.
Proof. vm_refl. Qed.
Lemma D_a39dc : decode_any W_a39dc = Some (Branch BC_LTU 11 21 28, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a39e0 : bv 32 := 0x00a00913.
Lemma F_a39e0 : fetch_word Asan.M.loaded_segments (0xa39e0 : word) = Some W_a39e0.
Proof. vm_refl. Qed.
Lemma D_a39e0 : decode_any W_a39e0 = Some (OpImm ALU_ADD 18 0 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a39e4 : bv 32 := 0xfff80597.
Lemma F_a39e4 : fetch_word Asan.M.loaded_segments (0xa39e4 : word) = Some W_a39e4.
Proof. vm_refl. Qed.
Lemma D_a39e4 : decode_any W_a39e4 = Some (Auipc 11 1048448, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a39e8 : bv 32 := 0xddc58a93.
Lemma F_a39e8 : fetch_word Asan.M.loaded_segments (0xa39e8 : word) = Some W_a39e8.
Proof. vm_refl. Qed.
Lemma D_a39e8 : decode_any W_a39e8 = Some (OpImm ALU_ADD 21 11 3548, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a39ec : bv 32 := 0x00aa8533.
Lemma F_a39ec : fetch_word Asan.M.loaded_segments (0xa39ec : word) = Some W_a39ec.
Proof. vm_refl. Qed.
Lemma D_a39ec : decode_any W_a39ec = Some (Op ALU_ADD 10 21 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a39f0 : bv 32 := 0x00154503.
Lemma F_a39f0 : fetch_word Asan.M.loaded_segments (0xa39f0 : word) = Some W_a39f0.
Proof. vm_refl. Qed.
Lemma D_a39f0 : decode_any W_a39f0 = Some (Load SZ1 false 10 10 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a39f4 : bv 32 := 0x03256e63.
Lemma F_a39f4 : fetch_word Asan.M.loaded_segments (0xa39f4 : word) = Some W_a39f4.
Proof. vm_refl. Qed.
Lemma D_a39f4 : decode_any W_a39f4 = Some (Branch BC_LTU 10 18 60, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a39f8 : bv 32 := 0x0c04b503.
Lemma F_a39f8 : fetch_word Asan.M.loaded_segments (0xa39f8 : word) = Some W_a39f8.
Proof. vm_refl. Qed.
Lemma D_a39f8 : decode_any W_a39f8 = Some (Load SZ8 true 10 9 192, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a39fc : bv 32 := 0x00054863.
Lemma F_a39fc : fetch_word Asan.M.loaded_segments (0xa39fc : word) = Some W_a39fc.
Proof. vm_refl. Qed.
Lemma D_a39fc : decode_any W_a39fc = Some (Branch BC_LT 10 0 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a3a00 : bv 32 := 0x0084b503.
Lemma F_a3a00 : fetch_word Asan.M.loaded_segments (0xa3a00 : word) = Some W_a3a00.
Proof. vm_refl. Qed.
Lemma D_a3a00 : decode_any W_a3a00 = Some (Load SZ8 true 10 9 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a3a04 : bv 32 := 0xfff50513.
Lemma F_a3a04 : fetch_word Asan.M.loaded_segments (0xa3a04 : word) = Some W_a3a04.
Proof. vm_refl. Qed.
Lemma D_a3a04 : decode_any W_a3a04 = Some (OpImm ALU_ADD 10 10 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a3a08 : bv 32 := 0x00a4b423.
Lemma F_a3a08 : fetch_word Asan.M.loaded_segments (0xa3a08 : word) = Some W_a3a08.
Proof. vm_refl. Qed.
Lemma D_a3a08 : decode_any W_a3a08 = Some (Store SZ8 9 10 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a3a0c : bv 32 := 0x0689f863.
Lemma F_a3a0c : fetch_word Asan.M.loaded_segments (0xa3a0c : word) = Some W_a3a0c.
Proof. vm_refl. Qed.
Lemma D_a3a0c : decode_any W_a3a0c = Some (Branch BC_GEU 19 8 112, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a3a10 : bv 32 := 0x0149c533.
Lemma F_a3a10 : fetch_word Asan.M.loaded_segments (0xa3a10 : word) = Some W_a3a10.
Proof. vm_refl. Qed.
Lemma D_a3a10 : decode_any W_a3a10 = Some (Op ALU_XOR 10 19 20, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a3a14 : bv 32 := 0x41450433.
Lemma F_a3a14 : fetch_word Asan.M.loaded_segments (0xa3a14 : word) = Some W_a3a14.
Proof. vm_refl. Qed.
Lemma D_a3a14 : decode_any W_a3a14 = Some (Op ALU_SUB 8 10 20, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a3a18 : bv 32 := 0x0ac0006f.
Lemma F_a3a18 : fetch_word Asan.M.loaded_segments (0xa3a18 : word) = Some W_a3a18.
Proof. vm_refl. Qed.
Lemma D_a3a18 : decode_any W_a3a18 = Some (Jal 0 172, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a3a1c : bv 32 := 0x00048513.
Lemma F_a3a1c : fetch_word Asan.M.loaded_segments (0xa3a1c : word) = Some W_a3a1c.
Proof. vm_refl. Qed.
Lemma D_a3a1c : decode_any W_a3a1c = Some (OpImm ALU_ADD 10 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a3a20 : bv 32 := 0xa39ff0ef.
Lemma F_a3a20 : fetch_word Asan.M.loaded_segments (0xa3a20 : word) = Some W_a3a20.
Proof. vm_refl. Qed.
Lemma D_a3a20 : decode_any W_a3a20 = Some (Jal 1 2095672, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a3a24 : bv 32 := 0x00aa8533.
Lemma F_a3a24 : fetch_word Asan.M.loaded_segments (0xa3a24 : word) = Some W_a3a24.
Proof. vm_refl. Qed.
Lemma D_a3a24 : decode_any W_a3a24 = Some (Op ALU_ADD 10 21 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a3a28 : bv 32 := 0x00154503.
Lemma F_a3a28 : fetch_word Asan.M.loaded_segments (0xa3a28 : word) = Some W_a3a28.
Proof. vm_refl. Qed.
Lemma D_a3a28 : decode_any W_a3a28 = Some (Load SZ1 false 10 10 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a3a2c : bv 32 := 0x03257463.
Lemma F_a3a2c : fetch_word Asan.M.loaded_segments (0xa3a2c : word) = Some W_a3a2c.
Proof. vm_refl. Qed.
Lemma D_a3a2c : decode_any W_a3a2c = Some (Branch BC_GEU 10 18 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a3a30 : bv 32 := 0x0084b503.
Lemma F_a3a30 : fetch_word Asan.M.loaded_segments (0xa3a30 : word) = Some W_a3a30.
Proof. vm_refl. Qed.
Lemma D_a3a30 : decode_any W_a3a30 = Some (Load SZ8 true 10 9 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a3a34 : bv 32 := 0x0b84b583.
Lemma F_a3a34 : fetch_word Asan.M.loaded_segments (0xa3a34 : word) = Some W_a3a34.
Proof. vm_refl. Qed.
Lemma D_a3a34 : decode_any W_a3a34 = Some (Load SZ8 true 11 9 184, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a3a38 : bv 32 := 0xfeb502e3.
Lemma F_a3a38 : fetch_word Asan.M.loaded_segments (0xa3a38 : word) = Some W_a3a38.
Proof. vm_refl. Qed.
Lemma D_a3a38 : decode_any W_a3a38 = Some (Branch BC_EQ 10 11 8164, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a3a3c : bv 32 := 0x00150593.
Lemma F_a3a3c : fetch_word Asan.M.loaded_segments (0xa3a3c : word) = Some W_a3a3c.
Proof. vm_refl. Qed.
Lemma D_a3a3c : decode_any W_a3a3c = Some (OpImm ALU_ADD 11 10 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a3a40 : bv 32 := 0x00b4b423.
Lemma F_a3a40 : fetch_word Asan.M.loaded_segments (0xa3a40 : word) = Some W_a3a40.
Proof. vm_refl. Qed.
Lemma D_a3a40 : decode_any W_a3a40 = Some (Store SZ8 9 11 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a3a44 : bv 32 := 0x00054503.
Lemma F_a3a44 : fetch_word Asan.M.loaded_segments (0xa3a44 : word) = Some W_a3a44.
Proof. vm_refl. Qed.
Lemma D_a3a44 : decode_any W_a3a44 = Some (Load SZ1 false 10 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a3a48 : bv 32 := 0x00aa8533.
Lemma F_a3a48 : fetch_word Asan.M.loaded_segments (0xa3a48 : word) = Some W_a3a48.
Proof. vm_refl. Qed.
Lemma D_a3a48 : decode_any W_a3a48 = Some (Op ALU_ADD 10 21 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a3a4c : bv 32 := 0x00154503.
Lemma F_a3a4c : fetch_word Asan.M.loaded_segments (0xa3a4c : word) = Some W_a3a4c.
Proof. vm_refl. Qed.
Lemma D_a3a4c : decode_any W_a3a4c = Some (Load SZ1 false 10 10 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a3a50 : bv 32 := 0xff2560e3.
Lemma F_a3a50 : fetch_word Asan.M.loaded_segments (0xa3a50 : word) = Some W_a3a50.
Proof. vm_refl. Qed.
Lemma D_a3a50 : decode_any W_a3a50 = Some (Branch BC_LTU 10 18 8160, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a3a54 : bv 32 := 0xba5f60ef.
Lemma F_a3a54 : fetch_word Asan.M.loaded_segments (0xa3a54 : word) = Some W_a3a54.
Proof. vm_refl. Qed.
Lemma D_a3a54 : decode_any W_a3a54 = Some (Jal 1 2059172, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a3a58 : bv 32 := 0x02200593.
Lemma F_a3a58 : fetch_word Asan.M.loaded_segments (0xa3a58 : word) = Some W_a3a58.
Proof. vm_refl. Qed.
Lemma D_a3a58 : decode_any W_a3a58 = Some (OpImm ALU_ADD 11 0 34, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a3a5c : bv 32 := 0x00b52023.
Lemma F_a3a5c : fetch_word Asan.M.loaded_segments (0xa3a5c : word) = Some W_a3a5c.
Proof. vm_refl. Qed.
Lemma D_a3a5c : decode_any W_a3a5c = Some (Store SZ4 10 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a3a60 : bv 32 := 0x00147513.
Lemma F_a3a60 : fetch_word Asan.M.loaded_segments (0xa3a60 : word) = Some W_a3a60.
Proof. vm_refl. Qed.
Lemma D_a3a60 : decode_any W_a3a60 = Some (OpImm ALU_AND 10 8 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a3a64 : bv 32 := 0xfff5051b.
Lemma F_a3a64 : fetch_word Asan.M.loaded_segments (0xa3a64 : word) = Some W_a3a64.
Proof. vm_refl. Qed.
Lemma D_a3a64 : decode_any W_a3a64 = Some (OpImm32 10 10 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a3a68 : bv 32 := 0x01457a33.
Lemma F_a3a68 : fetch_word Asan.M.loaded_segments (0xa3a68 : word) = Some W_a3a68.
Proof. vm_refl. Qed.
Lemma D_a3a68 : decode_any W_a3a68 = Some (Op ALU_AND 20 10 20, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a3a6c : bv 32 := 0x00040993.
Lemma F_a3a6c : fetch_word Asan.M.loaded_segments (0xa3a6c : word) = Some W_a3a6c.
Proof. vm_refl. Qed.
Lemma D_a3a6c : decode_any W_a3a6c = Some (OpImm ALU_ADD 19 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a3a70 : bv 32 := 0x0c04b503.
Lemma F_a3a70 : fetch_word Asan.M.loaded_segments (0xa3a70 : word) = Some W_a3a70.
Proof. vm_refl. Qed.
Lemma D_a3a70 : decode_any W_a3a70 = Some (Load SZ8 true 10 9 192, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a3a74 : bv 32 := 0xf80556e3.
Lemma F_a3a74 : fetch_word Asan.M.loaded_segments (0xa3a74 : word) = Some W_a3a74.
Proof. vm_refl. Qed.
Lemma D_a3a74 : decode_any W_a3a74 = Some (Branch BC_GE 10 0 8076, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a3a78 : bv 32 := 0xf95ff06f.
Lemma F_a3a78 : fetch_word Asan.M.loaded_segments (0xa3a78 : word) = Some W_a3a78.
Proof. vm_refl. Qed.
Lemma D_a3a78 : decode_any W_a3a78 = Some (Jal 0 2097044, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a3a7c : bv 32 := 0x00147513.
Lemma F_a3a7c : fetch_word Asan.M.loaded_segments (0xa3a7c : word) = Some W_a3a7c.
Proof. vm_refl. Qed.
Lemma D_a3a7c : decode_any W_a3a7c = Some (OpImm ALU_AND 10 8 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a3a80 : bv 32 := 0x00051e63.
Lemma F_a3a80 : fetch_word Asan.M.loaded_segments (0xa3a80 : word) = Some W_a3a80.
Proof. vm_refl. Qed.
Lemma D_a3a80 : decode_any W_a3a80 = Some (Branch BC_NE 10 0 28, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a3a84 : bv 32 := 0x000a1c63.
Lemma F_a3a84 : fetch_word Asan.M.loaded_segments (0xa3a84 : word) = Some W_a3a84.
Proof. vm_refl. Qed.
Lemma D_a3a84 : decode_any W_a3a84 = Some (Branch BC_NE 20 0 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a3a88 : bv 32 := 0xb71f60ef.
Lemma F_a3a88 : fetch_word Asan.M.loaded_segments (0xa3a88 : word) = Some W_a3a88.
Proof. vm_refl. Qed.
Lemma D_a3a88 : decode_any W_a3a88 = Some (Jal 1 2059120, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a3a8c : bv 32 := 0x02200593.
Lemma F_a3a8c : fetch_word Asan.M.loaded_segments (0xa3a8c : word) = Some W_a3a8c.
Proof. vm_refl. Qed.
Lemma D_a3a8c : decode_any W_a3a8c = Some (OpImm ALU_ADD 11 0 34, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a3a90 : bv 32 := 0x00b52023.
Lemma F_a3a90 : fetch_word Asan.M.loaded_segments (0xa3a90 : word) = Some W_a3a90.
Proof. vm_refl. Qed.
Lemma D_a3a90 : decode_any W_a3a90 = Some (Store SZ4 10 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a3a94 : bv 32 := 0xfff40413.
Lemma F_a3a94 : fetch_word Asan.M.loaded_segments (0xa3a94 : word) = Some W_a3a94.
Proof. vm_refl. Qed.
Lemma D_a3a94 : decode_any W_a3a94 = Some (OpImm ALU_ADD 8 8 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a3a98 : bv 32 := 0x02c0006f.
Lemma F_a3a98 : fetch_word Asan.M.loaded_segments (0xa3a98 : word) = Some W_a3a98.
Proof. vm_refl. Qed.
Lemma D_a3a98 : decode_any W_a3a98 = Some (Jal 0 44, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a3a9c : bv 32 := 0xf7347ae3.
Lemma F_a3a9c : fetch_word Asan.M.loaded_segments (0xa3a9c : word) = Some W_a3a9c.
Proof. vm_refl. Qed.
Lemma D_a3a9c : decode_any W_a3a9c = Some (Branch BC_GEU 8 19 8052, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a3aa0 : bv 32 := 0xb59f60ef.
Lemma F_a3aa0 : fetch_word Asan.M.loaded_segments (0xa3aa0 : word) = Some W_a3aa0.
Proof. vm_refl. Qed.
Lemma D_a3aa0 : decode_any W_a3aa0 = Some (Jal 1 2059096, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a3aa4 : bv 32 := 0x02200593.
Lemma F_a3aa4 : fetch_word Asan.M.loaded_segments (0xa3aa4 : word) = Some W_a3aa4.
Proof. vm_refl. Qed.
Lemma D_a3aa4 : decode_any W_a3aa4 = Some (OpImm ALU_ADD 11 0 34, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a3aa8 : bv 32 := 0x00b52023.
Lemma F_a3aa8 : fetch_word Asan.M.loaded_segments (0xa3aa8 : word) = Some W_a3aa8.
Proof. vm_refl. Qed.
Lemma D_a3aa8 : decode_any W_a3aa8 = Some (Store SZ4 10 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a3aac : bv 32 := 0x0180006f.
Lemma F_a3aac : fetch_word Asan.M.loaded_segments (0xa3aac : word) = Some W_a3aac.
Proof. vm_refl. Qed.
Lemma D_a3aac : decode_any W_a3aac = Some (Jal 0 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a3ab0 : bv 32 := 0x00099863.
Lemma F_a3ab0 : fetch_word Asan.M.loaded_segments (0xa3ab0 : word) = Some W_a3ab0.
Proof. vm_refl. Qed.
Lemma D_a3ab0 : decode_any W_a3ab0 = Some (Branch BC_NE 19 0 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a3ab4 : bv 32 := 0x00048513.
Lemma F_a3ab4 : fetch_word Asan.M.loaded_segments (0xa3ab4 : word) = Some W_a3ab4.
Proof. vm_refl. Qed.
Lemma D_a3ab4 : decode_any W_a3ab4 = Some (OpImm ALU_ADD 10 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a3ab8 : bv 32 := 0x00000593.
Lemma F_a3ab8 : fetch_word Asan.M.loaded_segments (0xa3ab8 : word) = Some W_a3ab8.
Proof. vm_refl. Qed.
Lemma D_a3ab8 : decode_any W_a3ab8 = Some (OpImm ALU_ADD 11 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a3abc : bv 32 := 0x965ff0ef.
Lemma F_a3abc : fetch_word Asan.M.loaded_segments (0xa3abc : word) = Some W_a3abc.
Proof. vm_refl. Qed.
Lemma D_a3abc : decode_any W_a3abc = Some (Jal 1 2095460, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a3ac0 : bv 32 := 0x00000413.
Lemma F_a3ac0 : fetch_word Asan.M.loaded_segments (0xa3ac0 : word) = Some W_a3ac0.
Proof. vm_refl. Qed.
Lemma D_a3ac0 : decode_any W_a3ac0 = Some (OpImm ALU_ADD 8 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a3ac4 : bv 32 := 0x00040513.
Lemma F_a3ac4 : fetch_word Asan.M.loaded_segments (0xa3ac4 : word) = Some W_a3ac4.
Proof. vm_refl. Qed.
Lemma D_a3ac4 : decode_any W_a3ac4 = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a3ac8 : bv 32 := 0x04813083.
Lemma F_a3ac8 : fetch_word Asan.M.loaded_segments (0xa3ac8 : word) = Some W_a3ac8.
Proof. vm_refl. Qed.
Lemma D_a3ac8 : decode_any W_a3ac8 = Some (Load SZ8 true 1 2 72, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a3acc : bv 32 := 0x04013403.
Lemma F_a3acc : fetch_word Asan.M.loaded_segments (0xa3acc : word) = Some W_a3acc.
Proof. vm_refl. Qed.
Lemma D_a3acc : decode_any W_a3acc = Some (Load SZ8 true 8 2 64, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a3ad0 : bv 32 := 0x03813483.
Lemma F_a3ad0 : fetch_word Asan.M.loaded_segments (0xa3ad0 : word) = Some W_a3ad0.
Proof. vm_refl. Qed.
Lemma D_a3ad0 : decode_any W_a3ad0 = Some (Load SZ8 true 9 2 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a3ad4 : bv 32 := 0x03013903.
Lemma F_a3ad4 : fetch_word Asan.M.loaded_segments (0xa3ad4 : word) = Some W_a3ad4.
Proof. vm_refl. Qed.
Lemma D_a3ad4 : decode_any W_a3ad4 = Some (Load SZ8 true 18 2 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a3ad8 : bv 32 := 0x02813983.
Lemma F_a3ad8 : fetch_word Asan.M.loaded_segments (0xa3ad8 : word) = Some W_a3ad8.
Proof. vm_refl. Qed.
Lemma D_a3ad8 : decode_any W_a3ad8 = Some (Load SZ8 true 19 2 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a3adc : bv 32 := 0x02013a03.
Lemma F_a3adc : fetch_word Asan.M.loaded_segments (0xa3adc : word) = Some W_a3adc.
Proof. vm_refl. Qed.
Lemma D_a3adc : decode_any W_a3adc = Some (Load SZ8 true 20 2 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a3ae0 : bv 32 := 0x01813a83.
Lemma F_a3ae0 : fetch_word Asan.M.loaded_segments (0xa3ae0 : word) = Some W_a3ae0.
Proof. vm_refl. Qed.
Lemma D_a3ae0 : decode_any W_a3ae0 = Some (Load SZ8 true 21 2 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a3ae4 : bv 32 := 0x01013b03.
Lemma F_a3ae4 : fetch_word Asan.M.loaded_segments (0xa3ae4 : word) = Some W_a3ae4.
Proof. vm_refl. Qed.
Lemma D_a3ae4 : decode_any W_a3ae4 = Some (Load SZ8 true 22 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a3ae8 : bv 32 := 0x00813b83.
Lemma F_a3ae8 : fetch_word Asan.M.loaded_segments (0xa3ae8 : word) = Some W_a3ae8.
Proof. vm_refl. Qed.
Lemma D_a3ae8 : decode_any W_a3ae8 = Some (Load SZ8 true 23 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a3aec : bv 32 := 0x00013c03.
Lemma F_a3aec : fetch_word Asan.M.loaded_segments (0xa3aec : word) = Some W_a3aec.
Proof. vm_refl. Qed.
Lemma D_a3aec : decode_any W_a3aec = Some (Load SZ8 true 24 2 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a3af0 : bv 32 := 0x05010113.
Lemma F_a3af0 : fetch_word Asan.M.loaded_segments (0xa3af0 : word) = Some W_a3af0.
Proof. vm_refl. Qed.
Lemma D_a3af0 : decode_any W_a3af0 = Some (OpImm ALU_ADD 2 2 80, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a3af4 : bv 32 := 0x00008067.
Lemma F_a3af4 : fetch_word Asan.M.loaded_segments (0xa3af4 : word) = Some W_a3af4.
Proof. vm_refl. Qed.
Lemma D_a3af4 : decode_any W_a3af4 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.
(* [comment removed for export] *)
Definition W_a3f44 : bv 32 := 0xee010113.
Lemma F_a3f44 : fetch_word Asan.M.loaded_segments (0xa3f44 : word) = Some W_a3f44.
Proof. vm_refl. Qed.
Lemma D_a3f44 : decode_any W_a3f44 = Some (OpImm ALU_ADD 2 2 3808, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a3f48 : bv 32 := 0x10113c23.
Lemma F_a3f48 : fetch_word Asan.M.loaded_segments (0xa3f48 : word) = Some W_a3f48.
Proof. vm_refl. Qed.
Lemma D_a3f48 : decode_any W_a3f48 = Some (Store SZ8 2 1 280, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a3f4c : bv 32 := 0x10813823.
Lemma F_a3f4c : fetch_word Asan.M.loaded_segments (0xa3f4c : word) = Some W_a3f4c.
Proof. vm_refl. Qed.
Lemma D_a3f4c : decode_any W_a3f4c = Some (Store SZ8 2 8 272, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a3f50 : bv 32 := 0x10913423.
Lemma F_a3f50 : fetch_word Asan.M.loaded_segments (0xa3f50 : word) = Some W_a3f50.
Proof. vm_refl. Qed.
Lemma D_a3f50 : decode_any W_a3f50 = Some (Store SZ8 2 9 264, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a3f54 : bv 32 := 0x11213023.
Lemma F_a3f54 : fetch_word Asan.M.loaded_segments (0xa3f54 : word) = Some W_a3f54.
Proof. vm_refl. Qed.
Lemma D_a3f54 : decode_any W_a3f54 = Some (Store SZ8 2 18 256, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a3f58 : bv 32 := 0x0f313c23.
Lemma F_a3f58 : fetch_word Asan.M.loaded_segments (0xa3f58 : word) = Some W_a3f58.
Proof. vm_refl. Qed.
Lemma D_a3f58 : decode_any W_a3f58 = Some (Store SZ8 2 19 248, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a3f5c : bv 32 := 0x00060913.
Lemma F_a3f5c : fetch_word Asan.M.loaded_segments (0xa3f5c : word) = Some W_a3f5c.
Proof. vm_refl. Qed.
Lemma D_a3f5c : decode_any W_a3f5c = Some (OpImm ALU_ADD 18 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a3f60 : bv 32 := 0x00058413.
Lemma F_a3f60 : fetch_word Asan.M.loaded_segments (0xa3f60 : word) = Some W_a3f60.
Proof. vm_refl. Qed.
Lemma D_a3f60 : decode_any W_a3f60 = Some (OpImm ALU_ADD 8 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a3f64 : bv 32 := 0x00050493.
Lemma F_a3f64 : fetch_word Asan.M.loaded_segments (0xa3f64 : word) = Some W_a3f64.
Proof. vm_refl. Qed.
Lemma D_a3f64 : decode_any W_a3f64 = Some (OpImm ALU_ADD 9 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a3f68 : bv 32 := 0x00008517.
Lemma F_a3f68 : fetch_word Asan.M.loaded_segments (0xa3f68 : word) = Some W_a3f68.
Proof. vm_refl. Qed.
Lemma D_a3f68 : decode_any W_a3f68 = Some (Auipc 10 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a3f6c : bv 32 := 0xba053983.
Lemma F_a3f6c : fetch_word Asan.M.loaded_segments (0xa3f6c : word) = Some W_a3f6c.
Proof. vm_refl. Qed.
Lemma D_a3f6c : decode_any W_a3f6c = Some (Load SZ8 true 19 10 2976, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a3f70 : bv 32 := 0x0009b503.
Lemma F_a3f70 : fetch_word Asan.M.loaded_segments (0xa3f70 : word) = Some W_a3f70.
Proof. vm_refl. Qed.
Lemma D_a3f70 : decode_any W_a3f70 = Some (Load SZ8 true 10 19 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a3f74 : bv 32 := 0x0ea13823.
Lemma F_a3f74 : fetch_word Asan.M.loaded_segments (0xa3f74 : word) = Some W_a3f74.
Proof. vm_refl. Qed.
Lemma D_a3f74 : decode_any W_a3f74 = Some (Store SZ8 2 10 240, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a3f78 : bv 32 := 0xfff00513.
Lemma F_a3f78 : fetch_word Asan.M.loaded_segments (0xa3f78 : word) = Some W_a3f78.
Proof. vm_refl. Qed.
Lemma D_a3f78 : decode_any W_a3f78 = Some (OpImm ALU_ADD 10 0 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a3f7c : bv 32 := 0x06913023.
Lemma F_a3f7c : fetch_word Asan.M.loaded_segments (0xa3f7c : word) = Some W_a3f7c.
Proof. vm_refl. Qed.
Lemma D_a3f7c : decode_any W_a3f7c = Some (Store SZ8 2 9 96, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a3f80 : bv 32 := 0x00913823.
Lemma F_a3f80 : fetch_word Asan.M.loaded_segments (0xa3f80 : word) = Some W_a3f80.
Proof. vm_refl. Qed.
Lemma D_a3f80 : decode_any W_a3f80 = Some (Store SZ8 2 9 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a3f84 : bv 32 := 0x00a13c23.
Lemma F_a3f84 : fetch_word Asan.M.loaded_segments (0xa3f84 : word) = Some W_a3f84.
Proof. vm_refl. Qed.
Lemma D_a3f84 : decode_any W_a3f84 = Some (Store SZ8 2 10 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a3f88 : bv 32 := 0x00810513.
Lemma F_a3f88 : fetch_word Asan.M.loaded_segments (0xa3f88 : word) = Some W_a3f88.
Proof. vm_refl. Qed.
Lemma D_a3f88 : decode_any W_a3f88 = Some (OpImm ALU_ADD 10 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a3f8c : bv 32 := 0x00000593.
Lemma F_a3f8c : fetch_word Asan.M.loaded_segments (0xa3f8c : word) = Some W_a3f8c.
Proof. vm_refl. Qed.
Lemma D_a3f8c : decode_any W_a3f8c = Some (OpImm ALU_ADD 11 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a3f90 : bv 32 := 0xc90ff0ef.
Lemma F_a3f90 : fetch_word Asan.M.loaded_segments (0xa3f90 : word) = Some W_a3f90.
Proof. vm_refl. Qed.
Lemma D_a3f90 : decode_any W_a3f90 = Some (Jal 1 2094224, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a3f94 : bv 32 := 0x00810513.
Lemma F_a3f94 : fetch_word Asan.M.loaded_segments (0xa3f94 : word) = Some W_a3f94.
Proof. vm_refl. Qed.
Lemma D_a3f94 : decode_any W_a3f94 = Some (OpImm ALU_ADD 10 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a3f98 : bv 32 := 0x00100613.
Lemma F_a3f98 : fetch_word Asan.M.loaded_segments (0xa3f98 : word) = Some W_a3f98.
Proof. vm_refl. Qed.
Lemma D_a3f98 : decode_any W_a3f98 = Some (OpImm ALU_ADD 12 0 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a3f9c : bv 32 := 0xfff00693.
Lemma F_a3f9c : fetch_word Asan.M.loaded_segments (0xa3f9c : word) = Some W_a3f9c.
Proof. vm_refl. Qed.
Lemma D_a3f9c : decode_any W_a3f9c = Some (OpImm ALU_ADD 13 0 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a3fa0 : bv 32 := 0x00090593.
Lemma F_a3fa0 : fetch_word Asan.M.loaded_segments (0xa3fa0 : word) = Some W_a3fa0.
Proof. vm_refl. Qed.
Lemma D_a3fa0 : decode_any W_a3fa0 = Some (OpImm ALU_ADD 11 18 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a3fa4 : bv 32 := 0xd7cff0ef.
Lemma F_a3fa4 : fetch_word Asan.M.loaded_segments (0xa3fa4 : word) = Some W_a3fa4.
Proof. vm_refl. Qed.
Lemma D_a3fa4 : decode_any W_a3fa4 = Some (Jal 1 2094460, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a3fa8 : bv 32 := 0x02040063.
Lemma F_a3fa8 : fetch_word Asan.M.loaded_segments (0xa3fa8 : word) = Some W_a3fa8.
Proof. vm_refl. Qed.
Lemma D_a3fa8 : decode_any W_a3fa8 = Some (Branch BC_EQ 8 0 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a3fac : bv 32 := 0x01013583.
Lemma F_a3fac : fetch_word Asan.M.loaded_segments (0xa3fac : word) = Some W_a3fac.
Proof. vm_refl. Qed.
Lemma D_a3fac : decode_any W_a3fac = Some (Load SZ8 true 11 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a3fb0 : bv 32 := 0x06013603.
Lemma F_a3fb0 : fetch_word Asan.M.loaded_segments (0xa3fb0 : word) = Some W_a3fb0.
Proof. vm_refl. Qed.
Lemma D_a3fb0 : decode_any W_a3fb0 = Some (Load SZ8 true 12 2 96, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a3fb4 : bv 32 := 0x0d013683.
Lemma F_a3fb4 : fetch_word Asan.M.loaded_segments (0xa3fb4 : word) = Some W_a3fb4.
Proof. vm_refl. Qed.
Lemma D_a3fb4 : decode_any W_a3fb4 = Some (Load SZ8 true 13 2 208, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a3fb8 : bv 32 := 0x40c585b3.
Lemma F_a3fb8 : fetch_word Asan.M.loaded_segments (0xa3fb8 : word) = Some W_a3fb8.
Proof. vm_refl. Qed.
Lemma D_a3fb8 : decode_any W_a3fb8 = Some (Op ALU_SUB 11 11 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a3fbc : bv 32 := 0x00d486b3.
Lemma F_a3fbc : fetch_word Asan.M.loaded_segments (0xa3fbc : word) = Some W_a3fbc.
Proof. vm_refl. Qed.
Lemma D_a3fbc : decode_any W_a3fbc = Some (Op ALU_ADD 13 9 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a3fc0 : bv 32 := 0x00b685b3.
Lemma F_a3fc0 : fetch_word Asan.M.loaded_segments (0xa3fc0 : word) = Some W_a3fc0.
Proof. vm_refl. Qed.
Lemma D_a3fc0 : decode_any W_a3fc0 = Some (Op ALU_ADD 11 13 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a3fc4 : bv 32 := 0x00b43023.
Lemma F_a3fc4 : fetch_word Asan.M.loaded_segments (0xa3fc4 : word) = Some W_a3fc4.
Proof. vm_refl. Qed.
Lemma D_a3fc4 : decode_any W_a3fc4 = Some (Store SZ8 8 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a3fc8 : bv 32 := 0x0009b583.
Lemma F_a3fc8 : fetch_word Asan.M.loaded_segments (0xa3fc8 : word) = Some W_a3fc8.
Proof. vm_refl. Qed.
Lemma D_a3fc8 : decode_any W_a3fc8 = Some (Load SZ8 true 11 19 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a3fcc : bv 32 := 0x0f013603.
Lemma F_a3fcc : fetch_word Asan.M.loaded_segments (0xa3fcc : word) = Some W_a3fcc.
Proof. vm_refl. Qed.
Lemma D_a3fcc : decode_any W_a3fcc = Some (Load SZ8 true 12 2 240, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a3fd0 : bv 32 := 0x02c59063.
Lemma F_a3fd0 : fetch_word Asan.M.loaded_segments (0xa3fd0 : word) = Some W_a3fd0.
Proof. vm_refl. Qed.
Lemma D_a3fd0 : decode_any W_a3fd0 = Some (Branch BC_NE 11 12 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a3fd4 : bv 32 := 0x11813083.
Lemma F_a3fd4 : fetch_word Asan.M.loaded_segments (0xa3fd4 : word) = Some W_a3fd4.
Proof. vm_refl. Qed.
Lemma D_a3fd4 : decode_any W_a3fd4 = Some (Load SZ8 true 1 2 280, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a3fd8 : bv 32 := 0x11013403.
Lemma F_a3fd8 : fetch_word Asan.M.loaded_segments (0xa3fd8 : word) = Some W_a3fd8.
Proof. vm_refl. Qed.
Lemma D_a3fd8 : decode_any W_a3fd8 = Some (Load SZ8 true 8 2 272, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a3fdc : bv 32 := 0x10813483.
Lemma F_a3fdc : fetch_word Asan.M.loaded_segments (0xa3fdc : word) = Some W_a3fdc.
Proof. vm_refl. Qed.
Lemma D_a3fdc : decode_any W_a3fdc = Some (Load SZ8 true 9 2 264, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a3fe0 : bv 32 := 0x10013903.
Lemma F_a3fe0 : fetch_word Asan.M.loaded_segments (0xa3fe0 : word) = Some W_a3fe0.
Proof. vm_refl. Qed.
Lemma D_a3fe0 : decode_any W_a3fe0 = Some (Load SZ8 true 18 2 256, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a3fe4 : bv 32 := 0x0f813983.
Lemma F_a3fe4 : fetch_word Asan.M.loaded_segments (0xa3fe4 : word) = Some W_a3fe4.
Proof. vm_refl. Qed.
Lemma D_a3fe4 : decode_any W_a3fe4 = Some (Load SZ8 true 19 2 248, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a3fe8 : bv 32 := 0x12010113.
Lemma F_a3fe8 : fetch_word Asan.M.loaded_segments (0xa3fe8 : word) = Some W_a3fe8.
Proof. vm_refl. Qed.
Lemma D_a3fe8 : decode_any W_a3fe8 = Some (OpImm ALU_ADD 2 2 288, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a3fec : bv 32 := 0x00008067.
Lemma F_a3fec : fetch_word Asan.M.loaded_segments (0xa3fec : word) = Some W_a3fec.
Proof. vm_refl. Qed.
Lemma D_a3fec : decode_any W_a3fec = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_a3ff0 : bv 32 := 0xe00f60ef.
Lemma F_a3ff0 : fetch_word Asan.M.loaded_segments (0xa3ff0 : word) = Some W_a3ff0.
Proof. vm_refl. Qed.
Lemma D_a3ff0 : decode_any W_a3ff0 = Some (Jal 1 2057728, 4%Z).
Proof. vm_refl. Qed.
