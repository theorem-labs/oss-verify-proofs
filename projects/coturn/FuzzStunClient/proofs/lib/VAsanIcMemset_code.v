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
Definition W_53e28 : bv 32 := 0x6e40006f.
Lemma F_53e28 : fetch_word Asan.M.loaded_segments (0x53e28 : word) = Some W_53e28.
Proof. vm_refl. Qed.
Lemma D_53e28 : decode_any W_53e28 = Some (Jal 0 1764, 4%Z).
Proof. vm_refl. Qed.
(* [comment removed for export] *)
Definition W_5450c : bv 32 := 0x81010113.
Lemma F_5450c : fetch_word Asan.M.loaded_segments (0x5450c : word) = Some W_5450c.
Proof. vm_refl. Qed.
Lemma D_5450c : decode_any W_5450c = Some (OpImm ALU_ADD 2 2 2064, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_54510 : bv 32 := 0x7e113423.
Lemma F_54510 : fetch_word Asan.M.loaded_segments (0x54510 : word) = Some W_54510.
Proof. vm_refl. Qed.
Lemma D_54510 : decode_any W_54510 = Some (Store SZ8 2 1 2024, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_54514 : bv 32 := 0x7e813023.
Lemma F_54514 : fetch_word Asan.M.loaded_segments (0x54514 : word) = Some W_54514.
Proof. vm_refl. Qed.
Lemma D_54514 : decode_any W_54514 = Some (Store SZ8 2 8 2016, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_54518 : bv 32 := 0x7c913c23.
Lemma F_54518 : fetch_word Asan.M.loaded_segments (0x54518 : word) = Some W_54518.
Proof. vm_refl. Qed.
Lemma D_54518 : decode_any W_54518 = Some (Store SZ8 2 9 2008, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5451c : bv 32 := 0x7d213823.
Lemma F_5451c : fetch_word Asan.M.loaded_segments (0x5451c : word) = Some W_5451c.
Proof. vm_refl. Qed.
Lemma D_5451c : decode_any W_5451c = Some (Store SZ8 2 18 2000, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_54520 : bv 32 := 0x7d313423.
Lemma F_54520 : fetch_word Asan.M.loaded_segments (0x54520 : word) = Some W_54520.
Proof. vm_refl. Qed.
Lemma D_54520 : decode_any W_54520 = Some (Store SZ8 2 19 1992, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_54524 : bv 32 := 0x7d413023.
Lemma F_54524 : fetch_word Asan.M.loaded_segments (0x54524 : word) = Some W_54524.
Proof. vm_refl. Qed.
Lemma D_54524 : decode_any W_54524 = Some (Store SZ8 2 20 1984, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_54528 : bv 32 := 0x7b513c23.
Lemma F_54528 : fetch_word Asan.M.loaded_segments (0x54528 : word) = Some W_54528.
Proof. vm_refl. Qed.
Lemma D_54528 : decode_any W_54528 = Some (Store SZ8 2 21 1976, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5452c : bv 32 := 0x7b613823.
Lemma F_5452c : fetch_word Asan.M.loaded_segments (0x5452c : word) = Some W_5452c.
Proof. vm_refl. Qed.
Lemma D_5452c : decode_any W_5452c = Some (Store SZ8 2 22 1968, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_54530 : bv 32 := 0x7f010413.
Lemma F_54530 : fetch_word Asan.M.loaded_segments (0x54530 : word) = Some W_54530.
Proof. vm_refl. Qed.
Lemma D_54530 : decode_any W_54530 = Some (OpImm ALU_ADD 8 2 2032, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_54534 : bv 32 := 0xf9010113.
Lemma F_54534 : fetch_word Asan.M.loaded_segments (0x54534 : word) = Some W_54534.
Proof. vm_refl. Qed.
Lemma D_54534 : decode_any W_54534 = Some (OpImm ALU_ADD 2 2 3984, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_54538 : bv 32 := 0x00057697.
Lemma F_54538 : fetch_word Asan.M.loaded_segments (0x54538 : word) = Some W_54538.
Proof. vm_refl. Qed.
Lemma D_54538 : decode_any W_54538 = Some (Auipc 13 87, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5453c : bv 32 := 0x4b06b683.
Lemma F_5453c : fetch_word Asan.M.loaded_segments (0x5453c : word) = Some W_5453c.
Proof. vm_refl. Qed.
Lemma D_5453c : decode_any W_5453c = Some (Load SZ8 true 13 13 1200, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_54540 : bv 32 := 0x0006c683.
Lemma F_54540 : fetch_word Asan.M.loaded_segments (0x54540 : word) = Some W_54540.
Proof. vm_refl. Qed.
Lemma D_54540 : decode_any W_54540 = Some (Load SZ1 false 13 13 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_54544 : bv 32 := 0x08068a63.
Lemma F_54544 : fetch_word Asan.M.loaded_segments (0x54544 : word) = Some W_54544.
Proof. vm_refl. Qed.
Lemma D_54544 : decode_any W_54544 = Some (Branch BC_EQ 13 0 148, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_54548 : bv 32 := 0xfff54693.
Lemma F_54548 : fetch_word Asan.M.loaded_segments (0x54548 : word) = Some W_54548.
Proof. vm_refl. Qed.
Lemma D_54548 : decode_any W_54548 = Some (OpImm ALU_XOR 13 10 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5454c : bv 32 := 0x80040a93.
Lemma F_5454c : fetch_word Asan.M.loaded_segments (0x5454c : word) = Some W_5454c.
Proof. vm_refl. Qed.
Lemma D_5454c : decode_any W_5454c = Some (OpImm ALU_ADD 21 8 2048, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_54550 : bv 32 := 0xfa8a8a93.
Lemma F_54550 : fetch_word Asan.M.loaded_segments (0x54550 : word) = Some W_54550.
Proof. vm_refl. Qed.
Lemma D_54550 : decode_any W_54550 = Some (OpImm ALU_ADD 21 21 4008, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_54554 : bv 32 := 0x0cc6ea63.
Lemma F_54554 : fetch_word Asan.M.loaded_segments (0x54554 : word) = Some W_54554.
Proof. vm_refl. Qed.
Lemma D_54554 : decode_any W_54554 = Some (Branch BC_LTU 13 12 212, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_54558 : bv 32 := 0xfbf60693.
Lemma F_54558 : fetch_word Asan.M.loaded_segments (0x54558 : word) = Some W_54558.
Proof. vm_refl. Qed.
Lemma D_54558 : decode_any W_54558 = Some (OpImm ALU_ADD 13 12 4031, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5455c : bv 32 := 0xfbf00713.
Lemma F_5455c : fetch_word Asan.M.loaded_segments (0x5455c : word) = Some W_5455c.
Proof. vm_refl. Qed.
Lemma D_5455c : decode_any W_5455c = Some (OpImm ALU_ADD 14 0 4031, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_54560 : bv 32 := 0x14d77863.
Lemma F_54560 : fetch_word Asan.M.loaded_segments (0x54560 : word) = Some W_54560.
Proof. vm_refl. Qed.
Lemma D_54560 : decode_any W_54560 = Some (Branch BC_GEU 14 13 336, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_54564 : bv 32 := 0x00057697.
Lemma F_54564 : fetch_word Asan.M.loaded_segments (0x54564 : word) = Some W_54564.
Proof. vm_refl. Qed.
Lemma D_54564 : decode_any W_54564 = Some (Auipc 13 87, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_54568 : bv 32 := 0x91c6b683.
Lemma F_54568 : fetch_word Asan.M.loaded_segments (0x54568 : word) = Some W_54568.
Proof. vm_refl. Qed.
Lemma D_54568 : decode_any W_54568 = Some (Load SZ8 true 13 13 2332, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5456c : bv 32 := 0x00c507b3.
Lemma F_5456c : fetch_word Asan.M.loaded_segments (0x5456c : word) = Some W_5456c.
Proof. vm_refl. Qed.
Lemma D_5456c : decode_any W_5456c = Some (Op ALU_ADD 15 10 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_54570 : bv 32 := 0x0006b703.
Lemma F_54570 : fetch_word Asan.M.loaded_segments (0x54570 : word) = Some W_54570.
Proof. vm_refl. Qed.
Lemma D_54570 : decode_any W_54570 = Some (Load SZ8 true 14 13 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_54574 : bv 32 := 0x00355693.
Lemma F_54574 : fetch_word Asan.M.loaded_segments (0x54574 : word) = Some W_54574.
Proof. vm_refl. Qed.
Lemma D_54574 : decode_any W_54574 = Some (ShiftImm ALU_SRL 13 10 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_54578 : bv 32 := 0xfff78793.
Lemma F_54578 : fetch_word Asan.M.loaded_segments (0x54578 : word) = Some W_54578.
Proof. vm_refl. Qed.
Lemma D_54578 : decode_any W_54578 = Some (OpImm ALU_ADD 15 15 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5457c : bv 32 := 0x0037d813.
Lemma F_5457c : fetch_word Asan.M.loaded_segments (0x5457c : word) = Some W_5457c.
Proof. vm_refl. Qed.
Lemma D_5457c : decode_any W_5457c = Some (ShiftImm ALU_SRL 16 15 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_54580 : bv 32 := 0x00d706b3.
Lemma F_54580 : fetch_word Asan.M.loaded_segments (0x54580 : word) = Some W_54580.
Proof. vm_refl. Qed.
Lemma D_54580 : decode_any W_54580 = Some (Op ALU_ADD 13 14 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_54584 : bv 32 := 0x01070733.
Lemma F_54584 : fetch_word Asan.M.loaded_segments (0x54584 : word) = Some W_54584.
Proof. vm_refl. Qed.
Lemma D_54584 : decode_any W_54584 = Some (Op ALU_ADD 14 14 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_54588 : bv 32 := 0xff86f813.
Lemma F_54588 : fetch_word Asan.M.loaded_segments (0x54588 : word) = Some W_54588.
Proof. vm_refl. Qed.
Lemma D_54588 : decode_any W_54588 = Some (OpImm ALU_AND 16 13 4088, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5458c : bv 32 := 0xff877893.
Lemma F_5458c : fetch_word Asan.M.loaded_segments (0x5458c : word) = Some W_5458c.
Proof. vm_refl. Qed.
Lemma D_5458c : decode_any W_5458c = Some (OpImm ALU_AND 17 14 4088, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_54590 : bv 32 := 0x00083803.
Lemma F_54590 : fetch_word Asan.M.loaded_segments (0x54590 : word) = Some W_54590.
Proof. vm_refl. Qed.
Lemma D_54590 : decode_any W_54590 = Some (Load SZ8 true 16 16 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_54594 : bv 32 := 0x0008b883.
Lemma F_54594 : fetch_word Asan.M.loaded_segments (0x54594 : word) = Some W_54594.
Proof. vm_refl. Qed.
Lemma D_54594 : decode_any W_54594 = Some (Load SZ8 true 17 17 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_54598 : bv 32 := 0x0108e833.
Lemma F_54598 : fetch_word Asan.M.loaded_segments (0x54598 : word) = Some W_54598.
Proof. vm_refl. Qed.
Lemma D_54598 : decode_any W_54598 = Some (Op ALU_OR 16 17 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5459c : bv 32 := 0x10081e63.
Lemma F_5459c : fetch_word Asan.M.loaded_segments (0x5459c : word) = Some W_5459c.
Proof. vm_refl. Qed.
Lemma D_5459c : decode_any W_5459c = Some (Branch BC_NE 16 0 284, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_545a0 : bv 32 := 0x00058697.
Lemma F_545a0 : fetch_word Asan.M.loaded_segments (0x545a0 : word) = Some W_545a0.
Proof. vm_refl. Qed.
Lemma D_545a0 : decode_any W_545a0 = Some (Auipc 13 88, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_545a4 : bv 32 := 0x7506b683.
Lemma F_545a4 : fetch_word Asan.M.loaded_segments (0x545a4 : word) = Some W_545a4.
Proof. vm_refl. Qed.
Lemma D_545a4 : decode_any W_545a4 = Some (Load SZ8 true 13 13 1872, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_545a8 : bv 32 := 0x000680e7.
Lemma F_545a8 : fetch_word Asan.M.loaded_segments (0x545a8 : word) = Some W_545a8.
Proof. vm_refl. Qed.
Lemma D_545a8 : decode_any W_545a8 = Some (Jalr 1 13 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_545ac : bv 32 := 0x07010113.
Lemma F_545ac : fetch_word Asan.M.loaded_segments (0x545ac : word) = Some W_545ac.
Proof. vm_refl. Qed.
Lemma D_545ac : decode_any W_545ac = Some (OpImm ALU_ADD 2 2 112, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_545b0 : bv 32 := 0x7e813083.
Lemma F_545b0 : fetch_word Asan.M.loaded_segments (0x545b0 : word) = Some W_545b0.
Proof. vm_refl. Qed.
Lemma D_545b0 : decode_any W_545b0 = Some (Load SZ8 true 1 2 2024, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_545b4 : bv 32 := 0x7e013403.
Lemma F_545b4 : fetch_word Asan.M.loaded_segments (0x545b4 : word) = Some W_545b4.
Proof. vm_refl. Qed.
Lemma D_545b4 : decode_any W_545b4 = Some (Load SZ8 true 8 2 2016, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_545b8 : bv 32 := 0x7d813483.
Lemma F_545b8 : fetch_word Asan.M.loaded_segments (0x545b8 : word) = Some W_545b8.
Proof. vm_refl. Qed.
Lemma D_545b8 : decode_any W_545b8 = Some (Load SZ8 true 9 2 2008, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_545bc : bv 32 := 0x7d013903.
Lemma F_545bc : fetch_word Asan.M.loaded_segments (0x545bc : word) = Some W_545bc.
Proof. vm_refl. Qed.
Lemma D_545bc : decode_any W_545bc = Some (Load SZ8 true 18 2 2000, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_545c0 : bv 32 := 0x7c813983.
Lemma F_545c0 : fetch_word Asan.M.loaded_segments (0x545c0 : word) = Some W_545c0.
Proof. vm_refl. Qed.
Lemma D_545c0 : decode_any W_545c0 = Some (Load SZ8 true 19 2 1992, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_545c4 : bv 32 := 0x7c013a03.
Lemma F_545c4 : fetch_word Asan.M.loaded_segments (0x545c4 : word) = Some W_545c4.
Proof. vm_refl. Qed.
Lemma D_545c4 : decode_any W_545c4 = Some (Load SZ8 true 20 2 1984, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_545c8 : bv 32 := 0x7b813a83.
Lemma F_545c8 : fetch_word Asan.M.loaded_segments (0x545c8 : word) = Some W_545c8.
Proof. vm_refl. Qed.
Lemma D_545c8 : decode_any W_545c8 = Some (Load SZ8 true 21 2 1976, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_545cc : bv 32 := 0x7b013b03.
Lemma F_545cc : fetch_word Asan.M.loaded_segments (0x545cc : word) = Some W_545cc.
Proof. vm_refl. Qed.
Lemma D_545cc : decode_any W_545cc = Some (Load SZ8 true 22 2 1968, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_545d0 : bv 32 := 0x7f010113.
Lemma F_545d0 : fetch_word Asan.M.loaded_segments (0x545d0 : word) = Some W_545d0.
Proof. vm_refl. Qed.
Lemma D_545d0 : decode_any W_545d0 = Some (OpImm ALU_ADD 2 2 2032, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_545d4 : bv 32 := 0x00008067.
Lemma F_545d4 : fetch_word Asan.M.loaded_segments (0x545d4 : word) = Some W_545d4.
Proof. vm_refl. Qed.
Lemma D_545d4 : decode_any W_545d4 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_545d8 : bv 32 := 0x00060913.
Lemma F_545d8 : fetch_word Asan.M.loaded_segments (0x545d8 : word) = Some W_545d8.
Proof. vm_refl. Qed.
Lemma D_545d8 : decode_any W_545d8 = Some (OpImm ALU_ADD 18 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_545dc : bv 32 := 0x00058993.
Lemma F_545dc : fetch_word Asan.M.loaded_segments (0x545dc : word) = Some W_545dc.
Proof. vm_refl. Qed.
Lemma D_545dc : decode_any W_545dc = Some (OpImm ALU_ADD 19 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_545e0 : bv 32 := 0x00050493.
Lemma F_545e0 : fetch_word Asan.M.loaded_segments (0x545e0 : word) = Some W_545e0.
Proof. vm_refl. Qed.
Lemma D_545e0 : decode_any W_545e0 = Some (OpImm ALU_ADD 9 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_545e4 : bv 32 := 0x14d060ef.
Lemma F_545e4 : fetch_word Asan.M.loaded_segments (0x545e4 : word) = Some W_545e4.
Proof. vm_refl. Qed.
Lemma D_545e4 : decode_any W_545e4 = Some (Jal 1 26956, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_545e8 : bv 32 := 0x00098593.
Lemma F_545e8 : fetch_word Asan.M.loaded_segments (0x545e8 : word) = Some W_545e8.
Proof. vm_refl. Qed.
Lemma D_545e8 : decode_any W_545e8 = Some (OpImm ALU_ADD 11 19 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_545ec : bv 32 := 0x00090613.
Lemma F_545ec : fetch_word Asan.M.loaded_segments (0x545ec : word) = Some W_545ec.
Proof. vm_refl. Qed.
Lemma D_545ec : decode_any W_545ec = Some (OpImm ALU_ADD 12 18 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_545f0 : bv 32 := 0x00050693.
Lemma F_545f0 : fetch_word Asan.M.loaded_segments (0x545f0 : word) = Some W_545f0.
Proof. vm_refl. Qed.
Lemma D_545f0 : decode_any W_545f0 = Some (OpImm ALU_ADD 13 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_545f4 : bv 32 := 0x00048513.
Lemma F_545f4 : fetch_word Asan.M.loaded_segments (0x545f4 : word) = Some W_545f4.
Proof. vm_refl. Qed.
Lemma D_545f4 : decode_any W_545f4 = Some (OpImm ALU_ADD 10 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_545f8 : bv 32 := 0xfa0694e3.
Lemma F_545f8 : fetch_word Asan.M.loaded_segments (0x545f8 : word) = Some W_545f8.
Proof. vm_refl. Qed.
Lemma D_545f8 : decode_any W_545f8 = Some (Branch BC_NE 13 0 8104, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_545fc : bv 32 := 0x07010113.
Lemma F_545fc : fetch_word Asan.M.loaded_segments (0x545fc : word) = Some W_545fc.
Proof. vm_refl. Qed.
Lemma D_545fc : decode_any W_545fc = Some (OpImm ALU_ADD 2 2 112, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_54600 : bv 32 := 0x7e813083.
Lemma F_54600 : fetch_word Asan.M.loaded_segments (0x54600 : word) = Some W_54600.
Proof. vm_refl. Qed.
Lemma D_54600 : decode_any W_54600 = Some (Load SZ8 true 1 2 2024, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_54604 : bv 32 := 0x7e013403.
Lemma F_54604 : fetch_word Asan.M.loaded_segments (0x54604 : word) = Some W_54604.
Proof. vm_refl. Qed.
Lemma D_54604 : decode_any W_54604 = Some (Load SZ8 true 8 2 2016, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_54608 : bv 32 := 0x7d813483.
Lemma F_54608 : fetch_word Asan.M.loaded_segments (0x54608 : word) = Some W_54608.
Proof. vm_refl. Qed.
Lemma D_54608 : decode_any W_54608 = Some (Load SZ8 true 9 2 2008, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5460c : bv 32 := 0x7d013903.
Lemma F_5460c : fetch_word Asan.M.loaded_segments (0x5460c : word) = Some W_5460c.
Proof. vm_refl. Qed.
Lemma D_5460c : decode_any W_5460c = Some (Load SZ8 true 18 2 2000, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_54610 : bv 32 := 0x7c813983.
Lemma F_54610 : fetch_word Asan.M.loaded_segments (0x54610 : word) = Some W_54610.
Proof. vm_refl. Qed.
Lemma D_54610 : decode_any W_54610 = Some (Load SZ8 true 19 2 1992, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_54614 : bv 32 := 0x7c013a03.
Lemma F_54614 : fetch_word Asan.M.loaded_segments (0x54614 : word) = Some W_54614.
Proof. vm_refl. Qed.
Lemma D_54614 : decode_any W_54614 = Some (Load SZ8 true 20 2 1984, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_54618 : bv 32 := 0x7b813a83.
Lemma F_54618 : fetch_word Asan.M.loaded_segments (0x54618 : word) = Some W_54618.
Proof. vm_refl. Qed.
Lemma D_54618 : decode_any W_54618 = Some (Load SZ8 true 21 2 1976, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5461c : bv 32 := 0x7b013b03.
Lemma F_5461c : fetch_word Asan.M.loaded_segments (0x5461c : word) = Some W_5461c.
Proof. vm_refl. Qed.
Lemma D_5461c : decode_any W_5461c = Some (Load SZ8 true 22 2 1968, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_54620 : bv 32 := 0x7f010113.
Lemma F_54620 : fetch_word Asan.M.loaded_segments (0x54620 : word) = Some W_54620.
Proof. vm_refl. Qed.
Lemma D_54620 : decode_any W_54620 = Some (OpImm ALU_ADD 2 2 2032, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_54624 : bv 32 := 0x3991106f.
Lemma F_54624 : fetch_word Asan.M.loaded_segments (0x54624 : word) = Some W_54624.
Proof. vm_refl. Qed.
Lemma D_54624 : decode_any W_54624 = Some (Jal 0 72600, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_54628 : bv 32 := 0x80040693.
Lemma F_54628 : fetch_word Asan.M.loaded_segments (0x54628 : word) = Some W_54628.
Proof. vm_refl. Qed.
Lemma D_54628 : decode_any W_54628 = Some (OpImm ALU_ADD 13 8 2048, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5462c : bv 32 := 0xfb868693.
Lemma F_5462c : fetch_word Asan.M.loaded_segments (0x5462c : word) = Some W_5462c.
Proof. vm_refl. Qed.
Lemma D_5462c : decode_any W_5462c = Some (OpImm ALU_ADD 13 13 4024, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_54630 : bv 32 := 0x80040713.
Lemma F_54630 : fetch_word Asan.M.loaded_segments (0x54630 : word) = Some W_54630.
Proof. vm_refl. Qed.
Lemma D_54630 : decode_any W_54630 = Some (OpImm ALU_ADD 14 8 2048, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_54634 : bv 32 := 0xfa870713.
Lemma F_54634 : fetch_word Asan.M.loaded_segments (0x54634 : word) = Some W_54634.
Proof. vm_refl. Qed.
Lemma D_54634 : decode_any W_54634 = Some (OpImm ALU_ADD 14 14 4008, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_54638 : bv 32 := 0x7ff70a13.
Lemma F_54638 : fetch_word Asan.M.loaded_segments (0x54638 : word) = Some W_54638.
Proof. vm_refl. Qed.
Lemma D_54638 : decode_any W_54638 = Some (OpImm ALU_ADD 20 14 2047, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5463c : bv 32 := 0x000a34a3.
Lemma F_5463c : fetch_word Asan.M.loaded_segments (0x5463c : word) = Some W_5463c.
Proof. vm_refl. Qed.
Lemma D_5463c : decode_any W_5463c = Some (Store SZ8 20 0 9, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_54640 : bv 32 := 0x00dab023.
Lemma F_54640 : fetch_word Asan.M.loaded_segments (0x54640 : word) = Some W_54640.
Proof. vm_refl. Qed.
Lemma D_54640 : decode_any W_54640 = Some (Store SZ8 21 13 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_54644 : bv 32 := 0x000ab423.
Lemma F_54644 : fetch_word Asan.M.loaded_segments (0x54644 : word) = Some W_54644.
Proof. vm_refl. Qed.
Lemma D_54644 : decode_any W_54644 = Some (Store SZ8 21 0 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_54648 : bv 32 := 0x00060493.
Lemma F_54648 : fetch_word Asan.M.loaded_segments (0x54648 : word) = Some W_54648.
Proof. vm_refl. Qed.
Lemma D_54648 : decode_any W_54648 = Some (OpImm ALU_ADD 9 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5464c : bv 32 := 0x00058993.
Lemma F_5464c : fetch_word Asan.M.loaded_segments (0x5464c : word) = Some W_5464c.
Proof. vm_refl. Qed.
Lemma D_5464c : decode_any W_5464c = Some (OpImm ALU_ADD 19 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_54650 : bv 32 := 0x00050913.
Lemma F_54650 : fetch_word Asan.M.loaded_segments (0x54650 : word) = Some W_54650.
Proof. vm_refl. Qed.
Lemma D_54650 : decode_any W_54650 = Some (OpImm ALU_ADD 18 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_54654 : bv 32 := 0x034210ef.
Lemma F_54654 : fetch_word Asan.M.loaded_segments (0x54654 : word) = Some W_54654.
Proof. vm_refl. Qed.
Lemma D_54654 : decode_any W_54654 = Some (Jal 1 135220, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_54658 : bv 32 := 0x00050593.
Lemma F_54658 : fetch_word Asan.M.loaded_segments (0x54658 : word) = Some W_54658.
Proof. vm_refl. Qed.
Lemma D_54658 : decode_any W_54658 = Some (OpImm ALU_ADD 11 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5465c : bv 32 := 0x00057517.
Lemma F_5465c : fetch_word Asan.M.loaded_segments (0x5465c : word) = Some W_5465c.
Proof. vm_refl. Qed.
Lemma D_5465c : decode_any W_5465c = Some (Auipc 10 87, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_54660 : bv 32 := 0x81453503.
Lemma F_54660 : fetch_word Asan.M.loaded_segments (0x54660 : word) = Some W_54660.
Proof. vm_refl. Qed.
Lemma D_54660 : decode_any W_54660 = Some (Load SZ8 true 10 10 2068, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_54664 : bv 32 := 0x02154703.
Lemma F_54664 : fetch_word Asan.M.loaded_segments (0x54664 : word) = Some W_54664.
Proof. vm_refl. Qed.
Lemma D_54664 : decode_any W_54664 = Some (Load SZ1 false 14 10 33, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_54668 : bv 32 := 0x008a34a3.
Lemma F_54668 : fetch_word Asan.M.loaded_segments (0x54668 : word) = Some W_54668.
Proof. vm_refl. Qed.
Lemma D_54668 : decode_any W_54668 = Some (Store SZ8 20 8 9, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5466c : bv 32 := 0x80040513.
Lemma F_5466c : fetch_word Asan.M.loaded_segments (0x5466c : word) = Some W_5466c.
Proof. vm_refl. Qed.
Lemma D_5466c : decode_any W_5466c = Some (OpImm ALU_ADD 10 8 2048, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_54670 : bv 32 := 0xfa850513.
Lemma F_54670 : fetch_word Asan.M.loaded_segments (0x54670 : word) = Some W_54670.
Proof. vm_refl. Qed.
Lemma D_54670 : decode_any W_54670 = Some (OpImm ALU_ADD 10 10 4008, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_54674 : bv 32 := 0x0ff00793.
Lemma F_54674 : fetch_word Asan.M.loaded_segments (0x54674 : word) = Some W_54674.
Proof. vm_refl. Qed.
Lemma D_54674 : decode_any W_54674 = Some (OpImm ALU_ADD 15 0 255, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_54678 : bv 32 := 0x00040613.
Lemma F_54678 : fetch_word Asan.M.loaded_segments (0x54678 : word) = Some W_54678.
Proof. vm_refl. Qed.
Lemma D_54678 : decode_any W_54678 = Some (OpImm ALU_ADD 12 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5467c : bv 32 := 0x00000693.
Lemma F_5467c : fetch_word Asan.M.loaded_segments (0x5467c : word) = Some W_5467c.
Proof. vm_refl. Qed.
Lemma D_5467c : decode_any W_5467c = Some (OpImm ALU_ADD 13 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_54680 : bv 32 := 0x558080ef.
Lemma F_54680 : fetch_word Asan.M.loaded_segments (0x54680 : word) = Some W_54680.
Proof. vm_refl. Qed.
Lemma D_54680 : decode_any W_54680 = Some (Jal 1 34136, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_54684 : bv 32 := 0x80040613.
Lemma F_54684 : fetch_word Asan.M.loaded_segments (0x54684 : word) = Some W_54684.
Proof. vm_refl. Qed.
Lemma D_54684 : decode_any W_54684 = Some (OpImm ALU_ADD 12 8 2048, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_54688 : bv 32 := 0xfa860613.
Lemma F_54688 : fetch_word Asan.M.loaded_segments (0x54688 : word) = Some W_54688.
Proof. vm_refl. Qed.
Lemma D_54688 : decode_any W_54688 = Some (OpImm ALU_ADD 12 12 4008, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5468c : bv 32 := 0x00090513.
Lemma F_5468c : fetch_word Asan.M.loaded_segments (0x5468c : word) = Some W_5468c.
Proof. vm_refl. Qed.
Lemma D_5468c : decode_any W_5468c = Some (OpImm ALU_ADD 10 18 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_54690 : bv 32 := 0x00048593.
Lemma F_54690 : fetch_word Asan.M.loaded_segments (0x54690 : word) = Some W_54690.
Proof. vm_refl. Qed.
Lemma D_54690 : decode_any W_54690 = Some (OpImm ALU_ADD 11 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_54694 : bv 32 := 0x2fc050ef.
Lemma F_54694 : fetch_word Asan.M.loaded_segments (0x54694 : word) = Some W_54694.
Proof. vm_refl. Qed.
Lemma D_54694 : decode_any W_54694 = Some (Jal 1 21244, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_54698 : bv 32 := 0x00090513.
Lemma F_54698 : fetch_word Asan.M.loaded_segments (0x54698 : word) = Some W_54698.
Proof. vm_refl. Qed.
Lemma D_54698 : decode_any W_54698 = Some (OpImm ALU_ADD 10 18 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5469c : bv 32 := 0x00098593.
Lemma F_5469c : fetch_word Asan.M.loaded_segments (0x5469c : word) = Some W_5469c.
Proof. vm_refl. Qed.
Lemma D_5469c : decode_any W_5469c = Some (OpImm ALU_ADD 11 19 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_546a0 : bv 32 := 0x00048613.
Lemma F_546a0 : fetch_word Asan.M.loaded_segments (0x546a0 : word) = Some W_546a0.
Proof. vm_refl. Qed.
Lemma D_546a0 : decode_any W_546a0 = Some (OpImm ALU_ADD 12 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_546a4 : bv 32 := 0xfbf48693.
Lemma F_546a4 : fetch_word Asan.M.loaded_segments (0x546a4 : word) = Some W_546a4.
Proof. vm_refl. Qed.
Lemma D_546a4 : decode_any W_546a4 = Some (OpImm ALU_ADD 13 9 4031, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_546a8 : bv 32 := 0xfbf00713.
Lemma F_546a8 : fetch_word Asan.M.loaded_segments (0x546a8 : word) = Some W_546a8.
Proof. vm_refl. Qed.
Lemma D_546a8 : decode_any W_546a8 = Some (OpImm ALU_ADD 14 0 4031, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_546ac : bv 32 := 0xead76ce3.
Lemma F_546ac : fetch_word Asan.M.loaded_segments (0x546ac : word) = Some W_546ac.
Proof. vm_refl. Qed.
Lemma D_546ac : decode_any W_546ac = Some (Branch BC_LTU 14 13 7864, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_546b0 : bv 32 := 0x02061e63.
Lemma F_546b0 : fetch_word Asan.M.loaded_segments (0x546b0 : word) = Some W_546b0.
Proof. vm_refl. Qed.
Lemma D_546b0 : decode_any W_546b0 = Some (Branch BC_NE 12 0 60, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_546b4 : bv 32 := 0xeedff06f.
Lemma F_546b4 : fetch_word Asan.M.loaded_segments (0x546b4 : word) = Some W_546b4.
Proof. vm_refl. Qed.
Lemma D_546b4 : decode_any W_546b4 = Some (Jal 0 2096876, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_546b8 : bv 32 := 0x00070803.
Lemma F_546b8 : fetch_word Asan.M.loaded_segments (0x546b8 : word) = Some W_546b8.
Proof. vm_refl. Qed.
Lemma D_546b8 : decode_any W_546b8 = Some (Load SZ1 true 16 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_546bc : bv 32 := 0x0077f793.
Lemma F_546bc : fetch_word Asan.M.loaded_segments (0x546bc : word) = Some W_546bc.
Proof. vm_refl. Qed.
Lemma D_546bc : decode_any W_546bc = Some (OpImm ALU_AND 15 15 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_546c0 : bv 32 := 0x010038b3.
Lemma F_546c0 : fetch_word Asan.M.loaded_segments (0x546c0 : word) = Some W_546c0.
Proof. vm_refl. Qed.
Lemma D_546c0 : decode_any W_546c0 = Some (Op ALU_SLTU 17 0 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_546c4 : bv 32 := 0x0107a7b3.
Lemma F_546c4 : fetch_word Asan.M.loaded_segments (0x546c4 : word) = Some W_546c4.
Proof. vm_refl. Qed.
Lemma D_546c4 : decode_any W_546c4 = Some (Op ALU_SLT 15 15 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_546c8 : bv 32 := 0x0017c793.
Lemma F_546c8 : fetch_word Asan.M.loaded_segments (0x546c8 : word) = Some W_546c8.
Proof. vm_refl. Qed.
Lemma D_546c8 : decode_any W_546c8 = Some (OpImm ALU_XOR 15 15 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_546cc : bv 32 := 0x00f8f7b3.
Lemma F_546cc : fetch_word Asan.M.loaded_segments (0x546cc : word) = Some W_546cc.
Proof. vm_refl. Qed.
Lemma D_546cc : decode_any W_546cc = Some (Op ALU_AND 15 17 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_546d0 : bv 32 := 0x00e6fa63.
Lemma F_546d0 : fetch_word Asan.M.loaded_segments (0x546d0 : word) = Some W_546d0.
Proof. vm_refl. Qed.
Lemma D_546d0 : decode_any W_546d0 = Some (Branch BC_GEU 13 14 20, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_546d4 : bv 32 := 0x0006c803.
Lemma F_546d4 : fetch_word Asan.M.loaded_segments (0x546d4 : word) = Some W_546d4.
Proof. vm_refl. Qed.
Lemma D_546d4 : decode_any W_546d4 = Some (Load SZ1 false 16 13 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_546d8 : bv 32 := 0x00168693.
Lemma F_546d8 : fetch_word Asan.M.loaded_segments (0x546d8 : word) = Some W_546d8.
Proof. vm_refl. Qed.
Lemma D_546d8 : decode_any W_546d8 = Some (OpImm ALU_ADD 13 13 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_546dc : bv 32 := 0x00f867b3.
Lemma F_546dc : fetch_word Asan.M.loaded_segments (0x546dc : word) = Some W_546dc.
Proof. vm_refl. Qed.
Lemma D_546dc : decode_any W_546dc = Some (Op ALU_OR 15 16 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_546e0 : bv 32 := 0xfee69ae3.
Lemma F_546e0 : fetch_word Asan.M.loaded_segments (0x546e0 : word) = Some W_546e0.
Proof. vm_refl. Qed.
Lemma D_546e0 : decode_any W_546e0 = Some (Branch BC_NE 13 14 8180, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_546e4 : bv 32 := 0x0ff7f693.
Lemma F_546e4 : fetch_word Asan.M.loaded_segments (0x546e4 : word) = Some W_546e4.
Proof. vm_refl. Qed.
Lemma D_546e4 : decode_any W_546e4 = Some (OpImm ALU_AND 13 15 255, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_546e8 : bv 32 := 0xea068ce3.
Lemma F_546e8 : fetch_word Asan.M.loaded_segments (0x546e8 : word) = Some W_546e8.
Proof. vm_refl. Qed.
Lemma D_546e8 : decode_any W_546e8 = Some (Branch BC_EQ 13 0 7864, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_546ec : bv 32 := 0x00050493.
Lemma F_546ec : fetch_word Asan.M.loaded_segments (0x546ec : word) = Some W_546ec.
Proof. vm_refl. Qed.
Lemma D_546ec : decode_any W_546ec = Some (OpImm ALU_ADD 9 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_546f0 : bv 32 := 0x00058b13.
Lemma F_546f0 : fetch_word Asan.M.loaded_segments (0x546f0 : word) = Some W_546f0.
Proof. vm_refl. Qed.
Lemma D_546f0 : decode_any W_546f0 = Some (OpImm ALU_ADD 22 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_546f4 : bv 32 := 0x00060593.
Lemma F_546f4 : fetch_word Asan.M.loaded_segments (0x546f4 : word) = Some W_546f4.
Proof. vm_refl. Qed.
Lemma D_546f4 : decode_any W_546f4 = Some (OpImm ALU_ADD 11 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_546f8 : bv 32 := 0x00060913.
Lemma F_546f8 : fetch_word Asan.M.loaded_segments (0x546f8 : word) = Some W_546f8.
Proof. vm_refl. Qed.
Lemma D_546f8 : decode_any W_546f8 = Some (OpImm ALU_ADD 18 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_546fc : bv 32 := 0x2b0020ef.
Lemma F_546fc : fetch_word Asan.M.loaded_segments (0x546fc : word) = Some W_546fc.
Proof. vm_refl. Qed.
Lemma D_546fc : decode_any W_546fc = Some (Jal 1 8880, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_54700 : bv 32 := 0x000b0593.
Lemma F_54700 : fetch_word Asan.M.loaded_segments (0x54700 : word) = Some W_54700.
Proof. vm_refl. Qed.
Lemma D_54700 : decode_any W_54700 = Some (OpImm ALU_ADD 11 22 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_54704 : bv 32 := 0x00090613.
Lemma F_54704 : fetch_word Asan.M.loaded_segments (0x54704 : word) = Some W_54704.
Proof. vm_refl. Qed.
Lemma D_54704 : decode_any W_54704 = Some (OpImm ALU_ADD 12 18 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_54708 : bv 32 := 0x00050993.
Lemma F_54708 : fetch_word Asan.M.loaded_segments (0x54708 : word) = Some W_54708.
Proof. vm_refl. Qed.
Lemma D_54708 : decode_any W_54708 = Some (OpImm ALU_ADD 19 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5470c : bv 32 := 0x00048513.
Lemma F_5470c : fetch_word Asan.M.loaded_segments (0x5470c : word) = Some W_5470c.
Proof. vm_refl. Qed.
Lemma D_5470c : decode_any W_5470c = Some (OpImm ALU_ADD 10 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_54710 : bv 32 := 0xe80988e3.
Lemma F_54710 : fetch_word Asan.M.loaded_segments (0x54710 : word) = Some W_54710.
Proof. vm_refl. Qed.
Lemma D_54710 : decode_any W_54710 = Some (Branch BC_EQ 19 0 7824, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_54714 : bv 32 := 0xfffc5517.
Lemma F_54714 : fetch_word Asan.M.loaded_segments (0x54714 : word) = Some W_54714.
Proof. vm_refl. Qed.
Lemma D_54714 : decode_any W_54714 = Some (Auipc 10 1048517, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_54718 : bv 32 := 0xfa650513.
Lemma F_54718 : fetch_word Asan.M.loaded_segments (0x54718 : word) = Some W_54718.
Proof. vm_refl. Qed.
Lemma D_54718 : decode_any W_54718 = Some (OpImm ALU_ADD 10 10 4006, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5471c : bv 32 := 0x468090ef.
Lemma F_5471c : fetch_word Asan.M.loaded_segments (0x5471c : word) = Some W_5471c.
Proof. vm_refl. Qed.
Lemma D_5471c : decode_any W_5471c = Some (Jal 1 37992, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_54720 : bv 32 := 0x000b0593.
Lemma F_54720 : fetch_word Asan.M.loaded_segments (0x54720 : word) = Some W_54720.
Proof. vm_refl. Qed.
Lemma D_54720 : decode_any W_54720 = Some (OpImm ALU_ADD 11 22 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_54724 : bv 32 := 0x00090613.
Lemma F_54724 : fetch_word Asan.M.loaded_segments (0x54724 : word) = Some W_54724.
Proof. vm_refl. Qed.
Lemma D_54724 : decode_any W_54724 = Some (OpImm ALU_ADD 12 18 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_54728 : bv 32 := 0x00050693.
Lemma F_54728 : fetch_word Asan.M.loaded_segments (0x54728 : word) = Some W_54728.
Proof. vm_refl. Qed.
Lemma D_54728 : decode_any W_54728 = Some (OpImm ALU_ADD 13 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5472c : bv 32 := 0x00048513.
Lemma F_5472c : fetch_word Asan.M.loaded_segments (0x5472c : word) = Some W_5472c.
Proof. vm_refl. Qed.
Lemma D_5472c : decode_any W_5472c = Some (OpImm ALU_ADD 10 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_54730 : bv 32 := 0xe60698e3.
Lemma F_54730 : fetch_word Asan.M.loaded_segments (0x54730 : word) = Some W_54730.
Proof. vm_refl. Qed.
Lemma D_54730 : decode_any W_54730 = Some (Branch BC_NE 13 0 7792, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_54734 : bv 32 := 0x4b8090ef.
Lemma F_54734 : fetch_word Asan.M.loaded_segments (0x54734 : word) = Some W_54734.
Proof. vm_refl. Qed.
Lemma D_54734 : decode_any W_54734 = Some (Jal 1 38072, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_54738 : bv 32 := 0x06050e63.
Lemma F_54738 : fetch_word Asan.M.loaded_segments (0x54738 : word) = Some W_54738.
Proof. vm_refl. Qed.
Lemma D_54738 : decode_any W_54738 = Some (Branch BC_EQ 10 0 124, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5473c : bv 32 := 0x80040513.
Lemma F_5473c : fetch_word Asan.M.loaded_segments (0x5473c : word) = Some W_5473c.
Proof. vm_refl. Qed.
Lemma D_5473c : decode_any W_5473c = Some (OpImm ALU_ADD 10 8 2048, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_54740 : bv 32 := 0xfb850513.
Lemma F_54740 : fetch_word Asan.M.loaded_segments (0x54740 : word) = Some W_54740.
Proof. vm_refl. Qed.
Lemma D_54740 : decode_any W_54740 = Some (OpImm ALU_ADD 10 10 4024, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_54744 : bv 32 := 0x80040593.
Lemma F_54744 : fetch_word Asan.M.loaded_segments (0x54744 : word) = Some W_54744.
Proof. vm_refl. Qed.
Lemma D_54744 : decode_any W_54744 = Some (OpImm ALU_ADD 11 8 2048, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_54748 : bv 32 := 0xfa858593.
Lemma F_54748 : fetch_word Asan.M.loaded_segments (0x54748 : word) = Some W_54748.
Proof. vm_refl. Qed.
Lemma D_54748 : decode_any W_54748 = Some (OpImm ALU_ADD 11 11 4008, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5474c : bv 32 := 0x7ff58a13.
Lemma F_5474c : fetch_word Asan.M.loaded_segments (0x5474c : word) = Some W_5474c.
Proof. vm_refl. Qed.
Lemma D_5474c : decode_any W_5474c = Some (OpImm ALU_ADD 20 11 2047, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_54750 : bv 32 := 0x000a34a3.
Lemma F_54750 : fetch_word Asan.M.loaded_segments (0x54750 : word) = Some W_54750.
Proof. vm_refl. Qed.
Lemma D_54750 : decode_any W_54750 = Some (Store SZ8 20 0 9, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_54754 : bv 32 := 0x00aab023.
Lemma F_54754 : fetch_word Asan.M.loaded_segments (0x54754 : word) = Some W_54754.
Proof. vm_refl. Qed.
Lemma D_54754 : decode_any W_54754 = Some (Store SZ8 21 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_54758 : bv 32 := 0x000ab423.
Lemma F_54758 : fetch_word Asan.M.loaded_segments (0x54758 : word) = Some W_54758.
Proof. vm_refl. Qed.
Lemma D_54758 : decode_any W_54758 = Some (Store SZ8 21 0 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5475c : bv 32 := 0x72d200ef.
Lemma F_5475c : fetch_word Asan.M.loaded_segments (0x5475c : word) = Some W_5475c.
Proof. vm_refl. Qed.
Lemma D_5475c : decode_any W_5475c = Some (Jal 1 134956, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_54760 : bv 32 := 0x00050593.
Lemma F_54760 : fetch_word Asan.M.loaded_segments (0x54760 : word) = Some W_54760.
Proof. vm_refl. Qed.
Lemma D_54760 : decode_any W_54760 = Some (OpImm ALU_ADD 11 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_54764 : bv 32 := 0x00056517.
Lemma F_54764 : fetch_word Asan.M.loaded_segments (0x54764 : word) = Some W_54764.
Proof. vm_refl. Qed.
Lemma D_54764 : decode_any W_54764 = Some (Auipc 10 86, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_54768 : bv 32 := 0x70c53503.
Lemma F_54768 : fetch_word Asan.M.loaded_segments (0x54768 : word) = Some W_54768.
Proof. vm_refl. Qed.
Lemma D_54768 : decode_any W_54768 = Some (Load SZ8 true 10 10 1804, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5476c : bv 32 := 0x02154703.
Lemma F_5476c : fetch_word Asan.M.loaded_segments (0x5476c : word) = Some W_5476c.
Proof. vm_refl. Qed.
Lemma D_5476c : decode_any W_5476c = Some (Load SZ1 false 14 10 33, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_54770 : bv 32 := 0x008a34a3.
Lemma F_54770 : fetch_word Asan.M.loaded_segments (0x54770 : word) = Some W_54770.
Proof. vm_refl. Qed.
Lemma D_54770 : decode_any W_54770 = Some (Store SZ8 20 8 9, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_54774 : bv 32 := 0x80040513.
Lemma F_54774 : fetch_word Asan.M.loaded_segments (0x54774 : word) = Some W_54774.
Proof. vm_refl. Qed.
Lemma D_54774 : decode_any W_54774 = Some (OpImm ALU_ADD 10 8 2048, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_54778 : bv 32 := 0xfa850513.
Lemma F_54778 : fetch_word Asan.M.loaded_segments (0x54778 : word) = Some W_54778.
Proof. vm_refl. Qed.
Lemma D_54778 : decode_any W_54778 = Some (OpImm ALU_ADD 10 10 4008, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5477c : bv 32 := 0x0ff00793.
Lemma F_5477c : fetch_word Asan.M.loaded_segments (0x5477c : word) = Some W_5477c.
Proof. vm_refl. Qed.
Lemma D_5477c : decode_any W_5477c = Some (OpImm ALU_ADD 15 0 255, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_54780 : bv 32 := 0x00040613.
Lemma F_54780 : fetch_word Asan.M.loaded_segments (0x54780 : word) = Some W_54780.
Proof. vm_refl. Qed.
Lemma D_54780 : decode_any W_54780 = Some (OpImm ALU_ADD 12 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_54784 : bv 32 := 0x00000693.
Lemma F_54784 : fetch_word Asan.M.loaded_segments (0x54784 : word) = Some W_54784.
Proof. vm_refl. Qed.
Lemma D_54784 : decode_any W_54784 = Some (OpImm ALU_ADD 13 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_54788 : bv 32 := 0x450080ef.
Lemma F_54788 : fetch_word Asan.M.loaded_segments (0x54788 : word) = Some W_54788.
Proof. vm_refl. Qed.
Lemma D_54788 : decode_any W_54788 = Some (Jal 1 33872, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5478c : bv 32 := 0x80040513.
Lemma F_5478c : fetch_word Asan.M.loaded_segments (0x5478c : word) = Some W_5478c.
Proof. vm_refl. Qed.
Lemma D_5478c : decode_any W_5478c = Some (OpImm ALU_ADD 10 8 2048, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_54790 : bv 32 := 0xfa850513.
Lemma F_54790 : fetch_word Asan.M.loaded_segments (0x54790 : word) = Some W_54790.
Proof. vm_refl. Qed.
Lemma D_54790 : decode_any W_54790 = Some (OpImm ALU_ADD 10 10 4008, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_54794 : bv 32 := 0x760090ef.
Lemma F_54794 : fetch_word Asan.M.loaded_segments (0x54794 : word) = Some W_54794.
Proof. vm_refl. Qed.
Lemma D_54794 : decode_any W_54794 = Some (Jal 1 38752, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_54798 : bv 32 := 0x00050693.
Lemma F_54798 : fetch_word Asan.M.loaded_segments (0x54798 : word) = Some W_54798.
Proof. vm_refl. Qed.
Lemma D_54798 : decode_any W_54798 = Some (OpImm ALU_ADD 13 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_5479c : bv 32 := 0x00040a13.
Lemma F_5479c : fetch_word Asan.M.loaded_segments (0x5479c : word) = Some W_5479c.
Proof. vm_refl. Qed.
Lemma D_5479c : decode_any W_5479c = Some (OpImm ALU_ADD 20 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_547a0 : bv 32 := 0x00090613.
Lemma F_547a0 : fetch_word Asan.M.loaded_segments (0x547a0 : word) = Some W_547a0.
Proof. vm_refl. Qed.
Lemma D_547a0 : decode_any W_547a0 = Some (OpImm ALU_ADD 12 18 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_547a4 : bv 32 := 0x000b0593.
Lemma F_547a4 : fetch_word Asan.M.loaded_segments (0x547a4 : word) = Some W_547a4.
Proof. vm_refl. Qed.
Lemma D_547a4 : decode_any W_547a4 = Some (OpImm ALU_ADD 11 22 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_547a8 : bv 32 := 0x00048513.
Lemma F_547a8 : fetch_word Asan.M.loaded_segments (0x547a8 : word) = Some W_547a8.
Proof. vm_refl. Qed.
Lemma D_547a8 : decode_any W_547a8 = Some (OpImm ALU_ADD 10 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_547ac : bv 32 := 0xde069ae3.
Lemma F_547ac : fetch_word Asan.M.loaded_segments (0x547ac : word) = Some W_547ac.
Proof. vm_refl. Qed.
Lemma D_547ac : decode_any W_547ac = Some (Branch BC_NE 13 0 7668, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_547b0 : bv 32 := 0x0080006f.
Lemma F_547b0 : fetch_word Asan.M.loaded_segments (0x547b0 : word) = Some W_547b0.
Proof. vm_refl. Qed.
Lemma D_547b0 : decode_any W_547b0 = Some (Jal 0 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_547b4 : bv 32 := 0x00040a13.
Lemma F_547b4 : fetch_word Asan.M.loaded_segments (0x547b4 : word) = Some W_547b4.
Proof. vm_refl. Qed.
Lemma D_547b4 : decode_any W_547b4 = Some (OpImm ALU_ADD 20 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_547b8 : bv 32 := 0x6d1200ef.
Lemma F_547b8 : fetch_word Asan.M.loaded_segments (0x547b8 : word) = Some W_547b8.
Proof. vm_refl. Qed.
Lemma D_547b8 : decode_any W_547b8 = Some (Jal 1 134864, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_547bc : bv 32 := 0xfffbc597.
Lemma F_547bc : fetch_word Asan.M.loaded_segments (0x547bc : word) = Some W_547bc.
Proof. vm_refl. Qed.
Lemma D_547bc : decode_any W_547bc = Some (Auipc 11 1048508, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_547c0 : bv 32 := 0xc3c5b583.
Lemma F_547c0 : fetch_word Asan.M.loaded_segments (0x547c0 : word) = Some W_547c0.
Proof. vm_refl. Qed.
Lemma D_547c0 : decode_any W_547c0 = Some (Load SZ8 true 11 11 3132, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_547c4 : bv 32 := 0x00bab023.
Lemma F_547c4 : fetch_word Asan.M.loaded_segments (0x547c4 : word) = Some W_547c4.
Proof. vm_refl. Qed.
Lemma D_547c4 : decode_any W_547c4 = Some (Store SZ8 21 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_547c8 : bv 32 := 0x80040613.
Lemma F_547c8 : fetch_word Asan.M.loaded_segments (0x547c8 : word) = Some W_547c8.
Proof. vm_refl. Qed.
Lemma D_547c8 : decode_any W_547c8 = Some (OpImm ALU_ADD 12 8 2048, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_547cc : bv 32 := 0xfa860613.
Lemma F_547cc : fetch_word Asan.M.loaded_segments (0x547cc : word) = Some W_547cc.
Proof. vm_refl. Qed.
Lemma D_547cc : decode_any W_547cc = Some (OpImm ALU_ADD 12 12 4008, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_547d0 : bv 32 := 0x00100713.
Lemma F_547d0 : fetch_word Asan.M.loaded_segments (0x547d0 : word) = Some W_547d0.
Proof. vm_refl. Qed.
Lemma D_547d0 : decode_any W_547d0 = Some (OpImm ALU_ADD 14 0 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_547d4 : bv 32 := 0x000a0593.
Lemma F_547d4 : fetch_word Asan.M.loaded_segments (0x547d4 : word) = Some W_547d4.
Proof. vm_refl. Qed.
Lemma D_547d4 : decode_any W_547d4 = Some (OpImm ALU_ADD 11 20 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_547d8 : bv 32 := 0x00098693.
Lemma F_547d8 : fetch_word Asan.M.loaded_segments (0x547d8 : word) = Some W_547d8.
Proof. vm_refl. Qed.
Lemma D_547d8 : decode_any W_547d8 = Some (OpImm ALU_ADD 13 19 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_547dc : bv 32 := 0x00090793.
Lemma F_547dc : fetch_word Asan.M.loaded_segments (0x547dc : word) = Some W_547dc.
Proof. vm_refl. Qed.
Lemma D_547dc : decode_any W_547dc = Some (OpImm ALU_ADD 15 18 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_547e0 : bv 32 := 0x00000813.
Lemma F_547e0 : fetch_word Asan.M.loaded_segments (0x547e0 : word) = Some W_547e0.
Proof. vm_refl. Qed.
Lemma D_547e0 : decode_any W_547e0 = Some (OpImm ALU_ADD 16 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_547e4 : bv 32 := 0x00000893.
Lemma F_547e4 : fetch_word Asan.M.loaded_segments (0x547e4 : word) = Some W_547e4.
Proof. vm_refl. Qed.
Lemma D_547e4 : decode_any W_547e4 = Some (OpImm ALU_ADD 17 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_547e8 : bv 32 := 0x700050ef.
Lemma F_547e8 : fetch_word Asan.M.loaded_segments (0x547e8 : word) = Some W_547e8.
Proof. vm_refl. Qed.
Lemma D_547e8 : decode_any W_547e8 = Some (Jal 1 22272, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_547ec : bv 32 := 0x00048513.
Lemma F_547ec : fetch_word Asan.M.loaded_segments (0x547ec : word) = Some W_547ec.
Proof. vm_refl. Qed.
Lemma D_547ec : decode_any W_547ec = Some (OpImm ALU_ADD 10 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_547f0 : bv 32 := 0x000b0593.
Lemma F_547f0 : fetch_word Asan.M.loaded_segments (0x547f0 : word) = Some W_547f0.
Proof. vm_refl. Qed.
Lemma D_547f0 : decode_any W_547f0 = Some (OpImm ALU_ADD 11 22 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_547f4 : bv 32 := 0x00090613.
Lemma F_547f4 : fetch_word Asan.M.loaded_segments (0x547f4 : word) = Some W_547f4.
Proof. vm_refl. Qed.
Lemma D_547f4 : decode_any W_547f4 = Some (OpImm ALU_ADD 12 18 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_547f8 : bv 32 := 0xda9ff06f.
Lemma F_547f8 : fetch_word Asan.M.loaded_segments (0x547f8 : word) = Some W_547f8.
Proof. vm_refl. Qed.
Lemma D_547f8 : decode_any W_547f8 = Some (Jal 0 2096552, 4%Z).
Proof. vm_refl. Qed.
