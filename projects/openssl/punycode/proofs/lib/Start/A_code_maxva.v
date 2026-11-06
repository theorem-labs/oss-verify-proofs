(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.openssl.punycode.images Require Import Asan.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.

(* [comment removed for export] *)
Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

(* [comment removed for export] *)
Definition W_1d65a0 : bv 32 := 0xff010113.
Lemma F_1d65a0 : fetch_word Asan.M.loaded_segments (0x1d65e0 : word) = Some W_1d65a0.
Proof. vm_refl. Qed.
Lemma D_1d65a0 : decode_any W_1d65a0 = Some (OpImm ALU_ADD 2 2 4080, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1d65a4 : bv 32 := 0x00113423.
Lemma F_1d65a4 : fetch_word Asan.M.loaded_segments (0x1d65e4 : word) = Some W_1d65a4.
Proof. vm_refl. Qed.
Lemma D_1d65a4 : decode_any W_1d65a4 = Some (Store SZ8 2 1 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1d65a8 : bv 32 := 0x00813023.
Lemma F_1d65a8 : fetch_word Asan.M.loaded_segments (0x1d65e8 : word) = Some W_1d65a8.
Proof. vm_refl. Qed.
Lemma D_1d65a8 : decode_any W_1d65a8 = Some (Store SZ8 2 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1d65ac : bv 32 := 0x01010413.
Lemma F_1d65ac : fetch_word Asan.M.loaded_segments (0x1d65ec : word) = Some W_1d65ac.
Proof. vm_refl. Qed.
Lemma D_1d65ac : decode_any W_1d65ac = Some (OpImm ALU_ADD 8 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1d65b0 : bv 32 := 0x003d2517.
Lemma F_1d65b0 : fetch_word Asan.M.loaded_segments (0x1d65f0 : word) = Some W_1d65b0.
Proof. vm_refl. Qed.
Lemma D_1d65b0 : decode_any W_1d65b0 = Some (Auipc 10 978, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1d65b4 : bv 32 := 0xfe853503.
Lemma F_1d65b4 : fetch_word Asan.M.loaded_segments (0x1d65f4 : word) = Some W_1d65b4.
Proof. vm_refl. Qed.
Lemma D_1d65b4 : decode_any W_1d65b4 = Some (Load SZ8 true 10 10 4072, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1d65b8 : bv 32 := 0x00050a63.
Lemma F_1d65b8 : fetch_word Asan.M.loaded_segments (0x1d65f8 : word) = Some W_1d65b8.
Proof. vm_refl. Qed.
Lemma D_1d65b8 : decode_any W_1d65b8 = Some (Branch BC_EQ 10 0 20, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1d65bc : bv 32 := 0x003d3517.
Lemma F_1d65bc : fetch_word Asan.M.loaded_segments (0x1d65fc : word) = Some W_1d65bc.
Proof. vm_refl. Qed.
Lemma D_1d65bc : decode_any W_1d65bc = Some (Auipc 10 979, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1d65c0 : bv 32 := 0xb6c53503.
Lemma F_1d65c0 : fetch_word Asan.M.loaded_segments (0x1d6600 : word) = Some W_1d65c0.
Proof. vm_refl. Qed.
Lemma D_1d65c0 : decode_any W_1d65c0 = Some (Load SZ8 true 10 10 2924, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1d65c4 : bv 32 := 0x00053503.
Lemma F_1d65c4 : fetch_word Asan.M.loaded_segments (0x1d6604 : word) = Some W_1d65c4.
Proof. vm_refl. Qed.
Lemma D_1d65c4 : decode_any W_1d65c4 = Some (Load SZ8 true 10 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1d65c8 : bv 32 := 0x00c0006f.
Lemma F_1d65c8 : fetch_word Asan.M.loaded_segments (0x1d6608 : word) = Some W_1d65c8.
Proof. vm_refl. Qed.
Lemma D_1d65c8 : decode_any W_1d65c8 = Some (Jal 0 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1d65cc : bv 32 := 0x0c040663.
Lemma F_1d65cc : fetch_word Asan.M.loaded_segments (0x1d660c : word) = Some W_1d65cc.
Proof. vm_refl. Qed.
Lemma D_1d65cc : decode_any W_1d65cc = Some (Branch BC_EQ 8 0 204, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1d65d0 : bv 32 := 0x00040513.
Lemma F_1d65d0 : fetch_word Asan.M.loaded_segments (0x1d6610 : word) = Some W_1d65d0.
Proof. vm_refl. Qed.
Lemma D_1d65d0 : decode_any W_1d65d0 = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1d65d4 : bv 32 := 0x00155593.
Lemma F_1d65d4 : fetch_word Asan.M.loaded_segments (0x1d6614 : word) = Some W_1d65d4.
Proof. vm_refl. Qed.
Lemma D_1d65d4 : decode_any W_1d65d4 = Some (ShiftImm ALU_SRL 11 10 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1d65d8 : bv 32 := 0x55555637.
Lemma F_1d65d8 : fetch_word Asan.M.loaded_segments (0x1d6618 : word) = Some W_1d65d8.
Proof. vm_refl. Qed.
Lemma D_1d65d8 : decode_any W_1d65d8 = Some (Lui 12 349525, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1d65dc : bv 32 := 0x333336b7.
Lemma F_1d65dc : fetch_word Asan.M.loaded_segments (0x1d661c : word) = Some W_1d65dc.
Proof. vm_refl. Qed.
Lemma D_1d65dc : decode_any W_1d65dc = Some (Lui 13 209715, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1d65e0 : bv 32 := 0x0f0f1737.
Lemma F_1d65e0 : fetch_word Asan.M.loaded_segments (0x1d6620 : word) = Some W_1d65e0.
Proof. vm_refl. Qed.
Lemma D_1d65e0 : decode_any W_1d65e0 = Some (Lui 14 61681, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1d65e4 : bv 32 := 0x010107b7.
Lemma F_1d65e4 : fetch_word Asan.M.loaded_segments (0x1d6624 : word) = Some W_1d65e4.
Proof. vm_refl. Qed.
Lemma D_1d65e4 : decode_any W_1d65e4 = Some (Lui 15 4112, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1d65e8 : bv 32 := 0x00b56533.
Lemma F_1d65e8 : fetch_word Asan.M.loaded_segments (0x1d6628 : word) = Some W_1d65e8.
Proof. vm_refl. Qed.
Lemma D_1d65e8 : decode_any W_1d65e8 = Some (Op ALU_OR 10 10 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1d65ec : bv 32 := 0x5556059b.
Lemma F_1d65ec : fetch_word Asan.M.loaded_segments (0x1d662c : word) = Some W_1d65ec.
Proof. vm_refl. Qed.
Lemma D_1d65ec : decode_any W_1d65ec = Some (OpImm32 11 12 1365, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1d65f0 : bv 32 := 0x3336861b.
Lemma F_1d65f0 : fetch_word Asan.M.loaded_segments (0x1d6630 : word) = Some W_1d65f0.
Proof. vm_refl. Qed.
Lemma D_1d65f0 : decode_any W_1d65f0 = Some (OpImm32 12 13 819, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1d65f4 : bv 32 := 0xf0f7069b.
Lemma F_1d65f4 : fetch_word Asan.M.loaded_segments (0x1d6634 : word) = Some W_1d65f4.
Proof. vm_refl. Qed.
Lemma D_1d65f4 : decode_any W_1d65f4 = Some (OpImm32 13 14 3855, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1d65f8 : bv 32 := 0x1017871b.
Lemma F_1d65f8 : fetch_word Asan.M.loaded_segments (0x1d6638 : word) = Some W_1d65f8.
Proof. vm_refl. Qed.
Lemma D_1d65f8 : decode_any W_1d65f8 = Some (OpImm32 14 15 257, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1d65fc : bv 32 := 0x00255793.
Lemma F_1d65fc : fetch_word Asan.M.loaded_segments (0x1d663c : word) = Some W_1d65fc.
Proof. vm_refl. Qed.
Lemma D_1d65fc : decode_any W_1d65fc = Some (ShiftImm ALU_SRL 15 10 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1d6600 : bv 32 := 0x00f56533.
Lemma F_1d6600 : fetch_word Asan.M.loaded_segments (0x1d6640 : word) = Some W_1d6600.
Proof. vm_refl. Qed.
Lemma D_1d6600 : decode_any W_1d6600 = Some (Op ALU_OR 10 10 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1d6604 : bv 32 := 0x02059793.
Lemma F_1d6604 : fetch_word Asan.M.loaded_segments (0x1d6644 : word) = Some W_1d6604.
Proof. vm_refl. Qed.
Lemma D_1d6604 : decode_any W_1d6604 = Some (ShiftImm ALU_SLL 15 11 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1d6608 : bv 32 := 0x00f585b3.
Lemma F_1d6608 : fetch_word Asan.M.loaded_segments (0x1d6648 : word) = Some W_1d6608.
Proof. vm_refl. Qed.
Lemma D_1d6608 : decode_any W_1d6608 = Some (Op ALU_ADD 11 11 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1d660c : bv 32 := 0x02061793.
Lemma F_1d660c : fetch_word Asan.M.loaded_segments (0x1d664c : word) = Some W_1d660c.
Proof. vm_refl. Qed.
Lemma D_1d660c : decode_any W_1d660c = Some (ShiftImm ALU_SLL 15 12 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1d6610 : bv 32 := 0x00f60633.
Lemma F_1d6610 : fetch_word Asan.M.loaded_segments (0x1d6650 : word) = Some W_1d6610.
Proof. vm_refl. Qed.
Lemma D_1d6610 : decode_any W_1d6610 = Some (Op ALU_ADD 12 12 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1d6614 : bv 32 := 0x02069793.
Lemma F_1d6614 : fetch_word Asan.M.loaded_segments (0x1d6654 : word) = Some W_1d6614.
Proof. vm_refl. Qed.
Lemma D_1d6614 : decode_any W_1d6614 = Some (ShiftImm ALU_SLL 15 13 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1d6618 : bv 32 := 0x00f686b3.
Lemma F_1d6618 : fetch_word Asan.M.loaded_segments (0x1d6658 : word) = Some W_1d6618.
Proof. vm_refl. Qed.
Lemma D_1d6618 : decode_any W_1d6618 = Some (Op ALU_ADD 13 13 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1d661c : bv 32 := 0x02071793.
Lemma F_1d661c : fetch_word Asan.M.loaded_segments (0x1d665c : word) = Some W_1d661c.
Proof. vm_refl. Qed.
Lemma D_1d661c : decode_any W_1d661c = Some (ShiftImm ALU_SLL 15 14 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1d6620 : bv 32 := 0x00f70733.
Lemma F_1d6620 : fetch_word Asan.M.loaded_segments (0x1d6660 : word) = Some W_1d6620.
Proof. vm_refl. Qed.
Lemma D_1d6620 : decode_any W_1d6620 = Some (Op ALU_ADD 14 14 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1d6624 : bv 32 := 0x00455793.
Lemma F_1d6624 : fetch_word Asan.M.loaded_segments (0x1d6664 : word) = Some W_1d6624.
Proof. vm_refl. Qed.
Lemma D_1d6624 : decode_any W_1d6624 = Some (ShiftImm ALU_SRL 15 10 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1d6628 : bv 32 := 0x00f56533.
Lemma F_1d6628 : fetch_word Asan.M.loaded_segments (0x1d6668 : word) = Some W_1d6628.
Proof. vm_refl. Qed.
Lemma D_1d6628 : decode_any W_1d6628 = Some (Op ALU_OR 10 10 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1d662c : bv 32 := 0x00855793.
Lemma F_1d662c : fetch_word Asan.M.loaded_segments (0x1d666c : word) = Some W_1d662c.
Proof. vm_refl. Qed.
Lemma D_1d662c : decode_any W_1d662c = Some (ShiftImm ALU_SRL 15 10 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1d6630 : bv 32 := 0x00f56533.
Lemma F_1d6630 : fetch_word Asan.M.loaded_segments (0x1d6670 : word) = Some W_1d6630.
Proof. vm_refl. Qed.
Lemma D_1d6630 : decode_any W_1d6630 = Some (Op ALU_OR 10 10 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1d6634 : bv 32 := 0x01055793.
Lemma F_1d6634 : fetch_word Asan.M.loaded_segments (0x1d6674 : word) = Some W_1d6634.
Proof. vm_refl. Qed.
Lemma D_1d6634 : decode_any W_1d6634 = Some (ShiftImm ALU_SRL 15 10 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1d6638 : bv 32 := 0x00f56533.
Lemma F_1d6638 : fetch_word Asan.M.loaded_segments (0x1d6678 : word) = Some W_1d6638.
Proof. vm_refl. Qed.
Lemma D_1d6638 : decode_any W_1d6638 = Some (Op ALU_OR 10 10 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1d663c : bv 32 := 0x02055793.
Lemma F_1d663c : fetch_word Asan.M.loaded_segments (0x1d667c : word) = Some W_1d663c.
Proof. vm_refl. Qed.
Lemma D_1d663c : decode_any W_1d663c = Some (ShiftImm ALU_SRL 15 10 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1d6640 : bv 32 := 0x00f56533.
Lemma F_1d6640 : fetch_word Asan.M.loaded_segments (0x1d6680 : word) = Some W_1d6640.
Proof. vm_refl. Qed.
Lemma D_1d6640 : decode_any W_1d6640 = Some (Op ALU_OR 10 10 15, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1d6644 : bv 32 := 0xfff54513.
Lemma F_1d6644 : fetch_word Asan.M.loaded_segments (0x1d6684 : word) = Some W_1d6644.
Proof. vm_refl. Qed.
Lemma D_1d6644 : decode_any W_1d6644 = Some (OpImm ALU_XOR 10 10 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1d6648 : bv 32 := 0x00155793.
Lemma F_1d6648 : fetch_word Asan.M.loaded_segments (0x1d6688 : word) = Some W_1d6648.
Proof. vm_refl. Qed.
Lemma D_1d6648 : decode_any W_1d6648 = Some (ShiftImm ALU_SRL 15 10 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1d664c : bv 32 := 0x00b7f5b3.
Lemma F_1d664c : fetch_word Asan.M.loaded_segments (0x1d668c : word) = Some W_1d664c.
Proof. vm_refl. Qed.
Lemma D_1d664c : decode_any W_1d664c = Some (Op ALU_AND 11 15 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1d6650 : bv 32 := 0x40b50533.
Lemma F_1d6650 : fetch_word Asan.M.loaded_segments (0x1d6690 : word) = Some W_1d6650.
Proof. vm_refl. Qed.
Lemma D_1d6650 : decode_any W_1d6650 = Some (Op ALU_SUB 10 10 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1d6654 : bv 32 := 0x00c575b3.
Lemma F_1d6654 : fetch_word Asan.M.loaded_segments (0x1d6694 : word) = Some W_1d6654.
Proof. vm_refl. Qed.
Lemma D_1d6654 : decode_any W_1d6654 = Some (Op ALU_AND 11 10 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1d6658 : bv 32 := 0x00255513.
Lemma F_1d6658 : fetch_word Asan.M.loaded_segments (0x1d6698 : word) = Some W_1d6658.
Proof. vm_refl. Qed.
Lemma D_1d6658 : decode_any W_1d6658 = Some (ShiftImm ALU_SRL 10 10 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1d665c : bv 32 := 0x00c57533.
Lemma F_1d665c : fetch_word Asan.M.loaded_segments (0x1d669c : word) = Some W_1d665c.
Proof. vm_refl. Qed.
Lemma D_1d665c : decode_any W_1d665c = Some (Op ALU_AND 10 10 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1d6660 : bv 32 := 0x00a58533.
Lemma F_1d6660 : fetch_word Asan.M.loaded_segments (0x1d66a0 : word) = Some W_1d6660.
Proof. vm_refl. Qed.
Lemma D_1d6660 : decode_any W_1d6660 = Some (Op ALU_ADD 10 11 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1d6664 : bv 32 := 0x00455593.
Lemma F_1d6664 : fetch_word Asan.M.loaded_segments (0x1d66a4 : word) = Some W_1d6664.
Proof. vm_refl. Qed.
Lemma D_1d6664 : decode_any W_1d6664 = Some (ShiftImm ALU_SRL 11 10 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1d6668 : bv 32 := 0x00b50533.
Lemma F_1d6668 : fetch_word Asan.M.loaded_segments (0x1d66a8 : word) = Some W_1d6668.
Proof. vm_refl. Qed.
Lemma D_1d6668 : decode_any W_1d6668 = Some (Op ALU_ADD 10 10 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1d666c : bv 32 := 0x00d57533.
Lemma F_1d666c : fetch_word Asan.M.loaded_segments (0x1d66ac : word) = Some W_1d666c.
Proof. vm_refl. Qed.
Lemma D_1d666c : decode_any W_1d666c = Some (Op ALU_AND 10 10 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1d6670 : bv 32 := 0x02e50533.
Lemma F_1d6670 : fetch_word Asan.M.loaded_segments (0x1d66b0 : word) = Some W_1d6670.
Proof. vm_refl. Qed.
Lemma D_1d6670 : decode_any W_1d6670 = Some (Mul M_MUL 10 10 14, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1d6674 : bv 32 := 0x03855513.
Lemma F_1d6674 : fetch_word Asan.M.loaded_segments (0x1d66b4 : word) = Some W_1d6674.
Proof. vm_refl. Qed.
Lemma D_1d6674 : decode_any W_1d6674 = Some (ShiftImm ALU_SRL 10 10 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1d6678 : bv 32 := 0x40a0053b.
Lemma F_1d6678 : fetch_word Asan.M.loaded_segments (0x1d66b8 : word) = Some W_1d6678.
Proof. vm_refl. Qed.
Lemma D_1d6678 : decode_any W_1d6678 = Some (Op32 ALU_SUB 10 0 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1d667c : bv 32 := 0xfff00593.
Lemma F_1d667c : fetch_word Asan.M.loaded_segments (0x1d66bc : word) = Some W_1d667c.
Proof. vm_refl. Qed.
Lemma D_1d667c : decode_any W_1d667c = Some (OpImm ALU_ADD 11 0 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1d6680 : bv 32 := 0x00a59533.
Lemma F_1d6680 : fetch_word Asan.M.loaded_segments (0x1d66c0 : word) = Some W_1d6680.
Proof. vm_refl. Qed.
Lemma D_1d6680 : decode_any W_1d6680 = Some (Op ALU_SLL 10 11 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1d6684 : bv 32 := 0xfff54513.
Lemma F_1d6684 : fetch_word Asan.M.loaded_segments (0x1d66c4 : word) = Some W_1d6684.
Proof. vm_refl. Qed.
Lemma D_1d6684 : decode_any W_1d6684 = Some (OpImm ALU_XOR 10 10 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1d6688 : bv 32 := 0x00813083.
Lemma F_1d6688 : fetch_word Asan.M.loaded_segments (0x1d66c8 : word) = Some W_1d6688.
Proof. vm_refl. Qed.
Lemma D_1d6688 : decode_any W_1d6688 = Some (Load SZ8 true 1 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1d668c : bv 32 := 0x00013403.
Lemma F_1d668c : fetch_word Asan.M.loaded_segments (0x1d66cc : word) = Some W_1d668c.
Proof. vm_refl. Qed.
Lemma D_1d668c : decode_any W_1d668c = Some (Load SZ8 true 8 2 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1d6690 : bv 32 := 0x01010113.
Lemma F_1d6690 : fetch_word Asan.M.loaded_segments (0x1d66d0 : word) = Some W_1d6690.
Proof. vm_refl. Qed.
Lemma D_1d6690 : decode_any W_1d6690 = Some (OpImm ALU_ADD 2 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1d6694 : bv 32 := 0x00008067.
Lemma F_1d6694 : fetch_word Asan.M.loaded_segments (0x1d66d4 : word) = Some W_1d6694.
Proof. vm_refl. Qed.
Lemma D_1d6694 : decode_any W_1d6694 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.
