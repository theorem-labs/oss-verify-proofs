(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)

From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.coturn.FuzzStunClient.images Require Import Ubsan.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.

(* [comment removed for export] *)
Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.


(* [comment removed for export] *)
Definition W_1b708 : bv 32 := 0xfbf5059b.
Lemma F_1b708 : fetch_word Ubsan.M.loaded_segments (0x1b708 : word) = Some W_1b708.
Proof. vm_refl. Qed.
Lemma D_1b708 : decode_any W_1b708 = Some (OpImm32 11 10 4031, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1b70c : bv 32 := 0x01a5b593.
Lemma F_1b70c : fetch_word Ubsan.M.loaded_segments (0x1b70c : word) = Some W_1b70c.
Proof. vm_refl. Qed.
Lemma D_1b70c : decode_any W_1b70c = Some (OpImm ALU_SLTU 11 11 26, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1b710 : bv 32 := 0x00559593.
Lemma F_1b710 : fetch_word Ubsan.M.loaded_segments (0x1b710 : word) = Some W_1b710.
Proof. vm_refl. Qed.
Lemma D_1b710 : decode_any W_1b710 = Some (ShiftImm ALU_SLL 11 11 5, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1b714 : bv 32 := 0x00b56533.
Lemma F_1b714 : fetch_word Ubsan.M.loaded_segments (0x1b714 : word) = Some W_1b714.
Proof. vm_refl. Qed.
Lemma D_1b714 : decode_any W_1b714 = Some (Op ALU_OR 10 10 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1b718 : bv 32 := 0x00008067.
Lemma F_1b718 : fetch_word Ubsan.M.loaded_segments (0x1b718 : word) = Some W_1b718.
Proof. vm_refl. Qed.
Lemma D_1b718 : decode_any W_1b718 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1b71c : bv 32 := 0x00008067.
Lemma F_1b71c : fetch_word Ubsan.M.loaded_segments (0x1b71c : word) = Some W_1b71c.
Proof. vm_refl. Qed.
Lemma D_1b71c : decode_any W_1b71c = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1b720 : bv 32 := 0xe8010113.
Lemma F_1b720 : fetch_word Ubsan.M.loaded_segments (0x1b720 : word) = Some W_1b720.
Proof. vm_refl. Qed.
Lemma D_1b720 : decode_any W_1b720 = Some (OpImm ALU_ADD 2 2 3712, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1b724 : bv 32 := 0x16113c23.
Lemma F_1b724 : fetch_word Ubsan.M.loaded_segments (0x1b724 : word) = Some W_1b724.
Proof. vm_refl. Qed.
Lemma D_1b724 : decode_any W_1b724 = Some (Store SZ8 2 1 376, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1b728 : bv 32 := 0x16813823.
Lemma F_1b728 : fetch_word Ubsan.M.loaded_segments (0x1b728 : word) = Some W_1b728.
Proof. vm_refl. Qed.
Lemma D_1b728 : decode_any W_1b728 = Some (Store SZ8 2 8 368, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1b72c : bv 32 := 0x16913423.
Lemma F_1b72c : fetch_word Ubsan.M.loaded_segments (0x1b72c : word) = Some W_1b72c.
Proof. vm_refl. Qed.
Lemma D_1b72c : decode_any W_1b72c = Some (Store SZ8 2 9 360, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1b730 : bv 32 := 0x17213023.
Lemma F_1b730 : fetch_word Ubsan.M.loaded_segments (0x1b730 : word) = Some W_1b730.
Proof. vm_refl. Qed.
Lemma D_1b730 : decode_any W_1b730 = Some (Store SZ8 2 18 352, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1b734 : bv 32 := 0x00058413.
Lemma F_1b734 : fetch_word Ubsan.M.loaded_segments (0x1b734 : word) = Some W_1b734.
Proof. vm_refl. Qed.
Lemma D_1b734 : decode_any W_1b734 = Some (OpImm ALU_ADD 8 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1b738 : bv 32 := 0x00050493.
Lemma F_1b738 : fetch_word Ubsan.M.loaded_segments (0x1b738 : word) = Some W_1b738.
Proof. vm_refl. Qed.
Lemma D_1b738 : decode_any W_1b738 = Some (OpImm ALU_ADD 9 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1b73c : bv 32 := 0x03010513.
Lemma F_1b73c : fetch_word Ubsan.M.loaded_segments (0x1b73c : word) = Some W_1b73c.
Proof. vm_refl. Qed.
Lemma D_1b73c : decode_any W_1b73c = Some (OpImm ALU_ADD 10 2 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1b740 : bv 32 := 0x13000613.
Lemma F_1b740 : fetch_word Ubsan.M.loaded_segments (0x1b740 : word) = Some W_1b740.
Proof. vm_refl. Qed.
Lemma D_1b740 : decode_any W_1b740 = Some (OpImm ALU_ADD 12 0 304, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1b744 : bv 32 := 0x00000593.
Lemma F_1b744 : fetch_word Ubsan.M.loaded_segments (0x1b744 : word) = Some W_1b744.
Proof. vm_refl. Qed.
Lemma D_1b744 : decode_any W_1b744 = Some (OpImm ALU_ADD 11 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1b748 : bv 32 := 0x7a4080ef.
Lemma F_1b748 : fetch_word Ubsan.M.loaded_segments (0x1b748 : word) = Some W_1b748.
Proof. vm_refl. Qed.
Lemma D_1b748 : decode_any W_1b748 = Some (Jal 1 34724, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1b74c : bv 32 := 0x0000a517.
Lemma F_1b74c : fetch_word Ubsan.M.loaded_segments (0x1b74c : word) = Some W_1b74c.
Proof. vm_refl. Qed.
Lemma D_1b74c : decode_any W_1b74c = Some (Auipc 10 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1b750 : bv 32 := 0x05c53503.
Lemma F_1b750 : fetch_word Ubsan.M.loaded_segments (0x1b750 : word) = Some W_1b750.
Proof. vm_refl. Qed.
Lemma D_1b750 : decode_any W_1b750 = Some (Load SZ8 true 10 10 92, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1b754 : bv 32 := 0x00953023.
Lemma F_1b754 : fetch_word Ubsan.M.loaded_segments (0x1b754 : word) = Some W_1b754.
Proof. vm_refl. Qed.
Lemma D_1b754 : decode_any W_1b754 = Some (Store SZ8 10 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1b758 : bv 32 := 0x0004b503.
Lemma F_1b758 : fetch_word Ubsan.M.loaded_segments (0x1b758 : word) = Some W_1b758.
Proof. vm_refl. Qed.
Lemma D_1b758 : decode_any W_1b758 = Some (Load SZ8 true 10 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1b75c : bv 32 := 0x00848493.
Lemma F_1b75c : fetch_word Ubsan.M.loaded_segments (0x1b75c : word) = Some W_1b75c.
Proof. vm_refl. Qed.
Lemma D_1b75c : decode_any W_1b75c = Some (OpImm ALU_ADD 9 9 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1b760 : bv 32 := 0xfe051ce3.
Lemma F_1b760 : fetch_word Ubsan.M.loaded_segments (0x1b760 : word) = Some W_1b760.
Proof. vm_refl. Qed.
Lemma D_1b760 : decode_any W_1b760 = Some (Branch BC_NE 10 0 8184, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1b764 : bv 32 := 0x0003b517.
Lemma F_1b764 : fetch_word Ubsan.M.loaded_segments (0x1b764 : word) = Some W_1b764.
Proof. vm_refl. Qed.
Lemma D_1b764 : decode_any W_1b764 = Some (Auipc 10 59, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1b768 : bv 32 := 0x78450913.
Lemma F_1b768 : fetch_word Ubsan.M.loaded_segments (0x1b768 : word) = Some W_1b768.
Proof. vm_refl. Qed.
Lemma D_1b768 : decode_any W_1b768 = Some (OpImm ALU_ADD 18 10 1924, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1b76c : bv 32 := 0x00993423.
Lemma F_1b76c : fetch_word Ubsan.M.loaded_segments (0x1b76c : word) = Some W_1b76c.
Proof. vm_refl. Qed.
Lemma D_1b76c : decode_any W_1b76c = Some (Store SZ8 18 9 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1b770 : bv 32 := 0x0004b583.
Lemma F_1b770 : fetch_word Ubsan.M.loaded_segments (0x1b770 : word) = Some W_1b770.
Proof. vm_refl. Qed.
Lemma D_1b770 : decode_any W_1b770 = Some (Load SZ8 true 11 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1b774 : bv 32 := 0x04058c63.
Lemma F_1b774 : fetch_word Ubsan.M.loaded_segments (0x1b774 : word) = Some W_1b774.
Proof. vm_refl. Qed.
Lemma D_1b774 : decode_any W_1b774 = Some (Branch BC_EQ 11 0 88, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1b778 : bv 32 := 0x01048493.
Lemma F_1b778 : fetch_word Ubsan.M.loaded_segments (0x1b778 : word) = Some W_1b778.
Proof. vm_refl. Qed.
Lemma D_1b778 : decode_any W_1b778 = Some (OpImm ALU_ADD 9 9 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1b77c : bv 32 := 0x02500513.
Lemma F_1b77c : fetch_word Ubsan.M.loaded_segments (0x1b77c : word) = Some W_1b77c.
Proof. vm_refl. Qed.
Lemma D_1b77c : decode_any W_1b77c = Some (OpImm ALU_ADD 10 0 37, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1b780 : bv 32 := 0x03010613.
Lemma F_1b780 : fetch_word Ubsan.M.loaded_segments (0x1b780 : word) = Some W_1b780.
Proof. vm_refl. Qed.
Lemma D_1b780 : decode_any W_1b780 = Some (OpImm ALU_ADD 12 2 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1b784 : bv 32 := 0x0100006f.
Lemma F_1b784 : fetch_word Ubsan.M.loaded_segments (0x1b784 : word) = Some W_1b784.
Proof. vm_refl. Qed.
Lemma D_1b784 : decode_any W_1b784 = Some (Jal 0 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1b788 : bv 32 := 0x0004b583.
Lemma F_1b788 : fetch_word Ubsan.M.loaded_segments (0x1b788 : word) = Some W_1b788.
Proof. vm_refl. Qed.
Lemma D_1b788 : decode_any W_1b788 = Some (Load SZ8 true 11 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1b78c : bv 32 := 0x01048493.
Lemma F_1b78c : fetch_word Ubsan.M.loaded_segments (0x1b78c : word) = Some W_1b78c.
Proof. vm_refl. Qed.
Lemma D_1b78c : decode_any W_1b78c = Some (OpImm ALU_ADD 9 9 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1b790 : bv 32 := 0x00058e63.
Lemma F_1b790 : fetch_word Ubsan.M.loaded_segments (0x1b790 : word) = Some W_1b790.
Proof. vm_refl. Qed.
Lemma D_1b790 : decode_any W_1b790 = Some (Branch BC_EQ 11 0 28, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1b794 : bv 32 := 0xfeb56ae3.
Lemma F_1b794 : fetch_word Ubsan.M.loaded_segments (0x1b794 : word) = Some W_1b794.
Proof. vm_refl. Qed.
Lemma D_1b794 : decode_any W_1b794 = Some (Branch BC_LTU 10 11 8180, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1b798 : bv 32 := 0xff84b683.
Lemma F_1b798 : fetch_word Ubsan.M.loaded_segments (0x1b798 : word) = Some W_1b798.
Proof. vm_refl. Qed.
Lemma D_1b798 : decode_any W_1b798 = Some (Load SZ8 true 13 9 4088, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1b79c : bv 32 := 0x00359593.
Lemma F_1b79c : fetch_word Ubsan.M.loaded_segments (0x1b79c : word) = Some W_1b79c.
Proof. vm_refl. Qed.
Lemma D_1b79c : decode_any W_1b79c = Some (ShiftImm ALU_SLL 11 11 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1b7a0 : bv 32 := 0x00b605b3.
Lemma F_1b7a0 : fetch_word Ubsan.M.loaded_segments (0x1b7a0 : word) = Some W_1b7a0.
Proof. vm_refl. Qed.
Lemma D_1b7a0 : decode_any W_1b7a0 = Some (Op ALU_ADD 11 12 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1b7a4 : bv 32 := 0x00d5b023.
Lemma F_1b7a4 : fetch_word Ubsan.M.loaded_segments (0x1b7a4 : word) = Some W_1b7a4.
Proof. vm_refl. Qed.
Lemma D_1b7a4 : decode_any W_1b7a4 = Some (Store SZ8 11 13 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1b7a8 : bv 32 := 0xfe1ff06f.
Lemma F_1b7a8 : fetch_word Ubsan.M.loaded_segments (0x1b7a8 : word) = Some W_1b7a8.
Proof. vm_refl. Qed.
Lemma D_1b7a8 : decode_any W_1b7a8 = Some (Jal 0 2097120, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1b7ac : bv 32 := 0x0b013583.
Lemma F_1b7ac : fetch_word Ubsan.M.loaded_segments (0x1b7ac : word) = Some W_1b7ac.
Proof. vm_refl. Qed.
Lemma D_1b7ac : decode_any W_1b7ac = Some (Load SZ8 true 11 2 176, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1b7b0 : bv 32 := 0x13013503.
Lemma F_1b7b0 : fetch_word Ubsan.M.loaded_segments (0x1b7b0 : word) = Some W_1b7b0.
Proof. vm_refl. Qed.
Lemma D_1b7b0 : decode_any W_1b7b0 = Some (Load SZ8 true 10 2 304, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1b7b4 : bv 32 := 0x0003b617.
Lemma F_1b7b4 : fetch_word Ubsan.M.loaded_segments (0x1b7b4 : word) = Some W_1b7b4.
Proof. vm_refl. Qed.
Lemma D_1b7b4 : decode_any W_1b7b4 = Some (Auipc 12 59, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1b7b8 : bv 32 := 0x78b63e23.
Lemma F_1b7b8 : fetch_word Ubsan.M.loaded_segments (0x1b7b8 : word) = Some W_1b7b8.
Proof. vm_refl. Qed.
Lemma D_1b7b8 : decode_any W_1b7b8 = Some (Store SZ8 12 11 1948, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1b7bc : bv 32 := 0x00050c63.
Lemma F_1b7bc : fetch_word Ubsan.M.loaded_segments (0x1b7bc : word) = Some W_1b7bc.
Proof. vm_refl. Qed.
Lemma D_1b7bc : decode_any W_1b7bc = Some (Branch BC_EQ 10 0 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1b7d4 : bv 32 := 0x06013503.
Lemma F_1b7d4 : fetch_word Ubsan.M.loaded_segments (0x1b7d4 : word) = Some W_1b7d4.
Proof. vm_refl. Qed.
Lemma D_1b7d4 : decode_any W_1b7d4 = Some (Load SZ8 true 10 2 96, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1b7d8 : bv 32 := 0x02a93823.
Lemma F_1b7d8 : fetch_word Ubsan.M.loaded_segments (0x1b7d8 : word) = Some W_1b7d8.
Proof. vm_refl. Qed.
Lemma D_1b7d8 : decode_any W_1b7d8 = Some (Store SZ8 18 10 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1b7dc : bv 32 := 0x00041463.
Lemma F_1b7dc : fetch_word Ubsan.M.loaded_segments (0x1b7dc : word) = Some W_1b7dc.
Proof. vm_refl. Qed.
Lemma D_1b7dc : decode_any W_1b7dc = Some (Branch BC_NE 8 0 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1b7e4 : bv 32 := 0x00041663.
Lemma F_1b7e4 : fetch_word Ubsan.M.loaded_segments (0x1b7e4 : word) = Some W_1b7e4.
Proof. vm_refl. Qed.
Lemma D_1b7e4 : decode_any W_1b7e4 = Some (Branch BC_NE 8 0 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1b7f0 : bv 32 := 0x0000a517.
Lemma F_1b7f0 : fetch_word Ubsan.M.loaded_segments (0x1b7f0 : word) = Some W_1b7f0.
Proof. vm_refl. Qed.
Lemma D_1b7f0 : decode_any W_1b7f0 = Some (Auipc 10 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1b7f4 : bv 32 := 0xfc053583.
Lemma F_1b7f4 : fetch_word Ubsan.M.loaded_segments (0x1b7f4 : word) = Some W_1b7f4.
Proof. vm_refl. Qed.
Lemma D_1b7f4 : decode_any W_1b7f4 = Some (Load SZ8 true 11 10 4032, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1b7f8 : bv 32 := 0x0000a517.
Lemma F_1b7f8 : fetch_word Ubsan.M.loaded_segments (0x1b7f8 : word) = Some W_1b7f8.
Proof. vm_refl. Qed.
Lemma D_1b7f8 : decode_any W_1b7f8 = Some (Auipc 10 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1b7fc : bv 32 := 0xfc053503.
Lemma F_1b7fc : fetch_word Ubsan.M.loaded_segments (0x1b7fc : word) = Some W_1b7fc.
Proof. vm_refl. Qed.
Lemma D_1b7fc : decode_any W_1b7fc = Some (Load SZ8 true 10 10 4032, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1b800 : bv 32 := 0x0085b023.
Lemma F_1b800 : fetch_word Ubsan.M.loaded_segments (0x1b800 : word) = Some W_1b800.
Proof. vm_refl. Qed.
Lemma D_1b800 : decode_any W_1b800 = Some (Store SZ8 11 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1b804 : bv 32 := 0x00140593.
Lemma F_1b804 : fetch_word Ubsan.M.loaded_segments (0x1b804 : word) = Some W_1b804.
Proof. vm_refl. Qed.
Lemma D_1b804 : decode_any W_1b804 = Some (OpImm ALU_ADD 11 8 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1b808 : bv 32 := 0x00853023.
Lemma F_1b808 : fetch_word Ubsan.M.loaded_segments (0x1b808 : word) = Some W_1b808.
Proof. vm_refl. Qed.
Lemma D_1b808 : decode_any W_1b808 = Some (Store SZ8 10 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1b80c : bv 32 := 0x02f00613.
Lemma F_1b80c : fetch_word Ubsan.M.loaded_segments (0x1b80c : word) = Some W_1b80c.
Proof. vm_refl. Qed.
Lemma D_1b80c : decode_any W_1b80c = Some (OpImm ALU_ADD 12 0 47, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1b810 : bv 32 := 0x00c0006f.
Lemma F_1b810 : fetch_word Ubsan.M.loaded_segments (0x1b810 : word) = Some W_1b810.
Proof. vm_refl. Qed.
Lemma D_1b810 : decode_any W_1b810 = Some (Jal 0 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1b814 : bv 32 := 0x00b53023.
Lemma F_1b814 : fetch_word Ubsan.M.loaded_segments (0x1b814 : word) = Some W_1b814.
Proof. vm_refl. Qed.
Lemma D_1b814 : decode_any W_1b814 = Some (Store SZ8 10 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1b818 : bv 32 := 0x00158593.
Lemma F_1b818 : fetch_word Ubsan.M.loaded_segments (0x1b818 : word) = Some W_1b818.
Proof. vm_refl. Qed.
Lemma D_1b818 : decode_any W_1b818 = Some (OpImm ALU_ADD 11 11 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1b81c : bv 32 := 0xfff5c683.
Lemma F_1b81c : fetch_word Ubsan.M.loaded_segments (0x1b81c : word) = Some W_1b81c.
Proof. vm_refl. Qed.
Lemma D_1b81c : decode_any W_1b81c = Some (Load SZ1 false 13 11 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1b820 : bv 32 := 0xfec68ae3.
Lemma F_1b820 : fetch_word Ubsan.M.loaded_segments (0x1b820 : word) = Some W_1b820.
Proof. vm_refl. Qed.
Lemma D_1b820 : decode_any W_1b820 = Some (Branch BC_EQ 13 12 8180, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1b824 : bv 32 := 0xfe069ae3.
Lemma F_1b824 : fetch_word Ubsan.M.loaded_segments (0x1b824 : word) = Some W_1b824.
Proof. vm_refl. Qed.
Lemma D_1b824 : decode_any W_1b824 = Some (Branch BC_NE 13 0 8180, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1b828 : bv 32 := 0x03010513.
Lemma F_1b828 : fetch_word Ubsan.M.loaded_segments (0x1b828 : word) = Some W_1b828.
Proof. vm_refl. Qed.
Lemma D_1b828 : decode_any W_1b828 = Some (OpImm ALU_ADD 10 2 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1b82c : bv 32 := 0x214000ef.
Lemma F_1b82c : fetch_word Ubsan.M.loaded_segments (0x1b82c : word) = Some W_1b82c.
Proof. vm_refl. Qed.
Lemma D_1b82c : decode_any W_1b82c = Some (Jal 1 532, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1b830 : bv 32 := 0x0f813503.
Lemma F_1b830 : fetch_word Ubsan.M.loaded_segments (0x1b830 : word) = Some W_1b830.
Proof. vm_refl. Qed.
Lemma D_1b830 : decode_any W_1b830 = Some (Load SZ8 true 10 2 248, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1b834 : bv 32 := 0x4bc000ef.
Lemma F_1b834 : fetch_word Ubsan.M.loaded_segments (0x1b834 : word) = Some W_1b834.
Proof. vm_refl. Qed.
Lemma D_1b834 : decode_any W_1b834 = Some (Jal 1 1212, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1b838 : bv 32 := 0x08813503.
Lemma F_1b838 : fetch_word Ubsan.M.loaded_segments (0x1b838 : word) = Some W_1b838.
Proof. vm_refl. Qed.
Lemma D_1b838 : decode_any W_1b838 = Some (Load SZ8 true 10 2 136, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1b83c : bv 32 := 0x09013583.
Lemma F_1b83c : fetch_word Ubsan.M.loaded_segments (0x1b83c : word) = Some W_1b83c.
Proof. vm_refl. Qed.
Lemma D_1b83c : decode_any W_1b83c = Some (Load SZ8 true 11 2 144, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1b840 : bv 32 := 0x00b51c63.
Lemma F_1b840 : fetch_word Ubsan.M.loaded_segments (0x1b840 : word) = Some W_1b840.
Proof. vm_refl. Qed.
Lemma D_1b840 : decode_any W_1b840 = Some (Branch BC_NE 10 11 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1b844 : bv 32 := 0x09813503.
Lemma F_1b844 : fetch_word Ubsan.M.loaded_segments (0x1b844 : word) = Some W_1b844.
Proof. vm_refl. Qed.
Lemma D_1b844 : decode_any W_1b844 = Some (Load SZ8 true 10 2 152, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1b848 : bv 32 := 0x0a013583.
Lemma F_1b848 : fetch_word Ubsan.M.loaded_segments (0x1b848 : word) = Some W_1b848.
Proof. vm_refl. Qed.
Lemma D_1b848 : decode_any W_1b848 = Some (Load SZ8 true 11 2 160, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1b84c : bv 32 := 0x00b51663.
Lemma F_1b84c : fetch_word Ubsan.M.loaded_segments (0x1b84c : word) = Some W_1b84c.
Proof. vm_refl. Qed.
Lemma D_1b84c : decode_any W_1b84c = Some (Branch BC_NE 10 11 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1b850 : bv 32 := 0x0e813503.
Lemma F_1b850 : fetch_word Ubsan.M.loaded_segments (0x1b850 : word) = Some W_1b850.
Proof. vm_refl. Qed.
Lemma D_1b850 : decode_any W_1b850 = Some (Load SZ8 true 10 2 232, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1b854 : bv 32 := 0x0e050063.
Lemma F_1b854 : fetch_word Ubsan.M.loaded_segments (0x1b854 : word) = Some W_1b854.
Proof. vm_refl. Qed.
Lemma D_1b854 : decode_any W_1b854 = Some (Branch BC_EQ 10 0 224, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1b934 : bv 32 := 0x17813083.
Lemma F_1b934 : fetch_word Ubsan.M.loaded_segments (0x1b934 : word) = Some W_1b934.
Proof. vm_refl. Qed.
Lemma D_1b934 : decode_any W_1b934 = Some (Load SZ8 true 1 2 376, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1b938 : bv 32 := 0x17013403.
Lemma F_1b938 : fetch_word Ubsan.M.loaded_segments (0x1b938 : word) = Some W_1b938.
Proof. vm_refl. Qed.
Lemma D_1b938 : decode_any W_1b938 = Some (Load SZ8 true 8 2 368, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1b93c : bv 32 := 0x16813483.
Lemma F_1b93c : fetch_word Ubsan.M.loaded_segments (0x1b93c : word) = Some W_1b93c.
Proof. vm_refl. Qed.
Lemma D_1b93c : decode_any W_1b93c = Some (Load SZ8 true 9 2 360, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1b940 : bv 32 := 0x16013903.
Lemma F_1b940 : fetch_word Ubsan.M.loaded_segments (0x1b940 : word) = Some W_1b940.
Proof. vm_refl. Qed.
Lemma D_1b940 : decode_any W_1b940 = Some (Load SZ8 true 18 2 352, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1b944 : bv 32 := 0x18010113.
Lemma F_1b944 : fetch_word Ubsan.M.loaded_segments (0x1b944 : word) = Some W_1b944.
Proof. vm_refl. Qed.
Lemma D_1b944 : decode_any W_1b944 = Some (OpImm ALU_ADD 2 2 384, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1b948 : bv 32 := 0x00008067.
Lemma F_1b948 : fetch_word Ubsan.M.loaded_segments (0x1b948 : word) = Some W_1b948.
Proof. vm_refl. Qed.
Lemma D_1b948 : decode_any W_1b948 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1b94c : bv 32 := 0xfe010113.
Lemma F_1b94c : fetch_word Ubsan.M.loaded_segments (0x1b94c : word) = Some W_1b94c.
Proof. vm_refl. Qed.
Lemma D_1b94c : decode_any W_1b94c = Some (OpImm ALU_ADD 2 2 4064, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1b950 : bv 32 := 0x00113c23.
Lemma F_1b950 : fetch_word Ubsan.M.loaded_segments (0x1b950 : word) = Some W_1b950.
Proof. vm_refl. Qed.
Lemma D_1b950 : decode_any W_1b950 = Some (Store SZ8 2 1 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1b954 : bv 32 := 0x00813823.
Lemma F_1b954 : fetch_word Ubsan.M.loaded_segments (0x1b954 : word) = Some W_1b954.
Proof. vm_refl. Qed.
Lemma D_1b954 : decode_any W_1b954 = Some (Store SZ8 2 8 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1b958 : bv 32 := 0x00913423.
Lemma F_1b958 : fetch_word Ubsan.M.loaded_segments (0x1b958 : word) = Some W_1b958.
Proof. vm_refl. Qed.
Lemma D_1b958 : decode_any W_1b958 = Some (Store SZ8 2 9 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1b95c : bv 32 := 0xdc1ff0ef.
Lemma F_1b95c : fetch_word Ubsan.M.loaded_segments (0x1b95c : word) = Some W_1b95c.
Proof. vm_refl. Qed.
Lemma D_1b95c : decode_any W_1b95c = Some (Jal 1 2096576, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1b960 : bv 32 := 0x0000a517.
Lemma F_1b960 : fetch_word Ubsan.M.loaded_segments (0x1b960 : word) = Some W_1b960.
Proof. vm_refl. Qed.
Lemma D_1b960 : decode_any W_1b960 = Some (Auipc 10 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1b964 : bv 32 := 0x0000a597.
Lemma F_1b964 : fetch_word Ubsan.M.loaded_segments (0x1b964 : word) = Some W_1b964.
Proof. vm_refl. Qed.
Lemma D_1b964 : decode_any W_1b964 = Some (Auipc 11 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1b968 : bv 32 := 0xe6053403.
Lemma F_1b968 : fetch_word Ubsan.M.loaded_segments (0x1b968 : word) = Some W_1b968.
Proof. vm_refl. Qed.
Lemma D_1b968 : decode_any W_1b968 = Some (Load SZ8 true 8 10 3680, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1b96c : bv 32 := 0xe645b483.
Lemma F_1b96c : fetch_word Ubsan.M.loaded_segments (0x1b96c : word) = Some W_1b96c.
Proof. vm_refl. Qed.
Lemma D_1b96c : decode_any W_1b96c = Some (Load SZ8 true 9 11 3684, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1b970 : bv 32 := 0x0084fa63.
Lemma F_1b970 : fetch_word Ubsan.M.loaded_segments (0x1b970 : word) = Some W_1b970.
Proof. vm_refl. Qed.
Lemma D_1b970 : decode_any W_1b970 = Some (Branch BC_GEU 9 8 20, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1b974 : bv 32 := 0x0004b503.
Lemma F_1b974 : fetch_word Ubsan.M.loaded_segments (0x1b974 : word) = Some W_1b974.
Proof. vm_refl. Qed.
Lemma D_1b974 : decode_any W_1b974 = Some (Load SZ8 true 10 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1b978 : bv 32 := 0x000500e7.
Lemma F_1b978 : fetch_word Ubsan.M.loaded_segments (0x1b978 : word) = Some W_1b978.
Proof. vm_refl. Qed.
Lemma D_1b978 : decode_any W_1b978 = Some (Jalr 1 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1b97c : bv 32 := 0x00848493.
Lemma F_1b97c : fetch_word Ubsan.M.loaded_segments (0x1b97c : word) = Some W_1b97c.
Proof. vm_refl. Qed.
Lemma D_1b97c : decode_any W_1b97c = Some (OpImm ALU_ADD 9 9 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1b980 : bv 32 := 0xfe84eae3.
Lemma F_1b980 : fetch_word Ubsan.M.loaded_segments (0x1b980 : word) = Some W_1b980.
Proof. vm_refl. Qed.
Lemma D_1b980 : decode_any W_1b980 = Some (Branch BC_LTU 9 8 8180, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1b984 : bv 32 := 0x01813083.
Lemma F_1b984 : fetch_word Ubsan.M.loaded_segments (0x1b984 : word) = Some W_1b984.
Proof. vm_refl. Qed.
Lemma D_1b984 : decode_any W_1b984 = Some (Load SZ8 true 1 2 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1b988 : bv 32 := 0x01013403.
Lemma F_1b988 : fetch_word Ubsan.M.loaded_segments (0x1b988 : word) = Some W_1b988.
Proof. vm_refl. Qed.
Lemma D_1b988 : decode_any W_1b988 = Some (Load SZ8 true 8 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1b98c : bv 32 := 0x00813483.
Lemma F_1b98c : fetch_word Ubsan.M.loaded_segments (0x1b98c : word) = Some W_1b98c.
Proof. vm_refl. Qed.
Lemma D_1b98c : decode_any W_1b98c = Some (Load SZ8 true 9 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1b990 : bv 32 := 0x02010113.
Lemma F_1b990 : fetch_word Ubsan.M.loaded_segments (0x1b990 : word) = Some W_1b990.
Proof. vm_refl. Qed.
Lemma D_1b990 : decode_any W_1b990 = Some (OpImm ALU_ADD 2 2 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1b994 : bv 32 := 0x00008067.
Lemma F_1b994 : fetch_word Ubsan.M.loaded_segments (0x1b994 : word) = Some W_1b994.
Proof. vm_refl. Qed.
Lemma D_1b994 : decode_any W_1b994 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1b998 : bv 32 := 0xfe010113.
Lemma F_1b998 : fetch_word Ubsan.M.loaded_segments (0x1b998 : word) = Some W_1b998.
Proof. vm_refl. Qed.
Lemma D_1b998 : decode_any W_1b998 = Some (OpImm ALU_ADD 2 2 4064, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1b99c : bv 32 := 0x00113c23.
Lemma F_1b99c : fetch_word Ubsan.M.loaded_segments (0x1b99c : word) = Some W_1b99c.
Proof. vm_refl. Qed.
Lemma D_1b99c : decode_any W_1b99c = Some (Store SZ8 2 1 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1b9a0 : bv 32 := 0x00813823.
Lemma F_1b9a0 : fetch_word Ubsan.M.loaded_segments (0x1b9a0 : word) = Some W_1b9a0.
Proof. vm_refl. Qed.
Lemma D_1b9a0 : decode_any W_1b9a0 = Some (Store SZ8 2 8 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1b9a4 : bv 32 := 0x00913423.
Lemma F_1b9a4 : fetch_word Ubsan.M.loaded_segments (0x1b9a4 : word) = Some W_1b9a4.
Proof. vm_refl. Qed.
Lemma D_1b9a4 : decode_any W_1b9a4 = Some (Store SZ8 2 9 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1b9a8 : bv 32 := 0x01213023.
Lemma F_1b9a8 : fetch_word Ubsan.M.loaded_segments (0x1b9a8 : word) = Some W_1b9a8.
Proof. vm_refl. Qed.
Lemma D_1b9a8 : decode_any W_1b9a8 = Some (Store SZ8 2 18 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1b9ac : bv 32 := 0x00060413.
Lemma F_1b9ac : fetch_word Ubsan.M.loaded_segments (0x1b9ac : word) = Some W_1b9ac.
Proof. vm_refl. Qed.
Lemma D_1b9ac : decode_any W_1b9ac = Some (OpImm ALU_ADD 8 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1b9b0 : bv 32 := 0x00058493.
Lemma F_1b9b0 : fetch_word Ubsan.M.loaded_segments (0x1b9b0 : word) = Some W_1b9b0.
Proof. vm_refl. Qed.
Lemma D_1b9b0 : decode_any W_1b9b0 = Some (OpImm ALU_ADD 9 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1b9b4 : bv 32 := 0x00050913.
Lemma F_1b9b4 : fetch_word Ubsan.M.loaded_segments (0x1b9b4 : word) = Some W_1b9b4.
Proof. vm_refl. Qed.
Lemma D_1b9b4 : decode_any W_1b9b4 = Some (OpImm ALU_ADD 18 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1b9b8 : bv 32 := 0x00063583.
Lemma F_1b9b8 : fetch_word Ubsan.M.loaded_segments (0x1b9b8 : word) = Some W_1b9b8.
Proof. vm_refl. Qed.
Lemma D_1b9b8 : decode_any W_1b9b8 = Some (Load SZ8 true 11 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1b9bc : bv 32 := 0x00349513.
Lemma F_1b9bc : fetch_word Ubsan.M.loaded_segments (0x1b9bc : word) = Some W_1b9bc.
Proof. vm_refl. Qed.
Lemma D_1b9bc : decode_any W_1b9bc = Some (ShiftImm ALU_SLL 10 9 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1b9c0 : bv 32 := 0x00a60533.
Lemma F_1b9c0 : fetch_word Ubsan.M.loaded_segments (0x1b9c0 : word) = Some W_1b9c0.
Proof. vm_refl. Qed.
Lemma D_1b9c0 : decode_any W_1b9c0 = Some (Op ALU_ADD 10 12 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1b9c4 : bv 32 := 0x00850513.
Lemma F_1b9c4 : fetch_word Ubsan.M.loaded_segments (0x1b9c4 : word) = Some W_1b9c4.
Proof. vm_refl. Qed.
Lemma D_1b9c4 : decode_any W_1b9c4 = Some (OpImm ALU_ADD 10 10 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1b9c8 : bv 32 := 0xd59ff0ef.
Lemma F_1b9c8 : fetch_word Ubsan.M.loaded_segments (0x1b9c8 : word) = Some W_1b9c8.
Proof. vm_refl. Qed.
Lemma D_1b9c8 : decode_any W_1b9c8 = Some (Jal 1 2096472, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1b9cc : bv 32 := 0x00000517.
Lemma F_1b9cc : fetch_word Ubsan.M.loaded_segments (0x1b9cc : word) = Some W_1b9cc.
Proof. vm_refl. Qed.
Lemma D_1b9cc : decode_any W_1b9cc = Some (Auipc 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1b9d0 : bv 32 := 0x02c50313.
Lemma F_1b9d0 : fetch_word Ubsan.M.loaded_segments (0x1b9d0 : word) = Some W_1b9d0.
Proof. vm_refl. Qed.
Lemma D_1b9d0 : decode_any W_1b9d0 = Some (OpImm ALU_ADD 6 10 44, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1b9d4 : bv 32 := 0x00090513.
Lemma F_1b9d4 : fetch_word Ubsan.M.loaded_segments (0x1b9d4 : word) = Some W_1b9d4.
Proof. vm_refl. Qed.
Lemma D_1b9d4 : decode_any W_1b9d4 = Some (OpImm ALU_ADD 10 18 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1b9d8 : bv 32 := 0x00048593.
Lemma F_1b9d8 : fetch_word Ubsan.M.loaded_segments (0x1b9d8 : word) = Some W_1b9d8.
Proof. vm_refl. Qed.
Lemma D_1b9d8 : decode_any W_1b9d8 = Some (OpImm ALU_ADD 11 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1b9dc : bv 32 := 0x00040613.
Lemma F_1b9dc : fetch_word Ubsan.M.loaded_segments (0x1b9dc : word) = Some W_1b9dc.
Proof. vm_refl. Qed.
Lemma D_1b9dc : decode_any W_1b9dc = Some (OpImm ALU_ADD 12 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1b9e0 : bv 32 := 0x01813083.
Lemma F_1b9e0 : fetch_word Ubsan.M.loaded_segments (0x1b9e0 : word) = Some W_1b9e0.
Proof. vm_refl. Qed.
Lemma D_1b9e0 : decode_any W_1b9e0 = Some (Load SZ8 true 1 2 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1b9e4 : bv 32 := 0x01013403.
Lemma F_1b9e4 : fetch_word Ubsan.M.loaded_segments (0x1b9e4 : word) = Some W_1b9e4.
Proof. vm_refl. Qed.
Lemma D_1b9e4 : decode_any W_1b9e4 = Some (Load SZ8 true 8 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1b9e8 : bv 32 := 0x00813483.
Lemma F_1b9e8 : fetch_word Ubsan.M.loaded_segments (0x1b9e8 : word) = Some W_1b9e8.
Proof. vm_refl. Qed.
Lemma D_1b9e8 : decode_any W_1b9e8 = Some (Load SZ8 true 9 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1b9ec : bv 32 := 0x00013903.
Lemma F_1b9ec : fetch_word Ubsan.M.loaded_segments (0x1b9ec : word) = Some W_1b9ec.
Proof. vm_refl. Qed.
Lemma D_1b9ec : decode_any W_1b9ec = Some (Load SZ8 true 18 2 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1b9f0 : bv 32 := 0x02010113.
Lemma F_1b9f0 : fetch_word Ubsan.M.loaded_segments (0x1b9f0 : word) = Some W_1b9f0.
Proof. vm_refl. Qed.
Lemma D_1b9f0 : decode_any W_1b9f0 = Some (OpImm ALU_ADD 2 2 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1b9f4 : bv 32 := 0x00030067.
Lemma F_1b9f4 : fetch_word Ubsan.M.loaded_segments (0x1b9f4 : word) = Some W_1b9f4.
Proof. vm_refl. Qed.
Lemma D_1b9f4 : decode_any W_1b9f4 = Some (Jalr 0 6 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1b9f8 : bv 32 := 0xfd010113.
Lemma F_1b9f8 : fetch_word Ubsan.M.loaded_segments (0x1b9f8 : word) = Some W_1b9f8.
Proof. vm_refl. Qed.
Lemma D_1b9f8 : decode_any W_1b9f8 = Some (OpImm ALU_ADD 2 2 4048, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1b9fc : bv 32 := 0x02113423.
Lemma F_1b9fc : fetch_word Ubsan.M.loaded_segments (0x1b9fc : word) = Some W_1b9fc.
Proof. vm_refl. Qed.
Lemma D_1b9fc : decode_any W_1b9fc = Some (Store SZ8 2 1 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1ba00 : bv 32 := 0x02813023.
Lemma F_1ba00 : fetch_word Ubsan.M.loaded_segments (0x1ba00 : word) = Some W_1ba00.
Proof. vm_refl. Qed.
Lemma D_1ba00 : decode_any W_1ba00 = Some (Store SZ8 2 8 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1ba04 : bv 32 := 0x00913c23.
Lemma F_1ba04 : fetch_word Ubsan.M.loaded_segments (0x1ba04 : word) = Some W_1ba04.
Proof. vm_refl. Qed.
Lemma D_1ba04 : decode_any W_1ba04 = Some (Store SZ8 2 9 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1ba08 : bv 32 := 0x01213823.
Lemma F_1ba08 : fetch_word Ubsan.M.loaded_segments (0x1ba08 : word) = Some W_1ba08.
Proof. vm_refl. Qed.
Lemma D_1ba08 : decode_any W_1ba08 = Some (Store SZ8 2 18 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1ba0c : bv 32 := 0x01313423.
Lemma F_1ba0c : fetch_word Ubsan.M.loaded_segments (0x1ba0c : word) = Some W_1ba0c.
Proof. vm_refl. Qed.
Lemma D_1ba0c : decode_any W_1ba0c = Some (Store SZ8 2 19 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1ba10 : bv 32 := 0x00060413.
Lemma F_1ba10 : fetch_word Ubsan.M.loaded_segments (0x1ba10 : word) = Some W_1ba10.
Proof. vm_refl. Qed.
Lemma D_1ba10 : decode_any W_1ba10 = Some (OpImm ALU_ADD 8 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1ba14 : bv 32 := 0x00058493.
Lemma F_1ba14 : fetch_word Ubsan.M.loaded_segments (0x1ba14 : word) = Some W_1ba14.
Proof. vm_refl. Qed.
Lemma D_1ba14 : decode_any W_1ba14 = Some (OpImm ALU_ADD 9 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1ba18 : bv 32 := 0x00050913.
Lemma F_1ba18 : fetch_word Ubsan.M.loaded_segments (0x1ba18 : word) = Some W_1ba18.
Proof. vm_refl. Qed.
Lemma D_1ba18 : decode_any W_1ba18 = Some (OpImm ALU_ADD 18 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1ba1c : bv 32 := 0x00359513.
Lemma F_1ba1c : fetch_word Ubsan.M.loaded_segments (0x1ba1c : word) = Some W_1ba1c.
Proof. vm_refl. Qed.
Lemma D_1ba1c : decode_any W_1ba1c = Some (ShiftImm ALU_SLL 10 11 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1ba20 : bv 32 := 0x00a60533.
Lemma F_1ba20 : fetch_word Ubsan.M.loaded_segments (0x1ba20 : word) = Some W_1ba20.
Proof. vm_refl. Qed.
Lemma D_1ba20 : decode_any W_1ba20 = Some (Op ALU_ADD 10 12 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1ba24 : bv 32 := 0x00850993.
Lemma F_1ba24 : fetch_word Ubsan.M.loaded_segments (0x1ba24 : word) = Some W_1ba24.
Proof. vm_refl. Qed.
Lemma D_1ba24 : decode_any W_1ba24 = Some (OpImm ALU_ADD 19 10 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1ba28 : bv 32 := 0xf25ff0ef.
Lemma F_1ba28 : fetch_word Ubsan.M.loaded_segments (0x1ba28 : word) = Some W_1ba28.
Proof. vm_refl. Qed.
Lemma D_1ba28 : decode_any W_1ba28 = Some (Jal 1 2096932, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1ba2c : bv 32 := 0x00048513.
Lemma F_1ba2c : fetch_word Ubsan.M.loaded_segments (0x1ba2c : word) = Some W_1ba2c.
Proof. vm_refl. Qed.
Lemma D_1ba2c : decode_any W_1ba2c = Some (OpImm ALU_ADD 10 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1ba30 : bv 32 := 0x00040593.
Lemma F_1ba30 : fetch_word Ubsan.M.loaded_segments (0x1ba30 : word) = Some W_1ba30.
Proof. vm_refl. Qed.
Lemma D_1ba30 : decode_any W_1ba30 = Some (OpImm ALU_ADD 11 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1ba34 : bv 32 := 0x00098613.
Lemma F_1ba34 : fetch_word Ubsan.M.loaded_segments (0x1ba34 : word) = Some W_1ba34.
Proof. vm_refl. Qed.
Lemma D_1ba34 : decode_any W_1ba34 = Some (OpImm ALU_ADD 12 19 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1ba38 : bv 32 := 0x000900e7.
Lemma F_1ba38 : fetch_word Ubsan.M.loaded_segments (0x1ba38 : word) = Some W_1ba38.
Proof. vm_refl. Qed.
Lemma D_1ba38 : decode_any W_1ba38 = Some (Jalr 1 18 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1bcf0 : bv 32 := 0xff010113.
Lemma F_1bcf0 : fetch_word Ubsan.M.loaded_segments (0x1bcf0 : word) = Some W_1bcf0.
Proof. vm_refl. Qed.
Lemma D_1bcf0 : decode_any W_1bcf0 = Some (OpImm ALU_ADD 2 2 4080, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1bcf4 : bv 32 := 0x00113423.
Lemma F_1bcf4 : fetch_word Ubsan.M.loaded_segments (0x1bcf4 : word) = Some W_1bcf4.
Proof. vm_refl. Qed.
Lemma D_1bcf4 : decode_any W_1bcf4 = Some (Store SZ8 2 1 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1bcf8 : bv 32 := 0x00050e63.
Lemma F_1bcf8 : fetch_word Ubsan.M.loaded_segments (0x1bcf8 : word) = Some W_1bcf8.
Proof. vm_refl. Qed.
Lemma D_1bcf8 : decode_any W_1bcf8 = Some (Branch BC_EQ 10 0 28, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1bcfc : bv 32 := 0x00050593.
Lemma F_1bcfc : fetch_word Ubsan.M.loaded_segments (0x1bcfc : word) = Some W_1bcfc.
Proof. vm_refl. Qed.
Lemma D_1bcfc : decode_any W_1bcfc = Some (OpImm ALU_ADD 11 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1bd00 : bv 32 := 0x0000a517.
Lemma F_1bd00 : fetch_word Ubsan.M.loaded_segments (0x1bd00 : word) = Some W_1bd00.
Proof. vm_refl. Qed.
Lemma D_1bd00 : decode_any W_1bd00 = Some (Auipc 10 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1bd04 : bv 32 := 0xaa053503.
Lemma F_1bd04 : fetch_word Ubsan.M.loaded_segments (0x1bd04 : word) = Some W_1bd04.
Proof. vm_refl. Qed.
Lemma D_1bd04 : decode_any W_1bd04 = Some (Load SZ8 true 10 10 2720, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1bd08 : bv 32 := 0x00800613.
Lemma F_1bd08 : fetch_word Ubsan.M.loaded_segments (0x1bd08 : word) = Some W_1bd08.
Proof. vm_refl. Qed.
Lemma D_1bd08 : decode_any W_1bd08 = Some (OpImm ALU_ADD 12 0 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1bd0c : bv 32 := 0x5dd070ef.
Lemma F_1bd0c : fetch_word Ubsan.M.loaded_segments (0x1bd0c : word) = Some W_1bd0c.
Proof. vm_refl. Qed.
Lemma D_1bd0c : decode_any W_1bd0c = Some (Jal 1 32220, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1bd10 : bv 32 := 0x01c0006f.
Lemma F_1bd10 : fetch_word Ubsan.M.loaded_segments (0x1bd10 : word) = Some W_1bd10.
Proof. vm_refl. Qed.
Lemma D_1bd10 : decode_any W_1bd10 = Some (Jal 0 28, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1bd2c : bv 32 := 0x0000a517.
Lemma F_1bd2c : fetch_word Ubsan.M.loaded_segments (0x1bd2c : word) = Some W_1bd2c.
Proof. vm_refl. Qed.
Lemma D_1bd2c : decode_any W_1bd2c = Some (Auipc 10 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1bd30 : bv 32 := 0xa7453503.
Lemma F_1bd30 : fetch_word Ubsan.M.loaded_segments (0x1bd30 : word) = Some W_1bd30.
Proof. vm_refl. Qed.
Lemma D_1bd30 : decode_any W_1bd30 = Some (Load SZ8 true 10 10 2676, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1bd34 : bv 32 := 0x000500a3.
Lemma F_1bd34 : fetch_word Ubsan.M.loaded_segments (0x1bd34 : word) = Some W_1bd34.
Proof. vm_refl. Qed.
Lemma D_1bd34 : decode_any W_1bd34 = Some (Store SZ1 10 0 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1bd38 : bv 32 := 0x00053503.
Lemma F_1bd38 : fetch_word Ubsan.M.loaded_segments (0x1bd38 : word) = Some W_1bd38.
Proof. vm_refl. Qed.
Lemma D_1bd38 : decode_any W_1bd38 = Some (Load SZ8 true 10 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1bd3c : bv 32 := 0x00020593.
Lemma F_1bd3c : fetch_word Ubsan.M.loaded_segments (0x1bd3c : word) = Some W_1bd3c.
Proof. vm_refl. Qed.
Lemma D_1bd3c : decode_any W_1bd3c = Some (OpImm ALU_ADD 11 4 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1bd40 : bv 32 := 0xfea5b823.
Lemma F_1bd40 : fetch_word Ubsan.M.loaded_segments (0x1bd40 : word) = Some W_1bd40.
Proof. vm_refl. Qed.
Lemma D_1bd40 : decode_any W_1bd40 = Some (Store SZ8 11 10 4080, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1bd44 : bv 32 := 0x00813083.
Lemma F_1bd44 : fetch_word Ubsan.M.loaded_segments (0x1bd44 : word) = Some W_1bd44.
Proof. vm_refl. Qed.
Lemma D_1bd44 : decode_any W_1bd44 = Some (Load SZ8 true 1 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1bd48 : bv 32 := 0x01010113.
Lemma F_1bd48 : fetch_word Ubsan.M.loaded_segments (0x1bd48 : word) = Some W_1bd48.
Proof. vm_refl. Qed.
Lemma D_1bd48 : decode_any W_1bd48 = Some (OpImm ALU_ADD 2 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1bd4c : bv 32 := 0x00008067.
Lemma F_1bd4c : fetch_word Ubsan.M.loaded_segments (0x1bd4c : word) = Some W_1bd4c.
Proof. vm_refl. Qed.
Lemma D_1bd4c : decode_any W_1bd4c = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1bd58 : bv 32 := 0x00020513.
Lemma F_1bd58 : fetch_word Ubsan.M.loaded_segments (0x1bd58 : word) = Some W_1bd58.
Proof. vm_refl. Qed.
Lemma D_1bd58 : decode_any W_1bd58 = Some (OpImm ALU_ADD 10 4 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1bd5c : bv 32 := 0xf5c50513.
Lemma F_1bd5c : fetch_word Ubsan.M.loaded_segments (0x1bd5c : word) = Some W_1bd5c.
Proof. vm_refl. Qed.
Lemma D_1bd5c : decode_any W_1bd5c = Some (OpImm ALU_ADD 10 10 3932, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1bd60 : bv 32 := 0x00008067.
Lemma F_1bd60 : fetch_word Ubsan.M.loaded_segments (0x1bd60 : word) = Some W_1bd60.
Proof. vm_refl. Qed.
Lemma D_1bd60 : decode_any W_1bd60 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1bda0 : bv 32 := 0x00050593.
Lemma F_1bda0 : fetch_word Ubsan.M.loaded_segments (0x1bda0 : word) = Some W_1bda0.
Proof. vm_refl. Qed.
Lemma D_1bda0 : decode_any W_1bda0 = Some (OpImm ALU_ADD 11 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1bda4 : bv 32 := 0x05e00893.
Lemma F_1bda4 : fetch_word Ubsan.M.loaded_segments (0x1bda4 : word) = Some W_1bda4.
Proof. vm_refl. Qed.
Lemma D_1bda4 : decode_any W_1bda4 = Some (OpImm ALU_ADD 17 0 94, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1bda8 : bv 32 := 0x00000073.
Lemma F_1bda8 : fetch_word Ubsan.M.loaded_segments (0x1bda8 : word) = Some W_1bda8.
Proof. vm_refl. Qed.
Lemma D_1bda8 : decode_any W_1bda8 = Some (Ecall, 4%Z).
Proof. vm_refl. Qed.
Lemma E_1bda8 : is_ecall W_1bda8 = true.
Proof. reflexivity. Qed.

(* [comment removed for export] *)
Definition W_1bdbc : bv 32 := 0xfd010113.
Lemma F_1bdbc : fetch_word Ubsan.M.loaded_segments (0x1bdbc : word) = Some W_1bdbc.
Proof. vm_refl. Qed.
Lemma D_1bdbc : decode_any W_1bdbc = Some (OpImm ALU_ADD 2 2 4048, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1bdc0 : bv 32 := 0x02113423.
Lemma F_1bdc0 : fetch_word Ubsan.M.loaded_segments (0x1bdc0 : word) = Some W_1bdc0.
Proof. vm_refl. Qed.
Lemma D_1bdc0 : decode_any W_1bdc0 = Some (Store SZ8 2 1 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1bdc4 : bv 32 := 0x02813023.
Lemma F_1bdc4 : fetch_word Ubsan.M.loaded_segments (0x1bdc4 : word) = Some W_1bdc4.
Proof. vm_refl. Qed.
Lemma D_1bdc4 : decode_any W_1bdc4 = Some (Store SZ8 2 8 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1bdc8 : bv 32 := 0x00913c23.
Lemma F_1bdc8 : fetch_word Ubsan.M.loaded_segments (0x1bdc8 : word) = Some W_1bdc8.
Proof. vm_refl. Qed.
Lemma D_1bdc8 : decode_any W_1bdc8 = Some (Store SZ8 2 9 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1bdcc : bv 32 := 0x01213823.
Lemma F_1bdcc : fetch_word Ubsan.M.loaded_segments (0x1bdcc : word) = Some W_1bdcc.
Proof. vm_refl. Qed.
Lemma D_1bdcc : decode_any W_1bdcc = Some (Store SZ8 2 18 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1bdd0 : bv 32 := 0x01313423.
Lemma F_1bdd0 : fetch_word Ubsan.M.loaded_segments (0x1bdd0 : word) = Some W_1bdd0.
Proof. vm_refl. Qed.
Lemma D_1bdd0 : decode_any W_1bdd0 = Some (Store SZ8 2 19 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1bdd4 : bv 32 := 0x0003b517.
Lemma F_1bdd4 : fetch_word Ubsan.M.loaded_segments (0x1bdd4 : word) = Some W_1bdd4.
Proof. vm_refl. Qed.
Lemma D_1bdd4 : decode_any W_1bdd4 = Some (Auipc 10 59, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1bdd8 : bv 32 := 0xed450913.
Lemma F_1bdd8 : fetch_word Ubsan.M.loaded_segments (0x1bdd8 : word) = Some W_1bdd8.
Proof. vm_refl. Qed.
Lemma D_1bdd8 : decode_any W_1bdd8 = Some (OpImm ALU_ADD 18 10 3796, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1bddc : bv 32 := 0x00490413.
Lemma F_1bddc : fetch_word Ubsan.M.loaded_segments (0x1bddc : word) = Some W_1bddc.
Proof. vm_refl. Qed.
Lemma D_1bddc : decode_any W_1bddc = Some (OpImm ALU_ADD 8 18 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1bde0 : bv 32 := 0x00040513.
Lemma F_1bde0 : fetch_word Ubsan.M.loaded_segments (0x1bde0 : word) = Some W_1bde0.
Proof. vm_refl. Qed.
Lemma D_1bde0 : decode_any W_1bde0 = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1bde4 : bv 32 := 0x444080ef.
Lemma F_1bde4 : fetch_word Ubsan.M.loaded_segments (0x1bde4 : word) = Some W_1bde4.
Proof. vm_refl. Qed.
Lemma D_1bde4 : decode_any W_1bde4 = Some (Jal 1 33860, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1bde8 : bv 32 := 0x01093503.
Lemma F_1bde8 : fetch_word Ubsan.M.loaded_segments (0x1bde8 : word) = Some W_1bde8.
Proof. vm_refl. Qed.
Lemma D_1bde8 : decode_any W_1bde8 = Some (Load SZ8 true 10 18 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1bdec : bv 32 := 0x06050863.
Lemma F_1bdec : fetch_word Ubsan.M.loaded_segments (0x1bdec : word) = Some W_1bdec.
Proof. vm_refl. Qed.
Lemma D_1bdec : decode_any W_1bdec = Some (Branch BC_EQ 10 0 112, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1be5c : bv 32 := 0x00100513.
Lemma F_1be5c : fetch_word Ubsan.M.loaded_segments (0x1be5c : word) = Some W_1be5c.
Proof. vm_refl. Qed.
Lemma D_1be5c : decode_any W_1be5c = Some (OpImm ALU_ADD 10 0 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1be60 : bv 32 := 0x00a90023.
Lemma F_1be60 : fetch_word Ubsan.M.loaded_segments (0x1be60 : word) = Some W_1be60.
Proof. vm_refl. Qed.
Lemma D_1be60 : decode_any W_1be60 = Some (Store SZ1 18 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1be64 : bv 32 := 0x00040513.
Lemma F_1be64 : fetch_word Ubsan.M.loaded_segments (0x1be64 : word) = Some W_1be64.
Proof. vm_refl. Qed.
Lemma D_1be64 : decode_any W_1be64 = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1be68 : bv 32 := 0x02813083.
Lemma F_1be68 : fetch_word Ubsan.M.loaded_segments (0x1be68 : word) = Some W_1be68.
Proof. vm_refl. Qed.
Lemma D_1be68 : decode_any W_1be68 = Some (Load SZ8 true 1 2 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1be6c : bv 32 := 0x02013403.
Lemma F_1be6c : fetch_word Ubsan.M.loaded_segments (0x1be6c : word) = Some W_1be6c.
Proof. vm_refl. Qed.
Lemma D_1be6c : decode_any W_1be6c = Some (Load SZ8 true 8 2 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1be70 : bv 32 := 0x01813483.
Lemma F_1be70 : fetch_word Ubsan.M.loaded_segments (0x1be70 : word) = Some W_1be70.
Proof. vm_refl. Qed.
Lemma D_1be70 : decode_any W_1be70 = Some (Load SZ8 true 9 2 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1be74 : bv 32 := 0x01013903.
Lemma F_1be74 : fetch_word Ubsan.M.loaded_segments (0x1be74 : word) = Some W_1be74.
Proof. vm_refl. Qed.
Lemma D_1be74 : decode_any W_1be74 = Some (Load SZ8 true 18 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1be78 : bv 32 := 0x00813983.
Lemma F_1be78 : fetch_word Ubsan.M.loaded_segments (0x1be78 : word) = Some W_1be78.
Proof. vm_refl. Qed.
Lemma D_1be78 : decode_any W_1be78 = Some (Load SZ8 true 19 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1be7c : bv 32 := 0x03010113.
Lemma F_1be7c : fetch_word Ubsan.M.loaded_segments (0x1be7c : word) = Some W_1be7c.
Proof. vm_refl. Qed.
Lemma D_1be7c : decode_any W_1be7c = Some (OpImm ALU_ADD 2 2 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1be80 : bv 32 := 0x6300806f.
Lemma F_1be80 : fetch_word Ubsan.M.loaded_segments (0x1be80 : word) = Some W_1be80.
Proof. vm_refl. Qed.
Lemma D_1be80 : decode_any W_1be80 = Some (Jal 0 34352, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1be84 : bv 32 := 0x00008067.
Lemma F_1be84 : fetch_word Ubsan.M.loaded_segments (0x1be84 : word) = Some W_1be84.
Proof. vm_refl. Qed.
Lemma D_1be84 : decode_any W_1be84 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1bf50 : bv 32 := 0x00008067.
Lemma F_1bf50 : fetch_word Ubsan.M.loaded_segments (0x1bf50 : word) = Some W_1bf50.
Proof. vm_refl. Qed.
Lemma D_1bf50 : decode_any W_1bf50 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1bf54 : bv 32 := 0xfe010113.
Lemma F_1bf54 : fetch_word Ubsan.M.loaded_segments (0x1bf54 : word) = Some W_1bf54.
Proof. vm_refl. Qed.
Lemma D_1bf54 : decode_any W_1bf54 = Some (OpImm ALU_ADD 2 2 4064, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1bf58 : bv 32 := 0x00113c23.
Lemma F_1bf58 : fetch_word Ubsan.M.loaded_segments (0x1bf58 : word) = Some W_1bf58.
Proof. vm_refl. Qed.
Lemma D_1bf58 : decode_any W_1bf58 = Some (Store SZ8 2 1 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1bf5c : bv 32 := 0x00813823.
Lemma F_1bf5c : fetch_word Ubsan.M.loaded_segments (0x1bf5c : word) = Some W_1bf5c.
Proof. vm_refl. Qed.
Lemma D_1bf5c : decode_any W_1bf5c = Some (Store SZ8 2 8 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1bf60 : bv 32 := 0x00913423.
Lemma F_1bf60 : fetch_word Ubsan.M.loaded_segments (0x1bf60 : word) = Some W_1bf60.
Proof. vm_refl. Qed.
Lemma D_1bf60 : decode_any W_1bf60 = Some (Store SZ8 2 9 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1bf64 : bv 32 := 0x0000a517.
Lemma F_1bf64 : fetch_word Ubsan.M.loaded_segments (0x1bf64 : word) = Some W_1bf64.
Proof. vm_refl. Qed.
Lemma D_1bf64 : decode_any W_1bf64 = Some (Auipc 10 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1bf68 : bv 32 := 0x0000a597.
Lemma F_1bf68 : fetch_word Ubsan.M.loaded_segments (0x1bf68 : word) = Some W_1bf68.
Proof. vm_refl. Qed.
Lemma D_1bf68 : decode_any W_1bf68 = Some (Auipc 11 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1bf6c : bv 32 := 0x86c53503.
Lemma F_1bf6c : fetch_word Ubsan.M.loaded_segments (0x1bf6c : word) = Some W_1bf6c.
Proof. vm_refl. Qed.
Lemma D_1bf6c : decode_any W_1bf6c = Some (Load SZ8 true 10 10 2156, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1bf70 : bv 32 := 0x8705b403.
Lemma F_1bf70 : fetch_word Ubsan.M.loaded_segments (0x1bf70 : word) = Some W_1bf70.
Proof. vm_refl. Qed.
Lemma D_1bf70 : decode_any W_1bf70 = Some (Load SZ8 true 8 11 2160, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1bf74 : bv 32 := 0x00a47c63.
Lemma F_1bf74 : fetch_word Ubsan.M.loaded_segments (0x1bf74 : word) = Some W_1bf74.
Proof. vm_refl. Qed.
Lemma D_1bf74 : decode_any W_1bf74 = Some (Branch BC_GEU 8 10 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1bf78 : bv 32 := 0xff853583.
Lemma F_1bf78 : fetch_word Ubsan.M.loaded_segments (0x1bf78 : word) = Some W_1bf78.
Proof. vm_refl. Qed.
Lemma D_1bf78 : decode_any W_1bf78 = Some (Load SZ8 true 11 10 4088, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1bf7c : bv 32 := 0xff850493.
Lemma F_1bf7c : fetch_word Ubsan.M.loaded_segments (0x1bf7c : word) = Some W_1bf7c.
Proof. vm_refl. Qed.
Lemma D_1bf7c : decode_any W_1bf7c = Some (OpImm ALU_ADD 9 10 4088, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1bf80 : bv 32 := 0x000580e7.
Lemma F_1bf80 : fetch_word Ubsan.M.loaded_segments (0x1bf80 : word) = Some W_1bf80.
Proof. vm_refl. Qed.
Lemma D_1bf80 : decode_any W_1bf80 = Some (Jalr 1 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1bf84 : bv 32 := 0x00048513.
Lemma F_1bf84 : fetch_word Ubsan.M.loaded_segments (0x1bf84 : word) = Some W_1bf84.
Proof. vm_refl. Qed.
Lemma D_1bf84 : decode_any W_1bf84 = Some (OpImm ALU_ADD 10 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1bf88 : bv 32 := 0xfe9468e3.
Lemma F_1bf88 : fetch_word Ubsan.M.loaded_segments (0x1bf88 : word) = Some W_1bf88.
Proof. vm_refl. Qed.
Lemma D_1bf88 : decode_any W_1bf88 = Some (Branch BC_LTU 8 9 8176, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1bf8c : bv 32 := 0x01813083.
Lemma F_1bf8c : fetch_word Ubsan.M.loaded_segments (0x1bf8c : word) = Some W_1bf8c.
Proof. vm_refl. Qed.
Lemma D_1bf8c : decode_any W_1bf8c = Some (Load SZ8 true 1 2 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1bf90 : bv 32 := 0x01013403.
Lemma F_1bf90 : fetch_word Ubsan.M.loaded_segments (0x1bf90 : word) = Some W_1bf90.
Proof. vm_refl. Qed.
Lemma D_1bf90 : decode_any W_1bf90 = Some (Load SZ8 true 8 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1bf94 : bv 32 := 0x00813483.
Lemma F_1bf94 : fetch_word Ubsan.M.loaded_segments (0x1bf94 : word) = Some W_1bf94.
Proof. vm_refl. Qed.
Lemma D_1bf94 : decode_any W_1bf94 = Some (Load SZ8 true 9 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1bf98 : bv 32 := 0x02010113.
Lemma F_1bf98 : fetch_word Ubsan.M.loaded_segments (0x1bf98 : word) = Some W_1bf98.
Proof. vm_refl. Qed.
Lemma D_1bf98 : decode_any W_1bf98 = Some (OpImm ALU_ADD 2 2 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1bf9c : bv 32 := 0xfb5ff06f.
Lemma F_1bf9c : fetch_word Ubsan.M.loaded_segments (0x1bf9c : word) = Some W_1bf9c.
Proof. vm_refl. Qed.
Lemma D_1bf9c : decode_any W_1bf9c = Some (Jal 0 2097076, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1bfa0 : bv 32 := 0xff010113.
Lemma F_1bfa0 : fetch_word Ubsan.M.loaded_segments (0x1bfa0 : word) = Some W_1bfa0.
Proof. vm_refl. Qed.
Lemma D_1bfa0 : decode_any W_1bfa0 = Some (OpImm ALU_ADD 2 2 4080, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1bfa4 : bv 32 := 0x00113423.
Lemma F_1bfa4 : fetch_word Ubsan.M.loaded_segments (0x1bfa4 : word) = Some W_1bfa4.
Proof. vm_refl. Qed.
Lemma D_1bfa4 : decode_any W_1bfa4 = Some (Store SZ8 2 1 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1bfa8 : bv 32 := 0x00813023.
Lemma F_1bfa8 : fetch_word Ubsan.M.loaded_segments (0x1bfa8 : word) = Some W_1bfa8.
Proof. vm_refl. Qed.
Lemma D_1bfa8 : decode_any W_1bfa8 = Some (Store SZ8 2 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1bfac : bv 32 := 0x00000593.
Lemma F_1bfac : fetch_word Ubsan.M.loaded_segments (0x1bfac : word) = Some W_1bfac.
Proof. vm_refl. Qed.
Lemma D_1bfac : decode_any W_1bfac = Some (OpImm ALU_ADD 11 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1bfb0 : bv 32 := 0x00020613.
Lemma F_1bfb0 : fetch_word Ubsan.M.loaded_segments (0x1bfb0 : word) = Some W_1bfb0.
Proof. vm_refl. Qed.
Lemma D_1bfb0 : decode_any W_1bfb0 = Some (OpImm ALU_ADD 12 4 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1bfb4 : bv 32 := 0xf5862603.
Lemma F_1bfb4 : fetch_word Ubsan.M.loaded_segments (0x1bfb4 : word) = Some W_1bfb4.
Proof. vm_refl. Qed.
Lemma D_1bfb4 : decode_any W_1bfb4 = Some (Load SZ4 true 12 12 3928, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1bfb8 : bv 32 := 0x0003b697.
Lemma F_1bfb8 : fetch_word Ubsan.M.loaded_segments (0x1bfb8 : word) = Some W_1bfb8.
Proof. vm_refl. Qed.
Lemma D_1bfb8 : decode_any W_1bfb8 = Some (Auipc 13 59, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1bfbc : bv 32 := 0xf1068693.
Lemma F_1bfbc : fetch_word Ubsan.M.loaded_segments (0x1bfbc : word) = Some W_1bfbc.
Proof. vm_refl. Qed.
Lemma D_1bfbc : decode_any W_1bfbc = Some (OpImm ALU_ADD 13 13 3856, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1bfc0 : bv 32 := 0x1606a72f.
Lemma F_1bfc0 : fetch_word Ubsan.M.loaded_segments (0x1bfc0 : word) = Some W_1bfc0.
Proof. vm_refl. Qed.
Lemma D_1bfc0 : decode_any W_1bfc0 = Some (Lr AW true true 14 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1bfc4 : bv 32 := 0x00b71663.
Lemma F_1bfc4 : fetch_word Ubsan.M.loaded_segments (0x1bfc4 : word) = Some W_1bfc4.
Proof. vm_refl. Qed.
Lemma D_1bfc4 : decode_any W_1bfc4 = Some (Branch BC_NE 14 11 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1bfc8 : bv 32 := 0x1ec6a7af.
Lemma F_1bfc8 : fetch_word Ubsan.M.loaded_segments (0x1bfc8 : word) = Some W_1bfc8.
Proof. vm_refl. Qed.
Lemma D_1bfc8 : decode_any W_1bfc8 = Some (Sc AW true true 15 13 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1bfcc : bv 32 := 0xfe079ae3.
Lemma F_1bfcc : fetch_word Ubsan.M.loaded_segments (0x1bfcc : word) = Some W_1bfcc.
Proof. vm_refl. Qed.
Lemma D_1bfcc : decode_any W_1bfcc = Some (Branch BC_NE 15 0 8180, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1bfd0 : bv 32 := 0x0007059b.
Lemma F_1bfd0 : fetch_word Ubsan.M.loaded_segments (0x1bfd0 : word) = Some W_1bfd0.
Proof. vm_refl. Qed.
Lemma D_1bfd0 : decode_any W_1bfd0 = Some (OpImm32 11 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1bfd4 : bv 32 := 0x02c58263.
Lemma F_1bfd4 : fetch_word Ubsan.M.loaded_segments (0x1bfd4 : word) = Some W_1bfd4.
Proof. vm_refl. Qed.
Lemma D_1bfd4 : decode_any W_1bfd4 = Some (Branch BC_EQ 11 12 36, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1bfd8 : bv 32 := 0x02058263.
Lemma F_1bfd8 : fetch_word Ubsan.M.loaded_segments (0x1bfd8 : word) = Some W_1bfd8.
Proof. vm_refl. Qed.
Lemma D_1bfd8 : decode_any W_1bfd8 = Some (Branch BC_EQ 11 0 36, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1bffc : bv 32 := 0x00050413.
Lemma F_1bffc : fetch_word Ubsan.M.loaded_segments (0x1bffc : word) = Some W_1bffc.
Proof. vm_refl. Qed.
Lemma D_1bffc : decode_any W_1bffc = Some (OpImm ALU_ADD 8 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1c000 : bv 32 := 0xdbdff0ef.
Lemma F_1c000 : fetch_word Ubsan.M.loaded_segments (0x1c000 : word) = Some W_1c000.
Proof. vm_refl. Qed.
Lemma D_1c000 : decode_any W_1c000 = Some (Jal 1 2096572, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1c004 : bv 32 := 0xf51ff0ef.
Lemma F_1c004 : fetch_word Ubsan.M.loaded_segments (0x1c004 : word) = Some W_1c004.
Proof. vm_refl. Qed.
Lemma D_1c004 : decode_any W_1c004 = Some (Jal 1 2096976, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1c008 : bv 32 := 0x224020ef.
Lemma F_1c008 : fetch_word Ubsan.M.loaded_segments (0x1c008 : word) = Some W_1c008.
Proof. vm_refl. Qed.
Lemma D_1c008 : decode_any W_1c008 = Some (Jal 1 8740, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1c00c : bv 32 := 0x00040513.
Lemma F_1c00c : fetch_word Ubsan.M.loaded_segments (0x1c00c : word) = Some W_1c00c.
Proof. vm_refl. Qed.
Lemma D_1c00c : decode_any W_1c00c = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1c010 : bv 32 := 0xd91ff0ef.
Lemma F_1c010 : fetch_word Ubsan.M.loaded_segments (0x1c010 : word) = Some W_1c010.
Proof. vm_refl. Qed.
Lemma D_1c010 : decode_any W_1c010 = Some (Jal 1 2096528, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1c0f8 : bv 32 := 0xfffff5b7.
Lemma F_1c0f8 : fetch_word Ubsan.M.loaded_segments (0x1c0f8 : word) = Some W_1c0f8.
Proof. vm_refl. Qed.
Lemma D_1c0f8 : decode_any W_1c0f8 = Some (Lui 11 1048575, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1c0fc : bv 32 := 0x0015859b.
Lemma F_1c0fc : fetch_word Ubsan.M.loaded_segments (0x1c0fc : word) = Some W_1c0fc.
Proof. vm_refl. Qed.
Lemma D_1c0fc : decode_any W_1c0fc = Some (OpImm32 11 11 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1c100 : bv 32 := 0x02b56663.
Lemma F_1c100 : fetch_word Ubsan.M.loaded_segments (0x1c100 : word) = Some W_1c100.
Proof. vm_refl. Qed.
Lemma D_1c100 : decode_any W_1c100 = Some (Branch BC_LTU 10 11 44, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1c12c : bv 32 := 0x00008067.
Lemma F_1c12c : fetch_word Ubsan.M.loaded_segments (0x1c12c : word) = Some W_1c12c.
Proof. vm_refl. Qed.
Lemma D_1c12c : decode_any W_1c12c = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1c27c : bv 32 := 0x1c050463.
Lemma F_1c27c : fetch_word Ubsan.M.loaded_segments (0x1c27c : word) = Some W_1c27c.
Proof. vm_refl. Qed.
Lemma D_1c27c : decode_any W_1c27c = Some (Branch BC_EQ 10 0 456, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1c280 : bv 32 := 0xfd010113.
Lemma F_1c280 : fetch_word Ubsan.M.loaded_segments (0x1c280 : word) = Some W_1c280.
Proof. vm_refl. Qed.
Lemma D_1c280 : decode_any W_1c280 = Some (OpImm ALU_ADD 2 2 4048, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1c284 : bv 32 := 0x02113423.
Lemma F_1c284 : fetch_word Ubsan.M.loaded_segments (0x1c284 : word) = Some W_1c284.
Proof. vm_refl. Qed.
Lemma D_1c284 : decode_any W_1c284 = Some (Store SZ8 2 1 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1c288 : bv 32 := 0x02813023.
Lemma F_1c288 : fetch_word Ubsan.M.loaded_segments (0x1c288 : word) = Some W_1c288.
Proof. vm_refl. Qed.
Lemma D_1c288 : decode_any W_1c288 = Some (Store SZ8 2 8 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1c28c : bv 32 := 0x00913c23.
Lemma F_1c28c : fetch_word Ubsan.M.loaded_segments (0x1c28c : word) = Some W_1c28c.
Proof. vm_refl. Qed.
Lemma D_1c28c : decode_any W_1c28c = Some (Store SZ8 2 9 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1c290 : bv 32 := 0x01213823.
Lemma F_1c290 : fetch_word Ubsan.M.loaded_segments (0x1c290 : word) = Some W_1c290.
Proof. vm_refl. Qed.
Lemma D_1c290 : decode_any W_1c290 = Some (Store SZ8 2 18 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1c294 : bv 32 := 0x01313423.
Lemma F_1c294 : fetch_word Ubsan.M.loaded_segments (0x1c294 : word) = Some W_1c294.
Proof. vm_refl. Qed.
Lemma D_1c294 : decode_any W_1c294 = Some (Store SZ8 2 19 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1c298 : bv 32 := 0x00050493.
Lemma F_1c298 : fetch_word Ubsan.M.loaded_segments (0x1c298 : word) = Some W_1c298.
Proof. vm_refl. Qed.
Lemma D_1c298 : decode_any W_1c298 = Some (OpImm ALU_ADD 9 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1c29c : bv 32 := 0x1ac000ef.
Lemma F_1c29c : fetch_word Ubsan.M.loaded_segments (0x1c29c : word) = Some W_1c29c.
Proof. vm_refl. Qed.
Lemma D_1c29c : decode_any W_1c29c = Some (Jal 1 428, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1c2a0 : bv 32 := 0x02053583.
Lemma F_1c2a0 : fetch_word Ubsan.M.loaded_segments (0x1c2a0 : word) = Some W_1c2a0.
Proof. vm_refl. Qed.
Lemma D_1c2a0 : decode_any W_1c2a0 = Some (Load SZ8 true 11 10 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1c2a4 : bv 32 := 0xffd4c683.
Lemma F_1c2a4 : fetch_word Ubsan.M.loaded_segments (0x1c2a4 : word) = Some W_1c2a4.
Proof. vm_refl. Qed.
Lemma D_1c2a4 : decode_any W_1c2a4 = Some (Load SZ1 false 13 9 4093, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1c2a8 : bv 32 := 0x00c5d613.
Lemma F_1c2a8 : fetch_word Ubsan.M.loaded_segments (0x1c2a8 : word) = Some W_1c2a8.
Proof. vm_refl. Qed.
Lemma D_1c2a8 : decode_any W_1c2a8 = Some (ShiftImm ALU_SRL 12 11 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1c2ac : bv 32 := 0x01f6f413.
Lemma F_1c2ac : fetch_word Ubsan.M.loaded_segments (0x1c2ac : word) = Some W_1c2ac.
Proof. vm_refl. Qed.
Lemma D_1c2ac : decode_any W_1c2ac = Some (OpImm ALU_AND 8 13 31, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1c2b0 : bv 32 := 0x00060e63.
Lemma F_1c2b0 : fetch_word Ubsan.M.loaded_segments (0x1c2b0 : word) = Some W_1c2b0.
Proof. vm_refl. Qed.
Lemma D_1c2b0 : decode_any W_1c2b0 = Some (Branch BC_EQ 12 0 28, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1c2b4 : bv 32 := 0x01f5f613.
Lemma F_1c2b4 : fetch_word Ubsan.M.loaded_segments (0x1c2b4 : word) = Some W_1c2b4.
Proof. vm_refl. Qed.
Lemma D_1c2b4 : decode_any W_1c2b4 = Some (OpImm ALU_AND 12 11 31, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1c2b8 : bv 32 := 0x00061a63.
Lemma F_1c2b8 : fetch_word Ubsan.M.loaded_segments (0x1c2b8 : word) = Some W_1c2b8.
Proof. vm_refl. Qed.
Lemma D_1c2b8 : decode_any W_1c2b8 = Some (Branch BC_NE 12 0 20, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1c2bc : bv 32 := 0xfffff637.
Lemma F_1c2bc : fetch_word Ubsan.M.loaded_segments (0x1c2bc : word) = Some W_1c2bc.
Proof. vm_refl. Qed.
Lemma D_1c2bc : decode_any W_1c2bc = Some (Lui 12 1048575, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1c2c0 : bv 32 := 0x00c5f633.
Lemma F_1c2c0 : fetch_word Ubsan.M.loaded_segments (0x1c2c0 : word) = Some W_1c2c0.
Proof. vm_refl. Qed.
Lemma D_1c2c0 : decode_any W_1c2c0 = Some (Op ALU_AND 12 11 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1c2c4 : bv 32 := 0xff060613.
Lemma F_1c2c4 : fetch_word Ubsan.M.loaded_segments (0x1c2c4 : word) = Some W_1c2c4.
Proof. vm_refl. Qed.
Lemma D_1c2c4 : decode_any W_1c2c4 = Some (OpImm ALU_ADD 12 12 4080, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1c2c8 : bv 32 := 0x0200006f.
Lemma F_1c2c8 : fetch_word Ubsan.M.loaded_segments (0x1c2c8 : word) = Some W_1c2c8.
Proof. vm_refl. Qed.
Lemma D_1c2c8 : decode_any W_1c2c8 = Some (Jal 0 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1c2cc : bv 32 := 0x0055d613.
Lemma F_1c2cc : fetch_word Ubsan.M.loaded_segments (0x1c2cc : word) = Some W_1c2cc.
Proof. vm_refl. Qed.
Lemma D_1c2cc : decode_any W_1c2cc = Some (ShiftImm ALU_SRL 12 11 5, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1c2d0 : bv 32 := 0xffff5717.
Lemma F_1c2d0 : fetch_word Ubsan.M.loaded_segments (0x1c2d0 : word) = Some W_1c2d0.
Proof. vm_refl. Qed.
Lemma D_1c2d0 : decode_any W_1c2d0 = Some (Auipc 14 1048565, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1c2d4 : bv 32 := 0x07e67613.
Lemma F_1c2d4 : fetch_word Ubsan.M.loaded_segments (0x1c2d4 : word) = Some W_1c2d4.
Proof. vm_refl. Qed.
Lemma D_1c2d4 : decode_any W_1c2d4 = Some (OpImm ALU_AND 12 12 126, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1c2d8 : bv 32 := 0xde870713.
Lemma F_1c2d8 : fetch_word Ubsan.M.loaded_segments (0x1c2d8 : word) = Some W_1c2d8.
Proof. vm_refl. Qed.
Lemma D_1c2d8 : decode_any W_1c2d8 = Some (OpImm ALU_ADD 14 14 3560, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1c2dc : bv 32 := 0x00c70633.
Lemma F_1c2dc : fetch_word Ubsan.M.loaded_segments (0x1c2dc : word) = Some W_1c2dc.
Proof. vm_refl. Qed.
Lemma D_1c2dc : decode_any W_1c2dc = Some (Op ALU_ADD 12 14 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1c2e0 : bv 32 := 0x00065603.
Lemma F_1c2e0 : fetch_word Ubsan.M.loaded_segments (0x1c2e0 : word) = Some W_1c2e0.
Proof. vm_refl. Qed.
Lemma D_1c2e0 : decode_any W_1c2e0 = Some (Load SZ2 false 12 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1c2e4 : bv 32 := 0x00461613.
Lemma F_1c2e4 : fetch_word Ubsan.M.loaded_segments (0x1c2e4 : word) = Some W_1c2e4.
Proof. vm_refl. Qed.
Lemma D_1c2e4 : decode_any W_1c2e4 = Some (ShiftImm ALU_SLL 12 12 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1c2e8 : bv 32 := 0x01053703.
Lemma F_1c2e8 : fetch_word Ubsan.M.loaded_segments (0x1c2e8 : word) = Some W_1c2e8.
Proof. vm_refl. Qed.
Lemma D_1c2e8 : decode_any W_1c2e8 = Some (Load SZ8 true 14 10 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1c2ec : bv 32 := 0x028607b3.
Lemma F_1c2ec : fetch_word Ubsan.M.loaded_segments (0x1c2ec : word) = Some W_1c2ec.
Proof. vm_refl. Qed.
Lemma D_1c2ec : decode_any W_1c2ec = Some (Mul M_MUL 15 12 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1c2f0 : bv 32 := 0x0a000813.
Lemma F_1c2f0 : fetch_word Ubsan.M.loaded_segments (0x1c2f0 : word) = Some W_1c2f0.
Proof. vm_refl. Qed.
Lemma D_1c2f0 : decode_any W_1c2f0 = Some (OpImm ALU_ADD 16 0 160, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1c2f4 : bv 32 := 0x00c70633.
Lemma F_1c2f4 : fetch_word Ubsan.M.loaded_segments (0x1c2f4 : word) = Some W_1c2f4.
Proof. vm_refl. Qed.
Lemma D_1c2f4 : decode_any W_1c2f4 = Some (Op ALU_ADD 12 14 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_1c2f8 : bv 32 := 0x00f607b3.
Lemma F_1c2f8 : fetch_word Ubsan.M.loaded_segments (0x1c2f8 : word) = Some W_1c2f8.
Proof. vm_refl. Qed.
Lemma D_1c2f8 : decode_any W_1c2f8 = Some (Op ALU_ADD 15 12 15, 4%Z).
Proof. vm_refl. Qed.
