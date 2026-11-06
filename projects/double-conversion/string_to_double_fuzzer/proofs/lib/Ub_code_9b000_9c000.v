(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib Require Import ImgU.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Abbreviation USEGS := ImgU.M.loaded_segments.
Open Scope bv_scope.

(* [comment removed for export] *)
Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

(* [comment removed for export] *)
Definition W_9b570 : bv 32 := 0x04b51463.
Lemma F_9b570 : fetch_word USEGS (0x9b570 : word) = Some W_9b570.
Proof. vm_refl. Qed.
Lemma D_9b570 : decode_any W_9b570 = Some (Branch BC_NE 10 11 72, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9b574 : bv 32 := 0x00048513.
Lemma F_9b574 : fetch_word USEGS (0x9b574 : word) = Some W_9b574.
Proof. vm_refl. Qed.
Lemma D_9b574 : decode_any W_9b574 = Some (OpImm ALU_ADD 10 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9b578 : bv 32 := 0x06813083.
Lemma F_9b578 : fetch_word USEGS (0x9b578 : word) = Some W_9b578.
Proof. vm_refl. Qed.
Lemma D_9b578 : decode_any W_9b578 = Some (Load SZ8 true 1 2 104, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9b57c : bv 32 := 0x06013403.
Lemma F_9b57c : fetch_word USEGS (0x9b57c : word) = Some W_9b57c.
Proof. vm_refl. Qed.
Lemma D_9b57c : decode_any W_9b57c = Some (Load SZ8 true 8 2 96, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9b580 : bv 32 := 0x05813483.
Lemma F_9b580 : fetch_word USEGS (0x9b580 : word) = Some W_9b580.
Proof. vm_refl. Qed.
Lemma D_9b580 : decode_any W_9b580 = Some (Load SZ8 true 9 2 88, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9b584 : bv 32 := 0x05013903.
Lemma F_9b584 : fetch_word USEGS (0x9b584 : word) = Some W_9b584.
Proof. vm_refl. Qed.
Lemma D_9b584 : decode_any W_9b584 = Some (Load SZ8 true 18 2 80, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9b588 : bv 32 := 0x04813983.
Lemma F_9b588 : fetch_word USEGS (0x9b588 : word) = Some W_9b588.
Proof. vm_refl. Qed.
Lemma D_9b588 : decode_any W_9b588 = Some (Load SZ8 true 19 2 72, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9b58c : bv 32 := 0x04013a03.
Lemma F_9b58c : fetch_word USEGS (0x9b58c : word) = Some W_9b58c.
Proof. vm_refl. Qed.
Lemma D_9b58c : decode_any W_9b58c = Some (Load SZ8 true 20 2 64, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9b590 : bv 32 := 0x03813a83.
Lemma F_9b590 : fetch_word USEGS (0x9b590 : word) = Some W_9b590.
Proof. vm_refl. Qed.
Lemma D_9b590 : decode_any W_9b590 = Some (Load SZ8 true 21 2 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9b5e4 : bv 32 := 0xfff58593.
Lemma F_9b5e4 : fetch_word USEGS (0x9b5e4 : word) = Some W_9b5e4.
Proof. vm_refl. Qed.
Lemma D_9b5e4 : decode_any W_9b5e4 = Some (OpImm ALU_ADD 11 11 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9b5e8 : bv 32 := 0x00a5e533.
Lemma F_9b5e8 : fetch_word USEGS (0x9b5e8 : word) = Some W_9b5e8.
Proof. vm_refl. Qed.
Lemma D_9b5e8 : decode_any W_9b5e8 = Some (Op ALU_OR 10 11 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9b5ec : bv 32 := 0x00008067.
Lemma F_9b5ec : fetch_word USEGS (0x9b5ec : word) = Some W_9b5ec.
Proof. vm_refl. Qed.
Lemma D_9b5ec : decode_any W_9b5ec = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9b5f0 : bv 32 := 0x00050613.
Lemma F_9b5f0 : fetch_word USEGS (0x9b5f0 : word) = Some W_9b5f0.
Proof. vm_refl. Qed.
Lemma D_9b5f0 : decode_any W_9b5f0 = Some (OpImm ALU_ADD 12 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9b5f4 : bv 32 := 0xfff7f517.
Lemma F_9b5f4 : fetch_word USEGS (0x9b5f4 : word) = Some W_9b5f4.
Proof. vm_refl. Qed.
Lemma D_9b5f4 : decode_any W_9b5f4 = Some (Auipc 10 1048447, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9b600 : bv 32 := 0x00800693.
Lemma F_9b600 : fetch_word USEGS (0x9b600 : word) = Some W_9b600.
Proof. vm_refl. Qed.
Lemma D_9b600 : decode_any W_9b600 = Some (OpImm ALU_ADD 13 0 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9b604 : bv 32 := 0x00000513.
Lemma F_9b604 : fetch_word USEGS (0x9b604 : word) = Some W_9b604.
Proof. vm_refl. Qed.
Lemma D_9b604 : decode_any W_9b604 = Some (OpImm ALU_ADD 10 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9b608 : bv 32 := 0x00000073.
Lemma F_9b608 : fetch_word USEGS (0x9b608 : word) = Some W_9b608.
Proof. vm_refl. Qed.
Lemma D_9b608 : decode_any W_9b608 = Some (Ecall, 4%Z).
Proof. vm_refl. Qed.
Lemma E_9b608 : is_ecall W_9b608 = true.
Proof. reflexivity. Qed.

(* [comment removed for export] *)
Definition W_9b60c : bv 32 := 0x00008067.
Lemma F_9b60c : fetch_word USEGS (0x9b60c : word) = Some W_9b60c.
Proof. vm_refl. Qed.
Lemma D_9b60c : decode_any W_9b60c = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9b610 : bv 32 := 0x00050613.
Lemma F_9b610 : fetch_word USEGS (0x9b610 : word) = Some W_9b610.
Proof. vm_refl. Qed.
Lemma D_9b610 : decode_any W_9b610 = Some (OpImm ALU_ADD 12 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9b614 : bv 32 := 0xfff7f517.
Lemma F_9b614 : fetch_word USEGS (0x9b614 : word) = Some W_9b614.
Proof. vm_refl. Qed.
Lemma D_9b614 : decode_any W_9b614 = Some (Auipc 10 1048447, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9b618 : bv 32 := 0x08700893.
Lemma F_9b618 : fetch_word USEGS (0x9b618 : word) = Some W_9b618.
Proof. vm_refl. Qed.
Lemma D_9b618 : decode_any W_9b618 = Some (OpImm ALU_ADD 17 0 135, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9b61c : bv 32 := 0x70450593.
Lemma F_9b61c : fetch_word USEGS (0x9b61c : word) = Some W_9b61c.
Proof. vm_refl. Qed.
Lemma D_9b61c : decode_any W_9b61c = Some (OpImm ALU_ADD 11 10 1796, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9b620 : bv 32 := 0x00800693.
Lemma F_9b620 : fetch_word USEGS (0x9b620 : word) = Some W_9b620.
Proof. vm_refl. Qed.
Lemma D_9b620 : decode_any W_9b620 = Some (OpImm ALU_ADD 13 0 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9b624 : bv 32 := 0x00000513.
Lemma F_9b624 : fetch_word USEGS (0x9b624 : word) = Some W_9b624.
Proof. vm_refl. Qed.
Lemma D_9b624 : decode_any W_9b624 = Some (OpImm ALU_ADD 10 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9b628 : bv 32 := 0x00000073.
Lemma F_9b628 : fetch_word USEGS (0x9b628 : word) = Some W_9b628.
Proof. vm_refl. Qed.
Lemma D_9b628 : decode_any W_9b628 = Some (Ecall, 4%Z).
Proof. vm_refl. Qed.
Lemma E_9b628 : is_ecall W_9b628 = true.
Proof. reflexivity. Qed.

(* [comment removed for export] *)
Definition W_9b640 : bv 32 := 0x00000613.
Lemma F_9b640 : fetch_word USEGS (0x9b640 : word) = Some W_9b640.
Proof. vm_refl. Qed.
Lemma D_9b640 : decode_any W_9b640 = Some (OpImm ALU_ADD 12 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9b644 : bv 32 := 0x00000073.
Lemma F_9b644 : fetch_word USEGS (0x9b644 : word) = Some W_9b644.
Proof. vm_refl. Qed.
Lemma D_9b644 : decode_any W_9b644 = Some (Ecall, 4%Z).
Proof. vm_refl. Qed.
Lemma E_9b644 : is_ecall W_9b644 = true.
Proof. reflexivity. Qed.

(* [comment removed for export] *)
Definition W_9b648 : bv 32 := 0x00008067.
Lemma F_9b648 : fetch_word USEGS (0x9b648 : word) = Some W_9b648.
Proof. vm_refl. Qed.
Lemma D_9b648 : decode_any W_9b648 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9b64c : bv 32 := 0xf6010113.
Lemma F_9b64c : fetch_word USEGS (0x9b64c : word) = Some W_9b64c.
Proof. vm_refl. Qed.
Lemma D_9b64c : decode_any W_9b64c = Some (OpImm ALU_ADD 2 2 3936, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9b650 : bv 32 := 0x08113c23.
Lemma F_9b650 : fetch_word USEGS (0x9b650 : word) = Some W_9b650.
Proof. vm_refl. Qed.
Lemma D_9b650 : decode_any W_9b650 = Some (Store SZ8 2 1 152, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9b65c : bv 32 := 0x00050413.
Lemma F_9b65c : fetch_word USEGS (0x9b65c : word) = Some W_9b65c.
Proof. vm_refl. Qed.
Lemma D_9b65c : decode_any W_9b65c = Some (OpImm ALU_ADD 8 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9b660 : bv 32 := 0x00017517.
Lemma F_9b660 : fetch_word USEGS (0x9b660 : word) = Some W_9b660.
Proof. vm_refl. Qed.
Lemma D_9b660 : decode_any W_9b660 = Some (Auipc 10 23, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9b664 : bv 32 := 0xc4853483.
Lemma F_9b664 : fetch_word USEGS (0x9b664 : word) = Some W_9b664.
Proof. vm_refl. Qed.
Lemma D_9b664 : decode_any W_9b664 = Some (Load SZ8 true 9 10 3144, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9b67c : bv 32 := 0xf5852503.
Lemma F_9b67c : fetch_word USEGS (0x9b67c : word) = Some W_9b67c.
Proof. vm_refl. Qed.
Lemma D_9b67c : decode_any W_9b67c = Some (Load SZ4 true 10 10 3928, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9b680 : bv 32 := 0x08200893.
Lemma F_9b680 : fetch_word USEGS (0x9b680 : word) = Some W_9b680.
Proof. vm_refl. Qed.
Lemma D_9b680 : decode_any W_9b680 = Some (OpImm ALU_ADD 17 0 130, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9b684 : bv 32 := 0x00040593.
Lemma F_9b684 : fetch_word USEGS (0x9b684 : word) = Some W_9b684.
Proof. vm_refl. Qed.
Lemma D_9b684 : decode_any W_9b684 = Some (OpImm ALU_ADD 11 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9b704 : bv 32 := 0xe7853503.
Lemma F_9b704 : fetch_word USEGS (0x9b704 : word) = Some W_9b704.
Proof. vm_refl. Qed.
Lemma D_9b704 : decode_any W_9b704 = Some (Load SZ8 true 10 10 3704, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9b708 : bv 32 := 0xfbdff0ef.
Lemma F_9b708 : fetch_word USEGS (0x9b708 : word) = Some W_9b708.
Proof. vm_refl. Qed.
Lemma D_9b708 : decode_any W_9b708 = Some (Jal 1 2097084, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9b70c : bv 32 := 0x00050413.
Lemma F_9b70c : fetch_word USEGS (0x9b70c : word) = Some W_9b70c.
Proof. vm_refl. Qed.
Lemma D_9b70c : decode_any W_9b70c = Some (OpImm ALU_ADD 8 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9b710 : bv 32 := 0x0940006f.
Lemma F_9b710 : fetch_word USEGS (0x9b710 : word) = Some W_9b710.
Proof. vm_refl. Qed.
Lemma D_9b710 : decode_any W_9b710 = Some (Jal 0 148, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9b904 : bv 32 := 0x00000693.
Lemma F_9b904 : fetch_word USEGS (0x9b904 : word) = Some W_9b904.
Proof. vm_refl. Qed.
Lemma D_9b904 : decode_any W_9b904 = Some (OpImm ALU_ADD 13 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9b908 : bv 32 := 0x00000073.
Lemma F_9b908 : fetch_word USEGS (0x9b908 : word) = Some W_9b908.
Proof. vm_refl. Qed.
Lemma D_9b908 : decode_any W_9b908 = Some (Ecall, 4%Z).
Proof. vm_refl. Qed.
Lemma E_9b908 : is_ecall W_9b908 = true.
Proof. reflexivity. Qed.

(* [comment removed for export] *)
Definition W_9b90c : bv 32 := 0xfa6510e3.
Lemma F_9b90c : fetch_word USEGS (0x9b90c : word) = Some W_9b90c.
Proof. vm_refl. Qed.
Lemma D_9b90c : decode_any W_9b90c = Some (Branch BC_NE 10 6 8096, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9b910 : bv 32 := 0x06200893.
Lemma F_9b910 : fetch_word USEGS (0x9b910 : word) = Some W_9b910.
Proof. vm_refl. Qed.
Lemma D_9b910 : decode_any W_9b910 = Some (OpImm ALU_ADD 17 0 98, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9b914 : bv 32 := 0x00070513.
Lemma F_9b914 : fetch_word USEGS (0x9b914 : word) = Some W_9b914.
Proof. vm_refl. Qed.
Lemma D_9b914 : decode_any W_9b914 = Some (OpImm ALU_ADD 10 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9b918 : bv 32 := 0x00000593.
Lemma F_9b918 : fetch_word USEGS (0x9b918 : word) = Some W_9b918.
Proof. vm_refl. Qed.
Lemma D_9b918 : decode_any W_9b918 = Some (OpImm ALU_ADD 11 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9b91c : bv 32 := 0x00000693.
Lemma F_9b91c : fetch_word USEGS (0x9b91c : word) = Some W_9b91c.
Proof. vm_refl. Qed.
Lemma D_9b91c : decode_any W_9b91c = Some (OpImm ALU_ADD 13 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9b920 : bv 32 := 0x00000073.
Lemma F_9b920 : fetch_word USEGS (0x9b920 : word) = Some W_9b920.
Proof. vm_refl. Qed.
Lemma D_9b920 : decode_any W_9b920 = Some (Ecall, 4%Z).
Proof. vm_refl. Qed.
Lemma E_9b920 : is_ecall W_9b920 = true.
Proof. reflexivity. Qed.

(* [comment removed for export] *)
Definition W_9b924 : bv 32 := 0xf89ff06f.
Lemma F_9b924 : fetch_word USEGS (0x9b924 : word) = Some W_9b924.
Proof. vm_refl. Qed.
Lemma D_9b924 : decode_any W_9b924 = Some (Jal 0 2097032, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9b928 : bv 32 := 0x00100513.
Lemma F_9b928 : fetch_word USEGS (0x9b928 : word) = Some W_9b928.
Proof. vm_refl. Qed.
Lemma D_9b928 : decode_any W_9b928 = Some (OpImm ALU_ADD 10 0 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9b92c : bv 32 := 0x00008067.
Lemma F_9b92c : fetch_word USEGS (0x9b92c : word) = Some W_9b92c.
Proof. vm_refl. Qed.
Lemma D_9b92c : decode_any W_9b92c = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9b930 : bv 32 := 0x00000593.
Lemma F_9b930 : fetch_word USEGS (0x9b930 : word) = Some W_9b930.
Proof. vm_refl. Qed.
Lemma D_9b930 : decode_any W_9b930 = Some (OpImm ALU_ADD 11 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9ba04 : bv 32 := 0xf586a683.
Lemma F_9ba04 : fetch_word USEGS (0x9ba04 : word) = Some W_9ba04.
Proof. vm_refl. Qed.
Lemma D_9ba04 : decode_any W_9ba04 = Some (Load SZ4 true 13 13 3928, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9ba34 : bv 32 := 0x00a68023.
Lemma F_9ba34 : fetch_word USEGS (0x9ba34 : word) = Some W_9ba34.
Proof. vm_refl. Qed.
Lemma D_9ba34 : decode_any W_9ba34 = Some (Store SZ1 13 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9ba38 : bv 32 := 0x00060513.
Lemma F_9ba38 : fetch_word USEGS (0x9ba38 : word) = Some W_9ba38.
Proof. vm_refl. Qed.
Lemma D_9ba38 : decode_any W_9ba38 = Some (OpImm ALU_ADD 10 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9ba3c : bv 32 := 0x00008067.
Lemma F_9ba3c : fetch_word USEGS (0x9ba3c : word) = Some W_9ba3c.
Proof. vm_refl. Qed.
Lemma D_9ba3c : decode_any W_9ba3c = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9ba40 : bv 32 := 0x0100006f.
Lemma F_9ba40 : fetch_word USEGS (0x9ba40 : word) = Some W_9ba40.
Proof. vm_refl. Qed.
Lemma D_9ba40 : decode_any W_9ba40 = Some (Jal 0 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9ba44 : bv 32 := 0x00058513.
Lemma F_9ba44 : fetch_word USEGS (0x9ba44 : word) = Some W_9ba44.
Proof. vm_refl. Qed.
Lemma D_9ba44 : decode_any W_9ba44 = Some (OpImm ALU_ADD 10 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9ba48 : bv 32 := 0x00060593.
Lemma F_9ba48 : fetch_word USEGS (0x9ba48 : word) = Some W_9ba48.
Proof. vm_refl. Qed.
Lemma D_9ba48 : decode_any W_9ba48 = Some (OpImm ALU_ADD 11 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9ba4c : bv 32 := 0x0fc0006f.
Lemma F_9ba4c : fetch_word USEGS (0x9ba4c : word) = Some W_9ba4c.
Proof. vm_refl. Qed.
Lemma D_9ba4c : decode_any W_9ba4c = Some (Jal 0 252, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9ba50 : bv 32 := 0xfe010113.
Lemma F_9ba50 : fetch_word USEGS (0x9ba50 : word) = Some W_9ba50.
Proof. vm_refl. Qed.
Lemma D_9ba50 : decode_any W_9ba50 = Some (OpImm ALU_ADD 2 2 4064, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9ba54 : bv 32 := 0x00113c23.
Lemma F_9ba54 : fetch_word USEGS (0x9ba54 : word) = Some W_9ba54.
Proof. vm_refl. Qed.
Lemma D_9ba54 : decode_any W_9ba54 = Some (Store SZ8 2 1 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9ba58 : bv 32 := 0x00813823.
Lemma F_9ba58 : fetch_word USEGS (0x9ba58 : word) = Some W_9ba58.
Proof. vm_refl. Qed.
Lemma D_9ba58 : decode_any W_9ba58 = Some (Store SZ8 2 8 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9ba5c : bv 32 := 0x00913423.
Lemma F_9ba5c : fetch_word USEGS (0x9ba5c : word) = Some W_9ba5c.
Proof. vm_refl. Qed.
Lemma D_9ba5c : decode_any W_9ba5c = Some (Store SZ8 2 9 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9ba60 : bv 32 := 0x01213023.
Lemma F_9ba60 : fetch_word USEGS (0x9ba60 : word) = Some W_9ba60.
Proof. vm_refl. Qed.
Lemma D_9ba60 : decode_any W_9ba60 = Some (Store SZ8 2 18 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9ba64 : bv 32 := 0x00058493.
Lemma F_9ba64 : fetch_word USEGS (0x9ba64 : word) = Some W_9ba64.
Proof. vm_refl. Qed.
Lemma D_9ba64 : decode_any W_9ba64 = Some (OpImm ALU_ADD 9 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9ba68 : bv 32 := 0x00000593.
Lemma F_9ba68 : fetch_word USEGS (0x9ba68 : word) = Some W_9ba68.
Proof. vm_refl. Qed.
Lemma D_9ba68 : decode_any W_9ba68 = Some (OpImm ALU_ADD 11 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9ba6c : bv 32 := 0x08c48413.
Lemma F_9ba6c : fetch_word USEGS (0x9ba6c : word) = Some W_9ba6c.
Proof. vm_refl. Qed.
Lemma D_9ba6c : decode_any W_9ba6c = Some (OpImm ALU_ADD 8 9 140, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9ba70 : bv 32 := 0x40000637.
Lemma F_9ba70 : fetch_word USEGS (0x9ba70 : word) = Some W_9ba70.
Proof. vm_refl. Qed.
Lemma D_9ba70 : decode_any W_9ba70 = Some (Lui 12 262144, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9ba74 : bv 32 := 0xfff6061b.
Lemma F_9ba74 : fetch_word USEGS (0x9ba74 : word) = Some W_9ba74.
Proof. vm_refl. Qed.
Lemma D_9ba74 : decode_any W_9ba74 = Some (OpImm32 12 12 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9ba78 : bv 32 := 0x160426af.
Lemma F_9ba78 : fetch_word USEGS (0x9ba78 : word) = Some W_9ba78.
Proof. vm_refl. Qed.
Lemma D_9ba78 : decode_any W_9ba78 = Some (Lr AW true true 13 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9ba7c : bv 32 := 0x00b69663.
Lemma F_9ba7c : fetch_word USEGS (0x9ba7c : word) = Some W_9ba7c.
Proof. vm_refl. Qed.
Lemma D_9ba7c : decode_any W_9ba7c = Some (Branch BC_NE 13 11 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9ba80 : bv 32 := 0x1ec4272f.
Lemma F_9ba80 : fetch_word USEGS (0x9ba80 : word) = Some W_9ba80.
Proof. vm_refl. Qed.
Lemma D_9ba80 : decode_any W_9ba80 = Some (Sc AW true true 14 8 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9ba84 : bv 32 := 0xfe071ae3.
Lemma F_9ba84 : fetch_word USEGS (0x9ba84 : word) = Some W_9ba84.
Proof. vm_refl. Qed.
Lemma D_9ba84 : decode_any W_9ba84 = Some (Branch BC_NE 14 0 8180, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9ba88 : bv 32 := 0x0006869b.
Lemma F_9ba88 : fetch_word USEGS (0x9ba88 : word) = Some W_9ba88.
Proof. vm_refl. Qed.
Lemma D_9ba88 : decode_any W_9ba88 = Some (OpImm32 13 13 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9ba8c : bv 32 := 0x00050913.
Lemma F_9ba8c : fetch_word USEGS (0x9ba8c : word) = Some W_9ba8c.
Proof. vm_refl. Qed.
Lemma D_9ba8c : decode_any W_9ba8c = Some (OpImm ALU_ADD 18 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9ba90 : bv 32 := 0x00068663.
Lemma F_9ba90 : fetch_word USEGS (0x9ba90 : word) = Some W_9ba90.
Proof. vm_refl. Qed.
Lemma D_9ba90 : decode_any W_9ba90 = Some (Branch BC_EQ 13 0 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9ba94 : bv 32 := 0x00048513.
Lemma F_9ba94 : fetch_word USEGS (0x9ba94 : word) = Some W_9ba94.
Proof. vm_refl. Qed.
Lemma D_9ba94 : decode_any W_9ba94 = Some (OpImm ALU_ADD 10 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9ba98 : bv 32 := 0xd9dff0ef.
Lemma F_9ba98 : fetch_word USEGS (0x9ba98 : word) = Some W_9ba98.
Proof. vm_refl. Qed.
Lemma D_9ba98 : decode_any W_9ba98 = Some (Jal 1 2096540, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9ba9c : bv 32 := 0x0904a503.
Lemma F_9ba9c : fetch_word USEGS (0x9ba9c : word) = Some W_9ba9c.
Proof. vm_refl. Qed.
Lemma D_9ba9c : decode_any W_9ba9c = Some (Load SZ4 true 10 9 144, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9baa0 : bv 32 := 0x0ff97693.
Lemma F_9baa0 : fetch_word USEGS (0x9baa0 : word) = Some W_9baa0.
Proof. vm_refl. Qed.
Lemma D_9baa0 : decode_any W_9baa0 = Some (OpImm ALU_AND 13 18 255, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9baa4 : bv 32 := 0x02a68063.
Lemma F_9baa4 : fetch_word USEGS (0x9baa4 : word) = Some W_9baa4.
Proof. vm_refl. Qed.
Lemma D_9baa4 : decode_any W_9baa4 = Some (Branch BC_EQ 13 10 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9baa8 : bv 32 := 0x0204b583.
Lemma F_9baa8 : fetch_word USEGS (0x9baa8 : word) = Some W_9baa8.
Proof. vm_refl. Qed.
Lemma D_9baa8 : decode_any W_9baa8 = Some (Load SZ8 true 11 9 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9baac : bv 32 := 0x0284b503.
Lemma F_9baac : fetch_word USEGS (0x9baac : word) = Some W_9baac.
Proof. vm_refl. Qed.
Lemma D_9baac : decode_any W_9baac = Some (Load SZ8 true 10 9 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9bab0 : bv 32 := 0x00b50a63.
Lemma F_9bab0 : fetch_word USEGS (0x9bab0 : word) = Some W_9bab0.
Proof. vm_refl. Qed.
Lemma D_9bab0 : decode_any W_9bab0 = Some (Branch BC_EQ 10 11 20, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9bab4 : bv 32 := 0x00150593.
Lemma F_9bab4 : fetch_word USEGS (0x9bab4 : word) = Some W_9bab4.
Proof. vm_refl. Qed.
Lemma D_9bab4 : decode_any W_9bab4 = Some (OpImm ALU_ADD 11 10 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9bab8 : bv 32 := 0x02b4b423.
Lemma F_9bab8 : fetch_word USEGS (0x9bab8 : word) = Some W_9bab8.
Proof. vm_refl. Qed.
Lemma D_9bab8 : decode_any W_9bab8 = Some (Store SZ8 9 11 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9babc : bv 32 := 0x01250023.
Lemma F_9babc : fetch_word USEGS (0x9babc : word) = Some W_9babc.
Proof. vm_refl. Qed.
Lemma D_9babc : decode_any W_9babc = Some (Store SZ1 10 18 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9bac0 : bv 32 := 0x0140006f.
Lemma F_9bac0 : fetch_word USEGS (0x9bac0 : word) = Some W_9bac0.
Proof. vm_refl. Qed.
Lemma D_9bac0 : decode_any W_9bac0 = Some (Jal 0 20, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9bac4 : bv 32 := 0x00048513.
Lemma F_9bac4 : fetch_word USEGS (0x9bac4 : word) = Some W_9bac4.
Proof. vm_refl. Qed.
Lemma D_9bac4 : decode_any W_9bac4 = Some (OpImm ALU_ADD 10 9 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9bac8 : bv 32 := 0x00068593.
Lemma F_9bac8 : fetch_word USEGS (0x9bac8 : word) = Some W_9bac8.
Proof. vm_refl. Qed.
Lemma D_9bac8 : decode_any W_9bac8 = Some (OpImm ALU_ADD 11 13 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9bacc : bv 32 := 0x07c000ef.
Lemma F_9bacc : fetch_word USEGS (0x9bacc : word) = Some W_9bacc.
Proof. vm_refl. Qed.
Lemma D_9bacc : decode_any W_9bacc = Some (Jal 1 124, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9bad0 : bv 32 := 0x00050693.
Lemma F_9bad0 : fetch_word USEGS (0x9bad0 : word) = Some W_9bad0.
Proof. vm_refl. Qed.
Lemma D_9bad0 : decode_any W_9bad0 = Some (OpImm ALU_ADD 13 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9bad4 : bv 32 := 0x00000513.
Lemma F_9bad4 : fetch_word USEGS (0x9bad4 : word) = Some W_9bad4.
Proof. vm_refl. Qed.
Lemma D_9bad4 : decode_any W_9bad4 = Some (OpImm ALU_ADD 10 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9bad8 : bv 32 := 0x00042583.
Lemma F_9bad8 : fetch_word USEGS (0x9bad8 : word) = Some W_9bad8.
Proof. vm_refl. Qed.
Lemma D_9bad8 : decode_any W_9bad8 = Some (Load SZ4 true 11 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9badc : bv 32 := 0x1604262f.
Lemma F_9badc : fetch_word USEGS (0x9badc : word) = Some W_9badc.
Proof. vm_refl. Qed.
Lemma D_9badc : decode_any W_9badc = Some (Lr AW true true 12 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9bae0 : bv 32 := 0x00b61663.
Lemma F_9bae0 : fetch_word USEGS (0x9bae0 : word) = Some W_9bae0.
Proof. vm_refl. Qed.
Lemma D_9bae0 : decode_any W_9bae0 = Some (Branch BC_NE 12 11 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9bae4 : bv 32 := 0x1ea4272f.
Lemma F_9bae4 : fetch_word USEGS (0x9bae4 : word) = Some W_9bae4.
Proof. vm_refl. Qed.
Lemma D_9bae4 : decode_any W_9bae4 = Some (Sc AW true true 14 8 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9bae8 : bv 32 := 0xfe071ae3.
Lemma F_9bae8 : fetch_word USEGS (0x9bae8 : word) = Some W_9bae8.
Proof. vm_refl. Qed.
Lemma D_9bae8 : decode_any W_9bae8 = Some (Branch BC_NE 14 0 8180, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9baec : bv 32 := 0x0006061b.
Lemma F_9baec : fetch_word USEGS (0x9baec : word) = Some W_9baec.
Proof. vm_refl. Qed.
Lemma D_9baec : decode_any W_9baec = Some (OpImm32 12 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9baf0 : bv 32 := 0xfeb614e3.
Lemma F_9baf0 : fetch_word USEGS (0x9baf0 : word) = Some W_9baf0.
Proof. vm_refl. Qed.
Lemma D_9baf0 : decode_any W_9baf0 = Some (Branch BC_NE 12 11 8168, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9baf4 : bv 32 := 0x02159593.
Lemma F_9baf4 : fetch_word USEGS (0x9baf4 : word) = Some W_9baf4.
Proof. vm_refl. Qed.
Lemma D_9baf4 : decode_any W_9baf4 = Some (ShiftImm ALU_SLL 11 11 33, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9baf8 : bv 32 := 0x0205da63.
Lemma F_9baf8 : fetch_word USEGS (0x9baf8 : word) = Some W_9baf8.
Proof. vm_refl. Qed.
Lemma D_9baf8 : decode_any W_9baf8 = Some (Branch BC_GE 11 0 52, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9bafc : bv 32 := 0x06200893.
Lemma F_9bafc : fetch_word USEGS (0x9bafc : word) = Some W_9bafc.
Proof. vm_refl. Qed.
Lemma D_9bafc : decode_any W_9bafc = Some (OpImm ALU_ADD 17 0 98, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9bb00 : bv 32 := 0x08100593.
Lemma F_9bb00 : fetch_word USEGS (0x9bb00 : word) = Some W_9bb00.
Proof. vm_refl. Qed.
Lemma D_9bb00 : decode_any W_9bb00 = Some (OpImm ALU_ADD 11 0 129, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9bb04 : bv 32 := 0x00100613.
Lemma F_9bb04 : fetch_word USEGS (0x9bb04 : word) = Some W_9bb04.
Proof. vm_refl. Qed.
Lemma D_9bb04 : decode_any W_9bb04 = Some (OpImm ALU_ADD 12 0 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9bb08 : bv 32 := 0xfda00713.
Lemma F_9bb08 : fetch_word USEGS (0x9bb08 : word) = Some W_9bb08.
Proof. vm_refl. Qed.
Lemma D_9bb08 : decode_any W_9bb08 = Some (OpImm ALU_ADD 14 0 4058, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9bb0c : bv 32 := 0x00040513.
Lemma F_9bb0c : fetch_word USEGS (0x9bb0c : word) = Some W_9bb0c.
Proof. vm_refl. Qed.
Lemma D_9bb0c : decode_any W_9bb0c = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9bb10 : bv 32 := 0x00000073.
Lemma F_9bb10 : fetch_word USEGS (0x9bb10 : word) = Some W_9bb10.
Proof. vm_refl. Qed.
Lemma D_9bb10 : decode_any W_9bb10 = Some (Ecall, 4%Z).
Proof. vm_refl. Qed.
Lemma E_9bb10 : is_ecall W_9bb10 = true.
Proof. reflexivity. Qed.

(* [comment removed for export] *)
Definition W_9bb14 : bv 32 := 0x00e51c63.
Lemma F_9bb14 : fetch_word USEGS (0x9bb14 : word) = Some W_9bb14.
Proof. vm_refl. Qed.
Lemma D_9bb14 : decode_any W_9bb14 = Some (Branch BC_NE 10 14 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9bb18 : bv 32 := 0x06200893.
Lemma F_9bb18 : fetch_word USEGS (0x9bb18 : word) = Some W_9bb18.
Proof. vm_refl. Qed.
Lemma D_9bb18 : decode_any W_9bb18 = Some (OpImm ALU_ADD 17 0 98, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9bb1c : bv 32 := 0x00100593.
Lemma F_9bb1c : fetch_word USEGS (0x9bb1c : word) = Some W_9bb1c.
Proof. vm_refl. Qed.
Lemma D_9bb1c : decode_any W_9bb1c = Some (OpImm ALU_ADD 11 0 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9bb20 : bv 32 := 0x00100613.
Lemma F_9bb20 : fetch_word USEGS (0x9bb20 : word) = Some W_9bb20.
Proof. vm_refl. Qed.
Lemma D_9bb20 : decode_any W_9bb20 = Some (OpImm ALU_ADD 12 0 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9bb24 : bv 32 := 0x00040513.
Lemma F_9bb24 : fetch_word USEGS (0x9bb24 : word) = Some W_9bb24.
Proof. vm_refl. Qed.
Lemma D_9bb24 : decode_any W_9bb24 = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9bb28 : bv 32 := 0x00000073.
Lemma F_9bb28 : fetch_word USEGS (0x9bb28 : word) = Some W_9bb28.
Proof. vm_refl. Qed.
Lemma D_9bb28 : decode_any W_9bb28 = Some (Ecall, 4%Z).
Proof. vm_refl. Qed.
Lemma E_9bb28 : is_ecall W_9bb28 = true.
Proof. reflexivity. Qed.

(* [comment removed for export] *)
Definition W_9bb2c : bv 32 := 0x00068513.
Lemma F_9bb2c : fetch_word USEGS (0x9bb2c : word) = Some W_9bb2c.
Proof. vm_refl. Qed.
Lemma D_9bb2c : decode_any W_9bb2c = Some (OpImm ALU_ADD 10 13 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9bb30 : bv 32 := 0x01813083.
Lemma F_9bb30 : fetch_word USEGS (0x9bb30 : word) = Some W_9bb30.
Proof. vm_refl. Qed.
Lemma D_9bb30 : decode_any W_9bb30 = Some (Load SZ8 true 1 2 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9bb34 : bv 32 := 0x01013403.
Lemma F_9bb34 : fetch_word USEGS (0x9bb34 : word) = Some W_9bb34.
Proof. vm_refl. Qed.
Lemma D_9bb34 : decode_any W_9bb34 = Some (Load SZ8 true 8 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9bb38 : bv 32 := 0x00813483.
Lemma F_9bb38 : fetch_word USEGS (0x9bb38 : word) = Some W_9bb38.
Proof. vm_refl. Qed.
Lemma D_9bb38 : decode_any W_9bb38 = Some (Load SZ8 true 9 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9bb3c : bv 32 := 0x00013903.
Lemma F_9bb3c : fetch_word USEGS (0x9bb3c : word) = Some W_9bb3c.
Proof. vm_refl. Qed.
Lemma D_9bb3c : decode_any W_9bb3c = Some (Load SZ8 true 18 2 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9bb40 : bv 32 := 0x02010113.
Lemma F_9bb40 : fetch_word USEGS (0x9bb40 : word) = Some W_9bb40.
Proof. vm_refl. Qed.
Lemma D_9bb40 : decode_any W_9bb40 = Some (OpImm ALU_ADD 2 2 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9bb44 : bv 32 := 0x00008067.
Lemma F_9bb44 : fetch_word USEGS (0x9bb44 : word) = Some W_9bb44.
Proof. vm_refl. Qed.
Lemma D_9bb44 : decode_any W_9bb44 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9bb48 : bv 32 := 0xfd010113.
Lemma F_9bb48 : fetch_word USEGS (0x9bb48 : word) = Some W_9bb48.
Proof. vm_refl. Qed.
Lemma D_9bb48 : decode_any W_9bb48 = Some (OpImm ALU_ADD 2 2 4048, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9bb4c : bv 32 := 0x02113423.
Lemma F_9bb4c : fetch_word USEGS (0x9bb4c : word) = Some W_9bb4c.
Proof. vm_refl. Qed.
Lemma D_9bb4c : decode_any W_9bb4c = Some (Store SZ8 2 1 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9bb50 : bv 32 := 0x02813023.
Lemma F_9bb50 : fetch_word USEGS (0x9bb50 : word) = Some W_9bb50.
Proof. vm_refl. Qed.
Lemma D_9bb50 : decode_any W_9bb50 = Some (Store SZ8 2 8 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9bb54 : bv 32 := 0x00913c23.
Lemma F_9bb54 : fetch_word USEGS (0x9bb54 : word) = Some W_9bb54.
Proof. vm_refl. Qed.
Lemma D_9bb54 : decode_any W_9bb54 = Some (Store SZ8 2 9 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9bb58 : bv 32 := 0x01213823.
Lemma F_9bb58 : fetch_word USEGS (0x9bb58 : word) = Some W_9bb58.
Proof. vm_refl. Qed.
Lemma D_9bb58 : decode_any W_9bb58 = Some (Store SZ8 2 18 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9bb5c : bv 32 := 0x00016617.
Lemma F_9bb5c : fetch_word USEGS (0x9bb5c : word) = Some W_9bb5c.
Proof. vm_refl. Qed.
Lemma D_9bb5c : decode_any W_9bb5c = Some (Auipc 12 22, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9bb60 : bv 32 := 0x74c63403.
Lemma F_9bb60 : fetch_word USEGS (0x9bb60 : word) = Some W_9bb60.
Proof. vm_refl. Qed.
Lemma D_9bb60 : decode_any W_9bb60 = Some (Load SZ8 true 8 12 1868, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9bb64 : bv 32 := 0x00043603.
Lemma F_9bb64 : fetch_word USEGS (0x9bb64 : word) = Some W_9bb64.
Proof. vm_refl. Qed.
Lemma D_9bb64 : decode_any W_9bb64 = Some (Load SZ8 true 12 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9bb68 : bv 32 := 0x00c13423.
Lemma F_9bb68 : fetch_word USEGS (0x9bb68 : word) = Some W_9bb68.
Proof. vm_refl. Qed.
Lemma D_9bb68 : decode_any W_9bb68 = Some (Store SZ8 2 12 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9bb6c : bv 32 := 0x02053683.
Lemma F_9bb6c : fetch_word USEGS (0x9bb6c : word) = Some W_9bb6c.
Proof. vm_refl. Qed.
Lemma D_9bb6c : decode_any W_9bb6c = Some (Load SZ8 true 13 10 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9bb70 : bv 32 := 0x00b103a3.
Lemma F_9bb70 : fetch_word USEGS (0x9bb70 : word) = Some W_9bb70.
Proof. vm_refl. Qed.
Lemma D_9bb70 : decode_any W_9bb70 = Some (Store SZ1 2 11 7, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9bb74 : bv 32 := 0x02068c63.
Lemma F_9bb74 : fetch_word USEGS (0x9bb74 : word) = Some W_9bb74.
Proof. vm_refl. Qed.
Lemma D_9bb74 : decode_any W_9bb74 = Some (Branch BC_EQ 13 0 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9bb78 : bv 32 := 0x02853603.
Lemma F_9bb78 : fetch_word USEGS (0x9bb78 : word) = Some W_9bb78.
Proof. vm_refl. Qed.
Lemma D_9bb78 : decode_any W_9bb78 = Some (Load SZ8 true 12 10 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9bb7c : bv 32 := 0x00d60863.
Lemma F_9bb7c : fetch_word USEGS (0x9bb7c : word) = Some W_9bb7c.
Proof. vm_refl. Qed.
Lemma D_9bb7c : decode_any W_9bb7c = Some (Branch BC_EQ 12 13 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9bb80 : bv 32 := 0x09052703.
Lemma F_9bb80 : fetch_word USEGS (0x9bb80 : word) = Some W_9bb80.
Proof. vm_refl. Qed.
Lemma D_9bb80 : decode_any W_9bb80 = Some (Load SZ4 true 14 10 144, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9bb84 : bv 32 := 0x0ff5f793.
Lemma F_9bb84 : fetch_word USEGS (0x9bb84 : word) = Some W_9bb84.
Proof. vm_refl. Qed.
Lemma D_9bb84 : decode_any W_9bb84 = Some (OpImm ALU_AND 15 11 255, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9bb88 : bv 32 := 0x02f71e63.
Lemma F_9bb88 : fetch_word USEGS (0x9bb88 : word) = Some W_9bb88.
Proof. vm_refl. Qed.
Lemma D_9bb88 : decode_any W_9bb88 = Some (Branch BC_NE 14 15 60, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9bc68 : bv 32 := 0xff010113.
Lemma F_9bc68 : fetch_word USEGS (0x9bc68 : word) = Some W_9bc68.
Proof. vm_refl. Qed.
Lemma D_9bc68 : decode_any W_9bc68 = Some (OpImm ALU_ADD 2 2 4080, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9bc6c : bv 32 := 0x00113423.
Lemma F_9bc6c : fetch_word USEGS (0x9bc6c : word) = Some W_9bc6c.
Proof. vm_refl. Qed.
Lemma D_9bc6c : decode_any W_9bc6c = Some (Store SZ8 2 1 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9bc70 : bv 32 := 0x00813023.
Lemma F_9bc70 : fetch_word USEGS (0x9bc70 : word) = Some W_9bc70.
Proof. vm_refl. Qed.
Lemma D_9bc70 : decode_any W_9bc70 = Some (Store SZ8 2 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9bc74 : bv 32 := 0x388000ef.
Lemma F_9bc74 : fetch_word USEGS (0x9bc74 : word) = Some W_9bc74.
Proof. vm_refl. Qed.
Lemma D_9bc74 : decode_any W_9bc74 = Some (Jal 1 904, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9bc78 : bv 32 := 0x00053403.
Lemma F_9bc78 : fetch_word USEGS (0x9bc78 : word) = Some W_9bc78.
Proof. vm_refl. Qed.
Lemma D_9bc78 : decode_any W_9bc78 = Some (Load SZ8 true 8 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9bc7c : bv 32 := 0x12041663.
Lemma F_9bc7c : fetch_word USEGS (0x9bc7c : word) = Some W_9bc7c.
Proof. vm_refl. Qed.
Lemma D_9bc7c : decode_any W_9bc7c = Some (Branch BC_NE 8 0 300, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9bc80 : bv 32 := 0x0004a517.
Lemma F_9bc80 : fetch_word USEGS (0x9bc80 : word) = Some W_9bc80.
Proof. vm_refl. Qed.
Lemma D_9bc80 : decode_any W_9bc80 = Some (Auipc 10 74, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9bc84 : bv 32 := 0xb6053403.
Lemma F_9bc84 : fetch_word USEGS (0x9bc84 : word) = Some W_9bc84.
Proof. vm_refl. Qed.
Lemma D_9bc84 : decode_any W_9bc84 = Some (Load SZ8 true 8 10 2912, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9bc88 : bv 32 := 0x04040a63.
Lemma F_9bc88 : fetch_word USEGS (0x9bc88 : word) = Some W_9bc88.
Proof. vm_refl. Qed.
Lemma D_9bc88 : decode_any W_9bc88 = Some (Branch BC_EQ 8 0 84, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9bcdc : bv 32 := 0x00018517.
Lemma F_9bcdc : fetch_word USEGS (0x9bcdc : word) = Some W_9bcdc.
Proof. vm_refl. Qed.
Lemma D_9bcdc : decode_any W_9bcdc = Some (Auipc 10 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9bce0 : bv 32 := 0x89453403.
Lemma F_9bce0 : fetch_word USEGS (0x9bce0 : word) = Some W_9bce0.
Proof. vm_refl. Qed.
Lemma D_9bce0 : decode_any W_9bce0 = Some (Load SZ8 true 8 10 2196, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9bce4 : bv 32 := 0x04040a63.
Lemma F_9bce4 : fetch_word USEGS (0x9bce4 : word) = Some W_9bce4.
Proof. vm_refl. Qed.
Lemma D_9bce4 : decode_any W_9bce4 = Some (Branch BC_EQ 8 0 84, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9bce8 : bv 32 := 0x08c42503.
Lemma F_9bce8 : fetch_word USEGS (0x9bce8 : word) = Some W_9bce8.
Proof. vm_refl. Qed.
Lemma D_9bce8 : decode_any W_9bce8 = Some (Load SZ4 true 10 8 140, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9bcec : bv 32 := 0x00054663.
Lemma F_9bcec : fetch_word USEGS (0x9bcec : word) = Some W_9bcec.
Proof. vm_refl. Qed.
Lemma D_9bcec : decode_any W_9bcec = Some (Branch BC_LT 10 0 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9bcf8 : bv 32 := 0x02843503.
Lemma F_9bcf8 : fetch_word USEGS (0x9bcf8 : word) = Some W_9bcf8.
Proof. vm_refl. Qed.
Lemma D_9bcf8 : decode_any W_9bcf8 = Some (Load SZ8 true 10 8 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9bcfc : bv 32 := 0x03843583.
Lemma F_9bcfc : fetch_word USEGS (0x9bcfc : word) = Some W_9bcfc.
Proof. vm_refl. Qed.
Lemma D_9bcfc : decode_any W_9bcfc = Some (Load SZ8 true 11 8 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9bd00 : bv 32 := 0x00b50c63.
Lemma F_9bd00 : fetch_word USEGS (0x9bd00 : word) = Some W_9bd00.
Proof. vm_refl. Qed.
Lemma D_9bd00 : decode_any W_9bd00 = Some (Branch BC_EQ 10 11 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9bd04 : bv 32 := 0x04843683.
Lemma F_9bd04 : fetch_word USEGS (0x9bd04 : word) = Some W_9bd04.
Proof. vm_refl. Qed.
Lemma D_9bd04 : decode_any W_9bd04 = Some (Load SZ8 true 13 8 72, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9bd08 : bv 32 := 0x00040513.
Lemma F_9bd08 : fetch_word USEGS (0x9bd08 : word) = Some W_9bd08.
Proof. vm_refl. Qed.
Lemma D_9bd08 : decode_any W_9bd08 = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9bd0c : bv 32 := 0x00000593.
Lemma F_9bd0c : fetch_word USEGS (0x9bd0c : word) = Some W_9bd0c.
Proof. vm_refl. Qed.
Lemma D_9bd0c : decode_any W_9bd0c = Some (OpImm ALU_ADD 11 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9bd10 : bv 32 := 0x00000613.
Lemma F_9bd10 : fetch_word USEGS (0x9bd10 : word) = Some W_9bd10.
Proof. vm_refl. Qed.
Lemma D_9bd10 : decode_any W_9bd10 = Some (OpImm ALU_ADD 12 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9bd14 : bv 32 := 0x000680e7.
Lemma F_9bd14 : fetch_word USEGS (0x9bd14 : word) = Some W_9bd14.
Proof. vm_refl. Qed.
Lemma D_9bd14 : decode_any W_9bd14 = Some (Jalr 1 13 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9bd18 : bv 32 := 0x00843503.
Lemma F_9bd18 : fetch_word USEGS (0x9bd18 : word) = Some W_9bd18.
Proof. vm_refl. Qed.
Lemma D_9bd18 : decode_any W_9bd18 = Some (Load SZ8 true 10 8 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9bd1c : bv 32 := 0x01043583.
Lemma F_9bd1c : fetch_word USEGS (0x9bd1c : word) = Some W_9bd1c.
Proof. vm_refl. Qed.
Lemma D_9bd1c : decode_any W_9bd1c = Some (Load SZ8 true 11 8 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9bd20 : bv 32 := 0x00b50c63.
Lemma F_9bd20 : fetch_word USEGS (0x9bd20 : word) = Some W_9bd20.
Proof. vm_refl. Qed.
Lemma D_9bd20 : decode_any W_9bd20 = Some (Branch BC_EQ 10 11 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9bd38 : bv 32 := 0x00017517.
Lemma F_9bd38 : fetch_word USEGS (0x9bd38 : word) = Some W_9bd38.
Proof. vm_refl. Qed.
Lemma D_9bd38 : decode_any W_9bd38 = Some (Auipc 10 23, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9bd3c : bv 32 := 0x74853403.
Lemma F_9bd3c : fetch_word USEGS (0x9bd3c : word) = Some W_9bd3c.
Proof. vm_refl. Qed.
Lemma D_9bd3c : decode_any W_9bd3c = Some (Load SZ8 true 8 10 1864, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9bd40 : bv 32 := 0x0a040e63.
Lemma F_9bd40 : fetch_word USEGS (0x9bd40 : word) = Some W_9bd40.
Proof. vm_refl. Qed.
Lemma D_9bd40 : decode_any W_9bd40 = Some (Branch BC_EQ 8 0 188, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9bd44 : bv 32 := 0x08c42503.
Lemma F_9bd44 : fetch_word USEGS (0x9bd44 : word) = Some W_9bd44.
Proof. vm_refl. Qed.
Lemma D_9bd44 : decode_any W_9bd44 = Some (Load SZ4 true 10 8 140, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9bd48 : bv 32 := 0x00054663.
Lemma F_9bd48 : fetch_word USEGS (0x9bd48 : word) = Some W_9bd48.
Proof. vm_refl. Qed.
Lemma D_9bd48 : decode_any W_9bd48 = Some (Branch BC_LT 10 0 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9bd54 : bv 32 := 0x02843503.
Lemma F_9bd54 : fetch_word USEGS (0x9bd54 : word) = Some W_9bd54.
Proof. vm_refl. Qed.
Lemma D_9bd54 : decode_any W_9bd54 = Some (Load SZ8 true 10 8 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9bd58 : bv 32 := 0x03843583.
Lemma F_9bd58 : fetch_word USEGS (0x9bd58 : word) = Some W_9bd58.
Proof. vm_refl. Qed.
Lemma D_9bd58 : decode_any W_9bd58 = Some (Load SZ8 true 11 8 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9bd5c : bv 32 := 0x00b50c63.
Lemma F_9bd5c : fetch_word USEGS (0x9bd5c : word) = Some W_9bd5c.
Proof. vm_refl. Qed.
Lemma D_9bd5c : decode_any W_9bd5c = Some (Branch BC_EQ 10 11 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9bd74 : bv 32 := 0x00843503.
Lemma F_9bd74 : fetch_word USEGS (0x9bd74 : word) = Some W_9bd74.
Proof. vm_refl. Qed.
Lemma D_9bd74 : decode_any W_9bd74 = Some (Load SZ8 true 10 8 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9bd78 : bv 32 := 0x01043583.
Lemma F_9bd78 : fetch_word USEGS (0x9bd78 : word) = Some W_9bd78.
Proof. vm_refl. Qed.
Lemma D_9bd78 : decode_any W_9bd78 = Some (Load SZ8 true 11 8 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9bd7c : bv 32 := 0x08b50063.
Lemma F_9bd7c : fetch_word USEGS (0x9bd7c : word) = Some W_9bd7c.
Proof. vm_refl. Qed.
Lemma D_9bd7c : decode_any W_9bd7c = Some (Branch BC_EQ 10 11 128, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9bdfc : bv 32 := 0x00813083.
Lemma F_9bdfc : fetch_word USEGS (0x9bdfc : word) = Some W_9bdfc.
Proof. vm_refl. Qed.
Lemma D_9bdfc : decode_any W_9bdfc = Some (Load SZ8 true 1 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9be00 : bv 32 := 0x00013403.
Lemma F_9be00 : fetch_word USEGS (0x9be00 : word) = Some W_9be00.
Proof. vm_refl. Qed.
Lemma D_9be00 : decode_any W_9be00 = Some (Load SZ8 true 8 2 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9be04 : bv 32 := 0x01010113.
Lemma F_9be04 : fetch_word USEGS (0x9be04 : word) = Some W_9be04.
Proof. vm_refl. Qed.
Lemma D_9be04 : decode_any W_9be04 = Some (OpImm ALU_ADD 2 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9be08 : bv 32 := 0x00008067.
Lemma F_9be08 : fetch_word USEGS (0x9be08 : word) = Some W_9be08.
Proof. vm_refl. Qed.
Lemma D_9be08 : decode_any W_9be08 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9bffc : bv 32 := 0xff010113.
Lemma F_9bffc : fetch_word USEGS (0x9bffc : word) = Some W_9bffc.
Proof. vm_refl. Qed.
Lemma D_9bffc : decode_any W_9bffc = Some (OpImm ALU_ADD 2 2 4080, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9c000 : bv 32 := 0x00113423.
Lemma F_9c000 : fetch_word USEGS (0x9c000 : word) = Some W_9c000.
Proof. vm_refl. Qed.
Lemma D_9c000 : decode_any W_9c000 = Some (Store SZ8 2 1 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9c004 : bv 32 := 0x00813023.
Lemma F_9c004 : fetch_word USEGS (0x9c004 : word) = Some W_9c004.
Proof. vm_refl. Qed.
Lemma D_9c004 : decode_any W_9c004 = Some (Store SZ8 2 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9c008 : bv 32 := 0x00049517.
Lemma F_9c008 : fetch_word USEGS (0x9c008 : word) = Some W_9c008.
Proof. vm_refl. Qed.
Lemma D_9c008 : decode_any W_9c008 = Some (Auipc 10 73, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9c00c : bv 32 := 0x7e050413.
Lemma F_9c00c : fetch_word USEGS (0x9c00c : word) = Some W_9c00c.
Proof. vm_refl. Qed.
Lemma D_9c00c : decode_any W_9c00c = Some (OpImm ALU_ADD 8 10 2016, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9c010 : bv 32 := 0x00040513.
Lemma F_9c010 : fetch_word USEGS (0x9c010 : word) = Some W_9c010.
Proof. vm_refl. Qed.
Lemma D_9c010 : decode_any W_9c010 = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9c014 : bv 32 := 0x2050b0ef.
Lemma F_9c014 : fetch_word USEGS (0x9c014 : word) = Some W_9c014.
Proof. vm_refl. Qed.
Lemma D_9c014 : decode_any W_9c014 = Some (Jal 1 47620, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9c018 : bv 32 := 0x00840513.
Lemma F_9c018 : fetch_word USEGS (0x9c018 : word) = Some W_9c018.
Proof. vm_refl. Qed.
Lemma D_9c018 : decode_any W_9c018 = Some (OpImm ALU_ADD 10 8 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9c01c : bv 32 := 0x00813083.
Lemma F_9c01c : fetch_word USEGS (0x9c01c : word) = Some W_9c01c.
Proof. vm_refl. Qed.
Lemma D_9c01c : decode_any W_9c01c = Some (Load SZ8 true 1 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9c020 : bv 32 := 0x00013403.
Lemma F_9c020 : fetch_word USEGS (0x9c020 : word) = Some W_9c020.
Proof. vm_refl. Qed.
Lemma D_9c020 : decode_any W_9c020 = Some (Load SZ8 true 8 2 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9c024 : bv 32 := 0x01010113.
Lemma F_9c024 : fetch_word USEGS (0x9c024 : word) = Some W_9c024.
Proof. vm_refl. Qed.
Lemma D_9c024 : decode_any W_9c024 = Some (OpImm ALU_ADD 2 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9c028 : bv 32 := 0x00008067.
Lemma F_9c028 : fetch_word USEGS (0x9c028 : word) = Some W_9c028.
Proof. vm_refl. Qed.
Lemma D_9c028 : decode_any W_9c028 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9c0fc : bv 32 := 0x00008067.
Lemma F_9c0fc : fetch_word USEGS (0x9c0fc : word) = Some W_9c0fc.
Proof. vm_refl. Qed.
Lemma D_9c0fc : decode_any W_9c0fc = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9c12c : bv 32 := 0xf9010113.
Lemma F_9c12c : fetch_word USEGS (0x9c12c : word) = Some W_9c12c.
Proof. vm_refl. Qed.
Lemma D_9c12c : decode_any W_9c12c = Some (OpImm ALU_ADD 2 2 3984, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9c130 : bv 32 := 0x06113423.
Lemma F_9c130 : fetch_word USEGS (0x9c130 : word) = Some W_9c130.
Proof. vm_refl. Qed.
Lemma D_9c130 : decode_any W_9c130 = Some (Store SZ8 2 1 104, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9c134 : bv 32 := 0x06813023.
Lemma F_9c134 : fetch_word USEGS (0x9c134 : word) = Some W_9c134.
Proof. vm_refl. Qed.
Lemma D_9c134 : decode_any W_9c134 = Some (Store SZ8 2 8 96, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9c138 : bv 32 := 0x04913c23.
Lemma F_9c138 : fetch_word USEGS (0x9c138 : word) = Some W_9c138.
Proof. vm_refl. Qed.
Lemma D_9c138 : decode_any W_9c138 = Some (Store SZ8 2 9 88, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9c13c : bv 32 := 0x05213823.
Lemma F_9c13c : fetch_word USEGS (0x9c13c : word) = Some W_9c13c.
Proof. vm_refl. Qed.
Lemma D_9c13c : decode_any W_9c13c = Some (Store SZ8 2 18 80, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9c140 : bv 32 := 0x05313423.
Lemma F_9c140 : fetch_word USEGS (0x9c140 : word) = Some W_9c140.
Proof. vm_refl. Qed.
Lemma D_9c140 : decode_any W_9c140 = Some (Store SZ8 2 19 72, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9c144 : bv 32 := 0x05413023.
Lemma F_9c144 : fetch_word USEGS (0x9c144 : word) = Some W_9c144.
Proof. vm_refl. Qed.
Lemma D_9c144 : decode_any W_9c144 = Some (Store SZ8 2 20 64, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9c148 : bv 32 := 0x03513c23.
Lemma F_9c148 : fetch_word USEGS (0x9c148 : word) = Some W_9c148.
Proof. vm_refl. Qed.
Lemma D_9c148 : decode_any W_9c148 = Some (Store SZ8 2 21 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9c14c : bv 32 := 0x03613823.
Lemma F_9c14c : fetch_word USEGS (0x9c14c : word) = Some W_9c14c.
Proof. vm_refl. Qed.
Lemma D_9c14c : decode_any W_9c14c = Some (Store SZ8 2 22 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9c150 : bv 32 := 0x00060413.
Lemma F_9c150 : fetch_word USEGS (0x9c150 : word) = Some W_9c150.
Proof. vm_refl. Qed.
Lemma D_9c150 : decode_any W_9c150 = Some (OpImm ALU_ADD 8 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9c154 : bv 32 := 0x00050493.
Lemma F_9c154 : fetch_word USEGS (0x9c154 : word) = Some W_9c154.
Proof. vm_refl. Qed.
Lemma D_9c154 : decode_any W_9c154 = Some (OpImm ALU_ADD 9 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9c158 : bv 32 := 0x00016517.
Lemma F_9c158 : fetch_word USEGS (0x9c158 : word) = Some W_9c158.
Proof. vm_refl. Qed.
Lemma D_9c158 : decode_any W_9c158 = Some (Auipc 10 22, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9c15c : bv 32 := 0x15053a83.
Lemma F_9c15c : fetch_word USEGS (0x9c15c : word) = Some W_9c15c.
Proof. vm_refl. Qed.
Lemma D_9c15c : decode_any W_9c15c = Some (Load SZ8 true 21 10 336, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9c160 : bv 32 := 0x000ab503.
Lemma F_9c160 : fetch_word USEGS (0x9c160 : word) = Some W_9c160.
Proof. vm_refl. Qed.
Lemma D_9c160 : decode_any W_9c160 = Some (Load SZ8 true 10 21 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9c164 : bv 32 := 0x02a13423.
Lemma F_9c164 : fetch_word USEGS (0x9c164 : word) = Some W_9c164.
Proof. vm_refl. Qed.
Lemma D_9c164 : decode_any W_9c164 = Some (Store SZ8 2 10 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9c168 : bv 32 := 0x0284b503.
Lemma F_9c168 : fetch_word USEGS (0x9c168 : word) = Some W_9c168.
Proof. vm_refl. Qed.
Lemma D_9c168 : decode_any W_9c168 = Some (Load SZ8 true 10 9 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9c16c : bv 32 := 0x0384b603.
Lemma F_9c16c : fetch_word USEGS (0x9c16c : word) = Some W_9c16c.
Proof. vm_refl. Qed.
Lemma D_9c16c : decode_any W_9c16c = Some (Load SZ8 true 12 9 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9c170 : bv 32 := 0x40c50b33.
Lemma F_9c170 : fetch_word USEGS (0x9c170 : word) = Some W_9c170.
Proof. vm_refl. Qed.
Lemma D_9c170 : decode_any W_9c170 = Some (Op ALU_SUB 22 10 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9c174 : bv 32 := 0x00c546b3.
Lemma F_9c174 : fetch_word USEGS (0x9c174 : word) = Some W_9c174.
Proof. vm_refl. Qed.
Lemma D_9c174 : decode_any W_9c174 = Some (Op ALU_XOR 13 10 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9c178 : bv 32 := 0x00c13423.
Lemma F_9c178 : fetch_word USEGS (0x9c178 : word) = Some W_9c178.
Proof. vm_refl. Qed.
Lemma D_9c178 : decode_any W_9c178 = Some (Store SZ8 2 12 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9c17c : bv 32 := 0x01613823.
Lemma F_9c17c : fetch_word USEGS (0x9c17c : word) = Some W_9c17c.
Proof. vm_refl. Qed.
Lemma D_9c17c : decode_any W_9c17c = Some (Store SZ8 2 22 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9c180 : bv 32 := 0x00b13c23.
Lemma F_9c180 : fetch_word USEGS (0x9c180 : word) = Some W_9c180.
Proof. vm_refl. Qed.
Lemma D_9c180 : decode_any W_9c180 = Some (Store SZ8 2 11 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9c184 : bv 32 := 0x02813023.
Lemma F_9c184 : fetch_word USEGS (0x9c184 : word) = Some W_9c184.
Proof. vm_refl. Qed.
Lemma D_9c184 : decode_any W_9c184 = Some (Store SZ8 2 8 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9c188 : bv 32 := 0x008b0b33.
Lemma F_9c188 : fetch_word USEGS (0x9c188 : word) = Some W_9c188.
Proof. vm_refl. Qed.
Lemma D_9c188 : decode_any W_9c188 = Some (Op ALU_ADD 22 22 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9c18c : bv 32 := 0x00d03933.
Lemma F_9c18c : fetch_word USEGS (0x9c18c : word) = Some W_9c18c.
Proof. vm_refl. Qed.
Lemma D_9c18c : decode_any W_9c18c = Some (Op ALU_SLTU 18 0 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9c190 : bv 32 := 0x00c50663.
Lemma F_9c190 : fetch_word USEGS (0x9c190 : word) = Some W_9c190.
Proof. vm_refl. Qed.
Lemma D_9c190 : decode_any W_9c190 = Some (Branch BC_EQ 10 12 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9c194 : bv 32 := 0x00810993.
Lemma F_9c194 : fetch_word USEGS (0x9c194 : word) = Some W_9c194.
Proof. vm_refl. Qed.
Lemma D_9c194 : decode_any W_9c194 = Some (OpImm ALU_ADD 19 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9c198 : bv 32 := 0x0080006f.
Lemma F_9c198 : fetch_word USEGS (0x9c198 : word) = Some W_9c198.
Proof. vm_refl. Qed.
Lemma D_9c198 : decode_any W_9c198 = Some (Jal 0 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9c19c : bv 32 := 0x01810993.
Lemma F_9c19c : fetch_word USEGS (0x9c19c : word) = Some W_9c19c.
Proof. vm_refl. Qed.
Lemma D_9c19c : decode_any W_9c19c = Some (OpImm ALU_ADD 19 2 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9c1a0 : bv 32 := 0x0784a503.
Lemma F_9c1a0 : fetch_word USEGS (0x9c1a0 : word) = Some W_9c1a0.
Proof. vm_refl. Qed.
Lemma D_9c1a0 : decode_any W_9c1a0 = Some (Load SZ4 true 10 9 120, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9c1a4 : bv 32 := 0x00190913.
Lemma F_9c1a4 : fetch_word USEGS (0x9c1a4 : word) = Some W_9c1a4.
Proof. vm_refl. Qed.
Lemma D_9c1a4 : decode_any W_9c1a4 = Some (OpImm ALU_ADD 18 18 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9c1a8 : bv 32 := 0x04200893.
Lemma F_9c1a8 : fetch_word USEGS (0x9c1a8 : word) = Some W_9c1a8.
Proof. vm_refl. Qed.
Lemma D_9c1a8 : decode_any W_9c1a8 = Some (OpImm ALU_ADD 17 0 66, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9c1ac : bv 32 := 0x00098593.
Lemma F_9c1ac : fetch_word USEGS (0x9c1ac : word) = Some W_9c1ac.
Proof. vm_refl. Qed.
Lemma D_9c1ac : decode_any W_9c1ac = Some (OpImm ALU_ADD 11 19 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9c1b0 : bv 32 := 0x00090613.
Lemma F_9c1b0 : fetch_word USEGS (0x9c1b0 : word) = Some W_9c1b0.
Proof. vm_refl. Qed.
Lemma D_9c1b0 : decode_any W_9c1b0 = Some (OpImm ALU_ADD 12 18 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9c1b4 : bv 32 := 0x00000073.
Lemma F_9c1b4 : fetch_word USEGS (0x9c1b4 : word) = Some W_9c1b4.
Proof. vm_refl. Qed.
Lemma D_9c1b4 : decode_any W_9c1b4 = Some (Ecall, 4%Z).
Proof. vm_refl. Qed.
Lemma E_9c1b4 : is_ecall W_9c1b4 = true.
Proof. reflexivity. Qed.
