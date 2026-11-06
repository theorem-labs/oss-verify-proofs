(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib Require Import ImgP.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Abbreviation PSEGS := ImgP.M.loaded_segments.
Open Scope bv_scope.

(* [comment removed for export] *)
Local Ltac vm_refl :=
  lazymatch goal with
  | |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true)
  end.

(* [comment removed for export] *)
Definition W_9b570 : bv 32 := 0xff010113.
Lemma F_9b570 : fetch_word PSEGS (0x9b570 : word) = Some W_9b570.
Proof. vm_refl. Qed.
Lemma D_9b570 : decode_any W_9b570 = Some (OpImm ALU_ADD 2 2 4080, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9b574 : bv 32 := 0x00113423.
Lemma F_9b574 : fetch_word PSEGS (0x9b574 : word) = Some W_9b574.
Proof. vm_refl. Qed.
Lemma D_9b574 : decode_any W_9b574 = Some (Store SZ8 2 1 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9b578 : bv 32 := 0x00813023.
Lemma F_9b578 : fetch_word PSEGS (0x9b578 : word) = Some W_9b578.
Proof. vm_refl. Qed.
Lemma D_9b578 : decode_any W_9b578 = Some (Store SZ8 2 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9b57c : bv 32 := 0x388000ef.
Lemma F_9b57c : fetch_word PSEGS (0x9b57c : word) = Some W_9b57c.
Proof. vm_refl. Qed.
Lemma D_9b57c : decode_any W_9b57c = Some (Jal 1 904, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9b580 : bv 32 := 0x00053403.
Lemma F_9b580 : fetch_word PSEGS (0x9b580 : word) = Some W_9b580.
Proof. vm_refl. Qed.
Lemma D_9b580 : decode_any W_9b580 = Some (Load SZ8 true 8 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9b584 : bv 32 := 0x12041663.
Lemma F_9b584 : fetch_word PSEGS (0x9b584 : word) = Some W_9b584.
Proof. vm_refl. Qed.
Lemma D_9b584 : decode_any W_9b584 = Some (Branch BC_NE 8 0 300, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9b588 : bv 32 := 0x0004a517.
Lemma F_9b588 : fetch_word PSEGS (0x9b588 : word) = Some W_9b588.
Proof. vm_refl. Qed.
Lemma D_9b588 : decode_any W_9b588 = Some (Auipc 10 74, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9b58c : bv 32 := 0xb5853403.
Lemma F_9b58c : fetch_word PSEGS (0x9b58c : word) = Some W_9b58c.
Proof. vm_refl. Qed.
Lemma D_9b58c : decode_any W_9b58c = Some (Load SZ8 true 8 10 2904, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9b590 : bv 32 := 0x04040a63.
Lemma F_9b590 : fetch_word PSEGS (0x9b590 : word) = Some W_9b590.
Proof. vm_refl. Qed.
Lemma D_9b590 : decode_any W_9b590 = Some (Branch BC_EQ 8 0 84, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9b5e4 : bv 32 := 0x00018517.
Lemma F_9b5e4 : fetch_word PSEGS (0x9b5e4 : word) = Some W_9b5e4.
Proof. vm_refl. Qed.
Lemma D_9b5e4 : decode_any W_9b5e4 = Some (Auipc 10 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9b5e8 : bv 32 := 0x89453403.
Lemma F_9b5e8 : fetch_word PSEGS (0x9b5e8 : word) = Some W_9b5e8.
Proof. vm_refl. Qed.
Lemma D_9b5e8 : decode_any W_9b5e8 = Some (Load SZ8 true 8 10 2196, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9b5ec : bv 32 := 0x04040a63.
Lemma F_9b5ec : fetch_word PSEGS (0x9b5ec : word) = Some W_9b5ec.
Proof. vm_refl. Qed.
Lemma D_9b5ec : decode_any W_9b5ec = Some (Branch BC_EQ 8 0 84, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9b5f0 : bv 32 := 0x08c42503.
Lemma F_9b5f0 : fetch_word PSEGS (0x9b5f0 : word) = Some W_9b5f0.
Proof. vm_refl. Qed.
Lemma D_9b5f0 : decode_any W_9b5f0 = Some (Load SZ4 true 10 8 140, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9b5f4 : bv 32 := 0x00054663.
Lemma F_9b5f4 : fetch_word PSEGS (0x9b5f4 : word) = Some W_9b5f4.
Proof. vm_refl. Qed.
Lemma D_9b5f4 : decode_any W_9b5f4 = Some (Branch BC_LT 10 0 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9b600 : bv 32 := 0x02843503.
Lemma F_9b600 : fetch_word PSEGS (0x9b600 : word) = Some W_9b600.
Proof. vm_refl. Qed.
Lemma D_9b600 : decode_any W_9b600 = Some (Load SZ8 true 10 8 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9b604 : bv 32 := 0x03843583.
Lemma F_9b604 : fetch_word PSEGS (0x9b604 : word) = Some W_9b604.
Proof. vm_refl. Qed.
Lemma D_9b604 : decode_any W_9b604 = Some (Load SZ8 true 11 8 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9b608 : bv 32 := 0x00b50c63.
Lemma F_9b608 : fetch_word PSEGS (0x9b608 : word) = Some W_9b608.
Proof. vm_refl. Qed.
Lemma D_9b608 : decode_any W_9b608 = Some (Branch BC_EQ 10 11 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9b60c : bv 32 := 0x04843683.
Lemma F_9b60c : fetch_word PSEGS (0x9b60c : word) = Some W_9b60c.
Proof. vm_refl. Qed.
Lemma D_9b60c : decode_any W_9b60c = Some (Load SZ8 true 13 8 72, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9b610 : bv 32 := 0x00040513.
Lemma F_9b610 : fetch_word PSEGS (0x9b610 : word) = Some W_9b610.
Proof. vm_refl. Qed.
Lemma D_9b610 : decode_any W_9b610 = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9b614 : bv 32 := 0x00000593.
Lemma F_9b614 : fetch_word PSEGS (0x9b614 : word) = Some W_9b614.
Proof. vm_refl. Qed.
Lemma D_9b614 : decode_any W_9b614 = Some (OpImm ALU_ADD 11 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9b618 : bv 32 := 0x00000613.
Lemma F_9b618 : fetch_word PSEGS (0x9b618 : word) = Some W_9b618.
Proof. vm_refl. Qed.
Lemma D_9b618 : decode_any W_9b618 = Some (OpImm ALU_ADD 12 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9b61c : bv 32 := 0x000680e7.
Lemma F_9b61c : fetch_word PSEGS (0x9b61c : word) = Some W_9b61c.
Proof. vm_refl. Qed.
Lemma D_9b61c : decode_any W_9b61c = Some (Jalr 1 13 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9b620 : bv 32 := 0x00843503.
Lemma F_9b620 : fetch_word PSEGS (0x9b620 : word) = Some W_9b620.
Proof. vm_refl. Qed.
Lemma D_9b620 : decode_any W_9b620 = Some (Load SZ8 true 10 8 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9b624 : bv 32 := 0x01043583.
Lemma F_9b624 : fetch_word PSEGS (0x9b624 : word) = Some W_9b624.
Proof. vm_refl. Qed.
Lemma D_9b624 : decode_any W_9b624 = Some (Load SZ8 true 11 8 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9b628 : bv 32 := 0x00b50c63.
Lemma F_9b628 : fetch_word PSEGS (0x9b628 : word) = Some W_9b628.
Proof. vm_refl. Qed.
Lemma D_9b628 : decode_any W_9b628 = Some (Branch BC_EQ 10 11 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9b640 : bv 32 := 0x00017517.
Lemma F_9b640 : fetch_word PSEGS (0x9b640 : word) = Some W_9b640.
Proof. vm_refl. Qed.
Lemma D_9b640 : decode_any W_9b640 = Some (Auipc 10 23, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9b644 : bv 32 := 0x74853403.
Lemma F_9b644 : fetch_word PSEGS (0x9b644 : word) = Some W_9b644.
Proof. vm_refl. Qed.
Lemma D_9b644 : decode_any W_9b644 = Some (Load SZ8 true 8 10 1864, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9b648 : bv 32 := 0x0a040e63.
Lemma F_9b648 : fetch_word PSEGS (0x9b648 : word) = Some W_9b648.
Proof. vm_refl. Qed.
Lemma D_9b648 : decode_any W_9b648 = Some (Branch BC_EQ 8 0 188, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9b64c : bv 32 := 0x08c42503.
Lemma F_9b64c : fetch_word PSEGS (0x9b64c : word) = Some W_9b64c.
Proof. vm_refl. Qed.
Lemma D_9b64c : decode_any W_9b64c = Some (Load SZ4 true 10 8 140, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9b650 : bv 32 := 0x00054663.
Lemma F_9b650 : fetch_word PSEGS (0x9b650 : word) = Some W_9b650.
Proof. vm_refl. Qed.
Lemma D_9b650 : decode_any W_9b650 = Some (Branch BC_LT 10 0 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9b65c : bv 32 := 0x02843503.
Lemma F_9b65c : fetch_word PSEGS (0x9b65c : word) = Some W_9b65c.
Proof. vm_refl. Qed.
Lemma D_9b65c : decode_any W_9b65c = Some (Load SZ8 true 10 8 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9b660 : bv 32 := 0x03843583.
Lemma F_9b660 : fetch_word PSEGS (0x9b660 : word) = Some W_9b660.
Proof. vm_refl. Qed.
Lemma D_9b660 : decode_any W_9b660 = Some (Load SZ8 true 11 8 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9b664 : bv 32 := 0x00b50c63.
Lemma F_9b664 : fetch_word PSEGS (0x9b664 : word) = Some W_9b664.
Proof. vm_refl. Qed.
Lemma D_9b664 : decode_any W_9b664 = Some (Branch BC_EQ 10 11 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9b67c : bv 32 := 0x00843503.
Lemma F_9b67c : fetch_word PSEGS (0x9b67c : word) = Some W_9b67c.
Proof. vm_refl. Qed.
Lemma D_9b67c : decode_any W_9b67c = Some (Load SZ8 true 10 8 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9b680 : bv 32 := 0x01043583.
Lemma F_9b680 : fetch_word PSEGS (0x9b680 : word) = Some W_9b680.
Proof. vm_refl. Qed.
Lemma D_9b680 : decode_any W_9b680 = Some (Load SZ8 true 11 8 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9b684 : bv 32 := 0x08b50063.
Lemma F_9b684 : fetch_word PSEGS (0x9b684 : word) = Some W_9b684.
Proof. vm_refl. Qed.
Lemma D_9b684 : decode_any W_9b684 = Some (Branch BC_EQ 10 11 128, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9b704 : bv 32 := 0x00813083.
Lemma F_9b704 : fetch_word PSEGS (0x9b704 : word) = Some W_9b704.
Proof. vm_refl. Qed.
Lemma D_9b704 : decode_any W_9b704 = Some (Load SZ8 true 1 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9b708 : bv 32 := 0x00013403.
Lemma F_9b708 : fetch_word PSEGS (0x9b708 : word) = Some W_9b708.
Proof. vm_refl. Qed.
Lemma D_9b708 : decode_any W_9b708 = Some (Load SZ8 true 8 2 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9b70c : bv 32 := 0x01010113.
Lemma F_9b70c : fetch_word PSEGS (0x9b70c : word) = Some W_9b70c.
Proof. vm_refl. Qed.
Lemma D_9b70c : decode_any W_9b70c = Some (OpImm ALU_ADD 2 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9b710 : bv 32 := 0x00008067.
Lemma F_9b710 : fetch_word PSEGS (0x9b710 : word) = Some W_9b710.
Proof. vm_refl. Qed.
Lemma D_9b710 : decode_any W_9b710 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9b904 : bv 32 := 0xff010113.
Lemma F_9b904 : fetch_word PSEGS (0x9b904 : word) = Some W_9b904.
Proof. vm_refl. Qed.
Lemma D_9b904 : decode_any W_9b904 = Some (OpImm ALU_ADD 2 2 4080, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9b908 : bv 32 := 0x00113423.
Lemma F_9b908 : fetch_word PSEGS (0x9b908 : word) = Some W_9b908.
Proof. vm_refl. Qed.
Lemma D_9b908 : decode_any W_9b908 = Some (Store SZ8 2 1 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9b90c : bv 32 := 0x00813023.
Lemma F_9b90c : fetch_word PSEGS (0x9b90c : word) = Some W_9b90c.
Proof. vm_refl. Qed.
Lemma D_9b90c : decode_any W_9b90c = Some (Store SZ8 2 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9b910 : bv 32 := 0x00049517.
Lemma F_9b910 : fetch_word PSEGS (0x9b910 : word) = Some W_9b910.
Proof. vm_refl. Qed.
Lemma D_9b910 : decode_any W_9b910 = Some (Auipc 10 73, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9b914 : bv 32 := 0x7d850413.
Lemma F_9b914 : fetch_word PSEGS (0x9b914 : word) = Some W_9b914.
Proof. vm_refl. Qed.
Lemma D_9b914 : decode_any W_9b914 = Some (OpImm ALU_ADD 8 10 2008, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9b918 : bv 32 := 0x00040513.
Lemma F_9b918 : fetch_word PSEGS (0x9b918 : word) = Some W_9b918.
Proof. vm_refl. Qed.
Lemma D_9b918 : decode_any W_9b918 = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9b91c : bv 32 := 0x2050b0ef.
Lemma F_9b91c : fetch_word PSEGS (0x9b91c : word) = Some W_9b91c.
Proof. vm_refl. Qed.
Lemma D_9b91c : decode_any W_9b91c = Some (Jal 1 47620, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9b920 : bv 32 := 0x00840513.
Lemma F_9b920 : fetch_word PSEGS (0x9b920 : word) = Some W_9b920.
Proof. vm_refl. Qed.
Lemma D_9b920 : decode_any W_9b920 = Some (OpImm ALU_ADD 10 8 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9b924 : bv 32 := 0x00813083.
Lemma F_9b924 : fetch_word PSEGS (0x9b924 : word) = Some W_9b924.
Proof. vm_refl. Qed.
Lemma D_9b924 : decode_any W_9b924 = Some (Load SZ8 true 1 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9b928 : bv 32 := 0x00013403.
Lemma F_9b928 : fetch_word PSEGS (0x9b928 : word) = Some W_9b928.
Proof. vm_refl. Qed.
Lemma D_9b928 : decode_any W_9b928 = Some (Load SZ8 true 8 2 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9b92c : bv 32 := 0x01010113.
Lemma F_9b92c : fetch_word PSEGS (0x9b92c : word) = Some W_9b92c.
Proof. vm_refl. Qed.
Lemma D_9b92c : decode_any W_9b92c = Some (OpImm ALU_ADD 2 2 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9b930 : bv 32 := 0x00008067.
Lemma F_9b930 : fetch_word PSEGS (0x9b930 : word) = Some W_9b930.
Proof. vm_refl. Qed.
Lemma D_9b930 : decode_any W_9b930 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9ba04 : bv 32 := 0x00008067.
Lemma F_9ba04 : fetch_word PSEGS (0x9ba04 : word) = Some W_9ba04.
Proof. vm_refl. Qed.
Lemma D_9ba04 : decode_any W_9ba04 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9ba34 : bv 32 := 0xf9010113.
Lemma F_9ba34 : fetch_word PSEGS (0x9ba34 : word) = Some W_9ba34.
Proof. vm_refl. Qed.
Lemma D_9ba34 : decode_any W_9ba34 = Some (OpImm ALU_ADD 2 2 3984, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9ba38 : bv 32 := 0x06113423.
Lemma F_9ba38 : fetch_word PSEGS (0x9ba38 : word) = Some W_9ba38.
Proof. vm_refl. Qed.
Lemma D_9ba38 : decode_any W_9ba38 = Some (Store SZ8 2 1 104, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9ba3c : bv 32 := 0x06813023.
Lemma F_9ba3c : fetch_word PSEGS (0x9ba3c : word) = Some W_9ba3c.
Proof. vm_refl. Qed.
Lemma D_9ba3c : decode_any W_9ba3c = Some (Store SZ8 2 8 96, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9ba40 : bv 32 := 0x04913c23.
Lemma F_9ba40 : fetch_word PSEGS (0x9ba40 : word) = Some W_9ba40.
Proof. vm_refl. Qed.
Lemma D_9ba40 : decode_any W_9ba40 = Some (Store SZ8 2 9 88, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9ba44 : bv 32 := 0x05213823.
Lemma F_9ba44 : fetch_word PSEGS (0x9ba44 : word) = Some W_9ba44.
Proof. vm_refl. Qed.
Lemma D_9ba44 : decode_any W_9ba44 = Some (Store SZ8 2 18 80, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9ba48 : bv 32 := 0x05313423.
Lemma F_9ba48 : fetch_word PSEGS (0x9ba48 : word) = Some W_9ba48.
Proof. vm_refl. Qed.
Lemma D_9ba48 : decode_any W_9ba48 = Some (Store SZ8 2 19 72, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9ba4c : bv 32 := 0x05413023.
Lemma F_9ba4c : fetch_word PSEGS (0x9ba4c : word) = Some W_9ba4c.
Proof. vm_refl. Qed.
Lemma D_9ba4c : decode_any W_9ba4c = Some (Store SZ8 2 20 64, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9ba50 : bv 32 := 0x03513c23.
Lemma F_9ba50 : fetch_word PSEGS (0x9ba50 : word) = Some W_9ba50.
Proof. vm_refl. Qed.
Lemma D_9ba50 : decode_any W_9ba50 = Some (Store SZ8 2 21 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9ba54 : bv 32 := 0x03613823.
Lemma F_9ba54 : fetch_word PSEGS (0x9ba54 : word) = Some W_9ba54.
Proof. vm_refl. Qed.
Lemma D_9ba54 : decode_any W_9ba54 = Some (Store SZ8 2 22 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9ba58 : bv 32 := 0x00060413.
Lemma F_9ba58 : fetch_word PSEGS (0x9ba58 : word) = Some W_9ba58.
Proof. vm_refl. Qed.
Lemma D_9ba58 : decode_any W_9ba58 = Some (OpImm ALU_ADD 8 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9ba5c : bv 32 := 0x00050493.
Lemma F_9ba5c : fetch_word PSEGS (0x9ba5c : word) = Some W_9ba5c.
Proof. vm_refl. Qed.
Lemma D_9ba5c : decode_any W_9ba5c = Some (OpImm ALU_ADD 9 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9ba60 : bv 32 := 0x00016517.
Lemma F_9ba60 : fetch_word PSEGS (0x9ba60 : word) = Some W_9ba60.
Proof. vm_refl. Qed.
Lemma D_9ba60 : decode_any W_9ba60 = Some (Auipc 10 22, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9ba64 : bv 32 := 0x15053a83.
Lemma F_9ba64 : fetch_word PSEGS (0x9ba64 : word) = Some W_9ba64.
Proof. vm_refl. Qed.
Lemma D_9ba64 : decode_any W_9ba64 = Some (Load SZ8 true 21 10 336, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9ba68 : bv 32 := 0x000ab503.
Lemma F_9ba68 : fetch_word PSEGS (0x9ba68 : word) = Some W_9ba68.
Proof. vm_refl. Qed.
Lemma D_9ba68 : decode_any W_9ba68 = Some (Load SZ8 true 10 21 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9ba6c : bv 32 := 0x02a13423.
Lemma F_9ba6c : fetch_word PSEGS (0x9ba6c : word) = Some W_9ba6c.
Proof. vm_refl. Qed.
Lemma D_9ba6c : decode_any W_9ba6c = Some (Store SZ8 2 10 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9ba70 : bv 32 := 0x0284b503.
Lemma F_9ba70 : fetch_word PSEGS (0x9ba70 : word) = Some W_9ba70.
Proof. vm_refl. Qed.
Lemma D_9ba70 : decode_any W_9ba70 = Some (Load SZ8 true 10 9 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9ba74 : bv 32 := 0x0384b603.
Lemma F_9ba74 : fetch_word PSEGS (0x9ba74 : word) = Some W_9ba74.
Proof. vm_refl. Qed.
Lemma D_9ba74 : decode_any W_9ba74 = Some (Load SZ8 true 12 9 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9ba78 : bv 32 := 0x40c50b33.
Lemma F_9ba78 : fetch_word PSEGS (0x9ba78 : word) = Some W_9ba78.
Proof. vm_refl. Qed.
Lemma D_9ba78 : decode_any W_9ba78 = Some (Op ALU_SUB 22 10 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9ba7c : bv 32 := 0x00c546b3.
Lemma F_9ba7c : fetch_word PSEGS (0x9ba7c : word) = Some W_9ba7c.
Proof. vm_refl. Qed.
Lemma D_9ba7c : decode_any W_9ba7c = Some (Op ALU_XOR 13 10 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9ba80 : bv 32 := 0x00c13423.
Lemma F_9ba80 : fetch_word PSEGS (0x9ba80 : word) = Some W_9ba80.
Proof. vm_refl. Qed.
Lemma D_9ba80 : decode_any W_9ba80 = Some (Store SZ8 2 12 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9ba84 : bv 32 := 0x01613823.
Lemma F_9ba84 : fetch_word PSEGS (0x9ba84 : word) = Some W_9ba84.
Proof. vm_refl. Qed.
Lemma D_9ba84 : decode_any W_9ba84 = Some (Store SZ8 2 22 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9ba88 : bv 32 := 0x00b13c23.
Lemma F_9ba88 : fetch_word PSEGS (0x9ba88 : word) = Some W_9ba88.
Proof. vm_refl. Qed.
Lemma D_9ba88 : decode_any W_9ba88 = Some (Store SZ8 2 11 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9ba8c : bv 32 := 0x02813023.
Lemma F_9ba8c : fetch_word PSEGS (0x9ba8c : word) = Some W_9ba8c.
Proof. vm_refl. Qed.
Lemma D_9ba8c : decode_any W_9ba8c = Some (Store SZ8 2 8 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9ba90 : bv 32 := 0x008b0b33.
Lemma F_9ba90 : fetch_word PSEGS (0x9ba90 : word) = Some W_9ba90.
Proof. vm_refl. Qed.
Lemma D_9ba90 : decode_any W_9ba90 = Some (Op ALU_ADD 22 22 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9ba94 : bv 32 := 0x00d03933.
Lemma F_9ba94 : fetch_word PSEGS (0x9ba94 : word) = Some W_9ba94.
Proof. vm_refl. Qed.
Lemma D_9ba94 : decode_any W_9ba94 = Some (Op ALU_SLTU 18 0 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9ba98 : bv 32 := 0x00c50663.
Lemma F_9ba98 : fetch_word PSEGS (0x9ba98 : word) = Some W_9ba98.
Proof. vm_refl. Qed.
Lemma D_9ba98 : decode_any W_9ba98 = Some (Branch BC_EQ 10 12 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9ba9c : bv 32 := 0x00810993.
Lemma F_9ba9c : fetch_word PSEGS (0x9ba9c : word) = Some W_9ba9c.
Proof. vm_refl. Qed.
Lemma D_9ba9c : decode_any W_9ba9c = Some (OpImm ALU_ADD 19 2 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9baa0 : bv 32 := 0x0080006f.
Lemma F_9baa0 : fetch_word PSEGS (0x9baa0 : word) = Some W_9baa0.
Proof. vm_refl. Qed.
Lemma D_9baa0 : decode_any W_9baa0 = Some (Jal 0 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9baa4 : bv 32 := 0x01810993.
Lemma F_9baa4 : fetch_word PSEGS (0x9baa4 : word) = Some W_9baa4.
Proof. vm_refl. Qed.
Lemma D_9baa4 : decode_any W_9baa4 = Some (OpImm ALU_ADD 19 2 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9baa8 : bv 32 := 0x0784a503.
Lemma F_9baa8 : fetch_word PSEGS (0x9baa8 : word) = Some W_9baa8.
Proof. vm_refl. Qed.
Lemma D_9baa8 : decode_any W_9baa8 = Some (Load SZ4 true 10 9 120, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9baac : bv 32 := 0x00190913.
Lemma F_9baac : fetch_word PSEGS (0x9baac : word) = Some W_9baac.
Proof. vm_refl. Qed.
Lemma D_9baac : decode_any W_9baac = Some (OpImm ALU_ADD 18 18 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9bab0 : bv 32 := 0x04200893.
Lemma F_9bab0 : fetch_word PSEGS (0x9bab0 : word) = Some W_9bab0.
Proof. vm_refl. Qed.
Lemma D_9bab0 : decode_any W_9bab0 = Some (OpImm ALU_ADD 17 0 66, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9bab4 : bv 32 := 0x00098593.
Lemma F_9bab4 : fetch_word PSEGS (0x9bab4 : word) = Some W_9bab4.
Proof. vm_refl. Qed.
Lemma D_9bab4 : decode_any W_9bab4 = Some (OpImm ALU_ADD 11 19 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9bab8 : bv 32 := 0x00090613.
Lemma F_9bab8 : fetch_word PSEGS (0x9bab8 : word) = Some W_9bab8.
Proof. vm_refl. Qed.
Lemma D_9bab8 : decode_any W_9bab8 = Some (OpImm ALU_ADD 12 18 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9babc : bv 32 := 0x00000073.
Lemma F_9babc : fetch_word PSEGS (0x9babc : word) = Some W_9babc.
Proof. vm_refl. Qed.
Lemma D_9babc : decode_any W_9babc = Some (Ecall, 4%Z).
Proof. vm_refl. Qed.
Lemma E_9babc : is_ecall W_9babc = true.
Proof. reflexivity. Qed.

(* [comment removed for export] *)
Definition W_9bac0 : bv 32 := 0xf94fa0ef.
Lemma F_9bac0 : fetch_word PSEGS (0x9bac0 : word) = Some W_9bac0.
Proof. vm_refl. Qed.
Lemma D_9bac0 : decode_any W_9bac0 = Some (Jal 1 2074516, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9bac4 : bv 32 := 0x09651863.
Lemma F_9bac4 : fetch_word PSEGS (0x9bac4 : word) = Some W_9bac4.
Proof. vm_refl. Qed.
Lemma D_9bac4 : decode_any W_9bac4 = Some (Branch BC_NE 10 22 144, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9bac8 : bv 32 := 0x0584b503.
Lemma F_9bac8 : fetch_word PSEGS (0x9bac8 : word) = Some W_9bac8.
Proof. vm_refl. Qed.
Lemma D_9bac8 : decode_any W_9bac8 = Some (Load SZ8 true 10 9 88, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9bacc : bv 32 := 0x0604b583.
Lemma F_9bacc : fetch_word PSEGS (0x9bacc : word) = Some W_9bacc.
Proof. vm_refl. Qed.
Lemma D_9bacc : decode_any W_9bacc = Some (Load SZ8 true 11 9 96, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9bad0 : bv 32 := 0x00b505b3.
Lemma F_9bad0 : fetch_word PSEGS (0x9bad0 : word) = Some W_9bad0.
Proof. vm_refl. Qed.
Lemma D_9bad0 : decode_any W_9bad0 = Some (Op ALU_ADD 11 10 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9bad4 : bv 32 := 0x02b4b023.
Lemma F_9bad4 : fetch_word PSEGS (0x9bad4 : word) = Some W_9bad4.
Proof. vm_refl. Qed.
Lemma D_9bad4 : decode_any W_9bad4 = Some (Store SZ8 9 11 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9bad8 : bv 32 := 0x02a4b423.
Lemma F_9bad8 : fetch_word PSEGS (0x9bad8 : word) = Some W_9bad8.
Proof. vm_refl. Qed.
Lemma D_9bad8 : decode_any W_9bad8 = Some (Store SZ8 9 10 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9badc : bv 32 := 0x02a4bc23.
Lemma F_9badc : fetch_word PSEGS (0x9badc : word) = Some W_9badc.
Proof. vm_refl. Qed.
Lemma D_9badc : decode_any W_9badc = Some (Store SZ8 9 10 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9bae0 : bv 32 := 0x00040513.
Lemma F_9bae0 : fetch_word PSEGS (0x9bae0 : word) = Some W_9bae0.
Proof. vm_refl. Qed.
Lemma D_9bae0 : decode_any W_9bae0 = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9bae4 : bv 32 := 0x000ab583.
Lemma F_9bae4 : fetch_word PSEGS (0x9bae4 : word) = Some W_9bae4.
Proof. vm_refl. Qed.
Lemma D_9bae4 : decode_any W_9bae4 = Some (Load SZ8 true 11 21 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9bae8 : bv 32 := 0x02813603.
Lemma F_9bae8 : fetch_word PSEGS (0x9bae8 : word) = Some W_9bae8.
Proof. vm_refl. Qed.
Lemma D_9bae8 : decode_any W_9bae8 = Some (Load SZ8 true 12 2 40, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9baec : bv 32 := 0x0cc59a63.
Lemma F_9baec : fetch_word PSEGS (0x9baec : word) = Some W_9baec.
Proof. vm_refl. Qed.
Lemma D_9baec : decode_any W_9baec = Some (Branch BC_NE 11 12 212, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9baf0 : bv 32 := 0x06813083.
Lemma F_9baf0 : fetch_word PSEGS (0x9baf0 : word) = Some W_9baf0.
Proof. vm_refl. Qed.
Lemma D_9baf0 : decode_any W_9baf0 = Some (Load SZ8 true 1 2 104, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9baf4 : bv 32 := 0x06013403.
Lemma F_9baf4 : fetch_word PSEGS (0x9baf4 : word) = Some W_9baf4.
Proof. vm_refl. Qed.
Lemma D_9baf4 : decode_any W_9baf4 = Some (Load SZ8 true 8 2 96, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9baf8 : bv 32 := 0x05813483.
Lemma F_9baf8 : fetch_word PSEGS (0x9baf8 : word) = Some W_9baf8.
Proof. vm_refl. Qed.
Lemma D_9baf8 : decode_any W_9baf8 = Some (Load SZ8 true 9 2 88, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9bafc : bv 32 := 0x05013903.
Lemma F_9bafc : fetch_word PSEGS (0x9bafc : word) = Some W_9bafc.
Proof. vm_refl. Qed.
Lemma D_9bafc : decode_any W_9bafc = Some (Load SZ8 true 18 2 80, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9bb00 : bv 32 := 0x04813983.
Lemma F_9bb00 : fetch_word PSEGS (0x9bb00 : word) = Some W_9bb00.
Proof. vm_refl. Qed.
Lemma D_9bb00 : decode_any W_9bb00 = Some (Load SZ8 true 19 2 72, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9bb04 : bv 32 := 0x04013a03.
Lemma F_9bb04 : fetch_word PSEGS (0x9bb04 : word) = Some W_9bb04.
Proof. vm_refl. Qed.
Lemma D_9bb04 : decode_any W_9bb04 = Some (Load SZ8 true 20 2 64, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9bb08 : bv 32 := 0x03813a83.
Lemma F_9bb08 : fetch_word PSEGS (0x9bb08 : word) = Some W_9bb08.
Proof. vm_refl. Qed.
Lemma D_9bb08 : decode_any W_9bb08 = Some (Load SZ8 true 21 2 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9bb0c : bv 32 := 0x03013b03.
Lemma F_9bb0c : fetch_word PSEGS (0x9bb0c : word) = Some W_9bb0c.
Proof. vm_refl. Qed.
Lemma D_9bb0c : decode_any W_9bb0c = Some (Load SZ8 true 22 2 48, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9bb10 : bv 32 := 0x07010113.
Lemma F_9bb10 : fetch_word PSEGS (0x9bb10 : word) = Some W_9bb10.
Proof. vm_refl. Qed.
Lemma D_9bb10 : decode_any W_9bb10 = Some (OpImm ALU_ADD 2 2 112, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9bb14 : bv 32 := 0x00008067.
Lemma F_9bb14 : fetch_word PSEGS (0x9bb14 : word) = Some W_9bb14.
Proof. vm_refl. Qed.
Lemma D_9bb14 : decode_any W_9bb14 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9bb18 : bv 32 := 0x00800713.
Lemma F_9bb18 : fetch_word PSEGS (0x9bb18 : word) = Some W_9bb18.
Proof. vm_refl. Qed.
Lemma D_9bb18 : decode_any W_9bb18 = Some (OpImm ALU_ADD 14 0 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9bb1c : bv 32 := 0x000a0593.
Lemma F_9bb1c : fetch_word PSEGS (0x9bb1c : word) = Some W_9bb1c.
Proof. vm_refl. Qed.
Lemma D_9bb1c : decode_any W_9bb1c = Some (OpImm ALU_ADD 11 20 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9bb20 : bv 32 := 0x00e98733.
Lemma F_9bb20 : fetch_word PSEGS (0x9bb20 : word) = Some W_9bb20.
Proof. vm_refl. Qed.
Lemma D_9bb20 : decode_any W_9bb20 = Some (Op ALU_ADD 14 19 14, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9bb24 : bv 32 := 0x00073783.
Lemma F_9bb24 : fetch_word PSEGS (0x9bb24 : word) = Some W_9bb24.
Proof. vm_refl. Qed.
Lemma D_9bb24 : decode_any W_9bb24 = Some (Load SZ8 true 15 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9bb28 : bv 32 := 0x40ab0b33.
Lemma F_9bb28 : fetch_word PSEGS (0x9bb28 : word) = Some W_9bb28.
Proof. vm_refl. Qed.
Lemma D_9bb28 : decode_any W_9bb28 = Some (Op ALU_SUB 22 22 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9bb2c : bv 32 := 0x0784a503.
Lemma F_9bb2c : fetch_word PSEGS (0x9bb2c : word) = Some W_9bb2c.
Proof. vm_refl. Qed.
Lemma D_9bb2c : decode_any W_9bb2c = Some (Load SZ4 true 10 9 120, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9bb30 : bv 32 := 0x40c9093b.
Lemma F_9bb30 : fetch_word PSEGS (0x9bb30 : word) = Some W_9bb30.
Proof. vm_refl. Qed.
Lemma D_9bb30 : decode_any W_9bb30 = Some (Op32 ALU_SUB 18 18 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9bb34 : bv 32 := 0x40d787b3.
Lemma F_9bb34 : fetch_word PSEGS (0x9bb34 : word) = Some W_9bb34.
Proof. vm_refl. Qed.
Lemma D_9bb34 : decode_any W_9bb34 = Some (Op ALU_SUB 15 15 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9bb38 : bv 32 := 0x00f73023.
Lemma F_9bb38 : fetch_word PSEGS (0x9bb38 : word) = Some W_9bb38.
Proof. vm_refl. Qed.
Lemma D_9bb38 : decode_any W_9bb38 = Some (Store SZ8 14 15 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9bb3c : bv 32 := 0x04200893.
Lemma F_9bb3c : fetch_word PSEGS (0x9bb3c : word) = Some W_9bb3c.
Proof. vm_refl. Qed.
Lemma D_9bb3c : decode_any W_9bb3c = Some (OpImm ALU_ADD 17 0 66, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9bb40 : bv 32 := 0x00090613.
Lemma F_9bb40 : fetch_word PSEGS (0x9bb40 : word) = Some W_9bb40.
Proof. vm_refl. Qed.
Lemma D_9bb40 : decode_any W_9bb40 = Some (OpImm ALU_ADD 12 18 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9bb44 : bv 32 := 0x00000073.
Lemma F_9bb44 : fetch_word PSEGS (0x9bb44 : word) = Some W_9bb44.
Proof. vm_refl. Qed.
Lemma D_9bb44 : decode_any W_9bb44 = Some (Ecall, 4%Z).
Proof. vm_refl. Qed.
Lemma E_9bb44 : is_ecall W_9bb44 = true.
Proof. reflexivity. Qed.

(* [comment removed for export] *)
Definition W_9bb48 : bv 32 := 0xf0cfa0ef.
Lemma F_9bb48 : fetch_word PSEGS (0x9bb48 : word) = Some W_9bb48.
Proof. vm_refl. Qed.
Lemma D_9bb48 : decode_any W_9bb48 = Some (Jal 1 2074380, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9bb4c : bv 32 := 0x000a0993.
Lemma F_9bb4c : fetch_word PSEGS (0x9bb4c : word) = Some W_9bb4c.
Proof. vm_refl. Qed.
Lemma D_9bb4c : decode_any W_9bb4c = Some (OpImm ALU_ADD 19 20 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9bb50 : bv 32 := 0xf7650ce3.
Lemma F_9bb50 : fetch_word PSEGS (0x9bb50 : word) = Some W_9bb50.
Proof. vm_refl. Qed.
Lemma D_9bb50 : decode_any W_9bb50 = Some (Branch BC_EQ 10 22 8056, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9bb54 : bv 32 := 0x02054c63.
Lemma F_9bb54 : fetch_word PSEGS (0x9bb54 : word) = Some W_9bb54.
Proof. vm_refl. Qed.
Lemma D_9bb54 : decode_any W_9bb54 = Some (Branch BC_LT 10 0 56, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9bb58 : bv 32 := 0x0089b583.
Lemma F_9bb58 : fetch_word PSEGS (0x9bb58 : word) = Some W_9bb58.
Proof. vm_refl. Qed.
Lemma D_9bb58 : decode_any W_9bb58 = Some (Load SZ8 true 11 19 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9bb5c : bv 32 := 0x00a5b633.
Lemma F_9bb5c : fetch_word PSEGS (0x9bb5c : word) = Some W_9bb5c.
Proof. vm_refl. Qed.
Lemma D_9bb5c : decode_any W_9bb5c = Some (Op ALU_SLTU 12 11 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9bb60 : bv 32 := 0x00461a13.
Lemma F_9bb60 : fetch_word PSEGS (0x9bb60 : word) = Some W_9bb60.
Proof. vm_refl. Qed.
Lemma D_9bb60 : decode_any W_9bb60 = Some (ShiftImm ALU_SLL 20 12 4, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9bb64 : bv 32 := 0x01498a33.
Lemma F_9bb64 : fetch_word PSEGS (0x9bb64 : word) = Some W_9bb64.
Proof. vm_refl. Qed.
Lemma D_9bb64 : decode_any W_9bb64 = Some (Op ALU_ADD 20 19 20, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9bb68 : bv 32 := 0x000a3703.
Lemma F_9bb68 : fetch_word PSEGS (0x9bb68 : word) = Some W_9bb68.
Proof. vm_refl. Qed.
Lemma D_9bb68 : decode_any W_9bb68 = Some (Load SZ8 true 14 20 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9bb6c : bv 32 := 0x40c006b3.
Lemma F_9bb6c : fetch_word PSEGS (0x9bb6c : word) = Some W_9bb6c.
Proof. vm_refl. Qed.
Lemma D_9bb6c : decode_any W_9bb6c = Some (Op ALU_SUB 13 0 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9bb70 : bv 32 := 0x00b6f6b3.
Lemma F_9bb70 : fetch_word PSEGS (0x9bb70 : word) = Some W_9bb70.
Proof. vm_refl. Qed.
Lemma D_9bb70 : decode_any W_9bb70 = Some (Op ALU_AND 13 13 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9bb74 : bv 32 := 0x40d506b3.
Lemma F_9bb74 : fetch_word PSEGS (0x9bb74 : word) = Some W_9bb74.
Proof. vm_refl. Qed.
Lemma D_9bb74 : decode_any W_9bb74 = Some (Op ALU_SUB 13 10 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9bb78 : bv 32 := 0x00d70733.
Lemma F_9bb78 : fetch_word PSEGS (0x9bb78 : word) = Some W_9bb78.
Proof. vm_refl. Qed.
Lemma D_9bb78 : decode_any W_9bb78 = Some (Op ALU_ADD 14 14 13, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9bb7c : bv 32 := 0x00ea3023.
Lemma F_9bb7c : fetch_word PSEGS (0x9bb7c : word) = Some W_9bb7c.
Proof. vm_refl. Qed.
Lemma D_9bb7c : decode_any W_9bb7c = Some (Store SZ8 20 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9bb80 : bv 32 := 0xf8a5fce3.
Lemma F_9bb80 : fetch_word PSEGS (0x9bb80 : word) = Some W_9bb80.
Proof. vm_refl. Qed.
Lemma D_9bb80 : decode_any W_9bb80 = Some (Branch BC_GEU 11 10 8088, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9bb84 : bv 32 := 0x01800713.
Lemma F_9bb84 : fetch_word PSEGS (0x9bb84 : word) = Some W_9bb84.
Proof. vm_refl. Qed.
Lemma D_9bb84 : decode_any W_9bb84 = Some (OpImm ALU_ADD 14 0 24, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9bb88 : bv 32 := 0xf95ff06f.
Lemma F_9bb88 : fetch_word PSEGS (0x9bb88 : word) = Some W_9bb88.
Proof. vm_refl. Qed.
Lemma D_9bb88 : decode_any W_9bb88 = Some (Jal 0 2097044, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9bd08 : bv 32 := 0x00c13423.
Lemma F_9bd08 : fetch_word PSEGS (0x9bd08 : word) = Some W_9bd08.
Proof. vm_refl. Qed.
Lemma D_9bd08 : decode_any W_9bd08 = Some (Store SZ8 2 12 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9bd0c : bv 32 := 0x00000513.
Lemma F_9bd0c : fetch_word PSEGS (0x9bd0c : word) = Some W_9bd0c.
Proof. vm_refl. Qed.
Lemma D_9bd0c : decode_any W_9bd0c = Some (OpImm ALU_ADD 10 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9bd10 : bv 32 := 0x00000593.
Lemma F_9bd10 : fetch_word PSEGS (0x9bd10 : word) = Some W_9bd10.
Proof. vm_refl. Qed.
Lemma D_9bd10 : decode_any W_9bd10 = Some (OpImm ALU_ADD 11 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9bd14 : bv 32 := 0x00040613.
Lemma F_9bd14 : fetch_word PSEGS (0x9bd14 : word) = Some W_9bd14.
Proof. vm_refl. Qed.
Lemma D_9bd14 : decode_any W_9bd14 = Some (OpImm ALU_ADD 12 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9bd18 : bv 32 := 0x121040ef.
Lemma F_9bd18 : fetch_word PSEGS (0x9bd18 : word) = Some W_9bd18.
Proof. vm_refl. Qed.
Lemma D_9bd18 : decode_any W_9bd18 = Some (Jal 1 18720, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9bd1c : bv 32 := 0xfff00493.
Lemma F_9bd1c : fetch_word PSEGS (0x9bd1c : word) = Some W_9bd1c.
Proof. vm_refl. Qed.
Lemma D_9bd1c : decode_any W_9bd1c = Some (OpImm ALU_ADD 9 0 4095, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9bd20 : bv 32 := 0x02054a63.
Lemma F_9bd20 : fetch_word PSEGS (0x9bd20 : word) = Some W_9bd20.
Proof. vm_refl. Qed.
Lemma D_9bd20 : decode_any W_9bd20 = Some (Branch BC_LT 10 0 52, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9bd24 : bv 32 := 0x00150513.
Lemma F_9bd24 : fetch_word PSEGS (0x9bd24 : word) = Some W_9bd24.
Proof. vm_refl. Qed.
Lemma D_9bd24 : decode_any W_9bd24 = Some (OpImm ALU_ADD 10 10 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9bd28 : bv 32 := 0x02051513.
Lemma F_9bd28 : fetch_word PSEGS (0x9bd28 : word) = Some W_9bd28.
Proof. vm_refl. Qed.
Lemma D_9bd28 : decode_any W_9bd28 = Some (ShiftImm ALU_SLL 10 10 32, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9bd7c : bv 32 := 0x05010113.
Lemma F_9bd7c : fetch_word PSEGS (0x9bd7c : word) = Some W_9bd7c.
Proof. vm_refl. Qed.
Lemma D_9bd7c : decode_any W_9bd7c = Some (OpImm ALU_ADD 2 2 80, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9bd80 : bv 32 := 0x00008067.
Lemma F_9bd80 : fetch_word PSEGS (0x9bd80 : word) = Some W_9bd80.
Proof. vm_refl. Qed.
Lemma D_9bd80 : decode_any W_9bd80 = Some (Jalr 0 1 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9bd84 : bv 32 := 0xcc8fa0ef.
Lemma F_9bd84 : fetch_word PSEGS (0x9bd84 : word) = Some W_9bd84.
Proof. vm_refl. Qed.
Lemma D_9bd84 : decode_any W_9bd84 = Some (Jal 1 2073800, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9bd88 : bv 32 := 0xe9010113.
Lemma F_9bd88 : fetch_word PSEGS (0x9bd88 : word) = Some W_9bd88.
Proof. vm_refl. Qed.
Lemma D_9bd88 : decode_any W_9bd88 = Some (OpImm ALU_ADD 2 2 3728, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9bd8c : bv 32 := 0x16113423.
Lemma F_9bd8c : fetch_word PSEGS (0x9bd8c : word) = Some W_9bd8c.
Proof. vm_refl. Qed.
Lemma D_9bd8c : decode_any W_9bd8c = Some (Store SZ8 2 1 360, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9bd98 : bv 32 := 0x15213823.
Lemma F_9bd98 : fetch_word PSEGS (0x9bd98 : word) = Some W_9bd98.
Proof. vm_refl. Qed.
Lemma D_9bd98 : decode_any W_9bd98 = Some (Store SZ8 2 18 336, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9bd9c : bv 32 := 0x15313423.
Lemma F_9bd9c : fetch_word PSEGS (0x9bd9c : word) = Some W_9bd9c.
Proof. vm_refl. Qed.
Lemma D_9bd9c : decode_any W_9bd9c = Some (Store SZ8 2 19 328, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9bda0 : bv 32 := 0x15413023.
Lemma F_9bda0 : fetch_word PSEGS (0x9bda0 : word) = Some W_9bda0.
Proof. vm_refl. Qed.
Lemma D_9bda0 : decode_any W_9bda0 = Some (Store SZ8 2 20 320, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9bda4 : bv 32 := 0x13513c23.
Lemma F_9bda4 : fetch_word PSEGS (0x9bda4 : word) = Some W_9bda4.
Proof. vm_refl. Qed.
Lemma D_9bda4 : decode_any W_9bda4 = Some (Store SZ8 2 21 312, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9bda8 : bv 32 := 0x00058493.
Lemma F_9bda8 : fetch_word PSEGS (0x9bda8 : word) = Some W_9bda8.
Proof. vm_refl. Qed.
Lemma D_9bda8 : decode_any W_9bda8 = Some (OpImm ALU_ADD 9 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9bdac : bv 32 := 0x00050413.
Lemma F_9bdac : fetch_word PSEGS (0x9bdac : word) = Some W_9bdac.
Proof. vm_refl. Qed.
Lemma D_9bdac : decode_any W_9bdac = Some (OpImm ALU_ADD 8 10 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9bdb0 : bv 32 := 0x00016517.
Lemma F_9bdb0 : fetch_word PSEGS (0x9bdb0 : word) = Some W_9bdb0.
Proof. vm_refl. Qed.
Lemma D_9bdb0 : decode_any W_9bdb0 = Some (Auipc 10 22, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9bdb4 : bv 32 := 0xe0053903.
Lemma F_9bdb4 : fetch_word PSEGS (0x9bdb4 : word) = Some W_9bdb4.
Proof. vm_refl. Qed.
Lemma D_9bdb4 : decode_any W_9bdb4 = Some (Load SZ8 true 18 10 3584, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9bdb8 : bv 32 := 0x00093503.
Lemma F_9bdb8 : fetch_word PSEGS (0x9bdb8 : word) = Some W_9bdb8.
Proof. vm_refl. Qed.
Lemma D_9bdb8 : decode_any W_9bdb8 = Some (Load SZ8 true 10 18 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9bdbc : bv 32 := 0x12a13823.
Lemma F_9bdbc : fetch_word PSEGS (0x9bdbc : word) = Some W_9bdbc.
Proof. vm_refl. Qed.
Lemma D_9bdbc : decode_any W_9bdbc = Some (Store SZ8 2 10 304, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9bdc0 : bv 32 := 0x00c13423.
Lemma F_9bdc0 : fetch_word PSEGS (0x9bdc0 : word) = Some W_9bdc0.
Proof. vm_refl. Qed.
Lemma D_9bdc0 : decode_any W_9bdc0 = Some (Store SZ8 2 12 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9bdd8 : bv 32 := 0x00c13023.
Lemma F_9bdd8 : fetch_word PSEGS (0x9bdd8 : word) = Some W_9bdd8.
Proof. vm_refl. Qed.
Lemma D_9bdd8 : decode_any W_9bdd8 = Some (Store SZ8 2 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9bddc : bv 32 := 0x00010613.
Lemma F_9bddc : fetch_word PSEGS (0x9bddc : word) = Some W_9bddc.
Proof. vm_refl. Qed.
Lemma D_9bddc : decode_any W_9bddc = Some (OpImm ALU_ADD 12 2 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9bde0 : bv 32 := 0x06010693.
Lemma F_9bde0 : fetch_word PSEGS (0x9bde0 : word) = Some W_9bde0.
Proof. vm_refl. Qed.
Lemma D_9bde0 : decode_any W_9bde0 = Some (OpImm ALU_ADD 13 2 96, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9bde4 : bv 32 := 0x10810713.
Lemma F_9bde4 : fetch_word PSEGS (0x9bde4 : word) = Some W_9bde4.
Proof. vm_refl. Qed.
Lemma D_9bde4 : decode_any W_9bde4 = Some (OpImm ALU_ADD 14 2 264, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9bde8 : bv 32 := 0x00000513.
Lemma F_9bde8 : fetch_word PSEGS (0x9bde8 : word) = Some W_9bde8.
Proof. vm_refl. Qed.
Lemma D_9bde8 : decode_any W_9bde8 = Some (OpImm ALU_ADD 10 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9bdf4 : bv 32 := 0x08c42503.
Lemma F_9bdf4 : fetch_word PSEGS (0x9bdf4 : word) = Some W_9bdf4.
Proof. vm_refl. Qed.
Lemma D_9bdf4 : decode_any W_9bdf4 = Some (Load SZ4 true 10 8 140, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9bdf8 : bv 32 := 0x00054e63.
Lemma F_9bdf8 : fetch_word PSEGS (0x9bdf8 : word) = Some W_9bdf8.
Proof. vm_refl. Qed.
Lemma D_9bdf8 : decode_any W_9bdf8 = Some (Branch BC_LT 10 0 28, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9bdfc : bv 32 := 0x00040513.
Lemma F_9bdfc : fetch_word PSEGS (0x9bdfc : word) = Some W_9bdfc.
Proof. vm_refl. Qed.
Lemma D_9bdfc : decode_any W_9bdfc = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9be14 : bv 32 := 0x00100993.
Lemma F_9be14 : fetch_word PSEGS (0x9be14 : word) = Some W_9be14.
Proof. vm_refl. Qed.
Lemma D_9be14 : decode_any W_9be14 = Some (OpImm ALU_ADD 19 0 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9be18 : bv 32 := 0x00042a83.
Lemma F_9be18 : fetch_word PSEGS (0x9be18 : word) = Some W_9be18.
Proof. vm_refl. Qed.
Lemma D_9be18 : decode_any W_9be18 = Some (Load SZ4 true 21 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9be1c : bv 32 := 0x06043503.
Lemma F_9be1c : fetch_word PSEGS (0x9be1c : word) = Some W_9be1c.
Proof. vm_refl. Qed.
Lemma D_9be1c : decode_any W_9be1c = Some (Load SZ8 true 10 8 96, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9be9c : bv 32 := 0x04843683.
Lemma F_9be9c : fetch_word PSEGS (0x9be9c : word) = Some W_9be9c.
Proof. vm_refl. Qed.
Lemma D_9be9c : decode_any W_9be9c = Some (Load SZ8 true 13 8 72, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9bea0 : bv 32 := 0x00040513.
Lemma F_9bea0 : fetch_word PSEGS (0x9bea0 : word) = Some W_9bea0.
Proof. vm_refl. Qed.
Lemma D_9bea0 : decode_any W_9bea0 = Some (OpImm ALU_ADD 10 8 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9bea4 : bv 32 := 0x00000593.
Lemma F_9bea4 : fetch_word PSEGS (0x9bea4 : word) = Some W_9bea4.
Proof. vm_refl. Qed.
Lemma D_9bea4 : decode_any W_9bea4 = Some (OpImm ALU_ADD 11 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9bea8 : bv 32 := 0x00000613.
Lemma F_9bea8 : fetch_word PSEGS (0x9bea8 : word) = Some W_9bea8.
Proof. vm_refl. Qed.
Lemma D_9bea8 : decode_any W_9bea8 = Some (OpImm ALU_ADD 12 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9c09c : bv 32 := 0x002ac703.
Lemma F_9c09c : fetch_word PSEGS (0x9c09c : word) = Some W_9c09c.
Proof. vm_refl. Qed.
Lemma D_9c09c : decode_any W_9c09c = Some (Load SZ1 false 14 21 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9c0a0 : bv 32 := 0x02400793.
Lemma F_9c0a0 : fetch_word PSEGS (0x9c0a0 : word) = Some W_9c0a0.
Proof. vm_refl. Qed.
Lemma D_9c0a0 : decode_any W_9c0a0 = Some (OpImm ALU_ADD 15 0 36, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9c0a4 : bv 32 := 0x00100813.
Lemma F_9c0a4 : fetch_word PSEGS (0x9c0a4 : word) = Some W_9c0a4.
Proof. vm_refl. Qed.
Lemma D_9c0a4 : decode_any W_9c0a4 = Some (OpImm ALU_ADD 16 0 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9c0a8 : bv 32 := 0x05013283.
Lemma F_9c0a8 : fetch_word PSEGS (0x9c0a8 : word) = Some W_9c0a8.
Proof. vm_refl. Qed.
Lemma D_9c0a8 : decode_any W_9c0a8 = Some (Load SZ8 true 5 2 80, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9c0ac : bv 32 := 0x02f71263.
Lemma F_9c0ac : fetch_word PSEGS (0x9c0ac : word) = Some W_9c0ac.
Proof. vm_refl. Qed.
Lemma D_9c0ac : decode_any W_9c0ac = Some (Branch BC_NE 14 15 36, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9c0b0 : bv 32 := 0x003ac583.
Lemma F_9c0b0 : fetch_word PSEGS (0x9c0b0 : word) = Some W_9c0b0.
Proof. vm_refl. Qed.
Lemma D_9c0b0 : decode_any W_9c0b0 = Some (Load SZ1 false 11 21 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9c0b4 : bv 32 := 0x003a8613.
Lemma F_9c0b4 : fetch_word PSEGS (0x9c0b4 : word) = Some W_9c0b4.
Proof. vm_refl. Qed.
Lemma D_9c0b4 : decode_any W_9c0b4 = Some (OpImm ALU_ADD 12 21 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9c0b8 : bv 32 := 0x00100513.
Lemma F_9c0b8 : fetch_word PSEGS (0x9c0b8 : word) = Some W_9c0b8.
Proof. vm_refl. Qed.
Lemma D_9c0b8 : decode_any W_9c0b8 = Some (OpImm ALU_ADD 10 0 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9c0bc : bv 32 := 0x04a13c23.
Lemma F_9c0bc : fetch_word PSEGS (0x9c0bc : word) = Some W_9c0bc.
Proof. vm_refl. Qed.
Lemma D_9c0bc : decode_any W_9c0bc = Some (Store SZ8 2 10 88, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9c0c0 : bv 32 := 0x00068513.
Lemma F_9c0c0 : fetch_word PSEGS (0x9c0c0 : word) = Some W_9c0c0.
Proof. vm_refl. Qed.
Lemma D_9c0c0 : decode_any W_9c0c0 = Some (OpImm ALU_ADD 10 13 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9c0c4 : bv 32 := 0x00c0006f.
Lemma F_9c0c4 : fetch_word PSEGS (0x9c0c4 : word) = Some W_9c0c4.
Proof. vm_refl. Qed.
Lemma D_9c0c4 : decode_any W_9c0c4 = Some (Jal 0 12, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9c0c8 : bv 32 := 0x00100813.
Lemma F_9c0c8 : fetch_word PSEGS (0x9c0c8 : word) = Some W_9c0c8.
Proof. vm_refl. Qed.
Lemma D_9c0c8 : decode_any W_9c0c8 = Some (OpImm ALU_ADD 16 0 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9c19c : bv 32 := 0xfd080593.
Lemma F_9c19c : fetch_word PSEGS (0x9c19c : word) = Some W_9c19c.
Proof. vm_refl. Qed.
Lemma D_9c19c : decode_any W_9c19c = Some (OpImm ALU_ADD 11 16 4048, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9c1cc : bv 32 := 0x1e50006f.
Lemma F_9c1cc : fetch_word PSEGS (0x9c1cc : word) = Some W_9c1cc.
Proof. vm_refl. Qed.
Lemma D_9c1cc : decode_any W_9c1cc = Some (Jal 0 2532, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9c1d0 : bv 32 := 0x05813583.
Lemma F_9c1d0 : fetch_word PSEGS (0x9c1d0 : word) = Some W_9c1d0.
Proof. vm_refl. Qed.
Lemma D_9c1d0 : decode_any W_9c1d0 = Some (Load SZ8 true 11 2 88, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9c1d4 : bv 32 := 0x320598e3.
Lemma F_9c1d4 : fetch_word PSEGS (0x9c1d4 : word) = Some W_9c1d4.
Proof. vm_refl. Qed.
Lemma D_9c1d4 : decode_any W_9c1d4 = Some (Branch BC_NE 11 0 2864, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9c1d8 : bv 32 := 0x00160613.
Lemma F_9c1d8 : fetch_word PSEGS (0x9c1d8 : word) = Some W_9c1d8.
Proof. vm_refl. Qed.
Lemma D_9c1d8 : decode_any W_9c1d8 = Some (OpImm ALU_ADD 12 12 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9c1dc : bv 32 := 0x020a0263.
Lemma F_9c1dc : fetch_word PSEGS (0x9c1dc : word) = Some W_9c1dc.
Proof. vm_refl. Qed.
Lemma D_9c1dc : decode_any W_9c1dc = Some (Branch BC_EQ 20 0 36, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9c1e0 : bv 32 := 0x04813703.
Lemma F_9c1e0 : fetch_word PSEGS (0x9c1e0 : word) = Some W_9c1e0.
Proof. vm_refl. Qed.
Lemma D_9c1e0 : decode_any W_9c1e0 = Some (Load SZ8 true 14 2 72, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9c1e4 : bv 32 := 0x00073583.
Lemma F_9c1e4 : fetch_word PSEGS (0x9c1e4 : word) = Some W_9c1e4.
Proof. vm_refl. Qed.
Lemma D_9c1e4 : decode_any W_9c1e4 = Some (Load SZ8 true 11 14 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9c1e8 : bv 32 := 0x00858693.
Lemma F_9c1e8 : fetch_word PSEGS (0x9c1e8 : word) = Some W_9c1e8.
Proof. vm_refl. Qed.
Lemma D_9c1e8 : decode_any W_9c1e8 = Some (OpImm ALU_ADD 13 11 8, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9c1ec : bv 32 := 0x00d73023.
Lemma F_9c1ec : fetch_word PSEGS (0x9c1ec : word) = Some W_9c1ec.
Proof. vm_refl. Qed.
Lemma D_9c1ec : decode_any W_9c1ec = Some (Store SZ8 14 13 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9c1f0 : bv 32 := 0x0005ab03.
Lemma F_9c1f0 : fetch_word PSEGS (0x9c1f0 : word) = Some W_9c1f0.
Proof. vm_refl. Qed.
Lemma D_9c1f0 : decode_any W_9c1f0 = Some (Load SZ4 true 22 11 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9c1f4 : bv 32 := 0x04013c23.
Lemma F_9c1f4 : fetch_word PSEGS (0x9c1f4 : word) = Some W_9c1f4.
Proof. vm_refl. Qed.
Lemma D_9c1f4 : decode_any W_9c1f4 = Some (Store SZ8 2 0 88, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9c1f8 : bv 32 := 0x040b5863.
Lemma F_9c1f8 : fetch_word PSEGS (0x9c1f8 : word) = Some W_9c1f8.
Proof. vm_refl. Qed.
Lemma D_9c1f8 : decode_any W_9c1f8 = Some (Branch BC_GE 22 0 80, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9c1fc : bv 32 := 0x0400006f.
Lemma F_9c1fc : fetch_word PSEGS (0x9c1fc : word) = Some W_9c1fc.
Proof. vm_refl. Qed.
Lemma D_9c1fc : decode_any W_9c1fc = Some (Jal 0 64, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9c200 : bv 32 := 0x04013c23.
Lemma F_9c200 : fetch_word PSEGS (0x9c200 : word) = Some W_9c200.
Proof. vm_refl. Qed.
Lemma D_9c200 : decode_any W_9c200 = Some (Store SZ8 2 0 88, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9c204 : bv 32 := 0x00000b13.
Lemma F_9c204 : fetch_word PSEGS (0x9c204 : word) = Some W_9c204.
Proof. vm_refl. Qed.
Lemma D_9c204 : decode_any W_9c204 = Some (OpImm ALU_ADD 22 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9c208 : bv 32 := 0x0400006f.
Lemma F_9c208 : fetch_word PSEGS (0x9c208 : word) = Some W_9c208.
Proof. vm_refl. Qed.
Lemma D_9c208 : decode_any W_9c208 = Some (Jal 0 64, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9c20c : bv 32 := 0x02e7fe63.
Lemma F_9c20c : fetch_word PSEGS (0x9c20c : word) = Some W_9c20c.
Proof. vm_refl. Qed.
Lemma D_9c20c : decode_any W_9c20c = Some (Branch BC_GEU 15 14 60, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9c210 : bv 32 := 0x1a10006f.
Lemma F_9c210 : fetch_word PSEGS (0x9c210 : word) = Some W_9c210.
Proof. vm_refl. Qed.
Lemma D_9c210 : decode_any W_9c210 = Some (Jal 0 2464, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9c214 : bv 32 := 0x00000b13.
Lemma F_9c214 : fetch_word PSEGS (0x9c214 : word) = Some W_9c214.
Proof. vm_refl. Qed.
Lemma D_9c214 : decode_any W_9c214 = Some (OpImm ALU_ADD 22 0 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9c218 : bv 32 := 0x00259593.
Lemma F_9c218 : fetch_word PSEGS (0x9c218 : word) = Some W_9c218.
Proof. vm_refl. Qed.
Lemma D_9c218 : decode_any W_9c218 = Some (ShiftImm ALU_SLL 11 11 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9c21c : bv 32 := 0x04013683.
Lemma F_9c21c : fetch_word PSEGS (0x9c21c : word) = Some W_9c21c.
Proof. vm_refl. Qed.
Lemma D_9c21c : decode_any W_9c21c = Some (Load SZ8 true 13 2 64, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9c220 : bv 32 := 0x00b685b3.
Lemma F_9c220 : fetch_word PSEGS (0x9c220 : word) = Some W_9c220.
Proof. vm_refl. Qed.
Lemma D_9c220 : decode_any W_9c220 = Some (Op ALU_ADD 11 13 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9c224 : bv 32 := 0x00a00693.
Lemma F_9c224 : fetch_word PSEGS (0x9c224 : word) = Some W_9c224.
Proof. vm_refl. Qed.
Lemma D_9c224 : decode_any W_9c224 = Some (OpImm ALU_ADD 13 0 10, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9c228 : bv 32 := 0x00d5a023.
Lemma F_9c228 : fetch_word PSEGS (0x9c228 : word) = Some W_9c228.
Proof. vm_refl. Qed.
Lemma D_9c228 : decode_any W_9c228 = Some (Store SZ4 11 13 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9c22c : bv 32 := 0x00360613.
Lemma F_9c22c : fetch_word PSEGS (0x9c22c : word) = Some W_9c22c.
Proof. vm_refl. Qed.
Lemma D_9c22c : decode_any W_9c22c = Some (OpImm ALU_ADD 12 12 3, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9c230 : bv 32 := 0x00100593.
Lemma F_9c230 : fetch_word PSEGS (0x9c230 : word) = Some W_9c230.
Proof. vm_refl. Qed.
Lemma D_9c230 : decode_any W_9c230 = Some (OpImm ALU_ADD 11 0 1, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9c234 : bv 32 := 0x04b13c23.
Lemma F_9c234 : fetch_word PSEGS (0x9c234 : word) = Some W_9c234.
Proof. vm_refl. Qed.
Lemma D_9c234 : decode_any W_9c234 = Some (Store SZ8 2 11 88, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9c238 : bv 32 := 0x000b5863.
Lemma F_9c238 : fetch_word PSEGS (0x9c238 : word) = Some W_9c238.
Proof. vm_refl. Qed.
Lemma D_9c238 : decode_any W_9c238 = Some (Branch BC_GE 22 0 16, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9c23c : bv 32 := 0x000025b7.
Lemma F_9c23c : fetch_word PSEGS (0x9c23c : word) = Some W_9c23c.
Proof. vm_refl. Qed.
Lemma D_9c23c : decode_any W_9c23c = Some (Lui 11 2, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9c240 : bv 32 := 0x00bc6c33.
Lemma F_9c240 : fetch_word PSEGS (0x9c240 : word) = Some W_9c240.
Proof. vm_refl. Qed.
Lemma D_9c240 : decode_any W_9c240 = Some (Op ALU_OR 24 24 11, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9c244 : bv 32 := 0x41600b3b.
Lemma F_9c244 : fetch_word PSEGS (0x9c244 : word) = Some W_9c244.
Proof. vm_refl. Qed.
Lemma D_9c244 : decode_any W_9c244 = Some (Op32 ALU_SUB 22 0 22, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9c248 : bv 32 := 0x00064583.
Lemma F_9c248 : fetch_word PSEGS (0x9c248 : word) = Some W_9c248.
Proof. vm_refl. Qed.
Lemma D_9c248 : decode_any W_9c248 = Some (Load SZ1 false 11 12 0, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9c24c : bv 32 := 0x02e00693.
Lemma F_9c24c : fetch_word PSEGS (0x9c24c : word) = Some W_9c24c.
Proof. vm_refl. Qed.
Lemma D_9c24c : decode_any W_9c24c = Some (OpImm ALU_ADD 13 0 46, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9c250 : bv 32 := 0x04d59863.
Lemma F_9c250 : fetch_word PSEGS (0x9c250 : word) = Some W_9c250.
Proof. vm_refl. Qed.
Lemma D_9c250 : decode_any W_9c250 = Some (Branch BC_NE 11 13 80, 4%Z).
Proof. vm_refl. Qed.

(* [comment removed for export] *)
Definition W_9c254 : bv 32 := 0x00164583.
Lemma F_9c254 : fetch_word PSEGS (0x9c254 : word) = Some W_9c254.
Proof. vm_refl. Qed.
Lemma D_9c254 : decode_any W_9c254 = Some (Load SZ1 false 11 12 1, 4%Z).
Proof. vm_refl. Qed.
